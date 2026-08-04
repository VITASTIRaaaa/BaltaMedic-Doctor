#!/usr/bin/env python3
"""
Patient Checker for Vitastir Doctor.

Default launch opens a small UI with a Practice Fusion login action (Chrome + .env).
After successful login it navigates to the Tasks page, clicks "My tasks", and runs a continuous loop:
- Scans for vitamins (L-Carnitine, Glutathione, NAD, Ascorbic Acid, B12, Folic Acid (B9), MIC, etc.) plus
  GLP compounds matched exactly by regex: "Semaglutide 1mg/B12 1mg/ml";
  "TIRZEPATIDE/Glycine/B12 10mg,5mg,1mg/ml" (after Finish: Dispense must be 1 or 2 for Tirzepatide combo, else My Tasks + Save draft).
  For both GLP combos: after prescribing provider is chosen, patient state is read from `[data-element="order-metadata-patient"]` (city, ST ZIP).
  Patients in LA, MS, or AR always go to My Tasks + Save draft (same as bad dispense).
  Other GLP-only orders are skipped.
- Clicks Finish → handles quick preview (locked notes check) → Edit/Next if error → Send eRx
- Returns to My Tasks and repeats immediately.

Tunings for speed (reduced from previous version):
- Post-Finish: 4s → 2s (relies on WebDriverWait)
- Send eRx: 6s → 0.5s (site returns quickly)
- Preview: dedicated short waits (4s/3s) + sleep(0.8s→0.3s). Eliminates previous ~15s modal close delay.
- Loop idle (no tasks): 15s → 3s
- Post-success cycle: 2s → 0.5s
- Scrolling: progressive (initial viewport + 1 scroll + rescan per cycle if no vitamins found)

Key fixes for the "modal-backdrop in copy-modal" / intercepted click error:
- Aggressive JS cleanup of .modal-backdrop, .copy-modal, and Escape key simulation right after preview.
- Send eRx now scrolls into view + falls back to `execute_script("arguments[0].click()")` if regular click is blocked.
- Tightened preview close selector to avoid matching patient photo `role="button"`.

New behavior (as of latest update):
- If the lock symbol (`<i class="pull-right icon-lock icon-color-default-dark"></i>`) is **not found** in the quick preview (or is older than 11 months), the script now **explicitly skips** the patient.
- For GLP combos, a recent lock alone is not enough: the preview item's `<p>` lines together must include **Tirzepatide** or **Semaglutide** (case-insensitive), matching the order type (e.g. CC line).
- It logs "No recent symbol/locked note found in quick preview — skipping this patient..." and early-returns before reaching Send eRx.
- Future runs will remember skipped orders (via skipped_orders.txt — add this file to .gitignore if desired). Includes Folic Acid (B9).
- UI "Send eRx sent" count and sent_erx_orders.txt log only orders where Send eRx was actually clicked (tab-separated: time, order #, patient name, details).
- **Virtual table support**: Parses "My tasks (N)" header, performs multi-increment scrolling on `.data-table__scroller` (with back-and-forth to trigger occluded-content rendering) to load all rows when total >50 (previously got stuck at ~43-50 rows).

The quick preview (for recent locked notes) now uses isolated short timeouts, specific selectors, JS fallback, and explicit skip-on-no-symbol.
Risk: Very low sleeps may cause flakiness on slow connections. Increase WAIT_TIMEOUT or sleeps if you see "element not found" or preview errors.
"""

from __future__ import annotations

import argparse
import logging
import os
import re
import subprocess
import sys
import threading
import time
from datetime import datetime, timedelta
from pathlib import Path
from typing import Any, Dict, List, Optional

import pandas as pd
from dotenv import load_dotenv
from rich import print as rprint
from rich.console import Console
from rich.table import Table
from selenium import webdriver
from selenium.common.exceptions import (
    NoSuchElementException,
    StaleElementReferenceException,
    TimeoutException,
)
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.common.action_chains import ActionChains
from selenium.webdriver.common.by import By
from selenium.webdriver.support import expected_conditions as EC
from selenium.webdriver.support.ui import WebDriverWait

import tkinter as tk
from tkinter import messagebox, ttk

load_dotenv()

console = Console()

_pf_log = logging.getLogger("check_patients.pf")


def _ensure_pf_logging() -> None:
    if _pf_log.handlers:
        return
    level_name = os.getenv("CHECK_PATIENTS_LOG_LEVEL", "INFO").upper()
    level = getattr(logging, level_name, logging.INFO)
    h = logging.StreamHandler(sys.stderr)
    h.setFormatter(logging.Formatter("%(asctime)s [%(levelname)s] %(message)s", datefmt="%H:%M:%S"))
    _pf_log.addHandler(h)
    _pf_log.setLevel(level)
    _pf_log.propagate = False


def _load_skipped_orders() -> set:
    """Load previously skipped order numbers from file."""
    skipped = set()
    path = Path(SKIPPED_ORDERS_FILE)
    if path.exists():
        try:
            with open(path, "r", encoding="utf-8") as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith("#"):
                        skipped.add(line.upper())
        except Exception as e:
            _pf_log.warning("Could not load %s: %s", SKIPPED_ORDERS_FILE, e)
    return skipped


def _save_skipped_order(order_num: str) -> None:
    """Append an order number to the skip list file."""
    if not order_num:
        return
    path = Path(SKIPPED_ORDERS_FILE)
    try:
        with open(path, "a", encoding="utf-8") as f:
            f.write(f"{order_num.upper()}\n")
        _pf_log.info("Added order %s to skipped list", order_num)
    except Exception as e:
        _pf_log.warning("Could not save to %s: %s", SKIPPED_ORDERS_FILE, e)


def _sanitize_log_field(text: Optional[str], max_len: int = 500) -> str:
    return re.sub(r"[\t\r\n]+", " ", (text or "").strip())[:max_len]


def _extract_patient_name_from_task_row(row: Any) -> Optional[str]:
    """Patient name from the task row patient column (`a[data-element='patient-link']`)."""
    try:
        link = row.find_element(By.CSS_SELECTOR, 'a[data-element="patient-link"]')
        name = (link.text or "").strip()
        if name:
            return name
    except NoSuchElementException:
        pass
    try:
        patient_cell = row.find_element(By.CSS_SELECTOR, "td.task-row__patient")
        link = patient_cell.find_element(By.CSS_SELECTOR, "a")
        name = (link.text or "").strip()
        if name:
            return name
    except NoSuchElementException:
        pass
    try:
        tds = row.find_elements(By.TAG_NAME, "td")
        if len(tds) >= 3:
            for link in tds[2].find_elements(By.TAG_NAME, "a"):
                name = (link.text or "").strip()
                if name and not name.startswith("#"):
                    return name
    except Exception:
        pass
    return None


def _save_sent_erx_order(
    order_num: Optional[str],
    details: Optional[str] = None,
    patient_name: Optional[str] = None,
) -> None:
    """Append a record when Process eRx succeeded (timestamp, order #, patient, details)."""
    path = Path(SENT_ERX_ORDERS_FILE)
    ts = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    order_part = (order_num or "UNKNOWN").upper()
    patient_part = _sanitize_log_field(patient_name, max_len=200) or "UNKNOWN"
    detail_part = _sanitize_log_field(details)
    try:
        with open(path, "a", encoding="utf-8") as f:
            f.write(f"{ts}\t{order_part}\t{patient_part}\t{detail_part}\n")
        _pf_log.info(
            "Logged Process eRx for order %s (%s) to %s",
            order_part,
            patient_part,
            SENT_ERX_ORDERS_FILE,
        )
    except Exception as e:
        _pf_log.warning("Could not save to %s: %s", SENT_ERX_ORDERS_FILE, e)

# Practice Fusion defaults (override with LOGIN_URL / DASHBOARD_URL in .env)
_DEFAULT_PF_LOGIN = "https://static.practicefusion.com/apps/ehr/index.html#/login"
_DEFAULT_PF_LOCK = "https://static.practicefusion.com/apps/ehr/index.html#/lock"
_DEFAULT_PF_TASKS = "https://static.practicefusion.com/apps/ehr/index.html#/PF/tasks/lists"

# Persistent skip list for orders that trigger "no recent symbol" in preview (prevents infinite loop on same vitamin)
SKIPPED_ORDERS_FILE = "skipped_orders.txt"
# Log of orders where Send eRx was clicked (tab-separated: timestamp, order #, patient, details)
SENT_ERX_ORDERS_FILE = "sent_erx_orders.txt"

# Same Send eRx / preview flow as vitamins; exempt from the blanket GLP skip when text matches.
GLP_VITAMIN_COMBO_RE = re.compile(
    r"Semaglutide 1mg/B12 1mg/ml",
    re.IGNORECASE,
)

GLP_TIRZEPATIDE_GLY_B12_COMBO_RE = re.compile(
    r"TIRZEPATIDE/Glycine/B12 10mg,5mg,1mg/ml",
    re.IGNORECASE,
)

# Semaglutide / Tirzepatide GLP combos: these states skip Send eRx (My Tasks + Save draft).
GLP_RESTRICTED_STATES = frozenset({"LA", "MS", "AR"})

# Detail pane ready: new prescriptions UI + legacy markers
DETAIL_PANE_READY_CSS = (
    'i[data-element="quick-preview-icon"], '
    '[data-element="quick-preview-icon"], '
    '.patient-previews__icon[data-element="quick-preview-icon"], '
    '[data-element="footer-process-btn"], '
    'span[data-element="readonly-qty-value"], '
    '.prescriptions__order-item-qty, '
    '[data-element="medication-header"], '
    '.erx-order-errors, '
    '.detail-pane-body-wrapper'
)
QUICK_PREVIEW_ICON_CSS = (
    'i.patient-previews__icon[data-element="quick-preview-icon"], '
    'i[data-element="quick-preview-icon"], '
    '[data-element="quick-preview-icon"]'
)


_CITY_STATE_ZIP_RE = re.compile(r",\s*([A-Z]{2})\s*\d{5}(?:-\d{4})?\b", re.IGNORECASE)
_LOOSE_STATE_ZIP_RE = re.compile(r"\b([A-Z]{2})\s+\d{5}\b")


def _parse_state_from_text(text: str) -> Optional[str]:
    normalized = re.sub(r"\s+", " ", (text or "").strip())
    m = _CITY_STATE_ZIP_RE.search(normalized)
    if m:
        return m.group(1).upper()
    m2 = _LOOSE_STATE_ZIP_RE.search(normalized)
    if m2:
        return m2.group(1).upper()
    return None


def _extract_patient_state_from_order_metadata(
    driver: webdriver.Chrome,
    log: logging.Logger,
) -> Optional[str]:
    """Parse US state from order metadata patient block (e.g. Columbus, GA 31904)."""
    try:
        block = driver.find_element(By.CSS_SELECTOR, '[data-element="order-metadata-patient"]')
        state = _parse_state_from_text(block.text)
        if state:
            return state
    except NoSuchElementException:
        log.debug("order-metadata-patient block not found for state extraction")
    except Exception as ex:
        log.debug("Could not parse state from order-metadata-patient: %s", ex)
    return None


def _ensure_prescribing_provider(driver: webdriver.Chrome, log: logging.Logger, wait: WebDriverWait) -> bool:
    """Choose prescribing provider when needed, then wait for order-metadata-patient address."""
    placeholder_hints = (
        "select",
        "choose",
        "prescribing provider",
        "required",
    )
    for sel in (
        '[data-element*="prescribing-provider"] button[data-element="split-button-default"]',
        '[data-element="order-metadata-prescribing-provider"] button[data-element="split-button-default"]',
        '[data-element*="prescribing-provider"] .split-button__main-button',
        'button[aria-label*="Prescribing provider"]',
    ):
        try:
            btn = driver.find_element(By.CSS_SELECTOR, sel)
            if not btn.is_displayed():
                continue
            label = ((btn.text or "") + " " + (btn.get_attribute("aria-label") or "")).strip()
            label_lower = label.lower()
            if not label or any(h in label_lower for h in placeholder_hints):
                _native_click(driver, btn)
                log.info("Opened prescribing provider selector")
                time.sleep(0.5)
                for opt_sel in (
                    '[role="option"]',
                    '.composable-select__result',
                    'li.composable-select__result',
                    '.dropdown-menu li a',
                ):
                    for opt in driver.find_elements(By.CSS_SELECTOR, opt_sel):
                        opt_text = (opt.text or "").strip()
                        if opt.is_displayed() and opt_text and len(opt_text) > 2:
                            _native_click(driver, opt)
                            log.info("Selected prescribing provider: %s", opt_text[:80])
                            time.sleep(0.4)
                            break
                    else:
                        continue
                    break
            else:
                log.info("Prescribing provider already set: %s", label[:80])
            break
        except NoSuchElementException:
            continue
        except Exception as prov_err:
            log.debug("Prescribing provider control %s: %s", sel, prov_err)

    try:
        wait.until(
            EC.presence_of_element_located((By.CSS_SELECTOR, '[data-element="order-metadata-patient"]')),
        )
        WebDriverWait(driver, 8).until(
            lambda d: _extract_patient_state_from_order_metadata(d, log) is not None,
        )
        return True
    except TimeoutException:
        log.warning("Patient metadata (order-metadata-patient) not ready after prescribing provider")
        return False


def _check_glp_restricted_state(
    driver: webdriver.Chrome,
    log: logging.Logger,
    wait: WebDriverWait,
    order_num: Optional[str],
) -> bool:
    """After prescribing provider: return False if patient state is LA, MS, or AR (navigates away)."""
    _ensure_prescribing_provider(driver, log, wait)
    patient_state = _extract_patient_state_from_order_metadata(driver, log)
    if patient_state is None:
        log.warning(
            "GLP combo: could not read patient state from order-metadata-patient — continuing (LA/MS/AR skip not applied)",
        )
        return True
    if patient_state in GLP_RESTRICTED_STATES:
        log.info(
            "GLP combo: patient state %s is restricted — navigating to My Tasks",
            patient_state,
        )
        if order_num:
            _save_skipped_order(order_num)
        _navigate_my_tasks_and_save_draft(driver, log)
        return False
    log.info("GLP combo: patient state %s — proceeding", patient_state)
    return True


def _iter_quick_preview_lock_roots(driver: webdriver.Chrome) -> List[Any]:
    """Ancestors of lock icons in quick preview: `div[data-element*='preview-item']` or table row."""
    roots: List[Any] = []
    seen: set[int] = set()
    for icon in driver.find_elements(By.XPATH, '//i[contains(@class,"icon-lock")]'):
        for rel_xpath in (
            './ancestor::div[contains(@data-element,"preview-item")][1]',
            './ancestor::tr[1]',
        ):
            try:
                root = icon.find_element(By.XPATH, rel_xpath)
                k = id(root)
                if k not in seen:
                    seen.add(k)
                    roots.append(root)
                break
            except NoSuchElementException:
                continue
    return roots


def _glp_quick_preview_keywords(
    tirzepatide_glycine_b12_combo: bool,
    semaglutide_b12_combo: bool,
) -> List[str]:
    needles: List[str] = []
    if tirzepatide_glycine_b12_combo:
        needles.append("tirzepatide")
    if semaglutide_b12_combo:
        needles.append("semaglutide")
    return needles


def _find_process_erx_button(driver: webdriver.Chrome) -> Optional[Any]:
    """The real control is the inner `button.btn--brand[data-element=footer-process-btn]`, not the popover wrapper."""
    candidates: List[Any] = []
    for sel in (
        '.detail-pane-footer button[data-element="footer-process-btn"]',
        '.detail-pane button[data-element="footer-process-btn"]',
        'button.btn--brand[data-element="footer-process-btn"]',
    ):
        candidates.extend(driver.find_elements(By.CSS_SELECTOR, sel))
    seen: set[str] = set()
    matched: List[Any] = []
    for btn in candidates:
        key = btn.get_attribute("id") or str(id(btn))
        if key in seen:
            continue
        seen.add(key)
        if btn.tag_name.lower() != "button":
            continue
        if not btn.is_displayed() or not btn.is_enabled():
            continue
        text = (btn.text or "").strip().lower()
        if "process" not in text or "erx" not in text:
            continue
        try:
            rect = btn.rect
            if rect.get("width", 0) < 10 or rect.get("height", 0) < 10:
                continue
        except Exception:
            pass
        matched.append(btn)

    if not matched:
        return None
    if len(matched) == 1:
        return matched[0]

    def _score(btn: Any) -> tuple:
        in_detail = driver.execute_script(
            """
            const b = arguments[0];
            if (b.closest('.detail-pane-footer, .detail-pane, .prescriptions')) return 2;
            const r = b.getBoundingClientRect();
            return r.bottom > window.innerHeight * 0.55 ? 1 : 0;
            """,
            btn,
        )
        return (in_detail, btn.rect.get("y", 0))

    matched.sort(key=_score, reverse=True)
    return matched[0]


def _order_detail_pane_visible(driver: webdriver.Chrome) -> bool:
    try:
        return _find_process_erx_button(driver) is not None
    except Exception:
        return False


def _log_page_context(driver: webdriver.Chrome, log: logging.Logger, label: str) -> None:
    try:
        url = driver.current_url or ""
        hash_part = url.split("#", 1)[-1] if "#" in url else url
        log.info(
            "%s — location: %s — Process eRx visible: %s",
            label,
            hash_part,
            _order_detail_pane_visible(driver),
        )
    except Exception as ex:
        log.debug("%s — could not read page context: %s", label, ex)


def _is_on_patient_summary(url: str) -> bool:
    return "/charts/patients/" in url and "/summary" in url


def _dismiss_quick_preview_overlay(driver: webdriver.Chrome, log: logging.Logger) -> None:
    """Remove only the quick-preview modal (not all carbon-content-modal-component nodes)."""
    try:
        removed = driver.execute_script("""
            let n = 0;
            document.querySelectorAll('.carbon-content-modal-component').forEach(el => {
                const isPreview = el.querySelector(
                    '[data-element*="preview-item"], .patient-previews, .icon-lock, [data-element="quick-preview-icon"]'
                );
                if (isPreview) { el.remove(); n++; }
            });
            document.querySelectorAll('.modal-backdrop.in, .modal-backdrop, .in.copy-modal, .copy-modal')
                .forEach(el => { el.remove(); });
            return n;
        """)
        log.info("Dismissed quick preview overlay (DOM only, removed %s preview modal(s))", removed)
        time.sleep(0.3)
    except Exception as ex:
        log.warning("Could not dismiss quick preview overlay: %s", ex)


def _native_click(driver: webdriver.Chrome, element: Any) -> None:
    """Click the element itself (not a parent composable-popover wrapper)."""
    driver.execute_script(
        "arguments[0].scrollIntoView({block: 'center', inline: 'center'});",
        element,
    )
    time.sleep(0.15)
    try:
        ActionChains(driver).move_to_element(element).pause(0.1).click(element).perform()
    except Exception:
        driver.execute_script(
            """
            const el = arguments[0];
            el.focus();
            for (const type of ['pointerdown', 'mousedown', 'pointerup', 'mouseup', 'click']) {
                el.dispatchEvent(new MouseEvent(type, {bubbles: true, cancelable: true, view: window}));
            }
            """,
            element,
        )


def _confirm_process_erx_popover(driver: webdriver.Chrome, log: logging.Logger) -> bool:
    """If Process eRx opens a composable popover, click confirm (fresh DOM query — avoids stale refs)."""
    try:
        clicked = driver.execute_script(
            """
            const mainBtn = document.querySelector(
                'button[data-element="footer-process-btn"]'
            );
            if (!mainBtn) return false;
            const wrap = mainBtn.closest('.ember-view');
            if (!wrap) return false;
            const pop = wrap.querySelector('.content-popover');
            if (!pop) return false;
            for (const b of pop.querySelectorAll('button')) {
                if (b.offsetParent === null) continue;
                const t = (b.textContent || '').trim();
                if (/process|confirm|send|submit/i.test(t)) {
                    b.click();
                    return true;
                }
            }
            return false;
            """,
        )
        if clicked:
            log.info("Clicked Process eRx confirmation in popover")
            time.sleep(0.4)
            return True
    except Exception as ex:
        log.debug("No Process eRx popover confirm: %s", ex)
    return False


def _wait_for_process_erx_result(driver: webdriver.Chrome, timeout: int = 12) -> bool:
    """True if we left the detail pane or returned to the tasks list (order was processed)."""
    try:
        WebDriverWait(driver, timeout).until(
            lambda d: (
                "/tasks/lists" in (d.current_url or "")
                or _find_process_erx_button(d) is None
            ),
        )
        return True
    except TimeoutException:
        return False


def _click_process_erx_button(driver: webdriver.Chrome, log: logging.Logger) -> bool:
    """Click the footer Process eRx `button` (re-find each attempt to avoid stale element errors)."""
    for attempt in range(1, 4):
        btn = _find_process_erx_button(driver)
        if btn is None:
            log.warning("Process eRx button not found (attempt %d/3)", attempt)
            time.sleep(0.5)
            continue
        try:
            btn_id = btn.get_attribute("id") or "(no id)"
            btn_text = (btn.text or "").strip()
            log.info(
                "Clicking Process eRx button (attempt %d/3): id=%s text=%r",
                attempt,
                btn_id,
                btn_text,
            )
            _native_click(driver, btn)
        except StaleElementReferenceException:
            log.debug("Process eRx button went stale before click — re-finding (attempt %d)", attempt)
            time.sleep(0.4)
            continue
        time.sleep(0.5)
        _confirm_process_erx_popover(driver, log)
        if _wait_for_process_erx_result(driver, timeout=10):
            log.info("Process eRx completed (left detail pane or returned to tasks)")
            return True
        log.debug("Process eRx not finished after attempt %d — retrying", attempt)
        time.sleep(0.4)

    log.warning("Process eRx click did not complete after retries")
    return False


def _script_date_today_display() -> str:
    return datetime.now().strftime("%m/%d/%Y")


def _script_date_needs_fix(driver: webdriver.Chrome) -> bool:
    """True if script date field shows an error or is not today's date."""
    today_variants = {
        _script_date_today_display(),
        datetime.now().strftime("%m/%d/%y"),
    }
    try:
        err_blocks = driver.find_elements(
            By.CSS_SELECTOR,
            '.prescriptions__order-item-script-date.prescriptions__order-item-input--error, '
            '.prescriptions__order-item-script-date[class*="--error"]',
        )
        if any(el.is_displayed() for el in err_blocks):
            return True
    except Exception:
        pass
    try:
        icons = driver.find_elements(By.CSS_SELECTOR, '[data-element="script-date-error-icon"]')
        if any(el.is_displayed() for el in icons):
            return True
    except Exception:
        pass
    try:
        inp = driver.find_element(
            By.CSS_SELECTOR,
            '[data-element="script-date-input"] input.input--date-time, '
            '[data-element="script-date-input"] input[type="text"]',
        )
        val = (inp.get_attribute("value") or "").strip()
        if not val or val not in today_variants:
            return True
    except NoSuchElementException:
        return True
    return False


def _select_calendar_today(driver: webdriver.Chrome, log: logging.Logger) -> bool:
    iso_today = datetime.now().strftime("%Y-%m-%d")
    try:
        day_btn = WebDriverWait(driver, 8).until(
            EC.element_to_be_clickable((By.CSS_SELECTOR, f'button[data-date="{iso_today}"]')),
        )
        _native_click(driver, day_btn)
        log.info("Selected script date %s in calendar", iso_today)
        time.sleep(0.3)
        return True
    except TimeoutException:
        try:
            day_btn = driver.find_element(
                By.CSS_SELECTOR,
                'button.ember-power-calendar-day--today.ember-power-calendar-day--interactive',
            )
            _native_click(driver, day_btn)
            log.info("Selected calendar cell marked as today")
            time.sleep(0.3)
            return True
        except Exception as day_err:
            log.warning("Could not select today's date in calendar: %s", day_err)
            return False


def _click_ready_to_process(driver: webdriver.Chrome, log: logging.Logger, timeout: int = 8) -> bool:
    """Click Ready to process after script date (required before Process eRx)."""
    selectors = (
        '[data-element="ready-select-split-btn"] button[data-element="split-button-default"]',
        '[data-element="ready-select-split-btn"] button.split-button__main-button',
        '[data-element="ready-select-split-btn"] button[aria-label="Ready to process"]',
        'button.split-button__main-button--default[aria-label="Ready to process"]',
    )
    for sel in selectors:
        try:
            btn = WebDriverWait(driver, timeout).until(
                EC.element_to_be_clickable((By.CSS_SELECTOR, sel)),
            )
            label = ((btn.text or "") + " " + (btn.get_attribute("aria-label") or "")).lower()
            if "ready" not in label or "process" not in label:
                continue
            _native_click(driver, btn)
            log.info("Clicked Ready to process")
            time.sleep(0.4)
            return True
        except TimeoutException:
            continue
        except Exception:
            continue
    try:
        btn = WebDriverWait(driver, 3).until(
            EC.element_to_be_clickable((
                By.XPATH,
                '//div[@data-element="ready-select-split-btn"]//button[contains(normalize-space(.),"Ready to process")]',
            )),
        )
        _native_click(driver, btn)
        log.info("Clicked Ready to process (XPath)")
        time.sleep(0.4)
        return True
    except TimeoutException:
        log.warning("Ready to process button not found")
        return False


def _set_script_date_then_ready_to_process(driver: webdriver.Chrome, log: logging.Logger) -> None:
    """Always set script date to today, then click Ready to process before Process eRx."""
    log.info("Script date → Ready to process (before Process eRx)")
    _ensure_script_date_today(driver, log)
    if not _click_ready_to_process(driver, log):
        log.warning("Ready to process was not clicked — Process eRx may not work")


def _ensure_script_date_today(driver: webdriver.Chrome, log: logging.Logger) -> tuple[bool, bool]:
    """Always set Script date to today via the prescriptions date picker (new UI).

    Returns (success, date_was_set) — date_was_set is True when today was applied.
    """
    today_str = _script_date_today_display()
    log.info("Setting script date to today (%s)", today_str)
    try:
        date_root = driver.find_element(By.CSS_SELECTOR, '[data-element="script-date-input"]')
        driver.execute_script("arguments[0].scrollIntoView({block: 'center'});", date_root)
        time.sleep(0.2)
    except NoSuchElementException:
        log.warning("Script date input [data-element=script-date-input] not found")
        return False, True

    opened = False
    for sel in (
        '[data-element="script-date-input"] button[data-element="btn-calendar-icon"]',
        '[data-element="script-date-input"] .date-picker__icon',
        '.prescriptions__order-item-script-date i.icon-calendar',
    ):
        try:
            cal_btn = driver.find_element(By.CSS_SELECTOR, sel)
            if cal_btn.is_displayed():
                _native_click(driver, cal_btn)
                log.info("Opened script date calendar")
                opened = True
                time.sleep(0.4)
                break
        except NoSuchElementException:
            continue

    if opened and _select_calendar_today(driver, log):
        time.sleep(0.3)
        if not _script_date_needs_fix(driver):
            log.info("Script date set to today via calendar")
            return True, True
        log.warning("Calendar pick did not leave script date as today — trying input fallback")

    # Fallback: type directly into the date input
    try:
        inp = driver.find_element(
            By.CSS_SELECTOR,
            '[data-element="script-date-input"] input.input--date-time, '
            '[data-element="script-date-input"] input[type="text"]',
        )
        _native_click(driver, inp)
        inp.clear()
        inp.send_keys(today_str)
        driver.execute_script(
            "arguments[0].dispatchEvent(new Event('change', {bubbles: true}));"
            "arguments[0].dispatchEvent(new Event('input', {bubbles: true}));",
            inp,
        )
        time.sleep(0.4)
        if not _script_date_needs_fix(driver):
            log.info("Script date set via input to %s", today_str)
            return True, True
    except Exception as inp_err:
        log.warning("Could not set script date via input: %s", inp_err)

    log.warning("Script date may still not be today after attempted fix")
    return False, True


def _restore_order_detail_after_preview(
    driver: webdriver.Chrome,
    log: logging.Logger,
    url_before_preview: str,
) -> bool:
    """If preview opened or closed onto patient summary, go back to the order detail view."""
    if _order_detail_pane_visible(driver):
        return True
    try:
        current = driver.current_url or ""
    except Exception:
        return False
    if not _is_on_patient_summary(current) and current == url_before_preview:
        return _order_detail_pane_visible(driver)
    if _is_on_patient_summary(current) or current != url_before_preview:
        log.info("Left order detail during preview (now: %s) — using browser back", current.split("#")[-1])
        try:
            driver.back()
            WebDriverWait(driver, 8).until(
                lambda d: _order_detail_pane_visible(d) or (d.current_url or "") != current,
            )
            time.sleep(0.4)
        except Exception as back_err:
            log.warning("browser.back() after preview did not restore detail pane: %s", back_err)
    _log_page_context(driver, log, "After restoring order detail")
    return _order_detail_pane_visible(driver)


def _dismiss_modal_backdrops_only(driver: webdriver.Chrome) -> None:
    """Remove click-blocking backdrops only; do not remove modals or dispatch Escape."""
    try:
        driver.execute_script("""
            document.querySelectorAll(
                '.modal-backdrop.in, .modal-backdrop, .in.copy-modal, .copy-modal'
            ).forEach(el => { el.style.pointerEvents = 'none'; el.remove(); });
        """)
    except Exception:
        pass


def _save_unsaved_changes_modal(driver: webdriver.Chrome, log: logging.Logger, timeout: int = 6) -> bool:
    """Click Save on the Unsaved changes modal when leaving an order with edits."""
    try:
        modal = WebDriverWait(driver, timeout).until(
            EC.visibility_of_element_located((
                By.CSS_SELECTOR,
                '[data-element="order-unsaved-changes-warning"]',
            )),
        )
        save_btn = modal.find_element(
            By.CSS_SELECTOR,
            'button[data-element="unsaved-changes-attempt-save-and-transition"]',
        )
        _native_click(driver, save_btn)
        log.info("Clicked Save on Unsaved changes modal")
        try:
            WebDriverWait(driver, 10).until(
                EC.invisibility_of_element_located((
                    By.CSS_SELECTOR,
                    '[data-element="order-unsaved-changes-warning"]',
                )),
            )
        except TimeoutException:
            pass
        time.sleep(0.8)
        return True
    except TimeoutException:
        return False
    except Exception as ex:
        log.warning("Could not save via Unsaved changes modal: %s", ex)
        return False


def _navigate_my_tasks_and_save_draft(
    driver: webdriver.Chrome,
    log: logging.Logger,
    cfg: Optional[Dict[str, Any]] = None,
) -> None:
    """Navigate back to My Tasks; save via Unsaved changes modal if script date (etc.) was edited."""
    tasks_url = "https://static.practicefusion.com/apps/ehr/index.html#/PF/tasks/lists"
    try:
        driver.get(tasks_url)
        log.info("Triggered navigation to My Tasks")
        if cfg and not ensure_practice_fusion_session(driver, cfg, log):
            log.error("Session expired while navigating to My Tasks")
            return
    except Exception as nav_err:
        log.warning("Could not navigate to tasks list: %s", nav_err)

    if _save_unsaved_changes_modal(driver, log):
        log.info("Saved order changes and left detail pane")
    else:
        log.info("Navigated to My Tasks (no Unsaved changes prompt)")

    if "/tasks/lists" not in (driver.current_url or ""):
        try:
            driver.get(tasks_url)
            _save_unsaved_changes_modal(driver, log, timeout=4)
            time.sleep(0.5)
        except Exception:
            pass


def _load_browser_config() -> Dict[str, Any]:
    return {
        "LOGIN_URL": os.getenv("LOGIN_URL", _DEFAULT_PF_LOGIN),
        "DASHBOARD_URL": os.getenv("DASHBOARD_URL", _DEFAULT_PF_TASKS),
        "USERNAME": os.getenv("DOCTOR_USERNAME"),
        "PASSWORD": os.getenv("DOCTOR_PASSWORD"),
        "HEADLESS": os.getenv("HEADLESS", "false").lower() == "true",
        "WAIT_TIMEOUT": int(os.getenv("WAIT_TIMEOUT", "30")),
        "LOGIN_USERNAME_SELECTOR": os.getenv(
            "LOGIN_USERNAME_SELECTOR",
            '#inputUsername, input[type="email"]',
        ),
        "LOGIN_PASSWORD_SELECTOR": os.getenv(
            "LOGIN_PASSWORD_SELECTOR",
            '#inputPswd, #inputPassword, input[type="password"]',
        ),
        "LOGIN_BUTTON_SELECTOR": os.getenv(
            "LOGIN_BUTTON_SELECTOR",
            '#loginButton, button.btn-login',
        ),
    }


def _build_chrome_driver(cfg: Dict[str, Any], log: logging.Logger) -> webdriver.Chrome:
    """Match shiptag: Selenium Manager resolves ChromeDriver (no webdriver-manager install step)."""
    t0 = time.perf_counter()
    chrome_options = Options()
    if cfg["HEADLESS"]:
        chrome_options.add_argument("--headless=new")

    user_data_dir = os.path.join(os.path.expanduser("~"), "chrome_debug_profile")
    chrome_options.add_argument(f"--user-data-dir={user_data_dir}")
    chrome_options.add_argument("--profile-directory=Default")

    chrome_options.add_argument("--no-sandbox")
    chrome_options.add_argument("--disable-dev-shm-usage")
    chrome_options.add_argument("--disable-blink-features=AutomationControlled")
    # Quieter Chromium stderr (DevTools / GCM messages still may appear from Chrome itself)
    chrome_options.add_argument("--log-level=3")
    chrome_options.add_experimental_option(
        "excludeSwitches",
        ["enable-automation", "enable-logging"],
    )
    chrome_options.add_experimental_option("useAutomationExtension", False)

    service = Service(log_output=subprocess.DEVNULL)
    driver = webdriver.Chrome(service=service, options=chrome_options)
    # Explicit waits only — implicit wait stacks with WebDriverWait and slows every lookup (unlike shiptag).
    driver.implicitly_wait(0)
    log.info("Chrome session started in %.2fs (implicit_wait=0)", time.perf_counter() - t0)
    return driver


def _is_pf_url(url: str) -> bool:
    return "practicefusion" in (url or "").lower()


def _is_pf_lock_or_login_url(url: str) -> bool:
    """True when Practice Fusion logged out or locked the session after idle timeout."""
    u = (url or "").lower()
    return "#/login" in u or "#/lock" in u


def _is_pf_lock_screen(driver: webdriver.Chrome) -> bool:
    """Lock screen: readonly email, password only, #unlockButton (not #loginButton)."""
    if "#/lock" in (driver.current_url or "").lower():
        return True
    try:
        return driver.find_element(By.ID, "unlockButton").is_displayed()
    except NoSuchElementException:
        return False


def ensure_practice_fusion_session(
    driver: webdriver.Chrome,
    cfg: Dict[str, Any],
    log: Optional[logging.Logger] = None,
) -> bool:
    """Re-authenticate if on PF login or lock screen (unlock vs full login)."""
    log = log or _pf_log
    url = driver.current_url or ""
    if not _is_pf_lock_or_login_url(url) and not _is_pf_lock_screen(driver):
        return True
    hash_part = url.split("#", 1)[-1] if "#" in url else url
    if _is_pf_lock_screen(driver):
        log.warning("Practice Fusion session locked (#%s) — unlocking", hash_part)
        return _unlock_pf_screen(driver, cfg, log)
    log.warning("Practice Fusion session ended (#%s) — logging in", hash_part)
    return login_practice_fusion(driver, cfg, log)


def _find_pf_password_field(driver: webdriver.Chrome) -> Optional[Any]:
    for pwd_id in ("inputPswd", "inputPassword"):
        try:
            el = driver.find_element(By.ID, pwd_id)
            if el.is_displayed():
                return el
        except NoSuchElementException:
            continue
    try:
        el = driver.find_element(By.CSS_SELECTOR, 'input[type="password"]')
        if el.is_displayed():
            return el
    except NoSuchElementException:
        pass
    return None


def _pf_navigate_to_tasks_after_auth(
    driver: webdriver.Chrome,
    cfg: Dict[str, Any],
    wait: WebDriverWait,
    log: logging.Logger,
    overall_start: float,
    auth_label: str,
) -> bool:
    t = time.perf_counter()
    log.info("Navigating to tasks page: %s", cfg["DASHBOARD_URL"])
    driver.get(cfg["DASHBOARD_URL"])
    try:
        wait.until(
            EC.presence_of_element_located(
                (By.CSS_SELECTOR, ".composable-header__nav-tab, .task-list, [role='tab'], table.data-table__grid")
            )
        )
        log.info("Tasks page loaded successfully")
    except TimeoutException:
        log.warning("Tasks page did not fully load within timeout")
    log.info(
        "Tasks page ready in %.2fs; total PF %s %.2fs",
        time.perf_counter() - t,
        auth_label,
        time.perf_counter() - overall_start,
    )
    return True


def _unlock_pf_screen(driver: webdriver.Chrome, cfg: Dict[str, Any], log: logging.Logger) -> bool:
    """Unlock idle lock screen: password + #unlockButton (email is readonly)."""
    wait = WebDriverWait(driver, cfg["WAIT_TIMEOUT"])
    overall = time.perf_counter()

    if not _is_pf_lock_screen(driver):
        t = time.perf_counter()
        driver.get(_DEFAULT_PF_LOCK)
        log.info("GET lock URL finished in %.2fs", time.perf_counter() - t)

    t = time.perf_counter()
    wait.until(EC.presence_of_element_located((By.ID, "inputPswd")))
    log.info("Lock screen ready (inputPswd) in %.2fs", time.perf_counter() - t)

    pwd = _find_pf_password_field(driver)
    if pwd is None:
        log.error("No password field found on lock screen (#inputPswd)")
        return False
    pwd.clear()
    pwd.send_keys(cfg["PASSWORD"] or "")
    log.info("Password entered for unlock")

    initial_url = driver.current_url
    try:
        unlock_btn = wait.until(EC.element_to_be_clickable((By.ID, "unlockButton")))
        log.info("Clicking unlockButton")
        unlock_btn.click()
    except TimeoutException:
        log.error("unlockButton not found or not clickable on lock screen")
        return False

    t = time.perf_counter()
    try:
        wait.until(lambda d: not _is_pf_lock_or_login_url(d.current_url or ""))
        log.info("Post-unlock URL change in %.2fs", time.perf_counter() - t)
    except TimeoutException:
        if (driver.current_url or "") == initial_url:
            log.error("Timed out after %.2fs waiting for URL to change away from lock", time.perf_counter() - t)
            return False
        log.info("URL changed after unlock (hash may still mention lock) in %.2fs", time.perf_counter() - t)

    return _pf_navigate_to_tasks_after_auth(driver, cfg, wait, log, overall, "unlock")


def _login_pf_fast(driver: webdriver.Chrome, cfg: Dict[str, Any], log: logging.Logger) -> bool:
    """Same flow as shiptag.connect_to_practicefusion, plus .env username/password when fields are empty."""
    wait = WebDriverWait(driver, cfg["WAIT_TIMEOUT"])
    overall = time.perf_counter()

    t = time.perf_counter()
    driver.get(cfg["LOGIN_URL"])
    log.info("GET login URL finished in %.2fs", time.perf_counter() - t)

    t = time.perf_counter()
    username_field = wait.until(EC.presence_of_element_located((By.ID, "inputUsername")))
    log.info("Login form ready (inputUsername) in %.2fs", time.perf_counter() - t)

    if _is_pf_lock_screen(driver):
        log.info("Lock screen detected at login URL — using unlock flow")
        return _unlock_pf_screen(driver, cfg, log)

    # Full login: username is editable; always apply .env credentials.
    if username_field.get_attribute("readonly"):
        log.info("Username field is readonly — skipping username entry")
    else:
        username_field.clear()
        username_field.send_keys(cfg["USERNAME"] or "")
        log.info("Username entered from .env")

    pwd = _find_pf_password_field(driver)
    if pwd is not None:
        pwd.clear()
        pwd.send_keys(cfg["PASSWORD"] or "")
        log.info("Password entered from .env")
    else:
        log.error("No password field found (Practice Fusion uses #inputPswd)")
        return False

    initial_url = driver.current_url
    log.debug("URL before submit: %s", initial_url)

    try:
        login_button = driver.find_element(By.ID, "loginButton")
        if login_button.is_enabled():
            log.info("Clicking loginButton (enabled)")
            login_button.click()
        else:
            log.info("loginButton present but disabled — waiting for URL change anyway")
    except NoSuchElementException:
        log.error("loginButton not found")
        return False

    t = time.perf_counter()
    try:
        wait.until(lambda d: not _is_pf_lock_or_login_url(d.current_url or ""))
        log.info("Post-login URL change in %.2fs", time.perf_counter() - t)
    except TimeoutException:
        log.error("Timed out after %.2fs waiting for URL to change away from login", time.perf_counter() - t)
        return False

    return _pf_navigate_to_tasks_after_auth(driver, cfg, wait, log, overall, "login")


def _find_first_displayed(driver: webdriver.Chrome, selectors: List[str], timeout: float) -> Optional[Any]:
    end = time.time() + timeout
    while time.time() < end:
        for sel in selectors:
            sel = sel.strip()
            if not sel:
                continue
            try:
                el = driver.find_element(By.CSS_SELECTOR, sel)
                if el.is_displayed():
                    return el
            except NoSuchElementException:
                continue
        time.sleep(0.05)
    return None


def _fill_username_password(
    driver: webdriver.Chrome,
    cfg: Dict[str, Any],
    wait: WebDriverWait,
    log: logging.Logger,
) -> bool:
    username_selectors = [s.strip() for s in cfg["LOGIN_USERNAME_SELECTOR"].split(",") if s.strip()]
    t = time.perf_counter()
    user_el = _find_first_displayed(driver, username_selectors, timeout=min(10, cfg["WAIT_TIMEOUT"]))
    log.info("Username field resolved in %.2fs", time.perf_counter() - t)
    if not user_el:
        return False
    user_el.clear()
    user_el.send_keys(cfg["USERNAME"] or "")

    password_selectors = [s.strip() for s in cfg["LOGIN_PASSWORD_SELECTOR"].split(",") if s.strip()]
    pwd_el = _find_first_displayed(driver, password_selectors, timeout=2.0)

    if not pwd_el:
        for sel in [s.strip() for s in cfg["LOGIN_BUTTON_SELECTOR"].split(",") if s.strip()]:
            try:
                btn = driver.find_element(By.CSS_SELECTOR, sel)
                if btn.is_displayed() and btn.is_enabled():
                    btn.click()
                    break
            except NoSuchElementException:
                continue
        pwd_el = _find_first_displayed(driver, password_selectors, timeout=float(cfg["WAIT_TIMEOUT"]))

    if pwd_el and cfg["PASSWORD"]:
        pwd_el.clear()
        pwd_el.send_keys(cfg["PASSWORD"])
        log.info("Password field filled")
    return True


def _click_login_button(driver: webdriver.Chrome, cfg: Dict[str, Any], wait: WebDriverWait, log: logging.Logger) -> bool:
    selectors = [s.strip() for s in cfg["LOGIN_BUTTON_SELECTOR"].split(",") if s.strip()]
    for sel in selectors:
        try:
            btn = wait.until(EC.element_to_be_clickable((By.CSS_SELECTOR, sel)))
            log.info("Clicking login selector: %s", sel)
            btn.click()
            return True
        except TimeoutException:
            continue
    return False


def login_practice_fusion(driver: webdriver.Chrome, cfg: Dict[str, Any], log: Optional[logging.Logger] = None) -> bool:
    log = log or _pf_log
    if not cfg["USERNAME"] or not cfg["PASSWORD"]:
        return False

    if _is_pf_url(cfg["LOGIN_URL"]):
        return _login_pf_fast(driver, cfg, log)

    wait = WebDriverWait(driver, cfg["WAIT_TIMEOUT"])
    log.info("Generic login path (non–Practice Fusion LOGIN_URL)")
    driver.get(cfg["LOGIN_URL"])

    if not _fill_username_password(driver, cfg, wait, log):
        log.error("Could not resolve username field")
        return False

    if not _click_login_button(driver, cfg, wait, log):
        log.error("Could not click login button")
        return False

    try:
        wait.until(lambda d: not _is_pf_lock_or_login_url(d.current_url or ""))
    except TimeoutException:
        log.error("Timeout waiting for login navigation")
        return False

    driver.get(cfg["DASHBOARD_URL"])
    try:
        wait.until(
            EC.presence_of_element_located(
                (By.CSS_SELECTOR, "[data-element='patient-search-input'] input")
            )
        )
    except TimeoutException:
        log.warning("Charts patient-search selector not found; continuing")
    return True


def process_vitamin_tasks(
    driver: webdriver.Chrome,
    log: logging.Logger,
    cfg: Optional[Dict[str, Any]] = None,
) -> int:
    """Scan My Tasks table (virtualized with occluded-content), find vitamin orders (and the
    Semaglutide 1mg/B12 1mg/ml and TIRZEPATIDE/Glycine/B12 10mg,5mg,1mg/ml (latter gates on Dispense 1–2).
    Both GLP combos skip Send eRx for patient states LA, MS, AR (My Tasks + Save draft).
    Other GLP-only rows are skipped.
    Progressive approach: scans initial ~50 tasks. If none found, performs **one scroll**
    at a time, rescans the expanded viewport, and repeats until a vitamin is processed
    or the list is exhausted. Much more efficient when vitamins appear early.

    When ``cfg`` is provided, re-authenticates if PF redirected to login/lock.
    """
    log.info("Starting vitamin task processor on My Tasks page...")
    if cfg and not ensure_practice_fusion_session(driver, cfg, log):
        log.error("Could not restore Practice Fusion session — skipping this scan cycle")
        return 0

    VITAMIN_KEYWORDS = {
        "glutathione", "nad", "nicotinamide", "vitamin", "b12", "methylcobalamin",
        "ascorbic", "niacin", "carnitine", "l-carnitine", "homekit", "mic", "lipo", "skinny",
        "folic", "folate", "b9",  # Folic Acid (B9)
        "zinc",  # e.g. Zinc Sulfate injections
        # B-Complex: row text is "B-Complex Injection ..." — no substring "vitamin"
        "b-complex", "b complex",
        "powershot",
        "glycine", "acetylcysteine", "n-acetylcysteine",
        # Spell-out forms (UI often uses spaces: "N-Acetyl Cysteine" vs NAC one-word)
        "acetyl cysteine", "n-acetyl",
        "biotin",
    }
    GLP_KEYWORDS = {"tirzepatide", "semaglutide", "glp", "ozempic", "wegovy", "mounjaro", "weight loss"}

    wait = WebDriverWait(driver, 15)

    processed = 0
    skipped_orders = _load_skipped_orders()
    if skipped_orders:
        log.info("Loaded %d previously skipped orders (will not re-process them)", len(skipped_orders))

    try:
        log.info("Waiting for tasks table...")
        # More robust table detection matching your HTML exactly
        table = wait.until(EC.presence_of_element_located((
            By.CSS_SELECTOR,
            'table[data-element="tasks-table-table"], table.data-table__grid, .data-table__container table'
        )))
        log.info("Tasks table found successfully")

        # Parse total task count from header (e.g. "My tasks (236)" or column header "50 tasks")
        total_tasks = 0
        try:
            # Check nav header first (most accurate)
            header_link = driver.find_elements(By.CSS_SELECTOR, 'a.composable-header__nav-link.active, a.composable-header__nav-link')
            for link in header_link:
                text = link.text.strip()
                if "My tasks" in text or "tasks" in text.lower():
                    match = re.search(r'\((\d+)\)', text)
                    if match:
                        total_tasks = int(match.group(1))
                        break
            if not total_tasks:
                # Fallback to column header
                task_header = driver.find_elements(By.CSS_SELECTOR, '[data-element="tasks-table-header-count"], .data-table__column.task-row__task')
                for el in task_header:
                    text = el.text.strip()
                    if any(c.isdigit() for c in text):
                        match = re.search(r'(\d+)', text)
                        if match:
                            total_tasks = int(match.group(1))
                            break
            if total_tasks:
                log.info("Total tasks in My Tasks: %d", total_tasks)
            else:
                log.warning("Could not parse total task count from header")
        except Exception as count_err:
            log.debug("Failed to parse total tasks count: %s", count_err)

        # Progressive 1-by-1 scrolling + scanning for virtual table (occluded-content).
        # Scans initial viewport (~50 tasks). If no vitamins found, does ONE scroll,
        # rescans the expanded list (~100 tasks), and repeats until a vitamin is found
        # or we exhaust the list / hit max scrolls.
        scroller = None
        try:
            scroller_selectors = [
                '[data-element="data-table-scroller"]',
                '.data-table__scroller',
                '.data-table__container',
                'div[data-element="data-table-scroller"]'
            ]
            for sel in scroller_selectors:
                try:
                    elements = driver.find_elements(By.CSS_SELECTOR, sel)
                    for el in elements:
                        if el.is_displayed():
                            scroller = el
                            break
                    if scroller:
                        break
                except:
                    continue
        except Exception as e:
            log.debug("Scroller detection failed: %s", e)

        max_scrolls = 8  # Covers ~400+ tasks safely
        rows_scanned = 0
        scrolls_performed = 0

        if scroller and total_tasks > 50:
            log.info("Starting progressive scroll+scan (initial viewport + 1 scroll per cycle if needed)")
        else:
            log.info("Using initial viewport only (small task list or no scroller)")

        # Main progressive loop
        while True:
            # Get current rows in viewport
            rows = driver.find_elements(By.CSS_SELECTOR, 'tr[data-element^="data-table-row-"], tr.task-row, tr[aria-rowindex]')
            current_count = len(rows)
            log.info("Scanning %d visible task rows (scrolls so far: %d)", current_count, scrolls_performed)

            found_vitamin_this_pass = False

            for i, row in enumerate(rows):
                try:
                    # Get details cell (4th column - Details)
                    details_cell = row.find_elements(By.TAG_NAME, "td")[3] if len(row.find_elements(By.TAG_NAME, "td")) > 3 else None
                    if not details_cell:
                        continue

                    # Get the raw text content (most reliable for medication name)
                    raw_text = ""
                    try:
                        raw_text_el = details_cell.find_element(By.CSS_SELECTOR, '.raw-text, div.raw-text, [data-element="task-details"] .raw-text')
                        raw_text = raw_text_el.text.strip()
                    except:
                        try:
                            details_div = details_cell.find_element(By.CSS_SELECTOR, '[data-element="task-details"], .expanding-text')
                            raw_text = details_div.text.strip()
                        except:
                            raw_text = details_cell.text.strip()
                    if not raw_text:
                        raw_text = details_cell.text.strip()

                    lower_text = raw_text.lower()
                    is_vitamin = any(kw in lower_text for kw in VITAMIN_KEYWORDS)
                    is_glp = any(kw in lower_text for kw in GLP_KEYWORDS)
                    is_glp_vitamin_combo = bool(GLP_VITAMIN_COMBO_RE.search(raw_text))
                    is_tirzepatide_gly_combo = bool(GLP_TIRZEPATIDE_GLY_B12_COMBO_RE.search(raw_text))

                    if (is_vitamin and not is_glp) or is_glp_vitamin_combo or is_tirzepatide_gly_combo:
                        # Extract Order # for skip list (e.g. D1D8KM)
                        order_match = re.search(r'Order #?([A-Z0-9]+)', raw_text, re.IGNORECASE)
                        order_num = order_match.group(1).upper() if order_match else None

                        if order_num and order_num in skipped_orders:
                            log.info("Skipping previously skipped order %s (no symbol on previous attempt)", order_num)
                            continue

                        patient_name = _extract_patient_name_from_task_row(row)
                        log.info(
                            "Found vitamin task #%d: %s%s",
                            i + 1,
                            raw_text[:100],
                            f" — patient: {patient_name}" if patient_name else "",
                        )
                        found_vitamin_this_pass = True

                        # Find Finish button in the same row's Actions column (last td)
                        actions_cell = row.find_elements(By.TAG_NAME, "td")[-1]
                        finish_btn = None
                        try:
                            # Primary selector from your HTML
                            finish_btn = actions_cell.find_element(By.CSS_SELECTOR, 'button[data-element="split-button-default"], button[aria-label="Finish"]')
                        except NoSuchElementException:
                            # Fallback: any button containing "Finish"
                            buttons = actions_cell.find_elements(By.TAG_NAME, "button")
                            for btn in buttons:
                                text = btn.text.strip()
                                aria = btn.get_attribute("aria-label") or ""
                                if "Finish" in text or "Finish" in aria:
                                    finish_btn = btn
                                    log.debug("Found Finish button via fallback")
                                    break

                        if finish_btn:
                            log.info("Clicking Finish for vitamin task")
                            finish_btn.click()
                            time.sleep(2)

                            # Handle the full order detail flow (passes order_num for skipping on "no symbol")
                            process_erx_ok = complete_order_detail_flow(
                                driver,
                                log,
                                order_num=order_num,
                                order_details=raw_text,
                                patient_name=patient_name,
                                tirzepatide_glycine_b12_combo=is_tirzepatide_gly_combo,
                                semaglutide_b12_combo=is_glp_vitamin_combo,
                            )
                            if process_erx_ok:
                                processed += 1

                            # Return to tasks list if needed
                            if "/tasks" not in (driver.current_url or ""):
                                log.info("Returning to tasks list after order completion")
                                driver.get("https://static.practicefusion.com/apps/ehr/index.html#/PF/tasks/lists")
                                if cfg and not ensure_practice_fusion_session(driver, cfg, log):
                                    log.error("Session expired while returning to tasks — aborting scan")
                                    return processed
                                WebDriverWait(driver, 10).until(
                                    EC.presence_of_element_located((By.CSS_SELECTOR, 'table[data-element="tasks-table-table"], .data-table__grid'))
                                )
                                time.sleep(2)
                        else:
                            log.warning("No Finish button found for row")
                        break  # After processing one vitamin, return to outer automation loop
                    else:
                        log.debug("Skipping non-vitamin task: %s", raw_text[:60])
                except Exception as row_err:
                    log.debug("Error processing row %d: %s", i, row_err)
                    continue

            rows_scanned = max(rows_scanned, current_count)

            # Decide whether to continue with another scroll
            if found_vitamin_this_pass or processed > 0:
                break
            if not scroller or scrolls_performed >= max_scrolls or (total_tasks > 0 and rows_scanned >= total_tasks):
                log.info("No vitamins found after %d scrolls (%d rows scanned).", scrolls_performed, rows_scanned)
                break

            # Perform ONE incremental scroll and continue
            try:
                driver.execute_script("arguments[0].scrollTop = arguments[0].scrollHeight;", scroller)
                time.sleep(1.0)
                # Small back-and-forth to help trigger virtual rendering
                driver.execute_script("arguments[0].scrollTop = Math.max(0, arguments[0].scrollHeight - 600);", scroller)
                time.sleep(0.6)
                driver.execute_script("arguments[0].scrollTop = arguments[0].scrollHeight;", scroller)
                time.sleep(0.8)
                scrolls_performed += 1
                log.info("Performed scroll #%d — checking next batch of tasks...", scrolls_performed)
            except Exception as scroll_err:
                log.warning("Scroll failed: %s", scroll_err)
                break

    except Exception as e:
        log.error("Error during vitamin task processing: %s", e)

    log.info("Vitamin task processor completed. Process eRx clicked for %d order(s).", processed)
    return processed


def _read_tirzepatide_qty(driver: webdriver.Chrome, log: logging.Logger) -> Optional[int]:
    """Read Qty from readonly span or editable input in prescriptions order item."""
    sources = (
        (
            "readonly",
            '.prescriptions__order-item-qty span[data-element="readonly-qty-value"]',
            False,
        ),
        ("readonly", 'span[data-element="readonly-qty-value"]', False),
        (
            "input",
            '.prescriptions__order-item-qty input[data-element="qty-input"]',
            True,
        ),
        ("input", 'input[data-element="qty-input"]', True),
    )
    for kind, sel, use_value_attr in sources:
        for el in driver.find_elements(By.CSS_SELECTOR, sel):
            if not el.is_displayed():
                continue
            raw = (el.get_attribute("value") if use_value_attr else (el.text or "")) or ""
            raw = raw.strip()
            if not raw:
                continue
            try:
                qty = int(raw)
                log.info("Read tirzepatide Qty %d from %s", qty, kind)
                return qty
            except ValueError:
                continue
    return None


def complete_order_detail_flow(
    driver: webdriver.Chrome,
    log: logging.Logger,
    order_num: Optional[str] = None,
    order_details: Optional[str] = None,
    patient_name: Optional[str] = None,
    *,
    tirzepatide_glycine_b12_combo: bool = False,
    semaglutide_b12_combo: bool = False,
) -> bool:
    """Handle the right detail pane after clicking Finish on a vitamin order.
    - For TIRZEPATIDE/Glycine/B12 10mg,5mg,1mg/ml: after load, waits 1.5s and reads Qty (`span[data-element="readonly-qty-value"]`).
      Qty must be exactly 1 or 2 to continue preview + Process eRx; otherwise My Tasks + Save draft (skip list if order_num set).
    - Always sets Script date to today via calendar after qty (not only on error).
      Clicks Ready to process before Process eRx after script date is set.
    - For GLP combos: after script date, selects prescribing provider and reads state from order-metadata-patient.
      LA, MS, AR → My Tasks (skip list if order_num set).
    - Opens quick preview to check for recent locked notes symbol.
      GLP combos: same row/preview-item must also contain Tirzepatide or Semaglutide (case-insensitive)
      in its `<p>` lines (e.g. CC line), matching the order type.
    - If NO recent lock found: closes preview modal (X button), navigates to tasks list,
      navigates to My Tasks, **adds the order to skipped_orders.txt**, then returns cleanly.
    - If recent lock IS found: proceeds with Process eRx (script date already set to today).
    - Dismisses preview overlay via DOM removal (no modal close clicks — those navigate to patient summary).

    Returns True only if Process eRx was clicked successfully.
    """
    wait = WebDriverWait(driver, 15)
    log.info("Handling order detail pane...")
    try:
        # Wait for detail pane (quick preview icon is the primary signal in the new UI)
        try:
            wait.until(EC.presence_of_element_located((By.CSS_SELECTOR, DETAIL_PANE_READY_CSS)))
        except TimeoutException as pane_err:
            log.error(
                "Detail pane did not load (expected quick preview icon or footer/qty): %s",
                pane_err,
            )
            raise
        log.info("Detail pane loaded")

        if tirzepatide_glycine_b12_combo:
            dispense_n: Optional[int] = None
            try:
                dispense_n = WebDriverWait(driver, 10).until(
                    lambda d: _read_tirzepatide_qty(d, log),
                )
            except TimeoutException as disp_err:
                log.warning(
                    "Could not read Qty for tirzepatide combo (expected 1 or 2): %s — leaving order (not added to skip list)",
                    disp_err,
                )
                return False
            except Exception as disp_err:
                log.warning(
                    "Could not read Qty for tirzepatide combo: %s — leaving order (not added to skip list)",
                    disp_err,
                )
                return False
            if dispense_n not in (1, 2):
                log.info(
                    "Qty is %s — need 1 or 2 to Process eRx; navigating to My Tasks",
                    dispense_n,
                )
                if order_num:
                    _save_skipped_order(order_num)
                _navigate_my_tasks_and_save_draft(driver, log)
                return False
            log.info("Dispense is %d — proceeding with preview and Send eRx", dispense_n)

        _ensure_script_date_today(driver, log)

        if tirzepatide_glycine_b12_combo or semaglutide_b12_combo:
            if not _check_glp_restricted_state(driver, log, wait, order_num):
                return False

        # === Quick Preview for locked notes check (optimized for speed) ===
        # Uses short timeout to avoid ~15s UI load delays. Non-critical for core Send eRx flow.
        try:
            url_before_preview = driver.current_url or ""
            preview_wait = WebDriverWait(driver, 8)
            preview_icon = preview_wait.until(EC.element_to_be_clickable((
                By.CSS_SELECTOR, QUICK_PREVIEW_ICON_CSS,
            )))
            driver.execute_script("arguments[0].scrollIntoView({block: 'center'});", preview_icon)
            time.sleep(0.2)
            try:
                preview_icon.click()
            except Exception:
                driver.execute_script("arguments[0].click();", preview_icon)
            log.info("Clicked quick preview icon")
            time.sleep(0.8)  # Reduced from 2s — modal usually responds faster
            
            # Check for locked notes/symbol in quick preview (recent within 11 months).
            # Rows may be `tr` or `div[data-element*='preview-item']` with `<p>` lines (date, CC, etc.).
            # GLP: require matching drug name in combined `<p>` text for that preview item.
            has_recent_lock = False
            try:
                glp_preview_needles = _glp_quick_preview_keywords(
                    tirzepatide_glycine_b12_combo,
                    semaglutide_b12_combo,
                )
                today = datetime.now()
                cutoff = today - timedelta(days=365 * 11 // 12)

                for row in _iter_quick_preview_lock_roots(driver):
                    paras = row.find_elements(By.TAG_NAME, "p")
                    combined_lower = " ".join(
                        re.sub(r"\s+", " ", (p.text or "").strip())
                        for p in paras
                        if (p.text or "").strip()
                    ).lower()

                    note_recent = False
                    date_str_shown: Optional[str] = None
                    for dt_el in paras:
                        date_str = (dt_el.text or "").strip()
                        try:
                            for fmt in ("%m/%d/%Y", "%m/%d/%y"):
                                try:
                                    note_date = datetime.strptime(date_str, fmt)
                                    if note_date.year < 100:
                                        note_date = note_date.replace(year=note_date.year + 2000)
                                    if note_date >= cutoff:
                                        note_recent = True
                                        date_str_shown = date_str
                                        break
                                except ValueError:
                                    continue
                            if note_recent:
                                break
                        except Exception:
                            continue

                    if not note_recent:
                        continue

                    if glp_preview_needles:
                        missing = [n for n in glp_preview_needles if n not in combined_lower]
                        if missing:
                            log.info(
                                "GLP preview: recent lock from %s but preview `<p>` text lacks required %s — skipping Send eRx path",
                                date_str_shown,
                                missing,
                            )
                            continue

                    # If the same encounter contains "denied", do NOT treat it as valid for processing
                    if "denied" in combined_lower:
                        log.info(
                            "Preview: encounter with recent lock from %s contains 'denied' — skipping processing for this order",
                            date_str_shown,
                        )
                        continue

                    has_recent_lock = True
                    log.info(
                        "Found recent locked note from %s%s — will close preview",
                        date_str_shown,
                        " (GLP keywords OK)" if glp_preview_needles else "",
                    )
                    break
            except Exception as preview_err:
                log.debug("Preview table check failed (non-critical): %s", preview_err)
            
            if not has_recent_lock:
                log.info("No recent symbol/locked note found in quick preview — closing modal and returning to My Tasks")
                # Remember this order so we don't loop on it forever
                if order_num:
                    _save_skipped_order(order_num)

                _dismiss_quick_preview_overlay(driver, log)
                _navigate_my_tasks_and_save_draft(driver, log)

                # Early return after cleanup — do NOT proceed to Send eRx for this order
                return False
            
            # Symbol WAS found — dismiss overlay without clicks, stay on order detail
            _dismiss_quick_preview_overlay(driver, log)
            _dismiss_modal_backdrops_only(driver)
            if not _restore_order_detail_after_preview(driver, log, url_before_preview):
                log.warning(
                    "Order detail pane not visible after preview — skipping Process eRx (no navigation attempted)",
                )
                return False

        except Exception as preview_err:
            log.debug("Could not open quick preview (continuing): %s", preview_err)

        if not _order_detail_pane_visible(driver):
            _log_page_context(driver, log, "Left order detail before Process eRx")
            log.warning(
                "Order detail pane not visible — skipping Process eRx",
            )
            return False

        _set_script_date_then_ready_to_process(driver, log)
        time.sleep(0.5)

        # Click Process eRx: scoped to detail-pane footer `button`, not parent popover wrapper
        _dismiss_modal_backdrops_only(driver)
        process_erx_ok = False
        try:
            WebDriverWait(driver, 10).until(lambda d: _find_process_erx_button(d) is not None)
            process_erx_ok = _click_process_erx_button(driver, log)
        except TimeoutException:
            log.error("Process eRx button never appeared in detail pane footer")
        except StaleElementReferenceException:
            log.warning("Stale element during Process eRx — retrying click")
            process_erx_ok = _click_process_erx_button(driver, log)
        except Exception as e:
            log.error("Unexpected error clicking Process eRx: %s", e)

        if process_erx_ok:
            _save_sent_erx_order(order_num, order_details, patient_name)
            log.info(
                "Order detail flow completed — Process eRx sent%s",
                f" for {patient_name}" if patient_name else "",
            )
        else:
            log.info("Order detail flow completed — Process eRx was not confirmed")

        return process_erx_ok

    except TimeoutException as e:
        log.error("Failed to handle order detail pane (timed out): %s", e)
    except Exception as e:
        log.error("Failed to handle order detail pane: %s", e)

    # Attempt to close pane on error
    try:
        close_btns = driver.find_elements(By.CSS_SELECTOR, '[data-element="btn-close-detail-pane"], .icon-go-away')
        for btn in close_btns:
            if btn.is_displayed():
                btn.click()
                break
    except Exception:
        pass
    return False


class PatientCheckerApp:
    """Minimal Tk UI: launch Chrome and log into Practice Fusion using .env (same idea as shiptag startup)."""

    def __init__(self) -> None:
        self._cfg = _load_browser_config()
        self.driver: Optional[webdriver.Chrome] = None
        self._login_lock = threading.Lock()
        self._login_in_progress = False
        self.automation_running = False
        self.automation_thread = None
        self.total_processed = 0

        self.root = tk.Tk()
        self.root.title("Vitastir Doctor — Patient Checker")
        self.root.geometry("520x200")
        self.root.resizable(False, False)
        self.root.protocol("WM_DELETE_WINDOW", self._on_close)

        main = ttk.Frame(self.root, padding="12")
        main.grid(row=0, column=0, sticky=(tk.N, tk.S, tk.E, tk.W))

        ttk.Label(main, text="Practice Fusion — Tasks").grid(row=0, column=0, columnspan=2, sticky=tk.W)

        self.status_var = tk.StringVar(value="Ready. Set DOCTOR_USERNAME and DOCTOR_PASSWORD in .env")
        ttk.Label(main, textvariable=self.status_var, wraplength=480).grid(
            row=1, column=0, columnspan=2, sticky=tk.W, pady=(8, 12)
        )

        style = ttk.Style()
        style.configure("Action.TButton", padding=6)

        self.login_btn = ttk.Button(
            main,
            text="Login to Practice Fusion + Start Automation",
            command=self._on_login_clicked,
            style="Action.TButton",
        )
        self.login_btn.grid(row=2, column=0, padx=5, sticky=tk.W)

        self.stop_btn = ttk.Button(
            main,
            text="Stop Automation",
            command=self._stop_automation,
            style="Action.TButton",
            state="disabled",
        )
        self.stop_btn.grid(row=2, column=1, padx=5, sticky=tk.W)

        ttk.Label(main, text="(Loops: vitamins → Finish → Process eRx. GLP: Semaglutide+B12 & Tirzepatide combo; Tirzepatide needs Qty 1–2; both skip LA/MS/AR.)", font=("TkDefaultFont", 8)).grid(
            row=3, column=0, columnspan=2, sticky=tk.W, pady=(8, 0)
        )

        self.processed_var = tk.StringVar(value="Process eRx sent: 0")
        ttk.Label(main, textvariable=self.processed_var, font=("TkDefaultFont", 9, "bold")).grid(
            row=4, column=0, columnspan=2, sticky=tk.W, pady=(5, 0)
        )

        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)
        main.columnconfigure(1, weight=1)

        self.root.mainloop()

    def _set_status(self, text: str) -> None:
        self.status_var.set(text)

    def _on_close(self) -> None:
        self._stop_automation()
        try:
            if self.driver:
                self.driver.quit()
        except Exception:
            pass
        self.driver = None
        self.root.destroy()

    def _start_automation(self) -> None:
        """Start the continuous vitamin processing loop."""
        if self.automation_running:
            return
        self.automation_running = True
        self.login_btn.state(["disabled"])
        self.stop_btn.state(["!disabled"])
        self.total_processed = 0
        self.processed_var.set("Process eRx sent: 0")
        self._set_status("Automation running — My Tasks scan (GLP: Dispense 1–2 for Tirzepatide combo; skip LA/MS/AR for GLP combos)...")
        self.automation_thread = threading.Thread(target=self._automation_loop, daemon=True)
        self.automation_thread.start()

    def _stop_automation(self) -> None:
        """Stop the automation loop."""
        self.automation_running = False
        if self.automation_thread and self.automation_thread.is_alive():
            self._set_status("Stopping automation...")
            self.automation_thread.join(timeout=5.0)
        self.login_btn.state(["!disabled"])
        self.stop_btn.state(["disabled"])
        self._set_status(f"Automation stopped. Total Process eRx sent: {self.total_processed}")

    def _automation_loop(self) -> None:
        """Main loop: ensure on My Tasks tab, process vitamins, repeat until stopped.
        No page refresh needed — the site returns to the tasks list after processing."""
        while self.automation_running:
            try:
                if not self.driver or not self.automation_running:
                    break

                if not ensure_practice_fusion_session(self.driver, self._cfg, _pf_log):
                    self.root.after(
                        0,
                        lambda: self._set_status("Session expired — re-login failed. Stopping automation."),
                    )
                    break

                # Ensure we're on My Tasks tab (only click if not already active)
                try:
                    my_tasks_tab = WebDriverWait(self.driver, 5).until(
                        EC.element_to_be_clickable((By.XPATH, '//a[contains(text(),"My tasks") or contains(@data-element,"tasks-tab-0")]'))
                    )
                    if "is-active" not in (my_tasks_tab.get_attribute("class") or ""):
                        my_tasks_tab.click()
                        _pf_log.info("Clicked 'My tasks' tab")
                        time.sleep(1)
                except:
                    pass  # Already on the right tab

                processed_this_cycle = process_vitamin_tasks(self.driver, _pf_log, self._cfg)
                self.total_processed += processed_this_cycle

                self.root.after(0, lambda count=self.total_processed: self.processed_var.set(f"Process eRx sent: {count}"))

                if processed_this_cycle == 0:
                    self.root.after(0, lambda: self._set_status(f"Automation running — no new vitamins this cycle. Total: {self.total_processed}. Next scan in 3s..."))
                    time.sleep(3)
                else:
                    self.root.after(0, lambda c=processed_this_cycle, t=self.total_processed: self._set_status(f"Process eRx sent for {c} this cycle. Total: {t}. Continuing..."))
                    time.sleep(0.5)  # Very short pause — website already returns to My Tasks

            except Exception as e:
                _pf_log.error("Error in automation loop: %s", e)
                self.root.after(0, lambda: self._set_status(f"Error in loop: {e}. Retrying..."))
                time.sleep(10)

        self.root.after(0, self._stop_automation)

    def _on_login_clicked(self) -> None:
        if not self._cfg["USERNAME"] or not self._cfg["PASSWORD"]:
            messagebox.showerror(
                "Missing credentials",
                "Set DOCTOR_USERNAME and DOCTOR_PASSWORD in your .env file (see .env.example).",
            )
            return

        with self._login_lock:
            if self._login_in_progress:
                return
            self._login_in_progress = True

        self.login_btn.state(["disabled"])
        self._set_status("Starting Chrome and logging in…")

        def worker() -> None:
            err: Optional[str] = None
            ok = False
            try:
                _ensure_pf_logging()
                if self.driver:
                    try:
                        self.driver.quit()
                    except Exception:
                        pass
                    self.driver = None

                self.driver = _build_chrome_driver(self._cfg, _pf_log)
                ok = login_practice_fusion(self.driver, self._cfg, _pf_log)
                if ok:
                    _pf_log.info("Login successful — starting continuous vitamin automation loop")
                    # Start the background loop (this will keep running until Stop is clicked)
                    self.root.after(0, self._start_automation)
                else:
                    err = "Login did not complete. Check credentials, selectors in .env, or complete any MFA in the browser."
            except Exception as e:
                err = str(e)
                _pf_log.error("Worker exception: %s", e)

            def done() -> None:
                with self._login_lock:
                    self._login_in_progress = False
                if not ok:
                    self.login_btn.state(["!disabled"])
                    self._set_status(f"Login failed: {err or 'unknown error'}")
                    messagebox.showerror("Login failed", err or "Unknown error")

            self.root.after(0, done)

        threading.Thread(target=worker, daemon=True).start()


def load_patients(file_path: str) -> pd.DataFrame:
    """Load patient data from CSV or Excel file."""
    path = Path(file_path)
    if not path.exists():
        console.print(f"[red]Error: File {file_path} not found.[/red]")
        sys.exit(1)

    if path.suffix.lower() == ".csv":
        df = pd.read_csv(path)
    elif path.suffix.lower() in (".xlsx", ".xls"):
        df = pd.read_excel(path)
    else:
        console.print(f"[red]Unsupported file format: {path.suffix}[/red]")
        sys.exit(1)

    required_cols = ["patient_id", "name", "age", "heart_rate", "blood_pressure", "temperature"]
    missing = [col for col in required_cols if col not in df.columns]
    if missing:
        console.print(f"[yellow]Warning: Missing columns: {missing}. Using available data.[/yellow]")

    console.print(f"[green]Loaded {len(df)} patients from {file_path}[/green]")
    return df


def check_vitals(row: pd.Series) -> Dict[str, Any]:
    """Check patient's vitals for abnormalities."""
    issues = []
    status = "Normal"

    hr = row.get("heart_rate", 70)
    if pd.isna(hr):
        issues.append("Missing heart rate")
    elif hr < 60:
        issues.append(f"Bradycardia (HR: {hr})")
        status = "Abnormal"
    elif hr > 100:
        issues.append(f"Tachycardia (HR: {hr})")
        status = "Abnormal"

    temp = row.get("temperature", 37.0)
    if pd.isna(temp):
        issues.append("Missing temperature")
    elif temp < 36.0:
        issues.append(f"Hypothermia (Temp: {temp}°C)")
        status = "Abnormal"
    elif temp > 38.0:
        issues.append(f"Fever (Temp: {temp}°C)")
        status = "Abnormal"

    age = row.get("age", 0)
    if pd.isna(age) or age < 0 or age > 120:
        issues.append(f"Invalid age: {age}")
        status = "Invalid"

    return {
        "patient_id": row.get("patient_id", "UNKNOWN"),
        "name": row.get("name", "Unknown"),
        "status": status,
        "issues": issues,
        "heart_rate": hr,
        "temperature": temp,
        "age": age,
    }


def generate_report(checks: List[Dict[str, Any]]) -> None:
    """Generate a rich report of patient checks."""
    table = Table(title="Patient Check Report")
    table.add_column("Patient ID", style="cyan")
    table.add_column("Name", style="magenta")
    table.add_column("Status", style="green")
    table.add_column("Issues", style="red")
    table.add_column("HR", justify="right")
    table.add_column("Temp (°C)", justify="right")

    abnormal_count = 0
    for check in checks:
        status_style = "red" if check["status"] != "Normal" else "green"
        issues_str = ", ".join(check["issues"]) if check["issues"] else "None"
        table.add_row(
            str(check["patient_id"]),
            check["name"],
            f"[{status_style}]{check['status']}[/{status_style}]",
            issues_str,
            str(check["heart_rate"]),
            f"{check['temperature']:.1f}",
        )
        if check["status"] != "Normal":
            abnormal_count += 1

    console.print(table)
    rprint(f"\n[bold]Summary:[/bold] {len(checks)} patients checked, [red]{abnormal_count} abnormal[/red]")

    if abnormal_count > 0:
        console.print("[yellow]Recommendation: Review patients with abnormal status.[/yellow]")


def run_check(file: str, verbose: bool) -> List[Dict[str, Any]]:
    """Check patients' vitals and generate report."""
    console.print("[bold blue]Vitastir Doctor - Patient Checker[/bold blue]")

    df = load_patients(file)

    checks = []
    for _, row in df.iterrows():
        check_result = check_vitals(row)
        checks.append(check_result)
        if verbose and check_result["issues"]:
            console.print(f"[yellow]Patient {check_result['name']}: {check_result['issues']}[/yellow]")

    generate_report(checks)
    return checks


def run_demo() -> None:
    """Run with demo patient data."""
    console.print("[bold blue]Running demo with sample patient data...[/bold blue]")

    data = {
        "patient_id": [1, 2, 3, 4],
        "name": ["Alice Smith", "Bob Johnson", "Carol Davis", "David Wilson"],
        "age": [34, 67, 25, 82],
        "heart_rate": [72, 105, 58, 95],
        "blood_pressure": ["120/80", "145/92", "110/70", "160/100"],
        "temperature": [36.8, 38.5, 35.2, 37.1],
    }
    df = pd.DataFrame(data)
    demo_file = Path("demo_patients.csv")
    df.to_csv(demo_file, index=False)
    console.print(f"[green]Created demo file: {demo_file}[/green]")

    run_check(file=str(demo_file), verbose=True)

    if demo_file.exists():
        demo_file.unlink()


def _build_arg_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Vitastir Doctor Patient Checker")
    sub = parser.add_subparsers(dest="command", help="Command to run (omit to open the login UI)")

    p_check = sub.add_parser("check", help="Check patients' vitals from a CSV/Excel file")
    p_check.add_argument("-f", "--file", default="patients.csv", help="Path to patient data file")
    p_check.add_argument("-v", "--verbose", action="store_true", help="Show detailed output")

    sub.add_parser("demo", help="Run vitals check on built-in sample data")

    return parser


if __name__ == "__main__":
    # Same idea as shiptag: no CLI args opens the Tk UI.
    if len(sys.argv) == 1:
        PatientCheckerApp()
    else:
        args = _build_arg_parser().parse_args()
        if args.command == "check":
            run_check(file=args.file, verbose=args.verbose)
        elif args.command == "demo":
            run_demo()
        else:
            _build_arg_parser().print_help()
            sys.exit(2)
