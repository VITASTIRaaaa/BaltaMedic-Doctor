#!/usr/bin/env python3
"""
Vitastir Doctor - Selenium Patient Approver

Automates:
1. Opening Chrome
2. Logging into the medical service
3. Navigating to pending patients
4. Approving patients

Configuration is loaded from .env file.
Update selectors in .env to match the target website's DOM.
"""

import os
import time
import logging
from pathlib import Path
from dotenv import load_dotenv
from selenium import webdriver
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.common.by import By
from selenium.webdriver.support.ui import WebDriverWait
from selenium.webdriver.support import expected_conditions as EC
from selenium.common.exceptions import TimeoutException, NoSuchElementException, WebDriverException
from webdriver_manager.chrome import ChromeDriverManager
from rich.console import Console
from rich import print as rprint
import argparse

# Load environment variables
load_dotenv()

console = Console()

# Configuration from .env
config = {
    "LOGIN_URL": os.getenv("LOGIN_URL", "https://example.com/login"),
    "DASHBOARD_URL": os.getenv("DASHBOARD_URL", "https://example.com/dashboard"),
    "APPROVAL_PAGE_URL": os.getenv("APPROVAL_PAGE_URL", "https://example.com/patients/pending"),
    "USERNAME": os.getenv("DOCTOR_USERNAME"),
    "PASSWORD": os.getenv("DOCTOR_PASSWORD"),
    "HEADLESS": os.getenv("HEADLESS", "false").lower() == "true",
    "WAIT_TIMEOUT": int(os.getenv("WAIT_TIMEOUT", 30)),
    "IMPLICIT_WAIT": int(os.getenv("IMPLICIT_WAIT", 10)),
    # Selectors
    "LOGIN_USERNAME_SELECTOR": os.getenv("LOGIN_USERNAME_SELECTOR", 'input[name="username"], input[type="email"], #username'),
    "LOGIN_PASSWORD_SELECTOR": os.getenv("LOGIN_PASSWORD_SELECTOR", 'input[type="password"], #password'),
    "LOGIN_BUTTON_SELECTOR": os.getenv("LOGIN_BUTTON_SELECTOR", 'button[type="submit"]'),
    "PATIENT_ROW_SELECTOR": os.getenv("PATIENT_ROW_SELECTOR", ".patient-row, tr[data-patient-id]"),
    "APPROVE_BUTTON_SELECTOR": os.getenv("APPROVE_BUTTON_SELECTOR", 'button.approve, button:has-text("Approve"), button[contains(text(), "Approve")]'),
    "APPROVE_ALL_BUTTON_SELECTOR": os.getenv("APPROVE_ALL_BUTTON_SELECTOR", "#approve-all, button.approve-all"),
}

def setup_driver() -> webdriver.Chrome:
    """Setup Chrome driver with proper options."""
    chrome_options = Options()
    
    if config["HEADLESS"]:
        chrome_options.add_argument("--headless")
    
    chrome_options.add_argument("--no-sandbox")
    chrome_options.add_argument("--disable-dev-shm-usage")
    chrome_options.add_argument("--disable-blink-features=AutomationControlled")
    chrome_options.add_experimental_option("excludeSwitches", ["enable-automation"])
    chrome_options.add_experimental_option("useAutomationExtension", False)
    
    # Add user-agent to appear more human-like
    chrome_options.add_argument("--user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/134.0.0.0 Safari/537.36")
    
    service = Service(ChromeDriverManager().install())
    driver = webdriver.Chrome(service=service, options=chrome_options)
    driver.implicitly_wait(config["IMPLICIT_WAIT"])
    
    # Remove webdriver property to avoid detection
    driver.execute_script("Object.defineProperty(navigator, 'webdriver', {get: () => undefined})")
    
    console.print("[green]Chrome driver initialized successfully.[/green]")
    return driver

def wait_and_click(driver: webdriver.Chrome, selector: str, timeout: int = None, by: By = By.CSS_SELECTOR) -> bool:
    """Wait for element and click it safely."""
    timeout = timeout or config["WAIT_TIMEOUT"]
    try:
        element = WebDriverWait(driver, timeout).until(
            EC.element_to_be_clickable((by, selector))
        )
        element.click()
        time.sleep(1)  # Small delay after click
        return True
    except TimeoutException:
        console.print(f"[red]Timeout waiting for selector: {selector}[/red]")
        return False
    except Exception as e:
        console.print(f"[red]Error clicking element {selector}: {e}[/red]")
        return False

def login(driver: webdriver.Chrome) -> bool:
    """Login to the service using credentials from .env."""
    if not config["USERNAME"] or not config["PASSWORD"]:
        console.print("[red]Error: DOCTOR_USERNAME or DOCTOR_PASSWORD not set in .env[/red]")
        return False
    
    console.print(f"[blue]Navigating to login page: {config['LOGIN_URL']}[/blue]")
    driver.get(config["LOGIN_URL"])
    
    try:
        # Wait for page to load
        WebDriverWait(driver, config["WAIT_TIMEOUT"]).until(
            EC.presence_of_element_located((By.TAG_NAME, "body"))
        )
        
        # Fill username
        username_selectors = config["LOGIN_USERNAME_SELECTOR"].split(",")
        username_filled = False
        for selector in username_selectors:
            selector = selector.strip()
            try:
                username_field = WebDriverWait(driver, 5).until(
                    EC.presence_of_element_located((By.CSS_SELECTOR, selector))
                )
                username_field.clear()
                username_field.send_keys(config["USERNAME"])
                username_filled = True
                console.print("[green]✓ Username field filled[/green]")
                break
            except:
                continue
        
        if not username_filled:
            console.print("[yellow]Warning: Could not find username field with provided selectors.[/yellow]")
        
        # Fill password
        password_selectors = config["LOGIN_PASSWORD_SELECTOR"].split(",")
        password_filled = False
        for selector in password_selectors:
            selector = selector.strip()
            try:
                password_field = WebDriverWait(driver, 5).until(
                    EC.presence_of_element_located((By.CSS_SELECTOR, selector))
                )
                password_field.clear()
                password_field.send_keys(config["PASSWORD"])
                password_filled = True
                console.print("[green]✓ Password field filled[/green]")
                break
            except:
                continue
        
        if not password_filled:
            console.print("[yellow]Warning: Could not find password field.[/yellow]")
        
        # Click login button
        login_selectors = config["LOGIN_BUTTON_SELECTOR"].split(",")
        login_clicked = False
        for selector in login_selectors:
            selector = selector.strip()
            if wait_and_click(driver, selector):
                login_clicked = True
                console.print("[green]✓ Login button clicked[/green]")
                break
        
        if not login_clicked:
            console.print("[red]Failed to click any login button selector.[/red]")
            return False
        
        # Wait for login to complete (redirect to dashboard)
        time.sleep(3)
        console.print("[green]Login attempt completed. Current URL:[/green]", driver.current_url)
        return True
        
    except Exception as e:
        console.print(f"[red]Login failed: {str(e)}[/red]")
        driver.save_screenshot("login_error.png")
        console.print("[yellow]Screenshot saved to login_error.png[/yellow]")
        return False

def approve_patients(driver: webdriver.Chrome, approve_all: bool = False) -> int:
    """Navigate to approval page and approve patients."""
    console.print(f"[blue]Navigating to approval page: {config['APPROVAL_PAGE_URL']}[/blue]")
    driver.get(config["APPROVAL_PAGE_URL"])
    
    time.sleep(4)  # Wait for page to fully load
    
    approved_count = 0
    
    try:
        if approve_all and config["APPROVE_ALL_BUTTON_SELECTOR"]:
            console.print("[blue]Looking for 'Approve All' button...[/blue]")
            all_selectors = config["APPROVE_ALL_BUTTON_SELECTOR"].split(",")
            for selector in all_selectors:
                selector = selector.strip()
                if wait_and_click(driver, selector, timeout=10):
                    console.print(f"[green]✓ Clicked Approve All button![/green]")
                    approved_count = 999  # Indicates bulk approval
                    time.sleep(5)
                    break
            if approved_count == 0:
                console.print("[yellow]Approve All button not found. Falling back to individual approval.[/yellow]")
        
        if approved_count == 0:
            # Individual patient approval
            console.print("[blue]Looking for patient rows and approve buttons...[/blue]")
            patient_rows = driver.find_elements(By.CSS_SELECTOR, config["PATIENT_ROW_SELECTOR"].split(",")[0].strip())
            
            console.print(f"[green]Found {len(patient_rows)} patient rows.[/green]")
            
            for i, row in enumerate(patient_rows[:10]):  # Limit to first 10 for safety
                try:
                    # Look for approve button within row or globally
                    approve_btn = None
                    try:
                        approve_btn = row.find_element(By.CSS_SELECTOR, config["APPROVE_BUTTON_SELECTOR"].split(",")[0].strip())
                    except:
                        # Try global selector
                        approve_buttons = driver.find_elements(By.CSS_SELECTOR, config["APPROVE_BUTTON_SELECTOR"].split(",")[0].strip())
                        if approve_buttons and i < len(approve_buttons):
                            approve_btn = approve_buttons[i]
                    
                    if approve_btn:
                        console.print(f"[yellow]Approving patient {i+1}...[/yellow]")
                        approve_btn.click()
                        approved_count += 1
                        time.sleep(2)  # Wait between approvals
                    else:
                        console.print(f"[yellow]No approve button found for patient {i+1}[/yellow]")
                except Exception as e:
                    console.print(f"[red]Error approving patient {i+1}: {e}[/red]")
                    continue
        
        console.print(f"[bold green]Successfully approved {approved_count} patients![/bold green]")
        return approved_count
        
    except Exception as e:
        console.print(f"[red]Error during patient approval: {e}[/red]")
        driver.save_screenshot("approval_error.png")
        return approved_count

def main():
    """Main entry point with argument parsing."""
    parser = argparse.ArgumentParser(description="Vitastir Doctor - Selenium Patient Approver")
    parser.add_argument("--all", "-a", action="store_true", help="Use Approve All button if available")
    parser.add_argument("--headless", action="store_true", help="Run browser in headless mode (no GUI)")
    parser.add_argument("--login-only", action="store_true", help="Only perform login, don't approve patients")
    args = parser.parse_args()

    console.print("[bold blue]🚀 Vitastir Doctor - Patient Approval Automation[/bold blue]")
    
    if args.headless:
        config["HEADLESS"] = True
    
    if not config.get("USERNAME") or not config.get("PASSWORD") or config["USERNAME"] == "your_doctor_username":
        console.print("[red]Please update .env with your real DOCTOR_USERNAME and DOCTOR_PASSWORD[/red]")
        console.print("Copy .env.example to .env and fill in the values.")
        console.print("\nExample credentials format:")
        console.print("DOCTOR_USERNAME=doctor@example.com")
        console.print("DOCTOR_PASSWORD=yourpassword")
        return 1
    
    driver = None
    try:
        driver = setup_driver()
        
        if not login(driver):
            console.print("[red]Login failed. Please check credentials, LOGIN_URL, and selectors in .env[/red]")
            console.print("Take a screenshot of the login page and update the CSS selectors accordingly.")
            return 1
        
        if args.login_only:
            console.print("[green]✅ Login successful! Stopping as requested.[/green]")
            console.print(f"Current URL: {driver.current_url}")
            input("\nPress Enter to close the browser...")
            return 0
        
        approved = approve_patients(driver, args.all)
        
        console.print("\n[bold green]✅ Automation completed successfully![/bold green]")
        console.print("[yellow]Review the browser. Close it manually or press Enter.[/yellow]")
        
        # Keep browser open for manual review
        input("\nPress Enter to close the browser...")
        return 0
        
    except WebDriverException as e:
        console.print(f"[red]WebDriver error: {e}[/red]")
        console.print("[yellow]Make sure Google Chrome is installed on your system.[/yellow]")
        return 1
    except Exception as e:
        console.print(f"[red]Unexpected error: {e}[/red]")
        import traceback
        console.print(traceback.format_exc())
        return 1
    finally:
        if driver:
            try:
                driver.quit()
                console.print("[green]Browser closed.[/green]")
            except:
                pass


if __name__ == "__main__":
    exit(main())
