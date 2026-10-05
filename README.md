# Jharkhand District Notification Monitor

Personal-use notification monitoring system for Jharkhand district websites.

## Flow

Government Websites
        ↓
GitHub Actions
        ↓
monitor.py
        ↓
Gemini classification
        ↓
Telegram Bot
        ↓
Telegram Channel

## Required GitHub Secrets

Repository → Settings → Secrets and variables → Actions

Add:

- TELEGRAM_BOT_TOKEN
- TELEGRAM_CHAT_ID
- GEMINI_API_KEY

## Gemini

Default model:

gemini-2.5-flash-lite

The GitHub Actions workflow does not define GEMINI_MODEL.

## First Run

The first successful scan of every website creates a baseline.

Existing notices are NOT sent to Telegram.

If a website is temporarily unavailable during the first run, its baseline remains incomplete.

When that website becomes available later, its current existing notices are baselined instead of being sent as old notifications.

## Later Runs

New candidate notices are classified by Gemini.

Only important notices are sent to Telegram.

## Telegram

Add your Telegram bot as an administrator of the Telegram channel.

Give it permission to post messages.

For a public channel:

@yourchannel

can normally be used as TELEGRAM_CHAT_ID.

For a private channel, use the numeric channel ID.

## State

state.json is intentionally stored in the repository.

Do not use GitHub Actions cache as the permanent notification database.

The Actions cache is only used for pip dependencies.

## Schedule

The workflow requests execution every 5 minutes:

*/5 * * * *

GitHub Actions scheduling is not an exact real-time guarantee.

The actual execution can sometimes be delayed.

## Website Limitation

This version reads server-returned HTML.

If a website loads its notices only through JavaScript/API after the initial HTML response, those notices may not be detected.

Such sites can later be handled with a dedicated API or browser/Playwright adapter.

## Personal Use

This project is designed for personal monitoring.

It is not intended to guarantee real-time crawling of every government website.
