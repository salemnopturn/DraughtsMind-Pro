# Security Policy

## Reporting Vulnerabilities

If you discover a security vulnerability in DraughtsMind Pro, please report it responsibly:

1. **Do NOT** open a public GitHub issue
2. Report it privately through [GitHub Security Advisories](https://github.com/salemnopturn/DraughtsMind-Pro/security/advisories/new).
3. Include detailed steps to reproduce the vulnerability
4. Allow reasonable time for a fix before public disclosure

## Security Measures

DraughtsMind Pro implements the following security measures:

- **Context Isolation**: Electron renderer runs in isolated context
- **Node Integration Disabled**: No direct Node.js access from renderer
- **Secure IPC**: All communication between main and renderer uses contextBridge
- **No External Network**: Application runs 100% offline
- **No Telemetry**: No data collection or tracking
- **Sandbox Mode**: Renderer process sandboxed where possible

## Scope

This security policy applies to:
- The DraughtsMind Pro Electron application
- The web application (DraughtsMind Classic.html)

## Supported Versions

| Version | Supported |
|---------|-----------|
| 1.0.x | Yes |
| < 1.0 | No |
