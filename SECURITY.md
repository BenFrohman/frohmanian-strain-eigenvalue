# Security reporting

Copyright (c) 2026 Benjamin Stanley Frohman. Apache-2.0.
Author: Benjamin Stanley Frohman
Maintainer: Frohman, Benjamin Stanley.

For a potentially sensitive vulnerability, use the existing author contact
`frohmanbenjamin@gmail.com`, also recorded in `CITATION.cff` and `NOTICE`.
This reuses a published contact; it does not claim a monitored security team,
response-time guarantee, bug bounty, or encrypted reporting infrastructure.

Include the affected commit/toolchain, a minimal reproduction, impact and
relevant logs with credentials and personal data removed. Do not publish
credentials, private data, exploit details affecting others, or secret-bearing
files in public issues. If a credential is exposed, revoke it through its
provider; do not send the credential in a report.

This repository runs Lean and GitHub Actions build workflows. Do not run
untrusted forks or scripts in environments containing credentials. A successful
Lean proof or axiom scan is not a sandbox or a general security audit.
Mathematical correctness questions without sensitive security content can use
ordinary repository review; mark algebraic kernel checks accurately. No release
support window or vulnerability-free guarantee is made.
