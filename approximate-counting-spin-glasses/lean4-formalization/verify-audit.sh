#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
exec lake env bash scripts/check_audit_rejections.sh
