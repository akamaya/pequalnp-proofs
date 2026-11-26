#!/usr/bin/env bash
set -euo pipefail
src="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
dst="${1:-$HOME/dev/LeanDojo-v2}"
[[ -d "$dst" && -d "$dst/.venv" ]] || { echo "Existing LeanDojo-v2 environment required: $dst" >&2; exit 1; }
files=(
  leandojo_local_smoke_v25.py
  leandojo_export_proof_v3.py
  pnp_autorun_v6.py
  pnp_table_solve_v2.py
  pnp_graph_solve_v1.py
  pnp_graph_support_v1.py
  pnp_graph_binary_v3.py
  pnp_graph_binary_width_v1.py
  pnp_graph_binary_pairs_v1.py
  pnp_graph_certificate_v3.py
  pnp_proof_audit_v1.py
)
for f in "${files[@]}"; do [[ -f "$src/$f" ]] || { echo "Missing $f" >&2; exit 1; }; done
# Preserve user-edited scripts; never touch logs, indexes, credentials or the official pnp_current.sh.
backup=""
put() {
  local from="$1" to="$2"
  if [[ -f "$dst/$to" ]] && cmp -s -- "$src/$from" "$dst/$to"; then return; fi
  if [[ -e "$dst/$to" || -L "$dst/$to" ]]; then
    if [[ -z "$backup" ]]; then backup="$(mktemp -d "$dst/.solver-tools-backup.XXXXXXXX")"; fi
    cp -a -- "$dst/$to" "$backup/$to"
  fi
  install -m 0644 -- "$src/$from" "$dst/$to"
  printf 'Installed %s\n' "$to"
}
for f in "${files[@]}"; do put "$f" "$f"; done
put leandojo_local_smoke_v25.py leandojo_local_smoke.py
put pnp_autorun_v6.py pnp_autorun.py
[[ -z "$backup" ]] || printf 'Previous files backed up: %s\n' "$backup"
echo "Solver tools sync complete."
