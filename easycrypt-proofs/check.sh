#!/usr/bin/env bash
set -u

cd "$(dirname "$0")"

if ! command -v easycrypt >/dev/null 2>&1; then
  if [ -x "$HOME/.opam/easycrypt/bin/easycrypt" ]; then
    export PATH="$HOME/.opam/easycrypt/bin:$PATH"
  else
    echo "easycrypt not found in PATH"
    exit 1
  fi
fi

# dependency order is algebra, then polynomials, then the scheme, then security.
FILES="Params.ec Types.ec BigOps.ec PolyList.ec Lagrange.ec Sharing.ec \
ShamirLagrange.ec Masking.ec Assumptions.ec Bounds.ec ROM.ec PRFSecurity.ec \
KeyGen.ec Protocol.ec Combine.ec Verify.ec Interchange.ec Correctness.ec \
ViewPartition.ec MaskAlgebra.ec Simulator.ec Corruption.ec Statelessness.ec \
Hierarchy.ec EUFCMA.ec GameHops.ec Security.ec"

echo " Thimza : machine-checked security proofs"
echo " EasyCrypt : $(command -v easycrypt)"
echo

echo "[1/3] scanning for skipped proofs"
BAD=0
for kw in admit admitted assume; do
  if grep -n -w -- "$kw" $FILES >/dev/null 2>&1; then
    echo "  FOUND forbidden keyword: $kw"
    grep -n -w -- "$kw" $FILES
    BAD=1
  fi
done
if [ "$BAD" -eq 0 ]; then
  echo "  none admit, admitted, assume commands found"
fi
echo

echo "[2/3] compiling and checking all proofs, in dependency order"
rm -f ./*.eco
FAIL=0
for f in $FILES; do
  printf '  %-22s ' "$f"
  START=$(date +%s)
  if easycrypt compile -I . "$f" > "/tmp/thimza_$(basename "${f%.ec}").log" 2>&1; then
    END=$(date +%s)
    printf 'OK   (%ss)\n' "$((END-START))"
  else
    printf 'FAIL\n'
    sed -n '1,25p' "/tmp/thimza_$(basename "${f%.ec}").log"
    FAIL=1
  fi
done
echo

echo "[3/3] summary"
NLEM=$(grep -c "^lemma \|^equiv \|^hoare " $FILES | awk -F: '{s+=$2} END {print s+0}')
NDECL=$(grep -c "^lemma \|^equiv \|^hoare \|^module \|^op \|^pred \|^type " $FILES | awk -F: '{s+=$2} END {print s+0}')
NLINES=$(cat $FILES | wc -l | tr -d ' ')
NAX=$(grep -c "^axiom " $FILES | awk -F: '{s+=$2} END {print s+0}')
echo "  files checked           : $(echo $FILES | wc -w | tr -d ' ')"
echo "  lines of EasyCrypt      : $NLINES"
echo "  proved statements       : $NLEM"
echo "  declarations total      : $NDECL"
echo "  declared model axioms   : $NAX"
if [ "$FAIL" -eq 0 ] && [ "$BAD" -eq 0 ]; then
  echo
  echo "  RESULT: ALL PROOFS CHECK"
  exit 0
else
  echo
  echo "  RESULT: FAILURE"
  exit 1
fi
