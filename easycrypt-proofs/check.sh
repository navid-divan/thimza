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

# dependency order: algebra, sharing and masks, oracles, protocol, notions, proofs, game chain
FILES="Params.ec Types.ec BigOps.ec PolyList.ec Lagrange.ec Sharing.ec ShamirLagrange.ec \
Masking.ec MaskAlgebra.ec ViewPartition.ec Corruption.ec Simulator.ec Statelessness.ec \
QROM.ec Protocol.ec Notions.ec Privacy.ec ClassSim.ec Interchange.ec HintAlg.ec Extract.ec \
Games.ec Hierarchy.ec Assumptions.ec Security.ec \
ExtRO.ec FinEnum.ec ChainBase.ec ChainGame.ec ChainCol.ec ChainSim.ec ChainDead.ec ChainLazy.ec \
ChainFlag.ec ChainExt.ec ChainRep.ec ChainProg.ec ChainHint.ec ShamirHide.ec ChainFin.ec \
ChainCons.ec ChainPB.ec ChainGA.ec ChainB2.ec ChainB3.ec ChainB1a.ec ChainB1b.ec ChainB1c.ec \
ChainB1d.ec ChainMain.ec"

# files allowed to state global axioms, and why
QFILES="QROM.ec ExtRO.ec"   # quantum random oracle facts and their theory parameters
MFILES="ChainBase.ec"       # properties of abstract distributions and finite types

echo " Thimza : machine-checked proofs"
echo " EasyCrypt : $(command -v easycrypt) ($(easycrypt config 2>&1 | grep git-hash | awk "{print \$2}"))"
echo

echo "[1/3] scanning for skipped proofs"
BAD=0
for kw in admit admitted; do
  if grep -n -w -- "$kw" $FILES >/dev/null 2>&1; then
    echo "  FOUND forbidden keyword: $kw"
    grep -n -w -- "$kw" $FILES
    BAD=1
  fi
done
[ "$BAD" -eq 0 ] && echo "  no admit or admitted anywhere"
echo

echo "[2/3] compiling and checking all proofs, in dependency order"
# remove cached results so that every proof is checked again
rm -f ./*.eco
FAIL=0
for f in $FILES; do
  start=$(date +%s)
  if easycrypt compile -I . "$f" > /tmp/thimza_ec_$$.log 2>&1; then
    end=$(date +%s); printf "  %-20s OK   (%ss)\n" "$f" "$((end-start))"
  else
    end=$(date +%s); printf "  %-20s FAIL (%ss)\n" "$f" "$((end-start))"
    tr '\r' '\n' < /tmp/thimza_ec_$$.log | grep -A8 -i "critical" | head -20
    FAIL=1
  fi
done
rm -f /tmp/thimza_ec_$$.log
echo

echo "[3/3] summary"
LINES=$(cat $FILES | wc -l | tr -d ' ')
STMTS=$(grep -E -c "^(lemma|equiv|hoare|phoare)\b" $FILES | awk -F: '{s+=$2} END {print s}')
QAX=$(grep -E "^axiom\b" $QFILES | wc -l | tr -d ' ')
MAX=$(grep -E "^axiom\b" $MFILES | wc -l | tr -d ' ')
OTHER=""
for f in $FILES; do
  case " $QFILES $MFILES " in *" $f "*) continue ;; esac
  if grep -E -q "^axiom\b" "$f"; then OTHER="$OTHER $f"; fi
done
HYP=$(grep -E -c "^declare axiom\b" $FILES | awk -F: '{s+=$2} END {print s}')
# every clone discharges all obligations, except clones of the oracle theories,
# which keep exactly the quantum facts as axioms
CLA=$(grep -c "^clone" $FILES | awk -F: '{s+=$2} END {print s}')
CLN=$(grep -c "proof \*\." $FILES | awk -F: '{s+=$2} END {print s}')
CLQ=$(grep -E "^clone (include )?(QROM\.|ExtRO\.)?(QROM|QROMLazy|ExtRO)\b" $FILES | wc -l | tr -d ' ')
PARAMS=$(grep -E -c "^op [a-zA-Z0-9_]+ *: *[^=]*\.$" $FILES | awk -F: '{s+=$2} END {print s}')
echo "  files checked                     : $(echo $FILES | wc -w | tr -d ' ')"
echo "  lines of EasyCrypt                : $LINES"
echo "  proved statements                 : $STMTS"
echo "  axioms of the oracle theories     : $QAX in $QFILES"
grep -E -h -B1 "^axiom\b" $QFILES | grep -E "^\(\*" | sed 's/^/                                      /'
echo "  modelling axioms on parameters    : $MAX in $MFILES (lossless or uniform"
echo "                                      distributions, finite message and digest types)"
echo "  section hypotheses (declare axiom): $HYP (adversary query bounds and termination,"
echo "                                      injective encoding, regularity of openings)"
echo "  global axioms anywhere else       : ${OTHER:-none}"
echo "  clones                            : $CLA, of which $CLN end with proof * and"
echo "                                      $CLQ instantiate an oracle theory"
echo "  abstract parameters (op x : T)    : $PARAMS"
echo
if [ "$BAD" -eq 0 ] && [ "$FAIL" -eq 0 ] && [ -z "$OTHER" ] && [ $((CLN + CLQ)) -eq "$CLA" ]; then
  echo "  RESULT: ALL PROOFS CHECK"
  exit 0
else
  echo "  RESULT: FAILURE"
  exit 1
fi
