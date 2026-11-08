#!/usr/bin/env python3
"""Les importgrafen til Mathlib fra kildefilene og skriv data.json.

Bruk: python3 bygg_graf.py <sti-til-mathlib4> <utfil.json>
Krever ikke at Lean er installert: importlinjene leses rett fra .lean-filene.
"""
import json, re, subprocess, sys
from collections import Counter, defaultdict
from pathlib import Path

rot = Path(sys.argv[1]); ut = Path(sys.argv[2])
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+([\w.']+)")
DEKL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|public|partial|unsafe)\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|structure|class|inductive)\b")

filer = sorted((rot / "Mathlib").rglob("*.lean"))
moduler = {}
for f in filer:
    navn = ".".join(f.relative_to(rot).with_suffix("").parts)
    imp, teorem, defn, linjer = [], 0, 0, 0
    i_hode, i_blokk, utgaatt = True, False, False
    for linje in f.read_text(encoding="utf-8", errors="replace").splitlines():
        linjer += 1
        if i_hode:
            # importer står bare i filhodet: kommentarer, `module`, `prelude`, `import`
            st = linje.split("--", 1)[0].strip() if not i_blokk else linje.strip()
            if i_blokk:
                if "-/" in st: i_blokk = False
                continue
            if st.startswith("/-"):
                i_blokk = "-/" not in st[2:]
                continue
            if not st or st.startswith("--") or st in ("module", "prelude"):
                continue
            m = IMPORT.match(linje)
            if m:
                imp.append(m.group(1)); continue
            i_hode = False
        if linje.startswith("deprecated_module"):
            utgaatt = True
        d = DEKL.match(linje)
        if d:
            if d.group(1) in ("theorem", "lemma"): teorem += 1
            else: defn += 1
    deler = navn.split(".")
    omraade = deler[1] if len(deler) > 2 else "(toppnivå)"
    moduler[navn] = dict(imp=imp, t=teorem, d=defn, l=linjer, a=omraade, utgaatt=utgaatt)

# bare kanter innad i Mathlib
for m in moduler.values():
    m["imp"] = sorted({i for i in m["imp"] if i in moduler})

# utgåtte filer (deprecated_module) er bare omdirigeringer: fjern dem og
# la importer som gikk gjennom dem, peke på det de selv importerer
utgaatte = {n for n, m in moduler.items() if m["utgaatt"]}
def loes(i, sett=()):
    if i not in utgaatte: return {i}
    ut = set()
    for j in moduler[i]["imp"]:
        if j not in sett: ut |= loes(j, sett + (i,))
    return ut
for n in utgaatte: pass
for m in moduler.values():
    m["imp"] = sorted(set().union(*[loes(i) for i in m["imp"]]) if m["imp"] else set())
for n in utgaatte: del moduler[n]
print(f"fjernet {len(utgaatte)} utgåtte omdirigeringsfiler")

# dybde = lengste vei fra en fil uten Mathlib-importer
# topologisk sortering (Kahn); feiler høyt hvis grafen har sykler
inn = {n: len(m["imp"]) for n, m in moduler.items()}
brukt_av = defaultdict(list)
for n, m in moduler.items():
    for i in m["imp"]: brukt_av[i].append(n)
dybde = {n: 0 for n in moduler}
koe = [n for n, k in inn.items() if k == 0]
sett = 0
while koe:
    n = koe.pop(); sett += 1
    for b in brukt_av[n]:
        dybde[b] = max(dybde[b], dybde[n] + 1)
        inn[b] -= 1
        if inn[b] == 0: koe.append(b)
if sett != len(moduler):
    sys.exit(f"sykel i importgrafen: {len(moduler) - sett} filer uten rekkefølge")

# små områder slås sammen
str_ = Counter(m["a"] for m in moduler.values())
for m in moduler.values():
    if str_[m["a"]] < 25: m["a"] = "Annet"

navn = sorted(moduler, key=lambda n: (dybde[n], n))
idx = {n: i for i, n in enumerate(navn)}
omr = sorted({moduler[n]["a"] for n in navn})
oidx = {a: i for i, a in enumerate(omr)}

commit = subprocess.run(["git", "-C", str(rot), "log", "-1", "--format=%H|%cs"],
                        capture_output=True, text=True).stdout.strip().split("|")
data = {
    "commit": commit[0], "dato": commit[1],
    "omraader": omr,
    "n": [n.removeprefix("Mathlib.") for n in navn],
    "a": [oidx[moduler[n]["a"]] for n in navn],
    "dy": [dybde[n] for n in navn],
    "t": [moduler[n]["t"] for n in navn],
    "d": [moduler[n]["d"] for n in navn],
    "l": [moduler[n]["l"] for n in navn],
    "imp": [[idx[i] for i in moduler[n]["imp"]] for n in navn],
}
ut.write_text(json.dumps(data, separators=(",", ":"), ensure_ascii=False))

# oppsummering
print(f"commit {commit[0][:10]} {commit[1]}: {len(navn)} filer, "
      f"{sum(len(x) for x in data['imp'])} importkanter, maks dybde {max(dybde.values())}")
print(f"teoremer/lemmaer ~{sum(data['t'])}, definisjoner m.m. ~{sum(data['d'])}, linjer {sum(data['l'])}")
per = defaultdict(list)
for n in navn: per[moduler[n]["a"]].append(dybde[n])
print(f"{'område':<22}{'filer':>6}{'median dybde':>14}")
for a, v in sorted(per.items(), key=lambda kv: sorted(kv[1])[len(kv[1])//2]):
    v = sorted(v); print(f"{a:<22}{len(v):>6}{v[len(v)//2]:>14}")
