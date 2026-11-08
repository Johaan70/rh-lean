# Mathlibs berggrunn

Et kart over [Mathlib](https://github.com/leanprover-community/mathlib4) bygget fra den faktiske importgrafen, ikke fra en metafor.

Hver prikk er én fil. Høyden er hvor mange importlag filen hviler på, med bunnen nederst. Kolonnene er fagområdene, sortert etter median dybde. Klikk på en fil for å se alt den står på, alt som bygger på den, og den lengste importkjeden ned til bunnen.

**Se kartet:** https://johaan70.github.io/rh-lean/mathlib-berggrunn/ (krever at GitHub Pages er slått på for repoet, med kilde `main` og mappen `/`). Uten Pages kan `index.html` lastes ned og åpnes lokalt i en nettleser.

## Hva dataene viser

Fra Mathlib på commit `1c2b155` (8. november 2026): 8 547 filer, 23 499 importer, 178 lag.

| Område | Median dybde |
|---|---|
| Ordensteori | 49 |
| Algebra | 60 |
| Kategoriteori | 72 |
| Topologi | 88 |
| Analyse | 115 |
| Tallteori | 116 |
| Målteori | 129 |
| Sannsynlighet | 159 |

- Ordensteori og det algebraiske hierarkiet ligger lavt. Grupper er definert på lag 17, og 84 % av Mathlib bygger på den filen.
- De reelle tallene ligger på lag 49, *over* grupper og ordensteori. De bygges av det algebraiske hierarkiet, ikke omvendt.
- Kategoriteori ligger midt i biblioteket. Den er et stort og sentralt område, men ikke en felles krone over resten.
- Sannsynlighet, målteori og tallteori ligger øverst og står på mest. Sentralgrenseteoremet (lag 164) står på 35 % av alle filene i Mathlib.

## Filer

| Fil | Hva |
|---|---|
| `bygg_graf.py` | Leser importlinjene fra en lokal kopi av mathlib4 og skriver `data.json`. Krever ikke Lean. |
| `mal.html` | Siden, med plass til dataene. |
| `lag_side.py` | Setter `data.json` inn i malen og skriver `index.html`. |
| `index.html` | Den ferdige siden (GitHub Pages). |

## Oppdatere til nyeste Mathlib

```bash
git clone --depth 1 --filter=blob:none --sparse https://github.com/leanprover-community/mathlib4.git
cd mathlib4 && git sparse-checkout set Mathlib && cd ..
python3 bygg_graf.py mathlib4 data.json   # kjør fra denne mappen
python3 lag_side.py
```

## Metode og begrensninger

- Bare importer mellom Mathlib-filer er tatt med, og bare fra filhodet.
- Filer merket `deprecated_module` er rene omdirigeringer. De er fjernet, og importer som gikk gjennom dem, peker til det de selv importerer.
- Dybde er lengden på den lengste importkjeden ned til en fil uten Mathlib-importer.
- Område er mappen rett under `Mathlib/`. Mapper med færre enn 25 filer er slått sammen til «Annet».
- Teoremer og definisjoner er talt med et regulært uttrykk. Det er et anslag; deklarasjoner Lean genererer automatisk, er ikke med.
- Kartet viser avhengigheter mellom filer, ikke mellom enkeltteoremer.
