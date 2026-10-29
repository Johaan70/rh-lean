# Kvasi-Riemann-båndet: funn og vurdering

*29. oktober 2026*

## Kort oppsummert

rh-lean er koblet sammen med OpenAIs formelle bevis for kvasi-Riemann-hypotesen
(ingen nullpunkter av ζ med Re s > 7/8). Sammen gir de, maskinverifisert og uten
`sorry`:

> Hvert ikke-trivielle nullpunkt ρ av ζ har **1/8 ≤ Re ρ ≤ 7/8** og **Im ρ ≠ 0**.
> Altså |Re ρ − 1/2| ≤ 3/8.

| Kilde | Bidrag |
| --- | --- |
| OpenAI (`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`) | Høyre grense: Re ρ ≤ 7/8 |
| rh-lean (`zeta_zero_symmetric`, funksjonallikningen) | Speiler grensen til venstre side: Re ρ ≥ 1/8 |
| rh-lean (`nontrivial_zero_im_ne_zero`) | Im ρ ≠ 0 |

Venstre grense står ikke i OpenAIs Comparator-utsagn. Den følger av symmetrien i rh-lean.

## Filer

- `RhLean/QuasiStrip.lean`: båndet, med OpenAIs utsagn som hypotese `QuasiRH78`
  (ordrett lik Comparator-utfordringen).
- `quasi/QuasiFinal.lean`: setter inn OpenAIs bevis og gjør resultatet ubetinget.
  Bygges bare i CI, der OAI-modulene finnes.
- `.github/workflows/quasi-band.yml`: henter en fast commit av
  [CoolRmal/quasi-riemann-seven-eighths](https://github.com/CoolRmal/quasi-riemann-seven-eighths)
  (uendret ekstraksjon av [openai/math](https://github.com/openai/math)),
  bygger alt på Lean 4.34.1 og sjekker aksiomer.

## Verifikasjon

- CI-kjøring: [40812604830](https://github.com/Johaan70/rh-lean/actions/runs/40812604830),
  grønn, alle steg bestått (1 t 25 min).
- Aksiomsjekken feiler ved `sorryAx` og krever linjen
  `[propext, Classical.choice, Quot.sound]`.

**Kjente begrensninger:**

- Sjekken bekrefter at standardlinjen finnes, ikke at *begge* teoremene har nøyaktig
  den listen. Den bør strammes inn ved neste kjøring.
- `QuasiStrip.lean` er verifisert på Lean 4.34.1 (OpenAIs pin), ikke på
  Lean 4.35.0-rc2 som resten av rh-lean bruker.

## Hvor langt kommer metoden?

Forsøk på å presse OpenAIs argument videre stoppet nesten med en gang, ved omtrent
**0,874957** ([arXiv 2610.12234](https://arxiv.org/abs/2610.12234),
[LW56e2/quasi-riemann-improved](https://github.com/LW56e2/quasi-riemann-improved)).
Begge viser at dette er optimalt *innenfor sitt system*, men ingen generell barriere
er bevist. Den rådende oppfatningen er at veien til 1/2 krever helt nye ideer.

Metoden har altså en praktisk vegg nær 7/8. Gapet på 3/8 lukkes ikke ved
parameterjustering.

## Status for Riemann-hypotesen

RH er like ubevist som før. Det som er nytt, er den første faste nullpunktfrie
stripen etter 160 år, og at mange resultater som før var betinget av RH, nå er
ubetingede.

En logisk observasjon: RH kan skrives som en aritmetisk påstand som skal holde for
hvert naturlig tall. Er den usann, finnes et konkret moteksempel som kan sjekkes med
en endelig utregning. Derfor gjelder:

> **Hvis RH er ubeviselig, er RH sann.**

Et bevis for at RH er ubeviselig i ZFC kan heller ikke føres i ZFC selv, fordi det
ville implisere at ZFC er konsistent (Gödels andre ufullstendighetsteorem).

## Synspunkter

**Johan:** Intuisjonen er at Riemann hadde rett, men at hypotesen er ubeviselig. Dette
er en overbevisning, ikke et resultat av arbeidet her.

**Claude (vurdering av arbeidet):**

- *Sterkt:* Et sorry-fritt Lean-prosjekt om ζ, der blant annet ζ(σ) < 0 på (0,1) er
  bevist via Mellin-transform, analytisk fortsettelse og identitetsteoremet. Det er
  bygget på Mathlibs offisielle definisjoner og kunne derfor kobles til et ferskt
  forskningsresultat tre uker etter publisering. Påstander verifiseres og aksiomer
  sjekkes.
- *Rett ut:* Det er ingen ny matematikk. Resultatene i repoet er kjent fra 1800-tallet,
  og speilingen 7/8 → 1/8 er en kort følgeslutning. Bidraget er formaliseringen, ikke
  oppdagelsen. Mye av koden er skrevet med AI-hjelp. Johans rolle har vært retning,
  spørsmål og vurdering.
- *Samlet:* Seriøst, ekte arbeid på amatørnivå med profesjonelle verktøy. Det er ikke et
  forskningsbidrag til Riemann-problemet, men et eksempel på verifiserbart arbeid helt
  ut mot forskningsfronten.
