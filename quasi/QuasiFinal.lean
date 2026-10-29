import RhLean.QuasiStrip
import OAI.NumberTheory.DirichletL.Nonvanishing

/-!
# Kvasi-Riemann-båndet, ubetinget

Setter inn OpenAIs bevis (openai/math, via CoolRmal/quasi-riemann-seven-eighths)
for hypotesen `QuasiRH78` i `RhLean.QuasiStrip`.

Bygges kun i CI (`.github/workflows/quasi-band.yml`), der OAI-modulene finnes.
-/

/-- OpenAIs 7/8-teorem oppfyller `QuasiRH78`. -/
theorem quasiRH78 : QuasiRH78 :=
  fun _ hs => OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re hs

/-- Hvert ikke-trivielle nullpunkt ρ har 1/8 ≤ Re ρ ≤ 7/8 og Im ρ ≠ 0. -/
theorem nontrivial_zero_in_quasi_band' (s : ℂ) (hz : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * (↑n + 1)) :
    1 / 8 ≤ s.re ∧ s.re ≤ 7 / 8 ∧ s.im ≠ 0 :=
  nontrivial_zero_in_quasi_band quasiRH78 s hz hnt

/-- |Re ρ − 1/2| ≤ 3/8. -/
theorem nontrivial_zero_dist_half_le' (s : ℂ) (hz : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * (↑n + 1)) : |s.re - 1 / 2| ≤ 3 / 8 :=
  nontrivial_zero_dist_half_le quasiRH78 s hz hnt

#print axioms nontrivial_zero_in_quasi_band'
#print axioms nontrivial_zero_dist_half_le'
