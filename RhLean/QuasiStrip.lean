import RhLean.Nonvanishing
import RhLean.Quadruple
import RhLean.ZetaSign

/-!
# Kvasi-Riemann-båndet

Bro mellom rh-lean og OpenAIs 7/8-resultat (openai/math,
`OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re`).

OpenAI beviser én side: ingen nullpunkter for Re s > 7/8.
Med funksjonallikningen fra rh-lean (`zeta_zero_symmetric`) speiles dette
til den andre siden: ingen ikke-trivielle nullpunkter for Re s < 1/8.

Resultatet er her formulert med OpenAIs påstand som hypotese `QuasiRH78`,
med nøyaktig samme utsagn som Comparator-utfordringen. Når OAI-modulen
bygges i samme prosjekt, settes beviset inn i `QuasiRH78` direkte.
-/

open Complex ComplexConjugate

/-- OpenAIs Comparator-utsagn, ordrett. -/
def QuasiRH78 : Prop :=
  ∀ s : ℂ, (7 / 8 : ℝ) < s.re → riemannZeta s ≠ 0

/-- Et nullpunkt i den åpne stripen er ikke et ikke-positivt heltall. -/
lemma ne_neg_nat_of_re_pos {s : ℂ} (h : 0 < s.re) : ∀ n : ℕ, s ≠ -↑n := by
  intro n heq
  have := congr_arg Complex.re heq
  simp only [neg_re, natCast_re] at this
  linarith [Nat.cast_nonneg (α := ℝ) n]

lemma ne_one_of_re_lt_one {s : ℂ} (h : s.re < 1) : s ≠ 1 := by
  intro heq; rw [heq, one_re] at h; exact lt_irrefl _ h

/-- Høyre side: direkte fra OpenAI. -/
theorem nontrivial_zero_re_le_seven_eighths (hQ : QuasiRH78)
    (s : ℂ) (hz : riemannZeta s = 0) : s.re ≤ 7 / 8 := by
  by_contra h
  exact hQ s (by push_neg at h; exact_mod_cast h) hz

/-- Venstre side: OpenAI speilet gjennom rh-leans funksjonallikning. -/
theorem nontrivial_zero_one_eighth_le_re (hQ : QuasiRH78)
    (s : ℂ) (hz : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * (↑n + 1)) : 1 / 8 ≤ s.re := by
  by_contra h
  push_neg at h
  obtain ⟨h0, h1⟩ := nontrivial_zero_in_strip s hz hnt
  have hsym := zeta_zero_symmetric s (ne_neg_nat_of_re_pos h0)
    (ne_one_of_re_lt_one h1) hz
  exact hQ (1 - s) (by simp only [sub_re, one_re]; push_cast; linarith) hsym

/-- **Kvasi-Riemann-båndet.** Hvert ikke-trivielle nullpunkt ρ har
    1/8 ≤ Re ρ ≤ 7/8 og Im ρ ≠ 0. -/
theorem nontrivial_zero_in_quasi_band (hQ : QuasiRH78)
    (s : ℂ) (hz : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * (↑n + 1)) :
    1 / 8 ≤ s.re ∧ s.re ≤ 7 / 8 ∧ s.im ≠ 0 :=
  ⟨nontrivial_zero_one_eighth_le_re hQ s hz hnt,
   nontrivial_zero_re_le_seven_eighths hQ s hz,
   nontrivial_zero_im_ne_zero s hz hnt⟩

/-- Avstanden til RH: hvert ikke-trivielle nullpunkt ligger innenfor 3/8
    av den kritiske linjen. -/
theorem nontrivial_zero_dist_half_le (hQ : QuasiRH78)
    (s : ℂ) (hz : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * (↑n + 1)) : |s.re - 1 / 2| ≤ 3 / 8 := by
  obtain ⟨h1, h2, _⟩ := nontrivial_zero_in_quasi_band hQ s hz hnt
  rw [abs_le]; constructor <;> linarith

/-- RH reduseres til båndet [1/8, 7/8]. -/
theorem rh_reduces_to_quasi_band (hQ : QuasiRH78) :
    (∀ s : ℂ, riemannZeta s = 0 → 1 / 8 ≤ s.re → s.re ≤ 7 / 8 →
      s.im ≠ 0 → s.re = 1 / 2) →
    RiemannHypothesis := by
  intro h s hz hnt _
  obtain ⟨h1, h2, h3⟩ := nontrivial_zero_in_quasi_band hQ s hz hnt
  exact h s hz h1 h2 h3

#print axioms nontrivial_zero_in_quasi_band
#print axioms nontrivial_zero_dist_half_le
#print axioms rh_reduces_to_quasi_band
