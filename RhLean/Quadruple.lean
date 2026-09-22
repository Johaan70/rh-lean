import RhLean.Nonvanishing
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

open Complex ComplexConjugate

/-- Nullpunkter i konjugerte par (bruker Mathlibs riemannZeta_conj). -/
theorem zeta_zero_conj (ρ : ℂ) (hz : riemannZeta ρ = 0) :
    riemannZeta (conj ρ) = 0 := by
  rw [riemannZeta_conj, hz, map_zero]

/-- Ikke-trivielle nullpunkter kommer i firergrupper:
    ρ, 1 − ρ, ρ̄ og 1 − ρ̄. -/
theorem zeta_zero_quadruple (ρ : ℂ)
    (hint : ∀ n : ℕ, ρ ≠ -↑n) (h1 : ρ ≠ 1)
    (hz : riemannZeta ρ = 0) :
    riemannZeta (1 - ρ) = 0 ∧
    riemannZeta (conj ρ) = 0 ∧
    riemannZeta (1 - conj ρ) = 0 := by
  have h_sym := zeta_zero_symmetric ρ hint h1 hz
  refine ⟨h_sym, zeta_zero_conj ρ hz, ?_⟩
  have := zeta_zero_conj (1 - ρ) h_sym
  rwa [map_sub, map_one] at this

#print axioms zeta_zero_quadruple
