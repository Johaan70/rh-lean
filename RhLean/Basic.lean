import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.ZetaZeros

open Nat Real ArithmeticFunction Complex

-- ✅ Mathlibens offisielle RH
#check @RiemannHypothesis
-- RiemannHypothesis : Prop  ← BEKREFTET!

-- ✅ Von Mangoldt
theorem vonMangoldt_prime (p : ℕ) (hp : p.Prime) :
    Λ p = Real.log p :=
  ArithmeticFunction.vonMangoldt_apply_prime hp

theorem vonMangoldt_nonneg (n : ℕ) : 0 ≤ Λ n :=
  ArithmeticFunction.vonMangoldt_nonneg

-- ✅ RH impliserer ingen nullpunkter utenfor critical line
theorem rh_no_zeros_off_line (h : RiemannHypothesis)
    (s : ℂ) (hzero : riemannZeta s = 0)
    (hntriv : ¬∃ n : ℕ, s = -2 * (n + 1))
    (hpole : s ≠ 1) :
    s.re = 1 / 2 :=
  h s hzero hntriv hpole

-- ✅ RH og kritisk strip
theorem rh_critical_strip (h : RiemannHypothesis)
    (s : ℂ) (hzero : riemannZeta s = 0)
    (hre_pos : 0 < s.re) (hre_lt : s.re < 1) :
    s.re = 1 / 2 := by
  apply h s hzero
  · intro ⟨n, hn⟩
    rw [hn] at hre_pos
    simp [mul_comm] at hre_pos
    -- s.re = -(2 * (n+1)) < 0, men hre_pos sier 0 < s.re
    linarith
  · intro heq
    rw [heq] at hre_lt
    norm_num at hre_lt

-- ✅ Nullpunktenes topologi
#check riemannZetaZeros
#check isClosed_riemannZetaZeros
#check isDiscrete_riemannZetaZeros
