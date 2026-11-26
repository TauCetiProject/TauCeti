/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.PrimesInAP
import TauCeti.NumberTheory.DirichletCharacter.LFunction.Basic

/-!
# Pole-cleared tails of von Mangoldt series in progressions

Removing a finite set of terms from the Dirichlet series does not change its residue at `1`.
After shifting by `1` and multiplying by the shifted variable, the tail is holomorphic on discs
where the pole-cleared Dirichlet L-functions are nonvanishing. This gives the holomorphic
numerator and its central value for a maximum-modulus argument in logarithmic prime windows.

The normalization is the one in `New.hasSum_residueClass_one` and
`New.analyticOnNhd_sub_mul_sum_term` of `grh/src/Lib/Analytic/Primes.lean` in the shorter GRH
formalization (lsernau/grh-lean, `72fead1`). Here we use Mathlib's `LFunctionResidueClassAux`
for the regular part, with any invertible residue class and any finite set of removed terms.
-/

public section

open DirichletCharacter

namespace ArithmeticFunction.vonMangoldt

variable {q : ℕ} [NeZero q]

/-- The regular part of the von Mangoldt series in a residue class is analytic wherever the
pole-cleared principal L-function and the nonprincipal L-functions are all nonzero. -/
theorem analyticAt_LFunctionResidueClassAux (a : ZMod q) {s : ℂ}
    (h₀ : LFunctionTrivChar₁ q s ≠ 0)
    (h : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → χ.LFunction s ≠ 0) :
    AnalyticAt ℂ (LFunctionResidueClassAux a) s := by
  classical
  have hprincipal := (differentiable_LFunctionTrivChar₁ q).analyticAt s
  have hterm (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
      AnalyticAt ℂ (fun z ↦ χ a⁻¹ * deriv χ.LFunction z / χ.LFunction z) s := by
    have hχan := χ.analyticAt_LFunction (s := s) (.inr hχ)
    exact (analyticAt_const.mul hχan.deriv).div hχan (h χ hχ)
  unfold LFunctionResidueClassAux
  refine analyticAt_const.mul ((hprincipal.deriv.neg.div hprincipal h₀).sub ?_)
  exact Finset.analyticAt_fun_sum _ fun χ hχ ↦ hterm χ (by simpa using hχ)

/-- A common bound for the logarithmic derivatives of the pole-cleared L-functions bounds the
regular part of the von Mangoldt series by the same constant. -/
theorem norm_LFunctionResidueClassAux_le (a : ZMod q) {s : ℂ} {M : ℝ}
    (h₀ : ‖logDeriv (LFunctionTrivChar₁ q) s‖ ≤ M)
    (h : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖logDeriv χ.LFunction s‖ ≤ M) :
    ‖LFunctionResidueClassAux a s‖ ≤ M := by
  classical
  have hq : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card, card_eq_totient_of_hasEnoughRootsOfUnity]
  rw [LFunctionResidueClassAux, norm_mul, norm_inv, Complex.norm_natCast,
    inv_mul_eq_div, div_le_iff₀ hq, mul_comm M]
  calc
    _ ≤ M + ∑ _ ∈ ({1}ᶜ : Finset (DirichletCharacter ℂ q)), M := by
      refine (norm_sub_le _ _).trans (add_le_add ?_ ((norm_sum_le _ _).trans ?_))
      · simpa only [neg_div, norm_neg, logDeriv_apply] using h₀
      · refine Finset.sum_le_sum fun χ hχ ↦ ?_
        rw [mul_div_assoc, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one _)).trans
          (h χ (by simpa using hχ))
    _ = ∑ _ : DirichletCharacter ℂ q, M :=
      (Fintype.sum_eq_add_sum_compl (1 : DirichletCharacter ℂ q) fun _ ↦ M).symm
    _ = (q.totient : ℝ) * M := by simp [hcard]

/-- At `1 + z`, the von Mangoldt series on the invertible class `a`, omitting the terms in `S`,
multiplied by `z` and continued across `z = 0`. -/
noncomputable def residueClassTailNumerator (a : (ZMod q)ˣ) (S : Finset ℕ) (z : ℂ) : ℂ :=
  (q.totient : ℂ)⁻¹ + z * (LFunctionResidueClassAux (a : ZMod q) (1 + z) -
    ∑ n ∈ S, LSeries.term (fun m ↦ (residueClass (a : ZMod q) m : ℂ)) (1 + z) n)

/-- The shifted numerator is the residue plus the shifted variable times the regular part
minus that variable times the removed terms. -/
theorem residueClassTailNumerator_def (a : (ZMod q)ˣ) (S : Finset ℕ) (z : ℂ) :
    residueClassTailNumerator a S z =
      (q.totient : ℂ)⁻¹ + z * (LFunctionResidueClassAux (a : ZMod q) (1 + z) -
        ∑ n ∈ S, LSeries.term (fun m ↦ (residueClass (a : ZMod q) m : ℂ)) (1 + z) n) :=
  (rfl)

/-- Subtracting the finite Dirichlet sum from the uncut numerator gives the truncated numerator. -/
theorem residueClassTailNumerator_eq_empty_sub (a : (ZMod q)ˣ) (S : Finset ℕ) (z : ℂ) :
    residueClassTailNumerator a S z = residueClassTailNumerator a ∅ z -
      z * ∑ n ∈ S, LSeries.term (fun m ↦ (residueClass (a : ZMod q) m : ℂ)) (1 + z) n := by
  simp only [residueClassTailNumerator_def, Finset.sum_empty, sub_zero, mul_sub, add_sub_assoc]

/-- The central value is independent of the cutoff: it is the residue of the full series at `1`. -/
@[simp] theorem residueClassTailNumerator_zero (a : (ZMod q)ˣ) (S : Finset ℕ) :
    residueClassTailNumerator a S 0 = (q.totient : ℂ)⁻¹ := by
  simp [residueClassTailNumerator_def]

/-- The numerator divided by `z` sums the tail on the half-plane of absolute convergence. -/
theorem hasSum_residueClassTailNumerator_div (a : (ZMod q)ˣ) (S : Finset ℕ) {z : ℂ}
    (hz : 0 < z.re) :
    HasSum (fun n : {n : ℕ // n ∉ S} ↦
      LSeries.term (fun m ↦ (residueClass (a : ZMod q) m : ℂ)) (1 + z) n)
      (residueClassTailNumerator a S z / z) := by
  have hs : 1 < (1 + z).re := by simpa using hz
  have hsum := LSeriesSummable_of_abscissaOfAbsConv_lt_re
    ((abscissaOfAbsConv_residueClass_le_one (a : ZMod q)).trans_lt (by exact_mod_cast hs))
  have hz₀ : z ≠ 0 := fun hz' ↦ by simp [hz'] at hz
  have heq := eqOn_LFunctionResidueClassAux a.isUnit hs
  have htail := (Finset.hasSum_iff_compl S).mp hsum.hasSum
  convert htail using 1
  simp only [residueClassTailNumerator_def, heq, add_sub_cancel_left, add_div,
    mul_div_cancel_left₀ _ hz₀, LSeries]
  ring

/-- The removed terms are entire, so the continuation of the shifted tail is analytic
wherever the pole-cleared Dirichlet L-functions are nonzero. -/
theorem analyticAt_residueClassTailNumerator (a : (ZMod q)ˣ) (S : Finset ℕ) {z : ℂ}
    (h₀ : LFunctionTrivChar₁ q (1 + z) ≠ 0)
    (h : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → χ.LFunction (1 + z) ≠ 0) :
    AnalyticAt ℂ (residueClassTailNumerator a S) z := by
  have hshift : AnalyticAt ℂ (fun v : ℂ ↦ 1 + v) z := analyticAt_const.add analyticAt_id
  unfold residueClassTailNumerator
  refine analyticAt_const.add (analyticAt_id.mul
    (((analyticAt_LFunctionResidueClassAux (a : ZMod q) h₀ h).comp hshift).sub ?_))
  refine S.analyticAt_fun_sum fun n _ ↦ ?_
  have hdiff : Differentiable ℂ
      (fun s ↦ LSeries.term (fun m ↦ (residueClass (a : ZMod q) m : ℂ)) s n) :=
    fun s ↦ (LSeries.hasDerivAt_term _ n s).differentiableAt
  exact (hdiff.analyticAt (1 + z)).comp hshift

/-- The uncut numerator grows at most linearly in the distance from `z = 0`, with slope bounded
by a common bound for the logarithmic derivatives. In particular, on `‖z‖ ≤ 1 / M` its norm is
at most `2` if all the logarithmic derivatives have norm at most `M > 0`. -/
theorem norm_residueClassTailNumerator_empty_le (a : (ZMod q)ˣ) {z : ℂ} {M : ℝ}
    (h₀ : ‖logDeriv (LFunctionTrivChar₁ q) (1 + z)‖ ≤ M)
    (h : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ‖logDeriv χ.LFunction (1 + z)‖ ≤ M) :
    ‖residueClassTailNumerator a ∅ z‖ ≤ (q.totient : ℝ)⁻¹ + ‖z‖ * M := by
  rw [residueClassTailNumerator_def, Finset.sum_empty, sub_zero]
  exact (norm_add_le _ _).trans (by
    rw [norm_inv, Complex.norm_natCast, norm_mul]
    gcongr
    exact norm_LFunctionResidueClassAux_le (a : ZMod q) h₀ h)

end ArithmeticFunction.vonMangoldt
