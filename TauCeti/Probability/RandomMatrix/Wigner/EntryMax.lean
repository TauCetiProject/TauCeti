/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Basic
import TauCeti.Probability.IdentDistrib
import TauCeti.Probability.RandomMatrix.Wigner.CornerEnumeration

/-!
# Maximum entry of a Wigner corner

A finite fourth moment controls the maximum absolute normalized entry of a zero-diagonal
Wigner corner almost surely, even with dependent upper entries.
-/

public section

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

/-- The largest absolute entry of the zero-diagonal normalized Wigner corners vanishes
almost surely for identically distributed upper entries of finite fourth moment.
Independence is unnecessary. -/
theorem ae_eventually_norm_wignerMatrix_zero_apply_le
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {Q : Measure Ω'} {ξ : StrictUpper → Ω → ℂ} {X : Ω' → ℂ}
    (hid : ∀ ij, IdentDistrib (ξ ij) X P Q) (hX : MemLp X 4 Q) :
    ∀ᵐ ω ∂P, ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ i j : Fin (n + 1), ‖wignerMatrix ξ (fun _ _ ↦ 0) (n + 1) ω i j‖ ≤ ε := by
  have hs : Tendsto (fun n : ℕ ↦ Real.sqrt (n + 1 : ℕ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hm : ∀ᶠ n : ℕ in atTop, ((n + 1).choose 2 : ℝ) ≤ Real.sqrt (n + 1 : ℕ) ^ 4 :=
    .of_forall fun n ↦ by
      have hpow : Real.sqrt (n + 1 : ℕ) ^ 4 = ((n + 1 : ℕ) : ℝ) ^ 2 := calc
        _ = (Real.sqrt (n + 1 : ℕ) ^ 2) ^ 2 := by norm_num [← pow_mul]
        _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]
      rw [hpow]
      exact_mod_cast Nat.choose_le_pow (n + 1) 2
  filter_upwards [ae_eventually_forall_lt_norm_le_mul_of_identDistrib
    (p := 4) (fun k ↦ hid (strictUpperEquivNat.symm k)) hX hs
    (by simpa only [NNReal.coe_ofNat, ← Real.rpow_natCast, Nat.cast_ofNat] using hm)] with ω hω
  intro ε hε
  filter_upwards [hω ε hε] with n hn i j
  have hscale (ij : StrictUpper) (hij : ij.val.2 < n + 1) :
      (Real.sqrt (n + 1 : ℕ))⁻¹ * ‖ξ ij ω‖ ≤ ε := by
    have h := hn _ ((strictUpperEquivNat_lt_choose_iff ij _).2 hij)
    rw [Equiv.symm_apply_apply] at h
    rw [inv_mul_eq_div, div_le_iff₀ (Real.sqrt_pos.2 (by positivity)), mul_comm]
    simpa only [mul_comm ε] using h
  by_cases hij : i = j
  · subst j
    simpa using hε.le
  · rw [norm_wignerMatrix_apply_of_ne _ _ _ hij]
    exact hscale _ (max_lt i.isLt j.isLt)

end TauCeti.Probability
