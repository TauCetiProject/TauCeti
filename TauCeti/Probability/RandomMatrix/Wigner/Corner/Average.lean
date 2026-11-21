/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.RandomMatrix.Wigner.Corner.Enumeration
import TauCeti.Algebra.BigOperators.Finset.Pairs
import TauCeti.Data.Nat.Choose.Basic
import Mathlib.Probability.StrongLaw
public import Mathlib.Analysis.Matrix.Normed

/-!
# Strong law for upper-triangular corners

In column order, the strictly upper entries of an `n × n` corner form an initial segment of
length `n.choose 2`. The strong law then controls empirical averages over the corner, including
the entrywise squared errors that give the Frobenius distance of two Wigner matrices.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory
open scoped Topology Matrix.Norms.Frobenius

namespace TauCeti

namespace Probability

/-- Squared Frobenius error between Wigner matrices with a common diagonal, in terms of
the squared errors on the strictly upper corner. -/
theorem norm_wignerMatrix_sub_sq_eq_sum_strictUpperFin
    {Ω : Type*} {ξ : StrictUpper → Ω → ℂ} (ζ : StrictUpper → Ω → ℂ)
    (η : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    ‖wignerMatrix ξ η n ω - wignerMatrix ζ η n ω‖ ^ 2 =
      (2 / (n : ℝ)) * ∑ i : StrictUpperFin n,
        ‖ξ (wignerUpperIndex i) ω - ζ (wignerUpperIndex i) ω‖ ^ 2 := by
  let D := wignerMatrix ξ η n ω - wignerMatrix ζ η n ω
  have hD : D.IsHermitian :=
    (wignerMatrix_isHermitian ξ η ω n).sub (wignerMatrix_isHermitian ζ η ω n)
  have hsymm (i j : Fin n) : ‖D i j‖ ^ 2 = ‖D j i‖ ^ 2 := by
    rw [← hD.apply i j, norm_star]
  have hdiag (i : Fin n) : ‖D i i‖ ^ 2 = 0 := by
    simp [D]
  have hn : ‖(Real.sqrt n : ℂ)⁻¹‖ ^ 2 = (n : ℝ)⁻¹ := by
    simp [norm_inv, Complex.norm_real, abs_of_nonneg (Real.sqrt_nonneg _), inv_pow,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  have hupper (p : StrictUpperFin n) : ‖D p.val.1 p.val.2‖ ^ 2 =
      (n : ℝ)⁻¹ * ‖ξ (wignerUpperIndex p) ω - ζ (wignerUpperIndex p) ω‖ ^ 2 := by
    have hp : wignerUpperIndex p = ⟨(p.val.1.val, p.val.2.val), p.prop⟩ :=
      Subtype.ext (wignerUpperIndex_val _)
    simp only [D, Matrix.sub_apply, wignerMatrix_apply_of_lt _ _ _ p.prop,
      hp, ← mul_sub, norm_mul, mul_pow, hn]
  rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two]
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _),
    sum_symmetric_pairs _ hsymm]
  simp only [hdiag, Finset.sum_const_zero, zero_add, hupper, ← Finset.mul_sum, nsmul_eq_mul,
    Nat.cast_ofNat, div_eq_mul_inv, mul_assoc]
  rfl

/-- Strong law for the arithmetic means of the strictly upper triangular corners of an
identically distributed, pairwise independent array. -/
theorem ae_tendsto_sum_strictUpperFin_div {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : StrictUpper → Ω → ℝ} (hInt : Integrable (X ⟨(0, 1), by decide⟩) P)
    (hind : Pairwise fun i j ↦ IndepFun (X i) (X j) P)
    (hid : ∀ i, IdentDistrib (X i) (X ⟨(0, 1), by decide⟩) P P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ ↦
      (∑ ij : StrictUpperFin n, X (wignerUpperIndex ij) ω) / (n.choose 2 : ℝ))
      atTop (𝓝 (∫ ω, X ⟨(0, 1), by decide⟩ ω ∂P)) := by
  let Y (k : ℕ) := X (strictUpperEquivNat.symm k)
  have h0 : strictUpperEquivNat.symm 0 = ⟨(0, 1), by decide⟩ := by
    apply strictUpperEquivNat.injective
    simp
  have hd : Tendsto (fun n : ℕ ↦ n.choose 2) atTop atTop := by
    refine tendsto_atTop_mono' _ ?_ tendsto_id
    filter_upwards [eventually_ge_atTop (3 : ℕ)] with n hn
    have hs := Nat.add_choose_two (n - 1) 1
    simp only [Nat.choose_eq_zero_of_lt (by decide : 1 < 2), add_zero, Nat.mul_one] at hs
    have hp : 1 ≤ (n - 1).choose 2 := Nat.choose_pos (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hs
    dsimp only [id_eq]
    omega
  have hY := strong_law_ae_real Y (by simpa only [Y, h0] using hInt)
    (fun i j hij ↦ hind (strictUpperEquivNat.symm.injective.ne hij))
    (fun i ↦ by simpa only [Y, h0] using hid (strictUpperEquivNat.symm i))
  filter_upwards [hY] with ω hω
  simp_rw [sum_strictUpperFin_eq_sum_range _ (fun ij ↦ X ij ω)]
  simpa only [Function.comp_def, Y, h0] using hω.comp hd

end Probability

end TauCeti
