/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.LinearCombination
import Mathlib.Analysis.Normed.Operator.NNNorm
import TauCeti.Analysis.Normed.Operator.Basic

/-!
# Canonical summation from `ℓ¹` of the closed unit ball

Every Banach space `E` over a nontrivially normed field `𝕜` is a quotient of an `ℓ¹` space: the
inclusion of the closed unit ball `Metric.closedBall (0 : E) 1` into `E` is a bounded family of
`ℓ∞` norm at most `1`, so `lp.linearCombination` extends it to a contractive continuous linear map

`TauCeti.unitClosedBallSummation 𝕜 E : lp (fun _ : Metric.closedBall (0 : E) 1 ↦ 𝕜) 1 →L[𝕜] E`,
`a ↦ ∑' y, a y • (y : E)`.

This is the projective counterpart of `TauCeti.dualBallEmbedding` in
`TauCeti.Analysis.Normed.Module.Dual.Embedding`, which embeds a normed space isometrically into
`ℓ∞` of its dual unit ball. Over any nontrivially normed field, `unitClosedBallSummation 𝕜 E` is
surjective. Over a densely normed field, rescaling into the closed unit ball by scalars of norm
arbitrarily close to `‖x‖` lifts every open ball `Metric.ball (0 : E) r` into the open ball of the
same radius in `ℓ¹`, making `unitClosedBallSummation 𝕜 E` a metric quotient map. Consequently,
precomposition with `unitClosedBallSummation 𝕜 E` preserves operator norms.

## Main definitions

* `TauCeti.unitClosedBallFamily`: the tautological bounded family in `ℓ∞` indexed by
  `Metric.closedBall (0 : E) 1`.
* `TauCeti.unitClosedBallSummation`: the canonical summation map
  `lp (fun _ : Metric.closedBall (0 : E) 1 ↦ R) 1 →L[R] E`.

## Main results

* `TauCeti.unitClosedBallSummation_surjective`: surjectivity over any nontrivially normed field.
* `TauCeti.ball_subset_image_unitClosedBallSummation_ball` and
  `TauCeti.image_unitClosedBallSummation_ball`: over a densely normed field, every open ball around
  `0` lifts to and equals the image of the open ball of the same radius.
* `TauCeti.norm_unitClosedBallSummation`: on a nontrivial Banach space over a densely normed field,
  `‖unitClosedBallSummation 𝕜 E‖ = 1`.
* `ContinuousLinearMap.norm_comp_unitClosedBallSummation`: precomposition with
  `unitClosedBallSummation 𝕜 E` preserves the operator norm.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, 2nd ed., Springer, 2016,
  Proposition 2.1.9.
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge University Press, 1987, Chapter 2.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

section Family

variable (E : Type*) [NormedAddCommGroup E]

/-- The tautological bounded family of points of the closed unit ball of `E`, viewed as an element
of `ℓ∞`. -/
noncomputable def unitClosedBallFamily :
    lp (fun _ : Metric.closedBall (0 : E) 1 ↦ E) ∞ :=
  ⟨Subtype.val, memℓp_infty ⟨1, by
    rintro _ ⟨y, rfl⟩
    exact mem_closedBall_zero_iff.mp y.2⟩⟩

/-- Coordinate evaluation of `unitClosedBallFamily` is subtype coercion. -/
@[simp]
theorem unitClosedBallFamily_apply (y : Metric.closedBall (0 : E) 1) :
    unitClosedBallFamily E y = (y : E) :=
  (rfl)

/-- The `ℓ∞` norm of `unitClosedBallFamily E` is at most `1`. -/
theorem norm_unitClosedBallFamily_le : ‖unitClosedBallFamily E‖ ≤ 1 :=
  lp.norm_le_of_forall_le zero_le_one fun y ↦ mem_closedBall_zero_iff.mp y.2

/-- The nonnegative `ℓ∞` norm of `unitClosedBallFamily E` is at most `1`. -/
theorem nnNorm_unitClosedBallFamily_le : ‖unitClosedBallFamily E‖₊ ≤ 1 :=
  mod_cast norm_unitClosedBallFamily_le E

end Family

section Ring

variable (R E : Type*) [NormedRing R] [NormedAddCommGroup E] [Module R E] [IsBoundedSMul R E]
  [CompleteSpace E]

/-- The canonical continuous `R`-linear summation map from `ℓ¹` on the closed unit ball of `E` into
`E`, sending `a` to `∑' y, a y • (y : E)`. -/
noncomputable def unitClosedBallSummation :
    lp (fun _ : Metric.closedBall (0 : E) 1 ↦ R) 1 →L[R] E :=
  lp.linearCombination R (unitClosedBallFamily E)

/-- `unitClosedBallSummation` is `lp.linearCombination` applied to `unitClosedBallFamily`. -/
theorem unitClosedBallSummation_eq_linearCombination :
    unitClosedBallSummation R E = lp.linearCombination R (unitClosedBallFamily E) :=
  (rfl)

/-- Pointwise formula for `unitClosedBallSummation`. -/
theorem unitClosedBallSummation_apply (a : lp (fun _ : Metric.closedBall (0 : E) 1 ↦ R) 1) :
    unitClosedBallSummation R E a = ∑' y : Metric.closedBall (0 : E) 1, a y • (y : E) :=
  lp.linearCombination_apply (unitClosedBallFamily E) a

/-- Unconditional series expansion of `unitClosedBallSummation R E a`. -/
theorem hasSum_unitClosedBallSummation (a : lp (fun _ : Metric.closedBall (0 : E) 1 ↦ R) 1) :
    HasSum (fun y : Metric.closedBall (0 : E) 1 ↦ a y • (y : E))
      (unitClosedBallSummation R E a) :=
  lp.hasSum_linearCombination (unitClosedBallFamily E) a

/-- On a coordinate vector `lp.single 1 y r`, `unitClosedBallSummation` evaluates to `r • y`. -/
@[simp]
theorem unitClosedBallSummation_single [DecidableEq (Metric.closedBall (0 : E) 1)]
    (y : Metric.closedBall (0 : E) 1) (r : R) :
    unitClosedBallSummation R E (lp.single 1 y r) = r • (y : E) :=
  lp.linearCombination_single (unitClosedBallFamily E) y r

/-- A continuous `R`-linear map out of `ℓ¹` of the closed unit ball equals
`unitClosedBallSummation R E` if and only if it sends each unit coordinate vector to its indexing
point. -/
theorem eq_unitClosedBallSummation_iff [DecidableEq (Metric.closedBall (0 : E) 1)]
    {u : lp (fun _ : Metric.closedBall (0 : E) 1 ↦ R) 1 →L[R] E} :
    u = unitClosedBallSummation R E ↔
      ∀ y : Metric.closedBall (0 : E) 1, u (lp.single 1 y 1) = (y : E) :=
  lp.eq_linearCombination_iff

/-- `unitClosedBallSummation` is pointwise norm-nonincreasing. -/
theorem norm_unitClosedBallSummation_apply_le
    (a : lp (fun _ : Metric.closedBall (0 : E) 1 ↦ R) 1) :
    ‖unitClosedBallSummation R E a‖ ≤ ‖a‖ :=
  calc ‖unitClosedBallSummation R E a‖
      ≤ ‖unitClosedBallFamily E‖ * ‖a‖ :=
        lp.norm_linearCombination_apply_le (unitClosedBallFamily E) a
    _ ≤ 1 * ‖a‖ := mul_le_mul_of_nonneg_right (norm_unitClosedBallFamily_le E) (norm_nonneg a)
    _ = ‖a‖ := one_mul _

end Ring

section NontriviallyNormedField

variable (𝕜 E : Type*) [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [CompleteSpace E]

/-- `unitClosedBallSummation 𝕜 E` is a contraction. -/
theorem norm_unitClosedBallSummation_le : ‖unitClosedBallSummation 𝕜 E‖ ≤ 1 :=
  (lp.norm_linearCombination (𝕜 := 𝕜) (unitClosedBallFamily E)).trans_le
    (norm_unitClosedBallFamily_le E)

/-- Nonnegative operator-norm contraction bound for `unitClosedBallSummation 𝕜 E`. -/
theorem nnNorm_unitClosedBallSummation_le : ‖unitClosedBallSummation 𝕜 E‖₊ ≤ 1 :=
  mod_cast norm_unitClosedBallSummation_le 𝕜 E

/-- Over any nontrivially normed field, `unitClosedBallSummation 𝕜 E` is surjective. -/
theorem unitClosedBallSummation_surjective :
    Function.Surjective (unitClosedBallSummation 𝕜 E) := by
  classical
  intro x
  obtain ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜 ‖x‖
  have hcpos : 0 < ‖c‖ := (norm_nonneg x).trans_lt hc
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  have hy : c⁻¹ • x ∈ Metric.closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv]
    exact (inv_mul_le_iff₀ hcpos).mpr (by simpa using hc.le)
  exact ⟨lp.single 1 ⟨c⁻¹ • x, hy⟩ c, by simp [smul_inv_smul₀ hc0]⟩

end NontriviallyNormedField

section DenselyNormedField

variable (𝕜 E : Type*) [DenselyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

include 𝕜 in
/-- Over a densely normed field, the closed unit ball of a nontrivial normed space has `ℓ∞` norm
`1`. -/
theorem norm_unitClosedBallFamily [Nontrivial E] : ‖unitClosedBallFamily E‖ = 1 := by
  refine le_antisymm (norm_unitClosedBallFamily_le E) (le_of_forall_lt fun r hr ↦ ?_)
  rcases lt_or_ge r 0 with hr0 | hr0
  · exact hr0.trans_le (norm_nonneg _)
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨c, hrc, hc1⟩ := NormedField.exists_lt_norm_lt 𝕜 (div_nonneg hr0 hxpos.le)
    (div_lt_div_of_pos_right hr hxpos)
  have hcx_gt : r < ‖c • x‖ := by
    rw [norm_smul]
    exact (div_lt_iff₀ hxpos).mp hrc
  have hcx_le : ‖c • x‖ ≤ 1 := by
    rw [norm_smul]
    exact ((lt_div_iff₀ hxpos).mp hc1).le
  let y : Metric.closedBall (0 : E) 1 := ⟨c • x, mem_closedBall_zero_iff.mpr hcx_le⟩
  exact hcx_gt.trans_le (lp.norm_apply_le_norm ENNReal.top_ne_zero (unitClosedBallFamily E) y)

variable [CompleteSpace E]

/-- Over a densely normed field, `unitClosedBallSummation 𝕜 E` lifts every vector of norm less
than `r` to an `ℓ¹` vector of norm less than `r`. -/
theorem ball_subset_image_unitClosedBallSummation_ball (r : ℝ) :
    Metric.ball (0 : E) r ⊆ unitClosedBallSummation 𝕜 E '' Metric.ball 0 r := by
  classical
  intro x hx
  have hxr : ‖x‖ < r := mem_ball_zero_iff.mp hx
  obtain ⟨c, hxc, hcr⟩ := NormedField.exists_lt_norm_lt 𝕜 (norm_nonneg x) hxr
  have hcpos : 0 < ‖c‖ := (norm_nonneg x).trans_lt hxc
  have hc0 : c ≠ 0 := norm_pos_iff.mp hcpos
  have hy : c⁻¹ • x ∈ Metric.closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv]
    exact (inv_mul_le_iff₀ hcpos).mpr (by simpa using hxc.le)
  refine ⟨lp.single 1 ⟨c⁻¹ • x, hy⟩ c, ?_, ?_⟩
  · simpa [mem_ball_zero_iff, lp.norm_single zero_lt_one] using hcr
  · simp [smul_inv_smul₀ hc0]

/-- **Metric quotient property**: over a densely normed field, `unitClosedBallSummation 𝕜 E` maps
each open ball around the origin onto the open ball of the same radius. -/
theorem image_unitClosedBallSummation_ball (r : ℝ) :
    unitClosedBallSummation 𝕜 E '' Metric.ball 0 r = Metric.ball 0 r :=
  (unitClosedBallSummation 𝕜 E).image_ball_eq_ball (norm_unitClosedBallSummation_le 𝕜 E)
    (ball_subset_image_unitClosedBallSummation_ball 𝕜 E) r

/-- On a nontrivial Banach space over a densely normed field, `unitClosedBallSummation 𝕜 E` has
operator norm `1`. -/
@[simp]
theorem norm_unitClosedBallSummation [Nontrivial E] :
    ‖unitClosedBallSummation 𝕜 E‖ = 1 :=
  (lp.norm_linearCombination (𝕜 := 𝕜) (unitClosedBallFamily E)).trans
    (norm_unitClosedBallFamily 𝕜 E)

/-- Nonnegative operator norm of `unitClosedBallSummation 𝕜 E` on a nontrivial Banach space over a
densely normed field. -/
@[simp]
theorem nnNorm_unitClosedBallSummation [Nontrivial E] :
    ‖unitClosedBallSummation 𝕜 E‖₊ = 1 :=
  NNReal.eq (norm_unitClosedBallSummation 𝕜 E)

end DenselyNormedField

end TauCeti

namespace ContinuousLinearMap

variable {𝕜 𝕜₂ E F : Type*} [DenselyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₂ F]
  {σ : 𝕜 →+* 𝕜₂} [RingHomIsometric σ]

/-- Precomposition with `TauCeti.unitClosedBallSummation 𝕜 E` preserves the operator norm. -/
@[simp]
theorem norm_comp_unitClosedBallSummation (T : E →SL[σ] F) :
    ‖T.comp (TauCeti.unitClosedBallSummation 𝕜 E)‖ = ‖T‖ := by
  rw [← (T.comp (TauCeti.unitClosedBallSummation 𝕜 E)).sSup_unit_ball_eq_norm,
    ← T.sSup_unit_ball_eq_norm, ← TauCeti.image_unitClosedBallSummation_ball 𝕜 E 1,
    Set.image_image]
  rfl

/-- Precomposition with `TauCeti.unitClosedBallSummation 𝕜 E` preserves the nonnegative operator
norm. -/
@[simp]
theorem nnNorm_comp_unitClosedBallSummation (T : E →SL[σ] F) :
    ‖T.comp (TauCeti.unitClosedBallSummation 𝕜 E)‖₊ = ‖T‖₊ :=
  NNReal.eq T.norm_comp_unitClosedBallSummation

end ContinuousLinearMap
