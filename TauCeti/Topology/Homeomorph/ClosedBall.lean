/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import TauCeti.Analysis.Normed.Module.Ball.Retraction
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# Extending and recentering boundary-fixing homeomorphisms of a closed ball

A homeomorphism of the closed unit ball that fixes the unit sphere extends by the identity
outside the ball. This construction works in every real normed space. It supplies the ambient
homeomorphism used in Alexander's trick.

The extension is expressed using the radial retraction, so continuity at the sphere follows
without a separate gluing argument.

Conversely, in a complete real normed space, any point `q` of the open unit ball is the image of
`0` under an explicit ambient homeomorphism `Homeomorph.shiftBallZero`
(`x ↦ x + max (1 - ‖x‖) 0 • q`) which fixes every point outside the open unit ball — in particular
every point of the unit sphere — and restricts to a boundary-fixing self-homeomorphism
`Homeomorph.shiftClosedBallZero` of the closed unit ball.

## References

* B. Farb, D. Margalit, *A Primer on Mapping Class Groups*, Section 2.2.1, Lemma 2.1.
-/

public section

noncomputable section

open Metric Set
open TauCeti

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section ExtendClosedBall

private def ballExtension (f : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1) (x : E) : E :=
  (f ⟨radialRetraction 1 x, radialRetraction_mem_closedBall zero_le_one x⟩ : E) +
    (x - radialRetraction 1 x)

private theorem ballExtension_coe (f : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1)
    (x : closedBall (0 : E) 1) : ballExtension f x = f x := by
  have h : radialRetraction 1 (x : E) = x :=
    radialRetraction_of_norm_le (mem_closedBall_zero_iff.mp x.2)
  simp [ballExtension, h]

private theorem ballExtension_of_one_le (f : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1)
    (hf : ∀ x : closedBall (0 : E) 1, ‖(x : E)‖ = 1 → f x = x)
    {x : E} (hx : 1 ≤ ‖x‖) : ballExtension f x = x := by
  have hr : ‖radialRetraction 1 x‖ = 1 := by
    rw [norm_radialRetraction zero_le_one, min_eq_right hx]
  rw [ballExtension, hf _ hr]
  simp

private theorem ballExtension_inverse (f : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1)
    (hf : ∀ x : closedBall (0 : E) 1, ‖(x : E)‖ = 1 → f x = x)
    (x : E) : ballExtension f.symm (ballExtension f x) = x := by
  have hfs : ∀ x : closedBall (0 : E) 1, ‖(x : E)‖ = 1 → f.symm x = x := by
    intro x hx
    rw [f.symm_apply_eq, hf x hx]
  by_cases hx : ‖x‖ ≤ 1
  · let y : closedBall (0 : E) 1 := ⟨x, mem_closedBall_zero_iff.mpr hx⟩
    rw [ballExtension_coe f y, ballExtension_coe f.symm (f y), f.symm_apply_apply]
  · rw [ballExtension_of_one_le f hf (le_of_not_ge hx),
      ballExtension_of_one_le f.symm hfs (le_of_not_ge hx)]

/-- Extend a homeomorphism of the closed unit ball fixing the unit sphere by the identity
outside the ball. -/
def extendClosedBall (f : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1)
    (hf : ∀ x : closedBall (0 : E) 1, ‖(x : E)‖ = 1 → f x = x) : E ≃ₜ E where
  toFun := ballExtension f
  invFun := ballExtension f.symm
  left_inv := ballExtension_inverse f hf
  right_inv := ballExtension_inverse f.symm (fun x hx => by rw [f.symm_apply_eq, hf x hx])
  continuous_toFun := by
    have hr := (lipschitzWith_radialRetraction (E := E) zero_le_one).continuous
    exact (continuous_subtype_val.comp (f.continuous.comp (hr.subtype_mk _))).add
      (continuous_id.sub hr)
  continuous_invFun := by
    have hr := (lipschitzWith_radialRetraction (E := E) zero_le_one).continuous
    exact (continuous_subtype_val.comp (f.symm.continuous.comp (hr.subtype_mk _))).add
      (continuous_id.sub hr)

variable (f : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1)
  (hf : ∀ x : closedBall (0 : E) 1, ‖(x : E)‖ = 1 → f x = x)

/-- On the closed ball the extension agrees with the given homeomorphism. -/
@[simp]
theorem extendClosedBall_coe (x : closedBall (0 : E) 1) :
    f.extendClosedBall hf x = (f x : E) :=
  ballExtension_coe f x

/-- The extension fixes the complement of the open unit ball, including its boundary. -/
theorem extendClosedBall_of_one_le {x : E} (hx : 1 ≤ ‖x‖) :
    f.extendClosedBall hf x = x :=
  ballExtension_of_one_le f hf hx

/-- Extending the inverse gives the inverse extension. -/
@[simp]
theorem symm_extendClosedBall :
    (f.extendClosedBall hf).symm =
      f.symm.extendClosedBall (fun x hx => by rw [f.symm_apply_eq, hf x hx]) :=
  (rfl)

/-- The extension and its inverse preserve membership in the closed unit ball. -/
@[simp]
theorem norm_extendClosedBall_le_one_iff (x : E) :
    ‖f.extendClosedBall hf x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  simp only [← mem_closedBall_zero_iff]
  by_cases hx : x ∈ closedBall (0 : E) 1
  · simpa only [hx, iff_true, extendClosedBall_coe f hf ⟨x, hx⟩] using (f ⟨x, hx⟩).2
  · have hx' : 1 ≤ ‖x‖ :=
      le_of_lt (not_le.mp (fun h => hx (mem_closedBall_zero_iff.mpr h)))
    rw [extendClosedBall_of_one_le f hf hx']

/-- The identity extension moves every point by at most twice the unit radius. -/
theorem norm_extendClosedBall_sub_le (x : E) : ‖f.extendClosedBall hf x - x‖ ≤ 2 := by
  by_cases hx : ‖x‖ ≤ 1
  · let y : closedBall (0 : E) 1 := ⟨x, mem_closedBall_zero_iff.mpr hx⟩
    rw [extendClosedBall_coe f hf y]
    exact (norm_sub_le _ _).trans (by
      have := mem_closedBall_zero_iff.mp (f y).2
      linarith)
  · rw [extendClosedBall_of_one_le f hf (le_of_not_ge hx), sub_self, norm_zero]
    norm_num

end ExtendClosedBall

section ShiftBallZero

private theorem approximatesLinearOn_shiftBallZero (q : E) :
    ApproximatesLinearOn (fun x : E ↦ x + max (1 - ‖x‖) 0 • q)
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) univ ‖q‖₊ := by
  intro x _ y _
  have hsub : (x + max (1 - ‖x‖) 0 • q) - (y + max (1 - ‖y‖) 0 • q) -
      (ContinuousLinearEquiv.refl ℝ E : E →L[ℝ] E) (x - y) =
      (max (1 - ‖x‖) 0 - max (1 - ‖y‖) 0) • q := by
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.refl_apply, sub_smul]
    abel
  rw [hsub, norm_smul, Real.norm_eq_abs, mul_comm, coe_nnNorm]
  gcongr
  calc |max (1 - ‖x‖) 0 - max (1 - ‖y‖) 0|
      ≤ |(1 - ‖x‖) - (1 - ‖y‖)| := abs_max_sub_max_le_abs _ _ _
    _ = |‖y‖ - ‖x‖| := by ring_nf
    _ = |‖x‖ - ‖y‖| := abs_sub_comm _ _
    _ ≤ ‖x - y‖ := abs_norm_sub_norm_le x y

variable [CompleteSpace E] {q : E}

/-- An ambient self-homeomorphism `x ↦ x + max (1 - ‖x‖) 0 • q` of a complete real normed space
sending `0` to a prescribed point `q` of the open unit ball while fixing every point outside the
open unit ball. -/
def shiftBallZero (hq : ‖q‖ < 1) : E ≃ₜ E :=
  (approximatesLinearOn_shiftBallZero q).toHomeomorph _ <| by
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    · refine Or.inr ?_
      have hid : ((ContinuousLinearEquiv.refl ℝ E).symm : E →L[ℝ] E) =
          ContinuousLinearMap.id ℝ E := rfl
      rw [hid, ContinuousLinearMap.nnNorm_id, inv_one]
      exact_mod_cast hq

/-- Explicit formula for `shiftBallZero`. -/
theorem shiftBallZero_apply (hq : ‖q‖ < 1) (x : E) :
    shiftBallZero hq x = x + max (1 - ‖x‖) 0 • q :=
  (rfl)

/-- `shiftBallZero hq` sends `0` to `q`. -/
@[simp]
theorem shiftBallZero_zero (hq : ‖q‖ < 1) : shiftBallZero hq 0 = q := by
  simp [shiftBallZero_apply]

/-- `shiftBallZero` fixes every point outside the open unit ball, including the unit sphere. -/
theorem shiftBallZero_of_one_le (hq : ‖q‖ < 1) {x : E} (hx : 1 ≤ ‖x‖) :
    shiftBallZero hq x = x := by
  have h0 : max (1 - ‖x‖) 0 = 0 := max_eq_right (sub_nonpos.mpr hx)
  simp [shiftBallZero_apply, h0]

/-- `shiftBallZero` preserves membership in the open unit ball. -/
@[simp]
theorem norm_shiftBallZero_lt_one_iff (hq : ‖q‖ < 1) (x : E) :
    ‖shiftBallZero hq x‖ < 1 ↔ ‖x‖ < 1 := by
  constructor
  · contrapose!
    intro hx
    rwa [shiftBallZero_of_one_le hq hx]
  · intro hx
    have hpos : 0 < 1 - ‖x‖ := sub_pos.mpr hx
    rw [shiftBallZero_apply, max_eq_left hpos.le]
    calc ‖x + (1 - ‖x‖) • q‖
        ≤ ‖x‖ + ‖(1 - ‖x‖) • q‖ := norm_add_le _ _
      _ = ‖x‖ + (1 - ‖x‖) * ‖q‖ := by
        rw [norm_smul, Real.norm_of_nonneg hpos.le]
      _ < ‖x‖ + (1 - ‖x‖) * 1 := by gcongr
      _ = 1 := by ring

/-- `shiftBallZero` preserves membership in the closed unit ball. -/
@[simp]
theorem norm_shiftBallZero_le_one_iff (hq : ‖q‖ < 1) (x : E) :
    ‖shiftBallZero hq x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
  constructor
  · contrapose!
    intro hx
    rwa [shiftBallZero_of_one_le hq hx.le]
  · intro hx
    rcases hx.lt_or_eq with hx' | hx'
    · exact ((norm_shiftBallZero_lt_one_iff hq x).mpr hx').le
    · rw [shiftBallZero_of_one_le hq hx'.ge, hx']

/-- `shiftBallZero` preserves membership in the unit sphere. -/
@[simp]
theorem norm_shiftBallZero_eq_one_iff (hq : ‖q‖ < 1) (x : E) :
    ‖shiftBallZero hq x‖ = 1 ↔ ‖x‖ = 1 := by
  simp only [le_antisymm_iff, norm_shiftBallZero_le_one_iff hq, ← not_lt,
    norm_shiftBallZero_lt_one_iff hq]

/-- Self-homeomorphism of the closed unit ball in a complete real normed space sending `0` to a
prescribed interior point `q` while fixing the boundary sphere pointwise. -/
def shiftClosedBallZero (hq : ‖q‖ < 1) : closedBall (0 : E) 1 ≃ₜ closedBall (0 : E) 1 :=
  (shiftBallZero hq).subtype fun x ↦ by simp

/-- On the closed unit ball, `shiftClosedBallZero` agrees with `shiftBallZero`. -/
@[simp]
theorem coe_shiftClosedBallZero_apply (hq : ‖q‖ < 1) (x : closedBall (0 : E) 1) :
    (shiftClosedBallZero hq x : E) = shiftBallZero hq x :=
  (rfl)

/-- `shiftClosedBallZero hq` sends `0` to `q`. -/
@[simp]
theorem shiftClosedBallZero_zero (hq : ‖q‖ < 1) :
    shiftClosedBallZero hq ⟨0, mem_closedBall_self zero_le_one⟩ =
      ⟨q, mem_closedBall_zero_iff.mpr hq.le⟩ :=
  Subtype.ext (shiftBallZero_zero hq)

/-- `shiftClosedBallZero` fixes every boundary point of the closed unit ball. -/
theorem shiftClosedBallZero_of_norm_eq_one (hq : ‖q‖ < 1) {x : closedBall (0 : E) 1}
    (hx : ‖(x : E)‖ = 1) : shiftClosedBallZero hq x = x :=
  Subtype.ext (shiftBallZero_of_one_le hq hx.ge)

end ShiftBallZero

end Homeomorph
