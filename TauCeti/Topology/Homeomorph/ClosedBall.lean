/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import TauCeti.Analysis.Normed.Module.Ball.Retraction

/-!
# Extending boundary-fixing homeomorphisms of a closed ball

A homeomorphism of the closed unit ball that fixes the unit sphere extends by the identity
outside the ball. This construction works in every real normed space. It supplies the ambient
homeomorphism used in Alexander's trick.

The extension is expressed using the radial retraction, so continuity at the sphere follows
without a separate gluing argument.

## References

* B. Farb, D. Margalit, *A Primer on Mapping Class Groups*, Section 2.2.1, Lemma 2.1.
-/

public section

noncomputable section

open Metric Set
open TauCeti

namespace Homeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

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

end Homeomorph
