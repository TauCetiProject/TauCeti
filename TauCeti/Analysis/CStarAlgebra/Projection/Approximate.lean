/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.RoundProjection

/-!
# Projections from approximate data

The perturbation steps that replace approximate projections in a C⋆-algebra, possibly without unit,
by exact ones.

* **Rounding.** A self-adjoint element `x` with `‖x - x * x‖ ≤ δ < 1/4` is within `2δ` of a star
  projection (`TauCeti.exists_isStarProjection_norm_sub_le`): the spectral projection
  `TauCeti.roundProjection x = χ_{[1/2, ∞)}(x)`, computed directly in `A` via `cfcₙ`.
* **Defect estimate.** An element within `η ≤ 1` of a projection has defect `‖x - x * x‖ ≤ 4η`
  (`IsStarProjection.norm_sub_mul_self_le`).

These are the projection-perturbation steps of the continuity of `K₀` along C⋆-inductive limits.

## Main statements

* `TauCeti.exists_isStarProjection_norm_sub_le`: rounding an almost-projection.
* `IsStarProjection.norm_sub_mul_self_le`: the defect estimate near a projection.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  5.2.4.
-/

public section

namespace TauCeti

section Rounding

variable {A : Type*} [NonUnitalCStarAlgebra A]

/-- **Rounding an almost-projection, without unit.** A self-adjoint element `x` of a C⋆-algebra,
possibly without unit, with `‖x - x * x‖ ≤ δ < 1/4` is within `2δ` of a star projection. -/
theorem exists_isStarProjection_norm_sub_le {x : A} (hx : IsSelfAdjoint x) {δ : ℝ}
    (hδ : ‖x - x * x‖ ≤ δ) (hδ4 : δ < 1 / 4) :
    ∃ p : A, IsStarProjection p ∧ ‖x - p‖ ≤ 2 * δ :=
  ⟨roundProjection x, isStarProjection_roundProjection x,
    by simpa only [norm_sub_rev] using hx.norm_sub_roundProjection_le (by rwa [norm_sub_rev]) hδ4⟩

end Rounding

end TauCeti

namespace IsStarProjection

variable {A : Type*} [NonUnitalCStarAlgebra A] {p : A}

/-- **Defect near a projection.** If `‖x - p‖ ≤ η ≤ 1` for a star projection `p`, then
`‖x - x * x‖ ≤ 4 η`. -/
theorem norm_sub_mul_self_le {x : A} (hp : IsStarProjection p) {η : ℝ} (hx : ‖x - p‖ ≤ η)
    (hη : η ≤ 1) : ‖x - x * x‖ ≤ 4 * η := by
  set d := x - p with hd
  have he : x - x * x = d - (p * d + d * p + d * d) := by
    rw [show x = p + d by rw [hd]; abel]
    have hpp : p * p = p := hp.isIdempotentElem.eq
    noncomm_ring
    rw [hpp]
    abel
  have hp1 : ‖p‖ ≤ 1 := hp.norm_le
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hx
  rw [he]
  calc ‖d - (p * d + d * p + d * d)‖ ≤ ‖d‖ + (‖p‖ * ‖d‖ + ‖d‖ * ‖p‖ + ‖d‖ * ‖d‖) := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_add₃_le).trans ?_
        gcongr <;> exact norm_mul_le _ _
    _ ≤ η + (1 * η + η * 1 + η * η) := by gcongr
    _ ≤ 4 * η := by nlinarith [norm_nonneg d]

end IsStarProjection
