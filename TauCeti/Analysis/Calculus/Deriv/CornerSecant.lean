/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Ray
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import TauCeti.Analysis.Calculus.Deriv.Slope
import TauCeti.Analysis.LocallyConvex.Separation

/-!
# Short secants across a corner

Let `γ₁` and `γ₂` be two curves in a real normed space which meet at `γ₁ 0 = γ₂ 0`: think of
`γ₁` as the arc arriving at a corner, with left derivative `v₁` at `0`, and of `γ₂` as the arc
leaving it, with right derivative `v₂` at `0`. Suppose that `v₁` and `v₂` are nonzero and do
not point in opposite directions, `¬SameRay ℝ v₁ (-v₂)`, so that both tangents exist and the
corner is not a cusp; straight joins and corners of either sign are allowed. Then a single
continuous linear functional `L` is positive on both tangent vectors and on every short secant
`γ₂ (t + r) - γ₁ t`, `-r ≤ t ≤ 0`, from the arriving arc to the leaving one across the corner:
all these secants lie in one open half-space.

These secants control the moving-average rounding of a corner. If the continuous curve `γ` is
`γ₁` on `t ≤ 0` and `γ₂` on `t ≥ 0`, then for `ρ > 0` the `C¹` curve `c s = (2ρ)⁻¹ ∫ γ` over
`[s - ρ, s + ρ]` has velocity `c' s = (2ρ)⁻¹ (γ (s + ρ) - γ (s - ρ))`; for `|s| ≤ ρ` this is
the positive multiple `(2ρ)⁻¹` of such a secant, with `r = 2ρ` and `t = s - ρ`. So once
`2ρ < δ`, the rounded curve has nonzero velocity near the corner, lying in the open half-space
`{L > 0}`. For a curve in an oriented Euclidean plane this means that the tangent direction of
the rounded curve does not wind around the corner: its signed turning across the corner is the
angle in `(-π, π)` between two secant directions tending to `v₁` and `v₂`. The same secants
appear in Hopf's secant proof of the theorem of turning tangents for planar curves with corners.

## Main results

* `TauCeti.exists_strongDual_pos_secant_of_not_sameRay_neg`: the short secants across a corner
  lie in an open half-space containing both tangent vectors.

## References

* H. Hopf, *Über die Drehung der Tangenten und Sehnen ebener Kurven*, Compositio Math. 2
  (1935), 50–62.
-/

public section

open Set Filter
open scoped Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Short secants across a corner lie in an open half-space.** Let `γ₁` have left derivative
`v₁` and `γ₂` right derivative `v₂` at `0`, with `γ₁ 0 = γ₂ 0`, and with `v₁` and `v₂` nonzero
and not pointing in opposite directions, `¬SameRay ℝ v₁ (-v₂)`. Then there are `δ > 0` and a
continuous linear functional `L`, positive on both tangent vectors, such that
`0 < L (γ₂ (t + r) - γ₁ t)` whenever `0 < r < δ` and `-r ≤ t ≤ 0`. -/
theorem exists_strongDual_pos_secant_of_not_sameRay_neg {γ₁ γ₂ : ℝ → E} {v₁ v₂ : E}
    (h₁ : HasDerivWithinAt γ₁ v₁ (Iic 0) 0) (h₂ : HasDerivWithinAt γ₂ v₂ (Ici 0) 0)
    (h₀ : γ₁ 0 = γ₂ 0) (hne : ¬SameRay ℝ v₁ (-v₂)) :
    ∃ δ > 0, ∃ L : StrongDual ℝ E, 0 < L v₁ ∧ 0 < L v₂ ∧
      ∀ r ∈ Ioo (0 : ℝ) δ, ∀ t ∈ Icc (-r) 0, 0 < L (γ₂ (t + r) - γ₁ t) := by
  obtain ⟨L, hL₁, hL₂⟩ := exists_strongDual_pos_of_not_sameRay_neg hne
  obtain ⟨a, ha, hlt₁⟩ := (nhdsLT_basis (0 : ℝ)).eventually_iff.mp
    ((L.hasFDerivAt.comp_hasDerivWithinAt 0 h₁).Iio_of_Iic.eventually_nhdsLT_lt_of_pos hL₁)
  obtain ⟨b, hb, hlt₂⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp
    ((L.hasFDerivAt.comp_hasDerivWithinAt 0 h₂).Ioi_of_Ici.eventually_nhdsGT_lt_of_pos hL₂)
  refine ⟨min (-a) b, lt_min (neg_pos.2 ha) hb, L, hL₁, hL₂, fun r hr t ht => ?_⟩
  have hra : r < -a := hr.2.trans_le (min_le_left _ _)
  have hrb : r < b := hr.2.trans_le (min_le_right _ _)
  have hL₀ : L (γ₁ 0) = L (γ₂ 0) := by rw [h₀]
  rw [map_sub, sub_pos]
  rcases ht.2.lt_or_eq with htlt | rfl
  · have h₁ : L (γ₁ t) < L (γ₁ 0) := hlt₁ ⟨by linarith [ht.1], htlt⟩
    rcases ht.1.lt_or_eq with htr | htr
    · have h₂ : L (γ₂ 0) < L (γ₂ (t + r)) := hlt₂ ⟨by linarith, by linarith⟩
      linarith
    · subst htr
      rw [neg_add_cancel]
      linarith
  · have h₂ : L (γ₂ 0) < L (γ₂ (0 + r)) := hlt₂ ⟨by linarith [hr.1], by linarith⟩
    linarith

end TauCeti
