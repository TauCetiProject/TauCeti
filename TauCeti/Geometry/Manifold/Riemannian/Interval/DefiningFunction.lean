/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.DefiningFunction.Examples
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Interval.Basic
public import TauCeti.Geometry.Manifold.Riemannian.InwardUnitNormal

/-!
# The boundary defining function of a closed interval

On the closed interval `[a, b]`, `a < b`, with its Euclidean metric
(`TauCeti.iccEuclideanMetric`), the dimension-one Checks of the boundary geometry hold:

* the boundary defining function `ρ = (x - a) (b - x)` (`TauCeti.intervalDefiningFunction`) has
  `|dρ_x| = |a + b - 2x|` (`TauCeti.norm_mvfderiv_intervalDefiningFunction`), hence `|dρ| = b - a`
  at both endpoints (`TauCeti.norm_mvfderiv_intervalDefiningFunction_boundary`); for `[0, 1]`
  and `ρ = x (1 - x)` this is `|dρ| = 1` at both ends;
* the gradient formula `grad ρ = |dρ| ν_in` reads `grad ρ = (b - a) ν_in` on the boundary
  (`TauCeti.mgradient_intervalDefiningFunction_boundary`), with `ν_in = +1` at `a` and `ν_in = -1`
  at `b` (`TauCeti.inwardUnitNormal_Icc_bot`, `TauCeti.inwardUnitNormal_Icc_top`).
-/

public section

open Bundle Set
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

open Fact.Manifold
open scoped IccZeroAddOne

variable {a b : ℝ} [Fact (a < b)]

/-- The differential of `ρ = (x - a) (b - x)` on `[a, b]` has norm `|a + b - 2x|` for the
Euclidean metric. -/
theorem norm_mvfderiv_intervalDefiningFunction (x : Icc a b) :
    ‖mvfderiv (𝓡∂ (0 + 1)) (intervalDefiningFunction a b) x‖ = |a + b - 2 * (x : ℝ)| := by
  rw [IccZeroAddOne.norm_mvfderiv]
  -- The unit vector `1` of `IccZeroAddOne.instOneTangentSpace` is that of `𝓡∂ 1` by definition, so
  -- this is the value of `dρ` on `1` computed for the charts `𝓡∂ (0 + 1)`.
  exact congrArg abs (mvfderiv_intervalDefiningFunction_one x)

/-- At both endpoints of `[a, b]`, the differential of `ρ = (x - a) (b - x)` has norm
`|dρ| = b - a`; for `ρ = x (1 - x)` on `[0, 1]` this is `|dρ| = 1`. -/
theorem norm_mvfderiv_intervalDefiningFunction_boundary
    (q : (𝓡∂ (0 + 1)).boundary (Icc a b)) :
    ‖mvfderiv (𝓡∂ (0 + 1)) (intervalDefiningFunction a b) (q : Icc a b)‖ = b - a := by
  have hab : a < b := Fact.out
  rw [norm_mvfderiv_intervalDefiningFunction]
  rcases (Icc_isBoundaryPoint_iff (q : Icc a b)).1 q.property with h | h <;> rw [h]
  · rw [show a + b - 2 * a = b - a by ring, abs_of_pos (sub_pos.2 hab)]
  · rw [show a + b - 2 * b = -(b - a) by ring, abs_neg, abs_of_pos (sub_pos.2 hab)]

/-- The inward unit normal of `[a, b]` at the left endpoint is `+1`, the image of `1 ∈ ℝ`. -/
@[simp]
theorem inwardUnitNormal_Icc_bot :
    inwardUnitNormal (⟨⊥, Icc_isBoundaryPoint_bot⟩ : (𝓡∂ (0 + 1)).boundary (Icc a b)) =
      (1 : TangentSpace (𝓡∂ (0 + 1)) (⊥ : Icc a b)) := by
  rw [inwardUnitNormal_def, outwardUnitNormal_Icc_bot, neg_neg]

/-- The inward unit normal of `[a, b]` at the right endpoint is `-1`, minus the image of
`1 ∈ ℝ`. -/
@[simp]
theorem inwardUnitNormal_Icc_top :
    inwardUnitNormal (⟨⊤, Icc_isBoundaryPoint_top⟩ : (𝓡∂ (0 + 1)).boundary (Icc a b)) =
      -(1 : TangentSpace (𝓡∂ (0 + 1)) (⊤ : Icc a b)) := by
  rw [inwardUnitNormal_def, outwardUnitNormal_Icc_top]

/-- On the boundary of `[a, b]`, `ρ = (x - a) (b - x)` has gradient `grad ρ = (b - a) ν_in`, the
gradient formula `grad ρ = |dρ| ν_in` for boundary defining functions. -/
theorem mgradient_intervalDefiningFunction_boundary (q : (𝓡∂ (0 + 1)).boundary (Icc a b)) :
    Manifold.mgradient (𝓡∂ (0 + 1)) (intervalDefiningFunction a b) (q : Icc a b) =
      (b - a) • inwardUnitNormal q := by
  rw [isBoundaryDefiningFunctionOn_interval.mgradient_eq_norm_smul_inwardUnitNormal
    (mem_univ _), norm_mvfderiv_intervalDefiningFunction_boundary]

/-- At the left endpoint of `[a, b]`, `ρ = (x - a) (b - x)` has gradient `(b - a) • 1`. -/
theorem mgradient_intervalDefiningFunction_bot :
    Manifold.mgradient (𝓡∂ (0 + 1)) (intervalDefiningFunction a b) (⊥ : Icc a b) =
      (b - a) • (1 : TangentSpace (𝓡∂ (0 + 1)) (⊥ : Icc a b)) := by
  rw [← inwardUnitNormal_Icc_bot]
  exact mgradient_intervalDefiningFunction_boundary ⟨⊥, Icc_isBoundaryPoint_bot⟩

/-- At the right endpoint of `[a, b]`, `ρ = (x - a) (b - x)` has gradient `-(b - a) • 1`. -/
theorem mgradient_intervalDefiningFunction_top :
    Manifold.mgradient (𝓡∂ (0 + 1)) (intervalDefiningFunction a b) (⊤ : Icc a b) =
      -((b - a) • (1 : TangentSpace (𝓡∂ (0 + 1)) (⊤ : Icc a b))) := by
  rw [← smul_neg, ← inwardUnitNormal_Icc_top]
  exact mgradient_intervalDefiningFunction_boundary ⟨⊤, Icc_isBoundaryPoint_top⟩

end TauCeti
