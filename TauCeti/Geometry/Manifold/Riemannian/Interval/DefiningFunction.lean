/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.DefiningFunction.Examples
public import TauCeti.Geometry.Manifold.Riemannian.Boundary.SecondFundamentalForm.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Interval.Basic
public import TauCeti.Geometry.Manifold.Riemannian.InwardUnitNormal

/-!
# The boundary of a closed interval as a Riemannian hypersurface

On the closed interval `[a, b]`, `a < b`, with its Euclidean metric
(`TauCeti.iccEuclideanMetric`), the dimension-one Checks of the boundary geometry hold:

* the boundary defining function `ρ = (x - a) (b - x)` (`TauCeti.intervalDefiningFunction`) has
  `|dρ_x| = |a + b - 2x|` (`TauCeti.norm_mvfderiv_intervalDefiningFunction`), hence `|dρ| = b - a`
  at both endpoints (`TauCeti.norm_mvfderiv_intervalDefiningFunction_boundary`); for `[0, 1]`
  and `ρ = x (1 - x)` this is `|dρ| = 1` at both ends;
* the gradient formula `grad ρ = |dρ| ν_in` reads `grad ρ = (b - a) ν_in` on the boundary
  (`TauCeti.mgradient_intervalDefiningFunction_boundary`), with `ν_in = +1` at `a` and `ν_in = -1`
  at `b` (`TauCeti.inwardUnitNormal_Icc_bot`, `TauCeti.inwardUnitNormal_Icc_top`);
* the tangent space of the boundary is zero, so the second fundamental form is the zero form
  (`TauCeti.boundarySecondFundamentalForm_Icc`), as for every manifold of dimension one
  (`TauCeti.boundarySecondFundamentalForm_eq_zero_of_eq_zero`).

Every tangent vector of `[a, b]` is a multiple of the unit tangent vector `1`
(`TauCeti.eq_mvfderiv_subtypeVal_smul_one_Icc`), so the norm of a differential is the absolute
value of its value on `1` (`TauCeti.norm_mvfderiv_Icc`).
-/

public section

open Bundle Set
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti

open Fact.Manifold
open scoped IccZeroAddOne

/-- In dimension one (`n = 0`) the second fundamental form of the boundary is the zero form: the
tangent space of the boundary is zero. -/
theorem boundarySecondFundamentalForm_eq_zero_of_eq_zero {n : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) 2 M] [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
    [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 1 (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
    (hn : n = 0) (q : (𝓡∂ (n + 1)).boundary M) : boundarySecondFundamentalForm q = 0 := by
  subst hn
  ext u w
  rw [Subsingleton.elim (α := EuclideanSpace ℝ (Fin 0)) w 0]
  exact map_zero (boundarySecondFundamentalForm q u)

variable {a b : ℝ} [Fact (a < b)]

/-- Every tangent vector `v` of `[a, b]` is the multiple `v = ι'(v) • 1` of the unit tangent
vector, where `ι'` is the differential of the inclusion into `ℝ`. -/
theorem eq_mvfderiv_subtypeVal_smul_one_Icc (x : Icc a b) (v : TangentSpace (𝓡∂ (0 + 1)) x) :
    v = mvfderiv (𝓡∂ (0 + 1)) (Subtype.val : Icc a b → ℝ) x v •
      (1 : TangentSpace (𝓡∂ (0 + 1)) x) := by
  apply injective_mvfderiv_subtypeVal_Icc x
  -- The models `𝓡∂ 1` and `𝓡∂ (0 + 1)` and their interval charts agree by definition.
  change mvfderiv (𝓡∂ (0 + 1)) (Subtype.val : Icc a b → ℝ) x v =
    mvfderiv (𝓡∂ (0 + 1)) (Subtype.val : Icc a b → ℝ) x
      (mvfderiv (𝓡∂ (0 + 1)) (Subtype.val : Icc a b → ℝ) x v •
        (1 : TangentSpace (𝓡∂ (0 + 1)) x))
  rw [map_smul, IccZeroAddOne.mvfderiv_subtypeVal_one, smul_eq_mul, mul_one]

/-- For the Euclidean metric of `[a, b]`, the differential of a function at `x` has norm the
absolute value of its value on the unit tangent vector `1`. -/
theorem norm_mvfderiv_Icc (f : Icc a b → ℝ) (x : Icc a b) :
    ‖mvfderiv (𝓡∂ (0 + 1)) f x‖ =
      |mvfderiv (𝓡∂ (0 + 1)) f x (1 : TangentSpace (𝓡∂ (0 + 1)) x)| := by
  refine le_antisymm (ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg _) fun v ↦ ?_) ?_
  · conv_lhs => rw [eq_mvfderiv_subtypeVal_smul_one_Icc x v]
    rw [map_smul, smul_eq_mul, norm_mul, IccZeroAddOne.norm_tangentSpace, Real.norm_eq_abs,
      Real.norm_eq_abs, mul_comm]
  · have h := (mvfderiv (𝓡∂ (0 + 1)) f x).le_opNorm (1 : TangentSpace (𝓡∂ (0 + 1)) x)
    rwa [IccZeroAddOne.norm_one_tangentSpace, mul_one, Real.norm_eq_abs] at h

/-- The differential of `ρ = (x - a) (b - x)` on `[a, b]` has norm `|a + b - 2x|` for the
Euclidean metric. -/
theorem norm_mvfderiv_intervalDefiningFunction (x : Icc a b) :
    ‖mvfderiv (𝓡∂ (0 + 1)) (intervalDefiningFunction a b) x‖ = |a + b - 2 * (x : ℝ)| := by
  rw [norm_mvfderiv_Icc]
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
theorem inwardUnitNormal_Icc_bot :
    inwardUnitNormal (⟨⊥, Icc_isBoundaryPoint_bot⟩ : (𝓡∂ (0 + 1)).boundary (Icc a b)) =
      (1 : TangentSpace (𝓡∂ (0 + 1)) (⊥ : Icc a b)) := by
  rw [inwardUnitNormal_def, outwardUnitNormal_Icc_bot, neg_neg]

/-- The inward unit normal of `[a, b]` at the right endpoint is `-1`, minus the image of
`1 ∈ ℝ`. -/
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

/-- The second fundamental form of the boundary of `[a, b]` is the zero form on the zero tangent
space of the boundary. -/
theorem boundarySecondFundamentalForm_Icc (q : (𝓡∂ (0 + 1)).boundary (Icc a b)) :
    boundarySecondFundamentalForm q = 0 :=
  boundarySecondFundamentalForm_eq_zero_of_eq_zero rfl q

end TauCeti
