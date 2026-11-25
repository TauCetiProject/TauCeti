/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.MinimalGraph.Equation.Scaling
public import TauCeti.Geometry.Euclidean.PolarGraph.AngleBranch

/-!
# The minimal graph equation for helicoid height branches

Every real multiple of the logarithmic angle branch satisfies the minimal graph equation
throughout its rotated slit domain, including at the projection of its chosen polar point.
-/

public noncomputable section

namespace TauCeti.PolarGraph

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- Every pitched logarithmic angle branch solves the native minimal graph equation on its
slit domain. The pitch may vanish. -/
theorem nondivergenceOperator_const_mul_angleBranch (c : ℝ) (p : PolarPoint) (x : Plane)
    (hx : Complex.orthonormalBasisOneI.repr.symm x / projection p ∈ Complex.slitPlane) :
    MinimalGraph.nondivergenceOperator
      (fun x : EuclideanSpace ℝ (Fin 2) ↦ c * angleBranch p x)
      x = 0 := by
  have hsmul : (fun y : Plane ↦ c * angleBranch p y) = c • angleBranch p :=
    funext fun _ ↦ (smul_eq_mul ..).symm
  rw [hsmul, MinimalGraph.nondivergenceOperator_const_smul (angleBranch p) c x,
    laplacian_angleBranch p x hx,
    fderiv_fderiv_angleBranch_gradient_gradient_eq_zero p x hx]
  ring

/-- At the projection of every polar point, every real multiple of the centered branch
satisfies the minimal graph equation. -/
theorem nondivergenceOperator_const_mul_angleBranch_repr_projection (c : ℝ) (p : PolarPoint) :
    MinimalGraph.nondivergenceOperator (fun x : Plane ↦ c * angleBranch p x)
      (Complex.orthonormalBasisOneI.repr (projection p)) = 0 := by
  apply nondivergenceOperator_const_mul_angleBranch
  simp [projection_ne_zero]

end TauCeti.PolarGraph
