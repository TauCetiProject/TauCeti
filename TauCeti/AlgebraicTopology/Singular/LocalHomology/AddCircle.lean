/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.IntegralCup
public import TauCeti.AlgebraicTopology.Singular.AddCircle
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Prod
public import TauCeti.Geometry.Manifold.Orientation.AddCircle

/-!
# The circuit class of a circle and the class of a torus are fundamental classes

For a positive period `p`, the circuit class `AddCircle.fundamentalClass p ∈ H₁(ℝ / pℤ; ℤ)`, the
class of the loop `t ↦ [t p]`, is an integral fundamental class of the circle in the sense of
`TauCeti.IsFundamentalClass` (`AddCircle.isFundamentalClass_fundamentalClass`). Indeed the circle
is a compact oriented manifold, so it has an integral fundamental class, and every class of
`H₁(ℝ / pℤ; ℤ)` is an integer multiple of the circuit class
(`AddCircle.eq_firstHomologyAddEquiv_zsmul_fundamentalClass`); a class with a fundamental multiple
is itself fundamental.

The cross product of fundamental classes of compact connected manifolds is a fundamental class of
their product (`TauCeti.IsFundamentalClass.singularHomologyCross`), so for positive periods `p`
and `q` the class `[ℝ / pℤ] × [ℝ / qℤ]` of the parameter torus
(`TauCeti.addCircleProdFundamentalClass`) is a fundamental class of the torus
(`TauCeti.isFundamentalClass_addCircleProdFundamentalClass`).

The integral fundamental class of an oriented manifold,
`TauCeti.HomologicalOrientation.fundamentalClass`, has coefficients in `ULift ℤ`; it is carried
to the coefficients `ℤ` of `TauCeti.singularChains ℤ` along `TauCeti.integralCoeffIso`, which
preserves fundamental classes (`TauCeti.isFundamentalClass_singularHomologyFunctor_map_app_iff`).

## Main results

* `AddCircle.isFundamentalClass_fundamentalClass`: the circuit class of a circle of positive
  period is a fundamental class.
* `TauCeti.isFundamentalClass_addCircleProdFundamentalClass`: the class of the parameter torus of
  two positive periods is a fundamental class.
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory Module AlgebraicTopology

namespace AddCircle

open TauCeti

variable (p : ℝ) [Fact (0 < p)]

/-- **The circuit class of a circle is a fundamental class.** For a positive period `p`, the
class of the loop `t ↦ [t p]` is an integral fundamental class of `ℝ / pℤ`. -/
theorem isFundamentalClass_fundamentalClass :
    IsFundamentalClass (M := AddCircle p) (N := ModuleCat.of ℤ ℤ) (fundamentalClass p) := by
  have h1 : finrank ℝ ℝ = 0 + 1 := by simp
  -- The fundamental class of the oriented circle, with coefficients carried from `ULift ℤ` to `ℤ`.
  set ν := ((singularHomologyFunctor (ModuleCat.{0} ℤ) 1).map integralCoeffIso.hom).app
    (TopCat.of (AddCircle p))
    ((((AddCircle.orientation p).toHomologicalOrientation h1).fundamentalClass h1))
  have hν : IsFundamentalClass ν :=
    (isFundamentalClass_singularHomologyFunctor_map_app_iff integralCoeffIso _).2
      (HomologicalOrientation.isFundamentalClass_fundamentalClass _ h1)
  -- `ν` is an integer multiple of the circuit class.
  rw [eq_firstHomologyAddEquiv_zsmul_fundamentalClass p ν, ← Int.cast_smul_eq_zsmul ℤ, Int.cast_id]
    at hν
  exact IsFundamentalClass.of_smul hν

end AddCircle

namespace TauCeti

variable (p q : ℝ) [Fact (0 < p)] [Fact (0 < q)]

/-- **The class of a torus is a fundamental class.** For positive periods `p` and `q`, the cross
product `[ℝ / pℤ] × [ℝ / qℤ]` of the circuit classes is an integral fundamental class of the torus
`ℝ / pℤ × ℝ / qℤ`. -/
theorem isFundamentalClass_addCircleProdFundamentalClass :
    IsFundamentalClass (M := AddCircle p × AddCircle q) (N := ModuleCat.of ℤ ℤ)
      (addCircleProdFundamentalClass p q) := by
  -- The class is the cross product followed by the coefficient identification `ℤ ⊗ ℤ ≅ ℤ`.
  have h := (isFundamentalClass_singularHomologyFunctor_map_app_iff (λ_ (𝟙_ _)) _).2
    (IsFundamentalClass.singularHomologyCross (E := ℝ) (F := ℝ) (LinearEquiv.refl ℤ ℤ)
      (LinearEquiv.refl ℤ ℤ) (by simp) (by simp)
      (AddCircle.isFundamentalClass_fundamentalClass p)
      (AddCircle.isFundamentalClass_fundamentalClass q))
  rw [addCircleProdFundamentalClass_def, TopCat.singularHomologyCrossBilinear_apply ℤ _ _ 1 1 2 rfl]
  exact h

end TauCeti
