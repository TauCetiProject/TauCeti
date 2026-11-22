/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.NormalQuotient
public import TauCeti.Geometry.Symplectic.JHolomorphic.Naturality
public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Linearization

/-!
# Coordinate covariance of the normal Cauchy–Riemann operator

The normal fiber of a parametrized curve `u` is the quotient by the actual derivative image
`range (du)`. The differential of any target map `Φ` induces the map of normal quotients
`normalFDerivMap` into the quotient by `range (d(Φ ∘ u))`.

At a pseudoholomorphic map, this quotient map intertwines the normal linearizations when
`Φ` is `C²` and intertwines the target structures near the image point. In particular, local
normal operators agree on target-coordinate overlaps. The statement applies to arbitrary
ambient lifts of normal variations, without choosing a metric complement or assuming
integrability. It does not require `u` to be immersive or `Φ` to be invertible; coordinate
changes are a special case.

On the source side, let the differential of `ψ : U' → U` at `y` intertwine the source
endomorphisms. The normal fiber of `u ∘ ψ` at `y` maps onto that of `u` at `ψ y` by
`Submodule.factor`, since `range (d(u ∘ ψ) y) ≤ range (du (ψ y))`, and this map carries the
normal linearization of `u ∘ ψ` on `ξ ∘ ψ` to the normal linearization of `u` on `ξ` composed
with `dψ y`. Only first derivatives at the point enter, and `u` need not be pseudoholomorphic.
When `dψ y` is surjective the two normal fibers are identified by `Submodule.quotEquivOfEq`, so
local normal operators also agree on overlaps of holomorphic source coordinates.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1 (linearization of the Cauchy–Riemann operator and its independence of
  coordinates at a holomorphic map).
-/

public section

noncomputable section

namespace TauCeti

open Filter
open scoped ContDiff Topology

variable {U V W : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The map of normal quotients induced by a `C²` target map intertwines the normal
Cauchy–Riemann linearizations at a zero of the nonlinear defect. The hypothesis on the
target structures is local near `u x`, as needed for coordinate overlaps. -/
theorem normalCauchyRiemannLinearization_comp_of_cauchyRiemannOperator_eq_zero
    (j : U →L[ℝ] U) (J : V → V →L[ℝ] V) (K : W → W →L[ℝ] W)
    (u ξ : U → V) (Φ : V → W) (x : U)
    (hu : DifferentiableAt ℝ u x) (hξ : DifferentiableAt ℝ ξ x)
    (hΦ : ContDiffAt ℝ 2 Φ (u x)) (hJ : DifferentiableAt ℝ J (u x))
    (hK : DifferentiableAt ℝ K (Φ (u x)))
    (hJK : ∀ᶠ y in 𝓝 (u x), (fderiv ℝ Φ y).comp (J y) =
      (K (Φ y)).comp (fderiv ℝ Φ y))
    (hhol : cauchyRiemannOperator j J u x = 0) :
    normalCauchyRiemannLinearization j K (Φ ∘ u)
        (fun y ↦ fderiv ℝ Φ (u y) (ξ y)) x =
      (normalFDerivMap ℝ u Φ x).comp (normalCauchyRiemannLinearization j J u ξ x) := by
  ext v
  simp only [LinearMap.comp_apply, normalCauchyRiemannLinearization_apply,
    Submodule.mkQ_apply, normalFDerivMap_mk]
  rw [cauchyRiemannLinearization_comp_of_cauchyRiemannOperator_eq_zero j J K u ξ Φ x
    hu hξ hΦ hJ hK hJK hhol, ContinuousLinearMap.comp_apply]

/-! ### Source maps -/

section Source

variable {U' : Type*} [NormedAddCommGroup U'] [NormedSpace ℝ U']

/-- Under a source map whose differential intertwines the source endomorphisms, the map of
normal fibers `V ⧸ range (d(u ∘ ψ) y) → V ⧸ range (du (ψ y))` carries the normal linearization
of `u ∘ ψ` on `ξ ∘ ψ` to the normal linearization of `u` on `ξ` composed with `dψ y`. -/
theorem normalCauchyRiemannLinearization_comp_right
    (j' : U' →L[ℝ] U') (j : U →L[ℝ] U) (J : V → V →L[ℝ] V) (u ξ : U → V) (ψ : U' → U)
    (y : U') (hu : DifferentiableAt ℝ u (ψ y)) (hξ : DifferentiableAt ℝ ξ (ψ y))
    (hψ : DifferentiableAt ℝ ψ y) (hj : (fderiv ℝ ψ y).comp j' = j.comp (fderiv ℝ ψ y)) :
    (Submodule.factor (range_fderiv_comp_le_range_fderiv u ψ y hu hψ)).comp
        (normalCauchyRiemannLinearization j' J (u ∘ ψ) (ξ ∘ ψ) y) =
      (normalCauchyRiemannLinearization j J u ξ (ψ y)).comp (fderiv ℝ ψ y).toLinearMap := by
  ext w
  simp only [LinearMap.comp_apply, normalCauchyRiemannLinearization_apply,
    Submodule.factor_mk, ContinuousLinearMap.coe_coe,
    cauchyRiemannLinearization_comp_right j' j J u ξ ψ y hu hξ hψ hj,
    ContinuousLinearMap.comp_apply]

/-- When the differential of the source map is moreover surjective, as for a holomorphic change
of source coordinate, the identification `V ⧸ range (d(u ∘ ψ) y) ≃ V ⧸ range (du (ψ y))` of the
normal fibers carries the normal linearization of `u ∘ ψ` on `ξ ∘ ψ` to the normal linearization
of `u` on `ξ` composed with `dψ y`. -/
theorem normalCauchyRiemannLinearization_comp_right_of_surjective
    (j' : U' →L[ℝ] U') (j : U →L[ℝ] U) (J : V → V →L[ℝ] V) (u ξ : U → V) (ψ : U' → U)
    (y : U') (hu : DifferentiableAt ℝ u (ψ y)) (hξ : DifferentiableAt ℝ ξ (ψ y))
    (hψ : DifferentiableAt ℝ ψ y) (hj : (fderiv ℝ ψ y).comp j' = j.comp (fderiv ℝ ψ y))
    (h : Function.Surjective (fderiv ℝ ψ y)) :
    (Submodule.quotEquivOfEq _ _
        (range_fderiv_comp_eq_range_fderiv u ψ y hu hψ h)).toLinearMap.comp
        (normalCauchyRiemannLinearization j' J (u ∘ ψ) (ξ ∘ ψ) y) =
      (normalCauchyRiemannLinearization j J u ξ (ψ y)).comp (fderiv ℝ ψ y).toLinearMap := by
  ext w
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, normalCauchyRiemannLinearization_apply,
    Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk, ContinuousLinearMap.coe_coe,
    cauchyRiemannLinearization_comp_right j' j J u ξ ψ y hu hξ hψ hj,
    ContinuousLinearMap.comp_apply]

end Source

end TauCeti
