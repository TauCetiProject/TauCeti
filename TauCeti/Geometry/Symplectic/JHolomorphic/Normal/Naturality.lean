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
# Target-coordinate covariance of the normal Cauchy–Riemann operator

The normal fiber of a parametrized curve `u` is the quotient by the actual derivative image
`range (du)`. The differential of any target map `Φ` induces the map of normal quotients
`normalFDerivMap` into the quotient by `range (d(Φ ∘ u))`.

At a pseudoholomorphic map, this quotient map intertwines the normal linearizations when
`Φ` is `C²` and intertwines the target structures near the image point. In particular, local
normal operators agree on target-coordinate overlaps. The statement applies to arbitrary
ambient lifts of normal variations, without choosing a metric complement or assuming
integrability. It does not require `u` to be immersive or `Φ` to be invertible; coordinate
changes are a special case.

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

end TauCeti
