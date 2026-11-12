/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Naturality
public import TauCeti.Geometry.Symplectic.JHolomorphic.Normal.Linearization
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Target-coordinate covariance of the normal Cauchy–Riemann operator

The normal fiber of a parametrized curve `u` is the quotient by the actual derivative image
`range (du)`. The differential of any target map `Φ` carries this image into
`range (d(Φ ∘ u))`, so it induces the map of normal quotients `normalFDerivMap`, built with
`Submodule.mapQ`.

At a pseudoholomorphic map, this quotient map intertwines the normal linearizations when
`Φ` is `C²` and intertwines the target structures near the image point. In particular, local
normal operators agree on target-coordinate overlaps. The statement applies to arbitrary
ambient lifts of normal variations, without choosing a metric complement or assuming
integrability. It does not require `u` to be immersive or `Φ` to be invertible; coordinate
changes are a special case.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 3.1 (the normal Cauchy–Riemann operator).
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

/-- The differential of any target map carries the derivative image of `u` into that of
`Φ ∘ u`. No differentiability is needed: otherwise one of the derivatives is zero. -/
theorem range_fderiv_le_comap_range_fderiv_comp (u : U → V) (Φ : V → W) (x : U) :
    (fderiv ℝ u x).toLinearMap.range ≤
      (fderiv ℝ (Φ ∘ u) x).toLinearMap.range.comap (fderiv ℝ Φ (u x)).toLinearMap := by
  by_cases hΦ : DifferentiableAt ℝ Φ (u x)
  · by_cases hu : DifferentiableAt ℝ u x
    · rintro _ ⟨a, rfl⟩
      exact ⟨a, by simp [fderiv_comp x hΦ hu]⟩
    · simp [fderiv_zero_of_not_differentiableAt hu]
  · simp [fderiv_zero_of_not_differentiableAt hΦ]

/-- The map of normal quotients `V ⧸ range (du x) → W ⧸ range (d(Φ ∘ u) x)` induced by the
differential of a target map `Φ`. -/
def normalFDerivMap (u : U → V) (Φ : V → W) (x : U) :
    (V ⧸ (fderiv ℝ u x).toLinearMap.range) →ₗ[ℝ]
      W ⧸ (fderiv ℝ (Φ ∘ u) x).toLinearMap.range :=
  (fderiv ℝ u x).toLinearMap.range.mapQ _ (fderiv ℝ Φ (u x)).toLinearMap
    (range_fderiv_le_comap_range_fderiv_comp u Φ x)

/-- The induced normal map sends the class of `w` to the class of `dΦ (u x) w`. -/
@[simp]
theorem normalFDerivMap_mk (u : U → V) (Φ : V → W) (x : U) (w : V) :
    normalFDerivMap u Φ x (Submodule.Quotient.mk w) =
      Submodule.Quotient.mk (fderiv ℝ Φ (u x) w) := (rfl)

/-- The identity target map induces the identity on the normal quotient. -/
@[simp]
theorem normalFDerivMap_id (u : U → V) (x : U) :
    normalFDerivMap u id x = LinearMap.id := by
  ext w
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, normalFDerivMap_mk, fderiv_id,
    ContinuousLinearMap.id_apply, LinearMap.id_apply]

/-- Normal quotient maps respect composition of target maps differentiable at the image
points, without requiring differentiability of the curve. -/
theorem normalFDerivMap_comp {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (u : U → V) (Φ : V → W) (Ψ : W → Z) (x : U)
    (hΨ : DifferentiableAt ℝ Ψ (Φ (u x))) (hΦ : DifferentiableAt ℝ Φ (u x)) :
    normalFDerivMap u (Ψ ∘ Φ) x =
      (normalFDerivMap (Φ ∘ u) Ψ x).comp (normalFDerivMap u Φ x) := by
  ext w
  simp [normalFDerivMap_mk, fderiv_comp (u x) hΨ hΦ]

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
      (normalFDerivMap u Φ x).comp (normalCauchyRiemannLinearization j J u ξ x) := by
  ext v
  simp only [LinearMap.comp_apply, normalCauchyRiemannLinearization_apply,
    Submodule.mkQ_apply, normalFDerivMap_mk]
  rw [cauchyRiemannLinearization_comp_of_cauchyRiemannOperator_eq_zero j J K u ξ Φ x
    hu hξ hΦ hJ hK hJK hhol, ContinuousLinearMap.comp_apply]

end TauCeti
