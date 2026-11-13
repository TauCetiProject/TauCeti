/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Circle
public import TauCeti.Analysis.InnerProductSpace.PlaneRotation
public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.Degree.SphereRotation

/-!
# The rotation family of a sphere as a family of diffeomorphisms

Let `Sⁿ` be the unit sphere of a real inner product space `E` and fix `p ∈ Sⁿ`. The unit tangent
vectors of `Sⁿ` at `p` are the unit vectors `v` of the hyperplane `p^⊥`. For such a `v` and a point
`z` of the unit circle of `ℂ`, the **rotation** `TauCeti.sphereRotation p (v, z)` of `E` rotates
the plane spanned by `p` and `v` by the angle of `z`, from `p` towards `v`, and fixes the orthogonal
complement of that plane. It is the rotation `LinearIsometry.planeRotation` of the plane cut out by
the isometric embedding `w ↦ Re w • p + Im w • v` of `ℂ` (`TauCeti.sphereRotationPlane`).

The rotation depends continuously on `(v, z)` for the operator norm, so restricting it to the sphere
gives a continuous family of diffeomorphisms `T¹_pSⁿ × S¹ → Diff(Sⁿ)` for the weak Whitney
topology (`TauCeti.sphereRotationDiffeomorph`). Its evaluation at `p` is the rotation family
`TauCeti.sphereRotationFamily p`, `(v, z) ↦ Re z • p + Im z • v`
(`TauCeti.evalAt_comp_sphereRotationDiffeomorph`), whose degree is `1 + (-1)ⁿ⁻¹`, so `2` in odd
dimensions. This is the family of rotations of the direct proof that odd spheres are covered by
diffeomorphisms (Barraud–Damian–Humilière–Oancea, Proposition 6.34).

## Main definitions

* `TauCeti.sphereRotationPlane p v`: the isometric embedding `w ↦ Re w • p + Im w • v` of `ℂ`.
* `TauCeti.sphereRotation p x`: the rotation of `E` by the angle of `x.2` in the plane of `p` and
  `x.1`.
* `TauCeti.sphereRotationDiffeomorph p m`: the continuous family `T¹_pSⁿ × S¹ → Diff(Sⁿ)` of these
  rotations.

## Main results

* `TauCeti.sphereRotation_apply_self`: the rotation sends `p` to the rotation family at `p`.
* `TauCeti.continuous_sphereRotation`: the rotation depends continuously on `(v, z)`.
* `TauCeti.evalAt_comp_sphereRotationDiffeomorph`: the evaluation of the family of
  diffeomorphisms at `p` is the rotation family at `p`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3, Proposition 6.34.
-/

public section

noncomputable section

open Metric Module
open scoped Manifold ContDiff RealInnerProductSpace TauCeti.DiffeomorphWeakWhitney

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The rotations -/

/-- The isometric embedding `w ↦ Re w • p + Im w • v` of `ℂ` into `E` cut out by a point `p` of
the unit sphere and a unit vector `v` of `p^⊥`. Its image is the plane in which `p` is rotated
towards `v`. -/
def sphereRotationPlane (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    ℂ →ₗᵢ[ℝ] E where
  toLinearMap := (Complex.reCLM.smulRight (p : E) +
    Complex.imCLM.smulRight ((v : (ℝ ∙ (p : E))ᗮ) : E)).toLinearMap
  norm_map' w := by
    -- `p` and `v` are orthonormal, and `Re w ^ 2 + Im w ^ 2 = ‖w‖ ^ 2`.
    have hp : ‖(p : E)‖ = 1 := norm_eq_of_mem_sphere p
    have hv : ‖((v : (ℝ ∙ (p : E))ᗮ) : E)‖ = 1 := norm_eq_of_mem_sphere v
    have hpv : ⟪(p : E), ((v : (ℝ ∙ (p : E))ᗮ) : E)⟫ = 0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.1 (v : (ℝ ∙ (p : E))ᗮ).2
    refine (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
    change ‖w.re • (p : E) + w.im • ((v : (ℝ ∙ (p : E))ᗮ) : E)‖ ^ 2 = ‖w‖ ^ 2
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, hpv,
      hp, hv, Complex.sq_norm, Complex.normSq_apply, Real.norm_eq_abs, Real.norm_eq_abs]
    ring_nf
    rw [sq_abs, sq_abs]

@[simp]
theorem sphereRotationPlane_apply (p : sphere (0 : E) 1) (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1)
    (w : ℂ) : sphereRotationPlane p v w = w.re • (p : E) + w.im • ((v : (ℝ ∙ (p : E))ᗮ) : E) :=
  (rfl)

/-- The **rotation** at a point `p` of the unit sphere, in the direction of a unit vector `v` of
`p^⊥` and by the angle of a point `z` of the unit circle: the linear isometry of `E` rotating the
plane spanned by `p` and `v` by the angle of `z`, from `p` towards `v`, and fixing the orthogonal
complement of that plane. -/
def sphereRotation (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) : E ≃ₗᵢ[ℝ] E :=
  (sphereRotationPlane p x.1).planeRotation (Circle.homeomorphSphere.symm x.2)

theorem sphereRotation_def (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    sphereRotation p x =
      (sphereRotationPlane p x.1).planeRotation (Circle.homeomorphSphere.symm x.2) :=
  (rfl)

/-- The rotation at `p` sends `p` to the rotation family at `p`: rotating `p` towards `v` by the
angle of `z` gives `Re z • p + Im z • v`. -/
@[simp]
theorem sphereRotation_apply_self (p : sphere (0 : E) 1)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    sphereRotation p x p = sphereRotationFamily p x := by
  have h := (sphereRotationPlane p x.1).planeRotation_apply_map (Circle.homeomorphSphere.symm x.2) 1
  simp only [sphereRotationPlane_apply, Complex.one_re, Complex.one_im, one_smul, zero_smul,
    add_zero, mul_one, Circle.coe_homeomorphSphere_symm_apply] at h
  rw [sphereRotation_def, h, coe_sphereRotationFamily]

/-- The rotation at `p` depends continuously on the direction and the angle, for the operator
norm. -/
theorem continuous_sphereRotation (p : sphere (0 : E) 1) :
    Continuous fun x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1 ↦
      ((sphereRotation p x).toContinuousLinearEquiv : E →L[ℝ] E) := by
  refine Continuous.planeRotation ?_ (Circle.homeomorphSphere.symm.continuous.comp continuous_snd)
  have h (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) : (sphereRotationPlane p v).toContinuousLinearMap =
      Complex.reCLM.smulRight (p : E) + Complex.imCLM.smulRight ((v : (ℝ ∙ (p : E))ᗮ) : E) :=
    (rfl)
  simp only [h]
  fun_prop

/-! ### The family of diffeomorphisms -/

-- The finite dimension makes the sphere compact, which the weak Whitney topology on its
-- diffeomorphisms requires.
variable [FiniteDimensional ℝ E] {n : ℕ} [Fact (finrank ℝ E = n + 1)]

/-- The **rotation family of diffeomorphisms** at a point `p` of the unit sphere `Sⁿ`: the
continuous family `T¹_pSⁿ × S¹ → Diff(Sⁿ)`, for the weak Whitney `C^m` topology, sending a unit
tangent vector `v` at `p` and a point `z` of the unit circle to the rotation of the sphere by the
angle of `z` in the plane of `p` and `v`. -/
def sphereRotationDiffeomorph (p : sphere (0 : E) 1) (m : ℕ∞ω) :
    C(sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1,
      sphere (0 : E) 1 ≃ₘ^m⟮𝓡 n, 𝓡 n⟯ sphere (0 : E) 1) where
  toFun x := LinearIsometryEquiv.unitSphereDiffeomorph (sphereRotation p x) m
  continuous_toFun :=
    Diffeomorph.continuous_weakWhitney_iff.2
      (continuous_sphereRotation p).toContMDiffMap_unitSphereDiffeomorph

@[simp]
theorem sphereRotationDiffeomorph_apply (p : sphere (0 : E) 1) (m : ℕ∞ω)
    (x : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 × sphere (0 : ℂ) 1) :
    sphereRotationDiffeomorph (n := n) p m x =
      LinearIsometryEquiv.unitSphereDiffeomorph (sphereRotation p x) m :=
  (rfl)

/-- **The evaluation of the rotation family of diffeomorphisms at `p`** is the rotation family
`TauCeti.sphereRotationFamily p`. -/
@[simp]
theorem evalAt_comp_sphereRotationDiffeomorph (p : sphere (0 : E) 1) (m : ℕ∞ω) :
    (Diffeomorph.evalAt p).comp (sphereRotationDiffeomorph (n := n) p m) =
      ⟨sphereRotationFamily p, continuous_sphereRotationFamily p⟩ := by
  refine ContinuousMap.ext fun x ↦ Subtype.ext ?_
  simp [Diffeomorph.evalAt_apply, LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply]

end TauCeti
