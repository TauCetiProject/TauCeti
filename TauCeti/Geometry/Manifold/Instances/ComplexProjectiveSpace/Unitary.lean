/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Sphere
public import TauCeti.Geometry.Manifold.Instances.ComplexProjectiveSpace.Symplectic
public import TauCeti.Topology.ComplexProjectiveSpace.Homogeneous
import TauCeti.Geometry.Diffeomorphism.Sphere
import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# Unitary symmetries of the Fubini–Study form

A unitary matrix `A ∈ U(n + 1)` acts on complex projective space `CPⁿ` by `A • [x] = [A x]`
(`TauCeti.ComplexProjectiveSpace.smul_mk`). This file shows that it acts by symplectomorphisms of
the Fubini–Study form `ω_FS` (`TauCeti.ComplexProjectiveSpace.fubiniStudyForm`).

* **Smoothness.** The action of `A` on the unit sphere `S²ⁿ⁺¹ ⊂ ℂⁿ⁺¹` is the restriction of a
  linear isometry, hence smooth, and the Hopf projection `mk : S²ⁿ⁺¹ → CPⁿ` is a surjective
  submersion intertwining the two actions. So `x ↦ A • x` is smooth on `CPⁿ`
  (`TauCeti.ComplexProjectiveSpace.instContMDiffConstSMulUnitaryGroup`).
* **Invariance of `ω_FS`.** The form `ω_FS` is determined by its pullback `π⁻¹ Im ⟪·, ·⟫_ℂ` to
  the sphere (`TauCeti.ComplexProjectiveSpace.eq_fubiniStudyForm_iff`), and a unitary map
  preserves `Im ⟪·, ·⟫_ℂ`. Hence `A^* ω_FS = ω_FS`
  (`TauCeti.ComplexProjectiveSpace.mpullback_smul_fubiniStudyForm`).
* **Areas of sphere classes.** By the naturality of the integral over spheres, the Fubini–Study
  area of a class of `π₂(CPⁿ, x)` equals that of its image under `A` in `π₂(CPⁿ, A • x)`
  (`TauCeti.ComplexProjectiveSpace.sphereIntegral_fubiniStudyForm_map_smul`). Since `U(n + 1)`
  acts transitively on `CPⁿ`, this compares the areas of sphere classes at any two base points.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 23 (symplectic reduction, with `CPⁿ` as the reduction of `ℂⁿ⁺¹` by the
  diagonal circle).
-/

public section

noncomputable section

open Matrix Metric
open scoped ContDiff Manifold Topology

namespace TauCeti.ComplexProjectiveSpace

variable {n : ℕ} (A : unitaryGroup (Fin (n + 1)) ℂ)

/-- **Unitary matrices act smoothly on `CPⁿ`**: for every unitary `A ∈ U(n + 1)`, the map
`x ↦ A • x` of `CPⁿ` is smooth of every order. -/
instance instContMDiffConstSMulUnitaryGroup {r : ℕ∞ω} :
    ContMDiffConstSMul 𝓘(ℝ, Fin n → ℂ) r (unitaryGroup (Fin (n + 1)) ℂ)
      (ComplexProjectiveSpace n) :=
  ⟨fun A ↦ ((isSubmersion_mk r).contMDiff_comp_iff (mk_surjective n) le_rfl).1 <|
    ((contMDiff_mk r).comp (contMDiff_const_smul (UnitaryGroup.toLinearIsometryEquiv A))).congr
      fun x ↦ smul_mk A x⟩

/-- **Unitary matrices are symplectomorphisms of `CPⁿ`**: the pullback of the Fubini–Study form
along `x ↦ A • x` is the Fubini–Study form. -/
@[simp]
theorem mpullback_smul_fubiniStudyForm :
    SmoothForm.mpullback (A • ·) (contMDiff_const_smul A) (fubiniStudyForm n) =
      fubiniStudyForm n := by
  set g := UnitaryGroup.toLinearIsometryEquiv A
  -- `A` lifts along `mk` to the restriction of `g` to the sphere, and `g` preserves
  -- `Im ⟪·, ·⟫_ℂ`.
  rw [eq_fubiniStudyForm_iff, SmoothForm.mpullback_mpullback_of_comp_eq (contMDiff_mk ∞) _
      (contMDiff_const_smul g) (contMDiff_mk ∞) (funext fun x ↦ smul_mk A x),
    mpullback_mk_fubiniStudyForm, SmoothForm.mpullback_smul,
    mpullback_mpullback_coe_sphere_of_im_inner_map_map _
      ((g.toContinuousLinearEquiv : EuclideanSpace ℂ (Fin (n + 1)) →L[ℂ] _).restrictScalars ℝ)
      (fun u w ↦ by simp) (LinearIsometryEquiv.coe_smul_unitSphere g)]

/-- **Unitary matrices preserve the Fubini–Study areas of sphere classes.** The image under
`x ↦ A • x` of a class of `π₂(CPⁿ, x)`, a class of `π₂(CPⁿ, y)` for `y = A • x`, has the same
Fubini–Study area as the class itself. -/
@[simp]
theorem sphereIntegral_fubiniStudyForm_map_smul {x y : ComplexProjectiveSpace n} (h : A • x = y)
    (a : π_ 2 (ComplexProjectiveSpace n) x) :
    sphereIntegral (fubiniStudyForm n).val y
        (HomotopyGroup.map ⟨(A • ·), continuous_const_smul A⟩ h a) =
      sphereIntegral (fubiniStudyForm n).val x a := by
  subst h
  have key := sphereIntegral_mpullback (contMDiff_const_smul A)
    (isSmoothForm_fubiniStudyForm n) (mextDeriv_fubiniStudyForm n) a
  rw [← SmoothForm.coe_mpullback (hf := contMDiff_const_smul A),
    mpullback_smul_fubiniStudyForm] at key
  exact key.symm

end TauCeti.ComplexProjectiveSpace
