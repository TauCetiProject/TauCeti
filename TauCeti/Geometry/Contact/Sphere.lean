/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Contact.Reeb
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Symplectic.Liouville.ContactType
public import TauCeti.Geometry.Symplectic.Liouville.Linear
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

/-!
# The contact form of the unit sphere of a symplectic vector space

Let `ω` be a linear symplectic form on a finite-dimensional real vector space `V`, regarded as the
constant symplectic form `TauCeti.SymplecticForm.constSmooth ω` on `V`. Its **radial primitive**
(`TauCeti.SymplecticForm.radialPrimitive`) is the one-form

`λₓ(v) = ω(x, v) / 2`,

with `dλ = ω` (`TauCeti.SymplecticForm.mextDeriv_radialPrimitive`). Its Liouville field is half
the position field, `ι_Z ω = λ` for `Z(x) = x / 2`
(`TauCeti.SymplecticForm.constSmooth_interior_two_inv_smul`).

If `V = E` also carries an inner product, then `Z` points outwards along the unit sphere
`S = sphere 0 1`, since `⟪x, x / 2⟫ = 1 / 2` there. So the unit sphere is a hypersurface of
restricted contact type with primitive `λ`
(`TauCeti.SymplecticForm.isRestrictedContactType_sphere`), and the restriction
`α = λ|S` (`TauCeti.SymplecticForm.sphereContactForm`) is a contact form on `S`
(`TauCeti.SymplecticForm.isContactForm_sphereContactForm`). No compatibility between `ω` and the
inner product is needed. For `E = ℝ^(2n+2)` with coordinates `(x, y)` and `ω = 2 Σⱼ dxⱼ ∧ dyⱼ`,
`α` is the standard contact form `Σⱼ (xⱼ dyⱼ - yⱼ dxⱼ)` of `S^(2n+1)`.

The Reeb vector field of `α` is computed through the map `K` determined by
`ω(u, K v) = ⟪u, v⟫`: in ambient coordinates it is `R_α(x) = 2 K x`
(`TauCeti.SymplecticForm.mvfderiv_reebVectorField_sphereContactForm`). When the inner product is
the metric `ω(u, J v)` of a compatible complex structure `J`, then `K = J`, and the Reeb flow
rotates each point along the complex line through it. For the standard form above `K x = J x / 2`,
so `R_α(z) = i z` on `S^(2n+1) ⊂ ℂ^(n+1)`, the generator of the Hopf fibration.

## Main definitions

* `TauCeti.SymplecticForm.radialPrimitive`: the one-form `λₓ(v) = ω(x, v) / 2`.
* `TauCeti.SymplecticForm.sphereContactForm`: its restriction to the unit sphere.

## Main results

* `TauCeti.SymplecticForm.mextDeriv_radialPrimitive`: `dλ = ω`.
* `TauCeti.SymplecticForm.isRestrictedContactType_sphere`: the unit sphere is of restricted
  contact type.
* `TauCeti.SymplecticForm.isContactForm_sphereContactForm`: `λ|S` is a contact form.
* `TauCeti.SymplecticForm.mvfderiv_reebVectorField_sphereContactForm`: its Reeb vector field.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Example 2.1.7 (the standard contact structure on `S^(2n+1)`) and Section 1.4.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (hypersurfaces of contact type, star-shaped hypersurfaces).
-/

public section

noncomputable section

open Metric Module
open scoped Manifold InnerProductSpace

namespace TauCeti

namespace SymplecticForm

section Radial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  (ω : SymplecticForm V)

/-- The **radial primitive** `λₓ(v) = ω(x, v) / 2` of a linear symplectic form `ω`, as a smooth
one-form on `V`. Its exterior derivative is the constant form `ω`
(`TauCeti.SymplecticForm.mextDeriv_radialPrimitive`). -/
def radialPrimitive : SmoothForm 𝓘(ℝ, V) V ℝ 1 :=
  ⟨fun x ↦ ContinuousLinearMap.liouvilleFormCLM ω.toBilinForm.toContinuousBilinearMap x,
    (isSmoothForm_modelSpace_iff.mpr
      (ContinuousLinearMap.liouvilleFormCLM _).contDiff).mem_smoothBundleForms⟩

private theorem radialPrimitive_toRoughForm :
    ω.radialPrimitive.1 =
      fun x ↦ ContinuousLinearMap.liouvilleFormCLM ω.toBilinForm.toContinuousBilinearMap x :=
  (rfl)

/-- The radial primitive evaluates as `λₓ(v) = ω(x, v) / 2`. -/
@[simp]
theorem radialPrimitive_apply (x : V) (v : TangentSpace 𝓘(ℝ, V) x) :
    ω.radialPrimitive.1 x ![v] = 2⁻¹ * ω x v := by
  rw [radialPrimitive_toRoughForm]
  exact (ContinuousLinearMap.liouvilleFormCLM_apply _ x ![v]).trans
    (congrArg ((2⁻¹ : ℝ) • ·) (LinearMap.toContinuousBilinearMap_apply _ _ _))

/-- **The radial primitive is a primitive**: `dλ = ω`. -/
@[simp]
theorem mextDeriv_radialPrimitive : mextDeriv ω.radialPrimitive.1 = ω.constSmooth.1 := by
  funext x
  ext v
  rw [mextDeriv_eq_extDeriv]
  refine (ContinuousLinearMap.extDeriv_liouvilleFormCLM_apply_of_skew _ two_ne_zero
    (fun u w ↦ by simpa using (ω.neg_eq w u).symm) x v).trans ?_
  have h := ω.constSmooth_apply x (v 0) (v 1)
  rw [SmoothBundleForm.eval₂_apply] at h
  have hv : v = ![v 0, v 1] := by
    funext i
    fin_cases i <;> rfl
  conv_rhs => rw [hv]
  exact h.symm

/-- The Liouville field of the radial primitive is half the position field:
`ι_Z ω = λ` for `Z(x) = x / 2`. -/
theorem constSmooth_interior_two_inv_smul :
    RoughForm.interior (I := 𝓘(ℝ, V)) (fun x : V ↦ (2⁻¹ : ℝ) • x) ω.constSmooth.1 =
      ω.radialPrimitive.1 := by
  funext x
  ext v
  have hv : v = ![v 0] := by
    funext i
    fin_cases i
    rfl
  have h := ω.constSmooth_apply x ((2⁻¹ : ℝ) • x) (v 0)
  refine (RoughForm.interior_apply _ _ x v).trans ?_
  rw [hv, radialPrimitive_apply]
  refine ((SmoothBundleForm.eval₂_apply _ _ _ _).symm.trans h).trans ?_
  exact LinearMap.map_smul₂ ω.toBilinForm _ x (v 0)

end Radial

end SymplecticForm

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- A nonzero multiple `x ↦ c • x` of the position field is transverse to the unit sphere: its
inner product with the outward normal `x` is `c`. -/
theorem isTransverseAlong_smul_coe_sphere {c : ℝ} (hc : c ≠ 0) :
    IsTransverseAlong (I := 𝓘(ℝ, E)) (𝓡 n) (fun x : E ↦ c • x)
      ((↑) : sphere (0 : E) 1 → E) := by
  refine isTransverseAlong_iff.2 fun x ⟨v, hv⟩ ↦ hc ?_
  have hmem : c • (x : E) ∈ (ℝ ∙ (x : E))ᗮ := by
    rw [← range_mvfderiv_subtypeVal (n := n)]
    exact ⟨v, (mvfderiv_apply_eq_mfderiv_apply _ _ _).trans hv⟩
  have h := Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self _) hmem
  rwa [inner_smul_right, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere, one_pow,
    mul_one] at h

namespace SymplecticForm

variable [FiniteDimensional ℝ E] (ω : SymplecticForm E)

/-- **The unit sphere of a symplectic vector space is of restricted contact type**, for the
constant form `ω` and its radial primitive `λₓ(v) = ω(x, v) / 2`, with Liouville field
`x ↦ x / 2`. -/
theorem isRestrictedContactType_sphere :
    IsRestrictedContactType (𝓡 n) ω.constSmooth.1 ω.radialPrimitive.1
      ((↑) : sphere (0 : E) 1 → E) :=
  isRestrictedContactType_iff.2 ⟨ω.mextDeriv_radialPrimitive,
    fun x ↦ (2⁻¹ : ℝ) • x,
    contMDiff_vectorSpace_iff_contDiff.2 (contDiff_const.smul contDiff_id),
    ω.constSmooth_interior_two_inv_smul, isTransverseAlong_smul_coe_sphere (by norm_num)⟩

variable (n) in
/-- The restriction `λ|S` of the radial primitive `λₓ(v) = ω(x, v) / 2` to the unit sphere `S`.
It is a contact form (`TauCeti.SymplecticForm.isContactForm_sphereContactForm`). -/
def sphereContactForm : SmoothForm (𝓡 n) (sphere (0 : E) 1) ℝ 1 :=
  SmoothForm.mpullback (↑) contMDiff_coe_sphere ω.radialPrimitive

/-- The contact form of the sphere evaluates a tangent vector `v` at `x` as `ω(x, v) / 2`, with
`v` read in `E`. -/
@[simp]
theorem sphereContactForm_apply (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    (ω.sphereContactForm n).1 x ![v] =
      2⁻¹ * ω x (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v) := by
  have hv : (fun i ↦ mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (![v] i)) =
      ![mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v] := by
    funext i
    fin_cases i
    rfl
  rw [sphereContactForm, SmoothForm.mpullback_apply, hv]
  exact (ω.radialPrimitive_apply _ _).trans
    (congrArg (fun u ↦ 2⁻¹ * ω (x : E) u) (mvfderiv_apply_eq_mfderiv_apply _ _ _).symm)

/-- The exterior derivative of the contact form of the sphere is the restriction of `ω`. -/
@[simp]
theorem mextDeriv_sphereContactForm_apply (x : sphere (0 : E) 1) (v w : TangentSpace (𝓡 n) x) :
    mextDeriv (ω.sphereContactForm n).1 x ![v, w] =
      ω (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v)
        (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w) := by
  have hv : (fun i ↦ mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (![v, w] i)) =
      ![mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v,
        mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x w] := by
    funext i
    fin_cases i <;> rfl
  rw [← mextDerivₗ_apply, sphereContactForm, SmoothForm.mextDerivₗ_mpullback,
    SmoothForm.mpullback_apply, mextDerivₗ_apply, mextDeriv_radialPrimitive, hv,
    ← SmoothBundleForm.eval₂_apply]
  exact (ω.constSmooth_apply _ _ _).trans (congrArg₂ (fun a b ↦ ω a b)
    (mvfderiv_apply_eq_mfderiv_apply _ _ _).symm (mvfderiv_apply_eq_mfderiv_apply _ _ _).symm)

/-- **The standard contact form of the sphere.** The restriction to the unit sphere of the radial
primitive `λₓ(v) = ω(x, v) / 2` of a linear symplectic form is a contact form. -/
theorem isContactForm_sphereContactForm : (ω.sphereContactForm n).IsContactForm := by
  refine (ω.isRestrictedContactType_sphere (n := n)).isContactType.isContactForm_mpullback
    ω.isNondegenerate_constSmooth contMDiff_coe_sphere (fun x ↦ ?_) ?_
  · intro v w hvw
    apply injective_mvfderiv_subtypeVal_sphere (n := n) x
    rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply, hvw]
  · rw [finrank_euclideanSpace_fin, (Fact.out : finrank ℝ E = n + 1)]

/-- **The Reeb vector field of the sphere.** Let `K` be a map with `ω(u, K v) = ⟪u, v⟫` for all
`u` and `v`, such as a compatible complex structure whose metric is the inner product. Then the
Reeb vector field of the contact form `λ|S` is `x ↦ 2 K x`, read in `E`. -/
theorem mvfderiv_reebVectorField_sphereContactForm {K : E → E}
    (hK : ∀ u v, ω u (K v) = ⟪u, v⟫_ℝ) (x : sphere (0 : E) 1) :
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x ((ω.sphereContactForm n).reebVectorField x) =
      (2 : ℝ) • K x := by
  -- The vector `2 K x` is tangent to the sphere, since `⟪K x, x⟫ = ω(K x, K x) = 0`.
  have hmem : (2 : ℝ) • K x ∈ (ℝ ∙ (x : E))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_smul_right, real_inner_comm,
      ← hK, self_eq_zero, mul_zero]
  rw [← range_mvfderiv_subtypeVal (n := n)] at hmem
  obtain ⟨w, hw⟩ := hmem
  rw [ContinuousLinearMap.coe_coe] at hw
  rw [← hw]
  refine congrArg (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x) ?_
  refine ((ω.isContactForm_sphereContactForm (n := n)).eq_reebVectorField_iff.2
    ⟨?_, fun u ↦ ?_⟩).symm
  · -- `λ(2 K x) = ω(x, K x) = ‖x‖² = 1`.
    rw [sphereContactForm_apply, hw]
    simp [hK, norm_eq_of_mem_sphere]
  · -- `dλ(2 K x, u) = -2 ω(u, K x) = -2 ⟪u, x⟫ = 0` for `u` tangent to the sphere.
    have hu : ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x u, (x : E)⟫_ℝ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self _)
        (range_mvfderiv_subtypeVal (n := n) x ▸ LinearMap.mem_range_self _ u)
    have h := hK (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x u) x
    rw [hu] at h
    rw [mextDeriv_sphereContactForm_apply, hw, ← ω.neg_eq]
    simp only [map_smul, h, smul_zero, neg_zero]

end SymplecticForm

end Sphere

end TauCeti
