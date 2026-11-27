/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Analysis.Normed.Module.Ball.Action
public import TauCeti.Geometry.Contact.Reeb
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Symplectic.AlmostComplex.Rotation
public import TauCeti.Geometry.Symplectic.Liouville.ContactType
public import TauCeti.Geometry.Symplectic.Liouville.Radial.Basic
import TauCeti.Analysis.InnerProductSpace.Complex
import TauCeti.Geometry.Contact.Pullback
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
import TauCeti.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Symplectic.CompatibleMetric
import TauCeti.Geometry.Symplectic.Complex.InnerProductSpace

/-!
# The contact form of the unit sphere of a symplectic vector space

Let `ω` be a linear symplectic form on a finite-dimensional real inner product space `E`, with
radial primitive `λₓ(v) = ω(x, v) / 2` (`TauCeti.SymplecticForm.radialPrimitive`, in
`TauCeti.Geometry.Symplectic.Liouville.Radial.Basic`) and Liouville field `Z(x) = x / 2`. Then `Z`
points outwards along the unit sphere `S = sphere 0 1`, since `⟪x, x / 2⟫ = 1 / 2` there. So the
unit sphere is a hypersurface of restricted contact type with primitive `λ`
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

The inclusion of the sphere pulls `ω` back to `dα`
(`TauCeti.SymplecticForm.mpullback_coe_sphere_constSmooth`), so the kernel of the form induced by
`ω` on `S`, its characteristic line, is spanned by the Reeb vector of `α`
(`TauCeti.SymplecticForm.ker_bilinFormAt_mpullback_coe_sphere`): it is a line, of the codimension
one of `S` (`TauCeti.SymplecticForm.finrank_ker_bilinFormAt_mpullback_coe_sphere`). Read in `E`,
the characteristic line at `x` is `ℝ (K x)`
(`TauCeti.SymplecticForm.map_ker_bilinFormAt_mpullback_coe_sphere`). For `ℂⁿ` with
`ω = Σⱼ dxⱼ ∧ dyⱼ`, `K` is multiplication by `i`, so the characteristic line of `S²ⁿ⁻¹` at `z` is
`ℝ (i z)`, the tangent line of the Hopf circle `t ↦ e^{it} z` through `z`; this is the form in
which the null directions of `Im ⟪·, ·⟫_ℂ` on `S²ⁿ⁺¹ ⊂ ℂⁿ⁺¹` are used to build the Fubini–Study
form (`TauCeti.ComplexProjectiveSpace.ker_bilinFormAt_mpullback_coe_sphere`).

For `E = ℂ^ι` with its Kähler form `Ω(v, w) = Im ⟪v, w⟫_ℂ`, the contact form `λ|S` is invariant
under the circle action `z ↦ u z` of the unit complex numbers
(`TauCeti.SymplecticForm.mpullback_smul_sphereContactForm`), since multiplication by `u` preserves
the Hermitian inner product, and it takes the value `1 / 2` on the generator `i z` of that action
(`TauCeti.SymplecticForm.sphereContactForm_apply_of_mvfderiv_eq_I_smul`).

In the compatible case the Reeb orbits are the great circles `cos (2 t) x + sin (2 t) J x` of the
complex lines through the points of `S`, the fibres of the Hopf fibration
(`TauCeti.SymplecticForm.isMIntegralCurve_reebVectorField_sphereContactForm_iff`), since the
solutions of `γ' = θ J γ` are rotations
(`TauCeti.AlmostComplexStructure.eq_cos_smul_add_sin_smul_of_hasDerivAt`). Every orbit is closed
with minimal period `π`
(`TauCeti.SymplecticForm.periodic_iff_of_isMIntegralCurve_reebVectorField_sphereContactForm`), and
the Reeb periods of the sphere are exactly the multiples `k π`
(`TauCeti.SymplecticForm.exists_periodic_reebVectorField_sphereContactForm_iff`).

## Main definitions

* `TauCeti.SymplecticForm.sphereContactForm`: the restriction of the radial primitive to the unit
  sphere.

## Main results

* `TauCeti.SymplecticForm.isRestrictedContactType_sphere`: the unit sphere is of restricted
  contact type.
* `TauCeti.SymplecticForm.isContactForm_sphereContactForm`: `λ|S` is a contact form.
* `TauCeti.SymplecticForm.mvfderiv_reebVectorField_sphereContactForm`: its Reeb vector field.
* `TauCeti.SymplecticForm.mpullback_coe_sphere_constSmooth`: the form induced by `ω` on the
  sphere is the exterior derivative of its contact form.
* `TauCeti.SymplecticForm.ker_bilinFormAt_mpullback_coe_sphere`: the characteristic line of the
  sphere is spanned by its Reeb vector field.
* `TauCeti.SymplecticForm.map_ker_bilinFormAt_mpullback_coe_sphere`: read in the ambient space,
  the characteristic line at `x` is `ℝ (K x)`, the Hopf direction.
* `TauCeti.SymplecticForm.mpullback_smul_sphereContactForm`: for the Kähler form of `ℂ^ι`, it is
  invariant under the circle action.
* `TauCeti.SymplecticForm.sphereContactForm_apply_of_mvfderiv_eq_I_smul`: for the Kähler form of
  `ℂ^ι`, it takes the value `1 / 2` on the generator `i z` of the circle action.
* `TauCeti.SymplecticForm.isMIntegralCurve_reebVectorField_sphereContactForm_iff`: the Reeb
  orbits of the unit sphere are the great circles `cos (2 t) x + sin (2 t) J x`.
* `TauCeti.SymplecticForm.periodic_iff_of_isMIntegralCurve_reebVectorField_sphereContactForm`:
  every Reeb orbit has the periods `k π`, and no others.
* `TauCeti.SymplecticForm.exists_periodic_reebVectorField_sphereContactForm_iff`: the Reeb periods
  of the unit sphere are the multiples of `π`.

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
    IsRestrictedContactType (𝓡 n) ω.constSmooth.val ω.radialPrimitive.val
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

/-- The contact form of the sphere is the pullback of the radial primitive along the inclusion. -/
theorem sphereContactForm_def :
    ω.sphereContactForm n = SmoothForm.mpullback (↑) contMDiff_coe_sphere ω.radialPrimitive :=
  (rfl)

/-- The contact form of the sphere evaluates a tangent vector `v` at `x` as `ω(x, v) / 2`, with
`v` read in `E`. -/
@[simp]
theorem sphereContactForm_apply (x : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) x) :
    (ω.sphereContactForm n).val x ![v] =
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
    mextDeriv (ω.sphereContactForm n).val x ![v, w] =
      ω (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x v)
        (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w) := by
  have hv : (fun i ↦ mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x (![v, w] i)) =
      ![mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x v,
        mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x w] := by
    funext i
    fin_cases i <;> rfl
  have hrad : IsSmoothBundleForm (I := 𝓘(ℝ, E)) (F := ℝ) (V := Bundle.Trivial E ℝ) 1
      ω.radialPrimitive.val :=
    (isSmoothBundleForm_def 1 _).mpr (ω.radialPrimitive.contMDiff.of_le (by simp))
  rw [sphereContactForm, SmoothForm.coe_mpullback,
    ← mpullback_mextDeriv contMDiff_coe_sphere hrad, mpullback_apply,
    mextDeriv_radialPrimitive, hv, ← SmoothBundleForm.eval₂_apply]
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

/-- **The form induced on the sphere is exact.** The inclusion of the unit sphere pulls the
constant form `ω` back to `dα`, the exterior derivative of the contact form `α = λ|S` given by the
radial primitive `λₓ(v) = ω(x, v) / 2`. -/
theorem mpullback_coe_sphere_constSmooth :
    SmoothForm.mpullback ((↑) : sphere (0 : E) 1 → E) contMDiff_coe_sphere ω.constSmooth =
      mextDerivₗ (𝓡 n) 1 (ω.sphereContactForm n) := by
  refine SmoothBundleForm.ext_eval₂ fun x v w ↦ ?_
  rw [SmoothForm.eval₂_mpullback, eval₂_constSmooth_mfderiv_eq, SmoothBundleForm.eval₂_apply,
    mextDerivₗ_apply, mextDeriv_sphereContactForm_apply]

/-- **The characteristic line of the sphere is spanned by its Reeb vector field.** At each point
`x` of the unit sphere, the kernel of the form induced by `ω` is the line spanned by the Reeb
vector of the contact form `λ|S`. -/
theorem ker_bilinFormAt_mpullback_coe_sphere (x : sphere (0 : E) 1) :
    LinearMap.ker ((SmoothForm.mpullback ((↑) : sphere (0 : E) 1 → E) contMDiff_coe_sphere
        ω.constSmooth).bilinFormAt x) =
      ℝ ∙ (ω.sphereContactForm n).reebVectorField x := by
  have hα := ω.isContactForm_sphereContactForm (n := n)
  rw [sphereContactForm_def] at hα ⊢
  rw [← ω.mextDerivₗ_radialPrimitive]
  exact SmoothForm.ker_bilinFormAt_mpullback_mextDerivₗ contMDiff_coe_sphere hα x

/-- The characteristic line of the sphere is a line: the kernel of the form induced by `ω` has
dimension one, the codimension of the sphere. -/
theorem finrank_ker_bilinFormAt_mpullback_coe_sphere (x : sphere (0 : E) 1) :
    finrank ℝ (LinearMap.ker ((SmoothForm.mpullback ((↑) : sphere (0 : E) 1 → E)
      (contMDiff_coe_sphere (n := n)) ω.constSmooth).bilinFormAt x)) = 1 := by
  rw [ker_bilinFormAt_mpullback_coe_sphere]
  exact finrank_span_singleton
    ((ω.isContactForm_sphereContactForm (n := n)).reebVectorField_ne_zero x)

/-- **The characteristic line of the sphere is the Hopf direction.** Let `K` be a map with
`ω(u, K v) = ⟪u, v⟫` for all `u` and `v`, such as a compatible complex structure whose metric is
the inner product. Read in the ambient space, the characteristic line of the unit sphere at `x` is
the line `ℝ (K x)`. For `ℂⁿ` with its standard symplectic form, `K x = i x`, and this is the
direction of the Hopf circle through `x`. -/
theorem map_ker_bilinFormAt_mpullback_coe_sphere {K : E → E} (hK : ∀ u v, ω u (K v) = ⟪u, v⟫_ℝ)
    (x : sphere (0 : E) 1) :
    (LinearMap.ker ((SmoothForm.mpullback ((↑) : sphere (0 : E) 1 → E) contMDiff_coe_sphere
        ω.constSmooth).bilinFormAt x)).map
        (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x : TangentSpace (𝓡 n) x →ₗ[ℝ] E) =
      ℝ ∙ K x := by
  rw [ker_bilinFormAt_mpullback_coe_sphere, Submodule.map_span, Set.image_singleton,
    ContinuousLinearMap.coe_coe, ω.mvfderiv_reebVectorField_sphereContactForm hK,
    Submodule.span_singleton_smul_eq (IsUnit.mk0 (2 : ℝ) two_ne_zero)]

end SymplecticForm

end Sphere

/-! ### Invariance under the circle action -/

section Circle

namespace SymplecticForm

variable {ι : Type*} [Fintype ι] {d : ℕ} [Fact (finrank ℝ (EuclideanSpace ℂ ι) = d + 1)]
  {Ω : SymplecticForm (EuclideanSpace ℂ ι)}

/-- **The contact form of the sphere of `ℂ^ι` is invariant under the circle action.** For the
Kähler form `Ω(v, w) = Im ⟪v, w⟫_ℂ` of `ℂ^ι`, the rotation `z ↦ u z` of the unit sphere by a unit
complex number `u` pulls the contact form `λ|S` back to itself. -/
theorem mpullback_smul_sphereContactForm (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im) (u : Circle) :
    SmoothForm.mpullback (fun z : sphere (0 : EuclideanSpace ℂ ι) 1 ↦ u • z)
      (ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) u) (Ω.sphereContactForm d) =
        Ω.sphereContactForm d := by
  refine SmoothBundleForm.ext fun z v ↦ ?_
  have hv : v = ![v 0] := (FinVec.etaExpand_eq v).symm
  set L : EuclideanSpace ℂ ι →L[ℝ] EuclideanSpace ℂ ι :=
    ((u : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ ι)).restrictScalars ℝ
  have hL (x : EuclideanSpace ℂ ι) : L x = (u : ℂ) • x := by simp [L]
  -- Read in `ℂ^ι`, the rotation of the sphere is the restriction of `L`.
  have hcomp : ((↑) : sphere (0 : EuclideanSpace ℂ ι) 1 → EuclideanSpace ℂ ι) ∘
      (fun z ↦ u • z) = L ∘ (↑) :=
    funext fun z ↦ by simp [hL, Circle.coe_smul_sphere]
  have hd : mvfderiv (𝓡 d) ((↑) : sphere (0 : EuclideanSpace ℂ ι) 1 → EuclideanSpace ℂ ι) (u • z)
      (mfderiv (𝓡 d) (𝓡 d) (fun z ↦ u • z) z (v 0)) =
        L (mvfderiv (𝓡 d) ((↑) : sphere (0 : EuclideanSpace ℂ ι) 1 → EuclideanSpace ℂ ι) z
          (v 0)) := by
    rw [← mvfderiv_comp_apply z ((contMDiff_coe_sphere (n := d) (m := 1) _).mdifferentiableAt
      one_ne_zero) ((ContMDiffSMul.contMDiff_const_smul (I := 𝓡 1) (n := 1) u z).mdifferentiableAt
        one_ne_zero) (v 0), hcomp,
      L.mvfderiv_comp_apply ((contMDiff_coe_sphere (n := d) (m := 1) z).mdifferentiableAt
        one_ne_zero)]
  rw [hv, SmoothForm.mpullback_apply_one, sphereContactForm_apply, sphereContactForm_apply, hd, hL,
    hΩ, hΩ, Circle.coe_smul_sphere, inner_smul_smul_of_norm_eq_one (Circle.norm_coe u)]

/-- **The contact form on the generator of the circle action.** For the Kähler form
`Ω(v, w) = Im ⟪v, w⟫_ℂ` of `ℂ^ι`, the contact form `λ|S` takes the value `1 / 2` on a tangent
vector at `z` that reads as `i z`, the velocity of the circle orbit `t ↦ e^(it) z`. -/
theorem sphereContactForm_apply_of_mvfderiv_eq_I_smul (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im)
    {z : sphere (0 : EuclideanSpace ℂ ι) 1} {v : TangentSpace (𝓡 d) z}
    (hv : mvfderiv (𝓡 d) ((↑) : sphere (0 : EuclideanSpace ℂ ι) 1 → EuclideanSpace ℂ ι) z v =
      Complex.I • (z : EuclideanSpace ℂ ι)) :
    (Ω.sphereContactForm d).val z ![v] = 1 / 2 := by
  rw [sphereContactForm_apply, hv, hΩ, inner_smul_right, inner_self_eq_norm_sq_to_K,
    norm_eq_of_mem_sphere z]
  simp

end SymplecticForm

end Circle

/-! ### The Reeb flow of the unit sphere -/

section ReebOrbit

open Function Real
open scoped RealInnerProductSpace

namespace SymplecticForm

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)] {ω : SymplecticForm E} {J : AlmostComplexStructure E}

omit [FiniteDimensional ℝ E] in
/-- The great circles `t ↦ cos (θ t) x + sin (θ t) J x` through the points of the unit sphere stay
on it: for a compatible `J` the vectors `x` and `J x` are orthonormal, so the circle is the
isometric image of the unit circle of `ℂ`. -/
private theorem cos_smul_add_sin_smul_mem_sphere (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    {x : E} (hx : x ∈ sphere (0 : E) 1) (θ : ℝ) :
    Real.cos θ • x + Real.sin θ • J x ∈ sphere (0 : E) 1 := by
  have hJ (v w : E) : ⟪J v, J w⟫ = ⟪v, w⟫ := by
    rw [inner_apply_left_eq_of_apply_apply_eq_inner hg, hg]
  have h := J.norm_re_smul_add_im_smul hJ (norm_eq_of_mem_sphere ⟨x, hx⟩)
    (Complex.exp (θ * Complex.I))
  rw [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.norm_exp_ofReal_mul_I] at h
  rwa [mem_sphere_zero_iff_norm]

/-- **The Reeb orbits of the unit sphere are great circles.** If the inner product of `E` is the
metric `ω(·, J ·)`, a curve `γ` on the unit sphere is an integral curve of the Reeb vector field of
the contact form `λ|S` exactly when it is the rotation `t ↦ cos (2 t) γ(0) + sin (2 t) J γ(0)` of
its initial point along the complex line of `J` through it. These great circles are the fibres of
the Hopf fibration. -/
theorem isMIntegralCurve_reebVectorField_sphereContactForm_iff
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {γ : ℝ → sphere (0 : E) 1} :
    IsMIntegralCurve γ (ω.sphereContactForm n).reebVectorField ↔
      ∀ t, (γ t : E) = Real.cos (2 * t) • (γ 0 : E) + Real.sin (2 * t) • J (γ 0 : E) := by
  -- In ambient coordinates the Reeb field is `x ↦ 2 J x`.
  have hR (x : sphere (0 : E) 1) :
      mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x
        ((ω.sphereContactForm n).reebVectorField x) = (2 : ℝ) • J (x : E) := by
    rw [← mvfderiv_apply_eq_mfderiv_apply]
    exact ω.mvfderiv_reebVectorField_sphereContactForm hg x
  have hcoe (x : sphere (0 : E) 1) :
      HasMFDerivAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x
        (mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x) :=
    ((contMDiff_coe_sphere x).mdifferentiableAt one_ne_zero).hasMFDerivAt
  constructor
  · -- The ambient curve solves `γ' = 2 J γ`, so it is a rotation.
    intro hγ
    rw [isMIntegralCurve_iff_isMIntegralCurveOn] at hγ
    have hmap := hγ.map_of_mfderiv_eq (f := ((↑) : sphere (0 : E) 1 → E))
      (W := fun y : E ↦ (2 : ℝ) • J y) (fun t _ ↦ (hcoe (γ t)).mdifferentiableAt)
      (fun t _ ↦ hR (γ t))
    have hint := isMIntegralCurveOn_iff_isIntegralCurveOn.1 hmap
    exact J.eq_cos_smul_add_sin_smul_of_hasDerivAt (γ := fun t ↦ (γ t : E))
      fun t ↦ hasDerivWithinAt_univ.1 (hint t trivial)
  · -- The great circle is smooth on the sphere, and its velocity is the Reeb field since the
    -- differential of the inclusion is injective.
    intro hγ t
    set c : ℝ → E := fun t ↦ Real.cos (2 * t) • (γ 0 : E) + Real.sin (2 * t) • J (γ 0 : E)
    have hc : ContDiff ℝ 1 c := by fun_prop
    have hmem (t : ℝ) : c t ∈ sphere (0 : E) 1 :=
      cos_smul_add_sin_smul_mem_sphere hg (γ 0).property _
    have hγc : γ = Set.codRestrict c (sphere (0 : E) 1) hmem := funext fun t ↦ Subtype.ext (hγ t)
    have hγd : MDifferentiableAt 𝓘(ℝ) (𝓡 n) γ t := by
      rw [hγc]
      exact (hc.contMDiff.codRestrict_sphere hmem).mdifferentiableAt one_ne_zero
    -- The velocity of the ambient curve is `2 J γ`.
    have hv : mfderiv (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (γ t)
        (mfderiv 𝓘(ℝ) (𝓡 n) γ t (1 : ℝ)) = (2 : ℝ) • J (γ t : E) := by
      have h1 := (hcoe (γ t)).comp t hγd.hasMFDerivAt
      rw [show ((↑) : sphere (0 : E) 1 → E) ∘ γ = c from funext hγ] at h1
      have h2 : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ, E) c t _ :=
        (J.hasDerivAt_cos_smul_add_sin_smul 2 (γ 0 : E) t).hasFDerivAt.hasMFDerivAt
      -- Evaluating both derivatives of `c` at `1`; `change` unfolds the `TangentSpace` synonyms.
      have h := DFunLike.congr_fun (h1.mfderiv.symm.trans h2.mfderiv) (1 : ℝ)
      change _ = (1 : ℝ) • (2 : ℝ) • J (c t) at h
      rwa [one_smul, ← show (γ t : E) = c t from hγ t] at h
    refine hγd.hasMFDerivAt.congr_mfderiv (ContinuousLinearMap.ext_ring ?_)
    refine Eq.trans ?_ (one_smul ℝ _).symm
    -- Compare the velocities after pushing them forward along the injective inclusion.
    refine injective_mvfderiv_subtypeVal_sphere (n := n) (γ t) ?_
    rw [mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply]
    exact hv.trans (hR (γ t)).symm

/-- **The periods of a Reeb orbit of the unit sphere.** If the inner product of `E` is the metric
`ω(·, J ·)`, every integral curve of the Reeb vector field of the contact form `λ|S` has period `T`
exactly when `T` is an integer multiple of `π`: every Reeb orbit is closed, with minimal period
`π`. -/
theorem periodic_iff_of_isMIntegralCurve_reebVectorField_sphereContactForm
    (hg : ∀ v w, ω v (J w) = ⟪v, w⟫) {γ : ℝ → sphere (0 : E) 1}
    (hγ : IsMIntegralCurve γ (ω.sphereContactForm n).reebVectorField) (T : ℝ) :
    Periodic γ T ↔ ∃ k : ℤ, T = k * π := by
  have hγ' : ((↑) : sphere (0 : E) 1 → E) ∘ γ =
      fun t ↦ Real.cos (2 * t) • (γ 0 : E) + Real.sin (2 * t) • J (γ 0 : E) :=
    funext ((isMIntegralCurve_reebVectorField_sphereContactForm_iff hg).1 hγ)
  have h0 : (γ 0 : E) ≠ 0 := ne_zero_of_mem_unit_sphere (γ 0)
  have hper : Periodic γ T ↔ Periodic (((↑) : sphere (0 : E) 1 → E) ∘ γ) T :=
    ⟨fun h t ↦ congrArg Subtype.val (h t), fun h t ↦ Subtype.ext (h t)⟩
  rw [hper, hγ', J.periodic_cos_smul_add_sin_smul_iff h0]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [hk]; ring⟩

/-- **The Reeb periods of the unit sphere are the multiples of `π`.** If the inner product of `E`
is the metric `ω(·, J ·)`, the Reeb vector field of the contact form `λ|S` of the unit sphere has a
`T`-periodic integral curve exactly when `T` is an integer multiple of `π`. For `ℝ²ⁿ` with
`ω = Σ dqⱼ ∧ dpⱼ` these are the periods `k π` of the closed Reeb orbits of `∂D²ⁿ`, the `k`-fold
covers of the simple orbits of period `π`, which the slopes of the Hamiltonians defining
`SH_*(D²ⁿ)` must avoid. -/
theorem exists_periodic_reebVectorField_sphereContactForm_iff (hg : ∀ v w, ω v (J w) = ⟪v, w⟫)
    (T : ℝ) :
    (∃ γ : ℝ → sphere (0 : E) 1,
        IsMIntegralCurve γ (ω.sphereContactForm n).reebVectorField ∧ Periodic γ T) ↔
      ∃ k : ℤ, T = k * π := by
  constructor
  · rintro ⟨γ, hγ, hT⟩
    exact (periodic_iff_of_isMIntegralCurve_reebVectorField_sphereContactForm hg hγ T).1 hT
  · intro hT
    have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = n + 1)
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := (0 : E)) (r := 1)).2 zero_le_one
    have hmem (t : ℝ) : Real.cos (2 * t) • x + Real.sin (2 * t) • J x ∈ sphere (0 : E) 1 :=
      cos_smul_add_sin_smul_mem_sphere hg hx _
    have hγ : IsMIntegralCurve (fun t ↦ (⟨_, hmem t⟩ : sphere (0 : E) 1))
        (ω.sphereContactForm n).reebVectorField :=
      (isMIntegralCurve_reebVectorField_sphereContactForm_iff hg).2 fun t ↦ by simp
    exact ⟨_, hγ, (periodic_iff_of_isMIntegralCurve_reebVectorField_sphereContactForm hg hγ T).2 hT⟩

end SymplecticForm

end ReebOrbit

end TauCeti
