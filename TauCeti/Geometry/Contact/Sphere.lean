/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
public import TauCeti.Geometry.Contact.Reeb
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Symplectic.AlmostComplex.Rotation
public import TauCeti.Geometry.Symplectic.Liouville.ContactType
public import TauCeti.Geometry.Symplectic.Liouville.Radial.Basic
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

end SymplecticForm

end Sphere

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
