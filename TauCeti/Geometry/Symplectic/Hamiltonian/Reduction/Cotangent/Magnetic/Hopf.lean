/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Sphere
public import TauCeti.Geometry.Symplectic.Coadjoint.Sphere
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Cotangent.Magnetic.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.Reduction.Hopf

/-!
# The magnetic term of the Hopf fibration

Let the circle act on the unit sphere `S³ ⊂ ℂ²` by `z ↦ e^(-iθ) z`, whose orbits are the fibres
of the Hopf map `h : S³ → S²` (`TauCeti.hopfMap`), and give `ℂ²` its Kähler form
`Ω(v, w) = Im ⟪v, w⟫_ℂ`. This file computes the magnetic term of cotangent reduction of `T*S³` by
this action at a nonzero value, and shows that it is not exact.

The **Hopf connection** is the one-form `A = 2 λ|S³` on `S³`, where `λ|S³` is the contact form of
the sphere (`TauCeti.SymplecticForm.sphereContactForm`), so that `A_z(v) = Im ⟪z, v⟫_ℂ`. It is
invariant under the circle action
(`TauCeti.SymplecticForm.mpullback_smul_sphereContactForm`) and takes the value `1` on the generator
`i z` of the rotation `z ↦ e^(iθ) z`
(`TauCeti.SymplecticForm.sphereContactForm_apply_of_mvfderiv_eq_I_smul`). Its curvature is half the
area form `σ` of `S²`:

`dA = h^* (σ / 2)`

(`TauCeti.mextDerivₗ_sphereContactForm_eq_mpullback_hopfMap`), so `∫_(S²) σ / 2 = 2π`.

For a value `c ∈ ℝ`, the magnetic one-form of cotangent reduction is `α = c A = 2c λ|S³`, which
pairs the generator `-i z` of the action `z ↦ e^(-iθ) z` with `-c`. Its **magnetic term** is the
two-form `β_c` on `S²` with `h^* β_c = dα`, and

`β_c = (c / 2) σ`

(`TauCeti.mpullback_hopfMap_eq_mextDerivₗ_iff`), `c` times the curvature of the Hopf connection.
For `c > 0`, this is also the reduced form of the Hopf reduction of `ℂ²` at the level
`‖z‖² / 2 = c` (`TauCeti.mpullback_hopfMap_eq_iff`). Its integral over `S²` is `2πc`
(`TauCeti.integralTopForm_of_mpullback_hopfMap_eq_mextDerivₗ`), so for `c ≠ 0` the magnetic term is
not exact (`TauCeti.notMem_exactForms_of_mpullback_hopfMap_eq_mextDerivₗ`): no change of connection,
which changes `β_c` by an exact form, removes it. In the standard picture of cotangent reduction,
the reduced space `T*S³ //_c S¹` is then `T*S²` with a twisted, not a canonical, symplectic form;
this file does not construct the reduced space, and proves only the pullback identity below.

Concretely, along a smooth family `f` of covectors `p` at `z` on the level `p(-i z) = c` of the
cotangent moment map, the magnetic reduction map of `α` along the Hopf map
(`TauCeti.CotangentBundle.magneticReductionMap`) pulls the twisted form `ω_(S²) + π^* β_c` back to
the canonical symplectic form of `T*S³`. This is
`TauCeti.CotangentBundle.mpullback_magneticReductionMap_hopfMap_comp_symplecticForm_add_mpullback`.

## Main results

* `TauCeti.mextDerivₗ_sphereContactForm_eq_mpullback_hopfMap`: the curvature of the Hopf
  connection.
* `TauCeti.mpullback_hopfMap_eq_mextDerivₗ_iff`: the magnetic term at `c` is `(c / 2) σ`.
* `TauCeti.integralTopForm_of_mpullback_hopfMap_eq_mextDerivₗ`: it integrates to `2πc`.
* `TauCeti.notMem_exactForms_of_mpullback_hopfMap_eq_mextDerivₗ`: it is not exact for `c ≠ 0`.
* magnetic reduction of `T*S³` along the Hopf map at `c`:
  `TauCeti.CotangentBundle.mpullback_magneticReductionMap_hopfMap_comp_symplecticForm_add_mpullback`

## References

* Juan-Pablo Ortega and Tudor S. Ratiu, *Cotangent bundle reduction*, in *Encyclopedia of
  Mathematical Physics*, Elsevier, 2006 (the embedding version of cotangent reduction at a
  coadjoint-invariant value, with its magnetic term).
* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  Springer, 1999, Section 6.6 (magnetic terms).
-/

public section

noncomputable section

open Metric Module WithLp Complex Real
open scoped Manifold ContDiff InnerProductSpace

attribute [local instance] TauCeti.finrank_euclideanSpace_fin_succ_fact

local notation "ℂ²" => EuclideanSpace ℂ (Fin 2)
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)
local notation "S³" => sphere (0 : ℂ²) 1
local notation "S²" => sphere (0 : ℝ³) 1

namespace TauCeti

variable {Ω : SymplecticForm ℂ²}

/-! ### The curvature of the Hopf connection -/

/-- **The curvature of the Hopf connection.** For the Kähler form `Ω(v, w) = Im ⟪v, w⟫_ℂ` of
`ℂ²`, the exterior derivative of the contact form `λ|S³` of the unit sphere is the pullback along
the Hopf map of a quarter of the area form `σ` of `S²`. So the Hopf connection `A = 2 λ|S³` has
curvature `dA = h^* (σ / 2)`. -/
theorem mextDerivₗ_sphereContactForm_eq_mpullback_hopfMap (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im) :
    mextDerivₗ (𝓡 3) 1 (Ω.sphereContactForm 3) =
      SmoothForm.mpullback hopfMap contMDiff_hopfMap ((4⁻¹ : ℝ) • sphereAreaForm) := by
  refine SmoothBundleForm.ext_eval₂ fun z v w ↦ ?_
  -- Both sides read as `Im ⟪v, w⟫_ℂ`, the right one through `σ(dh v, dh w) = 4 Im ⟪v, w⟫_ℂ`.
  have h := eval₂_sphereAreaForm_mfderiv_hopfMap z v w
  rw [SmoothBundleForm.eval₂_apply] at h
  rw [SmoothForm.eval₂_mpullback]
  simp only [SmoothBundleForm.eval₂_apply, mextDerivₗ_apply,
    SymplecticForm.mextDeriv_sphereContactForm_apply, Submodule.coe_smul, Pi.smul_apply,
    ContinuousAlternatingMap.smul_apply, h, hΩ, smul_eq_mul]
  ring

/-! ### The magnetic term -/

/-- **The magnetic term of the Hopf fibration.** For the Kähler form `Ω(v, w) = Im ⟪v, w⟫_ℂ` of
`ℂ²` and a real number `c`, a two-form `β` on `S²` pulls back along the Hopf map to the exterior
derivative of the magnetic one-form `c A = 2c λ|S³` exactly when `β = (c / 2) σ`, `c` times the
curvature of the Hopf connection. -/
theorem mpullback_hopfMap_eq_mextDerivₗ_iff (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im) (c : ℝ)
    {β : SmoothTwoForm (𝓡 2) S²} :
    SmoothForm.mpullback hopfMap contMDiff_hopfMap β =
        mextDerivₗ (𝓡 3) 1 ((2 * c) • Ω.sphereContactForm 3) ↔
      β = (c / 2) • sphereAreaForm := by
  rw [map_smul, mextDerivₗ_sphereContactForm_eq_mpullback_hopfMap hΩ, ← map_smul, smul_smul,
    show 2 * c * 4⁻¹ = c / 2 by ring]
  exact (SmoothForm.mpullback_injective_of_surjective contMDiff_hopfMap hopfMap_surjective
    mfderiv_hopfMap_surjective).eq_iff

/-- **The magnetic term of the Hopf fibration integrates to `2πc`.** If a two-form `β` on `S²`
pulls back along the Hopf map to the exterior derivative of `2c λ|S³`, its integral over `S²`, with
its outward-normal orientation, is `2πc`. -/
theorem integralTopForm_of_mpullback_hopfMap_eq_mextDerivₗ (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im)
    {c : ℝ} {β : SmoothTwoForm (𝓡 2) S²}
    (hβ : SmoothForm.mpullback hopfMap contMDiff_hopfMap β =
      mextDerivₗ (𝓡 3) 1 ((2 * c) • Ω.sphereContactForm 3)) :
    integralTopForm (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereOrientation
      β.val = 2 * π * c := by
  rw [(mpullback_hopfMap_eq_mextDerivₗ_iff hΩ c).1 hβ, integralTopForm_smul_sphereAreaForm]
  ring

/-- **The magnetic term of the Hopf fibration is not exact.** For `c ≠ 0`, a two-form `β` on `S²`
that pulls back along the Hopf map to the exterior derivative of `2c λ|S³` is not exact: it is
`(c / 2) σ`, whose integral `2πc` over `S²` does not vanish. -/
theorem notMem_exactForms_of_mpullback_hopfMap_eq_mextDerivₗ
    (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im) {c : ℝ} (hc : c ≠ 0) {β : SmoothTwoForm (𝓡 2) S²}
    (hβ : SmoothForm.mpullback hopfMap contMDiff_hopfMap β =
      mextDerivₗ (𝓡 3) 1 ((2 * c) • Ω.sphereContactForm 3)) :
    β ∉ exactForms (𝓡 2) S² 2 := by
  rw [(mpullback_hopfMap_eq_mextDerivₗ_iff hΩ c).1 hβ]
  exact smul_sphereAreaForm_notMem_exactForms (div_ne_zero hc two_ne_zero)

/-! ### Magnetic reduction of `T*S³` along the Hopf map -/

/-- **The level condition of Hopf magnetic reduction.** Let `p` be a covector at `z ∈ S³` that
takes the value `-c` on the generator `i z` of the circle action, that is `p(-i z) = c`. Then
`p + 2c λ|S³` vanishes on the vertical tangent vectors of the Hopf map. -/
theorem add_smul_sphereContactForm_apply_eq_zero_of_mfderiv_hopfMap_eq_zero
    (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im) {c : ℝ} {z : S³} {p : TangentSpace (𝓡 3) z →L[ℝ] ℝ}
    (hp : ∀ v, mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) z v = I • (z : ℂ²) → p v = -c)
    {v : TangentSpace (𝓡 3) z} (hv : mfderiv (𝓡 3) (𝓡 2) hopfMap z v = 0) :
    p v + ((2 * c) • Ω.sphereContactForm 3).val z ![v] = 0 := by
  -- A vertical vector is `t v₀`, where `v₀` reads as `i z`.
  obtain ⟨t, ht⟩ := (mfderiv_hopfMap_eq_zero_iff z v).1 hv
  have hz : ⟪(z : ℂ²), I • (z : ℂ²)⟫_ℝ = 0 := real_inner_I_smul_self ℂ _
  obtain ⟨v₀, hv₀⟩ := exists_mvfderiv_coe_sphere_eq (n := 3) z hz
  have hvt : v = t • v₀ := injective_mvfderiv_subtypeVal_sphere (n := 3) z
    (by rw [map_smul, hv₀, ht])
  -- The one-form is linear in its argument: read it through `degreeOneEquiv` to pull out `t`.
  have hlin : ((2 * c) • Ω.sphereContactForm 3).val z ![t • v₀] =
      t * ((2 * c) • Ω.sphereContactForm 3).val z ![v₀] := by
    rw [← SmoothForm.degreeOneEquiv_apply_apply_vec, map_smul,
      SmoothForm.degreeOneEquiv_apply_apply_vec, smul_eq_mul]
  rw [hvt, map_smul, hp v₀ hv₀, hlin]
  simp only [SetLike.val_smul, Pi.smul_apply, ContinuousAlternatingMap.coe_smul, smul_eq_mul,
    SymplecticForm.sphereContactForm_apply_of_mvfderiv_eq_I_smul hΩ hv₀]
  ring

variable {EX HX : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [TopologicalSpace HX]
  {IX : ModelWithCorners ℝ EX HX} {X : Type*} [TopologicalSpace X] [ChartedSpace HX X]
  [IsManifold IX ∞ X]

/-- **Magnetic reduction of `T*S³` along the Hopf map.** Let `f` be a smooth family of covectors
`p` at `z ∈ S³` on the level `p(-i z) = c` of the moment map of the circle action
`z ↦ e^(-iθ) z`. Then the magnetic reduction map of the one-form `2c λ|S³` along the Hopf map pulls
the twisted form `ω_(S²) + π^* ((c / 2) σ)` of `T*S²` back along `f` to the canonical symplectic
form of `T*S³`. -/
theorem CotangentBundle.mpullback_magneticReductionMap_hopfMap_comp_symplecticForm_add_mpullback
    (hΩ : ∀ v w, Ω v w = (⟪v, w⟫_ℂ).im) (c : ℝ) {f : X → CotangentBundle (𝓡 3) S³}
    (hf : ContMDiff IX ((𝓡 3).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)) ∞ f)
    (hc : ∀ x v, mvfderiv (𝓡 3) ((↑) : S³ → ℂ²) (f x).proj v = I • ((f x).proj : ℂ²) →
      (f x).snd v = -c) :
    SmoothForm.mpullback
        (CotangentBundle.magneticReductionMap (𝓡 3) (𝓡 2) hopfMap
          ((2 * c) • Ω.sphereContactForm 3) ∘ f)
        (CotangentBundle.contMDiff_magneticReductionMap_comp isSubmersion_hopfMap hf
          (fun x _ hv ↦ add_smul_sphereContactForm_apply_eq_zero_of_mfderiv_hopfMap_eq_zero hΩ
            (hc x) hv) le_rfl)
        (CotangentBundle.symplecticForm (𝓡 2) S² +
          SmoothForm.mpullback (Bundle.TotalSpace.proj : CotangentBundle (𝓡 2) S² → S²)
            (Bundle.contMDiff_proj _) ((c / 2) • sphereAreaForm)) =
      SmoothForm.mpullback f hf (CotangentBundle.symplecticForm (𝓡 3) S³) :=
  CotangentBundle.mpullback_magneticReductionMap_comp_symplecticForm_add_mpullback
    isSubmersion_hopfMap ((mpullback_hopfMap_eq_mextDerivₗ_iff hΩ c).2 rfl) hf
    fun x _ hv ↦ add_smul_sphereContactForm_apply_eq_zero_of_mfderiv_hopfMap_eq_zero hΩ (hc x) hv

end TauCeti
