/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Contact.Symplectization.Cotangent
public import TauCeti.Geometry.Manifold.Diffeomorph.Annihilator
public import TauCeti.Geometry.Manifold.VectorBundle.Cotangent.Annihilator
public import TauCeti.Geometry.Symplectic.Manifold.Opens
public import TauCeti.Topology.VectorBundle.EulerClass
import TauCeti.Geometry.Manifold.DifferentialForm.Closed
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# The symplectization of a contact structure

Let `ξ` be a contact structure on a finite-dimensional manifold `M`: a smooth hyperplane field with
nondegenerate Levi form (`TauCeti.IsContactDistribution`), with no defining one-form or
coorientation chosen. Its *annihilator line* `ξ⁰ ⊂ T*M` consists of the covectors vanishing on the
contact hyperplanes. It is canonically the dual `L*` of the contact line `L = TM ⧸ ξ`, and it is a
smooth line subbundle of `T*M`
(`TauCeti.IsContMDiffDistribution.isSmoothEmbedding_annihilatorInclusion`). Its manifold
structure is that of the rank-one annihilator bundle
`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`, which the statements below install as a
local instance.

The *symplectization* of `ξ` is the complement `ξ⁰ ∖ 0` of the zero section. It carries the
tautological one-form

`θ_z(v) = z(dπ v)`,

the pullback of the Liouville form `λ` of `T*M` along the inclusion `j : ξ⁰ → T*M`
(`TauCeti.IsContactDistribution.annihilatorLiouvilleForm`, with
`TauCeti.IsContactDistribution.annihilatorLiouvilleForm_apply`). This file proves that `dθ` is a
symplectic form on `ξ⁰ ∖ 0`
(`IsContactDistribution.isSymplectic_mpullback_subtype_val_mextDerivₗ_annihilatorLiouvilleForm`).
With the conventions `ω = -dλ` of the cotangent bundle, `dθ = j^* dλ = -j^* ω`
(`TauCeti.IsContactDistribution.mextDerivₗ_annihilatorLiouvilleForm`), so `j` restricted to
`ξ⁰ ∖ 0` is a symplectic embedding into `(T*M, -ω)`, and `λ_ξ = -θ` is a primitive of `dθ` in the
convention `ω = -dλ` for exact symplectic manifolds.

No coorientation is needed, so this also covers contact structures that are not the kernel of any
global one-form. When `ξ = ker α` for a contact form `α`, the covectors `eᵗ α_x` form one of the two
halves of `ξ⁰ ∖ 0` (`TauCeti.SmoothForm.mem_range_symplectizationToCotangent_or_neg_iff`), and the
map `(t, x) ↦ eᵗ α_x` pulls `λ` back to the symplectization form `eᵗ α`
(`TauCeti.SmoothForm.mpullback_symplectizationToCotangent_liouvilleForm`).

Contactomorphisms act on symplectizations. If a diffeomorphism `h : M → N` carries `ξ` onto a
contact structure `ξ'` on `N`, its annihilator lift `Φ : ξ⁰ → ξ'⁰`, `p ↦ p ∘ (dh)⁻¹`
(`Diffeomorph.annihilatorDiffeomorph`), the dual of the induced map of contact lines, satisfies
`Φ^* θ' = θ`
(`TauCeti.IsContactDistribution.mpullback_annihilatorDiffeomorph_annihilatorLiouvilleForm`), since
it is the restriction of the cotangent lift of `h`, which preserves `λ`. It maps `ξ⁰ ∖ 0` onto
`ξ'⁰ ∖ 0` and is therefore a symplectomorphism of symplectizations. No coorientation enters, so
contactomorphisms reversing a coorientation lift as well. The lift is unique: a map `G : ξ⁰ → ξ'⁰`
covering `h` with `G^* θ' = θ` at a point `z` agrees with `Φ` at `z`
(`TauCeti.IsContactDistribution.eq_annihilatorDiffeomorph_of_annihilatorLiouvilleForm`). Indeed
`θ'_(G z)(dG v) = (G z)(dh (dπ v))` and `θ_z(v) = z(dπ v)`, and `dπ` is surjective, so `G z` and
`z ∘ (dh)⁻¹` agree on every tangent vector `dh u`. In particular there is no freedom to shift the
lift along the fibres.

Nondegeneracy is a local statement. Near a point `x` the structure `ξ` is the kernel of a smooth
one-form `α` that is a contact form there
(`TauCeti.IsContactDistribution.exists_smoothForm_ker_eq_isContactFormAt`). A nonzero covector of
`ξ⁰` over `x` is `± eᵗ α_x`; replacing `α` by `-α` if necessary, it is `eᵗ α_x`. Near `(t, x)` the
map `(s, y) ↦ eˢ α_y` factors through `ξ⁰` as `j ∘ κ`, with `κ` smooth because `j` is a smooth
embedding. It pulls `θ` back to `eᵗ α`, whose exterior derivative is nondegenerate at `(t, x)`
(`TauCeti.SmoothForm.nondegenerate_bilinFormAt_mextDerivₗ_symplectization_iff`). So the
differential of `κ` at `(t, x)` is injective, hence bijective between these spaces of dimension
`dim M + 1`, and `dθ` is nondegenerate at `eᵗ α_x`.

## Main definitions

* `TauCeti.IsContactDistribution.annihilatorLiouvilleForm`: the tautological one-form `θ` on `ξ⁰`.
* `TauCeti.IsContactDistribution.annihilatorPunctured`: the open set `ξ⁰ ∖ 0`.

## Main results

* `TauCeti.IsContactDistribution.annihilatorLiouvilleForm_apply`: `θ_z(v) = z(dπ v)`.
* `TauCeti.IsContactDistribution.mextDerivₗ_annihilatorLiouvilleForm`: `dθ = j^* dλ = -j^* ω`.
* `TauCeti.IsContactDistribution.nondegenerate_bilinFormAt_mextDerivₗ_annihilatorLiouvilleForm`:
  `dθ` is nondegenerate at every nonzero covector of `ξ⁰`.
* `IsContactDistribution.isSymplectic_mpullback_subtype_val_mextDerivₗ_annihilatorLiouvilleForm`:
  `dθ` is a symplectic form on `ξ⁰ ∖ 0`.
* `TauCeti.IsContactDistribution.mpullback_annihilatorDiffeomorph_annihilatorLiouvilleForm`,
  `IsContactDistribution.mpullback_annihilatorDiffeomorph_mextDerivₗ_annihilatorLiouvilleForm`:
  the lift of a contactomorphism preserves `θ` and `dθ`.
* `TauCeti.IsContactDistribution.annihilatorDiffeomorph_mem_annihilatorPunctured_iff`: the lift
  maps `ξ⁰ ∖ 0` onto `ξ'⁰ ∖ 0`.
* `TauCeti.IsContactDistribution.eq_annihilatorDiffeomorph_of_annihilatorLiouvilleForm`,
  `TauCeti.IsContactDistribution.eq_annihilatorDiffeomorph_of_mpullback_annihilatorLiouvilleForm`:
  uniqueness of the lift.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989,
  Appendix 4 (the symplectification of a contact manifold as the nonzero covectors annihilating
  the contact hyperplanes).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 and Appendix B (symplectization of a contact structure).
-/

public section

noncomputable section

open Bundle Function Manifold Module Set Topology
open scoped Manifold ContDiff

namespace TauCeti

open CotangentBundle

namespace IsContactDistribution

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] {ξ : Π x : M, Submodule ℝ (TangentSpace I x)}

/-- `C^(∞ + 1)` charts, needed by the annihilator bundle construction of
`TauCeti.IsContMDiffDistribution.annihilatorContMDiffVectorBundle` at smoothness `∞`. -/
local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)

omit [FiniteDimensional ℝ E] in
/-- A nonzero covector `z` annihilating `ξ` over a point `x` of an open set `W` on which a one-form
`α` defines `ξ` and is a contact form is `eᵗ β_x` for `β = α` or `β = -α`, and `β` has the same
properties on `W`. -/
private theorem exists_symplectizationToCotangent_eq {α : SmoothForm I M ℝ 1} {W : Set M}
    (hα : ∀ y ∈ W, RoughForm.ker α.val y = ξ y ∧ IsContactFormAt α.val y)
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} (hzW : z.proj ∈ W)
    (hz : z.snd ≠ 0) :
    ∃ β : SmoothForm I M ℝ 1, (∀ y ∈ W, RoughForm.ker β.val y = ξ y ∧ IsContactFormAt β.val y) ∧
      ∃ t : ℝ,
        β.symplectizationToCotangent (t, z.proj) = annihilatorInclusion I ξ (Fin 1 → ℝ) z := by
  -- `z` is a nonzero covector vanishing on `ker α_x = ξ x`, so it is `eᵗ α_x` or `eᵗ (-α)_x`.
  have hmem := (SmoothForm.mem_range_symplectizationToCotangent_or_neg_iff
    (z := ⟨z.proj, z.snd⟩) (hα _ hzW).2.ne_zero).2
      ⟨fun h ↦ hz (Subtype.ext h), fun v hv ↦ mem_annihilatorSpace_iff.1 z.snd.property v
        (by rwa [← (hα _ hzW).1, RoughForm.mem_ker])⟩
  obtain ⟨β, hβ, ⟨t, y⟩, hp⟩ : ∃ β : SmoothForm I M ℝ 1,
      (∀ y ∈ W, RoughForm.ker β.val y = ξ y ∧ IsContactFormAt β.val y) ∧
        ⟨z.proj, z.snd⟩ ∈ range β.symplectizationToCotangent := by
    rcases hmem with h | h
    · exact ⟨α, hα, h⟩
    · refine ⟨-α, fun y hy ↦ ⟨?_, ?_⟩, h⟩
      · rw [NegMemClass.coe_neg, RoughForm.ker_neg, (hα y hy).1]
      · simpa [NegMemClass.coe_neg] using (hα y hy).2
  obtain rfl : y = z.proj :=
    (SmoothForm.proj_symplectizationToCotangent β (t, y)).symm.trans (congrArg TotalSpace.proj hp)
  exact ⟨β, hβ, t, hp.trans (annihilatorInclusion_apply I ξ (Fin 1 → ℝ) z).symm⟩

variable [Nonempty M] (hξ : IsContactDistribution I ∞ ξ)

/-- The **tautological one-form** `θ` on the annihilator line `ξ⁰ ⊂ T*M` of a contact structure:
the pullback of the Liouville form of `T*M` along the inclusion `ξ⁰ → T*M`, so that
`θ_z(v) = z(dπ v)` (`TauCeti.IsContactDistribution.annihilatorLiouvilleForm_apply`). Here `ξ⁰`
carries the manifold structure of the rank-one annihilator bundle
`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`. The exterior derivative of `θ` is a
symplectic form on the complement of the zero section
(`IsContactDistribution.isSymplectic_mpullback_subtype_val_mextDerivₗ_annihilatorLiouvilleForm`). -/
def annihilatorLiouvilleForm :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    SmoothForm (I.prod 𝓘(ℝ, Fin 1 → ℝ)) (TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x)
      ℝ 1 :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  SmoothForm.mpullback (annihilatorInclusion I ξ (Fin 1 → ℝ))
    (hξ.isContMDiffDistribution.contMDiff_annihilatorInclusion hξ.finrank_sub_one_add_one)
    (liouvilleForm I M)

/-- The tautological one-form of `ξ⁰` is the pullback of the Liouville form of `T*M` along the
inclusion `ξ⁰ → T*M`. -/
theorem annihilatorLiouvilleForm_def :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    hξ.annihilatorLiouvilleForm =
      SmoothForm.mpullback (annihilatorInclusion I ξ (Fin 1 → ℝ))
        (hξ.isContMDiffDistribution.contMDiff_annihilatorInclusion hξ.finrank_sub_one_add_one)
        (liouvilleForm I M) :=
  (rfl)

/-- **The tautological one-form is tautological.** At a covector `z ∈ ξ⁰` the form `θ` applies `z`
to the image of a tangent vector under the derivative of the bundle projection:
`θ_z(v) = z(dπ v)`. -/
theorem annihilatorLiouvilleForm_apply
    (z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    ∀ v : TangentSpace (I.prod 𝓘(ℝ, Fin 1 → ℝ)) z, hξ.annihilatorLiouvilleForm.val z ![v] =
      (z.snd : TangentSpace I z.proj →L[ℝ] ℝ)
        (mfderiv (I.prod 𝓘(ℝ, Fin 1 → ℝ)) I (TotalSpace.proj : _ → M) z v) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  by
  intro v
  rw [annihilatorLiouvilleForm_def, SmoothForm.coe_mpullback,
    mpullback_liouvilleForm_apply_of_proj_comp_eq
      (ψ := annihilatorInclusion I ξ (Fin 1 → ℝ)) (g := TotalSpace.proj)
      (fun _ ↦ annihilatorInclusion_proj _ _ _ _)
      ((hξ.isContMDiffDistribution.contMDiff_annihilatorInclusion hξ.finrank_sub_one_add_one
        z).mdifferentiableAt (by simp)),
    Matrix.cons_val_zero, annihilatorInclusion_apply]

/-- **The symplectic form of the symplectization.** The exterior derivative of the tautological
one-form of `ξ⁰` is the pullback of `dλ` along the inclusion `ξ⁰ → T*M`. With the canonical
symplectic form `ω = -dλ` of `T*M`, this says that `dθ = -j^* ω`. -/
theorem mextDerivₗ_annihilatorLiouvilleForm :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 hξ.annihilatorLiouvilleForm =
      SmoothForm.mpullback (annihilatorInclusion I ξ (Fin 1 → ℝ))
        (hξ.isContMDiffDistribution.contMDiff_annihilatorInclusion hξ.finrank_sub_one_add_one)
        (mextDerivₗ (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1 (liouvilleForm I M)) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  SmoothForm.mextDerivₗ_mpullback _ _ _ _

/-! ### Nondegeneracy away from the zero section -/

section Lift

variable {EX HX X : Type*} [NormedAddCommGroup EX] [NormedSpace ℝ EX] [FiniteDimensional ℝ EX]
  [TopologicalSpace HX] {J : ModelWithCorners ℝ EX HX} [TopologicalSpace X] [ChartedSpace HX X]
  [IsManifold J ∞ X]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ EX] [Nonempty M] in
/-- If `j ∘ κ` agrees near `p` with the map `(s, y) ↦ eˢ α_y` into `T*M`, then `κ` pulls
`j^* dλ` back at `p` to the exterior derivative of the symplectization form `eˢ α`. -/
private theorem eval₂_mpullback_mfderiv_of_eventuallyEq {j : X → CotangentBundle I M}
    (hj : ContMDiff J (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ j) {κ : ℝ × M → X} {α : SmoothForm I M ℝ 1}
    {p : ℝ × M} (hev : j ∘ κ =ᶠ[𝓝 p] α.symplectizationToCotangent)
    (hκ : MDifferentiableAt (𝓘(ℝ).prod I) J κ p) (u u' : TangentSpace (𝓘(ℝ).prod I) p) :
    SmoothBundleForm.eval₂
        (SmoothForm.mpullback j hj (mextDerivₗ (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1 (liouvilleForm I M)))
        (κ p) (mfderiv (𝓘(ℝ).prod I) J κ p u) (mfderiv (𝓘(ℝ).prod I) J κ p u') =
      SmoothBundleForm.eval₂ (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization) p u u' := by
  have h₁ : SmoothBundleForm.eval₂
      (SmoothForm.mpullback j hj (mextDerivₗ (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1 (liouvilleForm I M)))
        (κ p) (mfderiv (𝓘(ℝ).prod I) J κ p u) (mfderiv (𝓘(ℝ).prod I) J κ p u') =
      mpullback (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) (j ∘ κ)
        (mextDerivₗ (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1 (liouvilleForm I M)).val p ![u, u'] := by
    rw [mpullback_apply_pair, mfderiv_comp p ((hj (κ p)).mdifferentiableAt (by simp)) hκ,
      SmoothForm.eval₂_mpullback, SmoothBundleForm.eval₂_apply, Function.comp_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have h₂ : SmoothBundleForm.eval₂ (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization) p u u' =
      mpullback (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) α.symplectizationToCotangent
        (mextDerivₗ (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1 (liouvilleForm I M)).val p ![u, u'] := by
    rw [← SmoothForm.mpullback_symplectizationToCotangent_liouvilleForm,
      SmoothForm.mextDerivₗ_mpullback, SmoothBundleForm.eval₂_apply, SmoothForm.coe_mpullback]
  rw [h₁, h₂, hev.mpullback_eq]

omit [Nonempty M] in
/-- If `j ∘ κ` agrees near `p = (t, x)` with the map `(s, y) ↦ eˢ α_y`, where `α` is a contact form
at `x`, and the source of `j` has dimension `dim M + 1`, then `j^* dλ` is nondegenerate at `κ p`:
the differential of `κ` at `p` is injective, hence bijective. -/
private theorem nondegenerate_bilinFormAt_mpullback_of_eventuallyEq {j : X → CotangentBundle I M}
    (hj : ContMDiff J (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ j) {κ : ℝ × M → X} {α : SmoothForm I M ℝ 1}
    {p : ℝ × M} (hev : j ∘ κ =ᶠ[𝓝 p] α.symplectizationToCotangent)
    (hκ : MDifferentiableAt (𝓘(ℝ).prod I) J κ p) (hα : IsContactFormAt α.val p.2)
    (hfin : finrank ℝ (ℝ × E) = finrank ℝ EX) :
    ((SmoothForm.mpullback j hj
      (mextDerivₗ (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1 (liouvilleForm I M))).bilinFormAt
        (κ p)).Nondegenerate := by
  have key := eval₂_mpullback_mfderiv_of_eventuallyEq hj hev hκ
  have hsep (u : TangentSpace (𝓘(ℝ).prod I) p)
      (hu : ∀ u',
        SmoothBundleForm.eval₂ (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization) p u u' = 0) :
      u = 0 :=
    ((SmoothForm.nondegenerate_bilinFormAt_mextDerivₗ_symplectization_iff α p).2 hα).1 u
      fun u' ↦ (SmoothForm.bilinFormAt_apply _ p u u').trans (hu u')
  have hinj : Injective (mfderiv (𝓘(ℝ).prod I) J κ p) := by
    refine (injective_iff_map_eq_zero _).2 fun u hu ↦ hsep u fun u' ↦ ?_
    rw [← key, hu, ← SmoothForm.bilinFormAt_apply, map_zero, LinearMap.zero_apply]
  have hsurj : Surjective (mfderiv (𝓘(ℝ).prod I) J κ p) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin
      (f := (mfderiv (𝓘(ℝ).prod I) J κ p).toLinearMap)).1 hinj
  rw [LinearMap.BilinForm.Nondegenerate,
    (SmoothForm.isAlt_bilinFormAt _ _).isRefl.nondegenerate_iff_separatingLeft]
  intro v hv
  obtain ⟨u, rfl⟩ := hsurj v
  rw [hsep u fun u' ↦ by rw [← key, ← SmoothForm.bilinFormAt_apply]; exact hv _, map_zero]

end Lift

omit [FiniteDimensional ℝ E] [Nonempty M] in
/-- Over an open set `W` on which a one-form `α` defines `ξ`, the map `(s, y) ↦ eˢ α_y` lifts
near `(t, x)`, with `x ∈ W`, to a map `κ` into `ξ⁰` which is smooth at `(t, x)` and sends it to
the covector `eᵗ α_x`. -/
private theorem exists_lift_annihilatorInclusion
    [FiberBundle (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x]
    (hj : IsSmoothEmbedding (I.prod 𝓘(ℝ, Fin 1 → ℝ)) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞
      (annihilatorInclusion I ξ (Fin 1 → ℝ)))
    {α : SmoothForm I M ℝ 1} {W : Set M} (hW : IsOpen W) (hα : ∀ y ∈ W, RoughForm.ker α.val y = ξ y)
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} (hzW : z.proj ∈ W) {t : ℝ}
    (hz : α.symplectizationToCotangent (t, z.proj) = annihilatorInclusion I ξ (Fin 1 → ℝ) z) :
    ∃ κ : ℝ × M → TotalSpace (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x),
      κ (t, z.proj) = z ∧
        annihilatorInclusion I ξ (Fin 1 → ℝ) ∘ κ =ᶠ[𝓝 (t, z.proj)] α.symplectizationToCotangent ∧
        ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, Fin 1 → ℝ)) ∞ κ (t, z.proj) := by
  classical
  -- Over `W`, the covectors `eˢ α_y` annihilate `ξ`.
  have hmem (q : ℝ × M) (hq : q.2 ∈ W) :
      Real.exp q.1 • SmoothForm.degreeOneEquiv α q.2 ∈ annihilatorSpace I ξ q.2 := by
    rw [mem_annihilatorSpace_iff]
    intro v hv
    rw [← hα q.2 hq, RoughForm.mem_ker] at hv
    simp [SmoothForm.degreeOneEquiv_apply_apply_vec, hv]
  obtain ⟨κ, hev⟩ : ∃ κ : ℝ × M → TotalSpace (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x),
      annihilatorInclusion I ξ (Fin 1 → ℝ) ∘ κ =ᶠ[𝓝 (t, z.proj)]
        α.symplectizationToCotangent := by
    refine ⟨fun q ↦ if hq : q.2 ∈ W then TotalSpace.mk' (Fin 1 → ℝ) q.2 ⟨_, hmem q hq⟩
      else zeroSection (Fin 1 → ℝ) _ q.2, ?_⟩
    filter_upwards [(hW.preimage continuous_snd).mem_nhds hzW] with q hq
    simp only [comp_apply, show q.2 ∈ W from hq, ↓reduceDIte, annihilatorInclusion_mk']
    refine CotangentBundle.ext (by simp) fun v ↦ ?_
    simp [SmoothForm.degreeOneEquiv_apply_apply_vec]
  -- `κ` sends `(t, x)` to `z` because `j` is injective.
  have hκp : κ (t, z.proj) = z :=
    annihilatorInclusion_injective I ξ (Fin 1 → ℝ) (hev.self_of_nhds.trans hz)
  have hι := α.contMDiff_symplectizationToCotangent
  -- `κ` is smooth at `(t, x)` because `j` is a smooth embedding and `j ∘ κ` is smooth there.
  exact ⟨κ, hκp, hev, (ContMDiffAt.iff_comp_isImmersionAt (hj.isImmersion.isImmersionAt _)).2
    ⟨hj.isEmbedding.isInducing.continuousAt_iff.2 (hι.continuous.continuousAt.congr hev.symm),
      (hι _).congr_of_eventuallyEq hev⟩⟩

/-! ### The symplectization -/

/-- The **symplectization** `ξ⁰ ∖ 0` of a contact structure `ξ`: the open set of nonzero covectors
annihilating `ξ`. -/
def annihilatorPunctured :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    TopologicalSpace.Opens (TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  ⟨zeroSectionCompl (Fin 1 → ℝ) _, isOpen_zeroSectionCompl (Fin 1 → ℝ) _⟩

@[simp]
theorem mem_annihilatorPunctured {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} :
    z ∈ hξ.annihilatorPunctured ↔ z.snd ≠ 0 :=
  mem_zeroSectionCompl

/-! ### Lifts of contactomorphisms -/

section Contactomorphism

variable {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [Nonempty N] {ξ' : Π y : N, Submodule ℝ (TangentSpace J y)}
  (hξ' : IsContactDistribution J ∞ ξ') (h : M ≃ₘ⟮I, J⟯ N)
  (hh : ∀ x (v : TangentSpace I x), mfderiv I J h x v ∈ ξ' (h x) ↔ v ∈ ξ x)

/-- `C^(∞ + 1)` charts, needed by the annihilator bundle construction of
`TauCeti.IsContMDiffDistribution.annihilatorContMDiffVectorBundle` at smoothness `∞`. -/
local instance : IsManifold J ((∞ : WithTop ℕ∞) + 1) N := IsManifold.of_le (n := ∞) (by simp)

/-- **Contactomorphisms lift to the symplectization.** Let `h : M → N` be a contactomorphism from
`ξ` to `ξ'`, that is, a diffeomorphism whose differential carries `ξ` onto `ξ'`. Its annihilator
lift `ξ⁰ → ξ'⁰`, `p ↦ p ∘ (dh)⁻¹` (`Diffeomorph.annihilatorDiffeomorph`), pulls the tautological
one-form of `ξ'⁰` back to that of `ξ⁰`. No coorientation is involved, so this holds for
contactomorphisms reversing a coorientation as well. -/
theorem mpullback_annihilatorDiffeomorph_annihilatorLiouvilleForm :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ'.finrank_sub_one_add_one
    SmoothForm.mpullback
        (h.annihilatorDiffeomorph hξ.isContMDiffDistribution hξ.finrank_sub_one_add_one
          hξ'.isContMDiffDistribution hξ'.finrank_sub_one_add_one hh)
        (h.annihilatorDiffeomorph hξ.isContMDiffDistribution hξ.finrank_sub_one_add_one
          hξ'.isContMDiffDistribution hξ'.finrank_sub_one_add_one hh).contMDiff
        hξ'.annihilatorLiouvilleForm =
      hξ.annihilatorLiouvilleForm :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
    hξ'.finrank_sub_one_add_one
  by
  set Φ := h.annihilatorDiffeomorph hξ.isContMDiffDistribution hξ.finrank_sub_one_add_one
    hξ'.isContMDiffDistribution hξ'.finrank_sub_one_add_one hh
  have hj := hξ.isContMDiffDistribution.contMDiff_annihilatorInclusion hξ.finrank_sub_one_add_one
  have hj' :=
    hξ'.isContMDiffDistribution.contMDiff_annihilatorInclusion hξ'.finrank_sub_one_add_one
  -- The annihilator lift is the restriction of the cotangent lift of `h`, which preserves `λ`.
  have hcomp : annihilatorInclusion J ξ' (Fin 1 → ℝ) ∘ Φ =
      h.cotangent ∘ annihilatorInclusion I ξ (Fin 1 → ℝ) :=
    funext (h.annihilatorInclusion_annihilatorDiffeomorph _ _ _ _ hh)
  have hpull : ∀ (f : TotalSpace (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x) →
      CotangentBundle J N) (hf : ContMDiff (I.prod 𝓘(ℝ, Fin 1 → ℝ)) (J.prod 𝓘(ℝ, F →L[ℝ] ℝ)) ∞ f),
      f = h.cotangent ∘ annihilatorInclusion I ξ (Fin 1 → ℝ) →
        SmoothForm.mpullback f hf (liouvilleForm J N) =
          SmoothForm.mpullback _ (h.cotangent.contMDiff.comp hj) (liouvilleForm J N) := by
    rintro _ _ rfl
    rfl
  rw [annihilatorLiouvilleForm_def, annihilatorLiouvilleForm_def, ← LinearMap.comp_apply,
    ← SmoothForm.mpullback_comp Φ _ Φ.contMDiff hj', hpull _ _ hcomp,
    SmoothForm.mpullback_comp _ h.cotangent hj h.cotangent.contMDiff, LinearMap.comp_apply,
    Diffeomorph.mpullback_cotangent_liouvilleForm]

/-- **Lifts of contactomorphisms are symplectic.** The annihilator lift of a contactomorphism
pulls the symplectic form `dθ` of the symplectization of `ξ'` back to that of `ξ`. -/
theorem mpullback_annihilatorDiffeomorph_mextDerivₗ_annihilatorLiouvilleForm :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ'.finrank_sub_one_add_one
    SmoothForm.mpullback
        (h.annihilatorDiffeomorph hξ.isContMDiffDistribution hξ.finrank_sub_one_add_one
          hξ'.isContMDiffDistribution hξ'.finrank_sub_one_add_one hh)
        (h.annihilatorDiffeomorph hξ.isContMDiffDistribution hξ.finrank_sub_one_add_one
          hξ'.isContMDiffDistribution hξ'.finrank_sub_one_add_one hh).contMDiff
        (mextDerivₗ (J.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 hξ'.annihilatorLiouvilleForm) =
      mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 hξ.annihilatorLiouvilleForm :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
    hξ'.finrank_sub_one_add_one
  by
  rw [← SmoothForm.mextDerivₗ_mpullback,
    hξ.mpullback_annihilatorDiffeomorph_annihilatorLiouvilleForm hξ' h hh]

/-- The annihilator lift of a contactomorphism maps the symplectization `ξ⁰ ∖ 0` onto the
symplectization `ξ'⁰ ∖ 0`. -/
theorem annihilatorDiffeomorph_mem_annihilatorPunctured_iff
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
    h.annihilatorDiffeomorph hξ.isContMDiffDistribution hξ.finrank_sub_one_add_one
        hξ'.isContMDiffDistribution hξ'.finrank_sub_one_add_one hh z ∈
          hξ'.annihilatorPunctured ↔ z ∈ hξ.annihilatorPunctured := by
  simp

/-- **Uniqueness of the lift.** Let `G : ξ⁰ → ξ'⁰` be differentiable at `z`, cover the
contactomorphism `h` near `z`, and pull the tautological one-form of `ξ'⁰` back at `z` to that of
`ξ⁰`. Then `G z` is the annihilator lift of `h` at `z`. Only the behaviour of `G` near `z` enters,
so this also applies to lifts defined on the symplectization `ξ⁰ ∖ 0` alone. -/
theorem eq_annihilatorDiffeomorph_of_annihilatorLiouvilleForm
    {G : (TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x) →
      TotalSpace (Fin 1 → ℝ) fun y ↦ annihilatorSpace J ξ' y}
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ'.finrank_sub_one_add_one
    MDifferentiableAt (I.prod 𝓘(ℝ, Fin 1 → ℝ)) (J.prod 𝓘(ℝ, Fin 1 → ℝ)) G z →
      TotalSpace.proj ∘ G =ᶠ[𝓝 z] h ∘ TotalSpace.proj →
      (∀ v, hξ'.annihilatorLiouvilleForm.val (G z)
          ![mfderiv (I.prod 𝓘(ℝ, Fin 1 → ℝ)) (J.prod 𝓘(ℝ, Fin 1 → ℝ)) G z v] =
        hξ.annihilatorLiouvilleForm.val z ![v]) →
      G z = h.annihilatorDiffeomorph hξ.isContMDiffDistribution hξ.finrank_sub_one_add_one
        hξ'.isContMDiffDistribution hξ'.finrank_sub_one_add_one hh z :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
    hξ'.finrank_sub_one_add_one
  by
  intro hG hproj hθ
  set Φ := h.annihilatorDiffeomorph hξ.isContMDiffDistribution hξ.finrank_sub_one_add_one
    hξ'.isContMDiffDistribution hξ'.finrank_sub_one_add_one hh
  have hGz : (G z).proj = h z.proj := hproj.eq_of_nhds
  -- By the chain rule, `dπ' ∘ dG = dh ∘ dπ` at `z`.
  have hchain (v : TangentSpace (I.prod 𝓘(ℝ, Fin 1 → ℝ)) z) :
      mfderiv (J.prod 𝓘(ℝ, Fin 1 → ℝ)) J TotalSpace.proj (G z)
          (mfderiv (I.prod 𝓘(ℝ, Fin 1 → ℝ)) (J.prod 𝓘(ℝ, Fin 1 → ℝ)) G z v) =
        mfderiv I J h z.proj (mfderiv (I.prod 𝓘(ℝ, Fin 1 → ℝ)) I TotalSpace.proj z v) := by
    have hπ' := mfderiv_comp_apply z
      ((contMDiff_proj (n := 1) _).mdifferentiableAt one_ne_zero) hG v
    have hπ := mfderiv_comp_apply z (h.mdifferentiable (by simp) _)
      ((contMDiff_proj (n := 1) _).mdifferentiableAt one_ne_zero) v
    exact hπ'.symm.trans ((DFunLike.congr_fun hproj.mfderiv_eq v).trans hπ)
  -- So `G z` and `Φ z` agree on every vector `dh u`, as `dπ` is surjective.
  have hdh (u : TangentSpace I z.proj) :
      ((G z).snd : TangentSpace J (G z).proj →L[ℝ] ℝ) (mfderiv I J h z.proj u) =
        ((Φ z).snd : TangentSpace J (Φ z).proj →L[ℝ] ℝ) (mfderiv I J h z.proj u) := by
    obtain ⟨v, rfl⟩ := Bundle.mfderiv_proj_surjective z u
    have hv := hθ v
    rw [annihilatorLiouvilleForm_apply, annihilatorLiouvilleForm_apply, hchain] at hv
    rw [hv, h.annihilatorDiffeomorph_snd_apply_mfderiv]
  refine annihilatorInclusion_injective J ξ' (Fin 1 → ℝ) <|
    CotangentBundle.ext (by simp [hGz, Φ]) fun w ↦ ?_
  -- Every tangent vector at `h x` is `dh u` for `u = (dh)⁻¹ w`.
  have hw : mfderiv I J h z.proj (mfderiv J I h.symm (h z.proj) w) = w :=
    h.mfderiv_apply_mfderiv_symm_apply (by simp) z.proj w
  have hu := hdh (mfderiv J I h.symm (h z.proj) w)
  rw [hw] at hu
  rw [annihilatorInclusion_snd, annihilatorInclusion_snd]
  exact hu

/-- **The lift is the unique smooth symplectization map preserving `θ`.** A smooth map
`G : ξ⁰ → ξ'⁰` covering the contactomorphism `h` and pulling the tautological one-form of `ξ'⁰`
back to that of `ξ⁰` is the annihilator lift of `h`. -/
theorem eq_annihilatorDiffeomorph_of_mpullback_annihilatorLiouvilleForm
    {G : (TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x) →
      TotalSpace (Fin 1 → ℝ) fun y ↦ annihilatorSpace J ξ' y} :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
    haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ'.finrank_sub_one_add_one
    ∀ hG : ContMDiff (I.prod 𝓘(ℝ, Fin 1 → ℝ)) (J.prod 𝓘(ℝ, Fin 1 → ℝ)) ∞ G,
      (∀ z, (G z).proj = h z.proj) →
      SmoothForm.mpullback G hG hξ'.annihilatorLiouvilleForm = hξ.annihilatorLiouvilleForm →
      G = h.annihilatorDiffeomorph hξ.isContMDiffDistribution hξ.finrank_sub_one_add_one
        hξ'.isContMDiffDistribution hξ'.finrank_sub_one_add_one hh :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  letI := hξ'.isContMDiffDistribution.annihilatorFiberBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorVectorBundle hξ'.finrank_sub_one_add_one
  haveI := hξ'.isContMDiffDistribution.annihilatorContMDiffVectorBundle
    hξ'.finrank_sub_one_add_one
  fun hG hproj hθ ↦ funext fun z ↦
    hξ.eq_annihilatorDiffeomorph_of_annihilatorLiouvilleForm hξ' h hh
      ((hG z).mdifferentiableAt (by simp)) (Filter.Eventually.of_forall hproj) fun v ↦ by
        rw [← SmoothForm.mpullback_apply_one G hG, hθ]

end Contactomorphism

variable [T2Space M]

/-- **The symplectization of a contact structure is nondegenerate.** The exterior derivative of
the tautological one-form of `ξ⁰` is nondegenerate at every nonzero covector annihilating `ξ`. -/
theorem nondegenerate_bilinFormAt_mextDerivₗ_annihilatorLiouvilleForm
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} (hz : z.snd ≠ 0) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    ((mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 hξ.annihilatorLiouvilleForm).bilinFormAt
      z).Nondegenerate :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  by
  have hj := hξ.isContMDiffDistribution.isSmoothEmbedding_annihilatorInclusion (n := ∞)
    hξ.finrank_sub_one_add_one
  rw [mextDerivₗ_annihilatorLiouvilleForm]
  obtain ⟨W, hW, hxW, α, hα⟩ := hξ.exists_smoothForm_ker_eq_isContactFormAt z.proj
  obtain ⟨β, hβ, t, ht⟩ := exists_symplectizationToCotangent_eq hα hxW hz
  obtain ⟨κ, hκp, hev, hκ⟩ := exists_lift_annihilatorInclusion hj hW (fun y hy ↦ (hβ y hy).1)
    hxW ht
  rw [← hκp]
  refine nondegenerate_bilinFormAt_mpullback_of_eventuallyEq hj.contMDiff hev
    (hκ.mdifferentiableAt (by simp)) (hβ _ hxW).2 ?_
  -- The source `ξ⁰` is modelled on `E × (Fin 1 → ℝ)`.
  simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun, add_comm]

/-- **The symplectization of a contact structure is a symplectic manifold.** The exterior
derivative `dθ` of the tautological one-form restricts to a symplectic form on the open set
`ξ⁰ ∖ 0` of nonzero covectors annihilating `ξ`. No coorientation of `ξ` is needed. -/
theorem isSymplectic_mpullback_subtype_val_mextDerivₗ_annihilatorLiouvilleForm :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    SmoothTwoForm.IsSymplectic (SmoothForm.mpullback (Subtype.val : hξ.annihilatorPunctured → _)
      contMDiff_subtypeVal (mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 hξ.annihilatorLiouvilleForm)) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  by
  refine ⟨(SmoothForm.isClosed_mextDerivₗ _).mpullback _ _, ?_⟩
  rw [SmoothTwoForm.isNondegenerate_iff_separatingLeft]
  intro z v hv
  exact ((SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff z).2
    (hξ.nondegenerate_bilinFormAt_mextDerivₗ_annihilatorLiouvilleForm
      (hξ.mem_annihilatorPunctured.1 z.property))).1 v fun w ↦
      (SmoothForm.bilinFormAt_apply _ z v w).trans (hv w)

end IsContactDistribution

end TauCeti
