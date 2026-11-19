/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Distribution
public import TauCeti.Geometry.Contact.Symplectization.Cotangent
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
(`TauCeti.IsContactDistribution.isSymplectic_mextDerivₗ_annihilatorLiouvilleForm`). With the
conventions `ω = -dλ` of the cotangent bundle, `dθ = j^* dλ = -j^* ω`
(`TauCeti.IsContactDistribution.mextDerivₗ_annihilatorLiouvilleForm`), so `j` restricted to
`ξ⁰ ∖ 0` is a symplectic embedding into `(T*M, -ω)`, and `λ_ξ = -θ` is a primitive of `dθ` in the
convention `ω = -dλ` for exact symplectic manifolds.

No coorientation is needed, so this also covers contact structures that are not the kernel of any
global one-form. When `ξ = ker α` for a contact form `α`, the covectors `eᵗ α_x` form one of the two
halves of `ξ⁰ ∖ 0` (`TauCeti.SmoothForm.mem_range_symplectizationToCotangent_or_neg_iff`), and the
map `(t, x) ↦ eᵗ α_x` pulls `λ` back to the symplectization form `eᵗ α`
(`TauCeti.SmoothForm.mpullback_symplectizationToCotangent_liouvilleForm`).

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
* `TauCeti.IsContactDistribution.isSymplectic_mextDerivₗ_annihilatorLiouvilleForm`: `dθ` is a
  symplectic form on `ξ⁰ ∖ 0`.

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
/-- A nonzero covector annihilating `ξ` at a point `x` of an open set `W` on which a one-form `α`
defines `ξ` and is a contact form is a positive multiple `eᵗ β_x` of `β = α` or `β = -α`, and `β`
has the same properties on `W`. -/
private theorem exists_exp_smul_eq {α : SmoothForm I M ℝ 1} {W : Set M}
    (hα : ∀ y ∈ W, RoughForm.ker α.1 y = ξ y ∧ IsContactFormAt α.1 y) {x : M} (hx : x ∈ W)
    {w : TangentSpace I x →L[ℝ] ℝ} (hw : w ∈ annihilatorSpace I ξ x) (hw0 : w ≠ 0) :
    ∃ β : SmoothForm I M ℝ 1, (∀ y ∈ W, RoughForm.ker β.1 y = ξ y ∧ IsContactFormAt β.1 y) ∧
      ∃ t : ℝ, Real.exp t • SmoothForm.degreeOneEquiv β x = w := by
  -- The annihilator of the hyperplane `ξ x = ker α_x` is the line spanned by `α_x`.
  have hker : LinearMap.ker (SmoothForm.degreeOneEquiv α x).toLinearMap = ξ x := by
    rw [← (hα x hx).1]
    ext v
    rw [LinearMap.mem_ker, RoughForm.mem_ker, ContinuousLinearMap.coe_coe,
      SmoothForm.degreeOneEquiv_apply_apply_vec]
  rw [annihilatorSpace_eq_span_singleton hker, Submodule.mem_span_singleton] at hw
  obtain ⟨c, rfl⟩ := hw
  have hc : c ≠ 0 := by
    rintro rfl
    exact hw0 (zero_smul ℝ _)
  rcases hc.lt_or_gt with hneg | hpos
  · -- A negative multiple of `α_x` is a positive multiple of `(-α)_x`.
    refine ⟨-α, fun y hy ↦ ⟨?_, ?_⟩, Real.log (-c), ?_⟩
    · ext v
      simp only [RoughForm.mem_ker, NegMemClass.coe_neg, Pi.neg_apply,
        ContinuousAlternatingMap.neg_apply, neg_eq_zero, ← (hα y hy).1]
    · simpa [NegMemClass.coe_neg] using (hα y hy).2
    · rw [Real.exp_log (neg_pos.2 hneg)]
      ext v
      simp only [FunLike.coe_smul, Pi.smul_apply,
        SmoothForm.degreeOneEquiv_apply_apply_vec, NegMemClass.coe_neg, Pi.neg_apply,
        ContinuousAlternatingMap.neg_apply, smul_eq_mul, neg_mul_neg]
  · exact ⟨α, hα, Real.log c, by rw [Real.exp_log hpos]⟩

variable [Nonempty M] (hξ : IsContactDistribution I ∞ ξ)

/-- The **tautological one-form** `θ` on the annihilator line `ξ⁰ ⊂ T*M` of a contact structure:
the pullback of the Liouville form of `T*M` along the inclusion `ξ⁰ → T*M`, so that
`θ_z(v) = z(dπ v)` (`TauCeti.IsContactDistribution.annihilatorLiouvilleForm_apply`). Here `ξ⁰`
carries the manifold structure of the rank-one annihilator bundle
`TauCeti.IsContMDiffDistribution.annihilatorFiberBundle`. The exterior derivative of `θ` is a
symplectic form on the complement of the zero section
(`TauCeti.IsContactDistribution.isSymplectic_mextDerivₗ_annihilatorLiouvilleForm`). -/
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
    ∀ v : TangentSpace (I.prod 𝓘(ℝ, Fin 1 → ℝ)) z, hξ.annihilatorLiouvilleForm.1 z ![v] =
      (z.2 : TangentSpace I z.proj →L[ℝ] ℝ)
        (mfderiv (I.prod 𝓘(ℝ, Fin 1 → ℝ)) I (TotalSpace.proj : _ → M) z v) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  by
  intro v
  unfold annihilatorLiouvilleForm
  rw [SmoothForm.coe_mpullback, mpullback_liouvilleForm_apply_of_proj_comp_eq
      (ψ := annihilatorInclusion I ξ (Fin 1 → ℝ)) (g := TotalSpace.proj)
      (fun _ ↦ annihilatorInclusion_proj _ _ _ _)
      ((hξ.isContMDiffDistribution.contMDiff_annihilatorInclusion hξ.finrank_sub_one_add_one
        z).mdifferentiableAt (by simp)),
    annihilatorInclusion_snd]
  rfl

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
        (mextDerivₗ (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1 (liouvilleForm I M)).1 p ![u, u'] := by
    rw [mpullback_apply_pair, mfderiv_comp p ((hj (κ p)).mdifferentiableAt (by simp)) hκ,
      SmoothForm.eval₂_mpullback, SmoothBundleForm.eval₂_apply]
    rfl
  have h₂ : SmoothBundleForm.eval₂ (mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization) p u u' =
      mpullback (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) α.symplectizationToCotangent
        (mextDerivₗ (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1 (liouvilleForm I M)).1 p ![u, u'] := by
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
    (hκ : MDifferentiableAt (𝓘(ℝ).prod I) J κ p) (hα : IsContactFormAt α.1 p.2)
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
    {α : SmoothForm I M ℝ 1} {W : Set M} (hW : IsOpen W) (hα : ∀ y ∈ W, RoughForm.ker α.1 y = ξ y)
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} (hzW : z.proj ∈ W) {t : ℝ}
    (hz : Real.exp t • SmoothForm.degreeOneEquiv α z.proj =
      (z.2 : TangentSpace I z.proj →L[ℝ] ℝ)) :
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
  obtain ⟨κ, hκp, hev⟩ : ∃ κ : ℝ × M → TotalSpace (Fin 1 → ℝ) (fun x ↦ annihilatorSpace I ξ x),
      κ (t, z.proj) = z ∧
        annihilatorInclusion I ξ (Fin 1 → ℝ) ∘ κ =ᶠ[𝓝 (t, z.proj)]
          α.symplectizationToCotangent := by
    refine ⟨fun q ↦ if hq : q.2 ∈ W then TotalSpace.mk' (Fin 1 → ℝ) q.2 ⟨_, hmem q hq⟩
      else zeroSection (Fin 1 → ℝ) _ q.2, ?_, ?_⟩
    · simp only [hzW, ↓reduceDIte]
      exact congrArg (TotalSpace.mk z.proj) (Subtype.ext hz)
    · filter_upwards [(hW.preimage continuous_snd).mem_nhds hzW] with q hq
      simp only [comp_apply, show q.2 ∈ W from hq, ↓reduceDIte, annihilatorInclusion_mk']
      refine CotangentBundle.ext (by simp) fun v ↦ ?_
      simp [SmoothForm.degreeOneEquiv_apply_apply_vec]
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
    z ∈ hξ.annihilatorPunctured ↔ z.2 ≠ 0 :=
  mem_zeroSectionCompl

variable [T2Space M]

/-- **The symplectization of a contact structure is nondegenerate.** The exterior derivative of
the tautological one-form of `ξ⁰` is nondegenerate at every nonzero covector annihilating `ξ`. -/
theorem nondegenerate_bilinFormAt_mextDerivₗ_annihilatorLiouvilleForm
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} (hz : z.2 ≠ 0) :
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
  obtain ⟨β, hβ, t, ht⟩ := exists_exp_smul_eq hα hxW z.2.2 fun h ↦ hz (Subtype.ext h)
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
theorem isSymplectic_mextDerivₗ_annihilatorLiouvilleForm :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    SmoothTwoForm.IsSymplectic (SmoothForm.mpullback (Subtype.val : hξ.annihilatorPunctured → _)
      contMDiff_subtype_val (mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 hξ.annihilatorLiouvilleForm)) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  by
  refine ⟨(SmoothForm.isClosed_mextDerivₗ _).mpullback _ _, ?_⟩
  rw [SmoothTwoForm.isNondegenerate_iff_separatingLeft]
  intro z v hv
  exact ((SmoothTwoForm.nondegenerate_bilinFormAt_mpullback_subtype_val_iff z).2
    (hξ.nondegenerate_bilinFormAt_mextDerivₗ_annihilatorLiouvilleForm
      (hξ.mem_annihilatorPunctured.1 z.2))).1 v fun w ↦
      (SmoothForm.bilinFormAt_apply _ z v w).trans (hv w)

end IsContactDistribution

end TauCeti
