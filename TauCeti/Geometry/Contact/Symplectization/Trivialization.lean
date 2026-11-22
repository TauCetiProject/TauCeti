/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Symplectization.Annihilator
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic

/-!
# The contact-form trivialization of the symplectization

Let `ξ` be a contact structure on a finite-dimensional manifold `M`. Its symplectization is the
complement `ξ⁰ ∖ 0` of the zero section in the annihilator line `ξ⁰ ⊂ T*M`, with the tautological
one-form `θ_z(v) = z(dπ v)` (`TauCeti.IsContactDistribution.annihilatorLiouvilleForm`) and the
symplectic form `dθ`. This needs no coorientation of `ξ`.

When `ξ = ker α` for a global one-form `α`, the map

`κ_α : ℝ × M → ξ⁰`, `(t, x) ↦ eᵗ α_x`

(`TauCeti.SmoothForm.symplectizationToAnnihilator`) identifies the usual symplectization `ℝ × M`,
with the form `eᵗ α`, with one half of `ξ⁰ ∖ 0`. Composed with the inclusion `ξ⁰ → T*M` it is the
map `(t, x) ↦ eᵗ α_x` into the cotangent bundle
(`TauCeti.SmoothForm.symplectizationToCotangent`). This file proves:

* `κ_α` is smooth and pulls `θ` back to the symplectization form `eᵗ α`, hence `dθ` back to
  `d(eᵗ α)` (`TauCeti.SmoothForm.mpullback_symplectizationToAnnihilator_annihilatorLiouvilleForm`);
* for nowhere vanishing `α`, `κ_α` is injective, its image consists of the covectors that are
  positive multiples of `α`, and the images of `κ_α` and `κ_(-α)` are disjoint and together form
  `ξ⁰ ∖ 0` (`TauCeti.SmoothForm.mem_range_symplectizationToAnnihilator_or_neg_iff`);
* for a contact form `α` on a boundaryless manifold, `κ_α` is a local diffeomorphism
  (`TauCeti.SmoothForm.IsContactForm.isLocalDiffeomorph_symplectizationToAnnihilator`). So `κ_α`
  is a diffeomorphism from `ℝ × M` onto an open half of `ξ⁰ ∖ 0` carrying `d(eᵗ α)` to `dθ`;
* changing the contact form to `β = f α` changes the trivialization by the lift
  `(t, x) ↦ (t - log f(x), x)` of the identity when `f > 0`
  (`TauCeti.SmoothForm.symplectizationToAnnihilator_symplectizationLift`), and exchanges the two
  halves when `f < 0`
  (`TauCeti.SmoothForm.symplectizationToAnnihilator_symplectizationLift_neg`).

In the coordinate `r = eᵗ` on the fibres, these are the trivializations of the punctured dual
contact line `L* ∖ 0` with positive fibre coordinate `r` in which `θ = r α`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, second edition, Springer, 1989,
  Appendix 4 (the symplectification of a contact manifold).
* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 1.1 and Appendix B (symplectization of a contact structure).
-/

public section

noncomputable section

open Bundle Function Manifold Module Set
open scoped Manifold ContDiff

namespace TauCeti

open CotangentBundle

namespace SmoothForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {ξ : Π x : M, Submodule ℝ (TangentSpace I x)} {α : SmoothForm I M ℝ 1}

/-- The covector `eᵗ α_x` annihilates `ξ x` when `ξ = ker α`. -/
private theorem exp_smul_degreeOneEquiv_mem_annihilatorSpace (hα : α.kerDistribution = ξ)
    (p : ℝ × M) : Real.exp p.1 • degreeOneEquiv α p.2 ∈ annihilatorSpace I ξ p.2 := by
  rw [mem_annihilatorSpace_iff]
  intro v hv
  rw [← hα, mem_kerDistribution] at hv
  simp [hv]

/-- The **contact-form trivialization** `κ_α : ℝ × M → ξ⁰`, `(t, x) ↦ eᵗ α_x`, of the annihilator
line of the hyperplane field `ξ = ker α`. For a contact form `α` it is a diffeomorphism of the
symplectization `ℝ × M` onto one half of `ξ⁰ ∖ 0`, pulling the tautological one-form back to
`eᵗ α` (`TauCeti.SmoothForm.mpullback_symplectizationToAnnihilator_annihilatorLiouvilleForm`). -/
def symplectizationToAnnihilator (α : SmoothForm I M ℝ 1) (hα : α.kerDistribution = ξ)
    (p : ℝ × M) : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x :=
  TotalSpace.mk' (Fin 1 → ℝ) p.2 ⟨_, exp_smul_degreeOneEquiv_mem_annihilatorSpace hα p⟩

variable (hα : α.kerDistribution = ξ)

/-- The covector `κ_α(t, x) = eᵗ α_x` lies over `x`. -/
@[simp]
theorem proj_symplectizationToAnnihilator (p : ℝ × M) :
    (α.symplectizationToAnnihilator hα p).proj = p.2 :=
  (rfl)

/-- The covector `κ_α(t, x)` evaluates a tangent vector `v` to `eᵗ α_x(v)`. -/
@[simp]
theorem symplectizationToAnnihilator_snd_apply (p : ℝ × M)
    (v : TangentSpace I (α.symplectizationToAnnihilator hα p).proj) :
    ((α.symplectizationToAnnihilator hα p).snd :
        TangentSpace I (α.symplectizationToAnnihilator hα p).proj →L[ℝ] ℝ) v =
      Real.exp p.1 * α.val p.2 ![v] := by
  simp only [symplectizationToAnnihilator]
  exact congrArg (Real.exp p.1 * ·) (degreeOneEquiv_apply_apply_vec α p.2 v)

/-- Followed by the inclusion `ξ⁰ → T*M`, the trivialization `κ_α` is the map `(t, x) ↦ eᵗ α_x`
into the cotangent bundle. -/
@[simp]
theorem annihilatorInclusion_symplectizationToAnnihilator (p : ℝ × M) :
    annihilatorInclusion I ξ (Fin 1 → ℝ) (α.symplectizationToAnnihilator hα p) =
      α.symplectizationToCotangent p := by
  rw [annihilatorInclusion_apply]
  exact CotangentBundle.ext (by simp) fun v ↦ (symplectizationToAnnihilator_snd_apply hα p v).trans
    (symplectizationToCotangent_snd_apply α p v).symm

/-- Followed by the inclusion `ξ⁰ → T*M`, the trivialization `κ_α` is the map `(t, x) ↦ eᵗ α_x`
into the cotangent bundle. -/
theorem annihilatorInclusion_comp_symplectizationToAnnihilator :
    annihilatorInclusion I ξ (Fin 1 → ℝ) ∘ α.symplectizationToAnnihilator hα =
      α.symplectizationToCotangent :=
  funext <| annihilatorInclusion_symplectizationToAnnihilator hα

/-- A covector of `ξ⁰` lies in the image of `κ_α` exactly when, as a covector of `T*M`, it lies in
the image of `(t, x) ↦ eᵗ α_x`. -/
private theorem mem_range_symplectizationToAnnihilator_iff_mk
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} :
    z ∈ range (α.symplectizationToAnnihilator hα) ↔
      (⟨z.proj, z.snd⟩ : CotangentBundle I M) ∈ range α.symplectizationToCotangent := by
  rw [← annihilatorInclusion_apply, ← annihilatorInclusion_comp_symplectizationToAnnihilator hα,
    range_comp, (annihilatorInclusion_injective I ξ (Fin 1 → ℝ)).mem_set_image]

/-- For a nowhere vanishing one-form `α`, the trivialization `κ_α` is injective. -/
theorem symplectizationToAnnihilator_injective (hα₀ : ∀ x, α.val x ≠ 0) :
    Injective (α.symplectizationToAnnihilator hα) := fun _ _ h ↦
  symplectizationToCotangent_injective hα₀ <| by
    simpa using congrArg (annihilatorInclusion I ξ (Fin 1 → ℝ)) h

/-- A covector of `ξ⁰` lies in the image of `κ_α` exactly when it is a positive multiple of the
value of `α` at its base point. -/
theorem mem_range_symplectizationToAnnihilator_iff
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} :
    z ∈ range (α.symplectizationToAnnihilator hα) ↔
      ∃ c : ℝ, 0 < c ∧
        ∀ v, (z.snd : TangentSpace I z.proj →L[ℝ] ℝ) v = c * α.val z.proj ![v] := by
  rw [mem_range_symplectizationToAnnihilator_iff_mk, mem_range_symplectizationToCotangent_iff]

/-- For a nowhere vanishing one-form `α`, the images of the trivializations `κ_α` and `κ_(-α)` are
disjoint. -/
theorem disjoint_range_symplectizationToAnnihilator_neg (hα₀ : ∀ x, α.val x ≠ 0) :
    Disjoint (range (α.symplectizationToAnnihilator hα))
      (range ((-α).symplectizationToAnnihilator (kerDistribution_neg.trans hα))) := by
  rw [← disjoint_image_iff (annihilatorInclusion_injective I ξ (Fin 1 → ℝ)), ← range_comp,
    ← range_comp, annihilatorInclusion_comp_symplectizationToAnnihilator,
    annihilatorInclusion_comp_symplectizationToAnnihilator]
  exact disjoint_range_symplectizationToCotangent_neg hα₀

/-- **The two halves of the symplectization.** For a nowhere vanishing one-form `α` with kernel
`ξ`, a covector of `ξ⁰` lies in the image of `κ_α` or in that of `κ_(-α)` exactly when it is
nonzero. So the images of the two trivializations are the two halves of `ξ⁰ ∖ 0`. -/
theorem mem_range_symplectizationToAnnihilator_or_neg_iff (hα₀ : ∀ x, α.val x ≠ 0)
    {z : TotalSpace (Fin 1 → ℝ) fun x ↦ annihilatorSpace I ξ x} :
    z ∈ range (α.symplectizationToAnnihilator hα) ∨
        z ∈ range ((-α).symplectizationToAnnihilator (kerDistribution_neg.trans hα)) ↔
      z.snd ≠ 0 := by
  rw [mem_range_symplectizationToAnnihilator_iff_mk, mem_range_symplectizationToAnnihilator_iff_mk,
    mem_range_symplectizationToCotangent_or_neg_iff (hα₀ z.proj)]
  -- Every covector of `ξ⁰` vanishes on `ker α = ξ`.
  refine ⟨fun h h0 ↦ h.1 (by rw [h0, ZeroMemClass.coe_zero]), fun h ↦
    ⟨fun h0 ↦ h (Subtype.ext h0), fun v hv ↦ ?_⟩⟩
  exact mem_annihilatorSpace_iff.1 z.snd.property v
    (by rw [← congrFun hα z.proj, mem_kerDistribution]; exact hv)

/-- For a nowhere vanishing one-form `α`, the trivialization `κ_α` takes values in `ξ⁰ ∖ 0`. -/
theorem symplectizationToAnnihilator_snd_ne_zero (hα₀ : ∀ x, α.val x ≠ 0) (p : ℝ × M) :
    (α.symplectizationToAnnihilator hα p).snd ≠ 0 :=
  (mem_range_symplectizationToAnnihilator_or_neg_iff hα hα₀).1 (.inl ⟨p, rfl⟩)

/-! ### Change of contact form -/

/-- **Change of contact form.** If `β = f α` for a positive function `f`, the trivializations of
`ξ⁰` by `α` and by `β` differ by the lift `(t, x) ↦ (t - log f(x), x)` of the identity:
`κ_β(t - log f(x), x) = κ_α(t, x)`. -/
theorem symplectizationToAnnihilator_symplectizationLift {β : SmoothForm I M ℝ 1} {f : M → ℝ}
    (hf : ∀ x, 0 < f x) (hβ : ∀ x, β.val x = f x • α.val x) (p : ℝ × M) :
    β.symplectizationToAnnihilator ((kerDistribution_of_eq_smul (fun x ↦ (hf x).ne') hβ).trans hα)
        (symplectizationLift id f p) =
      α.symplectizationToAnnihilator hα p := by
  rw [symplectizationLift_apply]
  refine annihilatorInclusion_injective I ξ (Fin 1 → ℝ) ?_
  rw [annihilatorInclusion_symplectizationToAnnihilator,
    annihilatorInclusion_symplectizationToAnnihilator]
  refine CotangentBundle.ext (by simp) fun v ↦ (symplectizationToCotangent_snd_apply β _ v).trans
    (Eq.trans ?_ (symplectizationToCotangent_snd_apply α p v).symm)
  simp only [id, hβ, ContinuousAlternatingMap.smul_apply, smul_eq_mul, Real.exp_sub,
    Real.exp_log (hf p.2)]
  field_simp [(hf p.2).ne']

/-- **Change of contact form reversing the coorientation.** If `β = f α` for a negative function
`f`, the trivialization of `ξ⁰` by `β` restricts to the half of `-α`:
`κ_β(t - log(-f(x)), x) = κ_(-α)(t, x)`. -/
theorem symplectizationToAnnihilator_symplectizationLift_neg {β : SmoothForm I M ℝ 1} {f : M → ℝ}
    (hf : ∀ x, f x < 0) (hβ : ∀ x, β.val x = f x • α.val x) (p : ℝ × M) :
    β.symplectizationToAnnihilator ((kerDistribution_of_eq_smul (fun x ↦ (hf x).ne) hβ).trans hα)
        (symplectizationLift id (-f) p) =
      (-α).symplectizationToAnnihilator (kerDistribution_neg.trans hα) p :=
  symplectizationToAnnihilator_symplectizationLift (kerDistribution_neg.trans hα)
    (fun x ↦ neg_pos.2 (hf x)) (fun x ↦ by simp [hβ]) p

/-! ### Smoothness and the symplectic forms -/

section Smooth

variable [FiniteDimensional ℝ E] [Nonempty M] (hξ : IsContactDistribution I ∞ ξ)

/-- `C^(∞ + 1)` charts, needed by the annihilator bundle construction of
`TauCeti.IsContMDiffDistribution.annihilatorContMDiffVectorBundle` at smoothness `∞`. -/
local instance : IsManifold I ((∞ : WithTop ℕ∞) + 1) M := IsManifold.of_le (n := ∞) (by simp)

include hξ in
/-- The trivialization `κ_α` of the annihilator line of a contact structure `ξ = ker α` is
smooth, for the manifold structure of the annihilator bundle. -/
theorem contMDiff_symplectizationToAnnihilator :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, Fin 1 → ℝ)) ∞ (α.symplectizationToAnnihilator hα) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  fun p ↦ by
  -- The inclusion `ξ⁰ → T*M` is a smooth embedding, and its composite with `κ_α` is smooth.
  have hj := hξ.isContMDiffDistribution.isSmoothEmbedding_annihilatorInclusion (n := ∞)
    hξ.finrank_sub_one_add_one
  have hκ := α.contMDiff_symplectizationToCotangent
  rw [ContMDiffAt.iff_comp_isImmersionAt (hj.isImmersion.isImmersionAt _),
    hj.isEmbedding.isInducing.continuousAt_iff,
    annihilatorInclusion_comp_symplectizationToAnnihilator]
  exact ⟨hκ.continuous.continuousAt, hκ p⟩

/-- **The trivialization is tautological.** The trivialization `κ_α` of the annihilator line of a
contact structure `ξ = ker α` pulls the tautological one-form `θ` back to the symplectization
form `eᵗ α`. -/
@[simp]
theorem mpullback_symplectizationToAnnihilator_annihilatorLiouvilleForm :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    mpullback (α.symplectizationToAnnihilator hα)
        (contMDiff_symplectizationToAnnihilator hα hξ) hξ.annihilatorLiouvilleForm =
      α.symplectization :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  by
  -- `θ` is the pullback of the Liouville form along `ξ⁰ → T*M`, whose composite with `κ_α` is
  -- `(t, x) ↦ eᵗ α_x`.
  rw [IsContactDistribution.annihilatorLiouvilleForm_def, mpullback_mpullback]
  apply Subtype.ext
  rw [coe_mpullback, annihilatorInclusion_comp_symplectizationToAnnihilator,
    ← coe_mpullback _ α.contMDiff_symplectizationToCotangent,
    mpullback_symplectizationToCotangent_liouvilleForm]

/-- **The trivialization is symplectic.** The trivialization `κ_α` of the annihilator line of a
contact structure `ξ = ker α` pulls the symplectic form `dθ` of `ξ⁰ ∖ 0` back to the exterior
derivative `d(eᵗ α)` of the symplectization form. -/
theorem mpullback_symplectizationToAnnihilator_mextDerivₗ_annihilatorLiouvilleForm :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    mpullback (α.symplectizationToAnnihilator hα) (contMDiff_symplectizationToAnnihilator hα hξ)
        (mextDerivₗ (I.prod 𝓘(ℝ, Fin 1 → ℝ)) 1 hξ.annihilatorLiouvilleForm) =
      mextDerivₗ (𝓘(ℝ).prod I) 1 α.symplectization :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  by rw [← mextDerivₗ_mpullback, mpullback_symplectizationToAnnihilator_annihilatorLiouvilleForm]

/-- For a contact form `α` with kernel `ξ`, the trivialization `κ_α` is an immersion: its
composite with the inclusion `ξ⁰ → T*M` is the immersion `(t, x) ↦ eᵗ α_x`. -/
theorem IsContactForm.injective_mfderiv_symplectizationToAnnihilator (hαc : α.IsContactForm)
    (p : ℝ × M) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    Injective (mfderiv (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, Fin 1 → ℝ))
      (α.symplectizationToAnnihilator hα) p) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  by
  have hκ := (contMDiff_symplectizationToAnnihilator hα hξ p).mdifferentiableAt (by simp)
  have hj := (hξ.isContMDiffDistribution.contMDiff_annihilatorInclusion (n := ∞)
    hξ.finrank_sub_one_add_one (α.symplectizationToAnnihilator hα p)).mdifferentiableAt (by simp)
  have h := hαc.injective_mfderiv_symplectizationToCotangent p
  rw [← annihilatorInclusion_comp_symplectizationToAnnihilator hα, mfderiv_comp p hj hκ,
    ContinuousLinearMap.coe_comp] at h
  exact h.of_comp

/-- **The trivialization is a local diffeomorphism.** On a boundaryless manifold, the
trivialization `κ_α` of the annihilator line by a contact form `α` with kernel `ξ` is a local
diffeomorphism. Since it is injective (`TauCeti.SmoothForm.symplectizationToAnnihilator_injective`),
`IsLocalDiffeomorph.diffeomorphOfInjective` makes it a diffeomorphism from `ℝ × M` onto its open
image, the half of `ξ⁰ ∖ 0` described by
`TauCeti.SmoothForm.mem_range_symplectizationToAnnihilator_iff`. -/
theorem IsContactForm.isLocalDiffeomorph_symplectizationToAnnihilator [BoundarylessManifold I M]
    (hαc : α.IsContactForm) :
    letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
    haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle
      hξ.finrank_sub_one_add_one
    IsLocalDiffeomorph (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, Fin 1 → ℝ)) ∞
      (α.symplectizationToAnnihilator hα) :=
  letI := hξ.isContMDiffDistribution.annihilatorFiberBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorVectorBundle hξ.finrank_sub_one_add_one
  haveI := hξ.isContMDiffDistribution.annihilatorContMDiffVectorBundle hξ.finrank_sub_one_add_one
  fun p ↦ isLocalDiffeomorphAt_of_injective_mfderiv
    (contMDiff_symplectizationToAnnihilator hα hξ).contMDiffOn isOpen_univ (mem_univ p)
    BoundarylessManifold.isInteriorPoint (by simp)
    (hαc.injective_mfderiv_symplectizationToAnnihilator hα hξ p)
    (by simp [Module.finrank_prod, add_comm])

end Smooth

end SmoothForm

end TauCeti
