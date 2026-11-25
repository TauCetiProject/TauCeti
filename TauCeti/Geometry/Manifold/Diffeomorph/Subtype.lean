/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Basic

/-!
# Restricting a diffeomorphism to embedded submanifolds

Let `F : M → N` be a `C^n` diffeomorphism, and let `s ⊆ M` and `t ⊆ N` carry manifold structures
for which the inclusions `s → M` and `t → N` are `C^n` smooth embeddings. If `F` maps `s` onto `t`,
in the sense that `x ∈ s ↔ F x ∈ t` for every `x`, then `F` restricts to a `C^n` diffeomorphism
`s → t` (`Diffeomorph.subtypeOfIsSmoothEmbedding`), the analogue of Mathlib's
`Homeomorph.subtype`. For open subsets carrying the restricted charts this is
`Diffeomorph.subtype`. Both the restriction and its inverse are smooth because a map into a
smoothly embedded manifold is smooth exactly when its composite with the embedding is
(`Manifold.IsSmoothEmbedding.contMDiff_iff_comp`).

The restriction is compatible with forms: if `F` pulls a smooth form `τ` back to `σ`, then the
restriction pulls the restriction of `τ` to `t` back to the restriction of `σ` to `s`
(`Diffeomorph.mpullback_subtypeOfIsSmoothEmbedding_mpullback_subtype_val`). This is how
restricted forms on embedded submanifolds, such as the symplectic forms on the parts `M^K_d` of the
fixed locus of a group action, are transported along diffeomorphisms.

## Main definitions

* `Diffeomorph.subtypeOfIsSmoothEmbedding F hs ht h`: the restriction of `F` to a diffeomorphism
  `s ≃ t`.

## Main results

* `Diffeomorph.subtypeOfIsSmoothEmbedding_apply_coe`,
  `Diffeomorph.subtypeOfIsSmoothEmbedding_symm_apply_coe`: the restriction and its inverse act as
  `F` and `F.symm`.
* `Diffeomorph.mpullback_subtypeOfIsSmoothEmbedding_mpullback_subtype_val`: the restriction
  transports restricted forms.
-/

public section

open Manifold
open scoped Manifold ContDiff

noncomputable section

namespace Diffeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F₀ G}
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners ℝ F₁ G'}
  {n : WithTop ℕ∞} {s : Set M} {t : Set N} [ChartedSpace G s] [ChartedSpace G' t]

/-- The restriction of a `C^n` diffeomorphism `F : M → N` to a `C^n` diffeomorphism between
smoothly embedded subsets `s ⊆ M` and `t ⊆ N`, when `F` maps `s` onto `t`. -/
def subtypeOfIsSmoothEmbedding (F : M ≃ₘ^n⟮I, I'⟯ N)
    (hs : IsSmoothEmbedding J I n (Subtype.val : s → M))
    (ht : IsSmoothEmbedding J' I' n (Subtype.val : t → N)) (h : ∀ x, x ∈ s ↔ F x ∈ t) :
    s ≃ₘ^n⟮J, J'⟯ t where
  toEquiv := F.toEquiv.subtypeEquiv h
  contMDiff_toFun := ht.contMDiff_iff_comp.2 (F.contMDiff.comp hs.contMDiff)
  contMDiff_invFun := hs.contMDiff_iff_comp.2 (F.symm.contMDiff.comp ht.contMDiff)

variable (F : M ≃ₘ^n⟮I, I'⟯ N) (hs : IsSmoothEmbedding J I n (Subtype.val : s → M))
  (ht : IsSmoothEmbedding J' I' n (Subtype.val : t → N)) (h : ∀ x, x ∈ s ↔ F x ∈ t)

/-- The restriction evaluates as the diffeomorphism. -/
@[simp]
theorem subtypeOfIsSmoothEmbedding_apply_coe (x : s) :
    (F.subtypeOfIsSmoothEmbedding hs ht h x : N) = F x :=
  (rfl)

/-- The inverse of the restriction evaluates as the inverse diffeomorphism. -/
@[simp]
theorem subtypeOfIsSmoothEmbedding_symm_apply_coe (y : t) :
    ((F.subtypeOfIsSmoothEmbedding hs ht h).symm y : M) = F.symm y :=
  (rfl)

/-- The restriction is `F` read through the inclusions: `ι_t ∘ F|_s = F ∘ ι_s`. -/
theorem subtype_val_comp_subtypeOfIsSmoothEmbedding :
    Subtype.val ∘ F.subtypeOfIsSmoothEmbedding hs ht h = F ∘ Subtype.val :=
  (rfl)

end Diffeomorph

namespace Diffeomorph

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
  {F₀ : Type*} [NormedAddCommGroup F₀] [NormedSpace ℝ F₀]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F₀ G}
  {F₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  {G' : Type*} [TopologicalSpace G'] {J' : ModelWithCorners ℝ F₁ G'}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {k : ℕ}
  {s : Set M} {t : Set N} [ChartedSpace G s] [ChartedSpace G' t]
  [IsManifold J ∞ s] [IsManifold J' ∞ t]

/-- **Restricted diffeomorphisms transport restricted forms.** If a diffeomorphism `F` maps the
embedded submanifold `s` onto the embedded submanifold `t` and pulls the smooth form `τ` back to
`σ`, then its restriction `s → t` pulls the restriction of `τ` to `t` back to the restriction of
`σ` to `s`. -/
theorem mpullback_subtypeOfIsSmoothEmbedding_mpullback_subtype_val (F : M ≃ₘ⟮I, I'⟯ N)
    (hs : IsSmoothEmbedding J I ∞ (Subtype.val : s → M))
    (ht : IsSmoothEmbedding J' I' ∞ (Subtype.val : t → N)) (h : ∀ x, x ∈ s ↔ F x ∈ t)
    {σ : SmoothForm I M V k} {τ : SmoothForm I' N V k}
    (hFσ : SmoothForm.mpullback F F.contMDiff τ = σ) :
    SmoothForm.mpullback (F.subtypeOfIsSmoothEmbedding hs ht h)
        (F.subtypeOfIsSmoothEmbedding hs ht h).contMDiff
        (SmoothForm.mpullback Subtype.val ht.contMDiff τ) =
      SmoothForm.mpullback Subtype.val hs.contMDiff σ := by
  rw [← hFσ]
  exact SmoothForm.mpullback_mpullback_of_comp_eq _ _ _ _
    (F.subtype_val_comp_subtypeOfIsSmoothEmbedding hs ht h) τ

end Diffeomorph
