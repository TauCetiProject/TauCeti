/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.LocalHomology.System
public import TauCeti.AlgebraicTopology.Singular.MayerVietoris.Relative

/-!
# Mayer–Vietoris for local homology

For closed subsets `S` and `T` of a space `M`, the relative Mayer–Vietoris sequence of the open
sets `M ∖ S` and `M ∖ T` (`TopCat.relativeMayerVietoris_exact₁`) contains the segment
`Hₖ₊₁(M, M ∖ (S ∩ T)) ⟶ Hₖ(M, M ∖ (S ∪ T)) ⟶ Hₖ(M, M ∖ S) ⊞ Hₖ(M, M ∖ T)` of local homology
groups (`TauCeti.localHomology`).

## Main results

* `TauCeti.localHomology_hom_ext_of_union`: for closed `S` and `T` with
  `Hₖ₊₁(M, M ∖ (S ∩ T)) = 0`, maps into `Hₖ(M, M ∖ (S ∪ T))` are determined by their
  restrictions to `S` and to `T`.
* `TauCeti.exists_localHomologyRestriction_union_eq`: with coefficients in a module, classes along
  closed sets `S` and `T` with the same restriction to `S ∩ T` are the restrictions of a single
  class along `S ∪ T`.
-/

public section

noncomputable section

open CategoryTheory Limits Set

universe w v u

namespace TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] {R : A}
  {M : Type w} [TopologicalSpace M]

/-- **Maps into local homology of a union are detected on the pieces.** Let `S` and `T` be closed
and let `Hₖ₊₁(M, M ∖ (S ∩ T))` vanish. Two maps into `Hₖ(M, M ∖ (S ∪ T))` that agree after
restriction to `S` and to `T` are equal. -/
theorem localHomology_hom_ext_of_union {S T : Set M} (hS : IsClosed S) (hT : IsClosed T) {k : ℕ}
    (h : IsZero (localHomology R (S ∩ T) (k + 1))) {Z : A}
    {f g : Z ⟶ localHomology R (S ∪ T) k}
    (hfS : f ≫ localHomologyRestriction R subset_union_left k =
      g ≫ localHomologyRestriction R subset_union_left k)
    (hfT : f ≫ localHomologyRestriction R subset_union_right k =
      g ≫ localHomologyRestriction R subset_union_right k) :
    f = g := by
  have h' : IsZero ((TopPair.ofSubset (Sᶜ ∪ Tᶜ : Set (TopCat.of M))).singularHomology R
      (k + 1)) := by
    rw [← compl_inter]
    exact h
  have : Mono (TopCat.relativeMayerVietorisToBiprod R (X := TopCat.of M) Sᶜ Tᶜ k) :=
    (TopCat.relativeMayerVietoris_exact₁ R hS.isOpen_compl hT.isOpen_compl (k + 1) k).mono_g
      (h'.eq_of_src _ _)
  rw [localHomologyRestriction_def] at hfS hfT
  -- The sequence is stated for `(M ∖ S) ∩ (M ∖ T)`, which is `M ∖ (S ∪ T)` only propositionally,
  -- so generalize the subspace before comparing with the first map of the sequence.
  suffices key : ∀ (W : Set (TopCat.of M)) (_ : W = Sᶜ ∩ Tᶜ) (hWS : W ⊆ Sᶜ) (hWT : W ⊆ Tᶜ)
      (f g : Z ⟶ (TopPair.ofSubset W).singularHomology R k),
      f ≫ TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) hWS) R k =
          g ≫ TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) hWS) R k →
        f ≫ TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) hWT) R k =
          g ≫ TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 _) hWT) R k → f = g from
    key _ (compl_union S T) _ _ f g hfS hfT
  rintro W rfl hWS hWT f g hS hT
  rw [← cancel_mono (TopCat.relativeMayerVietorisToBiprod R (X := TopCat.of M) Sᶜ Tᶜ k)]
  ext
  · simpa using hS
  · simpa using hT

section Module

variable {Λ : Type w} [Ring Λ] (N : ModuleCat.{w} Λ)

/-- **Local homology classes on two closed sets glue.** Let `S` and `T` be closed. Classes of
`Hₖ(M, M ∖ S)` and `Hₖ(M, M ∖ T)` with the same restriction to `S ∩ T` are the restrictions of a
single class of `Hₖ(M, M ∖ (S ∪ T))`. This is exactness of the relative Mayer–Vietoris sequence
at `Hₖ(M, M ∖ S) ⊞ Hₖ(M, M ∖ T)`. -/
theorem exists_localHomologyRestriction_union_eq {S T : Set M} (hS : IsClosed S)
    (hT : IsClosed T) {k : ℕ} (α : (localHomology N S k : ModuleCat.{w} Λ))
    (β : (localHomology N T k : ModuleCat.{w} Λ))
    (h : localHomologyRestriction N inter_subset_left k α =
      localHomologyRestriction N inter_subset_right k β) :
    ∃ γ : (localHomology N (S ∪ T) k : ModuleCat.{w} Λ),
      localHomologyRestriction N subset_union_left k γ = α ∧
        localHomologyRestriction N subset_union_right k γ = β := by
  have hex := TopCat.relativeMayerVietoris_exact₂ N (X := TopCat.of M) hS.isOpen_compl
    hT.isOpen_compl k
  rw [ShortComplex.moduleCat_exact_iff] at hex
  simp only [localHomologyRestriction_def] at h ⊢
  -- As in `TauCeti.localHomology_hom_ext_of_union`, the sequence is stated for `Sᶜ ∩ Tᶜ` and
  -- `Sᶜ ∪ Tᶜ`, which are `(S ∪ T)ᶜ` and `(S ∩ T)ᶜ` only propositionally, so generalize them.
  suffices key : ∀ (W₁ W₂ : Set (TopCat.of M)) (_ : W₁ = Sᶜ ∩ Tᶜ) (_ : W₂ = Sᶜ ∪ Tᶜ)
      (hW₁S : W₁ ⊆ Sᶜ) (hW₁T : W₁ ⊆ Tᶜ) (hSW₂ : Sᶜ ⊆ W₂) (hTW₂ : Tᶜ ⊆ W₂),
      TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) hSW₂) N k α =
          TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) hTW₂) N k β →
        ∃ γ : ((TopPair.ofSubset W₁).singularHomology N k : ModuleCat.{w} Λ),
          TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) hW₁S) N k γ = α ∧
            TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of M)) hW₁T) N k γ = β from
    key _ _ (compl_union S T) (compl_inter S T) _ _ _ _ h
  rintro W₁ W₂ rfl rfl hW₁S hW₁T hSW₂ hTW₂ h
  let HS := (TopPair.ofSubset (Sᶜ : Set (TopCat.of M))).singularHomology N k
  let HT := (TopPair.ofSubset (Tᶜ : Set (TopCat.of M))).singularHomology N k
  obtain ⟨γ, hγ⟩ := hex ((biprod.inl : HS ⟶ HS ⊞ HT) α - (biprod.inr : HT ⟶ HS ⊞ HT) β) (by
    simp [HS, HT, ← ConcreteCategory.comp_apply, TopCat.inl_relativeMayerVietorisFromBiprod,
      TopCat.inr_relativeMayerVietorisFromBiprod, h])
  refine ⟨γ, ?_, ?_⟩
  · simpa [HS, HT, ← ConcreteCategory.comp_apply] using congrArg (biprod.fst : HS ⊞ HT ⟶ HS) hγ
  · simpa [HS, HT, ← ConcreteCategory.comp_apply] using congrArg (biprod.snd : HS ⊞ HT ⟶ HT) hγ

end Module

end TauCeti
