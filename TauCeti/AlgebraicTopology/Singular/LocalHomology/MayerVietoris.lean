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

end TauCeti
