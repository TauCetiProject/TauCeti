/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.Topology.Category.TopCat.Limits.Products

import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Closed embeddings in `TopCat`

This file introduces the class `TopCat.isClosedEmbedding` of morphisms of topological spaces that
are closed embeddings, and proves the closure properties that make it usable in cell
attachments: it contains the identities and isomorphisms, is stable under composition, cobase
change (pushouts), coproducts, and transfinite composition.

The key topological input is `TopCat.isClosedEmbedding_ι_of_isColimit`: in a filtered colimit of
spaces along closed embeddings, each space is a closed subspace of the colimit. Together with the
cobase-change and coproduct statements it shows that any relative cell complex in `TopCat` whose
basic cells are closed embeddings is itself a closed embedding.

## Main declarations

* `TopCat.isClosedEmbedding`: the morphism property of being a closed embedding.
* `TopCat.isClosedEmbedding_ι_of_isColimit`: filtered colimits along closed embeddings.
* `TopCat.isClosedEmbedding_map_of_isWellOrderContinuous`: in a well-order-continuous diagram
  whose successor maps are closed embeddings, every transition map is a closed embedding.
-/

public section

open CategoryTheory Limits MorphismProperty Topology

universe w v u

namespace TopCat

/-- The `MorphismProperty` in `TopCat` of a morphism being a closed embedding. -/
abbrev isClosedEmbedding : MorphismProperty TopCat.{u} :=
  fun ⦃_ _ : TopCat⦄ f ↦ IsClosedEmbedding f.hom

@[simp]
lemma isClosedEmbedding_iff ⦃X Y : TopCat.{u}⦄ (f : X ⟶ Y) :
    isClosedEmbedding f ↔ IsClosedEmbedding f.hom :=
  .rfl

instance : isClosedEmbedding.{u}.IsMultiplicative where
  id_mem _ := IsClosedEmbedding.id
  comp_mem _ _ hf hg := hg.comp hf

instance : isClosedEmbedding.{u}.RespectsIso :=
  respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) ↦
    (homeoOfIso (asIso f)).isClosedEmbedding

/-- In a filtered colimit of topological spaces along closed embeddings, each colimit injection
is a closed embedding. -/
lemma isClosedEmbedding_ι_of_isColimit {J : Type w} [Category.{v} J] [IsFiltered J]
    {F : J ⥤ TopCat.{u}} (hF : ∀ ⦃i j : J⦄ (g : i ⟶ j), IsClosedEmbedding (F.map g))
    {c : Cocone F} (hc : IsColimit c) (j : J) : IsClosedEmbedding (c.ι.app j) := by
  have hc' : IsColimit ((forget TopCat).mapCocone c) := isColimitOfPreserves _ hc
  have hinj (k : J) : Function.Injective (c.ι.app k) := fun x y hxy ↦ by
    obtain ⟨l, g, hg⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' x y).1 hxy
    exact (hF g).injective hg
  refine .of_continuous_injective_isClosedMap (c.ι.app j).hom.continuous (hinj j)
    fun C hC ↦ (isClosed_iff_of_isColimit _ hc _).2 fun i ↦ ?_
  -- Over a common upper bound `k` of `i` and `j`, the preimage of `c.ι.app j '' C` in `F.obj i`
  -- is the preimage of the closed set `F.map b '' C` under `F.map a`.
  let a := IsFiltered.leftToMax i j
  let b := IsFiltered.rightToMax i j
  have key : c.ι.app i ⁻¹' (c.ι.app j '' C) = F.map a ⁻¹' (F.map b '' C) := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image]
    refine exists_congr fun x ↦ and_congr_right fun _ ↦ ?_
    rw [← c.w a, ← c.w b]
    exact (hinj _).eq_iff
  rw [key]
  exact ((hF b).isClosedMap C hC).preimage (F.map a).hom.continuous

/-- A subset of a pushout of topological spaces is closed if and only if its preimages in the
two spaces being glued are closed. -/
lemma isClosed_iff_of_isPushout {A A' B B' : TopCat.{u}} {f : A ⟶ A'} {g : A ⟶ B}
    {f' : B ⟶ B'} {g' : A' ⟶ B'} (sq : IsPushout g f f' g') (s : Set B') :
    IsClosed s ↔ IsClosed (f'.hom ⁻¹' s) ∧ IsClosed (g'.hom ⁻¹' s) := by
  refine (isClosed_iff_of_isColimit _ sq.isColimit s).trans
    ⟨fun h ↦ ⟨h WalkingSpan.left, h WalkingSpan.right⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  rintro (_ | _ | _)
  · exact h₁.preimage g.hom.continuous
  · exact h₁
  · exact h₂

instance : isClosedEmbedding.{u}.IsStableUnderCobaseChange where
  of_isPushout {A A' B B'} {f g f' g'} sq hf := by
    have sq' := (sq.map (forget TopCat)).flip
    have hinj : Function.Injective f'.hom :=
      Types.pushoutCocone_inr_injective_of_isColimit sq'.isColimit hf.injective
    refine .of_continuous_injective_isClosedMap f'.hom.continuous hinj
      fun C hC ↦ (isClosed_iff_of_isPushout sq _).2 ⟨?_, ?_⟩
    · rw [hinj.preimage_image]
      exact hC
    -- A point of `A'` lands in `f' '' C` exactly when it comes from `g ⁻¹' C` along `f`.
    have hA' : g'.hom ⁻¹' (f'.hom '' C) = f.hom '' (g.hom ⁻¹' C) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨x, hx, hxy⟩
        obtain ⟨s, rfl, rfl⟩ :=
          (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit sq'.isColimit hf.injective y x).1
            hxy.symm
        exact ⟨s, hx, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨g s, hs, congr($(sq.w) s)⟩
    rw [hA']
    exact hf.isClosedMap _ (hC.preimage g.hom.continuous)

instance (J : Type u) : isClosedEmbedding.{u}.IsStableUnderCoproductsOfShape J := by
  refine IsStableUnderCoproductsOfShape.mk _ J fun X₁ X₂ _ _ f hf ↦ ?_
  let φ : TopCat.of (Σ j, X₁ j) ⟶ TopCat.of (Σ j, X₂ j) :=
    ofHom ⟨Sigma.map id fun j ↦ f j, by fun_prop⟩
  refine (isClosedEmbedding.arrow_mk_iso_iff
    (Arrow.isoMk (g := Arrow.mk φ) (sigmaIsoSigma X₁) (sigmaIsoSigma X₂) ?_)).2 ?_
  · refine Sigma.hom_ext _ _ fun j ↦ ?_
    ext x
    simp [φ, Sigma.map]
  · have hφ : IsClosedEmbedding (Sigma.map id fun j ↦ f j : (Σ j, X₁ j) → Σ j, X₂ j) := by
      refine ⟨(isEmbedding_sigmaMap Function.injective_id).2 fun j ↦ (hf j).isEmbedding,
        isClosed_sigma_iff.2 fun j ↦ ?_⟩
      convert (hf j).isClosed_range using 1
      ext x
      simp [Sigma.map]
    exact hφ

instance : IsStableUnderCoproducts.{u} isClosedEmbedding.{u} where

section TransfiniteComposition

variable {J : Type w} [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]

/-- In a well-order-continuous diagram of topological spaces whose successor maps are closed
embeddings, every transition map is a closed embedding. -/
lemma isClosedEmbedding_map_of_isWellOrderContinuous (F : J ⥤ TopCat.{u})
    [F.IsWellOrderContinuous]
    (hF : ∀ j, ¬ IsMax j → IsClosedEmbedding (F.map (homOfLE (Order.le_succ j))))
    {i j : J} (hij : i ≤ j) : IsClosedEmbedding (F.map (homOfLE hij)) := by
  induction j using SuccOrder.limitRecOn generalizing i with
  | isMin j hj =>
    obtain rfl := le_antisymm hij (hj.eq_bot ▸ bot_le)
    simpa using IsClosedEmbedding.id
  | succ j hj ih =>
    obtain hij | rfl := hij.lt_or_eq
    · have hij' := Order.le_of_lt_succ hij
      rw [← homOfLE_comp hij' (Order.le_succ j), F.map_comp]
      exact (hF j hj).comp (ih hij')
    · simpa using IsClosedEmbedding.id
  | isSuccLimit j hj ih =>
    obtain hij | rfl := hij.lt_or_eq
    · have : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
      refine isClosedEmbedding_ι_of_isColimit ?_ (F.isColimitOfIsWellOrderContinuous j hj) ⟨i, hij⟩
      exact fun a b g ↦ ih b b.2 (leOfHom g)
    · simpa using IsClosedEmbedding.id

instance : isClosedEmbedding.{u}.IsStableUnderTransfiniteCompositionOfShape J where
  le := by
    rintro X Y f ⟨hf⟩
    rw [← hf.fac]
    have : Nonempty J := ⟨⊥⟩
    exact isClosedEmbedding.comp_mem _ _ (isClosedEmbedding.of_isIso _)
      (isClosedEmbedding_ι_of_isColimit
        (fun _ _ g ↦ isClosedEmbedding_map_of_isWellOrderContinuous hf.F
          (fun j hj ↦ hf.map_mem j hj) (leOfHom g)) hf.isColimit ⊥)

end TransfiniteComposition

instance : IsStableUnderTransfiniteComposition.{w} isClosedEmbedding.{u} where

end TopCat
