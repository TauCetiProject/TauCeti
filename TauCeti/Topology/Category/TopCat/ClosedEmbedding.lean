/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.WellOrderContinuous
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition
public import Mathlib.Topology.Category.TopCat.Limits.Basic

/-!
# Closed embeddings in `TopCat`

This file introduces the morphism property `TauCeti.TopCat.isClosedEmbedding` of `TopCat`, the
closed embeddings, and proves that it is stable under the operations used to build relative cell
complexes:

* cobase change: in a pushout square, the map opposite to a closed embedding is a closed
  embedding (`TauCeti.TopCat.isClosedEmbedding_of_isPushout`);
* coproducts: a coproduct of closed embeddings is a closed embedding
  (`TauCeti.TopCat.isClosedEmbedding_sigmaMap`);
* transfinite composition: if every successor map of a well-order-continuous diagram is a closed
  embedding, then so is every transition map
  (`TauCeti.TopCat.isClosedEmbedding_map_of_isWellOrderContinuous`) and every map to its colimit
  (`TauCeti.TopCat.isClosedEmbedding_incl_app_of_transfiniteCompositionOfShape`).

The last point comes from a statement about directed colimits: if all transition maps of a
directed diagram are closed embeddings, so are the maps to its colimit
(`TauCeti.TopCat.isClosedEmbedding_ι_of_isColimit`).

With Mathlib's description of a relative cell complex as a transfinite composition of pushouts of
coproducts of its basic cells, these stability properties show that a relative cell complex in
`TopCat` whose basic cells are closed embeddings is a closed embedding; see
`TauCeti.Topology.CWComplex.Abstract.ClosedEmbedding`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix, on the topology of cell complexes.
-/

public section

open CategoryTheory Limits MorphismProperty Topology

universe w u

namespace TauCeti.TopCat

/-- The closed embeddings, as a class of morphisms of `TopCat`. -/
def isClosedEmbedding : MorphismProperty TopCat.{u} := fun _ _ f ↦ IsClosedEmbedding f

@[simp]
theorem isClosedEmbedding_iff {X Y : TopCat.{u}} (f : X ⟶ Y) :
    isClosedEmbedding f ↔ IsClosedEmbedding f := Iff.rfl

instance : isClosedEmbedding.{u}.IsMultiplicative where
  id_mem _ := IsClosedEmbedding.id
  comp_mem _ _ hf hg := hg.comp hf

instance : isClosedEmbedding.{u}.RespectsIso :=
  respectsIso_of_isStableUnderComposition fun _ _ f (_ : IsIso f) ↦
    (TopCat.homeoOfIso (asIso f)).isClosedEmbedding

section Pushout

variable {A A' B B' : TopCat.{u}} {f : A ⟶ A'} {g : A ⟶ B} {f' : B ⟶ B'} {g' : A' ⟶ B'}

/-- A subset of the corner of a pushout square in `TopCat` is closed if and only if its preimages
under the two maps into the corner are closed. -/
theorem isClosed_iff_of_isPushout (sq : IsPushout g f f' g') (s : Set B') :
    IsClosed s ↔ IsClosed (f' ⁻¹' s) ∧ IsClosed (g' ⁻¹' s) := by
  refine ⟨fun hs ↦ ⟨hs.preimage f'.hom.continuous, hs.preimage g'.hom.continuous⟩,
    fun ⟨h₁, h₂⟩ ↦ (TopCat.isClosed_iff_of_isColimit _ sq.isColimit s).2 ?_⟩
  rintro (_ | _ | _)
  · exact h₁.preimage g.hom.continuous
  · exact h₁
  · exact h₂

/-- In `TopCat`, the cobase change of a closed embedding is a closed embedding: in a pushout
square, the map opposite to a closed embedding is a closed embedding. -/
theorem isClosedEmbedding_of_isPushout (sq : IsPushout g f f' g') (hf : IsClosedEmbedding f) :
    IsClosedEmbedding f' := by
  have sq' := (forget TopCat).map_isPushout sq.flip
  have hinj : Function.Injective f' :=
    Types.pushoutCocone_inr_injective_of_isColimit sq'.isColimit hf.injective
  refine .of_continuous_injective_isClosedMap f'.hom.continuous hinj fun Z hZ ↦ ?_
  have hpre : g' ⁻¹' (f' '' Z) = f '' (g ⁻¹' Z) := by
    ext a'
    constructor
    · rintro ⟨b, hb, hba⟩
      obtain ⟨a, rfl, rfl⟩ :=
        (Types.pushoutCocone_inl_eq_inr_iff_of_isColimit sq'.isColimit hf.injective a' b).1
          hba.symm
      exact ⟨a, hb, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨g a, ha, by rw [← ConcreteCategory.comp_apply, sq.w, ConcreteCategory.comp_apply]⟩
  rw [isClosed_iff_of_isPushout sq, hinj.preimage_image, hpre]
  exact ⟨hZ, hf.isClosedMap _ (hZ.preimage g.hom.continuous)⟩

instance : isClosedEmbedding.{u}.IsStableUnderCobaseChange where
  of_isPushout sq hf := isClosedEmbedding_of_isPushout sq hf

end Pushout

section Coproduct

/-- In `TopCat`, a coproduct of closed embeddings is a closed embedding. -/
theorem isClosedEmbedding_sigmaMap {ι : Type w} {X₁ X₂ : ι → TopCat.{u}} [HasCoproduct X₁]
    [HasCoproduct X₂] (f : ∀ i, X₁ i ⟶ X₂ i) (hf : ∀ i, IsClosedEmbedding (f i)) :
    IsClosedEmbedding (Limits.Sigma.map f) := by
  have h₁ := isColimitOfHasCoproductOfPreservesColimit (forget TopCat) X₁
  have h₂ := isColimitOfHasCoproductOfPreservesColimit (forget TopCat) X₂
  have hmap (i : ι) (x : X₁ i) : Limits.Sigma.map f (Sigma.ι X₁ i x) = Sigma.ι X₂ i (f i x) := by
    rw [← ConcreteCategory.comp_apply, Sigma.ι_map, ConcreteCategory.comp_apply]
  refine .of_continuous_injective_isClosedMap (Limits.Sigma.map f).hom.continuous ?_ fun Z hZ ↦ ?_
  · intro z z' h
    obtain ⟨i, x, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit h₁ z
    obtain ⟨j, y, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit h₁ z'
    obtain ⟨rfl, h⟩ := (Cofan.inj_apply_eq_iff_of_isColimit h₂ _ _).1 (by simpa [hmap] using h)
    rw [(hf i).injective h]
  · rw [TopCat.isClosed_iff_of_isColimit _ (coproductIsCoproduct X₂)]
    rintro ⟨i⟩
    have hpre : Sigma.ι X₂ i ⁻¹' (Limits.Sigma.map f '' Z) = f i '' (Sigma.ι X₁ i ⁻¹' Z) := by
      ext y
      constructor
      · rintro ⟨z, hz, hzy⟩
        obtain ⟨j, x, rfl⟩ := Cofan.inj_jointly_surjective_of_isColimit h₁ z
        obtain ⟨rfl, hx⟩ := (Cofan.inj_apply_eq_iff_of_isColimit h₂ _ _).1
          ((hmap j x).symm.trans hzy)
        exact ⟨x, hz, hx.symm⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨_, hx, hmap i x⟩
    simpa [hpre] using (hf i).isClosedMap _ (hZ.preimage (Sigma.ι X₁ i).hom.continuous)

instance (J : Type w) : isClosedEmbedding.{u}.IsStableUnderCoproductsOfShape J :=
  IsStableUnderCoproductsOfShape.mk _ J fun _ _ _ _ f hf ↦ isClosedEmbedding_sigmaMap f hf

instance : IsStableUnderCoproducts.{w} isClosedEmbedding.{u} where

end Coproduct

section TransfiniteComposition

/-- If all transition maps of a directed diagram in `TopCat` are closed embeddings, then so are
the maps from the objects of the diagram to its colimit. -/
theorem isClosedEmbedding_ι_of_isColimit {J : Type w} [Preorder J] [IsDirectedOrder J]
    {F : J ⥤ TopCat.{u}}
    (hF : ∀ ⦃i j : J⦄ (hij : i ≤ j), IsClosedEmbedding (F.map (homOfLE hij)))
    {c : Cocone F} (hc : IsColimit c) (i : J) : IsClosedEmbedding (c.ι.app i) := by
  have : Nonempty J := ⟨i⟩
  have hc' := isColimitOfPreserves (forget TopCat) hc
  have hinj (j : J) : Function.Injective (c.ι.app j) := fun x y h ↦ by
    obtain ⟨k, g, hk⟩ := (Types.FilteredColimit.isColimit_eq_iff' hc' x y).1 h
    exact (hF (leOfHom g)).injective hk
  refine .of_continuous_injective_isClosedMap (c.ι.app i).hom.continuous (hinj i) fun Z hZ ↦ ?_
  rw [TopCat.isClosed_iff_of_isColimit _ hc]
  intro k
  obtain ⟨m, him, hkm⟩ := exists_ge_ge i k
  have hpre : c.ι.app k ⁻¹' (c.ι.app i '' Z) =
      F.map (homOfLE hkm) ⁻¹' (F.map (homOfLE him) '' Z) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_image, ← c.w (homOfLE him), ← c.w (homOfLE hkm),
      ConcreteCategory.comp_apply, (hinj m).eq_iff]
  rw [hpre]
  exact ((hF him).isClosedMap _ hZ).preimage (F.map _).hom.continuous

variable {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]

omit [OrderBot J] in
/-- If every successor map of a well-order-continuous diagram in `TopCat` is a closed embedding,
then so is every transition map. -/
theorem isClosedEmbedding_map_of_isWellOrderContinuous (F : J ⥤ TopCat.{u})
    [F.IsWellOrderContinuous]
    (hF : ∀ j : J, ¬IsMax j → IsClosedEmbedding (F.map (homOfLE (Order.le_succ j))))
    {i j : J} (hij : i ≤ j) : IsClosedEmbedding (F.map (homOfLE hij)) := by
  induction j using SuccOrder.limitRecOn generalizing i with
  | isMin j hj =>
    obtain rfl := le_antisymm hij (hj hij)
    simpa using IsClosedEmbedding.id
  | succ j hj ih =>
    by_cases hij' : i ≤ j
    · rw [← homOfLE_comp hij' (Order.le_succ j), F.map_comp]
      exact (hF j hj).comp (ih hij')
    · obtain rfl := le_antisymm hij (Order.succ_le_of_lt (not_le.1 hij'))
      simpa using IsClosedEmbedding.id
  | isSuccLimit j hj ih =>
    obtain hij | rfl := hij.lt_or_eq
    · exact isClosedEmbedding_ι_of_isColimit (fun a b hab ↦ ih b.1 b.2 _)
        (F.isColimitOfIsWellOrderContinuous j hj) ⟨i, hij⟩
    · simpa using IsClosedEmbedding.id

/-- A transfinite composition of closed embeddings in `TopCat` is a closed embedding, and so is
the map from each stage to the composite. -/
theorem isClosedEmbedding_incl_app_of_transfiniteCompositionOfShape {X Y : TopCat.{u}}
    {f : X ⟶ Y} (h : isClosedEmbedding.TransfiniteCompositionOfShape J f) (j : J) :
    IsClosedEmbedding (h.incl.app j) := by
  have := h.isWellOrderContinuous
  exact isClosedEmbedding_ι_of_isColimit
    (fun _ _ ↦ isClosedEmbedding_map_of_isWellOrderContinuous h.F h.map_mem) h.isColimit j

instance : isClosedEmbedding.{u}.IsStableUnderTransfiniteComposition.{w} where
  isStableUnderTransfiniteCompositionOfShape J _ _ _ _ := ⟨fun _ _ f ⟨h⟩ ↦ by
    rw [← h.fac]
    exact (isClosedEmbedding_incl_app_of_transfiniteCompositionOfShape h ⊥).comp
      (TopCat.homeoOfIso h.isoBot.symm).isClosedEmbedding⟩

end TransfiniteComposition

end TauCeti.TopCat
