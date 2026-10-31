/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Constructions.SumProd

/-!
# Pushouts with closed structure maps

A square of topological spaces which is a pushout on underlying sets is a topological pushout
if its two structure maps are closed. This recognizes adjunction spaces realized as finite
unions of closed embedded pieces, without a compactness assumption on the whole union.
-/

public section

open CategoryTheory Limits Topology

namespace CategoryTheory.IsPushout

/-- A pushout of underlying sets is a topological pushout when its two structure maps are closed.
-/
theorem of_map_forget_of_isClosedMap {A B C P : TopCat}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ P} {j : C ⟶ P}
    (h : IsPushout ((forget TopCat).map f) ((forget TopCat).map g)
      ((forget TopCat).map i) ((forget TopCat).map j))
    (hi : IsClosedMap i) (hj : IsClosedMap j) : IsPushout f g i j := by
  have hw : f ≫ i = g ≫ j := by
    ext x
    exact ConcreteCategory.congr_hom h.w x
  have hsurj : Function.Surjective (Sum.elim i j) := by
    intro x
    obtain ⟨b, hb⟩ | ⟨c, hc⟩ := Types.eq_or_eq_of_isPushout h x
    · exact ⟨Sum.inl b, hb⟩
    · exact ⟨Sum.inr c, hc⟩
  have hq := (hi.sumElim hj).isQuotientMap (i.hom.continuous.sumElim j.hom.continuous) hsurj
  let d (s : PushoutCocone f g) := h.desc ((forget TopCat).map s.inl)
    ((forget TopCat).map s.inr) ((forget TopCat).congr_map s.condition)
  have hd₁ (s : PushoutCocone f g) (b : B) : d s (i b) = s.inl b :=
    ConcreteCategory.congr_hom (h.inl_desc _ _ _) b
  have hd₂ (s : PushoutCocone f g) (c : C) : d s (j c) = s.inr c :=
    ConcreteCategory.congr_hom (h.inr_desc _ _ _) c
  refine ⟨⟨hw⟩, ⟨?_⟩⟩
  refine PushoutCocone.IsColimit.mk hw (fun s ↦ TopCat.ofHom ⟨d s, ?_⟩)
    (fun s ↦ by ext b; exact hd₁ s b) (fun s ↦ by ext c; exact hd₂ s c) ?_
  · apply hq.continuous_iff.2
    convert s.inl.hom.continuous.sumElim s.inr.hom.continuous using 1
    ext (b | c)
    · exact hd₁ s b
    · exact hd₂ s c
  · intro s m hm₁ hm₂
    ext x
    obtain ⟨b | c, rfl⟩ := hsurj x
    · exact (congrArg (fun k : B ⟶ s.pt ↦ k b) hm₁).trans (hd₁ s b).symm
    · exact (congrArg (fun k : C ⟶ s.pt ↦ k c) hm₂).trans (hd₂ s c).symm

end CategoryTheory.IsPushout
