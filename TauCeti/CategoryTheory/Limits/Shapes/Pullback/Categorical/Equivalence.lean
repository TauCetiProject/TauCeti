/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# Categorical pullbacks along an equivalence

For functors `F : A ⥤ B` and `G : C ⥤ B`, the categorical pullback `F ⊡ G` has as objects the
triples `(a, c, F a ≅ G c)`. The second projection `CategoricalPullback.π₂ F G : F ⊡ G ⥤ C`
inherits faithfulness, fullness and essential surjectivity from `F`: a morphism of `C` lifts
through the structural isomorphisms, and an object `c` of `C` lifts by choosing `a` with
`F a ≅ G c`. In particular, when `F` is an equivalence so is `π₂ F G`. This is the stability of
equivalences under pullback in the (2,1)-category of categories.

The explicit form `CategoricalPullback.sndEquiv` transports extra structure along an
equivalence: when `e : A ≌ B` identifies objects of `A` with objects of `B`, the category of
objects of `A` whose image in `B` is equipped with a lift along `G` is equivalent to `C`.

## Main declarations

* `CategoryTheory.Limits.CategoricalPullback.sndEquiv`: for `e : A ≌ B` and `G : C ⥤ B`, the
  equivalence `C ≌ e.functor ⊡ G` whose inverse is the second projection, with identity unit and
  with counit built from the structural isomorphism and the unit of `e`;
* `CategoryTheory.Limits.CategoricalPullback.faithful_π₂`,
  `CategoryTheory.Limits.CategoricalPullback.full_π₂`,
  `CategoryTheory.Limits.CategoricalPullback.essSurj_π₂`: the second projection out of `F ⊡ G` is
  faithful, full, or essentially surjective whenever `F` is;
* `CategoryTheory.Limits.CategoricalPullback.isEquivalence_π₂`: the second projection out of
  the categorical pullback of an equivalence is an equivalence.

## References

* [Kerodon, Tag 032Y](https://kerodon.net/tag/032Y) (categorical pullbacks).
-/

public section

namespace CategoryTheory.Limits.CategoricalPullback

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]

/-- The categorical pullback of an equivalence `e : A ≌ B` along `G : C ⥤ B` is equivalent to
`C`. The functor sends `c` to `(e.inverse (G c), c)` with the counit of `e` as structural
isomorphism, the inverse is the second projection `π₂`, the unit is the identity, and the counit
at `(a, c, φ)` is `e.inverse (G c) ≅ e.inverse (e.functor a) ≅ a`, built from `φ` and the unit
of `e`. -/
-- The body is exposed: the type of the structural isomorphism of an object in the image depends
-- on its components, so stating its characteristic equation requires unfolding the functor.
@[expose, simps! functor_obj_fst functor_obj_snd functor_obj_iso functor_map_fst functor_map_snd
  inverse_obj inverse_map unitIso_hom_app unitIso_inv_app counitIso_hom_app_fst
  counitIso_hom_app_snd counitIso_inv_app_fst counitIso_inv_app_snd]
def sndEquiv (e : A ≌ B) (G : C ⥤ B) : C ≌ e.functor ⊡ G where
  functor :=
    { obj c := ⟨e.inverse.obj (G.obj c), c, e.counitIso.app (G.obj c)⟩
      map f := ⟨e.inverse.map (G.map f), f, by simp⟩ }
  -- This is `π₂ e.functor G` (`sndEquiv_inverse`). Writing the projection out keeps the
  -- objects of the counit below in the form `x.snd`, which `simp` can work with.
  inverse :=
    { obj x := x.snd
      map f := f.snd }
  unitIso := Iso.refl _
  counitIso := NatIso.ofComponents
    (fun x ↦ mkIso (e.inverse.mapIso x.iso.symm ≪≫ e.unitIso.symm.app x.fst) (Iso.refl _)
      (by simp [Equivalence.fun_inv_map]))
    (fun _ ↦ by ext <;> simp [← Functor.map_comp_assoc])
  functor_unitIso_comp _ := by ext <;> simp

/-- The inverse of `sndEquiv e G` is the second projection. -/
lemma sndEquiv_inverse (e : A ≌ B) (G : C ⥤ B) : (sndEquiv e G).inverse = π₂ e.functor G :=
  rfl

variable (F : A ⥤ B) (G : C ⥤ B)

/-- The second projection out of the categorical pullback of a faithful functor is faithful: the
first component of a morphism is determined by the second through the structural
isomorphisms. -/
instance faithful_π₂ [F.Faithful] : (π₂ F G).Faithful where
  map_injective {x y} f g h := by
    rw [π₂_map, π₂_map] at h
    ext
    · exact F.map_injective (by rw [← cancel_mono y.iso.hom, f.w, g.w, h])
    · exact h

/-- The second projection out of the categorical pullback of a full functor is full: a morphism
`g : x.snd ⟶ y.snd` lifts with first component a preimage of `G.map g` conjugated by the
structural isomorphisms. -/
instance full_π₂ [F.Full] : (π₂ F G).Full where
  -- `(π₂ F G).obj x` is `x.snd` (`π₂_obj`); stating it lets `simp` cancel the structural
  -- isomorphisms in the compatibility condition.
  map_surjective {x y} (g : x.snd ⟶ y.snd) :=
    ⟨⟨F.preimage (x.iso.hom ≫ G.map g ≫ y.iso.inv), g, by simp⟩, rfl⟩

/-- The second projection out of the categorical pullback of an essentially surjective functor is
essentially surjective: an object `c` lifts to `(a, c, F a ≅ G c)` for any `a` with
`F a ≅ G c`. -/
instance essSurj_π₂ [F.EssSurj] : (π₂ F G).EssSurj where
  mem_essImage c := ⟨⟨F.objPreimage (G.obj c), c, F.objObjPreimageIso (G.obj c)⟩, ⟨Iso.refl _⟩⟩

/-- The second projection out of the categorical pullback of an equivalence is an equivalence:
an object of `C` lifts uniquely up to unique isomorphism. -/
instance isEquivalence_π₂ [F.IsEquivalence] : (π₂ F G).IsEquivalence where

end CategoryTheory.Limits.CategoricalPullback
