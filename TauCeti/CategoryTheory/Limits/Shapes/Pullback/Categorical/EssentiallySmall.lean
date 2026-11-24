/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# Smallness of categorical pullbacks

For functors `F : A ⥤ B` and `G : C ⥤ B`, the categorical pullback `F ⊡ G` has as objects the
triples `(a, c, F a ≅ G c)` and as morphisms the compatible pairs of morphisms. This file shows
that it inherits local smallness from `A` and `C`, and essential smallness from essentially small
`A` and `C` over a locally small `B`. Essential smallness is what a Grothendieck group presented
by isomorphism classes of such triples needs to live in the universe of its inputs.

## Main declarations

* `CategoryTheory.Limits.CategoricalPullback.locallySmall`: `F ⊡ G` is locally small when `A` and
  `C` are.
* `CategoryTheory.Limits.CategoricalPullback.essentiallySmall`: `F ⊡ G` is essentially small when
  `A` and `C` are essentially small and `B` is locally small.
-/

public section

namespace CategoryTheory.Limits.CategoricalPullback

universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] (F : A ⥤ B) (G : C ⥤ B)

/-- A categorical pullback of locally small categories is locally small: a morphism is determined
by its two components. -/
instance locallySmall [LocallySmall.{w} A] [LocallySmall.{w} C] : LocallySmall.{w} (F ⊡ G) where
  hom_small x y := small_of_injective (f := fun f : x ⟶ y ↦ (f.fst, f.snd))
    fun _ _ h ↦ hom_ext (Prod.ext_iff.1 h).1 (Prod.ext_iff.1 h).2

/-- A categorical pullback of essentially small categories over a locally small category is
essentially small: up to isomorphism, a triple `(a, c, F a ≅ G c)` has `a` and `c` in small models
of `A` and `C`, and the isomorphisms between two objects of `B` form a small type. -/
instance essentiallySmall [EssentiallySmall.{w} A] [EssentiallySmall.{w} C]
    [LocallySmall.{w} B] : EssentiallySmall.{w} (F ⊡ G) := by
  refine (essentiallySmall_iff _).2 ⟨?_, inferInstance⟩
  let eA := equivSmallModel.{w} A
  let eC := equivSmallModel.{w} C
  have hIso (X Y : B) : Small.{w} (X ≅ Y) :=
    small_of_injective (f := fun e : X ≅ Y ↦ e.hom) fun _ _ h ↦ Iso.ext h
  let φ : (Σ p : SmallModel.{w} A × SmallModel.{w} C,
      F.obj (eA.inverse.obj p.1) ≅ G.obj (eC.inverse.obj p.2)) → Skeleton (F ⊡ G) :=
    fun s ↦ toSkeleton ⟨eA.inverse.obj s.1.1, eC.inverse.obj s.1.2, s.2⟩
  refine small_of_surjective (f := φ) fun z ↦ ?_
  obtain ⟨⟨a, c, e⟩, rfl⟩ : ∃ x, toSkeleton x = z := ⟨_, toSkeleton_fromSkeleton_obj z⟩
  refine ⟨⟨(eA.functor.obj a, eC.functor.obj c),
    F.mapIso (eA.unitIso.app a).symm ≪≫ e ≪≫ G.mapIso (eC.unitIso.app c)⟩, ?_⟩
  exact congr_toSkeleton_of_iso
    (mkIso (eA.unitIso.app a).symm (eC.unitIso.app c).symm (by simp [← G.map_comp]))

end CategoryTheory.Limits.CategoricalPullback
