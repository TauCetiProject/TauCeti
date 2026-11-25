/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import TauCeti.CategoryTheory.Limits.Shapes.Pullback.Map
public import TauCeti.CategoryTheory.EquivalenceRelation

/-!
# Relatively representable morphisms: descent, monomorphisms and diagonals

Let `F : C ⥤ D` be a functor and let `f : X ⟶ Y` in `D` be relatively representable with respect
to `F`. Mathlib's `MorphismProperty.relative_of_snd` shows that, for `F` full and faithful, `f`
satisfies `P.relative F` once every base change `hf.snd g` along `g : F.obj a ⟶ Y` satisfies `P`.
This file weakens the hypothesis when `P` descends along `Q`: it suffices that each such base
change satisfies `P` after a further base change along a morphism satisfying `Q`. It also shows
that a relatively representable monomorphism is relatively a monomorphism, computes the base
changes of a relatively representable diagonal `X ⟶ X ⨯ X`, and shows that the kernel pair
`U ×_Y U` of a relatively representable `f : F.obj U ⟶ Y` is an internal equivalence relation on
`U`. Finally, relative representability is unchanged when the target is replaced through an
equivalence `e : D ≌ D'` and `F` by a functor `F'` with `F ⋙ e.functor ≅ F'`.

## Main results

* `CategoryTheory.MorphismProperty.relative_of_descendsAlong`: if `P` descends along `Q`, and for
  every `g : F.obj a ⟶ Y` there is `p : a' ⟶ a` satisfying `Q` such that the base change of `f`
  along `F.map p ≫ g` satisfies `P`, then `f` satisfies `P.relative F`.
* `CategoryTheory.MorphismProperty.relative_monomorphisms_of_mono`: if `F` reflects monomorphisms,
  a relatively representable monomorphism satisfies `(monomorphisms C).relative F`.
* `CategoryTheory.Functor.relativelyRepresentable.isPullback_diag_snd`: for `a : F.obj U ⟶ X`
  relatively representable, `b : F.obj V ⟶ X`, and `G : F.obj T ⟶ X ⨯ X` with components
  `F.map u ≫ a` and `F.map v ≫ b`, the base change of the diagonal of `X` along `G` is the base
  change of `(fst, snd) : U ×_X V ⟶ U ⨯ V` along `(u, v) : T ⟶ U ⨯ V`.
* `CategoryTheory.Functor.relativelyRepresentable.ofPairHom_iff`: for `f : F.obj U ⟶ Y`
  relatively representable, the kernel pair `U ×_Y U` relates `u` to `v` exactly when
  `F.map u ≫ f = F.map v ≫ f`.
* `CategoryTheory.Functor.relativelyRepresentable.isEquivalenceRelation`: the kernel pair
  `U ×_Y U` of a relatively representable `f : F.obj U ⟶ Y` is an internal equivalence relation.
* `CategoryTheory.Functor.relativelyRepresentable_equivalence_map_iff` and
  `CategoryTheory.MorphismProperty.relative_equivalence_map_iff`: transport along an equivalence
  of target categories.
-/

public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

open Limits

namespace MorphismProperty

section

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {F : C ⥤ D} [F.Full] [F.Faithful]
  {P Q : MorphismProperty C} {X Y : D} {f : X ⟶ Y}

/-- Let `F` be full and faithful, `f` relatively representable with respect to `F`, and let `P`
descend along `Q`. If for every `g : F.obj a ⟶ Y` there is a morphism `p : a' ⟶ a` satisfying `Q`
such that the base change of `f` along `F.map p ≫ g` satisfies `P`, then `f` satisfies
`P.relative F`. -/
theorem relative_of_descendsAlong [P.RespectsIso] [P.DescendsAlong Q]
    (hf : F.relativelyRepresentable f)
    (h : ∀ ⦃a : C⦄ (g : F.obj a ⟶ Y), ∃ (a' : C) (p : a' ⟶ a), Q p ∧ P (hf.snd (F.map p ≫ g))) :
    P.relative F f := by
  refine relative_of_snd hf fun a g ↦ ?_
  obtain ⟨a', p, hp, hP⟩ := h g
  let k := hf.lift (hf.fst (F.map p ≫ g)) (hf.snd (F.map p ≫ g) ≫ p)
    (by simpa using hf.w (F.map p ≫ g))
  have sq : IsPullback (F.map k) (F.map (hf.snd (F.map p ≫ g))) (F.map (hf.snd g)) (F.map p) :=
    IsPullback.of_right (by simpa [k] using hf.isPullback (F.map p ≫ g))
      (by simp [k, ← Functor.map_comp]) (hf.isPullback g)
  exact of_isPullback_of_descendsAlong (sq.of_map_of_faithful F).flip hp hP

end

/-- If `F` reflects monomorphisms, a relatively representable monomorphism `f` satisfies
`(monomorphisms C).relative F`. -/
theorem relative_monomorphisms_of_mono {C : Type*} [Category* C] {D : Type*} [Category* D]
    {F : C ⥤ D} [F.ReflectsMonomorphisms] {X Y : D} {f : X ⟶ Y} [Mono f]
    (hf : F.relativelyRepresentable f) : (monomorphisms C).relative F f :=
  ⟨hf, fun _ _ _ _ _ h ↦ have := h.mono_snd_of_mono; F.mono_of_mono_map ‹_›⟩

end MorphismProperty

namespace Functor.relativelyRepresentable

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {F : C ⥤ D}
  {X : D} [HasBinaryProduct X X] (hX : F.relativelyRepresentable (Limits.diag X))
  {U V T : C} {a : F.obj U ⟶ X} {b : F.obj V ⟶ X} {G : F.obj T ⟶ X ⨯ X} {u : T ⟶ U} {v : T ⟶ V}

include hX in
/-- If `G : F.obj T ⟶ X ⨯ X` has components `F.map u ≫ a` and `F.map v ≫ b`, then the composites
of the base change of the diagonal of `X` along `G` with `F.map u ≫ a` and `F.map v ≫ b` agree. -/
theorem map_diag_snd_comp_eq (hu : G ≫ prod.fst = F.map u ≫ a)
    (hv : G ≫ prod.snd = F.map v ≫ b) :
    F.map (hX.snd G ≫ u) ≫ a = F.map (hX.snd G ≫ v) ≫ b := by
  have e₁ := hX.w G =≫ prod.fst
  have e₂ := hX.w G =≫ prod.snd
  simp only [Category.assoc, Limits.diag, prod.lift_fst, prod.lift_snd, Category.comp_id, hu,
    hv] at e₁ e₂
  simpa using e₁.symm.trans e₂

/-- Let `a : F.obj U ⟶ X` be relatively representable, `b : F.obj V ⟶ X`, and let
`G : F.obj T ⟶ X ⨯ X` have components `F.map u ≫ a` and `F.map v ≫ b`. Then the base change of the
diagonal of `X` along `G` is the base change of `(fst, snd) : U ×_X V ⟶ U ⨯ V` along
`(u, v) : T ⟶ U ⨯ V`. -/
theorem isPullback_diag_snd [F.Full] [F.Faithful] [HasBinaryProduct U V]
    (ha : F.relativelyRepresentable a) (hu : G ≫ prod.fst = F.map u ≫ a)
    (hv : G ≫ prod.snd = F.map v ≫ b) :
    IsPullback (ha.lift' (hX.snd G ≫ u) (hX.snd G ≫ v) (hX.map_diag_snd_comp_eq hu hv))
      (hX.snd G) (prod.lift (ha.fst' b) (ha.snd b)) (prod.lift u v) := by
  have he (c : PullbackCone (prod.lift (ha.fst' b) (ha.snd b)) (prod.lift u v)) :
      c.fst ≫ ha.fst' b = c.snd ≫ u ∧ c.fst ≫ ha.snd b = c.snd ≫ v :=
    ⟨by simpa using c.condition =≫ prod.fst, by simpa using c.condition =≫ prod.snd⟩
  have ht₁ : hX.fst G = F.map (hX.snd G) ≫ F.map u ≫ a := by
    simpa [hu] using hX.w G =≫ prod.fst
  refine ⟨⟨by ext <;> simp⟩, ⟨PullbackCone.IsLimit.mk _
    (fun c ↦ hX.lift (F.map (c.snd ≫ u) ≫ a) c.snd ?_) (fun c ↦ ?_) (fun c ↦ ?_)
    (fun c m _ hm₂ ↦ ?_)⟩⟩
  · have : F.map (c.snd ≫ u) ≫ a = F.map (c.snd ≫ v) ≫ b := by
      simp only [← (he c).1, ← (he c).2, Functor.map_comp, Category.assoc, (ha.isPullback' b).w]
    apply prod.hom_ext
    · simp [hu]
    · simpa [hv] using this
  · apply ha.hom_ext'
    · simp [(he c).1]
    · simp [(he c).2]
  · exact hX.lift_snd _ _ _
  · apply hX.hom_ext
    · rw [hX.lift_fst, ht₁]
      simp only [← Functor.map_comp_assoc, reassoc_of% hm₂]
    · simp [hm₂]

end Functor.relativelyRepresentable

namespace Functor.relativelyRepresentable

open TauCeti.CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {F : C ⥤ D} [F.Full] [F.Faithful]
  {U : C} {Y : D} {f : F.obj U ⟶ Y} (hf : F.relativelyRepresentable f)

include hf in
/-- Two morphisms `u, v : T ⟶ U` are related by the kernel pair `U ×_Y U` of a relatively
representable `f : F.obj U ⟶ Y` exactly when `F.map u ≫ f = F.map v ≫ f`. -/
theorem ofPairHom_iff {T : C} {u v : T ⟶ U} :
    Rel.ofPairHom (hf.fst' f) (hf.snd f) T u v ↔ F.map u ≫ f = F.map v ≫ f := by
  rw [Rel.ofPairHom_iff]
  refine ⟨?_, fun h ↦ ⟨_, hf.lift'_fst u v h, hf.lift'_snd u v h⟩⟩
  rintro ⟨r, rfl, rfl⟩
  simp only [Functor.map_comp, Category.assoc, (hf.isPullback' f).w]

/-- The kernel pair `U ×_Y U` of a relatively representable `f : F.obj U ⟶ Y`, with its two
projections to `U`, is an internal equivalence relation on `U`. -/
theorem isEquivalenceRelation [HasPullback (hf.snd f) (hf.fst' f)] :
    IsEquivalenceRelation (hf.fst' f) (hf.snd f) := by
  refine isEquivalenceRelation_iff.mpr ⟨⟨fun _ _ _ h₁ h₂ ↦ hf.hom_ext' h₁ h₂⟩, fun T ↦ ?_⟩
  refine ⟨fun u ↦ hf.ofPairHom_iff.mpr rfl, fun h ↦ hf.ofPairHom_iff.mpr ?_,
    fun h h' ↦ hf.ofPairHom_iff.mpr ?_⟩
  · exact (hf.ofPairHom_iff.mp h).symm
  · exact (hf.ofPairHom_iff.mp h).trans (hf.ofPairHom_iff.mp h')

end Functor.relativelyRepresentable

section Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {D' : Type u₃} [Category.{v₃} D'] {F : C ⥤ D} {F' : C ⥤ D'} {e : D ≌ D'}
  (i : F ⋙ e.functor ≅ F')

include i

/-- Relative representability is invariant under replacing the target category through an
equivalence `e : D ≌ D'`, the functor `F` by `F'` with `F ⋙ e.functor ≅ F'`. -/
theorem Functor.relativelyRepresentable_equivalence_map_iff {X Y : D} (f : X ⟶ Y) :
    F'.relativelyRepresentable (e.functor.map f) ↔ F.relativelyRepresentable f := by
  constructor
  · intro h a g
    obtain ⟨b, snd, fst', hb⟩ := h (i.inv.app a ≫ e.functor.map g)
    refine ⟨b, snd, e.functor.preimage (i.hom.app b ≫ fst'), ?_⟩
    rw [← isPullback_equivalence_map_iff i]
    simpa using hb
  · intro h a g'
    obtain ⟨b, snd, fst, hb⟩ := h (e.functor.preimage (i.hom.app a ≫ g'))
    refine ⟨b, snd, i.inv.app b ≫ e.functor.map fst, ?_⟩
    simpa using (isPullback_equivalence_map_iff i).2 hb

/-- The morphism property `P.relative` is invariant under replacing the target category through
an equivalence `e : D ≌ D'`, the functor `F` by `F'` with `F ⋙ e.functor ≅ F'`. -/
theorem MorphismProperty.relative_equivalence_map_iff (P : MorphismProperty C) {X Y : D}
    (f : X ⟶ Y) : P.relative F' (e.functor.map f) ↔ P.relative F f := by
  refine and_congr (Functor.relativelyRepresentable_equivalence_map_iff i f) ⟨?_, ?_⟩
  · intro h a b g fst snd hb
    exact h (i.inv.app a ≫ e.functor.map g) _ snd ((isPullback_equivalence_map_iff i).2 hb)
  · intro h a b g' fst' snd hb
    refine h (e.functor.preimage (i.hom.app a ≫ g')) (e.functor.preimage (i.hom.app b ≫ fst'))
      snd ?_
    rw [← isPullback_equivalence_map_iff i]
    simpa using hb

end Equivalence

end CategoryTheory
