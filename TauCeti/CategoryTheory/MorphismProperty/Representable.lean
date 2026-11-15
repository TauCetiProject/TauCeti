/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Relatively representable morphisms: descent, monomorphisms and diagonals

Let `F : C ⥤ D` be a functor and let `f : X ⟶ Y` in `D` be relatively representable with respect
to `F`. Mathlib's `MorphismProperty.relative_of_snd` shows that, for `F` full and faithful, `f`
satisfies `P.relative F` once every base change `hf.snd g` along `g : F.obj a ⟶ Y` satisfies `P`.
This file weakens the hypothesis when `P` descends along `Q`: it suffices that each such base
change satisfies `P` after a further base change along a morphism satisfying `Q`. It also shows
that a relatively representable monomorphism is relatively a monomorphism, and computes the base
changes of a relatively representable diagonal `X ⟶ X ⨯ X`.

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
* `CategoryTheory.Functor.relativelyRepresentable.diag_of_mono`,
  `CategoryTheory.Functor.relativelyRepresentable.diag_prod`, and
  `CategoryTheory.Functor.relativelyRepresentable.diag_pullback`: relative representability of the
  diagonal passes to subobjects, binary products, and pullbacks.
-/

public section

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

namespace Limits

/-- For a monomorphism `ι : X ⟶ Y` between objects with binary self-products, the diagonal of `X`
is the pullback of the diagonal of `Y` along `ι ⨯ ι`. -/
theorem isPullback_diag_of_mono {D : Type*} [Category* D] {X Y : D}
    [HasBinaryProduct X X] [HasBinaryProduct Y Y] (ι : X ⟶ Y) [Mono ι] :
    IsPullback ι (Limits.diag X) (Limits.diag Y) (prod.map ι ι) := by
  refine IsPullback.mk' (by ext <;> simp)
    (fun _ _ _ h₁ _ ↦ (cancel_mono ι).1 h₁) fun _ a b h ↦ ?_
  have h₁ : a = (b ≫ prod.fst) ≫ ι := by simpa using h =≫ prod.fst
  have h₂ : a = (b ≫ prod.snd) ≫ ι := by simpa using h =≫ prod.snd
  have h₁₂ : b ≫ prod.fst = b ≫ prod.snd := (cancel_mono ι).1 (h₁.symm.trans h₂)
  exact ⟨b ≫ prod.fst, h₁.symm, by ext <;> simp [h₁₂]⟩

end Limits

namespace Functor.relativelyRepresentable

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {F : C ⥤ D}

/-- Relative representability of the diagonal passes along monomorphisms. -/
theorem diag_of_mono {X Y : D} [HasBinaryProduct X X] [HasBinaryProduct Y Y]
    (ι : X ⟶ Y) [Mono ι] (hY : F.relativelyRepresentable (Limits.diag Y)) :
    F.relativelyRepresentable (Limits.diag X) :=
  (isStableUnderBaseChange F).of_isPullback (Limits.isPullback_diag_of_mono ι) hY

/-- Relative representability of the diagonal is stable under binary products. -/
theorem diag_prod [HasBinaryProducts D] {X Y : D}
    (hX : F.relativelyRepresentable (Limits.diag X))
    (hY : F.relativelyRepresentable (Limits.diag Y)) :
    F.relativelyRepresentable (Limits.diag (X ⨯ Y)) := by
  have : F.relativelyRepresentable.IsStableUnderComposition :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  let e : (X ⨯ Y) ⨯ (X ⨯ Y) ≅ (X ⨯ X) ⨯ (Y ⨯ Y) :=
    { hom := prod.lift (prod.map prod.fst prod.fst) (prod.map prod.snd prod.snd)
      inv := prod.lift (prod.map prod.fst prod.fst) (prod.map prod.snd prod.snd)
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp }
  have h₁ : F.relativelyRepresentable (prod.map (Limits.diag X) (𝟙 Y)) :=
    (isStableUnderBaseChange F).of_isPullback (IsPullback.of_prod_fst_with_id (Limits.diag X) Y) hX
  have h₂ : F.relativelyRepresentable (prod.map (Limits.diag Y) (𝟙 (X ⨯ X))) :=
    (isStableUnderBaseChange F).of_isPullback
      (IsPullback.of_prod_fst_with_id (Limits.diag Y) (X ⨯ X)) hY
  have h₂' : F.relativelyRepresentable (prod.map (𝟙 (X ⨯ X)) (Limits.diag Y)) := by
    have hfac : prod.map (𝟙 (X ⨯ X)) (Limits.diag Y) =
        (prod.braiding (X ⨯ X) Y).hom ≫ prod.map (Limits.diag Y) (𝟙 (X ⨯ X)) ≫
          (prod.braiding (Y ⨯ Y) (X ⨯ X)).hom := by ext <;> simp
    rw [hfac, F.relativelyRepresentable.cancel_left_of_respectsIso,
      F.relativelyRepresentable.cancel_right_of_respectsIso]
    exact h₂
  have : IsIso e.inv := e.isIso_inv
  have hfac : Limits.diag (X ⨯ Y) =
      (prod.map (Limits.diag X) (𝟙 Y) ≫ prod.map (𝟙 (X ⨯ X)) (Limits.diag Y)) ≫ e.inv := by
    ext <;> simp [e]
  rw [hfac]
  exact MorphismProperty.comp_mem _ _ _ (MorphismProperty.comp_mem _ _ _ h₁ h₂')
    (of_isIso F e.inv)

/-- Relative representability of the diagonal is stable under pullbacks. -/
theorem diag_pullback [HasBinaryProducts D] {X Y Z : D} (f : X ⟶ Z) (g : Y ⟶ Z)
    [HasPullback f g]
    (hX : F.relativelyRepresentable (Limits.diag X))
    (hY : F.relativelyRepresentable (Limits.diag Y)) :
    F.relativelyRepresentable (Limits.diag (Limits.pullback f g)) := by
  have : Mono (prod.lift (Limits.pullback.fst f g) (Limits.pullback.snd f g)) :=
    ⟨fun _ _ h ↦ Limits.pullback.hom_ext (by simpa using h =≫ prod.fst)
      (by simpa using h =≫ prod.snd)⟩
  exact diag_of_mono (prod.lift (Limits.pullback.fst f g) (Limits.pullback.snd f g))
    (diag_prod hX hY)

end Functor.relativelyRepresentable

end CategoryTheory
