/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Filtered.Connected
public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Preorder.TransfiniteCompositionOfShape
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Transfinite compositions are stable under cobase change

Let `c : TransfiniteCompositionOfShape J f` express `f : X ⟶ Y` as the transfinite composition of
a well-order-continuous functor `c.F : J ⥤ C`, and let

```
X --f--> Y
|        |
a        b
v        v
Z --f'-> P
```

be a pushout square. Then `f'` is again a transfinite composition of shape `J`
(`CategoryTheory.TransfiniteCompositionOfShape.ofIsPushout`). Its `j`-th stage is the pushout of
the map `X ⟶ c.F.obj j` along `a` (`CategoryTheory.TransfiniteCompositionOfShape.pushoutF`), so
that every square

```
c.F.obj i ---> c.F.obj j
   |              |
   v              v
F'.obj i  --->  F'.obj j
```

is a pushout square (`CategoryTheory.TransfiniteCompositionOfShape.isPushout_pushoutF_map`). The
two facts behind the construction are that pushouts of functors are computed pointwise, and that
pushouts commute with colimits (`CategoryTheory.IsPushout.isColimitOfIsColimitOfIsPushout`), which
is used both for the colimit of all stages and for well-order continuity at limit elements. The
constant functors at `X` and `Z` have colimits `X` and `Z` because `J` and its initial segments
below a limit element are directed, hence connected.

This is the categorical input for attaching a relative cell complex along a map: in a pushout of a
relative cell complex the same cells are attached, stage by stage, to the new base.

## References

* M. Hovey, *Model Categories*, Mathematical Surveys and Monographs 63, American Mathematical
  Society, 1999, Section 2.1.2, for the stability of relative cell complexes under pushout.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.TransfiniteCompositionOfShape

open Limits

variable {C : Type u} [Category.{v} C] {J : Type w} [LinearOrder J] [OrderBot J] [SuccOrder J]
  [WellFoundedLT J] {X Y Z P : C} {f : X ⟶ Y} (c : TransfiniteCompositionOfShape J f)

/-- The maps from the source `X` of a transfinite composition to its stages, as a natural
transformation from the constant functor. -/
@[simps]
def fromBot : (Functor.const J).obj X ⟶ c.F where
  app j := c.isoBot.inv ≫ c.F.map (homOfLE bot_le)
  naturality i j hij := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc,
      ← Functor.map_comp]
    rfl

variable [HasPushouts C] (a : X ⟶ Z)

/-- The stages of the cobase change of a transfinite composition along `a : X ⟶ Z`: the `j`-th
stage is the pushout of `X ⟶ c.F.obj j` along `a`. -/
noncomputable def pushoutF : J ⥤ C :=
  pushout c.fromBot ((Functor.const J).map a)

/-- The map from the stages of `c` to the stages of its cobase change along `a`. -/
noncomputable def pushoutInl : c.F ⟶ c.pushoutF a :=
  pushout.inl _ _

/-- The map from the new base `Z` to the stages of the cobase change along `a`. -/
noncomputable def pushoutInr : (Functor.const J).obj Z ⟶ c.pushoutF a :=
  pushout.inr _ _

/-- The `j`-th stage of the cobase change along `a` is the pushout of `X ⟶ c.F.obj j` along
`a`. -/
lemma isPushout_pushoutF_obj (j : J) :
    IsPushout (c.fromBot.app j) a ((c.pushoutInl a).app j) ((c.pushoutInr a).app j) :=
  (IsPushout.of_hasPushout c.fromBot ((Functor.const J).map a)).app j

/-- **The stages of a cobase change are pushouts of the original stages.** For `i ≤ j`, the
square formed by the maps from stage `i` to stage `j` of `c` and of its cobase change along `a` is
a pushout square. -/
lemma isPushout_pushoutF_map {i j : J} (hij : i ≤ j) :
    IsPushout (c.F.map (homOfLE hij)) ((c.pushoutInl a).app i) ((c.pushoutInl a).app j)
      ((c.pushoutF a).map (homOfLE hij)) := by
  refine IsPushout.of_left (h₁₁ := c.fromBot.app i) (v₁₁ := a)
    (h₂₁ := (c.pushoutInr a).app i) ?_ ((c.pushoutInl a).naturality _)
    (c.isPushout_pushoutF_obj a i)
  rw [← c.fromBot.naturality, ← (c.pushoutInr a).naturality]
  simpa using c.isPushout_pushoutF_obj a j

/-- The bottom stage of the cobase change along `a` is `Z`. -/
lemma isIso_pushoutInr_app_bot : IsIso ((c.pushoutInr a).app ⊥) := by
  have : IsIso (c.fromBot.app ⊥) := by
    simp only [fromBot_app, homOfLE_refl, CategoryTheory.Functor.map_id, Category.comp_id]
    infer_instance
  exact (c.isPushout_pushoutF_obj a ⊥).isIso_inr_of_isIso

/-- The stages of the cobase change of a well-order-continuous transfinite composition are again
well-order-continuous: at a limit element pushouts commute with the colimit of the earlier
stages. -/
instance isWellOrderContinuous_pushoutF : (c.pushoutF a).IsWellOrderContinuous where
  nonempty_isColimit m hm := by
    -- The stages below `m` form a nonempty directed set, so constant functors on it have their
    -- values as colimits.
    obtain ⟨k, hk⟩ := not_isMin_iff.1 hm.not_isMin
    have : Nonempty (Set.Iio m) := ⟨⟨k, hk⟩⟩
    have := IsFiltered.isConnected (Set.Iio m)
    let ι := (Set.principalSegIio m).monotone.functor
    exact ⟨IsPushout.isColimitOfIsColimitOfIsPushout
      (t := Functor.whiskerLeft ι c.fromBot)
      (l := Functor.whiskerLeft ι ((Functor.const J).map a))
      (r := Functor.whiskerLeft ι (c.pushoutInl a))
      (b := Functor.whiskerLeft ι (c.pushoutInr a))
      (IsPushout.of_forall_isPushout_app fun k ↦ c.isPushout_pushoutF_obj a k)
      (constCocone _ X) ((Set.principalSegIio m).cocone c.F) (constCocone _ Z)
      ((Set.principalSegIio m).cocone (c.pushoutF a))
      (isColimitConstCocone _ X) (c.F.isColimitOfIsWellOrderContinuous m hm)
      (isColimitConstCocone _ Z) (c.isPushout_pushoutF_obj a m)
      (fun k ↦ c.fromBot.naturality (homOfLE k.2.le))
      (fun k ↦ by simp)
      (fun k ↦ (c.pushoutInl a).naturality (homOfLE k.2.le))
      (fun k ↦ (c.pushoutInr a).naturality (homOfLE k.2.le))⟩

variable {a} {b : Y ⟶ P} {f' : Z ⟶ P} (sq : IsPushout f a b f')

/-- The maps from the stages of the cobase change to the pushout `P`. -/
noncomputable def pushoutIncl : c.pushoutF a ⟶ (Functor.const J).obj P :=
  pushout.desc (c.incl ≫ (Functor.const J).map b) ((Functor.const J).map f') (by
    ext j
    simp [sq.w])

@[reassoc (attr := simp)]
lemma pushoutInl_app_comp_pushoutIncl_app (j : J) :
    (c.pushoutInl a).app j ≫ (c.pushoutIncl sq).app j = c.incl.app j ≫ b := by
  unfold pushoutInl pushoutIncl
  exact NatTrans.congr_app (pushout.inl_desc _ _ _) j

@[reassoc (attr := simp)]
lemma pushoutInr_app_comp_pushoutIncl_app (j : J) :
    (c.pushoutInr a).app j ≫ (c.pushoutIncl sq).app j = f' := by
  unfold pushoutInr pushoutIncl
  exact NatTrans.congr_app (pushout.inr_desc _ _ _) j

/-- **Cobase change of a transfinite composition.** If `f : X ⟶ Y` is a transfinite composition of
shape `J` and `f' : Z ⟶ P` is a pushout of `f` along `a : X ⟶ Z`, then `f'` is a transfinite
composition of shape `J`, whose `j`-th stage is the pushout of the `j`-th stage of `f` along `a`.
-/
noncomputable def ofIsPushout : TransfiniteCompositionOfShape J f' where
  F := c.pushoutF a
  isoBot :=
    have := c.isIso_pushoutInr_app_bot a
    (asIso ((c.pushoutInr a).app ⊥)).symm
  incl := c.pushoutIncl sq
  isColimit := by
    have := IsFiltered.isConnected J
    exact IsPushout.isColimitOfIsColimitOfIsPushout
      (IsPushout.of_hasPushout c.fromBot ((Functor.const J).map a))
      (constCocone J X) _ (constCocone J Z) _ (isColimitConstCocone J X) c.isColimit
      (isColimitConstCocone J Z) sq (fun j ↦ by simp) (fun j ↦ by simp)
      (fun j ↦ (c.pushoutInl_app_comp_pushoutIncl_app sq j).symm)
      (fun j ↦ (Category.id_comp _).trans (c.pushoutInr_app_comp_pushoutIncl_app sq j).symm)
  fac := by simp

@[simp]
lemma ofIsPushout_F : (c.ofIsPushout sq).F = c.pushoutF a := (rfl)

@[simp]
lemma ofIsPushout_isoBot_inv : (c.ofIsPushout sq).isoBot.inv = (c.pushoutInr a).app ⊥ := (rfl)

@[simp]
lemma ofIsPushout_incl : (c.ofIsPushout sq).incl = c.pushoutIncl sq := (rfl)

end CategoryTheory.TransfiniteCompositionOfShape
