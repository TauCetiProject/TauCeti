/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Code
-/
module

public import Mathlib.CategoryTheory.Comma.Final
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Comparison maps between limits of diagrams of different shapes

Let `F : J ⥤ 𝒱` and `F' : J' ⥤ 𝒱` be diagrams. A `TauCeti.DiagramComparison F F' A` is a span
`J ← A → J'` of index functors `K` and `H`, with `H` initial, together with a natural
transformation `β : K ⋙ F ⟶ H ⋙ F'`. It induces the map
`limit F ⟶ limit (K ⋙ F) ⟶ limit (H ⋙ F') ≅ limit F'`, restricting along `K`, applying
`limMap β` and inverting the restriction along `H`
(`TauCeti.DiagramComparison.limitMap_eq`). Initiality of `H` is exactly what makes the last step
possible: without it there need be no map at all.

Such comparisons are used to relate limits of coefficient diagrams indexed by different
categories, for instance a coefficient diagram and its restriction to a finer subdivision.
Two comparisons compose through the comma category of the middle pair of legs, whose second
projection is initial by `CategoryTheory.Comma.initial_snd`,
and the induced maps compose accordingly (`TauCeti.DiagramComparison.comp_limitMap`).

Adapted from `Mei/CategoryTheory/Limits/DiagramComparison.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`7f1e4c7714fb020473694755ad8748c8f15d0e7f` (Apache 2.0).

## Main definitions

* `TauCeti.DiagramComparison`: a span of index functors with initial target leg and a natural
  transformation between the restricted diagrams.
* `TauCeti.DiagramComparison.limitMap`: the induced map `limit F ⟶ limit F'`.
* `TauCeti.DiagramComparison.id`, `TauCeti.DiagramComparison.comp`: identity comparisons
  and composition through comma categories.
* `TauCeti.DiagramComparison.ofNatTrans`, `TauCeti.DiagramComparison.restriction`: comparisons
  from a natural transformation and restriction along an index functor.
* `TauCeti.DiagramComparison.map`: postcomposition with a functor of value categories.

## Main results

* `TauCeti.DiagramComparison.limitMap_π`: the characterizing projection formula.
* `TauCeti.DiagramComparison.id_limitMap`, `TauCeti.DiagramComparison.comp_limitMap`: identity and
  composition laws.
* `TauCeti.DiagramComparison.ofNatTrans_limitMap`, `TauCeti.DiagramComparison.restriction_limitMap`:
  identity spans recover `CategoryTheory.Limits.limMap` and restriction recovers
  `CategoryTheory.Limits.limit.pre`.
* `TauCeti.DiagramComparison.isIso_limitMap` and
  `TauCeti.DiagramComparison.isIso_limitMap_of_initial`: the map is an isomorphism when the
  natural transformation and the restriction along the source leg are.
* `TauCeti.DiagramComparison.map_limitMap`: compatibility with functors preserving the two limits.
* `TauCeti.DiagramComparison.exists_not_initial_isEmpty_limit_hom`: without initiality of the target
  leg there need be no map of limits at all.

The span constructors expose their index functors so that the types of the dependent
natural-transformation components compute. The induced limit map is kept unexposed.

The construction uses Mathlib's `CategoryTheory.Limits.IsLimit.map` and
`CategoryTheory.Functor.Initial.isLimitWhiskerEquiv`. Its factorization uses
`CategoryTheory.Limits.limit.pre`, `CategoryTheory.Limits.limMap` and
`CategoryTheory.Functor.Initial.limitIso`.
-/

public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ u₁ u₂ u₃ u₄ u₅ u₆ u₇

namespace TauCeti

open CategoryTheory Functor Limits

variable {J : Type u₁} [Category.{v₁} J] {J' : Type u₂} [Category.{v₂} J']
  {J'' : Type u₃} [Category.{v₃} J''] {𝒱 : Type u₄} [Category.{v₄} 𝒱]

/-- A comparison from a diagram `F : J ⥤ 𝒱` to a diagram `F' : J' ⥤ 𝒱`: a span
`J ← A → J'` of index functors whose target leg is initial, with a natural transformation
from the restriction of `F` along the source leg to the restriction of `F'` along the target
leg. -/
@[ext]
structure DiagramComparison (F : J ⥤ 𝒱) (F' : J' ⥤ 𝒱) (A : Type u₅) [Category.{v₅} A] where
  /-- The leg of the span into the index category of the source diagram. -/
  source : A ⥤ J
  /-- The leg of the span into the index category of the target diagram. -/
  target : A ⥤ J'
  /-- The natural transformation between the two restricted diagrams. -/
  app : source ⋙ F ⟶ target ⋙ F'
  /-- The target leg is initial, so that restriction along it does not change the limit. -/
  initial : target.Initial

attribute [instance] DiagramComparison.initial

namespace DiagramComparison

variable {A : Type u₅} [Category.{v₅} A] {B : Type u₆} [Category.{v₆} B]
  {F : J ⥤ 𝒱} {F' : J' ⥤ 𝒱} {F'' : J'' ⥤ 𝒱}

section LimitMap

variable (S : DiagramComparison F F' A) [HasLimit F] [HasLimit F']

/-- The map of limits induced by a diagram comparison. -/
noncomputable def limitMap : limit F ⟶ limit F' :=
  IsLimit.map ((limit.cone F).whisker S.source)
    ((Functor.Initial.isLimitWhiskerEquiv S.target (limit.cone F')).symm (limit.isLimit F'))
    S.app

/-- The comparison map is characterized by its projections onto the legs indexed by the
target leg of the span. -/
@[reassoc (attr := simp)]
theorem limitMap_π (a : A) :
    S.limitMap ≫ limit.π F' (S.target.obj a) = limit.π F (S.source.obj a) ≫ S.app.app a := by
  exact IsLimit.map_π _ _ _ a

omit [HasLimit F] in
/-- Maps into the target limit are determined by their projections onto the legs indexed by
the target leg of a comparison. -/
theorem hom_ext {X : 𝒱} {f g : X ⟶ limit F'}
    (h : ∀ a, f ≫ limit.π F' (S.target.obj a) = g ≫ limit.π F' (S.target.obj a)) : f = g :=
  ((Functor.Initial.isLimitWhiskerEquiv S.target (limit.cone F')).symm
    (limit.isLimit F')).hom_ext fun a => h a

/-- The comparison map is restriction along the source leg, followed by the map of limits
induced by the natural transformation and the inverse of restriction along the target leg. -/
theorem limitMap_eq [HasLimit (S.source ⋙ F)] :
    S.limitMap = limit.pre F S.source ≫ limMap S.app ≫
      (Functor.Initial.limitIso S.target F').hom := by
  apply S.hom_ext
  intro a
  simp [Functor.Initial.limitIso]

/-- The comparison map is an isomorphism when restriction along the source leg and the
natural transformation are isomorphisms. -/
instance isIso_limitMap [HasLimit (S.source ⋙ F)] [IsIso (limit.pre F S.source)] [IsIso S.app] :
    IsIso S.limitMap := by
  rw [S.limitMap_eq]
  infer_instance

/-- The comparison map is an isomorphism when the source leg is also initial and the natural
transformation is an isomorphism. -/
theorem isIso_limitMap_of_initial [S.source.Initial] [IsIso S.app] : IsIso S.limitMap :=
  S.isIso_limitMap

end LimitMap

section Constructions

variable (F) in
/-- The comparison of a diagram with itself along the identity span. -/
@[expose]
def id : DiagramComparison F F J where
  source := 𝟭 J
  target := 𝟭 J
  app := 𝟙 _
  initial := inferInstance

@[simp]
theorem id_source : (id F).source = 𝟭 J := (rfl)

@[simp]
theorem id_target : (id F).target = 𝟭 J := (rfl)

@[simp]
theorem id_app : (id F).app = 𝟙 _ := (rfl)

/-- The identity comparison induces the identity of the limit. -/
@[simp]
theorem id_limitMap [HasLimit F] : (id F).limitMap = 𝟙 (limit F) :=
  limit.hom_ext fun j => by
    simpa only [id, Functor.comp_obj, Functor.id_obj, NatTrans.id_app, Category.comp_id,
      Category.id_comp] using (id F).limitMap_π j

/-- The comparison along the identity span induced by a natural transformation of diagrams
of the same shape. -/
@[expose]
def ofNatTrans {G G' : J ⥤ 𝒱} (β : G ⟶ G') : DiagramComparison G G' J where
  source := 𝟭 J
  target := 𝟭 J
  app := (Functor.leftUnitor G).hom ≫ β ≫ (Functor.leftUnitor G').inv
  initial := inferInstance

@[simp]
theorem ofNatTrans_source {G G' : J ⥤ 𝒱} (β : G ⟶ G') : (ofNatTrans β).source = 𝟭 J := (rfl)

@[simp]
theorem ofNatTrans_target {G G' : J ⥤ 𝒱} (β : G ⟶ G') : (ofNatTrans β).target = 𝟭 J := (rfl)

@[simp]
theorem ofNatTrans_app {G G' : J ⥤ 𝒱} (β : G ⟶ G') :
    (ofNatTrans β).app = (Functor.leftUnitor G).hom ≫ β ≫ (Functor.leftUnitor G').inv := (rfl)

/-- The comparison of a natural transformation along the identity span induces `limMap`. -/
@[simp]
theorem ofNatTrans_limitMap {G G' : J ⥤ 𝒱} (β : G ⟶ G') [HasLimit G] [HasLimit G'] :
    (ofNatTrans β).limitMap = limMap β :=
  limit.hom_ext fun j => by
    simpa only [ofNatTrans, Functor.comp_obj, Functor.id_obj, NatTrans.comp_app,
      Functor.leftUnitor_hom_app, Functor.leftUnitor_inv_app, Category.id_comp,
      Category.comp_id, Category.assoc, limMap_π] using
      (ofNatTrans β).limitMap_π j

variable (F) in
/-- The comparison of a diagram with its restriction along an index functor `u`, given by
the span `J ← J' → J'` with legs `u` and the identity. -/
@[expose]
def restriction (u : J' ⥤ J) : DiagramComparison F (u ⋙ F) J' where
  source := u
  target := 𝟭 J'
  app := (Functor.leftUnitor _).inv
  initial := inferInstance

@[simp]
theorem restriction_source (u : J' ⥤ J) : (restriction F u).source = u := (rfl)

@[simp]
theorem restriction_target (u : J' ⥤ J) : (restriction F u).target = 𝟭 J' := (rfl)

@[simp]
theorem restriction_app (u : J' ⥤ J) :
    (restriction F u).app = (Functor.leftUnitor _).inv := (rfl)

/-- Restriction along an index functor induces `limit.pre`. -/
@[simp]
theorem restriction_limitMap (u : J' ⥤ J) [HasLimit F] [HasLimit (u ⋙ F)] :
    (restriction F u).limitMap = limit.pre F u :=
  limit.hom_ext fun j => by
    simpa only [restriction, Functor.comp_obj, Functor.id_obj, Functor.leftUnitor_inv_app,
      Category.comp_id, limit.pre_π] using (restriction F u).limitMap_π j

/-- The composite of two comparisons, indexed by the comma category of the target leg of the
first and the source leg of the second. Its natural transformation at `(a, b, f)` is the
composite `F (K a) ⟶ F' (H a) ⟶ F' (K' b) ⟶ F'' (H' b)`, with middle map `F'.map f`. -/
@[expose]
def comp (S : DiagramComparison F F' A) (T : DiagramComparison F' F'' B) :
    DiagramComparison F F'' (Comma S.target T.source) where
  source := Comma.fst S.target T.source ⋙ S.source
  target := Comma.snd S.target T.source ⋙ T.target
  app :=
    { app x := S.app.app x.left ≫ F'.map x.hom ≫ T.app.app x.right
      naturality x y f := by
        have hs := S.app.naturality f.left
        have ht := T.app.naturality f.right
        simp only [Functor.comp_obj, Functor.comp_map, Comma.fst_map, Comma.snd_map,
          Category.assoc] at hs ht ⊢
        rw [reassoc_of% hs, ← F'.map_comp_assoc, f.w, F'.map_comp_assoc, ht] }
  initial := inferInstance

@[simp]
theorem comp_source (S : DiagramComparison F F' A) (T : DiagramComparison F' F'' B) :
    (S.comp T).source = Comma.fst S.target T.source ⋙ S.source := (rfl)

@[simp]
theorem comp_target (S : DiagramComparison F F' A) (T : DiagramComparison F' F'' B) :
    (S.comp T).target = Comma.snd S.target T.source ⋙ T.target := (rfl)

@[simp]
theorem comp_app_app (S : DiagramComparison F F' A) (T : DiagramComparison F' F'' B)
    (x : Comma S.target T.source) :
    (S.comp T).app.app x = S.app.app x.left ≫ F'.map x.hom ≫ T.app.app x.right := (rfl)

/-- The map induced by a composite comparison is the composite of the induced maps. -/
@[simp, reassoc]
theorem comp_limitMap (S : DiagramComparison F F' A) (T : DiagramComparison F' F'' B)
    [HasLimit F] [HasLimit F'] [HasLimit F''] :
    (S.comp T).limitMap = S.limitMap ≫ T.limitMap := by
  refine (S.comp T).hom_ext fun x => ?_
  rw [(S.comp T).limitMap_π]
  simp only [comp, Functor.comp_obj, Comma.fst_obj, Comma.snd_obj, Category.assoc,
    T.limitMap_π]
  rw [← limit.w F' x.hom, Category.assoc, S.limitMap_π_assoc]

end Constructions

section Preservation

variable {𝒲 : Type u₇} [Category.{v₇} 𝒲]

/-- The comparison obtained by postcomposing both diagrams with a functor of value
categories. -/
@[expose]
def map (S : DiagramComparison F F' A) (G : 𝒱 ⥤ 𝒲) :
    DiagramComparison (F ⋙ G) (F' ⋙ G) A where
  source := S.source
  target := S.target
  app := (Functor.associator _ _ _).inv ≫ Functor.whiskerRight S.app G ≫
    (Functor.associator _ _ _).hom
  initial := S.initial

@[simp]
theorem map_source (S : DiagramComparison F F' A) (G : 𝒱 ⥤ 𝒲) :
    (S.map G).source = S.source := (rfl)

@[simp]
theorem map_target (S : DiagramComparison F F' A) (G : 𝒱 ⥤ 𝒲) :
    (S.map G).target = S.target := (rfl)

@[simp]
theorem map_app_app (S : DiagramComparison F F' A) (G : 𝒱 ⥤ 𝒲) (a : A) :
    (S.map G).app.app a = G.map (S.app.app a) := by
  simp [map]

/-- A functor preserving both limits carries the comparison map to the comparison map of the
postcomposed diagrams. -/
@[reassoc]
theorem map_limitMap (S : DiagramComparison F F' A) (G : 𝒱 ⥤ 𝒲) [HasLimit F] [HasLimit F']
    [PreservesLimit F G] [PreservesLimit F' G] :
    G.map S.limitMap ≫ (preservesLimitIso G F').hom =
      (preservesLimitIso G F).hom ≫ (S.map G).limitMap := by
  refine (S.map G).hom_ext fun a => ?_
  rw [Category.assoc, Category.assoc, (S.map G).limitMap_π]
  simp only [map, Functor.comp_obj, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.associator_hom_app, whiskerRight_app, Category.id_comp, Category.comp_id,
    preservesLimitIso_hom_π, preservesLimitIso_hom_π_assoc, ← G.map_comp, limitMap_π]

end Preservation

section NotInitial

/-- Initiality of the target leg cannot be dropped. For the constant diagram at a point on the
terminal index category, the diagram on two discrete objects with values a point and the empty
type, and the non-initial index functor picking out the first object, there is a natural
transformation between the restricted diagrams but no map from the first limit, a point, to the
second limit, which is empty. -/
theorem exists_not_initial_isEmpty_limit_hom :
    ∃ (F : Discrete PUnit.{1} ⥤ Type) (F' : Discrete Bool ⥤ Type)
      (H : Discrete PUnit.{1} ⥤ Discrete Bool),
      ¬ H.Initial ∧ Nonempty (𝟭 _ ⋙ F ⟶ H ⋙ F') ∧ IsEmpty (limit F ⟶ limit F') := by
  refine ⟨(Functor.const _).obj PUnit, Discrete.functor fun b => cond b PUnit PEmpty,
    Discrete.functor fun _ => ⟨true⟩, fun h => ?_, ⟨Discrete.natTrans fun _ => 𝟙 PUnit⟩,
    ⟨fun f => ?_⟩⟩
  · -- No object of the source is sent to an object with a map to the second object.
    obtain ⟨⟨_, _, g⟩⟩ := (h.out ⟨false⟩).is_nonempty
    exact Bool.noConfusion (Discrete.eq_of_hom g)
  · have x : limit ((Functor.const (Discrete PUnit.{1})).obj PUnit) :=
      Types.Limit.mk _ (fun _ => PUnit.unit) (fun _ _ _ => rfl)
    exact (limit.π (Discrete.functor fun b => cond b PUnit PEmpty) ⟨false⟩ (f x)).elim

end NotInitial

end DiagramComparison

end TauCeti
