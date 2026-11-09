/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.CategoryTheory.Limits.Final

/-!
# Maps between limits of reindexed diagrams

A natural transformation `α : u ⋙ F ⟶ G` induces `α.reindexLimitMap` from the limit
of `F` to the limit of `G`. Only these two limits are needed; the restricted diagram
need not have a chosen limit, and `u` need not be initial. The construction uses
Mathlib's `IsLimit.map` on a whiskered limit cone.

The projection formula characterizes the map. Identity and composition laws,
invariance under common restrictions, and inverse comparisons allow one to compare
inverse limits with different cutoff functions. In particular, enlarging a cutoff
and precomposing the component map with the transition map leaves the map unchanged.

Adapted from `Mei/CategoryTheory/Limits/Reindex.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`97304cc1bd51a202db1a705709fb4763f61e190a` (Apache 2.0).
-/

public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.NatTrans

open Limits CategoryTheory.Functor

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]
  {L : Type u₃} [Category.{v₃} L] {C : Type u₄} [Category.{v₄} C]
  {F : J ⥤ C} {G : K ⥤ C} {H : L ⥤ C}
  {u : K ⥤ J} {v : L ⥤ K}

/-- The map of limits induced by a natural transformation out of a reindexed diagram. -/
noncomputable def reindexLimitMap (α : u ⋙ F ⟶ G) [HasLimit F] [HasLimit G] :
    limit F ⟶ limit G :=
  (limit.isLimit G).map ((limit.cone F).whisker u) α

/-- Each target projection is the corresponding source projection followed by the component
of the natural transformation. -/
@[reassoc (attr := simp)]
theorem reindexLimitMap_π (α : u ⋙ F ⟶ G) [HasLimit F] [HasLimit G] (k : K) :
    α.reindexLimitMap ≫ limit.π G k = limit.π F (u.obj k) ≫ α.app k :=
  IsLimit.map_π _ _ _ _

/-- When the restricted limit exists, the map factors as restriction followed by `limMap`. -/
theorem reindexLimitMap_eq_limitPre_comp_limMap (α : u ⋙ F ⟶ G)
    [HasLimit F] [HasLimit G] [HasLimit (u ⋙ F)] :
    α.reindexLimitMap = limit.pre F u ≫ limMap α := by
  apply limit.hom_ext
  intro k
  simp

/-- With unchanged indices, the construction recovers the ordinary map of limits. -/
@[simp]
theorem reindexLimitMap_leftUnitor_hom {G' : J ⥤ C} (α : F ⟶ G')
    [HasLimit F] [HasLimit G'] :
    ((Functor.leftUnitor F).hom ≫ α).reindexLimitMap = limMap α := by
  apply limit.hom_ext
  intro j
  simp

/-- The identity transformation of a restricted diagram induces the restriction map. -/
@[simp]
theorem reindexLimitMap_id_eq_limitPre [HasLimit F] [HasLimit (u ⋙ F)] :
    reindexLimitMap (u := u) (𝟙 (u ⋙ F)) = limit.pre F u := by
  apply limit.hom_ext
  intro k
  simp

/-- An invertible comparison along an initial index functor identifies the limits. -/
instance isIso_reindexLimitMap (α : u ⋙ F ⟶ G)
    [HasLimit F] [HasLimit G] [u.Initial] [IsIso α] : IsIso α.reindexLimitMap := by
  rw [reindexLimitMap_eq_limitPre_comp_limMap]
  infer_instance

/-- Unchanged indices and the identity transformation give the identity of the limit. -/
@[simp]
theorem reindexLimitMap_id [HasLimit F] :
    (Functor.leftUnitor F).hom.reindexLimitMap = 𝟙 (limit F) := by
  apply limit.hom_ext
  intro j
  simp

/-- Successive comparisons compose their index functors in the reverse order. -/
@[simp, reassoc]
theorem reindexLimitMap_comp (α : u ⋙ F ⟶ G) (β : v ⋙ G ⟶ H)
    [HasLimit F] [HasLimit G] [HasLimit H] :
    (whiskerLeft v α ≫ β).reindexLimitMap (u := v ⋙ u) =
      α.reindexLimitMap ≫ β.reindexLimitMap := by
  apply limit.hom_ext
  intro l
  simp

/-- Common restrictions of the components suffice to identify maps of limits. The common
source and its two arrows may be chosen separately for each target object. -/
theorem reindexLimitMap_eq_of_common {u' : K ⥤ J}
    (α : u ⋙ F ⟶ G) (β : u' ⋙ F ⟶ G) [HasLimit F] [HasLimit G]
    (h : ∀ k, ∃ (j : J) (f : j ⟶ u.obj k) (g : j ⟶ u'.obj k),
      F.map f ≫ α.app k = F.map g ≫ β.app k) :
    α.reindexLimitMap = β.reindexLimitMap := by
  apply limit.hom_ext
  intro k
  obtain ⟨j, f, g, hfg⟩ := h k
  simp only [reindexLimitMap_π]
  rw [← limit.w F f, ← limit.w F g]
  simpa only [Category.assoc] using congrArg (limit.π F j ≫ ·) hfg

/-- Precomposing a comparison with a natural transformation of index functors leaves its
map of limits unchanged. -/
@[simp]
theorem reindexLimitMap_whiskerRight {u' : K ⥤ J} (σ : u' ⟶ u)
    (α : u ⋙ F ⟶ G) [HasLimit F] [HasLimit G] :
    (whiskerRight σ F ≫ α).reindexLimitMap = α.reindexLimitMap := by
  apply reindexLimitMap_eq_of_common
  intro k
  exact ⟨u'.obj k, 𝟙 _, σ.app k, by simp⟩

section Inverse

variable {w : J ⥤ K} (α : u ⋙ F ⟶ G) (β : w ⋙ G ⟶ F)
  [HasLimit F] [HasLimit G]

/-- A composite comparison agreeing with the identity after common restrictions induces the
identity on the limit. -/
theorem reindexLimitMap_comp_eq_id
    (h : ∀ j, ∃ (i : J) (f : i ⟶ u.obj (w.obj j)) (g : i ⟶ j),
      F.map f ≫ α.app (w.obj j) ≫ β.app j = F.map g) :
    α.reindexLimitMap ≫ β.reindexLimitMap = 𝟙 (limit F) := by
  rw [← reindexLimitMap_comp, ← reindexLimitMap_id (F := F)]
  apply reindexLimitMap_eq_of_common
  intro j
  obtain ⟨i, f, g, hfg⟩ := h j
  exact ⟨i, f, g, by simpa using hfg⟩

/-- Comparisons inverse after common restrictions identify the limits. No initiality or
surjectivity condition on the index functors or diagram maps is required. -/
noncomputable def reindexLimitIso
    (hF : ∀ j, ∃ (i : J) (f : i ⟶ u.obj (w.obj j)) (g : i ⟶ j),
      F.map f ≫ α.app (w.obj j) ≫ β.app j = F.map g)
    (hG : ∀ k, ∃ (i : K) (f : i ⟶ w.obj (u.obj k)) (g : i ⟶ k),
      G.map f ≫ β.app (u.obj k) ≫ α.app k = G.map g) :
    limit F ≅ limit G where
  hom := α.reindexLimitMap
  inv := β.reindexLimitMap
  hom_inv_id := reindexLimitMap_comp_eq_id α β hF
  inv_hom_id := reindexLimitMap_comp_eq_id β α hG

@[simp]
theorem reindexLimitIso_hom
    (hF : ∀ j, ∃ (i : J) (f : i ⟶ u.obj (w.obj j)) (g : i ⟶ j),
      F.map f ≫ α.app (w.obj j) ≫ β.app j = F.map g)
    (hG : ∀ k, ∃ (i : K) (f : i ⟶ w.obj (u.obj k)) (g : i ⟶ k),
      G.map f ≫ β.app (u.obj k) ≫ α.app k = G.map g) :
    (α.reindexLimitIso β hF hG).hom = α.reindexLimitMap :=
  (rfl)

@[simp]
theorem reindexLimitIso_inv
    (hF : ∀ j, ∃ (i : J) (f : i ⟶ u.obj (w.obj j)) (g : i ⟶ j),
      F.map f ≫ α.app (w.obj j) ≫ β.app j = F.map g)
    (hG : ∀ k, ∃ (i : K) (f : i ⟶ w.obj (u.obj k)) (g : i ⟶ k),
      G.map f ≫ β.app (u.obj k) ≫ α.app k = G.map g) :
    (α.reindexLimitIso β hF hG).inv = β.reindexLimitMap :=
  (rfl)

end Inverse

end CategoryTheory.NatTrans
