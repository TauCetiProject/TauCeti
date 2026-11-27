/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Constructions.Basic

/-!
# Changing the first factor of a fibre product

A map `g : X₁ → X₂` over `Y`, that is `q ∘ g = p`, induces a continuous map
`X₁ ×_Y Z → X₂ ×_Y Z` of fibre products, `(x, z) ↦ (g x, z)`
(`ContinuousMap.mapPullbackFst`), the case of `ContinuousMap.mapPullback` that is the first-factor
counterpart of `ContinuousMap.mapPullbackSnd`. Its image is the part of `X₂ ×_Y Z` over the image
of `g` (`ContinuousMap.range_mapPullbackFst`), and it is an open embedding when `g` is one
(`ContinuousMap.isOpenEmbedding_mapPullbackFst`). For a space `Z` over `Y` pulled back along a map
of parameter spaces, this includes the pullback over an open part of the parameters into the
pullback over all of them, as for the disk of a single cell among the disks of all cells.

## Main results

* `ContinuousMap.mapPullbackFst`: the map of fibre products induced by a map of first factors.
* `ContinuousMap.range_mapPullbackFst`, `ContinuousMap.isOpenEmbedding_mapPullbackFst`: its image,
  and the open embedding induced by an open embedding.
* `Function.Pullback.ext`: points of a fibre product are equal when their projections are.
-/

public section

open Set Topology

/-- Points of a fibre product are equal when both of their projections are. -/
theorem Function.Pullback.ext {X Y Z : Type*} {f : X → Y} {g : Z → Y} {x y : f.Pullback g}
    (h₁ : x.fst = y.fst) (h₂ : x.snd = y.snd) : x = y :=
  Subtype.ext (Prod.ext h₁ h₂)

@[simp]
theorem Function.Pullback.fst_mk {X Y Z : Type*} {f : X → Y} {g : Z → Y} (z : X × Z)
    (h : f z.1 = g z.2) : Pullback.fst (⟨z, h⟩ : f.Pullback g) = z.1 := (rfl)

@[simp]
theorem Function.Pullback.snd_mk {X Y Z : Type*} {f : X → Y} {g : Z → Y} (z : X × Z)
    (h : f z.1 = g z.2) : Pullback.snd (⟨z, h⟩ : f.Pullback g) = z.2 := (rfl)

section MapPullbackFst

variable {X₁ X₂ Y Z : Type*} [TopologicalSpace X₁] [TopologicalSpace X₂] [TopologicalSpace Z]
  {p : X₁ → Y} {q : X₂ → Y} (g : C(X₁, X₂)) (hg : q ∘ ⇑g = p) (f : Z → Y)

/-- Bundled continuous map `p.Pullback f → q.Pullback f` over `Z` induced by a map
`g : C(X₁, X₂)` over `Y` (`q ∘ g = p`): `(x, z) ↦ (g x, z)`. -/
def ContinuousMap.mapPullbackFst : C(p.Pullback f, q.Pullback f) :=
  ContinuousMap.mapPullback (g₁ := f) (g₂ := f) g id (.id Z) hg rfl

@[simp] theorem ContinuousMap.coe_mapPullbackFst_apply (x : p.Pullback f) :
    (ContinuousMap.mapPullbackFst g hg f x).val = (g x.val.1, x.val.2) :=
  ContinuousMap.coe_mapPullback_apply _ _ _ _ _ x

@[simp] theorem ContinuousMap.fst_mapPullbackFst (x : p.Pullback f) :
    (ContinuousMap.mapPullbackFst g hg f x).fst = g x.fst :=
  congrArg Prod.fst (ContinuousMap.coe_mapPullbackFst_apply g hg f x)

@[simp] theorem ContinuousMap.snd_mapPullbackFst (x : p.Pullback f) :
    (ContinuousMap.mapPullbackFst g hg f x).snd = x.snd :=
  congrArg Prod.snd (ContinuousMap.coe_mapPullbackFst_apply g hg f x)

@[simp] theorem ContinuousMap.pullbackFst_comp_mapPullbackFst :
    (ContinuousMap.pullbackFst q f).comp (ContinuousMap.mapPullbackFst g hg f) =
      g.comp (ContinuousMap.pullbackFst p f) := by
  ext : 1; simp

@[simp] theorem ContinuousMap.pullbackSnd_comp_mapPullbackFst :
    (ContinuousMap.pullbackSnd q f).comp (ContinuousMap.mapPullbackFst g hg f) =
      ContinuousMap.pullbackSnd p f := by
  ext : 1; simp

/-- The points of `q.Pullback f` over the image of `g` are exactly the image of the map induced
by `g`. -/
theorem ContinuousMap.range_mapPullbackFst :
    range (ContinuousMap.mapPullbackFst g hg f) = Function.Pullback.fst ⁻¹' range g := by
  refine Subset.antisymm ?_ fun y ⟨x, hx⟩ ↦
    ⟨⟨(x, y.snd), (congrFun hg x).symm.trans ((congrArg q hx).trans y.property)⟩,
      Function.Pullback.ext ((fst_mapPullbackFst g hg f _).trans hx) (snd_mapPullbackFst g hg f _)⟩
  rintro _ ⟨x, rfl⟩
  exact ⟨x.fst, (fst_mapPullbackFst g hg f x).symm⟩

/-- The map induced by an open embedding of first factors is an open embedding. -/
theorem ContinuousMap.isOpenEmbedding_mapPullbackFst (hg' : IsOpenEmbedding g) :
    IsOpenEmbedding (ContinuousMap.mapPullbackFst g hg f) := by
  have h : Subtype.val ∘ ⇑(ContinuousMap.mapPullbackFst g hg f) = Prod.map g id ∘ Subtype.val :=
    funext (ContinuousMap.coe_mapPullbackFst_apply g hg f)
  refine ⟨(IsEmbedding.subtypeVal (p := fun z : X₂ × Z ↦ q z.1 = f z.2)).of_comp_iff.1 ?_, ?_⟩
  · rw [h]
    exact (hg'.isEmbedding.prodMap IsEmbedding.id).comp IsEmbedding.subtypeVal
  · rw [range_mapPullbackFst]
    exact hg'.isOpen_range.preimage Function.Pullback.continuous_fst

end MapPullbackFst
