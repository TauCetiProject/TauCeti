/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.IsLimit
public import TauCeti.Algebra.Colimit.DirectLimit

/-!
# The direct limit of groups is a colimit in `GrpCat`

A directed system of groups `G i`, indexed by a directed preorder `ι`, with transition maps
`f i j : G i →* G j`, is a diagram `ι ⥤ GrpCat`. Mathlib's generic `DirectLimit G f`, with the
canonical maps `DirectLimit.Monoid.of G f i`, is a cocone over it, and the universal property
`DirectLimit.Monoid.lift` shows that this cocone is a colimit. Results about colimits of filtered
diagrams in `GrpCat` therefore apply to `DirectLimit G f`, and conversely `DirectLimit G f` is a
concrete model of the colimit of a directed system of groups.

## Main definitions

* `TauCeti.GrpCat.directLimitDiagram G f`: the diagram `ι ⥤ GrpCat` of a directed system of
  groups.
* `TauCeti.GrpCat.directLimitCocone G f`: the cocone with apex `DirectLimit G f`.
* `TauCeti.GrpCat.directLimitIsColimit G f`: this cocone is a colimit.

This follows `ModuleCat.directLimitIsColimit`, the corresponding statement for modules.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

namespace GrpCat

variable {ι : Type v} [Preorder ι] (G : ι → Type (max u v)) [∀ i, Group (G i)]
  (f : ∀ i j, i ≤ j → G i →* G j) [DirectedSystem G (f · · ·)]

/-- The diagram in `GrpCat` of a directed system of groups. -/
@[expose, simps]
def directLimitDiagram : ι ⥤ _root_.GrpCat.{max u v} where
  obj i := .of (G i)
  map hij := _root_.GrpCat.ofHom (f _ _ hij.le)
  -- In the proofs below, `GrpCat.ofHom`, identities and composition in `GrpCat` evaluate at `x` by
  -- `rfl`, and so do the diagram and cocone, whose objects and maps are `GrpCat.of` and
  -- `GrpCat.ofHom`. The goals are stated over `(directLimitDiagram G f).obj i` rather than
  -- `GrpCat.of (G i)`, so `GrpCat.hom_comp` cannot rewrite them; `exact` closes them up to this
  -- unfolding.
  map_id i := by
    ext x
    exact DirectedSystem.map_self (f := (f · · ·)) x
  map_comp hij hjk := by
    ext x
    exact (DirectedSystem.map_map (f := (f · · ·)) hij.le hjk.le x).symm

variable [IsDirectedOrder ι] [Nonempty ι]

/-- The cocone over the diagram of a directed system of groups with apex the direct limit
`DirectLimit G f` and legs the canonical maps `DirectLimit.Monoid.of G f i`. -/
@[expose, simps]
noncomputable def directLimitCocone : Cocone (directLimitDiagram G f) where
  pt := .of (DirectLimit G f)
  ι :=
    { app i := _root_.GrpCat.ofHom (DirectLimit.Monoid.of G f i)
      naturality i j hij := by
        ext x
        -- Up to the `rfl` unfolding of `GrpCat` above, this is `of_f`.
        exact DirectLimit.Monoid.of_f hij.le x }

/-- The direct limit of a directed system of groups is a colimit in `GrpCat`. -/
@[expose, simps]
noncomputable def directLimitIsColimit : IsColimit (directLimitCocone G f) where
  -- The compatibility of the legs `s.ι.app i` is the naturality `s.w` evaluated at `x`, since the
  -- diagram's maps are the transition maps `f i j` by `rfl`.
  desc s := _root_.GrpCat.ofHom <|
    DirectLimit.Monoid.lift G f (fun i => (s.ι.app i).hom) fun i j hij x =>
      ConcreteCategory.congr_hom (s.w (homOfLE hij)) x
  fac s i := by
    ext x
    -- Up to the `rfl` unfolding of `GrpCat` composition and `directLimitCocone`, this is `lift_of`.
    exact DirectLimit.Monoid.lift_of _ _ i x
  uniq s m hm := by
    ext1
    -- `(m ≫ ...).hom` is `m.hom.comp (of G f i)` by `rfl`, so `hm i` gives agreement on each
    -- component; the named arguments fix the source and target of `lift_comp_of`.
    exact DirectLimit.Monoid.hom_ext fun i => congr(($(hm i)).hom).trans
      (DirectLimit.Monoid.lift_comp_of (G := G) (f := f) (P := s.pt)
        (fun j => (s.ι.app j).hom) _ i).symm

end GrpCat

end TauCeti
