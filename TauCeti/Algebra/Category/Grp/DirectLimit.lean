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
# Direct limits of groups are colimits in `GrpCat`

A directed system of groups `G i`, with transition homomorphisms `f i j : G i →* G j` indexed by a
preorder `ι`, is a functor `ι ⥤ GrpCat`. Mathlib's `DirectLimit G f` carries a group structure,
and the canonical maps `TauCeti.DirectLimit.Monoid.of G f i : G i →* DirectLimit G f` form a
cocone over that functor. When `ι` is directed and nonempty, this cocone is a colimit: its
universal property is `TauCeti.DirectLimit.Monoid.lift`.

So `DirectLimit G f` is a concrete model of the colimit of a directed system of groups, and every
statement about colimit cocones in `GrpCat` applies to it. This parallels Mathlib's
`ModuleCat.directLimitIsColimit` for modules.

## Main declarations

* `TauCeti.GrpCat.directLimitDiagram`: the diagram `ι ⥤ GrpCat` of a directed system of groups.
* `TauCeti.GrpCat.directLimitCocone`: the cocone with apex `DirectLimit G f` and legs the canonical
  maps.
* `TauCeti.GrpCat.directLimitIsColimit`: this cocone is a colimit cocone, whose induced morphisms
  are given by `TauCeti.DirectLimit.Monoid.lift` (`TauCeti.GrpCat.directLimitIsColimit_desc`).
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u

namespace GrpCat

variable {ι : Type u} [Preorder ι] (G : ι → Type u) [∀ i, Group (G i)]
  (f : ∀ i j, i ≤ j → G i →* G j) [DirectedSystem G (f · · ·)]

/-- The diagram `ι ⥤ GrpCat` of a directed system of groups `G i` with transition homomorphisms
`f i j`. -/
@[expose] def directLimitDiagram : ι ⥤ _root_.GrpCat.{u} where
  obj i := _root_.GrpCat.of (G i)
  map hij := _root_.GrpCat.ofHom (f _ _ hij.le)
  map_id i := by
    ext x
    exact DirectedSystem.map_self' f x
  map_comp hij hjk := by
    ext x
    exact (DirectedSystem.map_map' f hij.le hjk.le x).symm

/-- The diagram sends `i` to the group `G i`. -/
@[simp]
theorem directLimitDiagram_obj (i : ι) :
    (directLimitDiagram G f).obj i = _root_.GrpCat.of (G i) :=
  (rfl)

/-- The diagram sends `i ≤ j` to the transition homomorphism `f i j`. -/
@[simp]
theorem directLimitDiagram_map {i j : ι} (hij : i ⟶ j) :
    (directLimitDiagram G f).map hij = _root_.GrpCat.ofHom (f _ _ hij.le) :=
  (rfl)

variable [IsDirectedOrder ι] [Nonempty ι]

/-- The cocone over `TauCeti.GrpCat.directLimitDiagram G f` with apex `DirectLimit G f`, whose legs
are the canonical maps `TauCeti.DirectLimit.Monoid.of G f i`. -/
@[expose] noncomputable def directLimitCocone : Cocone (directLimitDiagram G f) where
  pt := _root_.GrpCat.of (DirectLimit G f)
  ι :=
    { app i := _root_.GrpCat.ofHom (DirectLimit.Monoid.of G f i)
      naturality _ _ hij := by
        ext x
        exact DirectLimit.Monoid.of_f hij.le x }

/-- The apex of the cocone is the direct limit. -/
@[simp]
theorem directLimitCocone_pt : (directLimitCocone G f).pt = _root_.GrpCat.of (DirectLimit G f) :=
  (rfl)

/-- The legs of the cocone are the canonical maps into the direct limit. -/
@[simp]
theorem directLimitCocone_ι_app (i : ι) :
    (directLimitCocone G f).ι.app i = _root_.GrpCat.ofHom (DirectLimit.Monoid.of G f i) :=
  (rfl)

/-- Two morphisms out of `DirectLimit G f` agree once they agree after every leg of
`TauCeti.GrpCat.directLimitCocone G f`. -/
private theorem directLimitCocone_hom_ext {X : _root_.GrpCat.{u}}
    {g₁ g₂ : (directLimitCocone G f).pt ⟶ X}
    (h : ∀ i, (directLimitCocone G f).ι.app i ≫ g₁ = (directLimitCocone G f).ι.app i ≫ g₂) :
    g₁ = g₂ :=
  _root_.GrpCat.hom_ext <| DirectLimit.Monoid.hom_ext fun i => congr_arg _root_.GrpCat.Hom.hom (h i)

/-- The direct limit of a directed system of groups, indexed by a nonempty directed preorder, is
a colimit of its diagram in `GrpCat`. -/
noncomputable def directLimitIsColimit : IsColimit (directLimitCocone G f) where
  desc s := _root_.GrpCat.ofHom <|
    DirectLimit.Monoid.lift (fun i => (s.ι.app i).hom) fun i j hij x =>
      ConcreteCategory.congr_hom (s.w (homOfLE hij)) x
  fac s i := by
    ext x
    exact DirectLimit.Monoid.lift_of _ _ i x
  uniq s m hm := directLimitCocone_hom_ext G f fun i => by
    rw [hm i]
    symm
    ext x
    exact DirectLimit.Monoid.lift_of _ _ i x

/-- The morphism out of `DirectLimit G f` given by the colimit property is
`TauCeti.DirectLimit.Monoid.lift` of the legs of the target cocone. -/
theorem directLimitIsColimit_desc (s : Cocone (directLimitDiagram G f)) :
    (directLimitIsColimit G f).desc s = _root_.GrpCat.ofHom
      (DirectLimit.Monoid.lift (G := G) (f := f) (P := s.pt) (fun i => (s.ι.app i).hom)
        fun _ _ hij x => ConcreteCategory.congr_hom (s.w (homOfLE hij)) x) :=
  (rfl)

end GrpCat

end TauCeti
