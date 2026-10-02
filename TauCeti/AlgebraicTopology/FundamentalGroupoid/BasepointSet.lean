/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# The fundamental groupoid on a set of basepoints

For a set `S` of points of a topological space `X`, the fundamental groupoid of `X` on `S` is the
full subgroupoid of the fundamental groupoid of `X` whose objects are the points of `S`: its
morphisms from `s` to `t` are the homotopy classes of paths in `X` from `s` to `t`. Choosing `S`
to meet every path component of the spaces involved keeps the groupoid small while losing no
information, which is what makes the groupoid Seifert--van Kampen theorem a practical tool for
calculations, for instance on the circle covered by two arcs, where two basepoints are needed.

## Main declarations

* `TauCeti.FundamentalGroupoidOn`: the fundamental groupoid of `X` on a set of basepoints.
* `TauCeti.FundamentalGroupoidOn.incl`: its inclusion into the fundamental groupoid of `X`.
* `TauCeti.FundamentalGroupoidOn.map`: the functor induced by a continuous map sending one set of
  basepoints into another, with `map_id` and `map_comp`.

## References

* R. Brown, *Topology and Groupoids*, 3rd ed., Section 6.7.
-/

public section

noncomputable section

open CategoryTheory Set

namespace TauCeti

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The fundamental groupoid of `X` on a set `S` of basepoints: the full subgroupoid of the
fundamental groupoid of `X` whose objects are the points of `S`. -/
abbrev FundamentalGroupoidOn (S : Set X) : Type _ :=
  InducedCategory (FundamentalGroupoid X) fun s : S ↦ FundamentalGroupoid.mk (s : X)

namespace FundamentalGroupoidOn

variable {S : Set X} {T : Set Y} {U : Set Z}

variable (S) in
/-- The inclusion of the fundamental groupoid on `S` into the fundamental groupoid of `X`. -/
abbrev incl : FundamentalGroupoidOn S ⥤ FundamentalGroupoid X :=
  inducedFunctor _

/-- The functor between fundamental groupoids on sets of basepoints induced by a continuous map
`f` sending `S` into `T`. -/
@[expose]
def map (f : C(X, Y)) (hf : MapsTo f S T) : FundamentalGroupoidOn S ⥤ FundamentalGroupoidOn T where
  obj s := ⟨f s.1, hf s.2⟩
  map g := InducedCategory.homMk ((FundamentalGroupoid.map f).map g.hom)
  map_id _ := InducedCategory.hom_ext ((FundamentalGroupoid.map f).map_id _)
  map_comp _ _ := InducedCategory.hom_ext ((FundamentalGroupoid.map f).map_comp _ _)

@[simp]
theorem map_obj (f : C(X, Y)) (hf : MapsTo f S T) (s : FundamentalGroupoidOn S) :
    (map f hf).obj s = ⟨f s.1, hf s.2⟩ :=
  (rfl)

@[simp]
theorem map_map_hom (f : C(X, Y)) (hf : MapsTo f S T) {s t : FundamentalGroupoidOn S}
    (g : s ⟶ t) : ((map f hf).map g).hom = (FundamentalGroupoid.map f).map g.hom :=
  (rfl)

/-- The functor induced by `f` is compatible with the inclusions. -/
theorem map_comp_incl (f : C(X, Y)) (hf : MapsTo f S T) :
    map f hf ⋙ incl T = incl S ⋙ FundamentalGroupoid.map f :=
  (rfl)

/-- The identity map induces the identity functor. -/
@[simp]
theorem map_id : map (.id X) (mapsTo_id S) = 𝟭 _ := by
  -- Both functors are the identity on objects, so it suffices to compare them on morphisms.
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) fun s t g ↦ heq_of_eq ?_
  obtain ⟨g⟩ := g
  ext
  induction g using Path.Homotopic.Quotient.ind
  rfl

/-- The functor induced by a composite is the composite of the induced functors. -/
theorem map_comp (g : C(Y, Z)) (f : C(X, Y)) (hg : MapsTo g T U) (hf : MapsTo f S T) :
    map (g.comp f) (hg.comp hf) = map f hf ⋙ map g hg := by
  -- Both functors send `s` to `g (f s)`, so it suffices to compare them on morphisms.
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) fun s t p ↦ heq_of_eq ?_
  ext
  exact FundamentalGroupoid.map_comp_map g f p.hom

end FundamentalGroupoidOn

end TauCeti
