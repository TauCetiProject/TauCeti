/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Topology.KrullDimension
public import TauCeti.AlgebraicGeometry.GroupAction.Orbit.Basic
public import TauCeti.CategoryTheory.Monoidal.Cartesian.FixedPoint
import TauCeti.Topology.KrullDimension.Irreducible

/-!
# Orbits of fixed points of scheme actions

Let a monoid scheme `G` over `S` act on a scheme `X` over `S`, and let `x` be a section of `X`
fixed by `G` in the sense of `TauCeti.IsFixedPoint`: its orbit morphism is constant. Since the
structure morphism of `G` has the unit section, it is surjective, so the geometric orbit of `x`
is exactly the image of the section `x`. When the section is a closed immersion this orbit is
closed and its boundary is empty. Sections are closed immersions when `X` is separated over `S`,
and also, without separatedness, when `S` has a single point, such as the spectrum of a field.

Over a base with one point the orbit of a fixed section is that single point, and it has
dimension zero. Under the trivial action every section is fixed, so every orbit is the image of
its section: over a field, trivial actions have point orbits, and these are closed.

## Main declarations

* `TauCeti.SchemeAction.orbit_eq_range_of_isFixedPoint`: the orbit of a fixed section is its
  image.
* `TauCeti.SchemeAction.isClosed_orbit_of_isFixedPoint` and
  `TauCeti.SchemeAction.orbitBoundary_eq_empty_of_isFixedPoint`: for a closed-immersion section
  this orbit is closed, with empty boundary.
* `TauCeti.SchemeAction.orbit_eq_singleton_of_isFixedPoint` and
  `TauCeti.SchemeAction.topologicalKrullDim_orbit_of_isFixedPoint`: over a base with one point the
  orbit of a fixed section is one point, of dimension zero.
* `TauCeti.SchemeAction.orbit_trivialAction`,
  `TauCeti.SchemeAction.isClosed_orbit_trivialAction` and
  `TauCeti.SchemeAction.orbit_trivialAction_eq_singleton`: orbits of the trivial action.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry

namespace TauCeti.SchemeAction

universe u

variable {S : Scheme.{u}} (G : Over S) {X : Over S}

section Base

variable [MonObj G] [ModObj G X] {x : 𝟙_ (Over S) ⟶ X}

/-- The geometric orbit of a fixed section is the image of the section. -/
theorem orbit_eq_range_of_isFixedPoint (hx : IsFixedPoint G x) :
    orbit G x = Set.range x.left := by
  -- The structure morphism of `G` is surjective, since the unit is a section of it.
  have : Surjective (η[G].left ≫ (toUnit G).left) := by
    rw [← Over.comp_left, toUnit_unique (η[G] ≫ toUnit G) (𝟙 _), Over.id_left]
    infer_instance
  have : Surjective (toUnit G).left := .of_comp η[G].left _
  rw [orbit_def, isFixedPoint_iff.mp hx, Over.comp_left, Scheme.Hom.comp_base, TopCat.coe_comp,
    Set.range_comp, (toUnit G).left.surjective.range_eq, Set.image_univ]

variable [IsClosedImmersion x.left]

/-- The orbit of a fixed section is closed when the section is a closed immersion, for instance
when `X` is separated over `S` (`AlgebraicGeometry.Scheme.Hom.isClosedImmersion_of_comp_eq_id`) or
when `S` has only one point (`TauCeti.isClosedImmersion_section`). -/
theorem isClosed_orbit_of_isFixedPoint (hx : IsFixedPoint G x) : IsClosed (orbit G x) := by
  rw [orbit_eq_range_of_isFixedPoint G hx]
  exact x.left.isClosedEmbedding.isClosed_range

/-- The orbit of a fixed closed-immersion section is its own closure. -/
theorem orbitClosure_eq_orbit_of_isFixedPoint (hx : IsFixedPoint G x) :
    orbitClosure G x = orbit G x := by
  rw [orbitClosure_def, (isClosed_orbit_of_isFixedPoint G hx).closure_eq]

/-- The orbit of a fixed closed-immersion section has empty boundary. -/
theorem orbitBoundary_eq_empty_of_isFixedPoint (hx : IsFixedPoint G x) :
    orbitBoundary G x = ∅ :=
  (isClosed_orbit_iff_orbitBoundary_eq_empty G x).mp (isClosed_orbit_of_isFixedPoint G hx)

end Base

section Point

variable [Subsingleton S] [MonObj G] [ModObj G X] {x : 𝟙_ (Over S) ⟶ X}

/-- Over a base with one point, such as the spectrum of a field, the orbit of a fixed section is
a single point. -/
theorem orbit_eq_singleton_of_isFixedPoint (hx : IsFixedPoint G x) (a : (𝟙_ (Over S)).left) :
    orbit G x = {x.left a} := by
  rw [orbit_eq_range_of_isFixedPoint G hx]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨a, rfl⟩, ?_⟩
  rintro _ ⟨b, rfl⟩
  obtain rfl : b = a := Subsingleton.elim (α := S) _ _
  rfl

/-- Over a base with one point, such as the spectrum of a field, the orbit of a fixed section has
dimension zero. -/
theorem topologicalKrullDim_orbit_of_isFixedPoint [Nonempty S] (hx : IsFixedPoint G x) :
    topologicalKrullDim (orbit G x) = 0 := by
  obtain ⟨a⟩ : Nonempty (𝟙_ (Over S)).left := inferInstanceAs (Nonempty S)
  rw [orbit_eq_singleton_of_isFixedPoint G hx a]
  have := Subtype.irreducibleSpace (isIrreducible_singleton (x := x.left a))
  exact topologicalKrullDim_eq_zero_iff_subsingleton.mpr inferInstance

end Point

section Trivial

variable [MonObj G]

attribute [local instance] ModObj.trivialAction

/-- Under the trivial action, the orbit of a section is its image. -/
theorem orbit_trivialAction (x : 𝟙_ (Over S) ⟶ X) : orbit G x = Set.range x.left :=
  orbit_eq_range_of_isFixedPoint G (isFixedPoint_trivialAction G x)

/-- Under the trivial action, the orbit of a closed-immersion section is closed. -/
theorem isClosed_orbit_trivialAction (x : 𝟙_ (Over S) ⟶ X) [IsClosedImmersion x.left] :
    IsClosed (orbit G x) :=
  isClosed_orbit_of_isFixedPoint G (isFixedPoint_trivialAction G x)

/-- Over a base with one point, such as the spectrum of a field, every orbit of the trivial
action is a single point. -/
theorem orbit_trivialAction_eq_singleton [Subsingleton S] (x : 𝟙_ (Over S) ⟶ X)
    (a : (𝟙_ (Over S)).left) : orbit G x = {x.left a} :=
  orbit_eq_singleton_of_isFixedPoint G (isFixedPoint_trivialAction G x) a

end Trivial

end TauCeti.SchemeAction
