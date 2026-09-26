/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Continuous.TopRep
public import TauCeti.Algebra.Category.ModuleCat.Topology.RestrictScalars

/-!
# Forgetting the scalars of a topological representation

A continuous representation of a monoid `G` on a topological `R`-module `V` is in particular a
continuous representation on the underlying topological abelian group, that is on `V` as a
topological `ℤ`-module for the canonical action of `ℤ`, because every operator is additive and
continuous. This file packages that observation at the three levels at which Mathlib states
continuous representation theory: `ContRepresentation.restrictScalarsInt` on representations,
`ContIntertwiningMap.restrictScalarsInt` on continuous intertwining maps, and the functor
`TopRep.restrictScalarsInt : TopRep k G ⥤ TopRep ℤ G` on the category of topological
representations. It then records that the two functors from which Mathlib builds continuous
cohomology, the coinduction `TopRep.coind₁Functor` and the invariants `TopRep.invariantsFunctor`,
commute with forgetting the scalars: the coinduced representation of the underlying additive
representation is the underlying additive representation of the coinduced one, on the nose on the
function space `C(G, V)`, and the invariants of the underlying additive representation are the
underlying topological abelian group of the invariants.

The reason for stopping at `ℤ` is explained in
`TauCeti.Algebra.Category.ModuleCat.Topology.RestrictScalars`: only the canonical `ℤ`-module
structure exists on every topological module without a choice.

## Main definitions

* `ContRepresentation.restrictScalarsInt`, `ContIntertwiningMap.restrictScalarsInt`: a continuous
  representation, and a continuous intertwining map, read over `ℤ`.
* `TopRep.restrictScalarsInt`: the functor `TopRep k G ⥤ TopRep ℤ G` forgetting the scalars.
* `TopRep.coind₁RestrictScalarsIntIso`: coinduction commutes with forgetting the scalars.
* `TopRep.invariantsRestrictScalarsIntIso`: taking invariants commutes with forgetting the
  scalars.

## Main results

* `TopRep.coind₁ι_comp_coind₁RestrictScalarsIntIso_hom` and
  `TopRep.coind₁Functor_map_comp_coind₁RestrictScalarsIntIso_hom`: the identification of the
  coinduced representations is compatible with the unit `TopRep.coind₁ι` and with the maps
  induced by `TopRep.coind₁Functor`.
* `TopRep.invariantsRestrictScalarsIntIso_hom_comp_map`: the identification of the invariants is
  compatible with the maps induced by `TopRep.invariantsFunctor`.
-/

public section

open CategoryTheory ContRepresentation

/-! ### Continuous representations and intertwining maps -/

namespace ContRepresentation

variable {R : Type*} [Ring R] {G : Type*} [Monoid G] {V W : Type*}
  [AddCommGroup V] [Module R V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [AddCommGroup W] [Module R W] [TopologicalSpace W] [IsTopologicalAddGroup W]

/-- A continuous representation on a topological `R`-module, read as a continuous representation
on the underlying topological abelian group: each operator is restricted to a continuous
`ℤ`-linear map. The body is exposed because the point of the construction is that the operators
are the same functions as before, and a consumer identifying the action of `π.restrictScalarsInt`
with that of `π`, for instance through `TopRep.distribMulAction`, needs that identification to be
definitional. -/
@[expose] def restrictScalarsInt (π : ContRepresentation R G V) : ContRepresentation ℤ G V :=
  ofMonoidHom
    { toFun g := (π g).restrictScalars ℤ
      map_one' := ContinuousLinearMap.ext fun v ↦ by simp
      map_mul' g h := ContinuousLinearMap.ext fun v ↦ by simp }

/-- The operators of `π.restrictScalarsInt` are those of `π`. -/
@[simp]
theorem restrictScalarsInt_apply (π : ContRepresentation R G V) (g : G) (v : V) :
    π.restrictScalarsInt g v = π g v :=
  (rfl)

variable {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}

/-- A continuous intertwining map between representations on topological `R`-modules, read as a
continuous intertwining map between the underlying additive representations. -/
def _root_.ContIntertwiningMap.restrictScalarsInt (f : π₁ →ⁱL π₂) :
    π₁.restrictScalarsInt →ⁱL π₂.restrictScalarsInt where
  __ := f.toContinuousLinearMap.restrictScalars ℤ
  isIntertwining' g :=
    ContinuousLinearMap.ext fun v ↦ DFunLike.congr_fun (f.isIntertwining' g) v

/-- Restricting the scalars of an intertwining map does not change its underlying function. -/
@[simp]
theorem _root_.ContIntertwiningMap.restrictScalarsInt_apply (f : π₁ →ⁱL π₂) (v : V) :
    f.restrictScalarsInt v = f v :=
  (rfl)

end ContRepresentation

namespace TopRep

/-! ### The functor on topological representations -/

section Monoid

variable {k : Type*} [Ring k] [TopologicalSpace k] {G : Type*} [Monoid G]

/-- Forgetting the scalars of a topological representation: the functor `TopRep k G ⥤ TopRep ℤ G`
sending a representation on a topological `k`-module to the same representation on the underlying
topological abelian group. The body is exposed because a consumer must see that the underlying
type of `restrictScalarsInt.obj X` is that of `X` before it can name its elements. -/
@[expose] def restrictScalarsInt : TopRep k G ⥤ TopRep ℤ G where
  obj X := of X.ρ.restrictScalarsInt
  map f := ofHom f.hom.restrictScalarsInt

/-- The underlying type of a representation is unchanged by forgetting the scalars. -/
@[simp]
theorem restrictScalarsInt_obj_V (X : TopRep k G) : (restrictScalarsInt.obj X).V = X.V :=
  (rfl)

/-- The operators of a representation are unchanged by forgetting the scalars. -/
@[simp]
theorem restrictScalarsInt_obj_ρ_apply (X : TopRep k G) (g : G) (x : X.V) :
    (restrictScalarsInt.obj X).ρ g x = X.ρ g x :=
  (rfl)

/-- The underlying function of a morphism is unchanged by forgetting the scalars. -/
-- The argument is typed by the domain of `restrictScalarsInt.map f`, so that `simp` can use the
-- lemma: `(restrictScalarsInt.obj X).V` is `X.V` only after unfolding `restrictScalarsInt`.
@[simp]
theorem restrictScalarsInt_map_hom_apply {X Y : TopRep k G} (f : X ⟶ Y)
    (x : (restrictScalarsInt.obj X).V) :
    (restrictScalarsInt.map f).hom x = f.hom x :=
  (rfl)

instance : (restrictScalarsInt (k := k) (G := G)).Additive where
  map_add := rfl

/-- Forgetting the scalars preserves discreteness of the underlying type. This is
`TopRep.restrictScalarsInt_obj_V` read as an instance: the equality holds by definition but not
at reducible transparency, so instance search cannot see through the functor on its own. -/
instance (X : TopRep k G) [DiscreteTopology X.V] : DiscreteTopology (restrictScalarsInt.obj X).V :=
  ‹DiscreteTopology X.V›

end Monoid

/-! ### Compatibility with coinduction and invariants -/

section Coinduction

variable {k : Type*} [Ring k] [TopologicalSpace k] {G : Type*} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

/-- Coinduction commutes with forgetting the scalars: both sides are the representation of `G` on
`C(G, X.V)` by `g • f = x ↦ ρ(g) (f (g⁻¹ x))`, read over `ℤ`. -/
def coind₁RestrictScalarsIntIso (X : TopRep k G) :
    (restrictScalarsInt.obj X).coind₁ ≅ restrictScalarsInt.obj X.coind₁ where
  hom := ofHom
    { toFun := id
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      cont := continuous_id
      isIntertwining' _ := rfl }
  inv := ofHom
    { toFun := id
      map_add' _ _ := rfl
      map_smul' _ _ := rfl
      cont := continuous_id
      isIntertwining' _ := rfl }

/-- `coind₁RestrictScalarsIntIso` is the identity on the function space `C(G, X.V)`. -/
-- The argument is typed by the domain of the map, as in `restrictScalarsInt_map_hom_apply`.
@[simp]
theorem coind₁RestrictScalarsIntIso_hom_apply (X : TopRep k G)
    (f : C(G, (restrictScalarsInt.obj X).V)) :
    (coind₁RestrictScalarsIntIso X).hom.hom f = f :=
  (rfl)

/-- The inverse of `coind₁RestrictScalarsIntIso` is the identity on the function space
`C(G, X.V)`. -/
@[simp]
theorem coind₁RestrictScalarsIntIso_inv_apply (X : TopRep k G) (f : C(G, X.V)) :
    (coind₁RestrictScalarsIntIso X).inv.hom f = f :=
  (rfl)

/-- The identification of the coinduced representations is compatible with the unit
`TopRep.coind₁ι`, the inclusion of a representation as the constant functions. -/
-- Not a simp lemma: the unit lives in `TopRep.{max v w}`, so the carrier universe of `X` occurs
-- in every constant of the left-hand side only as `max v w`, which `simp` cannot instantiate.
@[reassoc]
theorem coind₁ι_comp_coind₁RestrictScalarsIntIso_hom (X : TopRep k G) :
    ofHom (restrictScalarsInt.obj X).ρ.coind₁ι ≫ (coind₁RestrictScalarsIntIso X).hom =
      restrictScalarsInt.map (ofHom X.ρ.coind₁ι) :=
  (rfl)

/-- The identification of the coinduced representations is compatible with the maps induced by
`TopRep.coind₁Functor`. -/
@[reassoc (attr := simp)]
theorem coind₁Functor_map_comp_coind₁RestrictScalarsIntIso_hom {X Y : TopRep k G} (f : X ⟶ Y) :
    (coind₁Functor ℤ G).map (restrictScalarsInt.map f) ≫ (coind₁RestrictScalarsIntIso Y).hom =
      (coind₁RestrictScalarsIntIso X).hom ≫ restrictScalarsInt.map ((coind₁Functor k G).map f) :=
  (rfl)

end Coinduction

section Invariants

variable {k : Type*} [Ring k] [TopologicalSpace k] {G : Type*} [Group G]

/-- Taking invariants commutes with forgetting the scalars, as topological `ℤ`-modules: the
invariants of the underlying additive representation are the underlying topological abelian group
of the invariants. -/
def invariantsRestrictScalarsIntEquiv (X : TopRep k G) :
    (restrictScalarsInt.obj X).invariants ≃L[ℤ]
      TopModuleCat.restrictScalarsInt.obj X.invariants where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_induced_rng.2 continuous_subtype_val
  continuous_invFun := continuous_induced_rng.2 continuous_subtype_val

/-- `invariantsRestrictScalarsIntEquiv` is the identity on the underlying elements. -/
@[simp]
theorem coe_invariantsRestrictScalarsIntEquiv_apply (X : TopRep k G)
    (x : (restrictScalarsInt.obj X).invariants) :
    (invariantsRestrictScalarsIntEquiv X x).1 = x.1 :=
  (rfl)

/-- Taking invariants commutes with forgetting the scalars, as an isomorphism in
`TopModuleCat ℤ`. -/
noncomputable def invariantsRestrictScalarsIntIso (X : TopRep k G) :
    (invariantsFunctor ℤ G).obj (restrictScalarsInt.obj X) ≅
      TopModuleCat.restrictScalarsInt.obj ((invariantsFunctor k G).obj X) :=
  TopModuleCat.ofIso (invariantsRestrictScalarsIntEquiv X)

/-- The identification of the invariants is compatible with the maps induced by
`TopRep.invariantsFunctor`. -/
@[reassoc (attr := simp)]
theorem invariantsRestrictScalarsIntIso_hom_comp_map {X Y : TopRep k G} (f : X ⟶ Y) :
    (invariantsRestrictScalarsIntIso X).hom ≫
        TopModuleCat.restrictScalarsInt.map ((invariantsFunctor k G).map f) =
      (invariantsFunctor ℤ G).map (restrictScalarsInt.map f) ≫
        (invariantsRestrictScalarsIntIso Y).hom := by
  ext x
  rfl

end Invariants

end TopRep
