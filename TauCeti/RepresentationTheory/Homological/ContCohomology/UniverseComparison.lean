/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.LowDegree
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero

/-!
# Universe comparison for continuous cohomology in the group's universe

For a topological ring `R : Type u` and a topological group `G : Type v`, Mathlib's coinduced
resolution `TopRep.resolutionX.{u, v, w}`, differential `TopRep.d.{u, v, w}`, homogeneous cochain
complex `TopRep.homogeneousCochains.{u, v, w}`, continuous cohomology
`continuousCohomology.{u, v, w}`, and compatible-pair maps
`ContinuousCohomology.map.{u, v, w}` take coefficients in `TopRep.{max v w, u, v} R G`. When the
coefficient representation `X : TopRep.{v, u, v} R G` already lives in the universe `v` of `G`,
both `w = v` and `w = 0` apply to `X` and take values in the same categories
`TopRep.{v, u, v} R G`, `CochainComplex (TopModuleCat.{v, u} R) ℕ`, and `TopModuleCat.{v, u} R`,
because `max v v` and `max v 0` both reduce definitionally to `v`. Because `TopRep.resolutionX`,
`TopRep.d`, and `ContinuousCohomology.resolutionMap` are defined by recursion on the degree while
parameterized by `w`, however, the two instantiations are not definitionally equal in a general
degree `n : ℕ`.

Since a single coinduction step `TopRep.coind₁` depends on `w` only through `max v w`, induction
on the degree shows that the resolution terms, differentials, shifted resolutions, homogeneous
cochain complexes, cocycle modules, and continuous cohomology modules at `w = v` and `w = 0` are
propositionally equal for every topological group `G` and every `X : TopRep.{v, u, v} R G`.

Rewriting directly along propositional equalities of objects cannot transport typed elements or
morphisms, so this file also packages those identifications as sealed categorical isomorphisms
(`TopRep.homogeneousCochainsUniverseIso`, `TauCeti.ContinuousCohomology.cocyclesUniverseIso`,
`TauCeti.ContinuousCohomology.continuousCohomologyUniverseIso`, and the functor isomorphism
`TauCeti.ContinuousCohomology.continuousCohomologyFunctorUniverseIso`) and records their
compatibility with cocycle inclusions, cohomology classes (`ContinuousCohomology.π` and
`TopRep.cochainClass`), the degree-zero invariants isomorphism (`ContinuousCohomology.zeroIso`),
low-degree homogeneous cochains (`0, 1, 2`), and compatible-pair functoriality
(`ContinuousCohomology.cochainsMap`, `ContinuousCohomology.cocyclesMap`,
`ContinuousCohomology.map`, `TauCeti.ContinuousCohomology.coeffMap`,
`TauCeti.ContinuousCohomology.res`, `TauCeti.ContinuousCohomology.resLE`, and
`TauCeti.ContinuousCohomology.infl`), together with their reduction to the identity when
`G : Type 0`.

## Main definitions

* `TopRep.homogeneousCochainsUniverseIso`: canonical chain isomorphism between
  `TopRep.homogeneousCochains.{u, v, v} X` and `TopRep.homogeneousCochains.{u, v, 0} X`.
* `TauCeti.ContinuousCohomology.cocyclesUniverseIso`: canonical isomorphism between
  `ContinuousCohomology.cocycles.{u, v, v} X n` and `ContinuousCohomology.cocycles.{u, v, 0} X n`.
* `TauCeti.ContinuousCohomology.continuousCohomologyUniverseIso`: canonical isomorphism between
  `continuousCohomology.{u, v, v} n X` and `continuousCohomology.{u, v, 0} n X`.
* `TauCeti.ContinuousCohomology.continuousCohomologyFunctorUniverseIso`: natural isomorphism
  between `continuousCohomologyFunctor.{u, v, v} R G n` and
  `continuousCohomologyFunctor.{u, v, 0} R G n`.

## Main results

* `TopRep.resolutionX_universe_eq`, `TopRep.resolution_universe_eq`,
  `TopRep.resolution'_universe_eq`, `TopRep.homogeneousCochains_universe_eq`: propositional
  equality of the coinduced resolutions and homogeneous cochain complexes at `w = v` and `w = 0`.
* `TauCeti.ContinuousCohomology.cocycles_universe_eq`,
  `TauCeti.ContinuousCohomology.continuousCohomology_universe_eq`: propositional equality of the
  cocycle and continuous cohomology objects at `w = v` and `w = 0`.
* `TauCeti.ContinuousCohomology.π_comp_continuousCohomologyUniverseIso_hom`,
  `TauCeti.ContinuousCohomology.continuousCohomologyUniverseIso_hom_cochainClass`: the cohomology
  comparison carries the class of a cocycle to the class of its image.
* `TauCeti.ContinuousCohomology.continuousCohomologyUniverseIso_hom_comp_zeroIso_hom`: in degree
  zero, the cohomology comparison commutes with `ContinuousCohomology.zeroIso` onto
  `X.ρ.invariants`.
* `TauCeti.ContinuousCohomology.map_comp_continuousCohomologyUniverseIso_hom`,
  `TauCeti.ContinuousCohomology.coeffMap_comp_continuousCohomologyUniverseIso_hom`,
  `TauCeti.ContinuousCohomology.res_comp_continuousCohomologyUniverseIso_hom`,
  `TauCeti.ContinuousCohomology.resLE_comp_continuousCohomologyUniverseIso_hom`,
  `TauCeti.ContinuousCohomology.infl_comp_continuousCohomologyUniverseIso_hom`: naturality with
  respect to compatible pairs, coefficient morphisms, restriction, and inflation.
-/

public section

open CategoryTheory

universe u v

/-! ### Coinduced resolution and homogeneous cochains -/

namespace TopRep

section Resolution

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

-- None of the `.{u, v, v} = .{u, v, 0}` object equalities in this file is marked `@[simp]`:
-- at `v = 0` both sides are syntactically identical, so a `simp` rule would loop.
/-- Every term of the coinduced resolution of `X : TopRep.{v, u, v} R G` at extra universe `v`
equals the corresponding term at extra universe `0`. -/
theorem resolutionX_universe_eq (X : TopRep.{v, u, v} R G) :
    ∀ n : ℕ, TopRep.resolutionX.{u, v, v} X n = TopRep.resolutionX.{u, v, 0} X n
  | 0 => rfl
  | n + 1 => congrArg TopRep.coind₁ (X.resolutionX_universe_eq n)

private theorem d_succ_heq_aux {A₀ B₀ : TopRep.{v, u, v} R G} (h₀ : A₀ = B₀)
    (f : A₀ ⟶ A₀.coind₁) (g : B₀ ⟶ B₀.coind₁) (hfg : f ≍ g) :
    TopRep.ofHom A₀.coind₁.ρ.coind₁ι - (TopRep.coind₁Functor R G).map f ≍
      TopRep.ofHom B₀.coind₁.ρ.coind₁ι - (TopRep.coind₁Functor R G).map g := by
  subst h₀
  cases hfg
  rfl

/-- Every differential of the coinduced resolution of `X : TopRep.{v, u, v} R G` at extra universe
`v` is heterogeneously equal to the corresponding differential at extra universe `0`. -/
theorem d_universe_heq (X : TopRep.{v, u, v} R G) :
    ∀ n : ℕ, TopRep.d.{u, v, v} X n ≍ TopRep.d.{u, v, 0} X n
  | 0 => HEq.rfl
  | n + 1 => by
    rw [TopRep.d_succ, TopRep.d_succ]
    exact d_succ_heq_aux (X.resolutionX_universe_eq n) _ _ (X.d_universe_heq n)

/-- Categorical form of `TopRep.d_universe_heq`: the resolution differentials at extra universes
`v` and `0` intertwine `eqToHom` along `TopRep.resolutionX_universe_eq`. -/
@[reassoc]
theorem d_comp_eqToHom_resolutionX_universe_eq (X : TopRep.{v, u, v} R G) (n : ℕ) :
    TopRep.d.{u, v, v} X n ≫ eqToHom (X.resolutionX_universe_eq (n + 1)) =
      eqToHom (X.resolutionX_universe_eq n) ≫ TopRep.d.{u, v, 0} X n :=
  eq_of_heq ((comp_eqToHom_heq _ _).trans
    ((X.d_universe_heq n).trans (eqToHom_comp_heq _ _).symm))

/-- The coinduced resolution `TopRep.resolution` of `X : TopRep.{v, u, v} R G` at extra universe
`v` equals that at extra universe `0`. -/
theorem resolution_universe_eq (X : TopRep.{v, u, v} R G) :
    TopRep.resolution.{u, v, v} X = TopRep.resolution.{u, v, 0} X :=
  HomologicalComplex.ext (funext X.resolutionX_universe_eq) fun i j hij ↦ by
    dsimp [ComplexShape.up] at hij
    subst hij
    simpa only [TopRep.resolution, CochainComplex.of_d] using
      X.d_comp_eqToHom_resolutionX_universe_eq i

/-- The shifted coinduced resolution `TopRep.resolution'` of `X : TopRep.{v, u, v} R G` at extra
universe `v` equals that at extra universe `0`. -/
theorem resolution'_universe_eq (X : TopRep.{v, u, v} R G) :
    TopRep.resolution'.{u, v, v} X = TopRep.resolution'.{u, v, 0} X :=
  HomologicalComplex.ext (funext fun n ↦ X.resolutionX_universe_eq (n + 1)) fun i j hij ↦ by
    dsimp [ComplexShape.up] at hij
    subst hij
    simpa only [TopRep.resolution', CochainComplex.of_d, TopRep.resolution'd_eq] using
      X.d_comp_eqToHom_resolutionX_universe_eq (i + 1)

/-- **Equality of homogeneous cochain complexes across the extra universe.** For
`X : TopRep.{v, u, v} R G`, the complex `TopRep.homogeneousCochains` formed at extra universe `v`
equals that formed at extra universe `0`. -/
theorem homogeneousCochains_universe_eq (X : TopRep.{v, u, v} R G) :
    TopRep.homogeneousCochains.{u, v, v} X = TopRep.homogeneousCochains.{u, v, 0} X :=
  congrArg (((TopRep.invariantsFunctor R G).mapHomologicalComplex _).obj)
    X.resolution'_universe_eq

/-- **Canonical chain isomorphism between homogeneous cochain complexes** of
`X : TopRep.{v, u, v} R G` formed at extra universe `v` and at extra universe `0`. -/
noncomputable def homogeneousCochainsUniverseIso (X : TopRep.{v, u, v} R G) :
    TopRep.homogeneousCochains.{u, v, v} X ≅ TopRep.homogeneousCochains.{u, v, 0} X :=
  eqToIso X.homogeneousCochains_universe_eq

/-- Defining equation of `TopRep.homogeneousCochainsUniverseIso` as `eqToIso` along
`TopRep.homogeneousCochains_universe_eq`. -/
theorem homogeneousCochainsUniverseIso_def (X : TopRep.{v, u, v} R G) :
    X.homogeneousCochainsUniverseIso = eqToIso X.homogeneousCochains_universe_eq :=
  (rfl)

/-- Degree-`n` forward component of `TopRep.homogeneousCochainsUniverseIso` as `eqToHom`. -/
theorem homogeneousCochainsUniverseIso_hom_f (X : TopRep.{v, u, v} R G) (n : ℕ) :
    X.homogeneousCochainsUniverseIso.hom.f n =
      eqToHom (congrArg (HomologicalComplex.X · n) X.homogeneousCochains_universe_eq) :=
  eqToHom_map (HomologicalComplex.eval _ _ n) X.homogeneousCochains_universe_eq

/-- Degree-`n` inverse component of `TopRep.homogeneousCochainsUniverseIso` as `eqToHom`. -/
theorem homogeneousCochainsUniverseIso_inv_f (X : TopRep.{v, u, v} R G) (n : ℕ) :
    X.homogeneousCochainsUniverseIso.inv.f n =
      eqToHom (congrArg (HomologicalComplex.X · n) X.homogeneousCochains_universe_eq.symm) :=
  eqToHom_map (HomologicalComplex.eval _ _ n) X.homogeneousCochains_universe_eq.symm

/-- In degree `0`, the two homogeneous cochain modules are definitionally identical and the forward
comparison is the identity morphism. -/
@[simp]
theorem homogeneousCochainsUniverseIso_hom_f_zero (X : TopRep.{v, u, v} R G) :
    X.homogeneousCochainsUniverseIso.hom.f 0 = 𝟙 _ :=
  (X.homogeneousCochainsUniverseIso_hom_f 0).trans (eqToHom_refl _ _)

/-- In degree `0`, the inverse homogeneous cochain comparison is the identity morphism. -/
@[simp]
theorem homogeneousCochainsUniverseIso_inv_f_zero (X : TopRep.{v, u, v} R G) :
    X.homogeneousCochainsUniverseIso.inv.f 0 = 𝟙 _ :=
  (X.homogeneousCochainsUniverseIso_inv_f 0).trans (eqToHom_refl _ _)

/-- In degree `1`, the two homogeneous cochain modules are definitionally identical and the forward
comparison is the identity morphism. -/
@[simp]
theorem homogeneousCochainsUniverseIso_hom_f_one (X : TopRep.{v, u, v} R G) :
    X.homogeneousCochainsUniverseIso.hom.f 1 = 𝟙 _ :=
  (X.homogeneousCochainsUniverseIso_hom_f 1).trans (eqToHom_refl _ _)

/-- In degree `1`, the inverse homogeneous cochain comparison is the identity morphism. -/
@[simp]
theorem homogeneousCochainsUniverseIso_inv_f_one (X : TopRep.{v, u, v} R G) :
    X.homogeneousCochainsUniverseIso.inv.f 1 = 𝟙 _ :=
  (X.homogeneousCochainsUniverseIso_inv_f 1).trans (eqToHom_refl _ _)

/-- In degree `2`, the two homogeneous cochain modules are definitionally identical and the forward
comparison is the identity morphism. -/
@[simp]
theorem homogeneousCochainsUniverseIso_hom_f_two (X : TopRep.{v, u, v} R G) :
    X.homogeneousCochainsUniverseIso.hom.f 2 = 𝟙 _ :=
  (X.homogeneousCochainsUniverseIso_hom_f 2).trans (eqToHom_refl _ _)

/-- In degree `2`, the inverse homogeneous cochain comparison is the identity morphism. -/
@[simp]
theorem homogeneousCochainsUniverseIso_inv_f_two (X : TopRep.{v, u, v} R G) :
    X.homogeneousCochainsUniverseIso.inv.f 2 = 𝟙 _ :=
  (X.homogeneousCochainsUniverseIso_inv_f 2).trans (eqToHom_refl _ _)

end Resolution

section ZeroUniverse

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type 0} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Over a group `G : Type 0`, the extra universes `v` and `0` coincide and
`TopRep.homogeneousCochainsUniverseIso` is the identity isomorphism. -/
@[simp]
theorem homogeneousCochainsUniverseIso_zero_univ (X : TopRep.{0, u, 0} R G) :
    X.homogeneousCochainsUniverseIso = Iso.refl _ := by
  simp [homogeneousCochainsUniverseIso_def]

end ZeroUniverse

end TopRep

/-! ### Cocycles, continuous cohomology, classes, and functoriality -/

namespace TauCeti.ContinuousCohomology

section Comparison

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- **Equality of cocycle modules across the extra universe.** For `X : TopRep.{v, u, v} R G`,
`ContinuousCohomology.cocycles` in degree `n` at extra universe `v` equals that at extra universe
`0`. -/
theorem cocycles_universe_eq (n : ℕ) (X : TopRep.{v, u, v} R G) :
    _root_.ContinuousCohomology.cocycles.{u, v, v} X n =
      _root_.ContinuousCohomology.cocycles.{u, v, 0} X n :=
  congrArg (HomologicalComplex.cycles · n) X.homogeneousCochains_universe_eq

/-- **Canonical isomorphism of continuous cocycles** of `X : TopRep.{v, u, v} R G` in degree `n`
between extra universes `v` and `0`. -/
noncomputable def cocyclesUniverseIso (n : ℕ) (X : TopRep.{v, u, v} R G) :
    _root_.ContinuousCohomology.cocycles.{u, v, v} X n ≅
      _root_.ContinuousCohomology.cocycles.{u, v, 0} X n :=
  eqToIso (cocycles_universe_eq n X)

/-- Defining equation of `cocyclesUniverseIso` as `eqToIso` along `cocycles_universe_eq`. -/
theorem cocyclesUniverseIso_def (n : ℕ) (X : TopRep.{v, u, v} R G) :
    cocyclesUniverseIso n X = eqToIso (cocycles_universe_eq n X) :=
  (rfl)

/-- The forward cocycle comparison is the map on cycles induced by
`TopRep.homogeneousCochainsUniverseIso`. -/
@[simp]
theorem cyclesMap_homogeneousCochainsUniverseIso_hom (n : ℕ) (X : TopRep.{v, u, v} R G) :
    HomologicalComplex.cyclesMap X.homogeneousCochainsUniverseIso.hom n =
      (cocyclesUniverseIso n X).hom := by
  rw [TopRep.homogeneousCochainsUniverseIso_def, cocyclesUniverseIso_def, eqToIso.hom, eqToIso.hom]
  exact eqToHom_map (HomologicalComplex.cyclesFunctor (TopModuleCat R) (ComplexShape.up ℕ) n)
    X.homogeneousCochains_universe_eq

/-- The inverse cocycle comparison is the map on cycles induced by the inverse of
`TopRep.homogeneousCochainsUniverseIso`. -/
@[simp]
theorem cyclesMap_homogeneousCochainsUniverseIso_inv (n : ℕ) (X : TopRep.{v, u, v} R G) :
    HomologicalComplex.cyclesMap X.homogeneousCochainsUniverseIso.inv n =
      (cocyclesUniverseIso n X).inv := by
  rw [TopRep.homogeneousCochainsUniverseIso_def, cocyclesUniverseIso_def, eqToIso.inv, eqToIso.inv]
  exact eqToHom_map (HomologicalComplex.cyclesFunctor (TopModuleCat R) (ComplexShape.up ℕ) n)
    X.homogeneousCochains_universe_eq.symm

/-- **Equality of continuous cohomology modules across the extra universe.** For
`X : TopRep.{v, u, v} R G`, `continuousCohomology` in degree `n` at extra universe `v` equals that
at extra universe `0`. -/
theorem continuousCohomology_universe_eq (n : ℕ) (X : TopRep.{v, u, v} R G) :
    continuousCohomology.{u, v, v} n X = continuousCohomology.{u, v, 0} n X :=
  congrArg (HomologicalComplex.homology · n) X.homogeneousCochains_universe_eq

/-- **Canonical isomorphism of continuous cohomology** of `X : TopRep.{v, u, v} R G` in degree `n`
between extra universes `v` and `0`. -/
noncomputable def continuousCohomologyUniverseIso (n : ℕ) (X : TopRep.{v, u, v} R G) :
    continuousCohomology.{u, v, v} n X ≅ continuousCohomology.{u, v, 0} n X :=
  eqToIso (continuousCohomology_universe_eq n X)

/-- Defining equation of `continuousCohomologyUniverseIso` as `eqToIso` along
`continuousCohomology_universe_eq`. -/
theorem continuousCohomologyUniverseIso_def (n : ℕ) (X : TopRep.{v, u, v} R G) :
    continuousCohomologyUniverseIso n X = eqToIso (continuousCohomology_universe_eq n X) :=
  (rfl)

/-- The forward continuous-cohomology comparison is the map on homology induced by
`TopRep.homogeneousCochainsUniverseIso`. -/
@[simp]
theorem homologyMap_homogeneousCochainsUniverseIso_hom (n : ℕ) (X : TopRep.{v, u, v} R G) :
    HomologicalComplex.homologyMap X.homogeneousCochainsUniverseIso.hom n =
      (continuousCohomologyUniverseIso n X).hom := by
  rw [TopRep.homogeneousCochainsUniverseIso_def, continuousCohomologyUniverseIso_def, eqToIso.hom,
    eqToIso.hom]
  exact eqToHom_map (HomologicalComplex.homologyFunctor (TopModuleCat R) (ComplexShape.up ℕ) n)
    X.homogeneousCochains_universe_eq

/-- The inverse continuous-cohomology comparison is the map on homology induced by the inverse of
`TopRep.homogeneousCochainsUniverseIso`. -/
@[simp]
theorem homologyMap_homogeneousCochainsUniverseIso_inv (n : ℕ) (X : TopRep.{v, u, v} R G) :
    HomologicalComplex.homologyMap X.homogeneousCochainsUniverseIso.inv n =
      (continuousCohomologyUniverseIso n X).inv := by
  rw [TopRep.homogeneousCochainsUniverseIso_def, continuousCohomologyUniverseIso_def, eqToIso.inv,
    eqToIso.inv]
  exact eqToHom_map (HomologicalComplex.homologyFunctor (TopModuleCat R) (ComplexShape.up ℕ) n)
    X.homogeneousCochains_universe_eq.symm

-- Not `@[simp]`: `simp` rewrites the implicit codomain `(TopRep.homogeneousCochains X).X n` of
-- `≫` through `CategoryTheory.Functor.mapHomologicalComplex_obj_X`, so the left-hand side is not
-- in `simp`-normal form; use with `rw`.
/-- The cocycle comparison commutes with the inclusion `HomologicalComplex.iCycles` into
homogeneous cochains. -/
@[reassoc]
theorem cocyclesUniverseIso_hom_comp_iCycles (n : ℕ) (X : TopRep.{v, u, v} R G) :
    (cocyclesUniverseIso n X).hom ≫ (TopRep.homogeneousCochains.{u, v, 0} X).iCycles n =
      (TopRep.homogeneousCochains.{u, v, v} X).iCycles n ≫
        X.homogeneousCochainsUniverseIso.hom.f n := by
  rw [← cyclesMap_homogeneousCochainsUniverseIso_hom, HomologicalComplex.cyclesMap_i]

-- Not `@[simp]`, for the same reason as `cocyclesUniverseIso_hom_comp_iCycles`.
/-- Inverse form of `cocyclesUniverseIso_hom_comp_iCycles`: the inverse cocycle comparison
intertwines the inclusions into homogeneous cochains. -/
@[reassoc]
theorem cocyclesUniverseIso_inv_comp_iCycles (n : ℕ) (X : TopRep.{v, u, v} R G) :
    (cocyclesUniverseIso n X).inv ≫ (TopRep.homogeneousCochains.{u, v, v} X).iCycles n =
      (TopRep.homogeneousCochains.{u, v, 0} X).iCycles n ≫
        X.homogeneousCochainsUniverseIso.inv.f n := by
  rw [← cyclesMap_homogeneousCochainsUniverseIso_inv, HomologicalComplex.cyclesMap_i]

/-- **The continuous-cohomology comparison preserves cocycle classes**:
`continuousCohomologyUniverseIso` intertwines the class projections `ContinuousCohomology.π` with
`cocyclesUniverseIso`. -/
@[reassoc (attr := simp)]
theorem π_comp_continuousCohomologyUniverseIso_hom (n : ℕ) (X : TopRep.{v, u, v} R G) :
    _root_.ContinuousCohomology.π.{u, v, v} X n ≫ (continuousCohomologyUniverseIso n X).hom =
      (cocyclesUniverseIso n X).hom ≫ _root_.ContinuousCohomology.π.{u, v, 0} X n :=
  eqToHom_naturality (fun C ↦ C.homologyπ n) X.homogeneousCochains_universe_eq

/-- Inverse form of `π_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc (attr := simp)]
theorem π_comp_continuousCohomologyUniverseIso_inv (n : ℕ) (X : TopRep.{v, u, v} R G) :
    _root_.ContinuousCohomology.π.{u, v, 0} X n ≫ (continuousCohomologyUniverseIso n X).inv =
      (cocyclesUniverseIso n X).inv ≫ _root_.ContinuousCohomology.π.{u, v, v} X n :=
  eqToHom_naturality (fun C ↦ C.homologyπ n) X.homogeneousCochains_universe_eq.symm

/-- Elementwise form of `π_comp_continuousCohomologyUniverseIso_hom`: the image of the cohomology
class of a cocycle `z` is the class of its image under `cocyclesUniverseIso`. -/
@[simp]
theorem continuousCohomologyUniverseIso_hom_π_apply (n : ℕ) (X : TopRep.{v, u, v} R G)
    (z : _root_.ContinuousCohomology.cocycles.{u, v, v} X n) :
    (continuousCohomologyUniverseIso n X).hom (_root_.ContinuousCohomology.π.{u, v, v} X n z) =
      _root_.ContinuousCohomology.π.{u, v, 0} X n ((cocyclesUniverseIso n X).hom z) := by
  have h := ConcreteCategory.congr_hom (π_comp_continuousCohomologyUniverseIso_hom n X) z
  simpa only [ConcreteCategory.comp_apply] using h

/-- Elementwise form of `π_comp_continuousCohomologyUniverseIso_inv`. -/
@[simp]
theorem continuousCohomologyUniverseIso_inv_π_apply (n : ℕ) (X : TopRep.{v, u, v} R G)
    (z : _root_.ContinuousCohomology.cocycles.{u, v, 0} X n) :
    (continuousCohomologyUniverseIso n X).inv (_root_.ContinuousCohomology.π.{u, v, 0} X n z) =
      _root_.ContinuousCohomology.π.{u, v, v} X n ((cocyclesUniverseIso n X).inv z) := by
  have h := ConcreteCategory.congr_hom (π_comp_continuousCohomologyUniverseIso_inv n X) z
  simpa only [ConcreteCategory.comp_apply] using h

/-- **The continuous-cohomology comparison carries `TopRep.cochainClass` to
`TopRep.cochainClass`**: the forward comparison sends the cohomology class of a homogeneous cocycle
`a` to the class of its image under `TopRep.homogeneousCochainsUniverseIso`. -/
@[simp]
theorem continuousCohomologyUniverseIso_hom_cochainClass (n : ℕ) (X : TopRep.{v, u, v} R G)
    (a : (TopRep.homogeneousCochains.{u, v, v} X).X n)
    (ha : ((TopRep.homogeneousCochains.{u, v, v} X).d n (n + 1)).hom a = 0) :
    (continuousCohomologyUniverseIso n X).hom (TopRep.cochainClass.{u, v, v} X n a ha) =
      TopRep.cochainClass.{u, v, 0} X n ((X.homogeneousCochainsUniverseIso.hom.f n).hom a) (by
        rw [HomologicalComplex.Hom.comm_apply, ha, map_zero]) := by
  rw [TopRep.cochainClass_def, TopRep.cochainClass_def,
    ← homologyMap_homogeneousCochainsUniverseIso_hom]
  exact HomologicalComplex.homologyMap_homologyπ_cyclesMkOfEq
    X.homogeneousCochainsUniverseIso.hom a (n + 1) (CochainComplex.next ℕ n) ha

/-- Inverse form of `continuousCohomologyUniverseIso_hom_cochainClass`. -/
@[simp]
theorem continuousCohomologyUniverseIso_inv_cochainClass (n : ℕ) (X : TopRep.{v, u, v} R G)
    (a : (TopRep.homogeneousCochains.{u, v, 0} X).X n)
    (ha : ((TopRep.homogeneousCochains.{u, v, 0} X).d n (n + 1)).hom a = 0) :
    (continuousCohomologyUniverseIso n X).inv (TopRep.cochainClass.{u, v, 0} X n a ha) =
      TopRep.cochainClass.{u, v, v} X n ((X.homogeneousCochainsUniverseIso.inv.f n).hom a) (by
        rw [HomologicalComplex.Hom.comm_apply, ha, map_zero]) := by
  rw [TopRep.cochainClass_def, TopRep.cochainClass_def,
    ← homologyMap_homogeneousCochainsUniverseIso_inv]
  exact HomologicalComplex.homologyMap_homologyπ_cyclesMkOfEq
    X.homogeneousCochainsUniverseIso.inv a (n + 1) (CochainComplex.next ℕ n) ha

/-! #### Compatibility with the degree-zero invariants isomorphism -/

/-- **Compatibility with `ContinuousCohomology.zeroIso`**: in degree zero, the comparison between
extra universes `v` and `0` commutes with the canonical isomorphism onto the `G`-invariants
`X.ρ.invariants`. -/
@[reassoc (attr := simp)]
theorem continuousCohomologyUniverseIso_hom_comp_zeroIso_hom (X : TopRep.{v, u, v} R G) :
    (continuousCohomologyUniverseIso 0 X).hom ≫
        (_root_.ContinuousCohomology.zeroIso.{u, v, 0} X).hom =
      (_root_.ContinuousCohomology.zeroIso.{u, v, v} X).hom := by
  rw [← cancel_epi (_root_.ContinuousCohomology.π.{u, v, v} X 0),
    π_comp_continuousCohomologyUniverseIso_hom_assoc]
  ext σ
  simp only [ConcreteCategory.comp_apply]
  rw [coe_zeroIso_hom_π.{u, v, 0} X, coe_zeroIso_hom_π.{u, v, v} X]
  have h := ConcreteCategory.congr_hom (cocyclesUniverseIso_hom_comp_iCycles 0 X) σ
  simp only [ConcreteCategory.comp_apply, TopRep.homogeneousCochainsUniverseIso_hom_f_zero,
    ConcreteCategory.id_apply] at h
  rw [h]

/-- Inverse-source form of `continuousCohomologyUniverseIso_hom_comp_zeroIso_hom`. -/
@[reassoc (attr := simp)]
theorem continuousCohomologyUniverseIso_inv_comp_zeroIso_hom (X : TopRep.{v, u, v} R G) :
    (continuousCohomologyUniverseIso 0 X).inv ≫
        (_root_.ContinuousCohomology.zeroIso.{u, v, v} X).hom =
      (_root_.ContinuousCohomology.zeroIso.{u, v, 0} X).hom := by
  rw [← continuousCohomologyUniverseIso_hom_comp_zeroIso_hom X, Iso.inv_hom_id_assoc]

/-- `ContinuousCohomology.zeroIso.inv` from `G`-invariants into degree-zero cohomology commutes
with `continuousCohomologyUniverseIso`. -/
@[reassoc (attr := simp)]
theorem zeroIso_inv_comp_continuousCohomologyUniverseIso_hom (X : TopRep.{v, u, v} R G) :
    (_root_.ContinuousCohomology.zeroIso.{u, v, v} X).inv ≫
        (continuousCohomologyUniverseIso 0 X).hom =
      (_root_.ContinuousCohomology.zeroIso.{u, v, 0} X).inv := by
  rw [Iso.inv_comp_eq, ← continuousCohomologyUniverseIso_hom_comp_zeroIso_hom X, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- Inverse form of `zeroIso_inv_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc (attr := simp)]
theorem zeroIso_inv_comp_continuousCohomologyUniverseIso_inv (X : TopRep.{v, u, v} R G) :
    (_root_.ContinuousCohomology.zeroIso.{u, v, 0} X).inv ≫
        (continuousCohomologyUniverseIso 0 X).inv =
      (_root_.ContinuousCohomology.zeroIso.{u, v, v} X).inv := by
  rw [← zeroIso_inv_comp_continuousCohomologyUniverseIso_hom X, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-! #### Functoriality under compatible pairs, restriction, and inflation -/

private theorem resolutionMap_succ_heq_aux (φ : H →ₜ* G)
    {A₀ A₀' : TopRep.{v, u, v} R G} {B₀ B₀' : TopRep.{v, u, v} R H}
    (hA : A₀ = A₀') (hB : B₀ = B₀')
    (f : TopRep.res φ A₀ ⟶ B₀) (g : TopRep.res φ A₀' ⟶ B₀') (hfg : f ≍ g) :
    (TopRep.ofHom (ContRepresentation.coind₁ResMap φ f.hom) :
        TopRep.res φ A₀.coind₁ ⟶ B₀.coind₁) ≍
      (TopRep.ofHom (ContRepresentation.coind₁ResMap φ g.hom) :
        TopRep.res φ A₀'.coind₁ ⟶ B₀'.coind₁) := by
  subst hA hB
  cases hfg
  rfl

/-- For a compatible pair `(φ, f)` with coefficients in `TopRep.{v, u, v}`, the induced resolution
morphisms `ContinuousCohomology.resolutionMap` at extra universes `v` and `0` are heterogeneously
equal in every degree. -/
theorem resolutionMap_universe_heq {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) :
    ∀ i : ℕ, _root_.ContinuousCohomology.resolutionMap.{u, v, v} φ f i ≍
      _root_.ContinuousCohomology.resolutionMap.{u, v, 0} φ f i
  | 0 => HEq.rfl
  | i + 1 => by
    rw [_root_.ContinuousCohomology.resolutionMap_succ,
      _root_.ContinuousCohomology.resolutionMap_succ]
    exact resolutionMap_succ_heq_aux φ (X.resolutionX_universe_eq i) (Y.resolutionX_universe_eq i)
      _ _ (resolutionMap_universe_heq φ f i)

/-- Categorical form of `resolutionMap_universe_heq`: the resolution maps at extra universes `v`
and `0` intertwine `eqToHom` along `TopRep.resolutionX_universe_eq`. -/
@[reassoc]
theorem resolutionMap_comp_eqToHom_resolutionX_universe_eq
    {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (i : ℕ) :
    _root_.ContinuousCohomology.resolutionMap.{u, v, v} φ f i ≫
        eqToHom (Y.resolutionX_universe_eq i) =
      eqToHom (congrArg (TopRep.res (φ : H →* G)) (X.resolutionX_universe_eq i)) ≫
        _root_.ContinuousCohomology.resolutionMap.{u, v, 0} φ f i :=
  eq_of_heq ((comp_eqToHom_heq _ _).trans
    ((resolutionMap_universe_heq φ f i).trans (eqToHom_comp_heq _ _).symm))

/-- **Naturality of `TopRep.homogeneousCochainsUniverseIso` with respect to compatible pairs.** -/
@[reassoc (attr := simp)]
theorem cochainsMap_comp_homogeneousCochainsUniverseIso_hom
    {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) :
    _root_.ContinuousCohomology.cochainsMap.{u, v, v} φ f ≫
        Y.homogeneousCochainsUniverseIso.hom =
      X.homogeneousCochainsUniverseIso.hom ≫
        _root_.ContinuousCohomology.cochainsMap.{u, v, 0} φ f := by
  ext i : 1
  simp only [HomologicalComplex.comp_f, TopRep.homogeneousCochainsUniverseIso_hom_f,
    _root_.ContinuousCohomology.cochainsMap_f]
  have h := resolutionMap_comp_eqToHom_resolutionX_universe_eq φ f (i + 1)
  rw [← eqToHom_map (TopRep.resFunctor (φ : H →* G)) (X.resolutionX_universe_eq (i + 1))] at h
  have h' := congrArg (TopRep.invariantsResMap (φ : H →* G)) h
  rw [TopRep.invariantsResMap_comp, TopRep.invariantsResMap_map_comp,
    eqToHom_map, eqToHom_map] at h'
  exact h'

/-- Inverse form of `cochainsMap_comp_homogeneousCochainsUniverseIso_hom`. -/
@[reassoc (attr := simp)]
theorem cochainsMap_comp_homogeneousCochainsUniverseIso_inv
    {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) :
    _root_.ContinuousCohomology.cochainsMap.{u, v, 0} φ f ≫
        Y.homogeneousCochainsUniverseIso.inv =
      X.homogeneousCochainsUniverseIso.inv ≫
        _root_.ContinuousCohomology.cochainsMap.{u, v, v} φ f := by
  rw [Iso.comp_inv_eq, Category.assoc, cochainsMap_comp_homogeneousCochainsUniverseIso_hom φ f,
    Iso.inv_hom_id_assoc]

/-- Heterogeneous equality form of `cochainsMap_comp_homogeneousCochainsUniverseIso_hom`. -/
theorem cochainsMap_universe_heq {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) :
    _root_.ContinuousCohomology.cochainsMap.{u, v, v} φ f ≍
      _root_.ContinuousCohomology.cochainsMap.{u, v, 0} φ f := by
  have h := cochainsMap_comp_homogeneousCochainsUniverseIso_hom φ f
  rw [TopRep.homogeneousCochainsUniverseIso_def, TopRep.homogeneousCochainsUniverseIso_def,
    eqToIso.hom, eqToIso.hom] at h
  exact (comp_eqToHom_heq _ _).symm.trans ((heq_of_eq h).trans (eqToHom_comp_heq _ _))

/-- **Naturality of `cocyclesUniverseIso` with respect to compatible pairs.** -/
@[reassoc (attr := simp)]
theorem cocyclesMap_comp_cocyclesUniverseIso_hom
    {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.cocyclesMap.{u, v, v} φ f n ≫ (cocyclesUniverseIso n Y).hom =
      (cocyclesUniverseIso n X).hom ≫
        _root_.ContinuousCohomology.cocyclesMap.{u, v, 0} φ f n := by
  rw [← cyclesMap_homogeneousCochainsUniverseIso_hom,
    ← cyclesMap_homogeneousCochainsUniverseIso_hom,
    ← HomologicalComplex.cyclesMap_comp, ← HomologicalComplex.cyclesMap_comp,
    cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

/-- Inverse form of `cocyclesMap_comp_cocyclesUniverseIso_hom`. -/
@[reassoc (attr := simp)]
theorem cocyclesMap_comp_cocyclesUniverseIso_inv
    {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.cocyclesMap.{u, v, 0} φ f n ≫ (cocyclesUniverseIso n Y).inv =
      (cocyclesUniverseIso n X).inv ≫
        _root_.ContinuousCohomology.cocyclesMap.{u, v, v} φ f n := by
  rw [Iso.comp_inv_eq, Category.assoc, cocyclesMap_comp_cocyclesUniverseIso_hom φ f n,
    Iso.inv_hom_id_assoc]

/-- **Naturality of `continuousCohomologyUniverseIso` with respect to compatible pairs.** -/
@[reassoc (attr := simp)]
theorem map_comp_continuousCohomologyUniverseIso_hom
    {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.map.{u, v, v} φ f n ≫
        (continuousCohomologyUniverseIso n Y).hom =
      (continuousCohomologyUniverseIso n X).hom ≫
        _root_.ContinuousCohomology.map.{u, v, 0} φ f n := by
  rw [← homologyMap_homogeneousCochainsUniverseIso_hom,
    ← homologyMap_homogeneousCochainsUniverseIso_hom,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

/-- Inverse form of `map_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc (attr := simp)]
theorem map_comp_continuousCohomologyUniverseIso_inv
    {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (φ : H →ₜ* G) (f : TopRep.res φ X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.map.{u, v, 0} φ f n ≫
        (continuousCohomologyUniverseIso n Y).inv =
      (continuousCohomologyUniverseIso n X).inv ≫
        _root_.ContinuousCohomology.map.{u, v, v} φ f n := by
  rw [Iso.comp_inv_eq, Category.assoc, map_comp_continuousCohomologyUniverseIso_hom φ f n,
    Iso.inv_hom_id_assoc]

/-- **Naturality of `continuousCohomologyUniverseIso` with respect to coefficient morphisms.** -/
@[reassoc (attr := simp)]
theorem coeffMap_comp_continuousCohomologyUniverseIso_hom
    {X Y : TopRep.{v, u, v} R G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap.{u, v, v} f n ≫ (continuousCohomologyUniverseIso n Y).hom =
      (continuousCohomologyUniverseIso n X).hom ≫ coeffMap.{u, v, 0} f n := by
  rw [coeffMap_def, coeffMap_def]
  exact map_comp_continuousCohomologyUniverseIso_hom (ContinuousMonoidHom.id G) f n

/-- Inverse form of `coeffMap_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc (attr := simp)]
theorem coeffMap_comp_continuousCohomologyUniverseIso_inv
    {X Y : TopRep.{v, u, v} R G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap.{u, v, 0} f n ≫ (continuousCohomologyUniverseIso n Y).inv =
      (continuousCohomologyUniverseIso n X).inv ≫ coeffMap.{u, v, v} f n := by
  rw [coeffMap_def, coeffMap_def]
  exact map_comp_continuousCohomologyUniverseIso_inv (ContinuousMonoidHom.id G) f n

/-- **Compatibility of `continuousCohomologyUniverseIso` with subgroup restriction `res`.** -/
@[reassoc (attr := simp)]
theorem res_comp_continuousCohomologyUniverseIso_hom
    (S : Subgroup G) (X : TopRep.{v, u, v} R G) (n : ℕ) :
    res.{u, v, v} S X n ≫
        (continuousCohomologyUniverseIso n (TopRep.res (S.subtype : S →* G) X)).hom =
      (continuousCohomologyUniverseIso n X).hom ≫ res.{u, v, 0} S X n := by
  rw [res_def, res_def]
  exact map_comp_continuousCohomologyUniverseIso_hom _ _ n

/-- Inverse form of `res_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc (attr := simp)]
theorem res_comp_continuousCohomologyUniverseIso_inv
    (S : Subgroup G) (X : TopRep.{v, u, v} R G) (n : ℕ) :
    res.{u, v, 0} S X n ≫
        (continuousCohomologyUniverseIso n (TopRep.res (S.subtype : S →* G) X)).inv =
      (continuousCohomologyUniverseIso n X).inv ≫ res.{u, v, v} S X n := by
  rw [res_def, res_def]
  exact map_comp_continuousCohomologyUniverseIso_inv _ _ n

/-- **Compatibility of `continuousCohomologyUniverseIso` with subgroup-inclusion restriction
`resLE`.** -/
@[reassoc (attr := simp)]
theorem resLE_comp_continuousCohomologyUniverseIso_hom
    {K S : Subgroup G} (h : K ≤ S) (X : TopRep.{v, u, v} R G) (n : ℕ) :
    resLE.{u, v, v} h X n ≫
        (continuousCohomologyUniverseIso n (TopRep.res (K.subtype : K →* G) X)).hom =
      (continuousCohomologyUniverseIso n (TopRep.res (S.subtype : S →* G) X)).hom ≫
        resLE.{u, v, 0} h X n := by
  rw [resLE_def, resLE_def]
  exact map_comp_continuousCohomologyUniverseIso_hom _ _ n

/-- Inverse form of `resLE_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc (attr := simp)]
theorem resLE_comp_continuousCohomologyUniverseIso_inv
    {K S : Subgroup G} (h : K ≤ S) (X : TopRep.{v, u, v} R G) (n : ℕ) :
    resLE.{u, v, 0} h X n ≫
        (continuousCohomologyUniverseIso n (TopRep.res (K.subtype : K →* G) X)).inv =
      (continuousCohomologyUniverseIso n (TopRep.res (S.subtype : S →* G) X)).inv ≫
        resLE.{u, v, v} h X n := by
  rw [resLE_def, resLE_def]
  exact map_comp_continuousCohomologyUniverseIso_inv _ _ n

/-- **Compatibility of `continuousCohomologyUniverseIso` with inflation `infl`.** -/
@[reassoc (attr := simp)]
theorem infl_comp_continuousCohomologyUniverseIso_hom
    (N : Subgroup G) [N.Normal] (X : TopRep.{v, u, v} R G) (n : ℕ) :
    infl.{u, v, v} N X n ≫ (continuousCohomologyUniverseIso n X).hom =
      (continuousCohomologyUniverseIso n (TopRep.quotientToInvariants X N)).hom ≫
        infl.{u, v, 0} N X n := by
  rw [infl_def, infl_def]
  exact map_comp_continuousCohomologyUniverseIso_hom _ _ n

/-- Inverse form of `infl_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc (attr := simp)]
theorem infl_comp_continuousCohomologyUniverseIso_inv
    (N : Subgroup G) [N.Normal] (X : TopRep.{v, u, v} R G) (n : ℕ) :
    infl.{u, v, 0} N X n ≫ (continuousCohomologyUniverseIso n X).inv =
      (continuousCohomologyUniverseIso n (TopRep.quotientToInvariants X N)).inv ≫
        infl.{u, v, v} N X n := by
  rw [infl_def, infl_def]
  exact map_comp_continuousCohomologyUniverseIso_inv _ _ n

end Comparison

section Functor

variable (R : Type u) [Ring R] [TopologicalSpace R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Natural isomorphism of continuous-cohomology functors** on `TopRep.{v, u, v} R G` between
extra universes `v` and `0`. -/
noncomputable def continuousCohomologyFunctorUniverseIso (n : ℕ) :
    continuousCohomologyFunctor.{u, v, v} R G n ≅
      continuousCohomologyFunctor.{u, v, 0} R G n :=
  NatIso.ofComponents (fun X ↦ continuousCohomologyUniverseIso n X) fun f ↦
    coeffMap_comp_continuousCohomologyUniverseIso_hom f n

/-- Component of the forward natural transformation of `continuousCohomologyFunctorUniverseIso` at
`X`. -/
@[simp]
theorem continuousCohomologyFunctorUniverseIso_hom_app (n : ℕ) (X : TopRep.{v, u, v} R G) :
    (continuousCohomologyFunctorUniverseIso R G n).hom.app X =
      (continuousCohomologyUniverseIso n X).hom :=
  (rfl)

/-- Component of the inverse natural transformation of `continuousCohomologyFunctorUniverseIso` at
`X`. -/
@[simp]
theorem continuousCohomologyFunctorUniverseIso_inv_app (n : ℕ) (X : TopRep.{v, u, v} R G) :
    (continuousCohomologyFunctorUniverseIso R G n).inv.app X =
      (continuousCohomologyUniverseIso n X).inv :=
  (rfl)

end Functor

section ZeroUniverse

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type 0} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Over a group `G : Type 0`, `cocyclesUniverseIso` is the identity isomorphism. -/
@[simp]
theorem cocyclesUniverseIso_zero_univ (n : ℕ) (X : TopRep.{0, u, 0} R G) :
    cocyclesUniverseIso n X = Iso.refl _ := by
  simp [cocyclesUniverseIso_def]

/-- Over a group `G : Type 0`, `continuousCohomologyUniverseIso` is the identity isomorphism. -/
@[simp]
theorem continuousCohomologyUniverseIso_zero_univ (n : ℕ) (X : TopRep.{0, u, 0} R G) :
    continuousCohomologyUniverseIso n X = Iso.refl _ := by
  simp [continuousCohomologyUniverseIso_def]

variable (R G) in
/-- Over a group `G : Type 0`, `continuousCohomologyFunctorUniverseIso` is the identity natural
isomorphism. -/
@[simp]
theorem continuousCohomologyFunctorUniverseIso_zero_univ (n : ℕ) :
    continuousCohomologyFunctorUniverseIso R G n = Iso.refl _ :=
  Iso.ext (NatTrans.ext (funext fun _ ↦ by
    simp only [continuousCohomologyFunctorUniverseIso_hom_app,
      continuousCohomologyUniverseIso_zero_univ, Iso.refl_hom, NatTrans.id_app,
      continuousCohomologyFunctor]))

end ZeroUniverse

end TauCeti.ContinuousCohomology
