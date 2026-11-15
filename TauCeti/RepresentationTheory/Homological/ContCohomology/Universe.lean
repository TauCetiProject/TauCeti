/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero

/-!
# Universe comparison for the coinduced resolution and continuous cohomology

For a topological ring `k : Type r` and a topological group `G : Type u`, Mathlib's coinduced
resolution `TopRep.resolutionX`, homogeneous cochain complex `TopRep.homogeneousCochains`, and
continuous cohomology `continuousCohomology` carry a third universe parameter `w`, taking objects
in `TopRep.{max u w, r, u} k G` and landing in `TopModuleCat.{max u w, r} k`. Since
`max u (max u v)` and `max u v` are definitionally equal for every universe `v`, any representation
`X : TopRep.{max u v, r, u} k G` admits two instances of these constructions — at `w = max u v` and
at `w = v` — living in the same categories `TopRep.{max u v, r, u} k G` and
`TopModuleCat.{max u v, r} k`, which are nevertheless not definitionally equal because the
recursive definitions carry different universe parameters. In particular, at `v = 0`
(`max u 0 = u`), an object `X : TopRep.{u, r, u} k G` in the universe of `G` has both
`continuousCohomology.{r, u, u} n X` and `continuousCohomology.{r, u, 0} n X`.

This file constructs the canonical comparison isomorphisms between the two instances:

* in resolution degree `0`, `TopRep.resolutionXUniverseIso` is `Iso.refl X`, and in degree `n + 1`
  it applies `TopRep.coind₁Functor k G` (postcomposition on `C(G, -)` with the previous degree's
  continuous `G`-equivariant linear equivalence);
* compatibility with the coinduction unit and the recursive differentials upgrades these levelwise
  isomorphisms to chain isomorphisms of the coinduced resolution (`TopRep.resolutionUniverseIso`),
  its shift (`TopRep.resolution'UniverseIso`), and its `G`-invariants
  (`TopRep.homogeneousCochainsUniverseIso`);
* passing to cycles and homology yields isomorphisms in `TopModuleCat k` on cocycles
  (`TopRep.cocyclesUniverseIso`) and continuous cohomology
  (`TopRep.continuousCohomologyUniverseIso`), carrying the class of any homogeneous cocycle to the
  class of its image, agreeing with `ContinuousCohomology.zeroIso` in degree zero, commuting with
  `ContinuousCohomology.map` for every compatible pair, and reducing to `Iso.refl` when
  `G : Type 0`.

The parameter `v` is placed first in `universe v r u` because `r` and `u` are inferred from `X`: a
caller writes `X.continuousCohomologyUniverseIso.{v} n` in general, and
`X.continuousCohomologyUniverseIso.{0} n` to compare `w = u` against `w = 0` for
`X : TopRep.{u, r, u} k G`.

## Main definitions

* `TopRep.resolutionXUniverseIso`: the levelwise isomorphism
  `TopRep.resolutionX.{r, u, max u v} X n ≅ TopRep.resolutionX.{r, u, v} X n`.
* `TopRep.resolutionUniverseIso`, `TopRep.resolution'UniverseIso`,
  `TopRep.homogeneousCochainsUniverseIso`: the induced chain isomorphisms of the unshifted and
  shifted coinduced resolutions and of the homogeneous cochain complex.
* `TopRep.cocyclesUniverseIso`, `TopRep.continuousCohomologyUniverseIso`: the induced isomorphisms
  in `TopModuleCat k` on cocycles and on continuous cohomology.
* `TauCeti.ContinuousCohomology.continuousCohomologyFunctorUniverseIso`: the natural isomorphism
  `continuousCohomologyFunctor.{r, u, max u v} k G n ≅ continuousCohomologyFunctor.{r, u, v} k G n`.

## Main results

* `TopRep.d_comp_resolutionXUniverseIso_hom`: `resolutionXUniverseIso` commutes with the
  differentials of the coinduced resolution.
* `TopRep.cochainsMap_comp_homogeneousCochainsUniverseIso_hom` and
  `TopRep.map_comp_continuousCohomologyUniverseIso_hom`: naturality of the cochain and cohomology
  comparisons with respect to compatible pairs `(φ, f)`.
* `TopRep.continuousCohomologyUniverseIso_hom_cochainClass`: the cohomology comparison sends the
  class of a homogeneous cocycle to the class of its image cocycle.
* `TopRep.continuousCohomologyUniverseIso_hom_comp_zeroIso_hom` and
  `TauCeti.ContinuousCohomology.continuousCohomologyUniverseIso_hom_degreeZeroClass`: compatibility
  with `ContinuousCohomology.zeroIso` and degree-zero classes of invariant vectors.
* `TopRep.homogeneousCochainsUniverseIso_type_zero` and
  `TopRep.continuousCohomologyUniverseIso_type_zero`: over `G : Type 0`, where `max 0 v` and `v`
  coincide definitionally, the comparisons are `Iso.refl`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I §2.
-/

public section

open CategoryTheory

namespace TopRep

universe v r u

section Comparison

variable {k : Type r} [Ring k] [TopologicalSpace k]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The levelwise isomorphism between the coinduced resolutions of `X : TopRep.{max u v, r, u} k G`
at the universe parameters `max u v` and `v`: the identity of `X` in degree `0`, and postcomposition
via `TopRep.coind₁Functor k G` in degree `n + 1`. -/
def resolutionXUniverseIso (X : TopRep.{max u v, r, u} k G) :
    ∀ n : ℕ, TopRep.resolutionX.{r, u, max u v} X n ≅ TopRep.resolutionX.{r, u, v} X n
  | 0 => Iso.refl X
  | n + 1 => (TopRep.coind₁Functor k G).mapIso (X.resolutionXUniverseIso n)

/-- In degree zero, `resolutionXUniverseIso` is the identity isomorphism of `X`. -/
@[simp]
theorem resolutionXUniverseIso_zero (X : TopRep.{max u v, r, u} k G) :
    X.resolutionXUniverseIso.{v} 0 = Iso.refl X :=
  (rfl)

/-- On a successor degree, `resolutionXUniverseIso` applies `TopRep.coind₁Functor` to the previous
degree's isomorphism. -/
theorem resolutionXUniverseIso_succ (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    X.resolutionXUniverseIso.{v} (n + 1) =
      (TopRep.coind₁Functor k G).mapIso (X.resolutionXUniverseIso.{v} n) :=
  (rfl)

-- Not `@[simp]`: `resolutionXUniverseIso_zero` already simplifies the left-hand side.
/-- In degree zero, the forward map of `resolutionXUniverseIso` is the identity on elements. -/
theorem resolutionXUniverseIso_zero_hom_apply (X : TopRep.{max u v, r, u} k G) (x : X.V) :
    (X.resolutionXUniverseIso.{v} 0).hom.hom x = x :=
  (rfl)

/-- In degree zero, the inverse map of `resolutionXUniverseIso` is the identity on elements. -/
theorem resolutionXUniverseIso_zero_inv_apply (X : TopRep.{max u v, r, u} k G) (x : X.V) :
    (X.resolutionXUniverseIso.{v} 0).inv.hom x = x :=
  (rfl)

/-- On a successor degree, the forward map of `resolutionXUniverseIso` postcomposes continuous
functions on `G` with the forward map in degree `n`. -/
@[simp]
theorem resolutionXUniverseIso_succ_hom_apply_apply (X : TopRep.{max u v, r, u} k G) (n : ℕ)
    (F : (TopRep.resolutionX.{r, u, max u v} X (n + 1)).V) (g : G) :
    ((X.resolutionXUniverseIso.{v} (n + 1)).hom.hom F :
        C(G, (TopRep.resolutionX.{r, u, v} X n).V)) g =
      (X.resolutionXUniverseIso.{v} n).hom.hom (F g) :=
  (rfl)

/-- On a successor degree, the inverse map of `resolutionXUniverseIso` postcomposes continuous
functions on `G` with the inverse map in degree `n`. -/
@[simp]
theorem resolutionXUniverseIso_succ_inv_apply_apply (X : TopRep.{max u v, r, u} k G) (n : ℕ)
    (F : (TopRep.resolutionX.{r, u, v} X (n + 1)).V) (g : G) :
    ((X.resolutionXUniverseIso.{v} (n + 1)).inv.hom F :
        C(G, (TopRep.resolutionX.{r, u, max u v} X n).V)) g =
      (X.resolutionXUniverseIso.{v} n).inv.hom (F g) :=
  (rfl)

/-- The forward maps of `resolutionXUniverseIso` commute with the differentials of the coinduced
resolution. -/
@[reassoc]
theorem d_comp_resolutionXUniverseIso_hom (X : TopRep.{max u v, r, u} k G) :
    ∀ n : ℕ, TopRep.d.{r, u, max u v} X n ≫ (X.resolutionXUniverseIso.{v} (n + 1)).hom =
      (X.resolutionXUniverseIso.{v} n).hom ≫ TopRep.d.{r, u, v} X n
  | 0 => by
    rw [resolutionXUniverseIso_succ, resolutionXUniverseIso_zero,
      CategoryTheory.Functor.mapIso_refl, Iso.refl_hom, Iso.refl_hom, Category.comp_id,
      Category.id_comp, TopRep.d_zero, TopRep.d_zero]
  | n + 1 => by
    rw [TopRep.d_succ, TopRep.d_succ, Preadditive.sub_comp, Preadditive.comp_sub]
    refine congrArg₂ Sub.sub ?_ ?_
    · rw [resolutionXUniverseIso_succ X (n + 1), CategoryTheory.Functor.mapIso_hom]
      exact ((TopRep.coind₁ι (k := k) (G := G)).naturality
        (X.resolutionXUniverseIso.{v} (n + 1)).hom).symm
    · rw [resolutionXUniverseIso_succ X (n + 1), CategoryTheory.Functor.mapIso_hom,
        ← CategoryTheory.Functor.map_comp, d_comp_resolutionXUniverseIso_hom X n,
        CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.mapIso_hom,
        ← resolutionXUniverseIso_succ X n]

/-- The inverse maps of `resolutionXUniverseIso` commute with the differentials of the coinduced
resolution. -/
@[reassoc]
theorem d_comp_resolutionXUniverseIso_inv (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    TopRep.d.{r, u, v} X n ≫ (X.resolutionXUniverseIso.{v} (n + 1)).inv =
      (X.resolutionXUniverseIso.{v} n).inv ≫ TopRep.d.{r, u, max u v} X n := by
  rw [Iso.comp_inv_eq, Category.assoc, d_comp_resolutionXUniverseIso_hom, Iso.inv_hom_id_assoc]

/-- The chain isomorphism between the unshifted coinduced resolutions of
`X : TopRep.{max u v, r, u} k G` at the universe parameters `max u v` and `v`. -/
def resolutionUniverseIso (X : TopRep.{max u v, r, u} k G) :
    TopRep.resolution.{r, u, max u v} X ≅ TopRep.resolution.{r, u, v} X :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ X.resolutionXUniverseIso.{v} n) fun i j hij ↦ by
    obtain rfl : i + 1 = j := hij
    simp only [CochainComplex.of_d]
    exact (d_comp_resolutionXUniverseIso_hom.{v} X i).symm

/-- The degree-`n` forward component of `resolutionUniverseIso` is that of
`resolutionXUniverseIso`. -/
@[simp]
theorem resolutionUniverseIso_hom_f (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    X.resolutionUniverseIso.{v}.hom.f n = (X.resolutionXUniverseIso.{v} n).hom :=
  (rfl)

/-- The degree-`n` inverse component of `resolutionUniverseIso` is that of
`resolutionXUniverseIso`. -/
@[simp]
theorem resolutionUniverseIso_inv_f (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    X.resolutionUniverseIso.{v}.inv.f n = (X.resolutionXUniverseIso.{v} n).inv :=
  (rfl)

/-- The chain isomorphism between the shifted coinduced resolutions of
`X : TopRep.{max u v, r, u} k G` at the universe parameters `max u v` and `v`. -/
def resolution'UniverseIso (X : TopRep.{max u v, r, u} k G) :
    TopRep.resolution'.{r, u, max u v} X ≅ TopRep.resolution'.{r, u, v} X :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ X.resolutionXUniverseIso.{v} (n + 1))
    fun i j hij ↦ by
      obtain rfl : i + 1 = j := hij
      simp only [CochainComplex.of_d, TopRep.resolution'd_eq]
      exact (d_comp_resolutionXUniverseIso_hom.{v} X (i + 1)).symm

/-- The degree-`n` forward component of `resolution'UniverseIso` is the degree-`(n + 1)` forward
map of `resolutionXUniverseIso`. -/
@[simp]
theorem resolution'UniverseIso_hom_f (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    X.resolution'UniverseIso.{v}.hom.f n = (X.resolutionXUniverseIso.{v} (n + 1)).hom :=
  (rfl)

/-- The degree-`n` inverse component of `resolution'UniverseIso` is the degree-`(n + 1)` inverse
map of `resolutionXUniverseIso`. -/
@[simp]
theorem resolution'UniverseIso_inv_f (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    X.resolution'UniverseIso.{v}.inv.f n = (X.resolutionXUniverseIso.{v} (n + 1)).inv :=
  (rfl)

/-- **Universe comparison for homogeneous cochains**: the chain isomorphism between
`TopRep.homogeneousCochains.{r, u, max u v} X` and `TopRep.homogeneousCochains.{r, u, v} X`
obtained by restricting `resolution'UniverseIso` to `G`-invariants. -/
def homogeneousCochainsUniverseIso (X : TopRep.{max u v, r, u} k G) :
    TopRep.homogeneousCochains.{r, u, max u v} X ≅ TopRep.homogeneousCochains.{r, u, v} X :=
  ((TopRep.invariantsFunctor k G).mapHomologicalComplex _).mapIso X.resolution'UniverseIso.{v}

/-- The defining equation of `homogeneousCochainsUniverseIso`: it is the image of
`resolution'UniverseIso` under `(TopRep.invariantsFunctor k G).mapHomologicalComplex _`. -/
theorem homogeneousCochainsUniverseIso_def (X : TopRep.{max u v, r, u} k G) :
    X.homogeneousCochainsUniverseIso.{v} =
      ((TopRep.invariantsFunctor k G).mapHomologicalComplex _).mapIso
        X.resolution'UniverseIso.{v} :=
  (rfl)

/-- The degree-`n` forward component of `homogeneousCochainsUniverseIso` restricts the
degree-`(n + 1)` forward map of `resolutionXUniverseIso` to `G`-invariants. -/
@[simp]
theorem homogeneousCochainsUniverseIso_hom_f (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    X.homogeneousCochainsUniverseIso.{v}.hom.f n =
      (TopRep.invariantsFunctor k G).map (X.resolutionXUniverseIso.{v} (n + 1)).hom :=
  (rfl)

/-- The degree-`n` inverse component of `homogeneousCochainsUniverseIso` restricts the
degree-`(n + 1)` inverse map of `resolutionXUniverseIso` to `G`-invariants. -/
@[simp]
theorem homogeneousCochainsUniverseIso_inv_f (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    X.homogeneousCochainsUniverseIso.{v}.inv.f n =
      (TopRep.invariantsFunctor k G).map (X.resolutionXUniverseIso.{v} (n + 1)).inv :=
  (rfl)

-- Not `@[simp]`: `homogeneousCochainsUniverseIso_hom_f` and `homogeneousCochainsUniverseIso_inv_f`
-- already simplify the left-hand sides through `resolutionXUniverseIso_succ_*_apply_apply`.
/-- In degree zero, `homogeneousCochainsUniverseIso` preserves the values of a homogeneous
`0`-cochain at every element of `G`. -/
theorem coe_homogeneousCochainsUniverseIso_hom_f_zero_apply (X : TopRep.{max u v, r, u} k G)
    (a : (TopRep.homogeneousCochains.{r, u, max u v} X).X 0) (g : G) :
    (((X.homogeneousCochainsUniverseIso.{v}.hom.f 0).hom a).val : C(G, X.V)) g = a.val g :=
  (rfl)

/-- In degree zero, the inverse of `homogeneousCochainsUniverseIso` preserves the values of a
homogeneous `0`-cochain at every element of `G`. -/
theorem coe_homogeneousCochainsUniverseIso_inv_f_zero_apply (X : TopRep.{max u v, r, u} k G)
    (a : (TopRep.homogeneousCochains.{r, u, v} X).X 0) (g : G) :
    (((X.homogeneousCochainsUniverseIso.{v}.inv.f 0).hom a).val : C(G, X.V)) g = a.val g :=
  (rfl)

/-- In degree one, `homogeneousCochainsUniverseIso` preserves the values of a homogeneous
`1`-cochain at every pair of elements of `G`. -/
theorem coe_homogeneousCochainsUniverseIso_hom_f_one_apply (X : TopRep.{max u v, r, u} k G)
    (a : (TopRep.homogeneousCochains.{r, u, max u v} X).X 1) (g₀ g₁ : G) :
    (((X.homogeneousCochainsUniverseIso.{v}.hom.f 1).hom a).val : C(G, C(G, X.V))) g₀ g₁ =
      a.val g₀ g₁ :=
  (rfl)

/-- In degree one, the inverse of `homogeneousCochainsUniverseIso` preserves the values of a
homogeneous `1`-cochain at every pair of elements of `G`. -/
theorem coe_homogeneousCochainsUniverseIso_inv_f_one_apply (X : TopRep.{max u v, r, u} k G)
    (a : (TopRep.homogeneousCochains.{r, u, v} X).X 1) (g₀ g₁ : G) :
    (((X.homogeneousCochainsUniverseIso.{v}.inv.f 1).hom a).val : C(G, C(G, X.V))) g₀ g₁ =
      a.val g₀ g₁ :=
  (rfl)

/-- **Universe comparison on cocycles**: the isomorphism in `TopModuleCat k` between the
`n`-cocycles of `X` at the universe parameters `max u v` and `v`. -/
noncomputable def cocyclesUniverseIso (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    ContinuousCohomology.cocycles.{r, u, max u v} X n ≅
      ContinuousCohomology.cocycles.{r, u, v} X n :=
  (HomologicalComplex.cyclesFunctor (TopModuleCat k) _ n).mapIso
    X.homogeneousCochainsUniverseIso.{v}

/-- The defining equation of `cocyclesUniverseIso`: it is induced on cycles by
`homogeneousCochainsUniverseIso`. -/
theorem cocyclesUniverseIso_def (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    X.cocyclesUniverseIso.{v} n =
      (HomologicalComplex.cyclesFunctor (TopModuleCat k) _ n).mapIso
        X.homogeneousCochainsUniverseIso.{v} :=
  (rfl)

/-- **Universe comparison on continuous cohomology**: the isomorphism in `TopModuleCat k` between
`continuousCohomology.{r, u, max u v} n X` and `continuousCohomology.{r, u, v} n X` induced on
homology by `homogeneousCochainsUniverseIso`. -/
noncomputable def continuousCohomologyUniverseIso (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    continuousCohomology.{r, u, max u v} n X ≅ continuousCohomology.{r, u, v} n X :=
  (HomologicalComplex.homologyFunctor (TopModuleCat k) _ n).mapIso
    X.homogeneousCochainsUniverseIso.{v}

/-- The defining equation of `continuousCohomologyUniverseIso`: it is induced on homology by
`homogeneousCochainsUniverseIso`. -/
theorem continuousCohomologyUniverseIso_def (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    X.continuousCohomologyUniverseIso.{v} n =
      (HomologicalComplex.homologyFunctor (TopModuleCat k) _ n).mapIso
        X.homogeneousCochainsUniverseIso.{v} :=
  (rfl)

/-- The forward map of `cocyclesUniverseIso` intertwines the inclusions of cocycles into
homogeneous cochains. -/
@[reassoc (attr := simp)]
theorem cocyclesUniverseIso_hom_comp_iCycles (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    (X.cocyclesUniverseIso.{v} n).hom ≫ (TopRep.homogeneousCochains.{r, u, v} X).iCycles n =
      (TopRep.homogeneousCochains.{r, u, max u v} X).iCycles n ≫
        X.homogeneousCochainsUniverseIso.{v}.hom.f n :=
  HomologicalComplex.cyclesMap_i X.homogeneousCochainsUniverseIso.{v}.hom n

/-- The inverse map of `cocyclesUniverseIso` intertwines the inclusions of cocycles into
homogeneous cochains. -/
@[reassoc (attr := simp)]
theorem cocyclesUniverseIso_inv_comp_iCycles (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    (X.cocyclesUniverseIso.{v} n).inv ≫
        (TopRep.homogeneousCochains.{r, u, max u v} X).iCycles n =
      (TopRep.homogeneousCochains.{r, u, v} X).iCycles n ≫
        X.homogeneousCochainsUniverseIso.{v}.inv.f n :=
  HomologicalComplex.cyclesMap_i X.homogeneousCochainsUniverseIso.{v}.inv n

/-- The forward map of `continuousCohomologyUniverseIso` carries the homology class of a cocycle to
the homology class of its image under `cocyclesUniverseIso`. -/
@[reassoc (attr := simp)]
theorem π_comp_continuousCohomologyUniverseIso_hom (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    ContinuousCohomology.π.{r, u, max u v} X n ≫ (X.continuousCohomologyUniverseIso.{v} n).hom =
      (X.cocyclesUniverseIso.{v} n).hom ≫ ContinuousCohomology.π.{r, u, v} X n := by
  simp [continuousCohomologyUniverseIso_def, cocyclesUniverseIso_def]

/-- The inverse map of `continuousCohomologyUniverseIso` carries the homology class of a cocycle to
the homology class of its preimage under `cocyclesUniverseIso`. -/
@[reassoc (attr := simp)]
theorem π_comp_continuousCohomologyUniverseIso_inv (X : TopRep.{max u v, r, u} k G) (n : ℕ) :
    ContinuousCohomology.π.{r, u, v} X n ≫ (X.continuousCohomologyUniverseIso.{v} n).inv =
      (X.cocyclesUniverseIso.{v} n).inv ≫ ContinuousCohomology.π.{r, u, max u v} X n := by
  simp [continuousCohomologyUniverseIso_def, cocyclesUniverseIso_def]

/-- **Action on classes of homogeneous cocycles**: `continuousCohomologyUniverseIso` carries the
class of a homogeneous `n`-cocycle `a` to the class of its image under
`homogeneousCochainsUniverseIso`. -/
@[simp]
theorem continuousCohomologyUniverseIso_hom_cochainClass (X : TopRep.{max u v, r, u} k G) (n : ℕ)
    (a : (TopRep.homogeneousCochains.{r, u, max u v} X).X n)
    (ha : ((TopRep.homogeneousCochains.{r, u, max u v} X).d n (n + 1)).hom a = 0) :
    (X.continuousCohomologyUniverseIso.{v} n).hom
        (TopRep.cochainClass.{r, u, max u v} X n a ha) =
      TopRep.cochainClass.{r, u, v} X n
        ((X.homogeneousCochainsUniverseIso.{v}.hom.f n).hom a) (by
          rw [← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm,
            ConcreteCategory.comp_apply, ha, map_zero]) := by
  rw [TopRep.cochainClass_def, TopRep.cochainClass_def, continuousCohomologyUniverseIso_def]
  exact HomologicalComplex.homologyMap_homologyπ_cyclesMkOfEq
    X.homogeneousCochainsUniverseIso.{v}.hom a (n + 1) (CochainComplex.next ℕ n) ha

/-- The inverse of `continuousCohomologyUniverseIso` carries the class of a homogeneous `n`-cocycle
to the class of its image under the inverse of `homogeneousCochainsUniverseIso`. -/
@[simp]
theorem continuousCohomologyUniverseIso_inv_cochainClass (X : TopRep.{max u v, r, u} k G) (n : ℕ)
    (a : (TopRep.homogeneousCochains.{r, u, v} X).X n)
    (ha : ((TopRep.homogeneousCochains.{r, u, v} X).d n (n + 1)).hom a = 0) :
    (X.continuousCohomologyUniverseIso.{v} n).inv (TopRep.cochainClass.{r, u, v} X n a ha) =
      TopRep.cochainClass.{r, u, max u v} X n
        ((X.homogeneousCochainsUniverseIso.{v}.inv.f n).hom a) (by
          rw [← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm,
            ConcreteCategory.comp_apply, ha, map_zero]) := by
  rw [TopRep.cochainClass_def, TopRep.cochainClass_def, continuousCohomologyUniverseIso_def]
  exact HomologicalComplex.homologyMap_homologyπ_cyclesMkOfEq
    X.homogeneousCochainsUniverseIso.{v}.inv a (n + 1) (CochainComplex.next ℕ n) ha

/-- **Compatibility with `ContinuousCohomology.zeroIso`**: in degree zero, the universe comparison
commutes with the identification of `H⁰(G, X)` with `X^G`. -/
@[reassoc (attr := simp)]
theorem continuousCohomologyUniverseIso_hom_comp_zeroIso_hom (X : TopRep.{max u v, r, u} k G) :
    (X.continuousCohomologyUniverseIso.{v} 0).hom ≫
        (ContinuousCohomology.zeroIso.{r, u, v} X).hom =
      (ContinuousCohomology.zeroIso.{r, u, max u v} X).hom := by
  rw [← cancel_epi (ContinuousCohomology.π.{r, u, max u v} X 0),
    π_comp_continuousCohomologyUniverseIso_hom_assoc]
  ext σ
  simp only [ConcreteCategory.comp_apply]
  rw [TauCeti.ContinuousCohomology.coe_zeroIso_hom_π,
    TauCeti.ContinuousCohomology.coe_zeroIso_hom_π]
  have hcyc : (TopRep.homogeneousCochains.{r, u, v} X).iCycles 0
        ((X.cocyclesUniverseIso.{v} 0).hom σ) =
      X.homogeneousCochainsUniverseIso.{v}.hom.f 0
        ((TopRep.homogeneousCochains.{r, u, max u v} X).iCycles 0 σ) :=
    ConcreteCategory.congr_hom (cocyclesUniverseIso_hom_comp_iCycles.{v} X 0) σ
  rw [hcyc]
  exact coe_homogeneousCochainsUniverseIso_hom_f_zero_apply.{v} X _ 1

/-- Inverse form of `continuousCohomologyUniverseIso_hom_comp_zeroIso_hom`. -/
@[reassoc (attr := simp)]
theorem continuousCohomologyUniverseIso_inv_comp_zeroIso_hom (X : TopRep.{max u v, r, u} k G) :
    (X.continuousCohomologyUniverseIso.{v} 0).inv ≫
        (ContinuousCohomology.zeroIso.{r, u, max u v} X).hom =
      (ContinuousCohomology.zeroIso.{r, u, v} X).hom := by
  rw [Iso.inv_comp_eq, continuousCohomologyUniverseIso_hom_comp_zeroIso_hom]

end Comparison

/-! ### Naturality in compatible pairs -/

section Naturality

variable {k : Type r} [Ring k] [TopologicalSpace k]
  {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (φ : H →ₜ* G) {X : TopRep.{max u v, r, u} k G} {Y : TopRep.{max u v, r, u} k H}
  (f : TopRep.res (φ : H →* G) X ⟶ Y)

/-- On the coinduced resolutions, Mathlib's `ContinuousCohomology.resolutionMap` commutes with
`resolutionXUniverseIso`. -/
@[reassoc]
theorem resolutionMap_comp_resolutionXUniverseIso_hom :
    ∀ n : ℕ, ContinuousCohomology.resolutionMap.{r, u, max u v} φ f n ≫
        (Y.resolutionXUniverseIso.{v} n).hom =
      (TopRep.resFunctor (φ : H →* G)).map (X.resolutionXUniverseIso.{v} n).hom ≫
        ContinuousCohomology.resolutionMap.{r, u, v} φ f n
  | 0 => by
    rw [ContinuousCohomology.resolutionMap_zero, ContinuousCohomology.resolutionMap_zero,
      resolutionXUniverseIso_zero, resolutionXUniverseIso_zero, Iso.refl_hom, Iso.refl_hom,
      CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]
  | n + 1 => by
    ext F h
    have ih := ConcreteCategory.congr_hom
      (resolutionMap_comp_resolutionXUniverseIso_hom n) (F (φ h))
    exact ih

/-- Inverse form of `resolutionMap_comp_resolutionXUniverseIso_hom`. -/
@[reassoc]
theorem resolutionMap_comp_resolutionXUniverseIso_inv (n : ℕ) :
    ContinuousCohomology.resolutionMap.{r, u, v} φ f n ≫
        (Y.resolutionXUniverseIso.{v} n).inv =
      (TopRep.resFunctor (φ : H →* G)).map (X.resolutionXUniverseIso.{v} n).inv ≫
        ContinuousCohomology.resolutionMap.{r, u, max u v} φ f n := by
  rw [Iso.comp_inv_eq, Category.assoc, resolutionMap_comp_resolutionXUniverseIso_hom,
    ← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- **Naturality on homogeneous cochains**: `ContinuousCohomology.cochainsMap` commutes with
`homogeneousCochainsUniverseIso` for every compatible pair `(φ, f)`. -/
@[reassoc]
theorem cochainsMap_comp_homogeneousCochainsUniverseIso_hom :
    ContinuousCohomology.cochainsMap.{r, u, max u v} φ f ≫
        Y.homogeneousCochainsUniverseIso.{v}.hom =
      X.homogeneousCochainsUniverseIso.{v}.hom ≫
        ContinuousCohomology.cochainsMap.{r, u, v} φ f := by
  ext n : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    ContinuousCohomology.cochainsMap_f, ContinuousCohomology.cochainsMap_f,
    homogeneousCochainsUniverseIso_hom_f, homogeneousCochainsUniverseIso_hom_f,
    ← TopRep.invariantsResMap_comp, resolutionMap_comp_resolutionXUniverseIso_hom,
    TopRep.invariantsResMap_map_comp]

/-- Inverse form of `cochainsMap_comp_homogeneousCochainsUniverseIso_hom`. -/
@[reassoc]
theorem cochainsMap_comp_homogeneousCochainsUniverseIso_inv :
    ContinuousCohomology.cochainsMap.{r, u, v} φ f ≫
        Y.homogeneousCochainsUniverseIso.{v}.inv =
      X.homogeneousCochainsUniverseIso.{v}.inv ≫
        ContinuousCohomology.cochainsMap.{r, u, max u v} φ f := by
  rw [Iso.comp_inv_eq, Category.assoc, cochainsMap_comp_homogeneousCochainsUniverseIso_hom,
    Iso.inv_hom_id_assoc]

/-- **Naturality on cocycles**: `ContinuousCohomology.cocyclesMap` commutes with
`cocyclesUniverseIso` for every compatible pair `(φ, f)`. -/
@[reassoc]
theorem cocyclesMap_comp_cocyclesUniverseIso_hom (n : ℕ) :
    ContinuousCohomology.cocyclesMap.{r, u, max u v} φ f n ≫ (Y.cocyclesUniverseIso.{v} n).hom =
      (X.cocyclesUniverseIso.{v} n).hom ≫ ContinuousCohomology.cocyclesMap.{r, u, v} φ f n := by
  simp only [ContinuousCohomology.cocyclesMap, cocyclesUniverseIso_def,
    CategoryTheory.Functor.mapIso_hom, HomologicalComplex.cyclesFunctor_map,
    ← HomologicalComplex.cyclesMap_comp, cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

/-- Inverse form of `cocyclesMap_comp_cocyclesUniverseIso_hom`. -/
@[reassoc]
theorem cocyclesMap_comp_cocyclesUniverseIso_inv (n : ℕ) :
    ContinuousCohomology.cocyclesMap.{r, u, v} φ f n ≫ (Y.cocyclesUniverseIso.{v} n).inv =
      (X.cocyclesUniverseIso.{v} n).inv ≫
        ContinuousCohomology.cocyclesMap.{r, u, max u v} φ f n := by
  rw [Iso.comp_inv_eq, Category.assoc, cocyclesMap_comp_cocyclesUniverseIso_hom,
    Iso.inv_hom_id_assoc]

/-- **Naturality on continuous cohomology**: `ContinuousCohomology.map` commutes with
`continuousCohomologyUniverseIso` for every compatible pair `(φ, f)`. -/
@[reassoc]
theorem map_comp_continuousCohomologyUniverseIso_hom (n : ℕ) :
    ContinuousCohomology.map.{r, u, max u v} φ f n ≫
        (Y.continuousCohomologyUniverseIso.{v} n).hom =
      (X.continuousCohomologyUniverseIso.{v} n).hom ≫
        ContinuousCohomology.map.{r, u, v} φ f n := by
  simp only [ContinuousCohomology.map, continuousCohomologyUniverseIso_def,
    CategoryTheory.Functor.mapIso_hom, HomologicalComplex.homologyFunctor_map,
    ← HomologicalComplex.homologyMap_comp, cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

/-- Inverse form of `map_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc]
theorem map_comp_continuousCohomologyUniverseIso_inv (n : ℕ) :
    ContinuousCohomology.map.{r, u, v} φ f n ≫
        (Y.continuousCohomologyUniverseIso.{v} n).inv =
      (X.continuousCohomologyUniverseIso.{v} n).inv ≫
        ContinuousCohomology.map.{r, u, max u v} φ f n := by
  rw [Iso.comp_inv_eq, Category.assoc, map_comp_continuousCohomologyUniverseIso_hom,
    Iso.inv_hom_id_assoc]

end Naturality

/-! ### Reduction to the identity over `Type 0` -/

section TypeZero

variable {k : Type r} [Ring k] [TopologicalSpace k]
  {G : Type 0} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : TopRep.{v, r, 0} k G)

-- None of the `*_type_zero` lemmas carry `@[simp]`: over `G : Type 0`, `max 0 v` and `v` are
-- definitionally equal, while `X.resolutionXUniverseIso` is still a defined head symbol; keeping
-- them explicit avoids unfolding `Iso.refl` where the general naturality API is expected.

/-- Over `G : Type 0`, where `max 0 v` and `v` coincide definitionally, `resolutionXUniverseIso` is
the identity isomorphism in every degree. -/
theorem resolutionXUniverseIso_type_zero :
    ∀ n : ℕ, X.resolutionXUniverseIso.{v} n = Iso.refl (TopRep.resolutionX.{r, 0, v} X n)
  | 0 => rfl
  | n + 1 => by
    rw [resolutionXUniverseIso_succ, resolutionXUniverseIso_type_zero n,
      CategoryTheory.Functor.mapIso_refl]

/-- Over `G : Type 0`, `resolutionUniverseIso` is the identity isomorphism. -/
theorem resolutionUniverseIso_type_zero :
    X.resolutionUniverseIso.{v} = Iso.refl (TopRep.resolution.{r, 0, v} X) := by
  ext n : 2
  simp [resolutionXUniverseIso_type_zero]

/-- Over `G : Type 0`, `resolution'UniverseIso` is the identity isomorphism. -/
theorem resolution'UniverseIso_type_zero :
    X.resolution'UniverseIso.{v} = Iso.refl (TopRep.resolution'.{r, 0, v} X) := by
  ext n : 2
  simp [resolutionXUniverseIso_type_zero]

/-- Over `G : Type 0`, `homogeneousCochainsUniverseIso` is the identity isomorphism. -/
theorem homogeneousCochainsUniverseIso_type_zero :
    X.homogeneousCochainsUniverseIso.{v} = Iso.refl (TopRep.homogeneousCochains.{r, 0, v} X) := by
  rw [homogeneousCochainsUniverseIso_def, resolution'UniverseIso_type_zero,
    CategoryTheory.Functor.mapIso_refl]

/-- Over `G : Type 0`, `cocyclesUniverseIso` is the identity isomorphism in every degree. -/
theorem cocyclesUniverseIso_type_zero (n : ℕ) :
    X.cocyclesUniverseIso.{v} n = Iso.refl (ContinuousCohomology.cocycles.{r, 0, v} X n) := by
  rw [cocyclesUniverseIso_def, homogeneousCochainsUniverseIso_type_zero,
    CategoryTheory.Functor.mapIso_refl]
  rfl

/-- Over `G : Type 0`, `continuousCohomologyUniverseIso` is the identity isomorphism in every
degree. -/
theorem continuousCohomologyUniverseIso_type_zero (n : ℕ) :
    X.continuousCohomologyUniverseIso.{v} n = Iso.refl (continuousCohomology.{r, 0, v} n X) := by
  rw [continuousCohomologyUniverseIso_def, homogeneousCochainsUniverseIso_type_zero,
    CategoryTheory.Functor.mapIso_refl]
  rfl

end TypeZero

end TopRep

namespace TauCeti.ContinuousCohomology

open CategoryTheory TopRep

universe v r u

variable {R : Type r} [Ring R] [TopologicalSpace R]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- In degree zero, `continuousCohomologyUniverseIso` preserves `degreeZeroClass` of every invariant
vector. -/
@[simp]
theorem continuousCohomologyUniverseIso_hom_degreeZeroClass (X : TopRep.{max u v, r, u} R G)
    (x : X.V) (hx : ∀ g : G, X.ρ g x = x) :
    (X.continuousCohomologyUniverseIso.{v} 0).hom
        (degreeZeroClass.{r, u, max u v} X x hx) =
      degreeZeroClass.{r, u, v} X x hx := by
  apply (_root_.ContinuousCohomology.zeroIso.{r, u, v} X).toContinuousLinearEquiv.injective
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom
    (continuousCohomologyUniverseIso_hom_comp_zeroIso_hom.{v} X)
    (degreeZeroClass.{r, u, max u v} X x hx)
  simp only [ConcreteCategory.comp_apply] at h
  rw [Iso.toContinuousLinearEquiv_apply, Iso.toContinuousLinearEquiv_apply, h,
    coe_zeroIso_hom_degreeZeroClass, coe_zeroIso_hom_degreeZeroClass]

/-- Inverse form of `continuousCohomologyUniverseIso_hom_degreeZeroClass`. -/
@[simp]
theorem continuousCohomologyUniverseIso_inv_degreeZeroClass (X : TopRep.{max u v, r, u} R G)
    (x : X.V) (hx : ∀ g : G, X.ρ g x = x) :
    (X.continuousCohomologyUniverseIso.{v} 0).inv (degreeZeroClass.{r, u, v} X x hx) =
      degreeZeroClass.{r, u, max u v} X x hx := by
  rw [← continuousCohomologyUniverseIso_hom_degreeZeroClass.{v} X x hx]
  exact ConcreteCategory.congr_hom (X.continuousCohomologyUniverseIso.{v} 0).hom_inv_id _

/-- Coefficient maps in continuous cohomology commute with `continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem coeffMap_comp_continuousCohomologyUniverseIso_hom {X Y : TopRep.{max u v, r, u} R G}
    (f : X ⟶ Y) (n : ℕ) :
    coeffMap.{r, u, max u v} f n ≫ (Y.continuousCohomologyUniverseIso.{v} n).hom =
      (X.continuousCohomologyUniverseIso.{v} n).hom ≫ coeffMap.{r, u, v} f n := by
  rw [coeffMap_def, coeffMap_def]
  exact map_comp_continuousCohomologyUniverseIso_hom.{v} (ContinuousMonoidHom.id G) f n

/-- Inverse form of `coeffMap_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc]
theorem coeffMap_comp_continuousCohomologyUniverseIso_inv {X Y : TopRep.{max u v, r, u} R G}
    (f : X ⟶ Y) (n : ℕ) :
    coeffMap.{r, u, v} f n ≫ (Y.continuousCohomologyUniverseIso.{v} n).inv =
      (X.continuousCohomologyUniverseIso.{v} n).inv ≫ coeffMap.{r, u, max u v} f n := by
  rw [coeffMap_def, coeffMap_def]
  exact map_comp_continuousCohomologyUniverseIso_inv.{v} (ContinuousMonoidHom.id G) f n

/-- Restriction to a subgroup commutes with `continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem res_comp_continuousCohomologyUniverseIso_hom (S : Subgroup G)
    (X : TopRep.{max u v, r, u} R G) (n : ℕ) :
    res.{r, u, max u v} S X n ≫
        ((TopRep.res (S.subtype : S →* G) X).continuousCohomologyUniverseIso.{v} n).hom =
      (X.continuousCohomologyUniverseIso.{v} n).hom ≫ res.{r, u, v} S X n := by
  rw [res_def, res_def]
  exact map_comp_continuousCohomologyUniverseIso_hom.{v}
    (ContinuousMonoidHom.subgroupSubtype S) (𝟙 _) n

/-- Inverse form of `res_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc]
theorem res_comp_continuousCohomologyUniverseIso_inv (S : Subgroup G)
    (X : TopRep.{max u v, r, u} R G) (n : ℕ) :
    res.{r, u, v} S X n ≫
        ((TopRep.res (S.subtype : S →* G) X).continuousCohomologyUniverseIso.{v} n).inv =
      (X.continuousCohomologyUniverseIso.{v} n).inv ≫ res.{r, u, max u v} S X n := by
  rw [res_def, res_def]
  exact map_comp_continuousCohomologyUniverseIso_inv.{v}
    (ContinuousMonoidHom.subgroupSubtype S) (𝟙 _) n

/-- Restriction along the inclusion of a subgroup into a larger subgroup commutes with
`continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem resLE_comp_continuousCohomologyUniverseIso_hom {H S : Subgroup G} (h : H ≤ S)
    (X : TopRep.{max u v, r, u} R G) (n : ℕ) :
    resLE.{r, u, max u v} h X n ≫
        ((TopRep.res (H.subtype : H →* G) X).continuousCohomologyUniverseIso.{v} n).hom =
      ((TopRep.res (S.subtype : S →* G) X).continuousCohomologyUniverseIso.{v} n).hom ≫
        resLE.{r, u, v} h X n := by
  rw [resLE_def, resLE_def]
  exact map_comp_continuousCohomologyUniverseIso_hom.{v}
    (ContinuousMonoidHom.subgroupInclusion h) (𝟙 _) n

/-- Inverse form of `resLE_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc]
theorem resLE_comp_continuousCohomologyUniverseIso_inv {H S : Subgroup G} (h : H ≤ S)
    (X : TopRep.{max u v, r, u} R G) (n : ℕ) :
    resLE.{r, u, v} h X n ≫
        ((TopRep.res (H.subtype : H →* G) X).continuousCohomologyUniverseIso.{v} n).inv =
      ((TopRep.res (S.subtype : S →* G) X).continuousCohomologyUniverseIso.{v} n).inv ≫
        resLE.{r, u, max u v} h X n := by
  rw [resLE_def, resLE_def]
  exact map_comp_continuousCohomologyUniverseIso_inv.{v}
    (ContinuousMonoidHom.subgroupInclusion h) (𝟙 _) n

/-- Inflation from a normal subgroup commutes with `continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem infl_comp_continuousCohomologyUniverseIso_hom (N : Subgroup G) [N.Normal]
    (X : TopRep.{max u v, r, u} R G) (n : ℕ) :
    infl.{r, u, max u v} N X n ≫ (X.continuousCohomologyUniverseIso.{v} n).hom =
      ((TopRep.quotientToInvariants X N).continuousCohomologyUniverseIso.{v} n).hom ≫
        infl.{r, u, v} N X n := by
  rw [infl_def, infl_def]
  exact map_comp_continuousCohomologyUniverseIso_hom.{v}
    (Subgroup.quotientMkContinuousMonoidHom N) _ n

/-- Inverse form of `infl_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc]
theorem infl_comp_continuousCohomologyUniverseIso_inv (N : Subgroup G) [N.Normal]
    (X : TopRep.{max u v, r, u} R G) (n : ℕ) :
    infl.{r, u, v} N X n ≫ (X.continuousCohomologyUniverseIso.{v} n).inv =
      ((TopRep.quotientToInvariants X N).continuousCohomologyUniverseIso.{v} n).inv ≫
        infl.{r, u, max u v} N X n := by
  rw [infl_def, infl_def]
  exact map_comp_continuousCohomologyUniverseIso_inv.{v}
    (Subgroup.quotientMkContinuousMonoidHom N) _ n

variable (R G) in
/-- **Universe comparison as a natural isomorphism of functors**: the natural isomorphism between
`continuousCohomologyFunctor.{r, u, max u v} R G n` and
`continuousCohomologyFunctor.{r, u, v} R G n` whose components are
`TopRep.continuousCohomologyUniverseIso`. -/
noncomputable def continuousCohomologyFunctorUniverseIso (n : ℕ) :
    continuousCohomologyFunctor.{r, u, max u v} R G n ≅
      continuousCohomologyFunctor.{r, u, v} R G n :=
  NatIso.ofComponents (fun X ↦ X.continuousCohomologyUniverseIso.{v} n)
    fun f ↦ coeffMap_comp_continuousCohomologyUniverseIso_hom.{v} f n

/-- The component of `continuousCohomologyFunctorUniverseIso` at `X` is
`X.continuousCohomologyUniverseIso n`. -/
@[simp]
theorem continuousCohomologyFunctorUniverseIso_app (X : TopRep.{max u v, r, u} R G) (n : ℕ) :
    (continuousCohomologyFunctorUniverseIso.{v} R G n).app X =
      X.continuousCohomologyUniverseIso.{v} n :=
  (rfl)

end TauCeti.ContinuousCohomology
