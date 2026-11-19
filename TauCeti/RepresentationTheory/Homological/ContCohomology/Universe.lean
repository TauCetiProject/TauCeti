/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Basic

/-!
# Continuous cohomology does not depend on the auxiliary universe parameter

For a topological group `G : Type u`, Mathlib builds the continuous cohomology of
`X : TopRep k G` from the coinduced resolution `TopRep.resolutionX X n`, the iterated function
space `C(G, C(G, …, C(G, X)))`. The construction carries a universe parameter `v` beyond those of
`k` and `G`: it applies to coefficients in `Type (max u v)`. For coefficients `X` in
`Type (max u v)`, the parameters `v` and `max u v` both apply, and in each fixed degree they build
objects with the same carriers; but the resolution is defined by recursion on the degree, and at a
variable degree the two complexes are not identified by `rfl`.

This file compares them. The isomorphism `TopRep.resolutionXUniverseIso` of the two resolutions
is the identity in degree zero and, in degree `n + 1`, postcomposition with its degree-`n`
component on `C(G, -)`. It commutes with the differentials, so it descends to an isomorphism
`TopRep.homogeneousCochainsUniverseIso` of homogeneous cochain complexes and to an isomorphism
`TopRep.continuousCohomologyUniverseIso` of continuous cohomology in every degree, which sends
the class of a cocycle to the class of its image. All three are natural in compatible pairs
`(φ, f)`.

Taking `v = 0`, so that `max u v` is `u`, compares the two universe parameters at which
Tau Ceti's cohomological-dimension invariants can be read for coefficients in `Type u`.

## Main definitions

* `TopRep.resolutionXUniverseIso`: the two coinduced resolutions agree, degree by degree.
* `TopRep.homogeneousCochainsUniverseIso`: the two homogeneous cochain complexes are isomorphic.
* `TopRep.continuousCohomologyUniverseIso`: the two continuous cohomology objects are isomorphic.

## Main results

* `TopRep.d_comp_resolutionXUniverseIso_hom`: the comparison commutes with the differentials.
* `TopRep.continuousCohomologyUniverseIso_hom_cochainClass` and
  `TopRep.π_comp_continuousCohomologyUniverseIso_hom`: the comparison sends the class of a
  cocycle to the class of its image under the cochain comparison.
* `TauCeti.ContinuousCohomology.map_comp_continuousCohomologyUniverseIso_hom`: the comparison is
  natural in compatible pairs, as are its cochain and resolution levels
  (`cochainsMap_comp_homogeneousCochainsUniverseIso_hom` and
  `resolutionMap_comp_resolutionXUniverseIso_hom`).
-/

public section

open CategoryTheory

universe w u v

namespace TopRep

variable {k : Type w} [Ring k] [TopologicalSpace k] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] (X : TopRep.{max u v} k G)

/-- The coinduced resolutions of `X` at the universe parameters `max u v` and `v` agree in every
degree: the identity in degree zero, and postcomposition with the previous component on the
function space `C(G, -)` in degree `n + 1`. -/
noncomputable def resolutionXUniverseIso :
    (n : ℕ) → resolutionX.{w, u, max u v} X n ≅ resolutionX.{w, u, v} X n
  | 0 => Iso.refl _
  | n + 1 => (coind₁Functor k G).mapIso (resolutionXUniverseIso n)

@[simp]
theorem resolutionXUniverseIso_zero : resolutionXUniverseIso X 0 = Iso.refl _ :=
  (rfl)

theorem resolutionXUniverseIso_succ (n : ℕ) :
    resolutionXUniverseIso X (n + 1) = (coind₁Functor k G).mapIso (resolutionXUniverseIso X n) :=
  (rfl)

/-- In degree `n + 1` the comparison is postcomposition with its degree-`n` component. -/
@[simp]
theorem resolutionXUniverseIso_succ_hom_apply_apply (n : ℕ)
    (F : (resolutionX.{w, u, max u v} X (n + 1)).V) (x : G) :
    (resolutionXUniverseIso X (n + 1)).hom.hom F x = (resolutionXUniverseIso X n).hom.hom (F x) :=
  (rfl)

/-- In degree `n + 1` the inverse comparison is postcomposition with the inverse of its
degree-`n` component. -/
@[simp]
theorem resolutionXUniverseIso_succ_inv_apply_apply (n : ℕ)
    (F : (resolutionX.{w, u, v} X (n + 1)).V) (x : G) :
    (resolutionXUniverseIso X (n + 1)).inv.hom F x = (resolutionXUniverseIso X n).inv.hom (F x) :=
  (rfl)

/-- The comparison of the two coinduced resolutions commutes with their differentials. -/
@[reassoc]
theorem d_comp_resolutionXUniverseIso_hom (n : ℕ) :
    d.{w, u, max u v} X n ≫ (resolutionXUniverseIso X (n + 1)).hom =
      (resolutionXUniverseIso X n).hom ≫ d.{w, u, v} X n := by
  induction n with
  | zero =>
    rw [resolutionXUniverseIso_succ, resolutionXUniverseIso_zero, Functor.mapIso_refl,
      Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
    -- both sides are `ofHom X.ρ.coind₁ι`, built at the two universe parameters
    rfl
  | succ n ih =>
    -- `d (n + 1) = coind₁ι - coind₁ (d n)`: the first term commutes with the comparison by
    -- naturality of `coind₁ι`, the second by the induction hypothesis
    rw [d_succ, d_succ, Preadditive.sub_comp, Preadditive.comp_sub]
    refine congrArg₂ (· - ·) (coind₁ι.naturality (resolutionXUniverseIso X (n + 1)).hom).symm ?_
    rw [resolutionXUniverseIso_succ, Functor.mapIso_hom, ← Functor.map_comp, ih,
      Functor.map_comp, ← Functor.mapIso_hom, ← resolutionXUniverseIso_succ]

/-- The comparison of the shifted coinduced resolutions, as an isomorphism of complexes. -/
private noncomputable def resolution'UniverseIso :
    resolution'.{w, u, max u v} X ≅ resolution'.{w, u, v} X :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ resolutionXUniverseIso X (n + 1)) <| by
    rintro i _ rfl
    simp only [CochainComplex.of_d, resolution'd_eq]
    exact (d_comp_resolutionXUniverseIso_hom X (i + 1)).symm

/-- The homogeneous cochain complexes of `X` at the universe parameters `max u v` and `v` are
isomorphic: the comparison of the coinduced resolutions, restricted to invariants. -/
noncomputable def homogeneousCochainsUniverseIso :
    homogeneousCochains.{w, u, max u v} X ≅ homogeneousCochains.{w, u, v} X :=
  ((invariantsFunctor k G).mapHomologicalComplex _).mapIso (resolution'UniverseIso X)

/-- The cochain comparison is the resolution comparison, applied to an invariant function. -/
-- Not a `simp` lemma: `simp` rewrites the type of the left-hand side through
-- `CategoryTheory.Functor.mapHomologicalComplex_obj_X`, so the statement is not in `simp`-normal
-- form.
theorem coe_homogeneousCochainsUniverseIso_hom_f_apply (n : ℕ)
    (σ : (homogeneousCochains.{w, u, max u v} X).X n) :
    (((homogeneousCochainsUniverseIso X).hom.f n).hom σ).1 =
      (resolutionXUniverseIso X (n + 1)).hom.hom σ.1 :=
  (rfl)

/-- The inverse cochain comparison is the inverse resolution comparison, applied to an invariant
function. -/
-- Not a `simp` lemma: `simp` rewrites the type of the left-hand side through
-- `CategoryTheory.Functor.mapHomologicalComplex_obj_X`, so the statement is not in `simp`-normal
-- form.
theorem coe_homogeneousCochainsUniverseIso_inv_f_apply (n : ℕ)
    (σ : (homogeneousCochains.{w, u, v} X).X n) :
    (((homogeneousCochainsUniverseIso X).inv.f n).hom σ).1 =
      (resolutionXUniverseIso X (n + 1)).inv.hom σ.1 :=
  (rfl)

/-- The continuous cohomology of `X` at the universe parameters `max u v` and `v` agrees in
every degree: the map induced on homology by `homogeneousCochainsUniverseIso`. -/
noncomputable def continuousCohomologyUniverseIso (n : ℕ) :
    continuousCohomology.{w, u, max u v} n X ≅ continuousCohomology.{w, u, v} n X :=
  HomologicalComplex.homologyMapIso (homogeneousCochainsUniverseIso X) n

/-- The cohomology comparison sends the class of a cocycle to the class of its image under the
cochain comparison. -/
@[reassoc (attr := simp)]
theorem π_comp_continuousCohomologyUniverseIso_hom (n : ℕ) :
    ContinuousCohomology.π.{w, u, max u v} X n ≫ (continuousCohomologyUniverseIso X n).hom =
      HomologicalComplex.cyclesMap (homogeneousCochainsUniverseIso X).hom n ≫
        ContinuousCohomology.π.{w, u, v} X n :=
  HomologicalComplex.homologyπ_naturality _ n

/-- **The cohomology comparison sends the class of a cocycle to the class of its image** under
the cochain comparison. -/
@[simp]
theorem continuousCohomologyUniverseIso_hom_cochainClass {n : ℕ}
    (a : (homogeneousCochains.{w, u, max u v} X).X n)
    (ha : ((homogeneousCochains.{w, u, max u v} X).d n (n + 1)).hom a = 0) :
    (continuousCohomologyUniverseIso X n).hom (X.cochainClass n a ha) =
      X.cochainClass n (((homogeneousCochainsUniverseIso X).hom.f n).hom a) (by
        rw [← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm,
          ConcreteCategory.comp_apply, ha, map_zero]) := by
  rw [cochainClass_def, cochainClass_def]
  exact HomologicalComplex.homologyMap_homologyπ_cyclesMkOfEq _ _ _ _ _

end TopRep

namespace TauCeti.ContinuousCohomology

open _root_.ContinuousCohomology _root_.TopRep _root_.ContRepresentation

variable {k : Type w} [Ring k] [TopologicalSpace k] {G H : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep.{max u v} k G} {Y : TopRep.{max u v} k H}

/-- The comparison of coinduced resolutions is natural in compatible pairs `(φ, f)`. -/
@[reassoc]
theorem resolutionMap_comp_resolutionXUniverseIso_hom (φ : H →ₜ* G) (f : res φ X ⟶ Y)
    (n : ℕ) :
    resolutionMap.{w, u, max u v} φ f n ≫ (resolutionXUniverseIso Y n).hom =
      (resFunctor (φ : H →* G)).map (resolutionXUniverseIso X n).hom ≫
        resolutionMap.{w, u, v} φ f n := by
  induction n with
  | zero =>
    rw [resolutionMap_zero, resolutionMap_zero, resolutionXUniverseIso_zero,
      resolutionXUniverseIso_zero, Iso.refl_hom, Iso.refl_hom, CategoryTheory.Functor.map_id,
      Category.comp_id, Category.id_comp]
  | succ n ih =>
    rw [resolutionMap_succ, resolutionMap_succ, resolutionXUniverseIso_succ,
      resolutionXUniverseIso_succ, Functor.mapIso_hom, Functor.mapIso_hom]
    ext : 1
    -- both sides are `coind₁ResMap φ` of the two sides of the induction hypothesis
    exact (coind₁Map_comp_coind₁ResMap φ _ _).trans <|
      (congrArg (coind₁ResMap φ) congr($(ih).hom)).trans
        (coind₁ResMap_comp_coind₁Map_restrict φ _ _).symm

/-- The comparison of homogeneous cochain complexes is natural in compatible pairs `(φ, f)`. -/
@[reassoc]
theorem cochainsMap_comp_homogeneousCochainsUniverseIso_hom (φ : H →ₜ* G) (f : res φ X ⟶ Y) :
    cochainsMap.{w, u, max u v} φ f ≫ (homogeneousCochainsUniverseIso Y).hom =
      (homogeneousCochainsUniverseIso X).hom ≫ cochainsMap.{w, u, v} φ f := by
  ext n : 1
  exact (invariantsResMap_comp _ _ _).symm.trans <|
    (congrArg _ (resolutionMap_comp_resolutionXUniverseIso_hom φ f (n + 1))).trans
      (invariantsResMap_map_comp _ _ _)

/-- **The comparison of continuous cohomology is natural** in compatible pairs `(φ, f)`. -/
@[reassoc]
theorem map_comp_continuousCohomologyUniverseIso_hom (φ : H →ₜ* G) (f : res φ X ⟶ Y)
    (n : ℕ) :
    map.{w, u, max u v} φ f n ≫ (continuousCohomologyUniverseIso Y n).hom =
      (continuousCohomologyUniverseIso X n).hom ≫ map.{w, u, v} φ f n := by
  simp only [map, continuousCohomologyUniverseIso, HomologicalComplex.homologyMapIso_hom,
    ← HomologicalComplex.homologyMap_comp, cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

end TauCeti.ContinuousCohomology
