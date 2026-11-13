/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Additive
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero

/-!
# Independence of continuous cohomology from the extra universe parameter

For a topological ring `R : Type u` and a topological group `G : Type v`, Mathlib's coinduced
resolution `TopRep.resolutionX`, homogeneous cochain complex `TopRep.homogeneousCochains`, and
continuous cohomology `continuousCohomology` take a representation in `TopRep.{max v w, u, v} R G`
for an auxiliary universe parameter `w`, so that `C(G, -)` stays in the same carrier universe.

When a representation `X : TopRep.{v, u, v} R G` already has its carrier in `Type v`, both
instantiations `w = v` and `w = 0` accept `X` (since `max v v` and `max v 0` both reduce
definitionally to `v`) and produce complexes in `CochainComplex (TopModuleCat.{v, u} R) ℕ` and
cohomology objects in `TopModuleCat.{v, u} R`. Because the recursion over `n : ℕ` in
`TopRep.resolutionX.{u, v, w}` is universe-polymorphic in `w`, however, the resulting objects at
`w = v` and `w = 0` are not definitionally equal.

This file builds the canonical comparison between the two instantiations for every topological
group `G` and every `X : TopRep.{v, u, v} R G`:

* On the coinduced resolution (`TopRep.resolutionXUniverseIso`), the isomorphism in degree `0` is
  the identity of `X`, and in degree `n + 1` it is the image of the degree-`n` isomorphism under
  `TopRep.coind₁Functor R G`, i.e. postcomposition on `C(G, -)` with inverse given by
  postcomposition with the inverse.
* It commutes with the diagonal `G`-action, the coinduction unit `coind₁ι`, and the differentials
  `TopRep.d`, assembling into chain isomorphisms `TopRep.resolutionUniverseIso` and
  `TopRep.resolution'UniverseIso`, and on `G`-invariants into an isomorphism of homogeneous cochain
  complexes `TopRep.homogeneousCochainsUniverseIso`.
* Passing to cycles and homology yields isomorphisms `TopRep.cocyclesUniverseIso` and
  `TopRep.continuousCohomologyUniverseIso` in `TopModuleCat.{v, u} R` that carry the class of a
  homogeneous cocycle (`TopRep.cochainClass`) to the class of its image, agree in degree `0` with
  `ContinuousCohomology.zeroIso` and `TauCeti.ContinuousCohomology.degreeZeroClass`, reduce to the
  identity isomorphism when `G : Type 0`, and commute with compatible-pair functoriality
  (`ContinuousCohomology.map`), coefficient maps, restriction, and inflation.
* As consequences, cardinality (`Nat.card`), triviality (`Subsingleton`), and primary components
  (`AddCommGroup.primaryComponent`) of `continuousCohomology n X` agree at `w = v` and `w = 0`.

## Main definitions

* `TopRep.resolutionXUniverseIso`: degreewise isomorphism between `TopRep.resolutionX.{u, v, v} X n`
  and `TopRep.resolutionX.{u, v, 0} X n`.
* `TopRep.resolutionUniverseIso`, `TopRep.resolution'UniverseIso`: the corresponding chain
  isomorphisms on unshifted and shifted coinduced resolutions.
* `TopRep.homogeneousCochainsUniverseIso`: the chain isomorphism between
  `TopRep.homogeneousCochains.{u, v, v} X` and `TopRep.homogeneousCochains.{u, v, 0} X`.
* `TopRep.cocyclesUniverseIso`, `TopRep.continuousCohomologyUniverseIso`: the induced isomorphisms
  in `TopModuleCat.{v, u} R` on cocycles and continuous cohomology.
* `TopRep.continuousCohomologyPrimaryComponentUniverseEquiv`: the induced additive equivalence on
  `p`-primary components of continuous cohomology.
* `TauCeti.ContinuousCohomology.continuousCohomologyFunctorUniverseIso`,
  `TauCeti.ContinuousCohomology.continuousCochainsFunctorCompHomologyUniverseIso`: natural
  isomorphisms between `continuousCohomologyFunctor` (and
  `continuousCochainsFunctor ⋙ homologyFunctor`) at `w = v` and `w = 0`.

## Main results

* `TopRep.continuousCohomologyUniverseIso_hom_cochainClass`: the cohomology comparison sends the
  class of a homogeneous cocycle to the class of its image under the cochain isomorphism.
* `TopRep.continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom` and
  `TopRep.continuousCohomologyUniverseIso_zero_hom_degreeZeroClass`: compatibility in degree zero
  with invariants and `degreeZeroClass`.
* `TopRep.continuousCohomologyUniverseIso_eq_refl`: at `G : Type 0`, the two parameters coincide and
  the comparison is the identity isomorphism in every degree.
* `TauCeti.ContinuousCohomology.map_comp_continuousCohomologyUniverseIso_hom`,
  `coeffMap_comp_continuousCohomologyUniverseIso_hom`,
  `res_comp_continuousCohomologyUniverseIso_hom`,
  `infl_comp_continuousCohomologyUniverseIso_hom`: naturality with respect to compatible pairs and
  their named instances.
* `TopRep.subsingleton_continuousCohomology_universe_iff` and
  `TopRep.primaryComponent_continuousCohomology_universe_eq_bot_iff`: invariance of vanishing and of
  triviality of `p`-primary components across the two universe parameters.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2.
-/

public section

open CategoryTheory

namespace TopRep

universe u v

section Resolution

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Universe comparison on the coinduced resolution.** For `X : TopRep.{v, u, v} R G`, the
terms `TopRep.resolutionX.{u, v, v} X n` and `TopRep.resolutionX.{u, v, 0} X n` are canonically
isomorphic in `TopRep.{v, u, v} R G`: by the identity of `X` in degree `0`, and by postcomposition
on `C(G, -)` via `TopRep.coind₁Functor R G` in successor degrees. -/
def resolutionXUniverseIso (X : TopRep.{v, u, v} R G) :
    (n : ℕ) → TopRep.resolutionX.{u, v, v} X n ≅ TopRep.resolutionX.{u, v, 0} X n
  | 0 => Iso.refl X
  | n + 1 => (TopRep.coind₁Functor R G).mapIso (resolutionXUniverseIso X n)

/-- In degree zero, `resolutionXUniverseIso` is the identity isomorphism of `X`. -/
@[simp]
theorem resolutionXUniverseIso_zero (X : TopRep.{v, u, v} R G) :
    X.resolutionXUniverseIso 0 = Iso.refl X :=
  (rfl)

/-- In degree zero, the forward map of `resolutionXUniverseIso` is the identity on elements. -/
theorem resolutionXUniverseIso_zero_hom_apply (X : TopRep.{v, u, v} R G) (x : X.V) :
    (X.resolutionXUniverseIso 0).hom.hom x = x :=
  (rfl)

/-- In degree zero, the inverse map of `resolutionXUniverseIso` is the identity on elements. -/
theorem resolutionXUniverseIso_zero_inv_apply (X : TopRep.{v, u, v} R G) (x : X.V) :
    (X.resolutionXUniverseIso 0).inv.hom x = x :=
  (rfl)

/-- In degree `n + 1`, `resolutionXUniverseIso` applies `TopRep.coind₁Functor R G` to the degree-`n`
isomorphism. -/
theorem resolutionXUniverseIso_succ (X : TopRep.{v, u, v} R G) (n : ℕ) :
    X.resolutionXUniverseIso (n + 1) =
      (TopRep.coind₁Functor R G).mapIso (X.resolutionXUniverseIso n) :=
  (rfl)

/-- On a successor level `C(G, -)`, the forward map of `resolutionXUniverseIso` postcomposes with
the previous degree's forward map. -/
@[simp]
theorem resolutionXUniverseIso_succ_hom_apply (X : TopRep.{v, u, v} R G) (n : ℕ)
    (F : (TopRep.resolutionX.{u, v, v} X (n + 1)).V) (g : G) :
    ((X.resolutionXUniverseIso (n + 1)).hom.hom F :
        C(G, (TopRep.resolutionX.{u, v, 0} X n).V)) g =
      (X.resolutionXUniverseIso n).hom.hom
        ((F : C(G, (TopRep.resolutionX.{u, v, v} X n).V)) g) :=
  (rfl)

/-- On a successor level `C(G, -)`, the inverse map of `resolutionXUniverseIso` postcomposes with
the previous degree's inverse map. -/
@[simp]
theorem resolutionXUniverseIso_succ_inv_apply (X : TopRep.{v, u, v} R G) (n : ℕ)
    (F : (TopRep.resolutionX.{u, v, 0} X (n + 1)).V) (g : G) :
    ((X.resolutionXUniverseIso (n + 1)).inv.hom F :
        C(G, (TopRep.resolutionX.{u, v, v} X n).V)) g =
      (X.resolutionXUniverseIso n).inv.hom
        ((F : C(G, (TopRep.resolutionX.{u, v, 0} X n).V)) g) :=
  (rfl)

/-- The forward map of `resolutionXUniverseIso` intertwines the `G`-actions on the two resolution
terms. -/
theorem resolutionXUniverseIso_hom_ρ_apply (X : TopRep.{v, u, v} R G) (n : ℕ) (g : G)
    (x : (TopRep.resolutionX.{u, v, v} X n).V) :
    (X.resolutionXUniverseIso n).hom.hom ((TopRep.resolutionX.{u, v, v} X n).ρ g x) =
      (TopRep.resolutionX.{u, v, 0} X n).ρ g ((X.resolutionXUniverseIso n).hom.hom x) :=
  hom_comm_apply (X.resolutionXUniverseIso n).hom g x

/-- The inverse map of `resolutionXUniverseIso` intertwines the `G`-actions on the two resolution
terms. -/
theorem resolutionXUniverseIso_inv_ρ_apply (X : TopRep.{v, u, v} R G) (n : ℕ) (g : G)
    (x : (TopRep.resolutionX.{u, v, 0} X n).V) :
    (X.resolutionXUniverseIso n).inv.hom ((TopRep.resolutionX.{u, v, 0} X n).ρ g x) =
      (TopRep.resolutionX.{u, v, v} X n).ρ g ((X.resolutionXUniverseIso n).inv.hom x) :=
  hom_comm_apply (X.resolutionXUniverseIso n).inv g x

/-- `resolutionXUniverseIso` commutes with the coinduction unit `coind₁ι` embedding each level as
constant functions into the next. -/
@[reassoc]
theorem resolutionXUniverseIso_hom_comp_coind₁ι (X : TopRep.{v, u, v} R G) (n : ℕ) :
    (X.resolutionXUniverseIso n).hom ≫
        ofHom (TopRep.resolutionX.{u, v, 0} X n).ρ.coind₁ι =
      ofHom (TopRep.resolutionX.{u, v, v} X n).ρ.coind₁ι ≫
        (X.resolutionXUniverseIso (n + 1)).hom := by
  ext x g
  rfl

/-- The inverse of `resolutionXUniverseIso` commutes with the coinduction unit `coind₁ι`. -/
@[reassoc]
theorem resolutionXUniverseIso_inv_comp_coind₁ι (X : TopRep.{v, u, v} R G) (n : ℕ) :
    (X.resolutionXUniverseIso n).inv ≫
        ofHom (TopRep.resolutionX.{u, v, v} X n).ρ.coind₁ι =
      ofHom (TopRep.resolutionX.{u, v, 0} X n).ρ.coind₁ι ≫
        (X.resolutionXUniverseIso (n + 1)).inv := by
  ext x g
  rfl

/-- **`resolutionXUniverseIso` commutes with the differentials of the coinduced resolutions.** -/
@[reassoc]
theorem resolutionXUniverseIso_hom_comp_d (X : TopRep.{v, u, v} R G) (n : ℕ) :
    (X.resolutionXUniverseIso n).hom ≫ TopRep.d.{u, v, 0} X n =
      TopRep.d.{u, v, v} X n ≫ (X.resolutionXUniverseIso (n + 1)).hom := by
  induction n with
  | zero => exact X.resolutionXUniverseIso_hom_comp_coind₁ι 0
  | succ n ih =>
    rw [TopRep.d_succ, TopRep.d_succ, Preadditive.comp_sub, Preadditive.sub_comp,
      X.resolutionXUniverseIso_hom_comp_coind₁ι (n + 1)]
    congr 1
    rw [X.resolutionXUniverseIso_succ n, X.resolutionXUniverseIso_succ (n + 1),
      Functor.mapIso_hom, Functor.mapIso_hom, ← Functor.map_comp, ih, Functor.map_comp]

/-- The inverse of `resolutionXUniverseIso` commutes with the differentials of the coinduced
resolutions. -/
@[reassoc]
theorem resolutionXUniverseIso_inv_comp_d (X : TopRep.{v, u, v} R G) (n : ℕ) :
    (X.resolutionXUniverseIso n).inv ≫ TopRep.d.{u, v, v} X n =
      TopRep.d.{u, v, 0} X n ≫ (X.resolutionXUniverseIso (n + 1)).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact (X.resolutionXUniverseIso_hom_comp_d n).symm

/-- Elementwise form of `resolutionXUniverseIso_hom_comp_d`. -/
theorem resolutionXUniverseIso_hom_d_apply (X : TopRep.{v, u, v} R G) (n : ℕ)
    (x : (TopRep.resolutionX.{u, v, v} X n).V) :
    (TopRep.d.{u, v, 0} X n).hom ((X.resolutionXUniverseIso n).hom.hom x) =
      (X.resolutionXUniverseIso (n + 1)).hom.hom ((TopRep.d.{u, v, v} X n).hom x) :=
  ConcreteCategory.congr_hom (X.resolutionXUniverseIso_hom_comp_d n) x

/-- Elementwise form of `resolutionXUniverseIso_inv_comp_d`. -/
theorem resolutionXUniverseIso_inv_d_apply (X : TopRep.{v, u, v} R G) (n : ℕ)
    (x : (TopRep.resolutionX.{u, v, 0} X n).V) :
    (TopRep.d.{u, v, v} X n).hom ((X.resolutionXUniverseIso n).inv.hom x) =
      (X.resolutionXUniverseIso (n + 1)).inv.hom ((TopRep.d.{u, v, 0} X n).hom x) :=
  ConcreteCategory.congr_hom (X.resolutionXUniverseIso_inv_comp_d n) x

/-- **Chain isomorphism on the unshifted coinduced resolution.** -/
def resolutionUniverseIso (X : TopRep.{v, u, v} R G) :
    TopRep.resolution.{u, v, v} X ≅ TopRep.resolution.{u, v, 0} X :=
  HomologicalComplex.Hom.isoOfComponents X.resolutionXUniverseIso <| by
    rintro i j (rfl : i + 1 = j)
    simp only [CochainComplex.of_d]
    exact X.resolutionXUniverseIso_hom_comp_d i

/-- In degree `n`, the forward map of `resolutionUniverseIso` is `resolutionXUniverseIso n`. -/
@[simp]
theorem resolutionUniverseIso_hom_f (X : TopRep.{v, u, v} R G) (n : ℕ) :
    X.resolutionUniverseIso.hom.f n = (X.resolutionXUniverseIso n).hom :=
  (rfl)

/-- In degree `n`, the inverse map of `resolutionUniverseIso` is
`(resolutionXUniverseIso n).inv`. -/
@[simp]
theorem resolutionUniverseIso_inv_f (X : TopRep.{v, u, v} R G) (n : ℕ) :
    X.resolutionUniverseIso.inv.f n = (X.resolutionXUniverseIso n).inv :=
  (rfl)

/-- **Chain isomorphism on the shifted coinduced resolution.** -/
def resolution'UniverseIso (X : TopRep.{v, u, v} R G) :
    TopRep.resolution'.{u, v, v} X ≅ TopRep.resolution'.{u, v, 0} X :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ X.resolutionXUniverseIso (n + 1)) <| by
    rintro i j (rfl : i + 1 = j)
    simp only [CochainComplex.of_d, TopRep.resolution'd_eq]
    exact X.resolutionXUniverseIso_hom_comp_d (i + 1)

/-- In degree `n`, the forward map of `resolution'UniverseIso` is
`resolutionXUniverseIso (n + 1)`. -/
@[simp]
theorem resolution'UniverseIso_hom_f (X : TopRep.{v, u, v} R G) (n : ℕ) :
    X.resolution'UniverseIso.hom.f n = (X.resolutionXUniverseIso (n + 1)).hom :=
  (rfl)

/-- In degree `n`, the inverse map of `resolution'UniverseIso` is
`(resolutionXUniverseIso (n + 1)).inv`. -/
@[simp]
theorem resolution'UniverseIso_inv_f (X : TopRep.{v, u, v} R G) (n : ℕ) :
    X.resolution'UniverseIso.inv.f n = (X.resolutionXUniverseIso (n + 1)).inv :=
  (rfl)

/-! ### Homogeneous cochains -/

/-- **Chain isomorphism between the homogeneous cochain complexes at the two universe
parameters.** Obtained by restricting `resolution'UniverseIso` to `G`-invariants. -/
def homogeneousCochainsUniverseIso (X : TopRep.{v, u, v} R G) :
    TopRep.homogeneousCochains.{u, v, v} X ≅ TopRep.homogeneousCochains.{u, v, 0} X :=
  ((TopRep.invariantsFunctor R G).mapHomologicalComplex _).mapIso X.resolution'UniverseIso

/-- In degree `n`, the forward map of `homogeneousCochainsUniverseIso` is the restriction of
`resolutionXUniverseIso (n + 1)` to `G`-invariants. -/
theorem homogeneousCochainsUniverseIso_hom_f (X : TopRep.{v, u, v} R G) (n : ℕ) :
    X.homogeneousCochainsUniverseIso.hom.f n =
      (TopRep.invariantsFunctor R G).map (X.resolutionXUniverseIso (n + 1)).hom :=
  (rfl)

/-- In degree `n`, the inverse map of `homogeneousCochainsUniverseIso` is the restriction of
`(resolutionXUniverseIso (n + 1)).inv` to `G`-invariants. -/
theorem homogeneousCochainsUniverseIso_inv_f (X : TopRep.{v, u, v} R G) (n : ℕ) :
    X.homogeneousCochainsUniverseIso.inv.f n =
      (TopRep.invariantsFunctor R G).map (X.resolutionXUniverseIso (n + 1)).inv :=
  (rfl)

/-- On underlying elements of the shifted resolution, the forward map of
`homogeneousCochainsUniverseIso` acts as `resolutionXUniverseIso (n + 1)`. -/
theorem coe_homogeneousCochainsUniverseIso_hom_f_apply (X : TopRep.{v, u, v} R G) (n : ℕ)
    (σ : (TopRep.homogeneousCochains.{u, v, v} X).X n) :
    ((X.homogeneousCochainsUniverseIso.hom.f n) σ).1 =
      (X.resolutionXUniverseIso (n + 1)).hom.hom σ.1 :=
  (rfl)

/-- On underlying elements of the shifted resolution, the inverse map of
`homogeneousCochainsUniverseIso` acts as `(resolutionXUniverseIso (n + 1)).inv`. -/
theorem coe_homogeneousCochainsUniverseIso_inv_f_apply (X : TopRep.{v, u, v} R G) (n : ℕ)
    (σ : (TopRep.homogeneousCochains.{u, v, 0} X).X n) :
    ((X.homogeneousCochainsUniverseIso.inv.f n) σ).1 =
      (X.resolutionXUniverseIso (n + 1)).inv.hom σ.1 :=
  (rfl)

/-- In degree `0`, `homogeneousCochainsUniverseIso` preserves the pointwise values of a homogeneous
`0`-cochain in `C(G, X)`. -/
theorem coe_homogeneousCochainsUniverseIso_hom_f_zero_apply (X : TopRep.{v, u, v} R G)
    (σ : (TopRep.homogeneousCochains.{u, v, v} X).X 0) (g : G) :
    (((X.homogeneousCochainsUniverseIso.hom.f 0) σ).1 : C(G, X.V)) g = (σ.1 : C(G, X.V)) g :=
  (rfl)

/-- In degree `0`, the inverse of `homogeneousCochainsUniverseIso` preserves pointwise values in
`C(G, X)`. -/
theorem coe_homogeneousCochainsUniverseIso_inv_f_zero_apply (X : TopRep.{v, u, v} R G)
    (σ : (TopRep.homogeneousCochains.{u, v, 0} X).X 0) (g : G) :
    (((X.homogeneousCochainsUniverseIso.inv.f 0) σ).1 : C(G, X.V)) g = (σ.1 : C(G, X.V)) g :=
  (rfl)

/-- In degree `1`, `homogeneousCochainsUniverseIso` preserves the two-argument values of a
homogeneous `1`-cochain in `C(G, C(G, X))`. -/
theorem coe_homogeneousCochainsUniverseIso_hom_f_one_apply (X : TopRep.{v, u, v} R G)
    (σ : (TopRep.homogeneousCochains.{u, v, v} X).X 1) (g₀ g₁ : G) :
    (((X.homogeneousCochainsUniverseIso.hom.f 1) σ).1 : C(G, C(G, X.V))) g₀ g₁ =
      (σ.1 : C(G, C(G, X.V))) g₀ g₁ :=
  (rfl)

/-- In degree `1`, the inverse of `homogeneousCochainsUniverseIso` preserves two-argument values in
`C(G, C(G, X))`. -/
theorem coe_homogeneousCochainsUniverseIso_inv_f_one_apply (X : TopRep.{v, u, v} R G)
    (σ : (TopRep.homogeneousCochains.{u, v, 0} X).X 1) (g₀ g₁ : G) :
    (((X.homogeneousCochainsUniverseIso.inv.f 1) σ).1 : C(G, C(G, X.V))) g₀ g₁ =
      (σ.1 : C(G, C(G, X.V))) g₀ g₁ :=
  (rfl)

/-! ### Cocycles and continuous cohomology -/

/-- **Universe comparison on continuous cocycles**, as an isomorphism in `TopModuleCat.{v, u} R`. -/
noncomputable def cocyclesUniverseIso (X : TopRep.{v, u, v} R G) (n : ℕ) :
    _root_.ContinuousCohomology.cocycles.{u, v, v} X n ≅
      _root_.ContinuousCohomology.cocycles.{u, v, 0} X n :=
  (HomologicalComplex.cyclesFunctor (TopModuleCat.{v, u} R) (ComplexShape.up ℕ) n).mapIso
    X.homogeneousCochainsUniverseIso

/-- The forward map of `cocyclesUniverseIso` is `HomologicalComplex.cyclesMap` of the cochain
isomorphism. -/
theorem cocyclesUniverseIso_hom (X : TopRep.{v, u, v} R G) (n : ℕ) :
    (X.cocyclesUniverseIso n).hom =
      HomologicalComplex.cyclesMap X.homogeneousCochainsUniverseIso.hom n :=
  (rfl)

/-- The inverse map of `cocyclesUniverseIso` is `HomologicalComplex.cyclesMap` of the inverse
cochain isomorphism. -/
theorem cocyclesUniverseIso_inv (X : TopRep.{v, u, v} R G) (n : ℕ) :
    (X.cocyclesUniverseIso n).inv =
      HomologicalComplex.cyclesMap X.homogeneousCochainsUniverseIso.inv n :=
  (rfl)

/-- `cocyclesUniverseIso` intertwines the inclusions `iCycles` into the homogeneous cochains. -/
@[reassoc (attr := simp)]
theorem cocyclesUniverseIso_hom_iCycles (X : TopRep.{v, u, v} R G) (n : ℕ) :
    (X.cocyclesUniverseIso n).hom ≫
        (TopRep.homogeneousCochains.{u, v, 0} X).iCycles n =
      (TopRep.homogeneousCochains.{u, v, v} X).iCycles n ≫
        X.homogeneousCochainsUniverseIso.hom.f n :=
  HomologicalComplex.cyclesMap_i X.homogeneousCochainsUniverseIso.hom n

/-- The inverse of `cocyclesUniverseIso` intertwines the inclusions `iCycles` into the homogeneous
cochains. -/
@[reassoc (attr := simp)]
theorem cocyclesUniverseIso_inv_iCycles (X : TopRep.{v, u, v} R G) (n : ℕ) :
    (X.cocyclesUniverseIso n).inv ≫
        (TopRep.homogeneousCochains.{u, v, v} X).iCycles n =
      (TopRep.homogeneousCochains.{u, v, 0} X).iCycles n ≫
        X.homogeneousCochainsUniverseIso.inv.f n :=
  HomologicalComplex.cyclesMap_i X.homogeneousCochainsUniverseIso.inv n

/-- **Universe comparison on continuous cohomology.** For `X : TopRep.{v, u, v} R G`, the canonical
continuous cohomology objects `continuousCohomology.{u, v, v} n X` and
`continuousCohomology.{u, v, 0} n X` are canonically isomorphic in `TopModuleCat.{v, u} R` via the
chain isomorphism `homogeneousCochainsUniverseIso`. -/
noncomputable def continuousCohomologyUniverseIso (X : TopRep.{v, u, v} R G) (n : ℕ) :
    continuousCohomology.{u, v, v} n X ≅ continuousCohomology.{u, v, 0} n X :=
  (HomologicalComplex.homologyFunctor (TopModuleCat.{v, u} R) (ComplexShape.up ℕ) n).mapIso
    X.homogeneousCochainsUniverseIso

/-- The forward map of `continuousCohomologyUniverseIso` is the map on homology induced by
`homogeneousCochainsUniverseIso.hom`. -/
theorem continuousCohomologyUniverseIso_hom (X : TopRep.{v, u, v} R G) (n : ℕ) :
    (X.continuousCohomologyUniverseIso n).hom =
      HomologicalComplex.homologyMap X.homogeneousCochainsUniverseIso.hom n :=
  (rfl)

/-- The inverse map of `continuousCohomologyUniverseIso` is the map on homology induced by
`homogeneousCochainsUniverseIso.inv`. -/
theorem continuousCohomologyUniverseIso_inv (X : TopRep.{v, u, v} R G) (n : ℕ) :
    (X.continuousCohomologyUniverseIso n).inv =
      HomologicalComplex.homologyMap X.homogeneousCochainsUniverseIso.inv n :=
  (rfl)

/-- `continuousCohomologyUniverseIso` commutes with the projection `ContinuousCohomology.π` from
cocycles to cohomology. -/
@[reassoc (attr := simp)]
theorem π_comp_continuousCohomologyUniverseIso_hom (X : TopRep.{v, u, v} R G) (n : ℕ) :
    _root_.ContinuousCohomology.π.{u, v, v} X n ≫ (X.continuousCohomologyUniverseIso n).hom =
      (X.cocyclesUniverseIso n).hom ≫ _root_.ContinuousCohomology.π.{u, v, 0} X n :=
  HomologicalComplex.homologyπ_naturality X.homogeneousCochainsUniverseIso.hom n

/-- The inverse of `continuousCohomologyUniverseIso` commutes with the projection
`ContinuousCohomology.π` from cocycles to cohomology. -/
@[reassoc (attr := simp)]
theorem π_comp_continuousCohomologyUniverseIso_inv (X : TopRep.{v, u, v} R G) (n : ℕ) :
    _root_.ContinuousCohomology.π.{u, v, 0} X n ≫ (X.continuousCohomologyUniverseIso n).inv =
      (X.cocyclesUniverseIso n).inv ≫ _root_.ContinuousCohomology.π.{u, v, v} X n :=
  HomologicalComplex.homologyπ_naturality X.homogeneousCochainsUniverseIso.inv n

/-- **Action on cocycle classes.** The forward isomorphism `continuousCohomologyUniverseIso` sends
the class of a homogeneous `n`-cocycle `a` to the class of its image under
`homogeneousCochainsUniverseIso`. -/
@[simp]
theorem continuousCohomologyUniverseIso_hom_cochainClass (X : TopRep.{v, u, v} R G) (n : ℕ)
    (a : (TopRep.homogeneousCochains.{u, v, v} X).X n)
    (ha : ((TopRep.homogeneousCochains.{u, v, v} X).d n (n + 1)).hom a = 0) :
    (X.continuousCohomologyUniverseIso n).hom (TopRep.cochainClass.{u, v, v} X n a ha) =
      TopRep.cochainClass.{u, v, 0} X n ((X.homogeneousCochainsUniverseIso.hom.f n).hom a) (by
        rw [← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm,
          ConcreteCategory.comp_apply, ha, map_zero]) := by
  rw [TopRep.cochainClass_def, TopRep.cochainClass_def, continuousCohomologyUniverseIso_hom]
  exact HomologicalComplex.homologyMap_homologyπ_cyclesMkOfEq _ _ _ _ _

/-- The inverse isomorphism `continuousCohomologyUniverseIso` sends the class of a homogeneous
`n`-cocycle `a` at `w = 0` to the class of its image under `homogeneousCochainsUniverseIso.inv`. -/
@[simp]
theorem continuousCohomologyUniverseIso_inv_cochainClass (X : TopRep.{v, u, v} R G) (n : ℕ)
    (a : (TopRep.homogeneousCochains.{u, v, 0} X).X n)
    (ha : ((TopRep.homogeneousCochains.{u, v, 0} X).d n (n + 1)).hom a = 0) :
    (X.continuousCohomologyUniverseIso n).inv (TopRep.cochainClass.{u, v, 0} X n a ha) =
      TopRep.cochainClass.{u, v, v} X n ((X.homogeneousCochainsUniverseIso.inv.f n).hom a) (by
        rw [← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm,
          ConcreteCategory.comp_apply, ha, map_zero]) := by
  rw [TopRep.cochainClass_def, TopRep.cochainClass_def, continuousCohomologyUniverseIso_inv]
  exact HomologicalComplex.homologyMap_homologyπ_cyclesMkOfEq _ _ _ _ _

/-! ### Compatibility in degree zero -/

/-- **In degree zero, `continuousCohomologyUniverseIso` commutes with
`ContinuousCohomology.zeroIso`.** Both cohomology objects project to the same invariant module
`X.invariants`. -/
@[reassoc (attr := simp)]
theorem continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom (X : TopRep.{v, u, v} R G) :
    (X.continuousCohomologyUniverseIso 0).hom ≫
        (_root_.ContinuousCohomology.zeroIso.{u, v, 0} X).hom =
      (_root_.ContinuousCohomology.zeroIso.{u, v, v} X).hom := by
  rw [← cancel_epi (_root_.ContinuousCohomology.π.{u, v, v} X 0),
    X.π_comp_continuousCohomologyUniverseIso_hom_assoc 0]
  ext σ
  simp only [ConcreteCategory.comp_apply]
  rw [TauCeti.ContinuousCohomology.coe_zeroIso_hom_π,
    TauCeti.ContinuousCohomology.coe_zeroIso_hom_π]
  have hi := ConcreteCategory.congr_hom (X.cocyclesUniverseIso_hom_iCycles 0) σ
  simp only [ConcreteCategory.comp_apply] at hi
  rw [hi]
  exact X.coe_homogeneousCochainsUniverseIso_hom_f_zero_apply _ 1

/-- In degree zero, the inverse of `continuousCohomologyUniverseIso` commutes with
`ContinuousCohomology.zeroIso`. -/
@[reassoc (attr := simp)]
theorem continuousCohomologyUniverseIso_zero_inv_comp_zeroIso_hom (X : TopRep.{v, u, v} R G) :
    (X.continuousCohomologyUniverseIso 0).inv ≫
        (_root_.ContinuousCohomology.zeroIso.{u, v, v} X).hom =
      (_root_.ContinuousCohomology.zeroIso.{u, v, 0} X).hom := by
  rw [Iso.inv_comp_eq]
  exact (X.continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom).symm

/-- `zeroIso.inv` followed by `continuousCohomologyUniverseIso` in degree zero is `zeroIso.inv` at
`w = 0`. -/
@[reassoc (attr := simp)]
theorem zeroIso_inv_comp_continuousCohomologyUniverseIso_zero_hom (X : TopRep.{v, u, v} R G) :
    (_root_.ContinuousCohomology.zeroIso.{u, v, v} X).inv ≫
        (X.continuousCohomologyUniverseIso 0).hom =
      (_root_.ContinuousCohomology.zeroIso.{u, v, 0} X).inv := by
  rw [Iso.inv_comp_eq, Iso.eq_comp_inv]
  exact X.continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom

/-- `zeroIso.inv` at `w = 0` followed by the inverse of `continuousCohomologyUniverseIso` in degree
zero is `zeroIso.inv` at `w = v`. -/
@[reassoc (attr := simp)]
theorem zeroIso_inv_comp_continuousCohomologyUniverseIso_zero_inv (X : TopRep.{v, u, v} R G) :
    (_root_.ContinuousCohomology.zeroIso.{u, v, 0} X).inv ≫
        (X.continuousCohomologyUniverseIso 0).inv =
      (_root_.ContinuousCohomology.zeroIso.{u, v, v} X).inv := by
  rw [Iso.inv_comp_eq, Iso.eq_comp_inv]
  exact X.continuousCohomologyUniverseIso_zero_inv_comp_zeroIso_hom

/-- **In degree zero, `continuousCohomologyUniverseIso` sends the degree-zero class of an invariant
element `m ∈ X^G` to the degree-zero class of the same `m`.** -/
@[simp]
theorem continuousCohomologyUniverseIso_zero_hom_degreeZeroClass (X : TopRep.{v, u, v} R G)
    (m : X.V) (hm : ∀ g : G, X.ρ g m = m) :
    (X.continuousCohomologyUniverseIso 0).hom
        (TauCeti.ContinuousCohomology.degreeZeroClass.{u, v, v} X m hm) =
      TauCeti.ContinuousCohomology.degreeZeroClass.{u, v, 0} X m hm := by
  apply (ConcreteCategory.bijective_of_isIso
    (_root_.ContinuousCohomology.zeroIso.{u, v, 0} X).hom).1
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom X.continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom
    (TauCeti.ContinuousCohomology.degreeZeroClass.{u, v, v} X m hm)
  simp only [ConcreteCategory.comp_apply] at h
  rw [h]
  simp only [TauCeti.ContinuousCohomology.coe_zeroIso_hom_degreeZeroClass]

/-- In degree zero, the inverse of `continuousCohomologyUniverseIso` preserves the degree-zero
class of every invariant element `m ∈ X^G`. -/
@[simp]
theorem continuousCohomologyUniverseIso_zero_inv_degreeZeroClass (X : TopRep.{v, u, v} R G)
    (m : X.V) (hm : ∀ g : G, X.ρ g m = m) :
    (X.continuousCohomologyUniverseIso 0).inv
        (TauCeti.ContinuousCohomology.degreeZeroClass.{u, v, 0} X m hm) =
      TauCeti.ContinuousCohomology.degreeZeroClass.{u, v, v} X m hm := by
  rw [← X.continuousCohomologyUniverseIso_zero_hom_degreeZeroClass m hm, Iso.hom_inv_id_apply]

/-! ### Cardinality, vanishing, and primary components -/

/-- The continuous cohomology groups at the two universe parameters have the same cardinality. -/
theorem natCard_continuousCohomology_universe_eq (X : TopRep.{v, u, v} R G) (n : ℕ) :
    Nat.card (continuousCohomology.{u, v, v} n X) =
      Nat.card (continuousCohomology.{u, v, 0} n X) :=
  Nat.card_congr (X.continuousCohomologyUniverseIso n).toContinuousLinearEquiv.toEquiv

/-- Continuous cohomology vanishes at `w = v` if and only if it vanishes at `w = 0`. -/
theorem subsingleton_continuousCohomology_universe_iff (X : TopRep.{v, u, v} R G) (n : ℕ) :
    Subsingleton (continuousCohomology.{u, v, v} n X) ↔
      Subsingleton (continuousCohomology.{u, v, 0} n X) :=
  (X.continuousCohomologyUniverseIso n).toContinuousLinearEquiv.toEquiv.subsingleton_congr

/-- **Additive equivalence between the `p`-primary components of continuous cohomology at the two
universe parameters.** -/
noncomputable def continuousCohomologyPrimaryComponentUniverseEquiv
    (X : TopRep.{v, u, v} R G) (n p : ℕ) :
    AddCommGroup.primaryComponent (continuousCohomology.{u, v, v} n X) p ≃+
      AddCommGroup.primaryComponent (continuousCohomology.{u, v, 0} n X) p where
  toFun x := ⟨(X.continuousCohomologyUniverseIso n).hom x.1, by
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.1 x.2
    exact AddCommGroup.mem_primaryComponent.2 ⟨k, by rw [← map_nsmul, hk, map_zero]⟩⟩
  invFun y := ⟨(X.continuousCohomologyUniverseIso n).inv y.1, by
    obtain ⟨k, hk⟩ := AddCommGroup.mem_primaryComponent.1 y.2
    exact AddCommGroup.mem_primaryComponent.2 ⟨k, by rw [← map_nsmul, hk, map_zero]⟩⟩
  left_inv x := Subtype.ext ((X.continuousCohomologyUniverseIso n).hom_inv_id_apply x.1)
  right_inv y := Subtype.ext ((X.continuousCohomologyUniverseIso n).inv_hom_id_apply y.1)
  map_add' x₁ x₂ := Subtype.ext (map_add _ x₁.1 x₂.1)

/-- `continuousCohomologyPrimaryComponentUniverseEquiv` acts on underlying cohomology classes by
`continuousCohomologyUniverseIso`. -/
@[simp]
theorem coe_continuousCohomologyPrimaryComponentUniverseEquiv_apply
    (X : TopRep.{v, u, v} R G) (n p : ℕ)
    (x : AddCommGroup.primaryComponent (continuousCohomology.{u, v, v} n X) p) :
    (X.continuousCohomologyPrimaryComponentUniverseEquiv n p x).1 =
      (X.continuousCohomologyUniverseIso n).hom x.1 :=
  (rfl)

/-- The inverse of `continuousCohomologyPrimaryComponentUniverseEquiv` acts on underlying
cohomology classes by `(continuousCohomologyUniverseIso n).inv`. -/
@[simp]
theorem coe_continuousCohomologyPrimaryComponentUniverseEquiv_symm_apply
    (X : TopRep.{v, u, v} R G) (n p : ℕ)
    (x : AddCommGroup.primaryComponent (continuousCohomology.{u, v, 0} n X) p) :
    ((X.continuousCohomologyPrimaryComponentUniverseEquiv n p).symm x).1 =
      (X.continuousCohomologyUniverseIso n).inv x.1 :=
  (rfl)

/-- The `p`-primary component of `continuousCohomology n X` is trivial at `w = v` if and only if
it is trivial at `w = 0`. -/
theorem primaryComponent_continuousCohomology_universe_eq_bot_iff
    (X : TopRep.{v, u, v} R G) (n p : ℕ) :
    AddCommGroup.primaryComponent (continuousCohomology.{u, v, v} n X) p = ⊥ ↔
      AddCommGroup.primaryComponent (continuousCohomology.{u, v, 0} n X) p = ⊥ := by
  have hs := (X.continuousCohomologyPrimaryComponentUniverseEquiv n p).toEquiv.subsingleton_congr
  exact ⟨fun h ↦ @AddSubgroup.eq_bot_of_subsingleton _ _ _ (hs.1 (h ▸ inferInstance)),
    fun h ↦ @AddSubgroup.eq_bot_of_subsingleton _ _ _ (hs.2 (h ▸ inferInstance))⟩

end Resolution

/-! ### Degeneration to the identity when `G : Type 0` -/

section TypeZero

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type 0} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- When `G : Type 0`, the two universe parameters `w = v` and `w = 0` coincide, and
`resolutionXUniverseIso` is the identity isomorphism in every degree. -/
@[simp]
theorem resolutionXUniverseIso_eq_refl (X : TopRep.{0, u, 0} R G) (n : ℕ) :
    X.resolutionXUniverseIso n = Iso.refl _ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [resolutionXUniverseIso_succ, ih, Functor.mapIso_refl]

/-- When `G : Type 0`, `resolutionUniverseIso` is the identity isomorphism. -/
@[simp]
theorem resolutionUniverseIso_eq_refl (X : TopRep.{0, u, 0} R G) :
    X.resolutionUniverseIso = Iso.refl _ := by
  ext n : 2
  simp [resolutionXUniverseIso_eq_refl]

/-- When `G : Type 0`, `resolution'UniverseIso` is the identity isomorphism. -/
@[simp]
theorem resolution'UniverseIso_eq_refl (X : TopRep.{0, u, 0} R G) :
    X.resolution'UniverseIso = Iso.refl _ := by
  ext n : 2
  simp [resolutionXUniverseIso_eq_refl]

/-- When `G : Type 0`, `homogeneousCochainsUniverseIso` is the identity isomorphism. -/
@[simp]
theorem homogeneousCochainsUniverseIso_eq_refl (X : TopRep.{0, u, 0} R G) :
    X.homogeneousCochainsUniverseIso = Iso.refl _ := by
  rw [homogeneousCochainsUniverseIso, resolution'UniverseIso_eq_refl, Functor.mapIso_refl]

/-- When `G : Type 0`, `cocyclesUniverseIso` is the identity isomorphism in every degree. -/
@[simp]
theorem cocyclesUniverseIso_eq_refl (X : TopRep.{0, u, 0} R G) (n : ℕ) :
    X.cocyclesUniverseIso n = Iso.refl _ := by
  rw [cocyclesUniverseIso, homogeneousCochainsUniverseIso_eq_refl, Functor.mapIso_refl]
  rfl

/-- When `G : Type 0`, `continuousCohomologyUniverseIso` is the identity isomorphism in every
degree. -/
@[simp]
theorem continuousCohomologyUniverseIso_eq_refl (X : TopRep.{0, u, 0} R G) (n : ℕ) :
    X.continuousCohomologyUniverseIso n = Iso.refl _ := by
  rw [continuousCohomologyUniverseIso, homogeneousCochainsUniverseIso_eq_refl, Functor.mapIso_refl]
  rfl

end TypeZero

end TopRep

namespace TauCeti.ContinuousCohomology

open TopRep

universe u v

section Naturality

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- **Naturality on the coinduced resolution.** For any compatible pair `(φ, f)`,
`ContinuousCohomology.resolutionMap` commutes with `TopRep.resolutionXUniverseIso`. -/
@[reassoc]
theorem resolutionMap_comp_resolutionXUniverseIso_hom (φ : H →ₜ* G)
    {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.resolutionMap.{u, v, v} φ f n ≫
        (Y.resolutionXUniverseIso n).hom =
      (TopRep.resFunctor (φ : H →* G)).map (X.resolutionXUniverseIso n).hom ≫
        _root_.ContinuousCohomology.resolutionMap.{u, v, 0} φ f n := by
  induction n with
  | zero =>
    ext x
    rfl
  | succ n ih =>
    ext F x
    exact ConcreteCategory.congr_hom ih
      ((F : C(G, (TopRep.resolutionX.{u, v, v} X n).V)) (φ x))

/-- Inverse naturality of `ContinuousCohomology.resolutionMap` with respect to
`TopRep.resolutionXUniverseIso`. -/
@[reassoc]
theorem resolutionMap_comp_resolutionXUniverseIso_inv (φ : H →ₜ* G)
    {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.resolutionMap.{u, v, 0} φ f n ≫
        (Y.resolutionXUniverseIso n).inv =
      (TopRep.resFunctor (φ : H →* G)).map (X.resolutionXUniverseIso n).inv ≫
        _root_.ContinuousCohomology.resolutionMap.{u, v, v} φ f n := by
  rw [Iso.comp_inv_eq, Category.assoc, ← (TopRep.resFunctor (φ : H →* G)).mapIso_inv,
    Iso.eq_inv_comp, Functor.mapIso_hom]
  exact (resolutionMap_comp_resolutionXUniverseIso_hom φ f n).symm

/-- **Naturality on homogeneous cochain complexes.** `ContinuousCohomology.cochainsMap` commutes
with `TopRep.homogeneousCochainsUniverseIso` for every compatible pair `(φ, f)`. -/
@[reassoc]
theorem cochainsMap_comp_homogeneousCochainsUniverseIso_hom (φ : H →ₜ* G)
    {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) :
    _root_.ContinuousCohomology.cochainsMap.{u, v, v} φ f ≫
        Y.homogeneousCochainsUniverseIso.hom =
      X.homogeneousCochainsUniverseIso.hom ≫
        _root_.ContinuousCohomology.cochainsMap.{u, v, 0} φ f := by
  ext n : 2
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    _root_.ContinuousCohomology.cochainsMap_f, _root_.ContinuousCohomology.cochainsMap_f,
    homogeneousCochainsUniverseIso_hom_f, homogeneousCochainsUniverseIso_hom_f,
    ← TopRep.invariantsResMap_comp, ← TopRep.invariantsResMap_map_comp,
    resolutionMap_comp_resolutionXUniverseIso_hom]

/-- Inverse naturality of `ContinuousCohomology.cochainsMap` with respect to
`TopRep.homogeneousCochainsUniverseIso`. -/
@[reassoc]
theorem cochainsMap_comp_homogeneousCochainsUniverseIso_inv (φ : H →ₜ* G)
    {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) :
    _root_.ContinuousCohomology.cochainsMap.{u, v, 0} φ f ≫
        Y.homogeneousCochainsUniverseIso.inv =
      X.homogeneousCochainsUniverseIso.inv ≫
        _root_.ContinuousCohomology.cochainsMap.{u, v, v} φ f := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (cochainsMap_comp_homogeneousCochainsUniverseIso_hom φ f).symm

/-- **Naturality on continuous cocycles.** `ContinuousCohomology.cocyclesMap` commutes with
`TopRep.cocyclesUniverseIso` for every compatible pair `(φ, f)`. -/
@[reassoc]
theorem cocyclesMap_comp_cocyclesUniverseIso_hom (φ : H →ₜ* G)
    {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.cocyclesMap.{u, v, v} φ f n ≫
        (Y.cocyclesUniverseIso n).hom =
      (X.cocyclesUniverseIso n).hom ≫
        _root_.ContinuousCohomology.cocyclesMap.{u, v, 0} φ f n := by
  simp only [_root_.ContinuousCohomology.cocyclesMap, cocyclesUniverseIso_hom,
    ← HomologicalComplex.cyclesMap_comp, cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

/-- Inverse naturality of `ContinuousCohomology.cocyclesMap` with respect to
`TopRep.cocyclesUniverseIso`. -/
@[reassoc]
theorem cocyclesMap_comp_cocyclesUniverseIso_inv (φ : H →ₜ* G)
    {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.cocyclesMap.{u, v, 0} φ f n ≫
        (Y.cocyclesUniverseIso n).inv =
      (X.cocyclesUniverseIso n).inv ≫
        _root_.ContinuousCohomology.cocyclesMap.{u, v, v} φ f n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (cocyclesMap_comp_cocyclesUniverseIso_hom φ f n).symm

/-- **Naturality on continuous cohomology.** `ContinuousCohomology.map` commutes with
`TopRep.continuousCohomologyUniverseIso` for every compatible pair `(φ, f)`. -/
@[reassoc]
theorem map_comp_continuousCohomologyUniverseIso_hom (φ : H →ₜ* G)
    {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.map.{u, v, v} φ f n ≫
        (Y.continuousCohomologyUniverseIso n).hom =
      (X.continuousCohomologyUniverseIso n).hom ≫
        _root_.ContinuousCohomology.map.{u, v, 0} φ f n := by
  simp only [_root_.ContinuousCohomology.map, continuousCohomologyUniverseIso_hom,
    ← HomologicalComplex.homologyMap_comp, cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

/-- Inverse naturality of `ContinuousCohomology.map` with respect to
`TopRep.continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem map_comp_continuousCohomologyUniverseIso_inv (φ : H →ₜ* G)
    {X : TopRep.{v, u, v} R G} {Y : TopRep.{v, u, v} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.map.{u, v, 0} φ f n ≫
        (Y.continuousCohomologyUniverseIso n).inv =
      (X.continuousCohomologyUniverseIso n).inv ≫
        _root_.ContinuousCohomology.map.{u, v, v} φ f n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (map_comp_continuousCohomologyUniverseIso_hom φ f n).symm

/-- **Naturality in coefficient morphisms**: `coeffMap` commutes with
`TopRep.continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem coeffMap_comp_continuousCohomologyUniverseIso_hom
    {X Y : TopRep.{v, u, v} R G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap.{u, v, v} f n ≫ (Y.continuousCohomologyUniverseIso n).hom =
      (X.continuousCohomologyUniverseIso n).hom ≫ coeffMap.{u, v, 0} f n := by
  rw [coeffMap_def, coeffMap_def]
  exact map_comp_continuousCohomologyUniverseIso_hom (ContinuousMonoidHom.id G) f n

/-- Inverse naturality of `coeffMap` with respect to `TopRep.continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem coeffMap_comp_continuousCohomologyUniverseIso_inv
    {X Y : TopRep.{v, u, v} R G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap.{u, v, 0} f n ≫ (Y.continuousCohomologyUniverseIso n).inv =
      (X.continuousCohomologyUniverseIso n).inv ≫ coeffMap.{u, v, v} f n := by
  rw [coeffMap_def, coeffMap_def]
  exact map_comp_continuousCohomologyUniverseIso_inv (ContinuousMonoidHom.id G) f n

/-- **Compatibility with restriction**: `res` commutes with
`TopRep.continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem res_comp_continuousCohomologyUniverseIso_hom (S : Subgroup G)
    (X : TopRep.{v, u, v} R G) (n : ℕ) :
    res.{u, v, v} S X n ≫
        ((TopRep.res (S.subtype : S →* G) X).continuousCohomologyUniverseIso n).hom =
      (X.continuousCohomologyUniverseIso n).hom ≫ res.{u, v, 0} S X n := by
  rw [res_def, res_def]
  exact map_comp_continuousCohomologyUniverseIso_hom (ContinuousMonoidHom.subgroupSubtype S) (𝟙 _) n

/-- Inverse compatibility of `res` with `TopRep.continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem res_comp_continuousCohomologyUniverseIso_inv (S : Subgroup G)
    (X : TopRep.{v, u, v} R G) (n : ℕ) :
    res.{u, v, 0} S X n ≫
        ((TopRep.res (S.subtype : S →* G) X).continuousCohomologyUniverseIso n).inv =
      (X.continuousCohomologyUniverseIso n).inv ≫ res.{u, v, v} S X n := by
  rw [res_def, res_def]
  exact map_comp_continuousCohomologyUniverseIso_inv (ContinuousMonoidHom.subgroupSubtype S) (𝟙 _) n

/-- **Compatibility with inflation**: `infl` commutes with
`TopRep.continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem infl_comp_continuousCohomologyUniverseIso_hom (N : Subgroup G) [N.Normal]
    (X : TopRep.{v, u, v} R G) (n : ℕ) :
    infl.{u, v, v} N X n ≫ (X.continuousCohomologyUniverseIso n).hom =
      ((TopRep.quotientToInvariants X N).continuousCohomologyUniverseIso n).hom ≫
        infl.{u, v, 0} N X n := by
  rw [infl_def, infl_def]
  exact map_comp_continuousCohomologyUniverseIso_hom (Subgroup.quotientMkContinuousMonoidHom N) _ n

/-- Inverse compatibility of `infl` with `TopRep.continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem infl_comp_continuousCohomologyUniverseIso_inv (N : Subgroup G) [N.Normal]
    (X : TopRep.{v, u, v} R G) (n : ℕ) :
    infl.{u, v, 0} N X n ≫ (X.continuousCohomologyUniverseIso n).inv =
      ((TopRep.quotientToInvariants X N).continuousCohomologyUniverseIso n).inv ≫
        infl.{u, v, v} N X n := by
  rw [infl_def, infl_def]
  exact map_comp_continuousCohomologyUniverseIso_inv (Subgroup.quotientMkContinuousMonoidHom N) _ n

end Naturality

section Functor

variable (R : Type u) [Ring R] [TopologicalSpace R]
  (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Natural isomorphism between the continuous cohomology functors at the two universe
parameters.** Both `continuousCohomologyFunctor.{u, v, v} R G n` and
`continuousCohomologyFunctor.{u, v, 0} R G n` are functors
`TopRep.{v, u, v} R G ⥤ TopModuleCat.{v, u} R`, naturally isomorphic via
`TopRep.continuousCohomologyUniverseIso`. -/
noncomputable def continuousCohomologyFunctorUniverseIso (n : ℕ) :
    continuousCohomologyFunctor.{u, v, v} R G n ≅
      continuousCohomologyFunctor.{u, v, 0} R G n :=
  NatIso.ofComponents (fun X ↦ X.continuousCohomologyUniverseIso n) fun f ↦
    coeffMap_comp_continuousCohomologyUniverseIso_hom f n

/-- The components of `continuousCohomologyFunctorUniverseIso` are
`TopRep.continuousCohomologyUniverseIso`. -/
@[simp]
theorem continuousCohomologyFunctorUniverseIso_hom_app (n : ℕ) (X : TopRep.{v, u, v} R G) :
    (continuousCohomologyFunctorUniverseIso R G n).hom.app X =
      (X.continuousCohomologyUniverseIso n).hom :=
  (rfl)

/-- The inverse components of `continuousCohomologyFunctorUniverseIso` are the inverses of
`TopRep.continuousCohomologyUniverseIso`. -/
@[simp]
theorem continuousCohomologyFunctorUniverseIso_inv_app (n : ℕ) (X : TopRep.{v, u, v} R G) :
    (continuousCohomologyFunctorUniverseIso R G n).inv.app X =
      (X.continuousCohomologyUniverseIso n).inv :=
  (rfl)

/-- The homology of `continuousCochainsFunctor R G` in degree `n` is naturally isomorphic to
`continuousCohomologyFunctor.{u, v, 0} R G n`, complementing
`continuousCochainsFunctorCompHomologyIso` (which targets parameter `w = v`). -/
noncomputable def continuousCochainsFunctorCompHomologyUniverseIso (n : ℕ) :
    continuousCochainsFunctor R G ⋙ HomologicalComplex.homologyFunctor _ _ n ≅
      continuousCohomologyFunctor.{u, v, 0} R G n :=
  NatIso.ofComponents (fun X ↦ X.continuousCohomologyUniverseIso n) fun f ↦ by
    simp only [Functor.comp_map, continuousCochainsFunctor_map, continuousCohomologyFunctor_map,
      coeffMap_def]
    exact map_comp_continuousCohomologyUniverseIso_hom (ContinuousMonoidHom.id G) f n

/-- The components of `continuousCochainsFunctorCompHomologyUniverseIso` are
`TopRep.continuousCohomologyUniverseIso`. -/
@[simp]
theorem continuousCochainsFunctorCompHomologyUniverseIso_hom_app (n : ℕ)
    (X : TopRep.{v, u, v} R G) :
    (continuousCochainsFunctorCompHomologyUniverseIso R G n).hom.app X =
      (X.continuousCohomologyUniverseIso n).hom :=
  (rfl)

/-- The inverse components of `continuousCochainsFunctorCompHomologyUniverseIso` are the inverses of
`TopRep.continuousCohomologyUniverseIso`. -/
@[simp]
theorem continuousCochainsFunctorCompHomologyUniverseIso_inv_app (n : ℕ)
    (X : TopRep.{v, u, v} R G) :
    (continuousCochainsFunctorCompHomologyUniverseIso R G n).inv.app X =
      (X.continuousCohomologyUniverseIso n).inv :=
  (rfl)

end Functor

end TauCeti.ContinuousCohomology
