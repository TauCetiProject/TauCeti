/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Instances.ZMod

/-!
# Universe comparison for homogeneous cochains and continuous cohomology

For a topological ring `k : Type u₁` and a topological group `G : Type u`, Mathlib's coinduced
resolution `TopRep.resolutionX`, homogeneous cochain complex `TopRep.homogeneousCochains`, cocycle
object `ContinuousCohomology.cocycles`, and continuous cohomology `continuousCohomology` carry an
extra universe parameter `v` so that coefficients in `TopRep.{max u v, u₁, u} k G` are closed under
applying `C(G, -)`.

Because `max u (max u v)` and `max u v` are definitionally equal, an object
`X : TopRep.{max u v, u₁, u} k G` admits both instantiations — at `max u v` and at `v` — inside
the same categories `TopRep.{max u v, u₁, u} k G`,
`CochainComplex (TopModuleCat.{max u v, u₁} k) ℕ`, and `TopModuleCat.{max u v, u₁} k`. In
particular, for `X : TopRep.{u, u₁, u} k G` (`v = 0`, using `max u 0 = u`), the instantiations at
`u` and at `0` live in the same category, yet are not definitionally equal because the structural
recursion of `TopRep.resolutionX` retains the raw universe parameter.

This file constructs the canonical comparison isomorphisms between the `max u v` and `v`
instantiations, from the coinduced resolution up to continuous cohomology:

* in resolution degree `0`, `TopRep.resolutionXUniverseIso` is the identity of `X`;
* in resolution degree `n + 1`, on `C(G, -)`, it is postcomposition with the degree-`n`
  isomorphism via `TopRep.coind₁Functor`.

Restricting to `G`-invariants yields the chain isomorphism `TopRep.homogeneousCochainsUniverseIso`,
and passing to cycles and homology yields `TopRep.cocyclesUniverseIso` and
`TopRep.continuousCohomologyUniverseIso`. These isomorphisms send cocycle classes to cocycle
classes, commute with `ContinuousCohomology.zeroIso` and degree-zero classes, are natural in
compatible pairs `(φ : H →ₜ* G, f : TopRep.res φ X ⟶ Y)` (hence in coefficient maps, restriction,
and inflation), collapse to the identity when `v` already has the form `max u w` (in particular at
`u = 0, v = 0`), and preserve triviality and `p`-primary components of cohomology groups. They say
nothing about changing the carrier universe of `X` itself to a strictly larger universe.

## Main definitions

* `TopRep.resolutionXUniverseIso`: levelwise isomorphism of `TopRep.resolutionX` between auxiliary
  universes `max u v` and `v`.
* `TopRep.resolutionUniverseIso`, `TopRep.resolution'UniverseIso`: chain isomorphisms on the
  unshifted and shifted coinduced resolutions.
* `TopRep.homogeneousCochainsUniverseIso`: chain isomorphism on `TopRep.homogeneousCochains`.
* `TopRep.cocyclesUniverseIso`: isomorphism on `ContinuousCohomology.cocycles`.
* `TopRep.continuousCohomologyUniverseIso`: isomorphism on `continuousCohomology` in
  `TopModuleCat k`.
* `TopRep.primaryComponentContinuousCohomologyUniverseAddEquiv`: additive equivalence between the
  `p`-primary components of `continuousCohomology` at `max u v` and at `v`.
* `TauCeti.ContinuousCohomology.continuousCohomologyUniverseNatIso`: natural isomorphism between
  the functors `continuousCohomologyFunctor` at `max u v` and at `v`.

## Main results

* `TopRep.π_comp_continuousCohomologyUniverseIso_hom` and
  `TopRep.continuousCohomologyUniverseIso_hom_cochainClass`: the cohomology comparison sends the
  class of a cocycle to the class of its image.
* `TopRep.continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom` and
  `TopRep.continuousCohomologyUniverseIso_zero_hom_degreeZeroClass`: compatibility in degree zero
  with `ContinuousCohomology.zeroIso` and `TauCeti.ContinuousCohomology.degreeZeroClass`.
* `TauCeti.ContinuousCohomology.map_comp_continuousCohomologyUniverseIso_hom`: naturality with
  respect to `ContinuousCohomology.map`, with specializations to `coeffMap`, `res`, `resLE`, and
  `infl`.
* `TopRep.continuousCohomologyUniverseIso_refl`: when `v = max u w` (in particular at `u = 0`,
  `v = 0`), the comparison is the identity isomorphism in every degree.
* `TopRep.subsingleton_continuousCohomology_max_iff` and
  `TopRep.primaryComponent_continuousCohomology_max_eq_bot_iff`: vanishing of continuous cohomology
  and of its `p`-primary component are invariant between `max u v` and `v` (and hence between `u`
  and `0`).

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2: the
  homogeneous cochain complex of continuous cohomology.
-/

public section

open CategoryTheory

universe u₁ u v w

namespace TopRep

variable {k : Type u₁} {G : Type u} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Levelwise comparison of the coinduced resolution -/

/-- The canonical isomorphism between the `n`-th terms of the coinduced resolution of
`X : TopRep.{max u v, u₁, u} k G` formed at auxiliary universe `max u v` and at `v`. It is the
identity of `X` in degree `0`, and postcomposition on `C(G, -)` with the previous degree's
isomorphism in degree `n + 1`. -/
def resolutionXUniverseIso (X : TopRep.{max u v, u₁, u} k G) :
    (n : ℕ) → TopRep.resolutionX.{u₁, u, max u v} X n ≅ TopRep.resolutionX.{u₁, u, v} X n
  | 0 => Iso.refl X
  | n + 1 => (TopRep.coind₁Functor k G).mapIso (resolutionXUniverseIso X n)

/-- In resolution degree zero, `resolutionXUniverseIso` is the identity isomorphism of `X`. -/
@[simp]
theorem resolutionXUniverseIso_zero (X : TopRep.{max u v, u₁, u} k G) :
    X.resolutionXUniverseIso 0 = Iso.refl X :=
  (rfl)

/-- In resolution degree `n + 1`, `resolutionXUniverseIso` is `TopRep.coind₁Functor` applied to the
degree-`n` isomorphism. -/
@[simp]
theorem resolutionXUniverseIso_succ (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    X.resolutionXUniverseIso (n + 1) =
      (TopRep.coind₁Functor k G).mapIso (X.resolutionXUniverseIso n) :=
  (rfl)

/-- In resolution degree zero, the forward map of `resolutionXUniverseIso` is the identity on
elements. -/
theorem resolutionXUniverseIso_zero_hom_apply (X : TopRep.{max u v, u₁, u} k G) (x : X.V) :
    (X.resolutionXUniverseIso.{u₁, u, v} 0).hom x = x :=
  (rfl)

/-- In resolution degree zero, the inverse map of `resolutionXUniverseIso` is the identity on
elements. -/
theorem resolutionXUniverseIso_zero_inv_apply (X : TopRep.{max u v, u₁, u} k G) (x : X.V) :
    (X.resolutionXUniverseIso.{u₁, u, v} 0).inv x = x :=
  (rfl)

/-- In resolution degree `n + 1`, the forward map of `resolutionXUniverseIso` acts on `C(G, -)` by
postcomposing with the degree-`n` forward map. -/
theorem resolutionXUniverseIso_succ_hom_apply_apply (X : TopRep.{max u v, u₁, u} k G) (n : ℕ)
    (F : (TopRep.resolutionX.{u₁, u, max u v} X (n + 1)).V) (g : G) :
    ((X.resolutionXUniverseIso.{u₁, u, v} (n + 1)).hom F :
        C(G, (TopRep.resolutionX.{u₁, u, v} X n).V)) g =
      (X.resolutionXUniverseIso.{u₁, u, v} n).hom
        ((F : C(G, (TopRep.resolutionX.{u₁, u, max u v} X n).V)) g) :=
  (rfl)

/-- In resolution degree `n + 1`, the inverse map of `resolutionXUniverseIso` acts on `C(G, -)` by
postcomposing with the degree-`n` inverse map. -/
theorem resolutionXUniverseIso_succ_inv_apply_apply (X : TopRep.{max u v, u₁, u} k G) (n : ℕ)
    (F : (TopRep.resolutionX.{u₁, u, v} X (n + 1)).V) (g : G) :
    ((X.resolutionXUniverseIso.{u₁, u, v} (n + 1)).inv F :
        C(G, (TopRep.resolutionX.{u₁, u, max u v} X n).V)) g =
      (X.resolutionXUniverseIso.{u₁, u, v} n).inv
        ((F : C(G, (TopRep.resolutionX.{u₁, u, v} X n).V)) g) :=
  (rfl)

/-- When the auxiliary universe already has the form `max u w` (in particular at `u = 0, w = 0`),
`resolutionXUniverseIso` is the identity isomorphism in every degree. -/
theorem resolutionXUniverseIso_refl (X : TopRep.{max u w, u₁, u} k G) :
    ∀ n : ℕ, resolutionXUniverseIso.{u₁, u, max u w} X n =
      Iso.refl (TopRep.resolutionX.{u₁, u, max u w} X n)
  | 0 => rfl
  | n + 1 => by
    rw [resolutionXUniverseIso_succ, resolutionXUniverseIso_refl X n, Functor.mapIso_refl]

/-- The forward map of `resolutionXUniverseIso` commutes with the coinduction unit `coind₁ι`. -/
@[reassoc]
theorem resolutionXUniverseIso_hom_comp_coind₁ι (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (X.resolutionXUniverseIso n).hom ≫
        TopRep.ofHom (TopRep.resolutionX.{u₁, u, v} X n).ρ.coind₁ι =
      TopRep.ofHom (TopRep.resolutionX.{u₁, u, max u v} X n).ρ.coind₁ι ≫
        (X.resolutionXUniverseIso (n + 1)).hom :=
  (TopRep.coind₁ι (k := k) (G := G)).naturality (X.resolutionXUniverseIso n).hom

/-- The inverse map of `resolutionXUniverseIso` commutes with the coinduction unit `coind₁ι`. -/
@[reassoc]
theorem resolutionXUniverseIso_inv_comp_coind₁ι (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (X.resolutionXUniverseIso n).inv ≫
        TopRep.ofHom (TopRep.resolutionX.{u₁, u, max u v} X n).ρ.coind₁ι =
      TopRep.ofHom (TopRep.resolutionX.{u₁, u, v} X n).ρ.coind₁ι ≫
        (X.resolutionXUniverseIso (n + 1)).inv :=
  (TopRep.coind₁ι (k := k) (G := G)).naturality (X.resolutionXUniverseIso n).inv

/-- The forward map of `resolutionXUniverseIso` commutes with the boundary maps `TopRep.d`. -/
@[reassoc]
theorem resolutionXUniverseIso_hom_comp_d (X : TopRep.{max u v, u₁, u} k G) :
    ∀ n : ℕ, (X.resolutionXUniverseIso n).hom ≫ TopRep.d.{u₁, u, v} X n =
      TopRep.d.{u₁, u, max u v} X n ≫ (X.resolutionXUniverseIso (n + 1)).hom
  | 0 => resolutionXUniverseIso_hom_comp_coind₁ι X 0
  | n + 1 => by
    rw [TopRep.d_succ, TopRep.d_succ, Preadditive.comp_sub, Preadditive.sub_comp]
    refine congrArg₂ (· - ·) (resolutionXUniverseIso_hom_comp_coind₁ι X (n + 1)) ?_
    rw [resolutionXUniverseIso_succ, Functor.mapIso_hom, resolutionXUniverseIso_succ,
      Functor.mapIso_hom, ← (TopRep.coind₁Functor k G).map_comp,
      ← (TopRep.coind₁Functor k G).map_comp, resolutionXUniverseIso_hom_comp_d X n]

/-- The inverse map of `resolutionXUniverseIso` commutes with the boundary maps `TopRep.d`. -/
@[reassoc]
theorem resolutionXUniverseIso_inv_comp_d (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (X.resolutionXUniverseIso n).inv ≫ TopRep.d.{u₁, u, max u v} X n =
      TopRep.d.{u₁, u, v} X n ≫ (X.resolutionXUniverseIso (n + 1)).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  exact (X.resolutionXUniverseIso_hom_comp_d n).symm

/-! ### Chain isomorphisms on resolutions and homogeneous cochains -/

/-- Chain isomorphism between the unshifted coinduced resolutions of `X` at auxiliary universes
`max u v` and `v`. -/
def resolutionUniverseIso (X : TopRep.{max u v, u₁, u} k G) :
    TopRep.resolution.{u₁, u, max u v} X ≅ TopRep.resolution.{u₁, u, v} X :=
  HomologicalComplex.Hom.isoOfComponents X.resolutionXUniverseIso fun i j hij ↦ by
    obtain rfl : i + 1 = j := hij
    simp only [CochainComplex.of_d]
    exact X.resolutionXUniverseIso_hom_comp_d i

/-- Degree-`n` forward component of `resolutionUniverseIso`. -/
@[simp]
theorem resolutionUniverseIso_hom_f (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (X.resolutionUniverseIso.hom).f n = (X.resolutionXUniverseIso n).hom :=
  (rfl)

/-- Degree-`n` inverse component of `resolutionUniverseIso`. -/
@[simp]
theorem resolutionUniverseIso_inv_f (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (X.resolutionUniverseIso.inv).f n = (X.resolutionXUniverseIso n).inv :=
  (rfl)

/-- When the auxiliary universe has the form `max u w`, `resolutionUniverseIso` is the identity. -/
theorem resolutionUniverseIso_refl (X : TopRep.{max u w, u₁, u} k G) :
    resolutionUniverseIso.{u₁, u, max u w} X =
      Iso.refl (TopRep.resolution.{u₁, u, max u w} X) := by
  ext n : 2
  rw [resolutionUniverseIso_hom_f, resolutionXUniverseIso_refl]
  rfl

/-- Chain isomorphism between the shifted coinduced resolutions `TopRep.resolution'` of `X` at
auxiliary universes `max u v` and `v`. -/
def resolution'UniverseIso (X : TopRep.{max u v, u₁, u} k G) :
    TopRep.resolution'.{u₁, u, max u v} X ≅ TopRep.resolution'.{u₁, u, v} X :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ X.resolutionXUniverseIso (n + 1)) fun i j hij ↦ by
    obtain rfl : i + 1 = j := hij
    simp only [CochainComplex.of_d, TopRep.resolution'd_eq]
    exact X.resolutionXUniverseIso_hom_comp_d (i + 1)

/-- Degree-`n` forward component of `resolution'UniverseIso`. -/
@[simp]
theorem resolution'UniverseIso_hom_f (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (X.resolution'UniverseIso.hom).f n = (X.resolutionXUniverseIso (n + 1)).hom :=
  (rfl)

/-- Degree-`n` inverse component of `resolution'UniverseIso`. -/
@[simp]
theorem resolution'UniverseIso_inv_f (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (X.resolution'UniverseIso.inv).f n = (X.resolutionXUniverseIso (n + 1)).inv :=
  (rfl)

/-- When the auxiliary universe has the form `max u w`, `resolution'UniverseIso` is the identity. -/
theorem resolution'UniverseIso_refl (X : TopRep.{max u w, u₁, u} k G) :
    resolution'UniverseIso.{u₁, u, max u w} X =
      Iso.refl (TopRep.resolution'.{u₁, u, max u w} X) := by
  ext n : 2
  rw [resolution'UniverseIso_hom_f, resolutionXUniverseIso_refl]
  rfl

/-- Chain isomorphism between the homogeneous cochain complexes `TopRep.homogeneousCochains` of `X`
at auxiliary universes `max u v` and `v`, obtained by restricting `resolution'UniverseIso` to
`G`-invariants. -/
def homogeneousCochainsUniverseIso (X : TopRep.{max u v, u₁, u} k G) :
    TopRep.homogeneousCochains.{u₁, u, max u v} X ≅ TopRep.homogeneousCochains.{u₁, u, v} X :=
  ((TopRep.invariantsFunctor k G).mapHomologicalComplex _).mapIso X.resolution'UniverseIso

/-- Degree-`n` forward component of `homogeneousCochainsUniverseIso`. -/
@[simp]
theorem homogeneousCochainsUniverseIso_hom_f (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (X.homogeneousCochainsUniverseIso.hom).f n =
      (TopRep.invariantsFunctor k G).map (X.resolutionXUniverseIso (n + 1)).hom :=
  (rfl)

/-- Degree-`n` inverse component of `homogeneousCochainsUniverseIso`. -/
@[simp]
theorem homogeneousCochainsUniverseIso_inv_f (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (X.homogeneousCochainsUniverseIso.inv).f n =
      (TopRep.invariantsFunctor k G).map (X.resolutionXUniverseIso (n + 1)).inv :=
  (rfl)

/-- On underlying coinduced-resolution elements, the forward component of
`homogeneousCochainsUniverseIso` in degree `n` applies `(X.resolutionXUniverseIso (n + 1)).hom`. -/
theorem coe_homogeneousCochainsUniverseIso_hom_f_apply (X : TopRep.{max u v, u₁, u} k G) (n : ℕ)
    (σ : (TopRep.homogeneousCochains.{u₁, u, max u v} X).X n) :
    (((X.homogeneousCochainsUniverseIso.{u₁, u, v}).hom.f n σ).val :
        (TopRep.resolutionX.{u₁, u, v} X (n + 1)).V) =
      (X.resolutionXUniverseIso.{u₁, u, v} (n + 1)).hom σ.val :=
  (rfl)

/-- On underlying coinduced-resolution elements, the inverse component of
`homogeneousCochainsUniverseIso` in degree `n` applies `(X.resolutionXUniverseIso (n + 1)).inv`. -/
theorem coe_homogeneousCochainsUniverseIso_inv_f_apply (X : TopRep.{max u v, u₁, u} k G) (n : ℕ)
    (σ : (TopRep.homogeneousCochains.{u₁, u, v} X).X n) :
    (((X.homogeneousCochainsUniverseIso.{u₁, u, v}).inv.f n σ).val :
        (TopRep.resolutionX.{u₁, u, max u v} X (n + 1)).V) =
      (X.resolutionXUniverseIso.{u₁, u, v} (n + 1)).inv σ.val :=
  (rfl)

/-- When the auxiliary universe has the form `max u w` (in particular at `u = 0, w = 0`),
`homogeneousCochainsUniverseIso` is the identity isomorphism. -/
theorem homogeneousCochainsUniverseIso_refl (X : TopRep.{max u w, u₁, u} k G) :
    homogeneousCochainsUniverseIso.{u₁, u, max u w} X =
      Iso.refl (TopRep.homogeneousCochains.{u₁, u, max u w} X) := by
  rw [homogeneousCochainsUniverseIso, resolution'UniverseIso_refl, Functor.mapIso_refl]

/-! ### Cocycles and continuous cohomology across universe parameters -/

/-- Canonical isomorphism in `TopModuleCat k` between the `n`-cocycles of `X` formed at auxiliary
universes `max u v` and `v`. -/
noncomputable def cocyclesUniverseIso (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    ContinuousCohomology.cocycles.{u₁, u, max u v} X n ≅
      ContinuousCohomology.cocycles.{u₁, u, v} X n :=
  (HomologicalComplex.cyclesFunctor (TopModuleCat k) _ n).mapIso X.homogeneousCochainsUniverseIso

/-- The forward morphism of `cocyclesUniverseIso` is `HomologicalComplex.cyclesMap` of the cochain
isomorphism. -/
theorem cocyclesUniverseIso_hom_def (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (X.cocyclesUniverseIso n).hom =
      HomologicalComplex.cyclesMap X.homogeneousCochainsUniverseIso.hom n :=
  (rfl)

/-- The inverse morphism of `cocyclesUniverseIso` is `HomologicalComplex.cyclesMap` of the inverse
cochain isomorphism. -/
theorem cocyclesUniverseIso_inv_def (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (X.cocyclesUniverseIso n).inv =
      HomologicalComplex.cyclesMap X.homogeneousCochainsUniverseIso.inv n :=
  (rfl)

/-- When the auxiliary universe has the form `max u w`, `cocyclesUniverseIso` is the identity. -/
theorem cocyclesUniverseIso_refl (X : TopRep.{max u w, u₁, u} k G) (n : ℕ) :
    cocyclesUniverseIso.{u₁, u, max u w} X n =
      Iso.refl (ContinuousCohomology.cocycles.{u₁, u, max u w} X n) := by
  rw [cocyclesUniverseIso, homogeneousCochainsUniverseIso_refl, Functor.mapIso_refl]
  rfl

/-- The forward cocycle comparison commutes with the inclusion `iCycles` into homogeneous
cochains. -/
@[reassoc (attr := simp)]
theorem cocyclesUniverseIso_hom_comp_iCycles (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (X.cocyclesUniverseIso.{u₁, u, v} n).hom ≫
        (TopRep.homogeneousCochains.{u₁, u, v} X).iCycles n =
      (TopRep.homogeneousCochains.{u₁, u, max u v} X).iCycles n ≫
        (X.homogeneousCochainsUniverseIso.{u₁, u, v}).hom.f n :=
  HomologicalComplex.cyclesMap_i X.homogeneousCochainsUniverseIso.hom n

/-- The inverse cocycle comparison commutes with the inclusion `iCycles` into homogeneous
cochains. -/
@[reassoc (attr := simp)]
theorem cocyclesUniverseIso_inv_comp_iCycles (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (X.cocyclesUniverseIso.{u₁, u, v} n).inv ≫
        (TopRep.homogeneousCochains.{u₁, u, max u v} X).iCycles n =
      (TopRep.homogeneousCochains.{u₁, u, v} X).iCycles n ≫
        (X.homogeneousCochainsUniverseIso.{u₁, u, v}).inv.f n :=
  HomologicalComplex.cyclesMap_i X.homogeneousCochainsUniverseIso.inv n

/-- Elementwise form of `cocyclesUniverseIso_hom_comp_iCycles`. -/
theorem iCycles_cocyclesUniverseIso_hom_apply (X : TopRep.{max u v, u₁, u} k G) (n : ℕ)
    (z : ContinuousCohomology.cocycles.{u₁, u, max u v} X n) :
    (TopRep.homogeneousCochains.{u₁, u, v} X).iCycles n
        ((X.cocyclesUniverseIso.{u₁, u, v} n).hom z) =
      (X.homogeneousCochainsUniverseIso.{u₁, u, v}).hom.f n
        ((TopRep.homogeneousCochains.{u₁, u, max u v} X).iCycles n z) :=
  ConcreteCategory.congr_hom (X.cocyclesUniverseIso_hom_comp_iCycles n) z

/-- Elementwise form of `cocyclesUniverseIso_inv_comp_iCycles`. -/
theorem iCycles_cocyclesUniverseIso_inv_apply (X : TopRep.{max u v, u₁, u} k G) (n : ℕ)
    (z : ContinuousCohomology.cocycles.{u₁, u, v} X n) :
    (TopRep.homogeneousCochains.{u₁, u, max u v} X).iCycles n
        ((X.cocyclesUniverseIso.{u₁, u, v} n).inv z) =
      (X.homogeneousCochainsUniverseIso.{u₁, u, v}).inv.f n
        ((TopRep.homogeneousCochains.{u₁, u, v} X).iCycles n z) :=
  ConcreteCategory.congr_hom (X.cocyclesUniverseIso_inv_comp_iCycles n) z

/-- `cocyclesUniverseIso` carries the cocycle built from a homogeneous `n`-cochain `a` to the
cocycle built from its image cochain. -/
@[simp]
theorem cocyclesUniverseIso_hom_cyclesMkOfEq (X : TopRep.{max u v, u₁, u} k G) (n : ℕ)
    (a : (TopRep.homogeneousCochains.{u₁, u, max u v} X).X n)
    (ha : ((TopRep.homogeneousCochains.{u₁, u, max u v} X).d n (n + 1)).hom a = 0) :
    (X.cocyclesUniverseIso.{u₁, u, v} n).hom
        ((TopRep.homogeneousCochains.{u₁, u, max u v} X).cyclesMkOfEq a (n + 1)
          (CochainComplex.next ℕ n) ha) =
      (TopRep.homogeneousCochains.{u₁, u, v} X).cyclesMkOfEq
        ((X.homogeneousCochainsUniverseIso.{u₁, u, v}).hom.f n a) (n + 1)
        (CochainComplex.next ℕ n) (by
          rw [← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm,
            ConcreteCategory.comp_apply, ha, map_zero]) := by
  apply (TopRep.homogeneousCochains.{u₁, u, v} X).iCycles_injective n
  rw [iCycles_cocyclesUniverseIso_hom_apply, HomologicalComplex.iCycles_cyclesMkOfEq,
    HomologicalComplex.iCycles_cyclesMkOfEq]

/-- The inverse of `cocyclesUniverseIso` carries the cocycle built from a homogeneous `n`-cochain
`a` to the cocycle built from its preimage cochain. -/
@[simp]
theorem cocyclesUniverseIso_inv_cyclesMkOfEq (X : TopRep.{max u v, u₁, u} k G) (n : ℕ)
    (a : (TopRep.homogeneousCochains.{u₁, u, v} X).X n)
    (ha : ((TopRep.homogeneousCochains.{u₁, u, v} X).d n (n + 1)).hom a = 0) :
    (X.cocyclesUniverseIso.{u₁, u, v} n).inv
        ((TopRep.homogeneousCochains.{u₁, u, v} X).cyclesMkOfEq a (n + 1)
          (CochainComplex.next ℕ n) ha) =
      (TopRep.homogeneousCochains.{u₁, u, max u v} X).cyclesMkOfEq
        ((X.homogeneousCochainsUniverseIso.{u₁, u, v}).inv.f n a) (n + 1)
        (CochainComplex.next ℕ n) (by
          rw [← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm,
            ConcreteCategory.comp_apply, ha, map_zero]) := by
  apply (TopRep.homogeneousCochains.{u₁, u, max u v} X).iCycles_injective n
  rw [iCycles_cocyclesUniverseIso_inv_apply, HomologicalComplex.iCycles_cyclesMkOfEq,
    HomologicalComplex.iCycles_cyclesMkOfEq]

/-- **Universe comparison for continuous cohomology.** For `X : TopRep.{max u v, u₁, u} k G`, the
continuous cohomology modules `continuousCohomology n X` formed at auxiliary universes `max u v`
and `v` are canonically isomorphic in `TopModuleCat k`. At `v = 0` (`max u 0 = u`), this identifies
`continuousCohomology.{u₁, u, u} n X` with `continuousCohomology.{u₁, u, 0} n X`. -/
noncomputable def continuousCohomologyUniverseIso (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    continuousCohomology.{u₁, u, max u v} n X ≅ continuousCohomology.{u₁, u, v} n X :=
  (HomologicalComplex.homologyFunctor (TopModuleCat k) _ n).mapIso X.homogeneousCochainsUniverseIso

/-- The forward morphism of `continuousCohomologyUniverseIso` is `HomologicalComplex.homologyMap`
of the cochain isomorphism. -/
theorem continuousCohomologyUniverseIso_hom_def (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (X.continuousCohomologyUniverseIso n).hom =
      HomologicalComplex.homologyMap X.homogeneousCochainsUniverseIso.hom n :=
  (rfl)

/-- The inverse morphism of `continuousCohomologyUniverseIso` is `HomologicalComplex.homologyMap`
of the inverse cochain isomorphism. -/
theorem continuousCohomologyUniverseIso_inv_def (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (X.continuousCohomologyUniverseIso n).inv =
      HomologicalComplex.homologyMap X.homogeneousCochainsUniverseIso.inv n :=
  (rfl)

/-- When the auxiliary universe has the form `max u w` (in particular at `u = 0, w = 0`),
`continuousCohomologyUniverseIso` is the identity isomorphism in every degree. -/
theorem continuousCohomologyUniverseIso_refl (X : TopRep.{max u w, u₁, u} k G) (n : ℕ) :
    continuousCohomologyUniverseIso.{u₁, u, max u w} X n =
      Iso.refl (continuousCohomology.{u₁, u, max u w} n X) := by
  rw [continuousCohomologyUniverseIso, homogeneousCochainsUniverseIso_refl, Functor.mapIso_refl]
  rfl

/-- **The forward cohomology comparison preserves cocycle classes.** -/
@[reassoc (attr := simp)]
theorem π_comp_continuousCohomologyUniverseIso_hom (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    ContinuousCohomology.π.{u₁, u, max u v} X n ≫ (X.continuousCohomologyUniverseIso n).hom =
      (X.cocyclesUniverseIso n).hom ≫ ContinuousCohomology.π.{u₁, u, v} X n :=
  HomologicalComplex.homologyπ_naturality X.homogeneousCochainsUniverseIso.hom n

/-- **The inverse cohomology comparison preserves cocycle classes.** -/
@[reassoc (attr := simp)]
theorem π_comp_continuousCohomologyUniverseIso_inv (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    ContinuousCohomology.π.{u₁, u, v} X n ≫ (X.continuousCohomologyUniverseIso n).inv =
      (X.cocyclesUniverseIso n).inv ≫ ContinuousCohomology.π.{u₁, u, max u v} X n :=
  HomologicalComplex.homologyπ_naturality X.homogeneousCochainsUniverseIso.inv n

/-- Elementwise form of `π_comp_continuousCohomologyUniverseIso_hom`: the comparison sends the
class of a cocycle `z` to the class of its image cocycle. -/
@[simp]
theorem continuousCohomologyUniverseIso_hom_π (X : TopRep.{max u v, u₁, u} k G) (n : ℕ)
    (z : ContinuousCohomology.cocycles.{u₁, u, max u v} X n) :
    (X.continuousCohomologyUniverseIso.{u₁, u, v} n).hom
        (ContinuousCohomology.π.{u₁, u, max u v} X n z) =
      ContinuousCohomology.π.{u₁, u, v} X n ((X.cocyclesUniverseIso.{u₁, u, v} n).hom z) :=
  ConcreteCategory.congr_hom (X.π_comp_continuousCohomologyUniverseIso_hom n) z

/-- Elementwise form of `π_comp_continuousCohomologyUniverseIso_inv`: the inverse comparison sends
the class of a cocycle `z` to the class of its preimage cocycle. -/
@[simp]
theorem continuousCohomologyUniverseIso_inv_π (X : TopRep.{max u v, u₁, u} k G) (n : ℕ)
    (z : ContinuousCohomology.cocycles.{u₁, u, v} X n) :
    (X.continuousCohomologyUniverseIso.{u₁, u, v} n).inv
        (ContinuousCohomology.π.{u₁, u, v} X n z) =
      ContinuousCohomology.π.{u₁, u, max u v} X n ((X.cocyclesUniverseIso.{u₁, u, v} n).inv z) :=
  ConcreteCategory.congr_hom (X.π_comp_continuousCohomologyUniverseIso_inv n) z

/-- `continuousCohomologyUniverseIso` carries the class `TopRep.cochainClass` of a homogeneous
cocycle `a` to the class of its image cochain. -/
@[simp]
theorem continuousCohomologyUniverseIso_hom_cochainClass (X : TopRep.{max u v, u₁, u} k G) (n : ℕ)
    (a : (TopRep.homogeneousCochains.{u₁, u, max u v} X).X n)
    (ha : ((TopRep.homogeneousCochains.{u₁, u, max u v} X).d n (n + 1)).hom a = 0) :
    (X.continuousCohomologyUniverseIso.{u₁, u, v} n).hom
        (TopRep.cochainClass.{u₁, u, max u v} X n a ha) =
      TopRep.cochainClass.{u₁, u, v} X n
        ((X.homogeneousCochainsUniverseIso.{u₁, u, v}).hom.f n a) (by
          rw [← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm,
            ConcreteCategory.comp_apply, ha, map_zero]) := by
  rw [cochainClass_def, cochainClass_def, continuousCohomologyUniverseIso_hom_π,
    cocyclesUniverseIso_hom_cyclesMkOfEq]

/-- The inverse of `continuousCohomologyUniverseIso` carries the class `TopRep.cochainClass` of a
homogeneous cocycle `a` to the class of its preimage cochain. -/
@[simp]
theorem continuousCohomologyUniverseIso_inv_cochainClass (X : TopRep.{max u v, u₁, u} k G) (n : ℕ)
    (a : (TopRep.homogeneousCochains.{u₁, u, v} X).X n)
    (ha : ((TopRep.homogeneousCochains.{u₁, u, v} X).d n (n + 1)).hom a = 0) :
    (X.continuousCohomologyUniverseIso.{u₁, u, v} n).inv
        (TopRep.cochainClass.{u₁, u, v} X n a ha) =
      TopRep.cochainClass.{u₁, u, max u v} X n
        ((X.homogeneousCochainsUniverseIso.{u₁, u, v}).inv.f n a) (by
          rw [← ConcreteCategory.comp_apply, HomologicalComplex.Hom.comm,
            ConcreteCategory.comp_apply, ha, map_zero]) := by
  rw [cochainClass_def, cochainClass_def, continuousCohomologyUniverseIso_inv_π,
    cocyclesUniverseIso_inv_cyclesMkOfEq]

/-! ### Compatibility in degree zero -/

/-- In degree zero, `continuousCohomologyUniverseIso` commutes with Mathlib's identification
`ContinuousCohomology.zeroIso` onto `X.invariants`. -/
@[reassoc (attr := simp)]
theorem continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom
    (X : TopRep.{max u v, u₁, u} k G) :
    (X.continuousCohomologyUniverseIso.{u₁, u, v} 0).hom ≫
        (ContinuousCohomology.zeroIso.{u₁, u, v} X).hom =
      (ContinuousCohomology.zeroIso.{u₁, u, max u v} X).hom := by
  ext x
  obtain ⟨z, rfl⟩ := (TopRep.homogeneousCochains.{u₁, u, max u v} X).homologyπ_surjective 0 x
  have hπ := X.continuousCohomologyUniverseIso_hom_π.{u₁, u, v} 0 z
  have hz : (((TopRep.homogeneousCochains.{u₁, u, v} X).iCycles 0
        ((X.cocyclesUniverseIso.{u₁, u, v} 0).hom z)).val : C(G, X.V)) 1 =
      (((TopRep.homogeneousCochains.{u₁, u, max u v} X).iCycles 0 z).val : C(G, X.V)) 1 := by
    rw [iCycles_cocyclesUniverseIso_hom_apply, coe_homogeneousCochainsUniverseIso_hom_f_apply,
      resolutionXUniverseIso_succ_hom_apply_apply, resolutionXUniverseIso_zero_hom_apply]
  simp only [ConcreteCategory.comp_apply]
  rw [hπ, TauCeti.ContinuousCohomology.coe_zeroIso_hom_π,
    TauCeti.ContinuousCohomology.coe_zeroIso_hom_π, hz]

/-- Inverse form of `continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom`. -/
@[reassoc (attr := simp)]
theorem continuousCohomologyUniverseIso_zero_inv_comp_zeroIso_hom
    (X : TopRep.{max u v, u₁, u} k G) :
    (X.continuousCohomologyUniverseIso.{u₁, u, v} 0).inv ≫
        (ContinuousCohomology.zeroIso.{u₁, u, max u v} X).hom =
      (ContinuousCohomology.zeroIso.{u₁, u, v} X).hom := by
  rw [Iso.inv_comp_eq]
  exact (X.continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom).symm

/-- `continuousCohomologyUniverseIso` preserves the degree-zero class of an invariant element. -/
@[simp]
theorem continuousCohomologyUniverseIso_zero_hom_degreeZeroClass
    (X : TopRep.{max u v, u₁, u} k G) (m : X.V) (hm : ∀ g : G, X.ρ g m = m) :
    (X.continuousCohomologyUniverseIso.{u₁, u, v} 0).hom
        (TauCeti.ContinuousCohomology.degreeZeroClass.{u₁, u, max u v} X m hm) =
      TauCeti.ContinuousCohomology.degreeZeroClass.{u₁, u, v} X m hm := by
  apply (ContinuousCohomology.zeroIso.{u₁, u, v} X).toContinuousLinearEquiv.injective
  have h := ConcreteCategory.congr_hom
    (X.continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom.{u₁, u, v})
    (TauCeti.ContinuousCohomology.degreeZeroClass.{u₁, u, max u v} X m hm)
  exact h.trans <| Subtype.ext <|
    (TauCeti.ContinuousCohomology.coe_zeroIso_hom_degreeZeroClass m hm).trans
      (TauCeti.ContinuousCohomology.coe_zeroIso_hom_degreeZeroClass m hm).symm

/-- The inverse of `continuousCohomologyUniverseIso` preserves the degree-zero class of an
invariant element. -/
@[simp]
theorem continuousCohomologyUniverseIso_zero_inv_degreeZeroClass
    (X : TopRep.{max u v, u₁, u} k G) (m : X.V) (hm : ∀ g : G, X.ρ g m = m) :
    (X.continuousCohomologyUniverseIso.{u₁, u, v} 0).inv
        (TauCeti.ContinuousCohomology.degreeZeroClass.{u₁, u, v} X m hm) =
      TauCeti.ContinuousCohomology.degreeZeroClass.{u₁, u, max u v} X m hm := by
  rw [← X.continuousCohomologyUniverseIso_zero_hom_degreeZeroClass.{u₁, u, v} m hm,
    Iso.hom_inv_id_apply]

/-! ### Preservation of vanishing and `p`-primary components -/

/-- Vanishing of `continuousCohomology n X` is equivalent at auxiliary universes `max u v` and
`v`. -/
theorem subsingleton_continuousCohomology_max_iff (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    Subsingleton (continuousCohomology.{u₁, u, max u v} n X) ↔
      Subsingleton (continuousCohomology.{u₁, u, v} n X) :=
  (X.continuousCohomologyUniverseIso n).toContinuousLinearEquiv.toEquiv.subsingleton_congr

/-- For `X : TopRep.{u, u₁, u} k G`, vanishing of `continuousCohomology n X` is equivalent at
auxiliary universes `u` and `0`. -/
theorem subsingleton_continuousCohomology_universe_iff (X : TopRep.{u, u₁, u} k G) (n : ℕ) :
    Subsingleton (continuousCohomology.{u₁, u, u} n X) ↔
      Subsingleton (continuousCohomology.{u₁, u, 0} n X) :=
  X.subsingleton_continuousCohomology_max_iff.{u₁, u, 0} n

/-- The forward map of `continuousCohomologyUniverseIso` preserves membership in the `p`-primary
component. -/
-- Not a `simp` lemma: Mathlib's `AddCommGroup.mem_primaryComponent` is already `@[simp]` and
-- rewrites the left-hand side to `∃ k, p ^ k • _ = 0`, so the `simpNF` linter rejects `@[simp]`
-- here; use with `rw` or `simp only`.
theorem mem_primaryComponent_continuousCohomologyUniverseIso_hom_iff
    (X : TopRep.{max u v, u₁, u} k G) (n p : ℕ)
    (x : continuousCohomology.{u₁, u, max u v} n X) :
    (X.continuousCohomologyUniverseIso.{u₁, u, v} n).hom x ∈
        AddCommGroup.primaryComponent (continuousCohomology.{u₁, u, v} n X) p ↔
      x ∈ AddCommGroup.primaryComponent (continuousCohomology.{u₁, u, max u v} n X) p := by
  let e := (X.continuousCohomologyUniverseIso.{u₁, u, v} n).toContinuousLinearEquiv
  simp only [AddCommGroup.mem_primaryComponent]
  refine exists_congr fun m ↦ ?_
  have hm : (X.continuousCohomologyUniverseIso.{u₁, u, v} n).hom (p ^ m • x) =
      p ^ m • (X.continuousCohomologyUniverseIso.{u₁, u, v} n).hom x :=
    map_nsmul e (p ^ m) x
  rw [← hm, ← (map_zero e : (X.continuousCohomologyUniverseIso.{u₁, u, v} n).hom 0 = 0)]
  exact e.injective.eq_iff

/-- The inverse map of `continuousCohomologyUniverseIso` preserves membership in the `p`-primary
component. -/
-- Not a `simp` lemma, for the same reason as
-- `mem_primaryComponent_continuousCohomologyUniverseIso_hom_iff`.
theorem mem_primaryComponent_continuousCohomologyUniverseIso_inv_iff
    (X : TopRep.{max u v, u₁, u} k G) (n p : ℕ)
    (x : continuousCohomology.{u₁, u, v} n X) :
    (X.continuousCohomologyUniverseIso.{u₁, u, v} n).inv x ∈
        AddCommGroup.primaryComponent (continuousCohomology.{u₁, u, max u v} n X) p ↔
      x ∈ AddCommGroup.primaryComponent (continuousCohomology.{u₁, u, v} n X) p := by
  rw [← X.mem_primaryComponent_continuousCohomologyUniverseIso_hom_iff.{u₁, u, v} n p,
    Iso.inv_hom_id_apply]

/-- Canonical additive equivalence between the `p`-primary components of `continuousCohomology n X`
at auxiliary universes `max u v` and `v`. -/
noncomputable def primaryComponentContinuousCohomologyUniverseAddEquiv
    (X : TopRep.{max u v, u₁, u} k G) (n p : ℕ) :
    AddCommGroup.primaryComponent (continuousCohomology.{u₁, u, max u v} n X) p ≃+
      AddCommGroup.primaryComponent (continuousCohomology.{u₁, u, v} n X) p where
  toFun x := ⟨(X.continuousCohomologyUniverseIso.{u₁, u, v} n).hom x.val,
    (X.mem_primaryComponent_continuousCohomologyUniverseIso_hom_iff n p x.val).2 x.prop⟩
  invFun y := ⟨(X.continuousCohomologyUniverseIso.{u₁, u, v} n).inv y.val,
    (X.mem_primaryComponent_continuousCohomologyUniverseIso_inv_iff n p y.val).2 y.prop⟩
  left_inv x := Subtype.ext (Iso.hom_inv_id_apply (X.continuousCohomologyUniverseIso n) x.val)
  right_inv y := Subtype.ext (Iso.inv_hom_id_apply (X.continuousCohomologyUniverseIso n) y.val)
  map_add' x₁ x₂ := Subtype.ext
    (map_add (X.continuousCohomologyUniverseIso n).toContinuousLinearEquiv x₁.val x₂.val)

/-- Underlying value of `primaryComponentContinuousCohomologyUniverseAddEquiv`. -/
@[simp]
theorem coe_primaryComponentContinuousCohomologyUniverseAddEquiv_apply
    (X : TopRep.{max u v, u₁, u} k G) (n p : ℕ)
    (x : AddCommGroup.primaryComponent (continuousCohomology.{u₁, u, max u v} n X) p) :
    ((X.primaryComponentContinuousCohomologyUniverseAddEquiv.{u₁, u, v} n p x) :
        continuousCohomology.{u₁, u, v} n X) =
      (X.continuousCohomologyUniverseIso.{u₁, u, v} n).hom x.val :=
  (rfl)

/-- Underlying value of `primaryComponentContinuousCohomologyUniverseAddEquiv.symm`. -/
@[simp]
theorem coe_primaryComponentContinuousCohomologyUniverseAddEquiv_symm_apply
    (X : TopRep.{max u v, u₁, u} k G) (n p : ℕ)
    (y : AddCommGroup.primaryComponent (continuousCohomology.{u₁, u, v} n X) p) :
    ((X.primaryComponentContinuousCohomologyUniverseAddEquiv.{u₁, u, v} n p).symm y :
        continuousCohomology.{u₁, u, max u v} n X) =
      (X.continuousCohomologyUniverseIso.{u₁, u, v} n).inv y.val :=
  (rfl)

/-- Vanishing of the `p`-primary component of `continuousCohomology n X` is equivalent at auxiliary
universes `max u v` and `v`. -/
theorem primaryComponent_continuousCohomology_max_eq_bot_iff
    (X : TopRep.{max u v, u₁, u} k G) (n p : ℕ) :
    AddCommGroup.primaryComponent (continuousCohomology.{u₁, u, max u v} n X) p = ⊥ ↔
      AddCommGroup.primaryComponent (continuousCohomology.{u₁, u, v} n X) p = ⊥ := by
  simp only [AddSubgroup.eq_bot_iff_forall]
  refine ⟨fun h y hy ↦ ?_, fun h x hx ↦ ?_⟩
  · have hinv := h ((X.continuousCohomologyUniverseIso.{u₁, u, v} n).inv y)
      ((X.mem_primaryComponent_continuousCohomologyUniverseIso_inv_iff n p y).2 hy)
    rw [← Iso.inv_hom_id_apply (X.continuousCohomologyUniverseIso.{u₁, u, v} n) y, hinv, map_zero]
  · have hhom := h ((X.continuousCohomologyUniverseIso.{u₁, u, v} n).hom x)
      ((X.mem_primaryComponent_continuousCohomologyUniverseIso_hom_iff n p x).2 hx)
    rw [← Iso.hom_inv_id_apply (X.continuousCohomologyUniverseIso.{u₁, u, v} n) x, hhom, map_zero]

/-- For `X : TopRep.{u, u₁, u} k G`, vanishing of the `p`-primary component of
`continuousCohomology n X` is equivalent at auxiliary universes `u` and `0`. -/
theorem primaryComponent_continuousCohomology_universe_eq_bot_iff
    (X : TopRep.{u, u₁, u} k G) (n p : ℕ) :
    AddCommGroup.primaryComponent (continuousCohomology.{u₁, u, u} n X) p = ⊥ ↔
      AddCommGroup.primaryComponent (continuousCohomology.{u₁, u, 0} n X) p = ⊥ :=
  X.primaryComponent_continuousCohomology_max_eq_bot_iff.{u₁, u, 0} n p

end TopRep

namespace TauCeti.ContinuousCohomology

open _root_.ContinuousCohomology TopRep

variable {k : Type u₁} {G H : Type u} [Ring k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-! ### Naturality in compatible pairs, coefficient maps, restriction, and inflation -/

/-- `TopRep.resolutionXUniverseIso` commutes with `ContinuousCohomology.resolutionMap` for any
compatible pair `(φ, f)`. -/
@[reassoc]
theorem resFunctor_resolutionXUniverseIso_hom_comp_resolutionMap (φ : H →ₜ* G)
    {X : TopRep.{max u v, u₁, u} k G} {Y : TopRep.{max u v, u₁, u} k H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) :
    ∀ n : ℕ, (TopRep.resFunctor (φ : H →* G)).map (X.resolutionXUniverseIso.{u₁, u, v} n).hom ≫
        resolutionMap.{u₁, u, v} φ f n =
      resolutionMap.{u₁, u, max u v} φ f n ≫
        (Y.resolutionXUniverseIso.{u₁, u, v} n).hom
  | 0 => by
    rw [resolutionXUniverseIso_zero, resolutionXUniverseIso_zero, Iso.refl_hom, Iso.refl_hom,
      (TopRep.resFunctor (φ : H →* G)).map_id, Category.id_comp, Category.comp_id]
    rfl
  | n + 1 => by
    have ih := resFunctor_resolutionXUniverseIso_hom_comp_resolutionMap φ f n
    ext F h
    exact ConcreteCategory.congr_hom ih ((F : C(G, _)) (φ h))

/-- `TopRep.homogeneousCochainsUniverseIso` is natural with respect to
`ContinuousCohomology.cochainsMap` for any compatible pair `(φ, f)`. -/
@[reassoc]
theorem cochainsMap_comp_homogeneousCochainsUniverseIso_hom (φ : H →ₜ* G)
    {X : TopRep.{max u v, u₁, u} k G} {Y : TopRep.{max u v, u₁, u} k H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) :
    cochainsMap.{u₁, u, max u v} φ f ≫ (Y.homogeneousCochainsUniverseIso.{u₁, u, v}).hom =
      (X.homogeneousCochainsUniverseIso.{u₁, u, v}).hom ≫ cochainsMap.{u₁, u, v} φ f := by
  refine HomologicalComplex.Hom.ext (funext fun n ↦ ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    homogeneousCochainsUniverseIso_hom_f, homogeneousCochainsUniverseIso_hom_f,
    cochainsMap_f, cochainsMap_f, ← TopRep.invariantsResMap_comp,
    ← TopRep.invariantsResMap_map_comp, resFunctor_resolutionXUniverseIso_hom_comp_resolutionMap]

/-- Inverse form of `cochainsMap_comp_homogeneousCochainsUniverseIso_hom`. -/
@[reassoc]
theorem cochainsMap_comp_homogeneousCochainsUniverseIso_inv (φ : H →ₜ* G)
    {X : TopRep.{max u v, u₁, u} k G} {Y : TopRep.{max u v, u₁, u} k H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) :
    cochainsMap.{u₁, u, v} φ f ≫ (Y.homogeneousCochainsUniverseIso.{u₁, u, v}).inv =
      (X.homogeneousCochainsUniverseIso.{u₁, u, v}).inv ≫ cochainsMap.{u₁, u, max u v} φ f := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

/-- `TopRep.cocyclesUniverseIso` is natural with respect to `ContinuousCohomology.cocyclesMap`. -/
@[reassoc]
theorem cocyclesMap_comp_cocyclesUniverseIso_hom (φ : H →ₜ* G)
    {X : TopRep.{max u v, u₁, u} k G} {Y : TopRep.{max u v, u₁, u} k H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    cocyclesMap.{u₁, u, max u v} φ f n ≫ (Y.cocyclesUniverseIso.{u₁, u, v} n).hom =
      (X.cocyclesUniverseIso.{u₁, u, v} n).hom ≫ cocyclesMap.{u₁, u, v} φ f n := by
  rw [cocyclesUniverseIso_hom_def, cocyclesUniverseIso_hom_def, cocyclesMap, cocyclesMap,
    ← HomologicalComplex.cyclesMap_comp, ← HomologicalComplex.cyclesMap_comp,
    cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

/-- Inverse form of `cocyclesMap_comp_cocyclesUniverseIso_hom`. -/
@[reassoc]
theorem cocyclesMap_comp_cocyclesUniverseIso_inv (φ : H →ₜ* G)
    {X : TopRep.{max u v, u₁, u} k G} {Y : TopRep.{max u v, u₁, u} k H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    cocyclesMap.{u₁, u, v} φ f n ≫ (Y.cocyclesUniverseIso.{u₁, u, v} n).inv =
      (X.cocyclesUniverseIso.{u₁, u, v} n).inv ≫ cocyclesMap.{u₁, u, max u v} φ f n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, cocyclesMap_comp_cocyclesUniverseIso_hom]

/-- **Compatible-pair naturality of `continuousCohomologyUniverseIso`.** For any continuous group
homomorphism `φ : H →ₜ* G` and compatible morphism `f : TopRep.res φ X ⟶ Y`, the induced cohomology
maps at auxiliary universes `max u v` and `v` intertwine `continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem map_comp_continuousCohomologyUniverseIso_hom (φ : H →ₜ* G)
    {X : TopRep.{max u v, u₁, u} k G} {Y : TopRep.{max u v, u₁, u} k H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.map.{u₁, u, max u v} φ f n ≫
        (Y.continuousCohomologyUniverseIso.{u₁, u, v} n).hom =
      (X.continuousCohomologyUniverseIso.{u₁, u, v} n).hom ≫
        _root_.ContinuousCohomology.map.{u₁, u, v} φ f n := by
  rw [continuousCohomologyUniverseIso_hom_def, continuousCohomologyUniverseIso_hom_def,
    _root_.ContinuousCohomology.map, _root_.ContinuousCohomology.map,
    ← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

/-- Inverse form of `map_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc]
theorem map_comp_continuousCohomologyUniverseIso_inv (φ : H →ₜ* G)
    {X : TopRep.{max u v, u₁, u} k G} {Y : TopRep.{max u v, u₁, u} k H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.map.{u₁, u, v} φ f n ≫
        (Y.continuousCohomologyUniverseIso.{u₁, u, v} n).inv =
      (X.continuousCohomologyUniverseIso.{u₁, u, v} n).inv ≫
        _root_.ContinuousCohomology.map.{u₁, u, max u v} φ f n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    map_comp_continuousCohomologyUniverseIso_hom]

/-- Coefficient maps commute with `continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem coeffMap_comp_continuousCohomologyUniverseIso_hom
    {X Y : TopRep.{max u v, u₁, u} k G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap.{u₁, u, max u v} f n ≫ (Y.continuousCohomologyUniverseIso.{u₁, u, v} n).hom =
      (X.continuousCohomologyUniverseIso.{u₁, u, v} n).hom ≫ coeffMap.{u₁, u, v} f n := by
  rw [coeffMap_def, coeffMap_def]
  exact map_comp_continuousCohomologyUniverseIso_hom (ContinuousMonoidHom.id G) f n

/-- Inverse form of `coeffMap_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc]
theorem coeffMap_comp_continuousCohomologyUniverseIso_inv
    {X Y : TopRep.{max u v, u₁, u} k G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap.{u₁, u, v} f n ≫ (Y.continuousCohomologyUniverseIso.{u₁, u, v} n).inv =
      (X.continuousCohomologyUniverseIso.{u₁, u, v} n).inv ≫ coeffMap.{u₁, u, max u v} f n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    coeffMap_comp_continuousCohomologyUniverseIso_hom]

variable (k G) in
/-- **Natural isomorphism between continuous-cohomology functors across auxiliary universes.** -/
noncomputable def continuousCohomologyUniverseNatIso (n : ℕ) :
    continuousCohomologyFunctor.{u₁, u, max u v} k G n ≅
      continuousCohomologyFunctor.{u₁, u, v} k G n :=
  NatIso.ofComponents (fun X ↦ X.continuousCohomologyUniverseIso n) fun f ↦
    coeffMap_comp_continuousCohomologyUniverseIso_hom f n

/-- Forward component of `continuousCohomologyUniverseNatIso` at `X`. -/
@[simp]
theorem continuousCohomologyUniverseNatIso_hom_app (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (continuousCohomologyUniverseNatIso.{u₁, u, v} k G n).hom.app X =
      (X.continuousCohomologyUniverseIso.{u₁, u, v} n).hom :=
  (rfl)

/-- Inverse component of `continuousCohomologyUniverseNatIso` at `X`. -/
@[simp]
theorem continuousCohomologyUniverseNatIso_inv_app (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    (continuousCohomologyUniverseNatIso.{u₁, u, v} k G n).inv.app X =
      (X.continuousCohomologyUniverseIso.{u₁, u, v} n).inv :=
  (rfl)

/-- Restriction to a subgroup commutes with `continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem res_comp_continuousCohomologyUniverseIso_hom (S : Subgroup G)
    (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    res.{u₁, u, max u v} S X n ≫
        ((TopRep.res (S.subtype : S →* G) X).continuousCohomologyUniverseIso.{u₁, u, v} n).hom =
      (X.continuousCohomologyUniverseIso.{u₁, u, v} n).hom ≫ res.{u₁, u, v} S X n := by
  rw [res_def, res_def]
  exact map_comp_continuousCohomologyUniverseIso_hom (X := X)
    (Y := TopRep.res (S.subtype : S →* G) X) (ContinuousMonoidHom.subgroupSubtype S)
    (𝟙 (TopRep.res (S.subtype : S →* G) X)) n

/-- Inverse form of `res_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc]
theorem res_comp_continuousCohomologyUniverseIso_inv (S : Subgroup G)
    (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    res.{u₁, u, v} S X n ≫
        ((TopRep.res (S.subtype : S →* G) X).continuousCohomologyUniverseIso.{u₁, u, v} n).inv =
      (X.continuousCohomologyUniverseIso.{u₁, u, v} n).inv ≫ res.{u₁, u, max u v} S X n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    res_comp_continuousCohomologyUniverseIso_hom]

/-- Restriction between subgroups `S₁ ≤ S₂` commutes with `continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem resLE_comp_continuousCohomologyUniverseIso_hom {S₁ S₂ : Subgroup G} (h : S₁ ≤ S₂)
    (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    resLE.{u₁, u, max u v} h X n ≫
        ((TopRep.res (S₁.subtype : S₁ →* G) X).continuousCohomologyUniverseIso.{u₁, u, v} n).hom =
      ((TopRep.res (S₂.subtype : S₂ →* G) X).continuousCohomologyUniverseIso.{u₁, u, v} n).hom ≫
        resLE.{u₁, u, v} h X n := by
  rw [resLE_def, resLE_def]
  exact map_comp_continuousCohomologyUniverseIso_hom
    (X := TopRep.res (S₂.subtype : S₂ →* G) X) (Y := TopRep.res (S₁.subtype : S₁ →* G) X)
    (ContinuousMonoidHom.subgroupInclusion h) (𝟙 (TopRep.res (S₁.subtype : S₁ →* G) X)) n

/-- Inverse form of `resLE_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc]
theorem resLE_comp_continuousCohomologyUniverseIso_inv {S₁ S₂ : Subgroup G} (h : S₁ ≤ S₂)
    (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    resLE.{u₁, u, v} h X n ≫
        ((TopRep.res (S₁.subtype : S₁ →* G) X).continuousCohomologyUniverseIso.{u₁, u, v} n).inv =
      ((TopRep.res (S₂.subtype : S₂ →* G) X).continuousCohomologyUniverseIso.{u₁, u, v} n).inv ≫
        resLE.{u₁, u, max u v} h X n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    resLE_comp_continuousCohomologyUniverseIso_hom]

/-- Inflation from a quotient by a normal subgroup commutes with
`continuousCohomologyUniverseIso`. -/
@[reassoc]
theorem infl_comp_continuousCohomologyUniverseIso_hom (N : Subgroup G) [N.Normal]
    (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    infl.{u₁, u, max u v} N X n ≫ (X.continuousCohomologyUniverseIso.{u₁, u, v} n).hom =
      ((TopRep.quotientToInvariants X N).continuousCohomologyUniverseIso.{u₁, u, v} n).hom ≫
        infl.{u₁, u, v} N X n := by
  rw [infl_def, infl_def]
  exact map_comp_continuousCohomologyUniverseIso_hom (X := TopRep.quotientToInvariants X N)
    (Y := X) (Subgroup.quotientMkContinuousMonoidHom N)
    (eqToHom (congrArg (fun ψ ↦ TopRep.res ψ (TopRep.quotientToInvariants X N))
      (Subgroup.coe_quotientMkContinuousMonoidHom N)) ≫ TopRep.quotientToInvariantsι X N) n

/-- Inverse form of `infl_comp_continuousCohomologyUniverseIso_hom`. -/
@[reassoc]
theorem infl_comp_continuousCohomologyUniverseIso_inv (N : Subgroup G) [N.Normal]
    (X : TopRep.{max u v, u₁, u} k G) (n : ℕ) :
    infl.{u₁, u, v} N X n ≫ (X.continuousCohomologyUniverseIso.{u₁, u, v} n).inv =
      ((TopRep.quotientToInvariants X N).continuousCohomologyUniverseIso.{u₁, u, v} n).inv ≫
        infl.{u₁, u, max u v} N X n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    infl_comp_continuousCohomologyUniverseIso_hom]

end TauCeti.ContinuousCohomology

end

section
open CategoryTheory TopRep TauCeti.ContinuousCohomology

/-- For a trivial representation `X` and an additive character `f : G → X.V`, the homogeneous
difference cochain `(g₀, g₁) ↦ f g₁ - f g₀` is `G`-invariant in `TopRep.resolutionX X 2`. -/
private theorem diffChar_mem_invariants
    {k : Type u₁} {G : Type u} [Ring k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : TopRep.{max u v, u₁, u} k G) (hρ : ∀ (g : G) (m : X.V), X.ρ g m = m)
    (f : G → X.V) (hf : ∀ g h : G, f (g * h) = f g + f h)
    (F : C(G, C(G, X.V))) (hF : ∀ g₀ g₁ : G, F g₀ g₁ = f g₁ - f g₀) :
    F ∈ (TopRep.resolutionX.{u₁, u, v} X 2).ρ.invariants := by
  rw [ContRepresentation.mem_invariants]
  intro g
  refine ContinuousMap.ext fun g₀ ↦ ContinuousMap.ext fun g₁ ↦ ?_
  rw [TopRep.resolutionX_succ_ρ_apply_apply, TopRep.resolutionX_succ_ρ_apply_apply,
    hρ, hF, hF, hf, hf]
  abel

/-- Any homogeneous `1`-cochain of the form `(g₀, g₁) ↦ f g₁ - f g₀` is a `1`-cocycle. -/
private theorem diffChar_d_one_eq_zero
    {k : Type u₁} {G : Type u} [Ring k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : TopRep.{max u v, u₁, u} k G) (f : G → X.V)
    (a : (TopRep.homogeneousCochains.{u₁, u, v} X).X 1)
    (ha : ∀ g₀ g₁ : G, (a.val : C(G, C(G, X.V))) g₀ g₁ = f g₁ - f g₀) :
    ((TopRep.homogeneousCochains.{u₁, u, v} X).d 1 2).hom a = 0 := by
  refine Subtype.ext (ContinuousMap.ext fun g₀ ↦ ContinuousMap.ext fun g₁ ↦
    ContinuousMap.ext fun g₂ ↦ ?_)
  rw [TopRep.homogeneousCochains.d_one_apply, ha, ha, ha]
  simp only [ZeroMemClass.coe_zero, ContinuousMap.zero_apply]
  abel

/-- Action of a coefficient map `f : X ⟶ Y` on a degree-zero cohomology class. -/
private theorem coeffMap_degreeZeroClass_eq
    {k : Type u₁} {G : Type u} [Ring k] [TopologicalSpace k]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {X Y : TopRep.{max u v, u₁, u} k G} (f : X ⟶ Y)
    (x : X.V) (hx : ∀ g : G, X.ρ g x = x)
    (y : Y.V) (hy : ∀ g : G, Y.ρ g y = y) (hf : f.hom x = y) :
    coeffMap.{u₁, u, v} f 0 (degreeZeroClass.{u₁, u, v} X x hx) =
      degreeZeroClass.{u₁, u, v} Y y hy := by
  have h := ConcreteCategory.congr_hom (coeffMap_comp_zeroIso_hom.{u₁, u, v} f)
    (degreeZeroClass.{u₁, u, v} X x hx)
  simp only [ConcreteCategory.comp_apply] at h
  have hval : ((ContinuousCohomology.zeroIso.{u₁, u, v} Y).hom
      (coeffMap.{u₁, u, v} f 0 (degreeZeroClass.{u₁, u, v} X x hx)) : Y.V) = y := by
    rw [h]
    simp only [TopModuleCat.hom_ofHom, ContIntertwiningMap.mapInvariants_apply,
      coe_zeroIso_hom_degreeZeroClass, hf]
  exact (ContinuousCohomology.zeroIso.{u₁, u, v} Y).toContinuousLinearEquiv.injective
    (Subtype.ext (hval.trans (coe_zeroIso_hom_degreeZeroClass y hy).symm))

/-- Over the trivial group `PUnit.{u + 1}` with trivial coefficients `ULift.{u} ℤ` in degree `0`,
the comparison sends the degree-zero class of `1` to the degree-zero class of `1`, and that class
is distinct from its negation (excluding the sign-flip automorphism `x ↦ -x`). -/
example :
    let X := TopRep.of (ContRepresentation.trivial ℤ PUnit.{u + 1} (ULift.{u} ℤ))
    let hm : ∀ g : PUnit.{u + 1}, X.ρ g ⟨1⟩ = ⟨1⟩ := fun _ ↦ rfl
    (X.continuousCohomologyUniverseIso.{0, u, 0} 0).hom
        (degreeZeroClass.{0, u, u} X ⟨1⟩ hm) =
      degreeZeroClass.{0, u, 0} X ⟨1⟩ hm ∧
      degreeZeroClass.{0, u, 0} X ⟨1⟩ hm ≠ -degreeZeroClass.{0, u, 0} X ⟨1⟩ hm := by
  intro X hm
  refine ⟨X.continuousCohomologyUniverseIso_zero_hom_degreeZeroClass ⟨1⟩ hm, fun hneg ↦ ?_⟩
  let e := (ContinuousCohomology.zeroIso.{0, u, 0} X).toContinuousLinearEquiv
  have h0 : e (degreeZeroClass.{0, u, 0} X ⟨1⟩ hm) =
      -e (degreeZeroClass.{0, u, 0} X ⟨1⟩ hm) := by
    simpa [e] using congrArg e hneg
  have h1 : ((ContinuousCohomology.zeroIso.{0, u, 0} X).hom
      (degreeZeroClass.{0, u, 0} X ⟨1⟩ hm) : ULift.{u} ℤ) = ⟨1⟩ :=
    coe_zeroIso_hom_degreeZeroClass (X := X) (ULift.up 1) hm
  have h2 : (⟨1⟩ : ULift.{u} ℤ) = -⟨1⟩ := by
    have hval : (e (degreeZeroClass.{0, u, 0} X ⟨1⟩ hm) : ULift.{u} ℤ) =
        -(e (degreeZeroClass.{0, u, 0} X ⟨1⟩ hm) : ULift.{u} ℤ) :=
      congrArg (fun z : X.ρ.invariants ↦ (z : ULift.{u} ℤ)) h0
    exact h1.symm.trans (hval.trans (congrArg Neg.neg h1))
  have h3 : (1 : ℤ) = -1 := congrArg ULift.down h2
  omega

/-- Over the discrete group `C₂` in universe `u` with trivial `𝔽₂` coefficients in degree `1`,
the comparison carries the cohomology class of the identity character homogeneous `1`-cocycle to
the class of the same cocycle at auxiliary universe `0`, and that class is nonzero (excluding the
zero map). -/
example :
    letI : TopologicalSpace (Multiplicative (ZMod 2)) := ⊥
    letI : DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩
    letI : IsTopologicalGroup (Multiplicative (ZMod 2)) :=
      { continuous_mul := continuous_of_discreteTopology
        continuous_inv := continuous_of_discreteTopology }
    let G := ULift.{u} (Multiplicative (ZMod 2))
    let M := ULift.{u} (ZMod 2)
    let X := TopRep.of (ContRepresentation.trivial ℤ G M)
    let F : C(G, C(G, M)) := ContinuousMap.curry
      ⟨fun p : G × G ↦ ULift.up (Multiplicative.toAdd p.2.down - Multiplicative.toAdd p.1.down),
        continuous_of_discreteTopology⟩
    ∃ (a₁ : (TopRep.homogeneousCochains.{0, u, u} X).X 1)
      (ha₁ : ((TopRep.homogeneousCochains.{0, u, u} X).d 1 2).hom a₁ = 0)
      (a₀ : (TopRep.homogeneousCochains.{0, u, 0} X).X 1)
      (ha₀ : ((TopRep.homogeneousCochains.{0, u, 0} X).d 1 2).hom a₀ = 0),
      a₁.val = F ∧ a₀.val = F ∧
      (X.continuousCohomologyUniverseIso.{0, u, 0} 1).hom
          (X.cochainClass.{0, u, u} 1 a₁ ha₁) =
        X.cochainClass.{0, u, 0} 1 a₀ ha₀ ∧
      X.cochainClass.{0, u, 0} 1 a₀ ha₀ ≠ 0 := by
  let : TopologicalSpace (Multiplicative (ZMod 2)) := ⊥
  let : DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩
  let : IsTopologicalGroup (Multiplicative (ZMod 2)) :=
    { continuous_mul := continuous_of_discreteTopology
      continuous_inv := continuous_of_discreteTopology }
  let G := ULift.{u} (Multiplicative (ZMod 2))
  let M := ULift.{u} (ZMod 2)
  let X := TopRep.of (ContRepresentation.trivial ℤ G M)
  let f : G → M := fun g ↦ ULift.up (Multiplicative.toAdd g.down)
  let F : C(G, C(G, M)) := ContinuousMap.curry
    ⟨fun p : G × G ↦ ULift.up (Multiplicative.toAdd p.2.down - Multiplicative.toAdd p.1.down),
      continuous_of_discreteTopology⟩
  have hρ : ∀ (g : G) (m : X.V), X.ρ g m = m := fun _ _ ↦ rfl
  have hf : ∀ g h : G, f (g * h) = f g + f h := fun g h ↦ ULift.ext (toAdd_mul g.down h.down)
  have hF : ∀ g₀ g₁ : G, F g₀ g₁ = f g₁ - f g₀ := fun _ _ ↦ ULift.ext rfl
  let a₁ : (TopRep.homogeneousCochains.{0, u, u} X).X 1 :=
    ⟨F, diffChar_mem_invariants.{0, u, u} X hρ f hf F hF⟩
  let a₀ : (TopRep.homogeneousCochains.{0, u, 0} X).X 1 :=
    ⟨F, diffChar_mem_invariants.{0, u, 0} X hρ f hf F hF⟩
  have ha₁ : ((TopRep.homogeneousCochains.{0, u, u} X).d 1 2).hom a₁ = 0 :=
    diffChar_d_one_eq_zero.{0, u, u} X f a₁ hF
  have ha₀ : ((TopRep.homogeneousCochains.{0, u, 0} X).d 1 2).hom a₀ = 0 :=
    diffChar_d_one_eq_zero.{0, u, 0} X f a₀ hF
  refine ⟨a₁, ha₁, a₀, ha₀, rfl, rfl, ?_, ?_⟩
  · rw [X.continuousCohomologyUniverseIso_hom_cochainClass.{0, u, 0} 1 a₁ ha₁]
    congr 1
  · intro h0
    have h0' : X.cochainClass.{0, u, 0} 1 a₀ ha₀ =
        X.cochainClass.{0, u, 0} 1 0 (map_zero _) := by
      simpa using h0
    obtain ⟨c, hc⟩ := (TopRep.cochainClass_eq_cochainClass_iff (j := 0) rfl ha₀ (map_zero _)).1 h0'
    rw [sub_zero] at hc
    let g₁ : G := ⟨Multiplicative.ofAdd 1⟩
    have hc_inv : (c.val : C(G, M)) g₁ = (c.val : C(G, M)) 1 := by
      have hcg := (ContRepresentation.mem_invariants c.val).1 c.2 g₁⁻¹
      have hev := congrArg (fun b : C(G, M) ↦ b 1) hcg
      rw [TopRep.resolutionX_succ_ρ_apply_apply, inv_inv, mul_one, hρ] at hev
      exact hev
    have hc_val : (a₀.val : C(G, C(G, M))) = (TopRep.d.{0, u, 0} X 1).hom c.val :=
      (congrArg Subtype.val hc).trans (TopRep.homogeneousCochains.d_apply X 0 c)
    have hev : (a₀.val : C(G, C(G, M))) 1 g₁ = (c.val : C(G, M)) g₁ - (c.val : C(G, M)) 1 :=
      congrArg (fun b : C(G, C(G, M)) ↦ b 1 g₁) hc_val
    rw [hc_inv, sub_self] at hev
    have h10 : (1 : ZMod 2) = 0 := by
      simpa [a₀, F, g₁] using congrArg ULift.down hev
    exact one_ne_zero h10

/-- Naturality check on the doubling coefficient map `x ↦ 2 • x` of trivial `ℤ`-modules in degree
`0`: both paths around the naturality square send the class of `1` to the class of `2`. -/
example {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    let X := TopRep.of (ContRepresentation.trivial ℤ G (ULift.{u} ℤ))
    let hm₁ : ∀ g : G, X.ρ g ⟨1⟩ = ⟨1⟩ := fun _ ↦ rfl
    let hm₂ : ∀ g : G, X.ρ g ⟨2⟩ = ⟨2⟩ := fun _ ↦ rfl
    (X.continuousCohomologyUniverseIso.{0, u, 0} 0).hom
        (coeffMap.{0, u, u} (2 • 𝟙 X) 0 (degreeZeroClass.{0, u, u} X ⟨1⟩ hm₁)) =
      degreeZeroClass.{0, u, 0} X ⟨2⟩ hm₂ ∧
    coeffMap.{0, u, 0} (2 • 𝟙 X) 0
        ((X.continuousCohomologyUniverseIso.{0, u, 0} 0).hom
          (degreeZeroClass.{0, u, u} X ⟨1⟩ hm₁)) =
      degreeZeroClass.{0, u, 0} X ⟨2⟩ hm₂ := by
  intro X hm₁ hm₂
  have hf_val : (2 • 𝟙 X : X ⟶ X).hom (ULift.up 1) = ULift.up (2 : ℤ) := by
    rw [two_nsmul, TopRep.hom_add, ContIntertwiningMap.add_apply, TopRep.hom_id,
      ContIntertwiningMap.id_apply]
    exact ULift.ext one_add_one_eq_two
  refine ⟨?_, ?_⟩
  · rw [coeffMap_degreeZeroClass_eq.{0, u, u} (X := X) (Y := X) (2 • 𝟙 X) ⟨1⟩ hm₁ ⟨2⟩ hm₂ hf_val,
      X.continuousCohomologyUniverseIso_zero_hom_degreeZeroClass]
  · rw [X.continuousCohomologyUniverseIso_zero_hom_degreeZeroClass,
      coeffMap_degreeZeroClass_eq.{0, u, 0} (X := X) (Y := X) (2 • 𝟙 X) ⟨1⟩ hm₁ ⟨2⟩ hm₂ hf_val]

/-- At `u = 0` (`G : Type 0`), the universe comparison on continuous cohomology is the identity in
every degree. -/
example {k : Type u₁} {G : Type 0} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (X : TopRep.{0, u₁, 0} k G) (n : ℕ) :
    (X.continuousCohomologyUniverseIso.{u₁, 0, 0} n).hom = 𝟙 _ := by
  rw [X.continuousCohomologyUniverseIso_refl.{u₁, 0, 0} n, Iso.refl_hom]

end
