/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero

/-!
# Independence of continuous cohomology from the auxiliary universe parameter

For scalars `k : Type w` and a topological group `G : Type u`, Mathlib's coinduced resolution
`TopRep.resolutionX.{w, u, v}` takes a continuous representation `X : TopRep.{max u v} k G`, so that
the coinduction `C(G, -)` stays in `TopRep.{max u v} k G`. The auxiliary universe `v` therefore
appears as a universe parameter of `TopRep.resolutionX`, `TopRep.d`, `TopRep.resolution'`,
`TopRep.homogeneousCochains`, `ContinuousCohomology.cocycles`, and `continuousCohomology`, even
though `X` and every term of the resolution depend on `v` only through `max u v`.

In particular, for any `X : TopRep.{max u v} k G`, the objects
`continuousCohomology.{w, u, max u v} n X` and `continuousCohomology.{w, u, v} n X` both live in
`TopModuleCat.{max u v} k`, yet they are not definitionally equal when `u` is polymorphic because
the recursion inside `TopRep.resolutionX` records the unnormalized universe parameter. At `v = 0`,
since `max u 0 = u`, this compares `continuousCohomology.{w, u, u} n X` with
`continuousCohomology.{w, u, 0} n X` for any `X : TopRep.{u} k G`.

This file constructs the canonical comparison isomorphism at each stage of Mathlib's construction
and shows that it commutes with all structural maps:

* **Resolution (`TopRep.resolutionXUniverseIso`, `TopRep.resolution'UniverseIso`).** In degree `0`
  the isomorphism is the identity of `X`; in degree `n + 1` it is `(coind₁Functor k G).mapIso` of
  the degree-`n` isomorphism, acting on `C(G, -)` by postcomposition with the degree-`n` map and
  with inverse given by postcomposition with the degree-`n` inverse. It commutes with the
  `G`-action, with the coinduction unit `coind₁ι`, and with the recursive differentials
  `d_{n+1} = const - C(G, d_n)`.
* **Homogeneous cochains (`TopRep.homogeneousCochainsUniverseIso`).** Applying
  `TopRep.invariantsFunctor k G` degreewise gives a chain isomorphism of homogeneous cochain
  complexes in `CochainComplex (TopModuleCat k) ℕ`.
* **Cocycles and cohomology (`TopRep.cocyclesUniverseIso`, `TopRep.continuousCohomologyUniverseIso`,
  `TopRep.cocyclesUniverseAddEquiv`, `TopRep.continuousCohomologyUniverseAddEquiv`).** Passing to
  cycles and homology in `TopModuleCat k` yields topological `k`-linear isomorphisms and additive
  equivalences in every degree `n`, carrying the cohomology class of a cocycle to the cohomology
  class of its image (`TopRep.π_comp_continuousCohomologyUniverseIso_hom`,
  `TopRep.continuousCohomologyUniverseAddEquiv_π`) and preserving pointwise cocycle values in low
  degrees.
* **Naturality and degree zero.** The comparison commutes with compatible-pair functoriality
  `ContinuousCohomology.map` (`TopRep.map_comp_continuousCohomologyUniverseIso_hom`), hence with
  coefficient maps, restriction, and inflation, upgrades to a natural isomorphism of functors
  `TauCeti.ContinuousCohomology.continuousCohomologyFunctorUniverseIso`, and commutes with
  `ContinuousCohomology.zeroIso` and `TauCeti.ContinuousCohomology.degreeZeroClass` in degree zero.
* **Coincidence when normalized.** When the parameter already has the form `max u v` (in particular
  when `u = 0` and `v = 0`), every stage of the comparison is the identity isomorphism.

The construction follows the stage-by-stage pattern of
`TauCeti.RepresentationTheory.Homological.ContCohomology.RestrictScalars` against Mathlib's
`TopRep.homogeneousCochains` and `ContinuousCohomology.map`.

## Main definitions

* `TopRep.resolutionXUniverseIso`, `TopRep.resolution'UniverseIso`: canonical degreewise and
  cochain-complex isomorphisms on the coinduced resolution between universe parameters `max u v` and
  `v`.
* `TopRep.homogeneousCochainsUniverseIso`: canonical isomorphism of homogeneous cochain complexes in
  `CochainComplex (TopModuleCat k) ℕ`.
* `TopRep.cocyclesUniverseIso`, `TopRep.continuousCohomologyUniverseIso`: canonical `TopModuleCat k`
  isomorphisms on `n`-cocycles and `n`-th continuous cohomology.
* `TopRep.cocyclesUniverseAddEquiv`, `TopRep.continuousCohomologyUniverseAddEquiv`: the underlying
  additive equivalences on cocycles and continuous cohomology groups.
* `TauCeti.ContinuousCohomology.continuousCohomologyFunctorUniverseIso`: natural isomorphism between
  `continuousCohomologyFunctor` at universe parameters `max u v` and `v`.

## Main results

* `TopRep.d_comp_resolutionXUniverseIso_hom`: compatibility with the differentials `TopRep.d`.
* `TopRep.π_comp_continuousCohomologyUniverseIso_hom`,
  `TopRep.continuousCohomologyUniverseAddEquiv_π`: compatibility with the cohomology projection
  `ContinuousCohomology.π`.
* `TopRep.iCycles_cocyclesUniverseAddEquiv_zero_apply`,
  `TopRep.iCycles_cocyclesUniverseAddEquiv_one_apply`,
  `TopRep.iCycles_cocyclesUniverseAddEquiv_two_apply`: preservation of pointwise cocycle values in
  degrees `0`, `1`, and `2`.
* `TopRep.subsingleton_continuousCohomology_max_iff`,
  `TopRep.primaryComponent_continuousCohomology_max_eq_bot_iff`: invariance of vanishing and of
  vanishing of `p`-primary components across universe parameters `max u v` and `v`.
* `TopRep.map_comp_continuousCohomologyUniverseIso_hom`,
  `TauCeti.ContinuousCohomology.coeffMap_comp_continuousCohomologyUniverseIso_hom`,
  `TauCeti.ContinuousCohomology.res_comp_continuousCohomologyUniverseIso_hom`,
  `TauCeti.ContinuousCohomology.infl_comp_continuousCohomologyUniverseIso_hom`: naturality with
  respect to compatible pairs, coefficient morphisms, restriction, and inflation.
* `TauCeti.ContinuousCohomology.continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom`,
  `TauCeti.ContinuousCohomology.continuousCohomologyUniverseAddEquiv_zero_degreeZeroClass`:
  compatibility in degree zero with `ContinuousCohomology.zeroIso` and `degreeZeroClass`.
* `TopRep.continuousCohomologyUniverseIso_max`, `TopRep.continuousCohomologyUniverseAddEquiv_max`:
  when the parameter already has the form `max u v`, the comparison is the identity.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I §2:
  continuous cohomology of a topological group `G` with coefficients in a topological `G`-module
  `X` is computed by the complex of homogeneous continuous cochains `C(G^{n+1}, X)^G`.
-/

public section

open CategoryTheory ContRepresentation

namespace TopRep

open _root_.ContinuousCohomology

universe w u v

variable {k : Type w} [Ring k] [TopologicalSpace k]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### The coinduced resolution -/

/-- Canonical isomorphism between `TopRep.resolutionX` at universe parameters `max u v` and `v` for
`X : TopRep.{max u v} k G`. In degree `0` it is the identity of `X`; in degree `n + 1` it applies
`TopRep.coind₁Functor k G` to the degree-`n` isomorphism. -/
def resolutionXUniverseIso (X : TopRep.{max u v, w, u} k G) :
    ∀ n : ℕ, resolutionX.{w, u, max u v} X n ≅ resolutionX.{w, u, v} X n
  | 0 => Iso.refl X
  | n + 1 => (coind₁Functor k G).mapIso (resolutionXUniverseIso X n)

/-- In degree zero, `resolutionXUniverseIso` is the identity isomorphism of `X`. -/
@[simp]
theorem resolutionXUniverseIso_zero (X : TopRep.{max u v, w, u} k G) :
    X.resolutionXUniverseIso 0 = Iso.refl X :=
  (rfl)

/-- In degree zero, the forward direction of `resolutionXUniverseIso` acts as the identity on
elements. -/
-- Not `@[simp]`: `simp` already reduces the left-hand side via `resolutionXUniverseIso_zero` and
-- `Iso.refl_hom`, so `simpNF` would reject it; kept for explicit low-degree cocycle rewrites.
theorem resolutionXUniverseIso_zero_hom_apply (X : TopRep.{max u v, w, u} k G)
    (x : (resolutionX.{w, u, max u v} X 0).V) :
    (X.resolutionXUniverseIso 0).hom.hom x = x :=
  (rfl)

/-- In degree zero, the inverse direction of `resolutionXUniverseIso` acts as the identity on
elements. -/
-- Not `@[simp]`, for the same reason as `resolutionXUniverseIso_zero_hom_apply`.
theorem resolutionXUniverseIso_zero_inv_apply (X : TopRep.{max u v, w, u} k G)
    (x : (resolutionX.{w, u, v} X 0).V) :
    (X.resolutionXUniverseIso 0).inv.hom x = x :=
  (rfl)

/-- In degree `n + 1`, `resolutionXUniverseIso` is the coinduction of the degree-`n` isomorphism. -/
theorem resolutionXUniverseIso_succ (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    X.resolutionXUniverseIso (n + 1) =
      (coind₁Functor k G).mapIso (X.resolutionXUniverseIso n) :=
  (rfl)

/-- In degree `n + 1`, the forward direction of `resolutionXUniverseIso` acts on `C(G, -)` by
postcomposing with the forward direction in degree `n`. -/
@[simp]
theorem resolutionXUniverseIso_succ_hom_apply (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (f : (resolutionX.{w, u, max u v} X (n + 1)).V) (g : G) :
    DFunLike.coe (F := C(G, (resolutionX.{w, u, v} X n).V))
        ((X.resolutionXUniverseIso (n + 1)).hom.hom f) g =
      (X.resolutionXUniverseIso n).hom.hom (f g) :=
  (rfl)

/-- In degree `n + 1`, the inverse direction of `resolutionXUniverseIso` acts on `C(G, -)` by
postcomposing with the inverse direction in degree `n`. -/
@[simp]
theorem resolutionXUniverseIso_succ_inv_apply (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (f : (resolutionX.{w, u, v} X (n + 1)).V) (g : G) :
    DFunLike.coe (F := C(G, (resolutionX.{w, u, max u v} X n).V))
        ((X.resolutionXUniverseIso (n + 1)).inv.hom f) g =
      (X.resolutionXUniverseIso n).inv.hom (f g) :=
  (rfl)

/-- `resolutionXUniverseIso` commutes with the coinduction unit `coind₁ι` into the next degree. -/
@[reassoc]
theorem coind₁ι_comp_resolutionXUniverseIso_succ_hom (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    ofHom (resolutionX.{w, u, max u v} X n).ρ.coind₁ι ≫
        (X.resolutionXUniverseIso (n + 1)).hom =
      (X.resolutionXUniverseIso n).hom ≫ ofHom (resolutionX.{w, u, v} X n).ρ.coind₁ι := by
  rw [resolutionXUniverseIso_succ, Functor.mapIso_hom, ← coind₁ι_app, ← coind₁ι_app]
  exact ((coind₁ι (k := k) (G := G)).naturality (X.resolutionXUniverseIso n).hom).symm

/-- `resolutionXUniverseIso` commutes with the differentials `TopRep.d` of the coinduced
resolution. -/
@[reassoc]
theorem d_comp_resolutionXUniverseIso_hom (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    d.{w, u, max u v} X n ≫ (X.resolutionXUniverseIso (n + 1)).hom =
      (X.resolutionXUniverseIso n).hom ≫ d.{w, u, v} X n := by
  induction n with
  | zero =>
    rw [d_zero, d_zero]
    exact coind₁ι_comp_resolutionXUniverseIso_succ_hom X 0
  | succ n ih =>
    rw [d_succ, d_succ, Preadditive.sub_comp, Preadditive.comp_sub,
      coind₁ι_comp_resolutionXUniverseIso_succ_hom X (n + 1),
      resolutionXUniverseIso_succ X (n + 1), Functor.mapIso_hom, ← Functor.map_comp, ih,
      Functor.map_comp, ← Functor.mapIso_hom, ← resolutionXUniverseIso_succ X n]

/-- The inverse of `resolutionXUniverseIso` commutes with the differentials `TopRep.d` of the
coinduced resolution. -/
@[reassoc]
theorem d_comp_resolutionXUniverseIso_inv (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    d.{w, u, v} X n ≫ (X.resolutionXUniverseIso (n + 1)).inv =
      (X.resolutionXUniverseIso n).inv ≫ d.{w, u, max u v} X n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, d_comp_resolutionXUniverseIso_hom]

/-- Canonical chain isomorphism between the shifted coinduced resolutions `TopRep.resolution'` at
universe parameters `max u v` and `v`. -/
noncomputable def resolution'UniverseIso (X : TopRep.{max u v, w, u} k G) :
    resolution'.{w, u, max u v} X ≅ resolution'.{w, u, v} X :=
  HomologicalComplex.Hom.isoOfComponents (fun n ↦ X.resolutionXUniverseIso (n + 1))
    (by
      rintro i j (rfl : i + 1 = j)
      simp only [CochainComplex.of_d, resolution'd_eq]
      exact (d_comp_resolutionXUniverseIso_hom X (i + 1)).symm)

/-- The degree-`n` component of `resolution'UniverseIso.hom` is `resolutionXUniverseIso` in degree
`n + 1`. -/
@[simp]
theorem resolution'UniverseIso_hom_f (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    X.resolution'UniverseIso.hom.f n = (X.resolutionXUniverseIso (n + 1)).hom :=
  (rfl)

/-- The degree-`n` component of `resolution'UniverseIso.inv` is the inverse of
`resolutionXUniverseIso` in degree `n + 1`. -/
@[simp]
theorem resolution'UniverseIso_inv_f (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    X.resolution'UniverseIso.inv.f n = (X.resolutionXUniverseIso (n + 1)).inv :=
  (rfl)

/-! ### Homogeneous cochains -/

/-- Canonical chain isomorphism between the homogeneous cochain complexes
`TopRep.homogeneousCochains` at universe parameters `max u v` and `v`. -/
noncomputable def homogeneousCochainsUniverseIso (X : TopRep.{max u v, w, u} k G) :
    homogeneousCochains.{w, u, max u v} X ≅ homogeneousCochains.{w, u, v} X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (invariantsFunctor k G).mapIso (X.resolutionXUniverseIso (n + 1)))
    (by
      rintro i j (rfl : i + 1 = j)
      rw [homogeneousCochains.d_eq, homogeneousCochains.d_eq, Functor.mapIso_hom,
        Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp,
        d_comp_resolutionXUniverseIso_hom])

/-- The degree-`n` component of `homogeneousCochainsUniverseIso.hom` restricts
`resolutionXUniverseIso` in degree `n + 1` to `G`-invariants. -/
theorem homogeneousCochainsUniverseIso_hom_f (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    X.homogeneousCochainsUniverseIso.hom.f n =
      (invariantsFunctor k G).map (X.resolutionXUniverseIso (n + 1)).hom :=
  (rfl)

/-- The degree-`n` component of `homogeneousCochainsUniverseIso.inv` restricts the inverse of
`resolutionXUniverseIso` in degree `n + 1` to `G`-invariants. -/
theorem homogeneousCochainsUniverseIso_inv_f (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    X.homogeneousCochainsUniverseIso.inv.f n =
      (invariantsFunctor k G).map (X.resolutionXUniverseIso (n + 1)).inv :=
  (rfl)

/-- On underlying invariant cochains, `homogeneousCochainsUniverseIso.hom` acts as
`resolutionXUniverseIso` in degree `n + 1`. -/
theorem coe_homogeneousCochainsUniverseIso_hom_f (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (c : (homogeneousCochains.{w, u, max u v} X).X n) :
    (X.homogeneousCochainsUniverseIso.hom.f n c).val =
      (X.resolutionXUniverseIso (n + 1)).hom.hom c.val :=
  (rfl)

/-- On underlying invariant cochains, `homogeneousCochainsUniverseIso.inv` acts as the inverse of
`resolutionXUniverseIso` in degree `n + 1`. -/
theorem coe_homogeneousCochainsUniverseIso_inv_f (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (c : (homogeneousCochains.{w, u, v} X).X n) :
    (X.homogeneousCochainsUniverseIso.inv.f n c).val =
      (X.resolutionXUniverseIso (n + 1)).inv.hom c.val :=
  (rfl)

/-! ### Cocycles and continuous cohomology -/

/-- Canonical isomorphism in `TopModuleCat k` between the `n`-cocycles at universe parameters
`max u v` and `v`. -/
noncomputable def cocyclesUniverseIso (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    cocycles.{w, u, max u v} X n ≅ cocycles.{w, u, v} X n :=
  HomologicalComplex.cyclesMapIso X.homogeneousCochainsUniverseIso n

/-- **Continuous cohomology does not depend on the auxiliary universe parameter.** For
`X : TopRep.{max u v} k G`, the continuous cohomology objects at universe parameters `max u v` and
`v` are canonically isomorphic in `TopModuleCat k`. At `v = 0` this identifies
`continuousCohomology.{w, u, u} n X` with `continuousCohomology.{w, u, 0} n X`. -/
noncomputable def continuousCohomologyUniverseIso (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    continuousCohomology.{w, u, max u v} n X ≅ continuousCohomology.{w, u, v} n X :=
  HomologicalComplex.homologyMapIso X.homogeneousCochainsUniverseIso n

/-- `cocyclesUniverseIso.hom` intertwines the inclusions `iCycles` into homogeneous cochains. -/
@[reassoc (attr := simp)]
theorem cocyclesUniverseIso_hom_comp_iCycles (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    (X.cocyclesUniverseIso n).hom ≫ (homogeneousCochains.{w, u, v} X).iCycles n =
      (homogeneousCochains.{w, u, max u v} X).iCycles n ≫
        X.homogeneousCochainsUniverseIso.hom.f n :=
  HomologicalComplex.cyclesMap_i X.homogeneousCochainsUniverseIso.hom n

/-- `cocyclesUniverseIso.inv` intertwines the inclusions `iCycles` into homogeneous cochains. -/
@[reassoc (attr := simp)]
theorem cocyclesUniverseIso_inv_comp_iCycles (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    (X.cocyclesUniverseIso n).inv ≫ (homogeneousCochains.{w, u, max u v} X).iCycles n =
      (homogeneousCochains.{w, u, v} X).iCycles n ≫
        X.homogeneousCochainsUniverseIso.inv.f n :=
  HomologicalComplex.cyclesMap_i X.homogeneousCochainsUniverseIso.inv n

/-- `continuousCohomologyUniverseIso.hom` sends the cohomology class of a cocycle to the cohomology
class of its image under `cocyclesUniverseIso.hom`. -/
@[reassoc (attr := simp)]
theorem π_comp_continuousCohomologyUniverseIso_hom (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    π.{w, u, max u v} X n ≫ (X.continuousCohomologyUniverseIso n).hom =
      (X.cocyclesUniverseIso n).hom ≫ π.{w, u, v} X n :=
  HomologicalComplex.homologyπ_naturality X.homogeneousCochainsUniverseIso.hom n

/-- `continuousCohomologyUniverseIso.inv` sends the cohomology class of a cocycle to the cohomology
class of its image under `cocyclesUniverseIso.inv`. -/
@[reassoc (attr := simp)]
theorem π_comp_continuousCohomologyUniverseIso_inv (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    π.{w, u, v} X n ≫ (X.continuousCohomologyUniverseIso n).inv =
      (X.cocyclesUniverseIso n).inv ≫ π.{w, u, max u v} X n :=
  HomologicalComplex.homologyπ_naturality X.homogeneousCochainsUniverseIso.inv n

/-- Canonical additive equivalence between the `n`-cocycles at universe parameters `max u v` and
`v`. -/
noncomputable def cocyclesUniverseAddEquiv (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    cocycles.{w, u, max u v} X n ≃+ cocycles.{w, u, v} X n :=
  (X.cocyclesUniverseIso n).toContinuousLinearEquiv.toAddEquiv

/-- `cocyclesUniverseAddEquiv` acts as `cocyclesUniverseIso.hom` on elements. -/
theorem cocyclesUniverseAddEquiv_apply (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (z : cocycles.{w, u, max u v} X n) :
    X.cocyclesUniverseAddEquiv n z = (X.cocyclesUniverseIso n).hom z :=
  (rfl)

/-- `cocyclesUniverseAddEquiv.symm` acts as `cocyclesUniverseIso.inv` on elements. -/
theorem cocyclesUniverseAddEquiv_symm_apply (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (z : cocycles.{w, u, v} X n) :
    (X.cocyclesUniverseAddEquiv n).symm z = (X.cocyclesUniverseIso n).inv z :=
  (rfl)

/-- **Canonical additive equivalence between continuous cohomology groups** at universe parameters
`max u v` and `v`. At `v = 0` this is `Hⁿ_{v=u}(G, X) ≃+ Hⁿ_{v=0}(G, X)`. -/
noncomputable def continuousCohomologyUniverseAddEquiv (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    continuousCohomology.{w, u, max u v} n X ≃+ continuousCohomology.{w, u, v} n X :=
  (X.continuousCohomologyUniverseIso n).toContinuousLinearEquiv.toAddEquiv

/-- `continuousCohomologyUniverseAddEquiv` acts as `continuousCohomologyUniverseIso.hom` on
elements. -/
theorem continuousCohomologyUniverseAddEquiv_apply (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (x : continuousCohomology.{w, u, max u v} n X) :
    X.continuousCohomologyUniverseAddEquiv n x = (X.continuousCohomologyUniverseIso n).hom x :=
  (rfl)

/-- `continuousCohomologyUniverseAddEquiv.symm` acts as `continuousCohomologyUniverseIso.inv` on
elements. -/
theorem continuousCohomologyUniverseAddEquiv_symm_apply (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (x : continuousCohomology.{w, u, v} n X) :
    (X.continuousCohomologyUniverseAddEquiv n).symm x =
      (X.continuousCohomologyUniverseIso n).inv x :=
  (rfl)

/-- `continuousCohomologyUniverseAddEquiv` sends the cohomology class of a cocycle to the
cohomology class of its image cocycle. -/
@[simp]
theorem continuousCohomologyUniverseAddEquiv_π (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (z : cocycles.{w, u, max u v} X n) :
    X.continuousCohomologyUniverseAddEquiv n (π.{w, u, max u v} X n z) =
      π.{w, u, v} X n (X.cocyclesUniverseAddEquiv n z) :=
  congr($(π_comp_continuousCohomologyUniverseIso_hom X n) z)

/-- `continuousCohomologyUniverseAddEquiv.symm` sends the cohomology class of a cocycle to the
cohomology class of its preimage cocycle. -/
@[simp]
theorem continuousCohomologyUniverseAddEquiv_symm_π (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (z : cocycles.{w, u, v} X n) :
    (X.continuousCohomologyUniverseAddEquiv n).symm (π.{w, u, v} X n z) =
      π.{w, u, max u v} X n ((X.cocyclesUniverseAddEquiv n).symm z) :=
  congr($(π_comp_continuousCohomologyUniverseIso_inv X n) z)

/-- Under `cocyclesUniverseAddEquiv`, the underlying homogeneous cochain of a cocycle is carried by
`resolutionXUniverseIso` in degree `n + 1`. -/
theorem coe_iCycles_cocyclesUniverseAddEquiv (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (z : cocycles.{w, u, max u v} X n) :
    ((homogeneousCochains.{w, u, v} X).iCycles n (X.cocyclesUniverseAddEquiv n z)).val =
      (X.resolutionXUniverseIso (n + 1)).hom.hom
        ((homogeneousCochains.{w, u, max u v} X).iCycles n z).val := by
  have h : (homogeneousCochains.{w, u, v} X).iCycles n (X.cocyclesUniverseAddEquiv n z) =
      X.homogeneousCochainsUniverseIso.hom.f n
        ((homogeneousCochains.{w, u, max u v} X).iCycles n z) :=
    congr($(cocyclesUniverseIso_hom_comp_iCycles X n) z)
  rw [h, coe_homogeneousCochainsUniverseIso_hom_f]

/-- In degree zero, `cocyclesUniverseAddEquiv` preserves the values of a homogeneous cocycle on
`G`. -/
theorem iCycles_cocyclesUniverseAddEquiv_zero_apply (X : TopRep.{max u v, w, u} k G)
    (z : cocycles.{w, u, max u v} X 0) (g₀ : G) :
    ((homogeneousCochains.{w, u, v} X).iCycles 0 (X.cocyclesUniverseAddEquiv 0 z)).val g₀ =
      ((homogeneousCochains.{w, u, max u v} X).iCycles 0 z).val g₀ :=
  (congrArg (fun w : C(G, X.V) ↦ w g₀) (coe_iCycles_cocyclesUniverseAddEquiv X 0 z)).trans
    ((resolutionXUniverseIso_succ_hom_apply X 0 _ g₀).trans
      (resolutionXUniverseIso_zero_hom_apply X _))

/-- In degree one, `cocyclesUniverseAddEquiv` preserves the values of a homogeneous cocycle on
`G × G`. -/
theorem iCycles_cocyclesUniverseAddEquiv_one_apply (X : TopRep.{max u v, w, u} k G)
    (z : cocycles.{w, u, max u v} X 1) (g₀ g₁ : G) :
    ((homogeneousCochains.{w, u, v} X).iCycles 1 (X.cocyclesUniverseAddEquiv 1 z)).val g₀ g₁ =
      ((homogeneousCochains.{w, u, max u v} X).iCycles 1 z).val g₀ g₁ :=
  (congrArg (fun w : C(G, C(G, X.V)) ↦ w g₀ g₁)
    (coe_iCycles_cocyclesUniverseAddEquiv X 1 z)).trans
    ((congrArg (fun w : C(G, X.V) ↦ w g₁)
      (resolutionXUniverseIso_succ_hom_apply X 1 _ g₀)).trans
      ((resolutionXUniverseIso_succ_hom_apply X 0 _ g₁).trans
        (resolutionXUniverseIso_zero_hom_apply X _)))

/-- In degree two, `cocyclesUniverseAddEquiv` preserves the values of a homogeneous cocycle on
`G × G × G`. -/
theorem iCycles_cocyclesUniverseAddEquiv_two_apply (X : TopRep.{max u v, w, u} k G)
    (z : cocycles.{w, u, max u v} X 2) (g₀ g₁ g₂ : G) :
    ((homogeneousCochains.{w, u, v} X).iCycles 2 (X.cocyclesUniverseAddEquiv 2 z)).val g₀ g₁ g₂ =
      ((homogeneousCochains.{w, u, max u v} X).iCycles 2 z).val g₀ g₁ g₂ :=
  (congrArg (fun w : C(G, C(G, C(G, X.V))) ↦ w g₀ g₁ g₂)
    (coe_iCycles_cocyclesUniverseAddEquiv X 2 z)).trans
    ((congrArg (fun w : C(G, C(G, X.V)) ↦ w g₁ g₂)
      (resolutionXUniverseIso_succ_hom_apply X 2 _ g₀)).trans
      ((congrArg (fun w : C(G, X.V) ↦ w g₂)
        (resolutionXUniverseIso_succ_hom_apply X 1 _ g₁)).trans
        ((resolutionXUniverseIso_succ_hom_apply X 0 _ g₂).trans
          (resolutionXUniverseIso_zero_hom_apply X _))))

/-- Vanishing of `continuousCohomology` at universe parameter `max u v` is equivalent to vanishing
at universe parameter `v`. -/
theorem subsingleton_continuousCohomology_max_iff (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    Subsingleton (continuousCohomology.{w, u, max u v} n X) ↔
      Subsingleton (continuousCohomology.{w, u, v} n X) :=
  (X.continuousCohomologyUniverseAddEquiv n).toEquiv.subsingleton_congr

/-- Nontriviality of `continuousCohomology` at universe parameter `max u v` is equivalent to
nontriviality at universe parameter `v`. -/
theorem nontrivial_continuousCohomology_max_iff (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    Nontrivial (continuousCohomology.{w, u, max u v} n X) ↔
      Nontrivial (continuousCohomology.{w, u, v} n X) :=
  (X.continuousCohomologyUniverseAddEquiv n).toEquiv.nontrivial_congr

/-- `Nat.card` of `continuousCohomology` agrees at universe parameters `max u v` and `v`. -/
theorem natCard_continuousCohomology_max_eq (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    Nat.card (continuousCohomology.{w, u, max u v} n X) =
      Nat.card (continuousCohomology.{w, u, v} n X) :=
  Nat.card_congr (X.continuousCohomologyUniverseAddEquiv n).toEquiv

/-- Vanishing of the `p`-primary component of `continuousCohomology` at universe parameter
`max u v` is equivalent to vanishing at universe parameter `v`. -/
theorem primaryComponent_continuousCohomology_max_eq_bot_iff (X : TopRep.{max u v, w, u} k G)
    (n p : ℕ) :
    AddCommGroup.primaryComponent (continuousCohomology.{w, u, max u v} n X) p = ⊥ ↔
      AddCommGroup.primaryComponent (continuousCohomology.{w, u, v} n X) p = ⊥ := by
  set e := X.continuousCohomologyUniverseAddEquiv n
  simp only [AddSubgroup.eq_bot_iff_forall, AddCommGroup.mem_primaryComponent]
  exact ⟨fun h y ⟨m, hm⟩ ↦ e.symm.injective
      ((h (e.symm y) ⟨m, by rw [← map_nsmul, hm, map_zero]⟩).trans (map_zero e.symm).symm),
    fun h x ⟨m, hm⟩ ↦ e.injective ((h (e x) ⟨m, by rw [← map_nsmul, hm, map_zero]⟩).trans
      (map_zero e).symm)⟩

/-! ### Naturality -/

section Naturality

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep.{max u v, w, u} k G} {Y : TopRep.{max u v, w, u} k H}
  (φ : H →ₜ* G) (f : res (φ : H →* G) X ⟶ Y)

/-- `resolutionXUniverseIso` is natural with respect to `ContinuousCohomology.resolutionMap` along
a compatible pair `(φ, f)`. -/
@[reassoc]
theorem resolutionMap_comp_resolutionXUniverseIso_hom (i : ℕ) :
    resolutionMap.{w, u, max u v} φ f i ≫ (Y.resolutionXUniverseIso i).hom =
      (resFunctor (φ : H →* G)).map (X.resolutionXUniverseIso i).hom ≫
        resolutionMap.{w, u, v} φ f i := by
  induction i with
  | zero =>
    rw [resolutionMap_zero, resolutionMap_zero, resolutionXUniverseIso_zero,
      resolutionXUniverseIso_zero, Iso.refl_hom, Iso.refl_hom, CategoryTheory.Functor.map_id,
      Category.comp_id, Category.id_comp]
  | succ i ih =>
    ext F h
    exact congr(($ih).hom (F (φ h)))

/-- `homogeneousCochainsUniverseIso` is natural with respect to `ContinuousCohomology.cochainsMap`
along a compatible pair `(φ, f)`. -/
@[reassoc (attr := simp)]
theorem cochainsMap_comp_homogeneousCochainsUniverseIso_hom :
    cochainsMap.{w, u, max u v} φ f ≫ Y.homogeneousCochainsUniverseIso.hom =
      X.homogeneousCochainsUniverseIso.hom ≫ cochainsMap.{w, u, v} φ f := by
  ext i : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, cochainsMap_f, cochainsMap_f,
    homogeneousCochainsUniverseIso_hom_f, homogeneousCochainsUniverseIso_hom_f,
    ← invariantsResMap_comp, resolutionMap_comp_resolutionXUniverseIso_hom,
    invariantsResMap_map_comp]

/-- `cocyclesUniverseIso` is natural with respect to `ContinuousCohomology.cocyclesMap` along a
compatible pair `(φ, f)`. -/
@[reassoc (attr := simp)]
theorem cocyclesMap_comp_cocyclesUniverseIso_hom (n : ℕ) :
    cocyclesMap.{w, u, max u v} φ f n ≫ (Y.cocyclesUniverseIso n).hom =
      (X.cocyclesUniverseIso n).hom ≫ cocyclesMap.{w, u, v} φ f n := by
  dsimp only [cocyclesMap, cocyclesUniverseIso, HomologicalComplex.cyclesMapIso]
  rw [← HomologicalComplex.cyclesMap_comp, ← HomologicalComplex.cyclesMap_comp,
    cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

/-- **Naturality of `continuousCohomologyUniverseIso` in compatible pairs.** Pullback along a
continuous homomorphism `φ : H →ₜ* G` and compatible morphism `f : res φ X ⟶ Y` commutes with
`continuousCohomologyUniverseIso`. -/
@[reassoc (attr := simp)]
theorem map_comp_continuousCohomologyUniverseIso_hom (n : ℕ) :
    _root_.ContinuousCohomology.map.{w, u, max u v} φ f n ≫
        (Y.continuousCohomologyUniverseIso n).hom =
      (X.continuousCohomologyUniverseIso n).hom ≫
        _root_.ContinuousCohomology.map.{w, u, v} φ f n := by
  dsimp only [_root_.ContinuousCohomology.map, continuousCohomologyUniverseIso,
    HomologicalComplex.homologyMapIso]
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

/-- The inverse of `continuousCohomologyUniverseIso` commutes with pullback along a compatible pair
`(φ, f)`. -/
@[reassoc (attr := simp)]
theorem map_comp_continuousCohomologyUniverseIso_inv (n : ℕ) :
    _root_.ContinuousCohomology.map.{w, u, v} φ f n ≫
        (Y.continuousCohomologyUniverseIso n).inv =
      (X.continuousCohomologyUniverseIso n).inv ≫
        _root_.ContinuousCohomology.map.{w, u, max u v} φ f n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    map_comp_continuousCohomologyUniverseIso_hom]

/-- Elementwise naturality of `continuousCohomologyUniverseAddEquiv` under compatible-pair pullback
`ContinuousCohomology.map φ f n`. -/
theorem continuousCohomologyUniverseAddEquiv_map (n : ℕ)
    (x : continuousCohomology.{w, u, max u v} n X) :
    Y.continuousCohomologyUniverseAddEquiv n
        (_root_.ContinuousCohomology.map.{w, u, max u v} φ f n x) =
      _root_.ContinuousCohomology.map.{w, u, v} φ f n
        (X.continuousCohomologyUniverseAddEquiv n x) :=
  congr($(map_comp_continuousCohomologyUniverseIso_hom φ f n) x)

end Naturality

/-! ### Coincidence when the universe parameter is already normalized -/

/-- When the auxiliary universe parameter already has the form `max u v`, `resolutionXUniverseIso`
is the identity isomorphism in every degree. At `u = 0` and `v = 0` this says that the comparison
between `v = u` and `v = 0` is the identity. -/
theorem resolutionXUniverseIso_max (X : TopRep.{max u v, w, u} k G) :
    ∀ n : ℕ, X.resolutionXUniverseIso.{w, u, max u v} n = Iso.refl _
  | 0 => rfl
  | n + 1 => by
    rw [resolutionXUniverseIso_succ, resolutionXUniverseIso_max X n, Functor.mapIso_refl]

/-- When the auxiliary universe parameter already has the form `max u v`,
`resolution'UniverseIso` is the identity isomorphism. -/
theorem resolution'UniverseIso_max (X : TopRep.{max u v, w, u} k G) :
    X.resolution'UniverseIso.{w, u, max u v} = Iso.refl _ := by
  ext n : 2
  rw [resolution'UniverseIso_hom_f, resolutionXUniverseIso_max, Iso.refl_hom, Iso.refl_hom,
    HomologicalComplex.id_f]

/-- When the auxiliary universe parameter already has the form `max u v`,
`homogeneousCochainsUniverseIso` is the identity isomorphism. -/
theorem homogeneousCochainsUniverseIso_max (X : TopRep.{max u v, w, u} k G) :
    X.homogeneousCochainsUniverseIso.{w, u, max u v} = Iso.refl _ := by
  ext n : 2
  rw [homogeneousCochainsUniverseIso_hom_f, resolutionXUniverseIso_max, Iso.refl_hom,
    CategoryTheory.Functor.map_id, Iso.refl_hom, HomologicalComplex.id_f]
  rfl

/-- When the auxiliary universe parameter already has the form `max u v`, `cocyclesUniverseIso` is
the identity isomorphism. -/
theorem cocyclesUniverseIso_max (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    X.cocyclesUniverseIso.{w, u, max u v} n = Iso.refl _ := by
  ext : 1
  dsimp only [cocyclesUniverseIso, HomologicalComplex.cyclesMapIso]
  rw [homogeneousCochainsUniverseIso_max, Iso.refl_hom, HomologicalComplex.cyclesMap_id,
    Iso.refl_hom]

/-- When the auxiliary universe parameter already has the form `max u v`,
`continuousCohomologyUniverseIso` is the identity isomorphism. In particular, at `u = 0` and
`v = 0` the comparison between `v = u` and `v = 0` is the identity in every degree. -/
theorem continuousCohomologyUniverseIso_max (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    X.continuousCohomologyUniverseIso.{w, u, max u v} n = Iso.refl _ := by
  ext : 1
  dsimp only [continuousCohomologyUniverseIso, HomologicalComplex.homologyMapIso]
  rw [homogeneousCochainsUniverseIso_max, Iso.refl_hom, HomologicalComplex.homologyMap_id,
    Iso.refl_hom]

/-- When the auxiliary universe parameter already has the form `max u v`,
`cocyclesUniverseAddEquiv` is the identity additive equivalence. -/
theorem cocyclesUniverseAddEquiv_max (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    X.cocyclesUniverseAddEquiv.{w, u, max u v} n = AddEquiv.refl _ := by
  ext z
  rw [cocyclesUniverseAddEquiv_apply, cocyclesUniverseIso_max]
  rfl

/-- When the auxiliary universe parameter already has the form `max u v`,
`continuousCohomologyUniverseAddEquiv` is the identity additive equivalence. -/
theorem continuousCohomologyUniverseAddEquiv_max (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    X.continuousCohomologyUniverseAddEquiv.{w, u, max u v} n = AddEquiv.refl _ := by
  ext x
  rw [continuousCohomologyUniverseAddEquiv_apply, continuousCohomologyUniverseIso_max]
  rfl

end TopRep

namespace TauCeti.ContinuousCohomology

open TopRep _root_.ContinuousCohomology

universe w u v

variable {k : Type w} [Ring k] [TopologicalSpace k]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Coefficient maps, restriction, inflation, and degree zero -/

/-- `continuousCohomologyUniverseIso` is natural in coefficient morphisms `f : X ⟶ Y`. -/
@[reassoc (attr := simp)]
theorem coeffMap_comp_continuousCohomologyUniverseIso_hom
    {X Y : TopRep.{max u v, w, u} k G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap.{w, u, max u v} f n ≫ (Y.continuousCohomologyUniverseIso n).hom =
      (X.continuousCohomologyUniverseIso n).hom ≫ coeffMap.{w, u, v} f n := by
  rw [coeffMap_def, coeffMap_def]
  exact map_comp_continuousCohomologyUniverseIso_hom (ContinuousMonoidHom.id G) f n

/-- Elementwise naturality of `continuousCohomologyUniverseAddEquiv` under coefficient morphisms
`f : X ⟶ Y`. -/
theorem continuousCohomologyUniverseAddEquiv_coeffMap
    {X Y : TopRep.{max u v, w, u} k G} (f : X ⟶ Y) (n : ℕ)
    (x : continuousCohomology.{w, u, max u v} n X) :
    Y.continuousCohomologyUniverseAddEquiv n (coeffMap.{w, u, max u v} f n x) =
      coeffMap.{w, u, v} f n (X.continuousCohomologyUniverseAddEquiv n x) :=
  congr($(coeffMap_comp_continuousCohomologyUniverseIso_hom f n) x)

variable (k G) in
/-- `continuousCohomologyFunctor` at universe parameters `max u v` and `v` are canonically
naturally isomorphic. -/
noncomputable def continuousCohomologyFunctorUniverseIso (n : ℕ) :
    continuousCohomologyFunctor.{w, u, max u v} k G n ≅
      continuousCohomologyFunctor.{w, u, v} k G n :=
  NatIso.ofComponents (fun X ↦ X.continuousCohomologyUniverseIso n)
    fun f ↦ coeffMap_comp_continuousCohomologyUniverseIso_hom f n

/-- The forward components of `continuousCohomologyFunctorUniverseIso` are
`continuousCohomologyUniverseIso.hom`. -/
@[simp]
theorem continuousCohomologyFunctorUniverseIso_hom_app
    (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    (continuousCohomologyFunctorUniverseIso k G n).hom.app X =
      (X.continuousCohomologyUniverseIso n).hom :=
  (rfl)

/-- The inverse components of `continuousCohomologyFunctorUniverseIso` are
`continuousCohomologyUniverseIso.inv`. -/
@[simp]
theorem continuousCohomologyFunctorUniverseIso_inv_app
    (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    (continuousCohomologyFunctorUniverseIso k G n).inv.app X =
      (X.continuousCohomologyUniverseIso n).inv :=
  (rfl)

/-- Restriction to a subgroup `S : Subgroup G` commutes with `continuousCohomologyUniverseIso`. -/
@[reassoc (attr := simp)]
theorem res_comp_continuousCohomologyUniverseIso_hom (S : Subgroup G)
    (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    res.{w, u, max u v} S X n ≫
        ((TopRep.res (S.subtype : S →* G) X).continuousCohomologyUniverseIso n).hom =
      (X.continuousCohomologyUniverseIso n).hom ≫ res.{w, u, v} S X n := by
  rw [res_def, res_def]
  exact map_comp_continuousCohomologyUniverseIso_hom
    (ContinuousMonoidHom.subgroupSubtype S) (𝟙 _) n

/-- Elementwise naturality of `continuousCohomologyUniverseAddEquiv` under restriction to a subgroup
`S : Subgroup G`. -/
theorem continuousCohomologyUniverseAddEquiv_res (S : Subgroup G)
    (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (x : continuousCohomology.{w, u, max u v} n X) :
    (TopRep.res (S.subtype : S →* G) X).continuousCohomologyUniverseAddEquiv n
        (res.{w, u, max u v} S X n x) =
      res.{w, u, v} S X n (X.continuousCohomologyUniverseAddEquiv n x) :=
  congr($(res_comp_continuousCohomologyUniverseIso_hom S X n) x)

/-- Inflation from a quotient `G ⧸ N` commutes with `continuousCohomologyUniverseIso`. -/
@[reassoc (attr := simp)]
theorem infl_comp_continuousCohomologyUniverseIso_hom (N : Subgroup G) [N.Normal]
    (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    infl.{w, u, max u v} N X n ≫ (X.continuousCohomologyUniverseIso n).hom =
      ((TopRep.quotientToInvariants X N).continuousCohomologyUniverseIso n).hom ≫
        infl.{w, u, v} N X n := by
  rw [infl_def, infl_def]
  exact map_comp_continuousCohomologyUniverseIso_hom
    (Subgroup.quotientMkContinuousMonoidHom N) _ n

/-- Elementwise naturality of `continuousCohomologyUniverseAddEquiv` under inflation from a quotient
`G ⧸ N`. -/
theorem continuousCohomologyUniverseAddEquiv_infl (N : Subgroup G) [N.Normal]
    (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (x : continuousCohomology.{w, u, max u v} n (TopRep.quotientToInvariants X N)) :
    X.continuousCohomologyUniverseAddEquiv n (infl.{w, u, max u v} N X n x) =
      infl.{w, u, v} N X n
        ((TopRep.quotientToInvariants X N).continuousCohomologyUniverseAddEquiv n x) :=
  congr($(infl_comp_continuousCohomologyUniverseIso_hom N X n) x)

/-- In degree zero, `continuousCohomologyUniverseIso` commutes with Mathlib's
`ContinuousCohomology.zeroIso` onto `X^G`. -/
@[reassoc (attr := simp)]
theorem continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom
    (X : TopRep.{max u v, w, u} k G) :
    (X.continuousCohomologyUniverseIso 0).hom ≫ (zeroIso.{w, u, v} X).hom =
      (zeroIso.{w, u, max u v} X).hom := by
  rw [← cancel_epi (π.{w, u, max u v} X 0), π_comp_continuousCohomologyUniverseIso_hom_assoc]
  ext σ
  simp only [ConcreteCategory.comp_apply]
  exact (coe_zeroIso_hom_π X ((X.cocyclesUniverseIso 0).hom σ)).trans
    ((X.iCycles_cocyclesUniverseAddEquiv_zero_apply σ 1).trans (coe_zeroIso_hom_π X σ).symm)

/-- In degree zero, `zeroIso.inv` commutes with `continuousCohomologyUniverseIso.hom`. -/
@[reassoc (attr := simp)]
theorem zeroIso_inv_comp_continuousCohomologyUniverseIso_zero_hom
    (X : TopRep.{max u v, w, u} k G) :
    (zeroIso.{w, u, max u v} X).inv ≫ (X.continuousCohomologyUniverseIso 0).hom =
      (zeroIso.{w, u, v} X).inv := by
  rw [Iso.inv_comp_eq, ← continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- In degree zero, `continuousCohomologyUniverseAddEquiv` carries the degree-zero class of any
invariant vector `x : X.V` to the degree-zero class of the same invariant vector `x`. -/
@[simp]
theorem continuousCohomologyUniverseAddEquiv_zero_degreeZeroClass
    (X : TopRep.{max u v, w, u} k G) (x : X.V) (hx : ∀ g : G, X.ρ g x = x) :
    X.continuousCohomologyUniverseAddEquiv 0 (degreeZeroClass.{w, u, max u v} X x hx) =
      degreeZeroClass.{w, u, v} X x hx := by
  apply (zeroIso.{w, u, v} X).toContinuousLinearEquiv.injective
  apply Subtype.ext
  have h := congrArg Subtype.val
    (congr($(continuousCohomologyUniverseIso_zero_hom_comp_zeroIso_hom X)
      (degreeZeroClass.{w, u, max u v} X x hx)))
  -- Both `zeroIso` projections evaluate `degreeZeroClass X x hx` to `x`.
  exact h.trans ((coe_zeroIso_hom_degreeZeroClass.{w, u, max u v} (X := X) x hx).trans
    (coe_zeroIso_hom_degreeZeroClass.{w, u, v} (X := X) x hx).symm)

end TauCeti.ContinuousCohomology
