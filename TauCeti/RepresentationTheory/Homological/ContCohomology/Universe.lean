/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Functoriality

/-!
# Independence of continuous cohomology from the redundant universe parameter

Mathlib's coinduced resolution `TopRep.resolutionX.{w, u, v}`, homogeneous cochain complex
`TopRep.homogeneousCochains.{w, u, v}`, cocycles `ContinuousCohomology.cocycles.{w, u, v}`, and
continuous cohomology `continuousCohomology.{w, u, v}`, for scalars `k : Type w` and a topological
group `G : Type u`, carry a third universe parameter `v` that enters the representation carrier
universe only through `max u v`. For a representation `X : TopRep.{max u v, w, u} k G`, the two
specializations at `max u v` and at `v` — in particular, for `X : TopRep.{u, w, u} k G`, the
specializations at `u` and at `0` (`max u 0 = u`) — therefore live in the same categories
`TopRep.{max u v, w, u} k G`, `CochainComplex (TopModuleCat.{max u v, w} k) ℕ`, and
`TopModuleCat.{max u v, w} k`, without being definitionally equal across arbitrary degrees.

This file constructs the canonical comparison isomorphisms between the two specializations at every
stage of the construction:

* `TopRep.resolutionXUniverseIso`: degreewise isomorphism of the coinduced resolutions, the
  identity on `X` in degree `0` and postcomposition on `C(G, -)` with the previous degree's
  isomorphism in degree `n + 1` (with inverse given by postcomposition with the inverse), commuting
  with the differentials `TopRep.d`;
* `TopRep.homogeneousCochainsUniverseIso`: isomorphism of the complexes of homogeneous cochains,
  obtained by restricting `TopRep.resolutionXUniverseIso` to `G`-invariants;
* `TauCeti.ContCohomology.cocyclesUniverseIso` and `TauCeti.ContCohomology.universeIso`: the
  induced isomorphisms in `TopModuleCat k` on cocycles and on continuous cohomology, together with
  the underlying additive equivalences `TauCeti.ContCohomology.cocyclesUniverseEquiv` and
  `TauCeti.ContCohomology.universeEquiv`.

The comparison carries the cohomology class of a cocycle to the class of the corresponding cocycle
(`TauCeti.ContCohomology.π_comp_universeIso_hom`, `TauCeti.ContCohomology.universeEquiv_π`),
leaves the values of low-degree homogeneous cocycles unchanged, reduces to the identity when `v = u`
(and hence in particular at `u = 0`, `v = 0`), and is natural with respect to simultaneous change
of group and coefficients (`TauCeti.ContCohomology.map_comp_universeIso_hom`), coefficient maps,
subgroup restriction, and quotient inflation.

## Main definitions

* `TopRep.resolutionXUniverseIso`: degreewise isomorphism between
  `TopRep.resolutionX.{w, u, max u v} X n` and `TopRep.resolutionX.{w, u, v} X n`.
* `TopRep.homogeneousCochainsUniverseIso`: chain isomorphism between
  `TopRep.homogeneousCochains.{w, u, max u v} X` and `TopRep.homogeneousCochains.{w, u, v} X`.
* `TauCeti.ContCohomology.universeIso`, `TauCeti.ContCohomology.cocyclesUniverseIso`: isomorphisms
  in `TopModuleCat k` on continuous cohomology and on cocycles;
  `TauCeti.ContCohomology.universeEquiv` and `TauCeti.ContCohomology.cocyclesUniverseEquiv` are the
  underlying additive equivalences.
* `TauCeti.ContCohomology.continuousCohomologyFunctorUniverseIso`: natural isomorphism between
  `continuousCohomologyFunctor.{w, u, max u v} k G n` and
  `continuousCohomologyFunctor.{w, u, v} k G n`.

## Main results

* `TopRep.d_comp_resolutionXUniverseIso_hom`, `TopRep.d_comp_resolutionXUniverseIso_inv`: the
  resolution isomorphism and its inverse commute with the differentials.
* `TauCeti.ContCohomology.π_comp_universeIso_hom`, `TauCeti.ContCohomology.universeEquiv_π`: the
  cohomology comparison sends the class of a cocycle to the class of its image, and preserves
  pointwise values of homogeneous cocycles in degrees `0`, `1`, and `2`.
* `TopRep.resolutionXUniverseIso_self`, `TopRep.homogeneousCochainsUniverseIso_self`,
  `TauCeti.ContCohomology.cocyclesUniverseIso_self`, `TauCeti.ContCohomology.universeIso_self`:
  when `v = u`, every comparison isomorphism is the identity.
* `TauCeti.ContCohomology.map_comp_universeIso_hom`,
  `TauCeti.ContCohomology.coeffMap_comp_universeIso_hom`,
  `TauCeti.ContCohomology.res_comp_universeIso_hom`,
  `TauCeti.ContCohomology.infl_comp_universeIso_hom`: naturality under compatible pairs,
  coefficient morphisms, restriction, and inflation (along with their inverse forms).
* `TauCeti.ContCohomology.subsingleton_continuousCohomology_max_universe_iff`,
  `TauCeti.ContCohomology.nontrivial_continuousCohomology_max_universe_iff`,
  `TauCeti.ContCohomology.natCard_continuousCohomology_max_universe_eq`,
  `TauCeti.ContCohomology.primaryComponent_continuousCohomology_max_universe_eq_bot_iff`:
  vanishing, nontriviality, cardinality, and vanishing of `p`-primary components are independent of
  the redundant universe parameter (with `v = 0` specializations `*_universe_*`).

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2.
-/

public section

open CategoryTheory ContRepresentation

namespace TopRep

universe w u v

variable {k : Type w} [Ring k] [TopologicalSpace k]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### The coinduced resolution -/

/-- Degreewise isomorphism between the coinduced resolutions of `X : TopRep.{max u v, w, u} k G`
formed at the universe parameters `max u v` and `v`. It is the identity on `X` in degree `0` and
applies `coind₁Functor k G` inductively in degree `n + 1`. -/
def resolutionXUniverseIso (X : TopRep.{max u v, w, u} k G) :
    ∀ n : ℕ, resolutionX.{w, u, max u v} X n ≅ resolutionX.{w, u, v} X n
  | 0 => Iso.refl X
  | n + 1 => (coind₁Functor k G).mapIso (resolutionXUniverseIso X n)

/-- In degree zero, `resolutionXUniverseIso` is the identity isomorphism on `X`. -/
@[simp]
theorem resolutionXUniverseIso_zero (X : TopRep.{max u v, w, u} k G) :
    resolutionXUniverseIso.{w, u, v} X 0 = Iso.refl X :=
  (rfl)

/-- In degree zero, the forward direction of `resolutionXUniverseIso` is the identity on
elements. -/
-- Not `@[simp]`: `simp` already reduces the left-hand side via `resolutionXUniverseIso_zero`.
theorem resolutionXUniverseIso_zero_hom_apply (X : TopRep.{max u v, w, u} k G)
    (x : (resolutionX.{w, u, max u v} X 0).V) :
    (resolutionXUniverseIso.{w, u, v} X 0).hom.hom x = x :=
  (rfl)

/-- In degree zero, the inverse direction of `resolutionXUniverseIso` is the identity on
elements. -/
theorem resolutionXUniverseIso_zero_inv_apply (X : TopRep.{max u v, w, u} k G)
    (x : (resolutionX.{w, u, v} X 0).V) :
    (resolutionXUniverseIso.{w, u, v} X 0).inv.hom x = x :=
  (rfl)

/-- In degree `n + 1`, `resolutionXUniverseIso` is the image under `coind₁Functor k G` of the
degree-`n` isomorphism. -/
theorem resolutionXUniverseIso_succ (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    resolutionXUniverseIso.{w, u, v} X (n + 1) =
      (coind₁Functor k G).mapIso (resolutionXUniverseIso.{w, u, v} X n) :=
  (rfl)

/-- In degree `n + 1`, the forward map of `resolutionXUniverseIso` acts on `C(G, -)` by
postcomposing with the forward map in degree `n`. -/
@[simp]
theorem resolutionXUniverseIso_succ_hom_apply (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (f : (resolutionX.{w, u, max u v} X (n + 1)).V) (g : G) :
    DFunLike.coe (F := C(G, (resolutionX.{w, u, v} X n).V))
        ((resolutionXUniverseIso.{w, u, v} X (n + 1)).hom.hom f) g =
      (resolutionXUniverseIso.{w, u, v} X n).hom.hom (f g) :=
  (rfl)

/-- In degree `n + 1`, the inverse map of `resolutionXUniverseIso` acts on `C(G, -)` by
postcomposing with the inverse map in degree `n`. -/
@[simp]
theorem resolutionXUniverseIso_succ_inv_apply (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (f : (resolutionX.{w, u, v} X (n + 1)).V) (g : G) :
    DFunLike.coe (F := C(G, (resolutionX.{w, u, max u v} X n).V))
        ((resolutionXUniverseIso.{w, u, v} X (n + 1)).inv.hom f) g =
      (resolutionXUniverseIso.{w, u, v} X n).inv.hom (f g) :=
  (rfl)

/-- When `v = u`, `resolutionXUniverseIso` is the identity isomorphism in every degree. -/
@[simp]
theorem resolutionXUniverseIso_self (X : TopRep.{u, w, u} k G) :
    ∀ n : ℕ, resolutionXUniverseIso.{w, u, u} X n = Iso.refl (resolutionX.{w, u, u} X n)
  | 0 => rfl
  | n + 1 => by simp [resolutionXUniverseIso_succ, resolutionXUniverseIso_self X n]

/-- `resolutionXUniverseIso` commutes with the differentials of the coinduced resolution. -/
@[reassoc]
theorem d_comp_resolutionXUniverseIso_hom (X : TopRep.{max u v, w, u} k G) :
    ∀ n : ℕ, d.{w, u, max u v} X n ≫ (resolutionXUniverseIso.{w, u, v} X (n + 1)).hom =
      (resolutionXUniverseIso.{w, u, v} X n).hom ≫ d.{w, u, v} X n
  | 0 => by simp [d_zero, resolutionXUniverseIso_succ]
  | n + 1 => by
    rw [d_succ, d_succ, resolutionXUniverseIso_succ, Functor.mapIso_hom,
      Preadditive.sub_comp, Preadditive.comp_sub]
    refine congrArg₂ (· - ·) ?_ ?_
    · rw [← coind₁ι_app, ← coind₁ι_app]
      exact (coind₁ι.naturality (resolutionXUniverseIso.{w, u, v} X (n + 1)).hom).symm.trans
        (by simp)
    · rw [← Functor.map_comp, d_comp_resolutionXUniverseIso_hom X n, Functor.map_comp,
        resolutionXUniverseIso_succ, Functor.mapIso_hom]

/-- The inverse of `resolutionXUniverseIso` commutes with the differentials of the coinduced
resolution. -/
@[reassoc]
theorem d_comp_resolutionXUniverseIso_inv (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    d.{w, u, v} X n ≫ (resolutionXUniverseIso.{w, u, v} X (n + 1)).inv =
      (resolutionXUniverseIso.{w, u, v} X n).inv ≫ d.{w, u, max u v} X n := by
  rw [Iso.comp_inv_eq, Category.assoc, d_comp_resolutionXUniverseIso_hom, Iso.inv_hom_id_assoc]

/-! ### The homogeneous cochains -/

/-- Chain isomorphism between the homogeneous cochain complexes of `X : TopRep.{max u v, w, u} k G`
formed at the universe parameters `max u v` and `v`, induced on `G`-invariants by
`resolutionXUniverseIso`. -/
def homogeneousCochainsUniverseIso (X : TopRep.{max u v, w, u} k G) :
    homogeneousCochains.{w, u, max u v} X ≅ homogeneousCochains.{w, u, v} X :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (invariantsFunctor k G).mapIso (resolutionXUniverseIso.{w, u, v} X (n + 1)))
    (by
      rintro i j (rfl : i + 1 = j)
      rw [homogeneousCochains.d_eq, homogeneousCochains.d_eq, Functor.mapIso_hom,
        Functor.mapIso_hom, ← Functor.map_comp, ← Functor.map_comp,
        d_comp_resolutionXUniverseIso_hom])

/-- In degree `n`, the forward component of `homogeneousCochainsUniverseIso` is the map on
`G`-invariants induced by `resolutionXUniverseIso` in degree `n + 1`. -/
theorem homogeneousCochainsUniverseIso_hom_f (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    (homogeneousCochainsUniverseIso.{w, u, v} X).hom.f n =
      (invariantsFunctor k G).map (resolutionXUniverseIso.{w, u, v} X (n + 1)).hom :=
  (rfl)

/-- In degree `n`, the inverse component of `homogeneousCochainsUniverseIso` is the map on
`G`-invariants induced by the inverse of `resolutionXUniverseIso` in degree `n + 1`. -/
theorem homogeneousCochainsUniverseIso_inv_f (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    (homogeneousCochainsUniverseIso.{w, u, v} X).inv.f n =
      (invariantsFunctor k G).map (resolutionXUniverseIso.{w, u, v} X (n + 1)).inv :=
  (rfl)

/-- On underlying invariant elements, the forward component of `homogeneousCochainsUniverseIso` in
degree `n` acts as `resolutionXUniverseIso` in degree `n + 1`. -/
theorem coe_homogeneousCochainsUniverseIso_hom_f (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (x : (homogeneousCochains.{w, u, max u v} X).X n) :
    ((homogeneousCochainsUniverseIso.{w, u, v} X).hom.f n x).val =
      (resolutionXUniverseIso.{w, u, v} X (n + 1)).hom.hom x.val :=
  (rfl)

/-- On underlying invariant elements, the inverse component of `homogeneousCochainsUniverseIso` in
degree `n` acts as the inverse of `resolutionXUniverseIso` in degree `n + 1`. -/
theorem coe_homogeneousCochainsUniverseIso_inv_f (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (x : (homogeneousCochains.{w, u, v} X).X n) :
    ((homogeneousCochainsUniverseIso.{w, u, v} X).inv.f n x).val =
      (resolutionXUniverseIso.{w, u, v} X (n + 1)).inv.hom x.val :=
  (rfl)

/-- When `v = u`, `homogeneousCochainsUniverseIso` is the identity isomorphism of cochain
complexes. -/
@[simp]
theorem homogeneousCochainsUniverseIso_self (X : TopRep.{u, w, u} k G) :
    homogeneousCochainsUniverseIso.{w, u, u} X = Iso.refl (homogeneousCochains.{w, u, u} X) := by
  ext n
  simp [homogeneousCochainsUniverseIso]

end TopRep

namespace TauCeti.ContCohomology

open TopRep _root_.ContinuousCohomology
open TauCeti.ContinuousCohomology (coeffMap coeffMap_def continuousCohomologyFunctor
  res res_def infl infl_def)

universe w u v

/-! ### Cocycles and continuous cohomology -/

section Cohomology

variable {k : Type w} [Ring k] [TopologicalSpace k]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Continuous cohomology does not depend on the redundant universe parameter.** For
`X : TopRep.{max u v, w, u} k G`, the `n`th continuous cohomology formed at `max u v` is
canonically isomorphic in `TopModuleCat k` to that formed at `v`. -/
noncomputable def universeIso (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    continuousCohomology.{w, u, max u v} n X ≅ continuousCohomology.{w, u, v} n X :=
  HomologicalComplex.homologyMapIso (homogeneousCochainsUniverseIso.{w, u, v} X) n

/-- The `n`-cocycles of `X : TopRep.{max u v, w, u} k G` formed at `max u v` are canonically
isomorphic in `TopModuleCat k` to those formed at `v`. -/
noncomputable def cocyclesUniverseIso (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    cocycles.{w, u, max u v} X n ≅ cocycles.{w, u, v} X n :=
  HomologicalComplex.cyclesMapIso (homogeneousCochainsUniverseIso.{w, u, v} X) n

/-- Under `cocyclesUniverseIso`, a cocycle corresponds to its image under
`homogeneousCochainsUniverseIso`. -/
@[reassoc (attr := simp)]
theorem cocyclesUniverseIso_hom_comp_iCycles (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    (cocyclesUniverseIso.{w, u, v} X n).hom ≫ (homogeneousCochains.{w, u, v} X).iCycles n =
      (homogeneousCochains.{w, u, max u v} X).iCycles n ≫
        (homogeneousCochainsUniverseIso.{w, u, v} X).hom.f n :=
  HomologicalComplex.cyclesMap_i (homogeneousCochainsUniverseIso.{w, u, v} X).hom n

/-- Under the inverse of `cocyclesUniverseIso`, a cocycle corresponds to its image under the
inverse of `homogeneousCochainsUniverseIso`. -/
@[reassoc (attr := simp)]
theorem cocyclesUniverseIso_inv_comp_iCycles (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    (cocyclesUniverseIso.{w, u, v} X n).inv ≫ (homogeneousCochains.{w, u, max u v} X).iCycles n =
      (homogeneousCochains.{w, u, v} X).iCycles n ≫
        (homogeneousCochainsUniverseIso.{w, u, v} X).inv.f n :=
  HomologicalComplex.cyclesMap_i (homogeneousCochainsUniverseIso.{w, u, v} X).inv n

/-- `universeIso` sends the cohomology class of a cocycle to the class of its image under
`cocyclesUniverseIso`. -/
@[reassoc (attr := simp)]
theorem π_comp_universeIso_hom (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    π.{w, u, max u v} X n ≫ (universeIso.{w, u, v} X n).hom =
      (cocyclesUniverseIso.{w, u, v} X n).hom ≫ π.{w, u, v} X n :=
  HomologicalComplex.homologyπ_naturality (homogeneousCochainsUniverseIso.{w, u, v} X).hom n

/-- The inverse of `universeIso` sends the cohomology class of a cocycle to the class of its image
under the inverse of `cocyclesUniverseIso`. -/
@[reassoc (attr := simp)]
theorem π_comp_universeIso_inv (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    π.{w, u, v} X n ≫ (universeIso.{w, u, v} X n).inv =
      (cocyclesUniverseIso.{w, u, v} X n).inv ≫ π.{w, u, max u v} X n :=
  HomologicalComplex.homologyπ_naturality (homogeneousCochainsUniverseIso.{w, u, v} X).inv n

/-- Additive equivalence between the `n`-cocycles of `X` formed at the universe parameters
`max u v` and `v`. -/
noncomputable def cocyclesUniverseEquiv (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    cocycles.{w, u, max u v} X n ≃+ cocycles.{w, u, v} X n :=
  (cocyclesUniverseIso.{w, u, v} X n).toContinuousLinearEquiv.toAddEquiv

/-- `cocyclesUniverseEquiv` acts on elements as the forward morphism of `cocyclesUniverseIso`. -/
theorem cocyclesUniverseEquiv_apply (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (z : cocycles.{w, u, max u v} X n) :
    cocyclesUniverseEquiv.{w, u, v} X n z = (cocyclesUniverseIso.{w, u, v} X n).hom z :=
  (rfl)

/-- The inverse of `cocyclesUniverseEquiv` acts on elements as the inverse morphism of
`cocyclesUniverseIso`. -/
theorem cocyclesUniverseEquiv_symm_apply (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (z : cocycles.{w, u, v} X n) :
    (cocyclesUniverseEquiv.{w, u, v} X n).symm z = (cocyclesUniverseIso.{w, u, v} X n).inv z :=
  (rfl)

/-- **Additive equivalence on continuous cohomology across the redundant universe parameter**: for
`X : TopRep.{max u v, w, u} k G` and every degree `n`, an additive equivalence between
`continuousCohomology.{w, u, max u v} n X` and `continuousCohomology.{w, u, v} n X`. At `v = 0`,
for `X : TopRep.{u, w, u} k G`, this compares `continuousCohomology.{w, u, u} n X` with
`continuousCohomology.{w, u, 0} n X`. -/
noncomputable def universeEquiv (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    continuousCohomology.{w, u, max u v} n X ≃+ continuousCohomology.{w, u, v} n X :=
  (universeIso.{w, u, v} X n).toContinuousLinearEquiv.toAddEquiv

/-- `universeEquiv` acts on elements as the forward morphism of `universeIso`. -/
theorem universeEquiv_apply (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (a : continuousCohomology.{w, u, max u v} n X) :
    universeEquiv.{w, u, v} X n a = (universeIso.{w, u, v} X n).hom a :=
  (rfl)

/-- The inverse of `universeEquiv` acts on elements as the inverse morphism of `universeIso`. -/
theorem universeEquiv_symm_apply (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (a : continuousCohomology.{w, u, v} n X) :
    (universeEquiv.{w, u, v} X n).symm a = (universeIso.{w, u, v} X n).inv a :=
  (rfl)

/-- `universeEquiv` carries the cohomology class of a cocycle to the class of its image under
`cocyclesUniverseEquiv`. -/
@[simp]
theorem universeEquiv_π (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (z : cocycles.{w, u, max u v} X n) :
    universeEquiv.{w, u, v} X n (π.{w, u, max u v} X n z) =
      π.{w, u, v} X n (cocyclesUniverseEquiv.{w, u, v} X n z) :=
  congr($(π_comp_universeIso_hom.{w, u, v} X n) z)

/-- The inverse of `universeEquiv` carries the cohomology class of a cocycle to the class of its
preimage under `cocyclesUniverseEquiv`. -/
@[simp]
theorem universeEquiv_symm_π (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (z : cocycles.{w, u, v} X n) :
    (universeEquiv.{w, u, v} X n).symm (π.{w, u, v} X n z) =
      π.{w, u, max u v} X n ((cocyclesUniverseEquiv.{w, u, v} X n).symm z) :=
  congr($(π_comp_universeIso_inv.{w, u, v} X n) z)

/-- Under `cocyclesUniverseEquiv`, the underlying homogeneous cochain of an `n`-cocycle is carried
by `resolutionXUniverseIso` in degree `n + 1`. -/
theorem coe_iCycles_cocyclesUniverseEquiv (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (z : cocycles.{w, u, max u v} X n) :
    ((homogeneousCochains.{w, u, v} X).iCycles n (cocyclesUniverseEquiv.{w, u, v} X n z)).val =
      (resolutionXUniverseIso.{w, u, v} X (n + 1)).hom.hom
        ((homogeneousCochains.{w, u, max u v} X).iCycles n z).val := by
  have h : (homogeneousCochains.{w, u, v} X).iCycles n (cocyclesUniverseEquiv.{w, u, v} X n z) =
      (homogeneousCochainsUniverseIso.{w, u, v} X).hom.f n
        ((homogeneousCochains.{w, u, max u v} X).iCycles n z) :=
    congr($(cocyclesUniverseIso_hom_comp_iCycles.{w, u, v} X n) z)
  rw [h, coe_homogeneousCochainsUniverseIso_hom_f]

/-- Under the inverse of `cocyclesUniverseEquiv`, the underlying homogeneous cochain of an
`n`-cocycle is carried by the inverse of `resolutionXUniverseIso` in degree `n + 1`. -/
theorem coe_iCycles_cocyclesUniverseEquiv_symm (X : TopRep.{max u v, w, u} k G) (n : ℕ)
    (z : cocycles.{w, u, v} X n) :
    ((homogeneousCochains.{w, u, max u v} X).iCycles n
        ((cocyclesUniverseEquiv.{w, u, v} X n).symm z)).val =
      (resolutionXUniverseIso.{w, u, v} X (n + 1)).inv.hom
        ((homogeneousCochains.{w, u, v} X).iCycles n z).val := by
  have h : (homogeneousCochains.{w, u, max u v} X).iCycles n
        ((cocyclesUniverseEquiv.{w, u, v} X n).symm z) =
      (homogeneousCochainsUniverseIso.{w, u, v} X).inv.f n
        ((homogeneousCochains.{w, u, v} X).iCycles n z) :=
    congr($(cocyclesUniverseIso_inv_comp_iCycles.{w, u, v} X n) z)
  rw [h, coe_homogeneousCochainsUniverseIso_inv_f]

/-- In degree zero, `cocyclesUniverseEquiv` preserves the values of a homogeneous cocycle on `G`. -/
-- Not `@[simp]`: `simp` unfolds `(homogeneousCochains _).X 0` inside the implicit type of
-- `Subtype.val` before matching; use with `rw`.
theorem iCycles_cocyclesUniverseEquiv_zero_apply (X : TopRep.{max u v, w, u} k G)
    (z : cocycles.{w, u, max u v} X 0) (g₀ : G) :
    ((homogeneousCochains.{w, u, v} X).iCycles 0
        (cocyclesUniverseEquiv.{w, u, v} X 0 z)).val g₀ =
      ((homogeneousCochains.{w, u, max u v} X).iCycles 0 z).val g₀ :=
  (congrArg (fun w : C(G, X.V) ↦ w g₀)
    (coe_iCycles_cocyclesUniverseEquiv.{w, u, v} X 0 z)).trans
    ((resolutionXUniverseIso_succ_hom_apply.{w, u, v} X 0 _ g₀).trans
      (resolutionXUniverseIso_zero_hom_apply.{w, u, v} X _))

/-- In degree zero, the inverse of `cocyclesUniverseEquiv` preserves the values of a homogeneous
cocycle on `G`. -/
theorem iCycles_cocyclesUniverseEquiv_symm_zero_apply (X : TopRep.{max u v, w, u} k G)
    (z : cocycles.{w, u, v} X 0) (g₀ : G) :
    ((homogeneousCochains.{w, u, max u v} X).iCycles 0
        ((cocyclesUniverseEquiv.{w, u, v} X 0).symm z)).val g₀ =
      ((homogeneousCochains.{w, u, v} X).iCycles 0 z).val g₀ :=
  (congrArg (fun w : C(G, X.V) ↦ w g₀)
    (coe_iCycles_cocyclesUniverseEquiv_symm.{w, u, v} X 0 z)).trans
    ((resolutionXUniverseIso_succ_inv_apply.{w, u, v} X 0 _ g₀).trans
      (resolutionXUniverseIso_zero_inv_apply.{w, u, v} X _))

/-- In degree one, `cocyclesUniverseEquiv` preserves the values of a homogeneous cocycle on `G`. -/
theorem iCycles_cocyclesUniverseEquiv_one_apply (X : TopRep.{max u v, w, u} k G)
    (z : cocycles.{w, u, max u v} X 1) (g₀ g₁ : G) :
    ((homogeneousCochains.{w, u, v} X).iCycles 1
        (cocyclesUniverseEquiv.{w, u, v} X 1 z)).val g₀ g₁ =
      ((homogeneousCochains.{w, u, max u v} X).iCycles 1 z).val g₀ g₁ :=
  (congrArg (fun w : C(G, C(G, X.V)) ↦ w g₀ g₁)
    (coe_iCycles_cocyclesUniverseEquiv.{w, u, v} X 1 z)).trans
    ((congrArg (fun w : C(G, X.V) ↦ w g₁)
      (resolutionXUniverseIso_succ_hom_apply.{w, u, v} X 1 _ g₀)).trans
      ((resolutionXUniverseIso_succ_hom_apply.{w, u, v} X 0 _ g₁).trans
        (resolutionXUniverseIso_zero_hom_apply.{w, u, v} X _)))

/-- In degree one, the inverse of `cocyclesUniverseEquiv` preserves the values of a homogeneous
cocycle on `G`. -/
theorem iCycles_cocyclesUniverseEquiv_symm_one_apply (X : TopRep.{max u v, w, u} k G)
    (z : cocycles.{w, u, v} X 1) (g₀ g₁ : G) :
    ((homogeneousCochains.{w, u, max u v} X).iCycles 1
        ((cocyclesUniverseEquiv.{w, u, v} X 1).symm z)).val g₀ g₁ =
      ((homogeneousCochains.{w, u, v} X).iCycles 1 z).val g₀ g₁ :=
  (congrArg (fun w : C(G, C(G, X.V)) ↦ w g₀ g₁)
    (coe_iCycles_cocyclesUniverseEquiv_symm.{w, u, v} X 1 z)).trans
    ((congrArg (fun w : C(G, X.V) ↦ w g₁)
      (resolutionXUniverseIso_succ_inv_apply.{w, u, v} X 1 _ g₀)).trans
      ((resolutionXUniverseIso_succ_inv_apply.{w, u, v} X 0 _ g₁).trans
        (resolutionXUniverseIso_zero_inv_apply.{w, u, v} X _)))

/-- In degree two, `cocyclesUniverseEquiv` preserves the values of a homogeneous cocycle on `G`. -/
theorem iCycles_cocyclesUniverseEquiv_two_apply (X : TopRep.{max u v, w, u} k G)
    (z : cocycles.{w, u, max u v} X 2) (g₀ g₁ g₂ : G) :
    ((homogeneousCochains.{w, u, v} X).iCycles 2
        (cocyclesUniverseEquiv.{w, u, v} X 2 z)).val g₀ g₁ g₂ =
      ((homogeneousCochains.{w, u, max u v} X).iCycles 2 z).val g₀ g₁ g₂ :=
  (congrArg (fun w : C(G, C(G, C(G, X.V))) ↦ w g₀ g₁ g₂)
    (coe_iCycles_cocyclesUniverseEquiv.{w, u, v} X 2 z)).trans
    ((congrArg (fun w : C(G, C(G, X.V)) ↦ w g₁ g₂)
      (resolutionXUniverseIso_succ_hom_apply.{w, u, v} X (1 + 1) _ g₀)).trans
      ((congrArg (fun w : C(G, X.V) ↦ w g₂)
        (resolutionXUniverseIso_succ_hom_apply.{w, u, v} X 1 _ g₁)).trans
        ((resolutionXUniverseIso_succ_hom_apply.{w, u, v} X 0 _ g₂).trans
          (resolutionXUniverseIso_zero_hom_apply.{w, u, v} X _))))

/-- In degree two, the inverse of `cocyclesUniverseEquiv` preserves the values of a homogeneous
cocycle on `G`. -/
theorem iCycles_cocyclesUniverseEquiv_symm_two_apply (X : TopRep.{max u v, w, u} k G)
    (z : cocycles.{w, u, v} X 2) (g₀ g₁ g₂ : G) :
    ((homogeneousCochains.{w, u, max u v} X).iCycles 2
        ((cocyclesUniverseEquiv.{w, u, v} X 2).symm z)).val g₀ g₁ g₂ =
      ((homogeneousCochains.{w, u, v} X).iCycles 2 z).val g₀ g₁ g₂ :=
  (congrArg (fun w : C(G, C(G, C(G, X.V))) ↦ w g₀ g₁ g₂)
    (coe_iCycles_cocyclesUniverseEquiv_symm.{w, u, v} X 2 z)).trans
    ((congrArg (fun w : C(G, C(G, X.V)) ↦ w g₁ g₂)
      (resolutionXUniverseIso_succ_inv_apply.{w, u, v} X (1 + 1) _ g₀)).trans
      ((congrArg (fun w : C(G, X.V) ↦ w g₂)
        (resolutionXUniverseIso_succ_inv_apply.{w, u, v} X 1 _ g₁)).trans
        ((resolutionXUniverseIso_succ_inv_apply.{w, u, v} X 0 _ g₂).trans
          (resolutionXUniverseIso_zero_inv_apply.{w, u, v} X _))))

end Cohomology

/-! ### Identity when the universe parameters coincide -/

section Self

variable {k : Type w} [Ring k] [TopologicalSpace k]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : TopRep.{u, w, u} k G) (n : ℕ)

/-- When `v = u`, `cocyclesUniverseIso` is the identity isomorphism on `cocycles X n`. -/
@[simp]
theorem cocyclesUniverseIso_self :
    cocyclesUniverseIso.{w, u, u} X n = Iso.refl (cocycles.{w, u, u} X n) := by
  ext x
  simp [cocyclesUniverseIso]

/-- When `v = u`, `universeIso` is the identity isomorphism on `continuousCohomology n X`. -/
@[simp]
theorem universeIso_self :
    universeIso.{w, u, u} X n = Iso.refl (continuousCohomology.{w, u, u} n X) := by
  ext x
  simp [universeIso]

/-- When `v = u`, `cocyclesUniverseEquiv` is the identity additive equivalence. -/
@[simp]
theorem cocyclesUniverseEquiv_self :
    cocyclesUniverseEquiv.{w, u, u} X n = AddEquiv.refl (cocycles.{w, u, u} X n) := by
  ext x
  simp [cocyclesUniverseEquiv_apply]

/-- When `v = u` (and in particular at `u = 0`, `v = 0`), `universeEquiv` is the identity additive
equivalence in every degree. -/
@[simp]
theorem universeEquiv_self :
    universeEquiv.{w, u, u} X n = AddEquiv.refl (continuousCohomology.{w, u, u} n X) := by
  ext x
  simp [universeEquiv_apply]

end Self

/-! ### Naturality -/

section Naturality

variable {k : Type w} [Ring k] [TopologicalSpace k]
  {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {X : TopRep.{max u v, w, u} k G} {Y : TopRep.{max u v, w, u} k H}

/-- `resolutionXUniverseIso` commutes with the map induced on coinduced resolutions by a compatible
pair `(φ, f)`. -/
@[reassoc]
theorem resolutionMap_comp_resolutionXUniverseIso_hom (φ : H →ₜ* G)
    (f : TopRep.res (φ : H →* G) X ⟶ Y) :
    ∀ i : ℕ,
      resolutionMap.{w, u, max u v} φ f i ≫ (resolutionXUniverseIso.{w, u, v} Y i).hom =
        (resFunctor (φ : H →* G)).map (resolutionXUniverseIso.{w, u, v} X i).hom ≫
          resolutionMap.{w, u, v} φ f i
  | 0 => by ext; rfl
  | i + 1 => by
    ext g h
    exact ConcreteCategory.congr_hom
      (resolutionMap_comp_resolutionXUniverseIso_hom φ f i) (g (φ h))

/-- The inverse of `resolutionXUniverseIso` commutes with the map induced on coinduced resolutions
by a compatible pair `(φ, f)`. -/
@[reassoc]
theorem resolutionMap_comp_resolutionXUniverseIso_inv (φ : H →ₜ* G)
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (i : ℕ) :
    resolutionMap.{w, u, v} φ f i ≫ (resolutionXUniverseIso.{w, u, v} Y i).inv =
      (resFunctor (φ : H →* G)).map (resolutionXUniverseIso.{w, u, v} X i).inv ≫
        resolutionMap.{w, u, max u v} φ f i := by
  rw [Iso.comp_inv_eq, Category.assoc, resolutionMap_comp_resolutionXUniverseIso_hom,
    ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]

/-- `homogeneousCochainsUniverseIso` commutes with the cochain map induced by a compatible pair
`(φ, f)`. -/
@[reassoc]
theorem cochainsMap_comp_homogeneousCochainsUniverseIso_hom (φ : H →ₜ* G)
    (f : TopRep.res (φ : H →* G) X ⟶ Y) :
    cochainsMap.{w, u, max u v} φ f ≫ (homogeneousCochainsUniverseIso.{w, u, v} Y).hom =
      (homogeneousCochainsUniverseIso.{w, u, v} X).hom ≫ cochainsMap.{w, u, v} φ f := by
  ext i x
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    (resolutionMap_comp_resolutionXUniverseIso_hom.{w, u, v} φ f (i + 1)) x.1

/-- The inverse of `homogeneousCochainsUniverseIso` commutes with the cochain map induced by a
compatible pair `(φ, f)`. -/
@[reassoc]
theorem cochainsMap_comp_homogeneousCochainsUniverseIso_inv (φ : H →ₜ* G)
    (f : TopRep.res (φ : H →* G) X ⟶ Y) :
    cochainsMap.{w, u, v} φ f ≫ (homogeneousCochainsUniverseIso.{w, u, v} Y).inv =
      (homogeneousCochainsUniverseIso.{w, u, v} X).inv ≫ cochainsMap.{w, u, max u v} φ f := by
  rw [Iso.comp_inv_eq, Category.assoc, cochainsMap_comp_homogeneousCochainsUniverseIso_hom,
    Iso.inv_hom_id_assoc]

/-- `cocyclesUniverseIso` is natural with respect to the cocycle map of any compatible pair
`(φ, f)`. -/
@[reassoc (attr := simp)]
theorem cocyclesMap_comp_cocyclesUniverseIso_hom (φ : H →ₜ* G)
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    cocyclesMap.{w, u, max u v} φ f n ≫ (cocyclesUniverseIso.{w, u, v} Y n).hom =
      (cocyclesUniverseIso.{w, u, v} X n).hom ≫ cocyclesMap.{w, u, v} φ f n := by
  simp only [cocyclesMap, cocyclesUniverseIso, HomologicalComplex.cyclesMapIso_hom,
    ← HomologicalComplex.cyclesMap_comp, cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

/-- The inverse of `cocyclesUniverseIso` is natural with respect to the cocycle map of any
compatible pair `(φ, f)`. -/
@[reassoc (attr := simp)]
theorem cocyclesMap_comp_cocyclesUniverseIso_inv (φ : H →ₜ* G)
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    cocyclesMap.{w, u, v} φ f n ≫ (cocyclesUniverseIso.{w, u, v} Y n).inv =
      (cocyclesUniverseIso.{w, u, v} X n).inv ≫ cocyclesMap.{w, u, max u v} φ f n := by
  rw [Iso.comp_inv_eq, Category.assoc, cocyclesMap_comp_cocyclesUniverseIso_hom,
    Iso.inv_hom_id_assoc]

/-- **Naturality of `universeIso` for compatible pairs**: `universeIso` commutes with
`ContinuousCohomology.map φ f n` for every continuous homomorphism `φ : H →ₜ* G` and
equivariant coefficient map `f`. -/
@[reassoc (attr := simp)]
theorem map_comp_universeIso_hom (φ : H →ₜ* G)
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.map.{w, u, max u v} φ f n ≫ (universeIso.{w, u, v} Y n).hom =
      (universeIso.{w, u, v} X n).hom ≫ _root_.ContinuousCohomology.map.{w, u, v} φ f n := by
  simp only [_root_.ContinuousCohomology.map, universeIso, HomologicalComplex.homologyMapIso_hom,
    ← HomologicalComplex.homologyMap_comp, cochainsMap_comp_homogeneousCochainsUniverseIso_hom]

/-- The inverse of `universeIso` commutes with `ContinuousCohomology.map φ f n`. -/
@[reassoc (attr := simp)]
theorem map_comp_universeIso_inv (φ : H →ₜ* G)
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.map.{w, u, v} φ f n ≫ (universeIso.{w, u, v} Y n).inv =
      (universeIso.{w, u, v} X n).inv ≫
        _root_.ContinuousCohomology.map.{w, u, max u v} φ f n := by
  rw [Iso.comp_inv_eq, Category.assoc, map_comp_universeIso_hom, Iso.inv_hom_id_assoc]

end Naturality

section SameGroupNaturality

variable {k : Type w} [Ring k] [TopologicalSpace k]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Naturality of `universeIso` in the representation**: `universeIso` commutes with the
coefficient map `coeffMap f n` induced by a morphism `f : X ⟶ Y` in `TopRep k G`. -/
@[reassoc (attr := simp)]
theorem coeffMap_comp_universeIso_hom {X Y : TopRep.{max u v, w, u} k G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap.{w, u, max u v} f n ≫ (universeIso.{w, u, v} Y n).hom =
      (universeIso.{w, u, v} X n).hom ≫ coeffMap.{w, u, v} f n := by
  rw [coeffMap_def, coeffMap_def]
  exact map_comp_universeIso_hom.{w, u, v} (X := X) (ContinuousMonoidHom.id G) f n

/-- The inverse of `universeIso` commutes with coefficient maps `coeffMap f n`. -/
@[reassoc (attr := simp)]
theorem coeffMap_comp_universeIso_inv {X Y : TopRep.{max u v, w, u} k G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap.{w, u, v} f n ≫ (universeIso.{w, u, v} Y n).inv =
      (universeIso.{w, u, v} X n).inv ≫ coeffMap.{w, u, max u v} f n := by
  rw [Iso.comp_inv_eq, Category.assoc, coeffMap_comp_universeIso_hom, Iso.inv_hom_id_assoc]

/-- Elementwise naturality of `universeEquiv` with respect to equivariant coefficient maps. -/
theorem universeEquiv_coeffMap_apply {X Y : TopRep.{max u v, w, u} k G} (f : X ⟶ Y) (n : ℕ)
    (a : continuousCohomology.{w, u, max u v} n X) :
    universeEquiv.{w, u, v} Y n (coeffMap.{w, u, max u v} f n a) =
      coeffMap.{w, u, v} f n (universeEquiv.{w, u, v} X n a) :=
  congr($(coeffMap_comp_universeIso_hom.{w, u, v} f n) a)

/-- Elementwise naturality of the inverse of `universeEquiv` with respect to equivariant
coefficient maps. -/
theorem universeEquiv_symm_coeffMap_apply {X Y : TopRep.{max u v, w, u} k G} (f : X ⟶ Y) (n : ℕ)
    (a : continuousCohomology.{w, u, v} n X) :
    (universeEquiv.{w, u, v} Y n).symm (coeffMap.{w, u, v} f n a) =
      coeffMap.{w, u, max u v} f n ((universeEquiv.{w, u, v} X n).symm a) :=
  congr($(coeffMap_comp_universeIso_inv.{w, u, v} f n) a)

/-- `universeIso` commutes with subgroup restriction `TauCeti.ContinuousCohomology.res`. -/
@[reassoc (attr := simp)]
theorem res_comp_universeIso_hom (S : Subgroup G) (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    res.{w, u, max u v} S X n ≫
        (universeIso.{w, u, v} (TopRep.res (S.subtype : S →* G) X) n).hom =
      (universeIso.{w, u, v} X n).hom ≫ res.{w, u, v} S X n := by
  rw [res_def, res_def]
  exact map_comp_universeIso_hom.{w, u, v} (X := X)
    (ContinuousMonoidHom.subgroupSubtype S) (𝟙 (TopRep.res (S.subtype : S →* G) X)) n

/-- The inverse of `universeIso` commutes with subgroup restriction. -/
@[reassoc (attr := simp)]
theorem res_comp_universeIso_inv (S : Subgroup G) (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    res.{w, u, v} S X n ≫
        (universeIso.{w, u, v} (TopRep.res (S.subtype : S →* G) X) n).inv =
      (universeIso.{w, u, v} X n).inv ≫ res.{w, u, max u v} S X n := by
  rw [Iso.comp_inv_eq, Category.assoc, res_comp_universeIso_hom, Iso.inv_hom_id_assoc]

/-- `universeIso` commutes with quotient inflation `TauCeti.ContinuousCohomology.infl`. -/
@[reassoc (attr := simp)]
theorem infl_comp_universeIso_hom (N : Subgroup G) [N.Normal]
    (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    infl.{w, u, max u v} N X n ≫ (universeIso.{w, u, v} X n).hom =
      (universeIso.{w, u, v} (X.quotientToInvariants N) n).hom ≫ infl.{w, u, v} N X n := by
  rw [infl_def, infl_def]
  exact map_comp_universeIso_hom.{w, u, v} (Subgroup.quotientMkContinuousMonoidHom N) _ n

/-- The inverse of `universeIso` commutes with quotient inflation. -/
@[reassoc (attr := simp)]
theorem infl_comp_universeIso_inv (N : Subgroup G) [N.Normal]
    (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    infl.{w, u, v} N X n ≫ (universeIso.{w, u, v} X n).inv =
      (universeIso.{w, u, v} (X.quotientToInvariants N) n).inv ≫ infl.{w, u, max u v} N X n := by
  rw [Iso.comp_inv_eq, Category.assoc, infl_comp_universeIso_hom, Iso.inv_hom_id_assoc]

end SameGroupNaturality

/-- Natural isomorphism between the continuous cohomology functors formed at the universe parameters
`max u v` and `v`. -/
noncomputable def continuousCohomologyFunctorUniverseIso (k : Type w) [Ring k] [TopologicalSpace k]
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (n : ℕ) :
    continuousCohomologyFunctor.{w, u, max u v} k G n ≅
      continuousCohomologyFunctor.{w, u, v} k G n :=
  NatIso.ofComponents (fun X ↦ universeIso.{w, u, v} X n)
    (fun f ↦ coeffMap_comp_universeIso_hom.{w, u, v} f n)

section FunctorApp

variable {k : Type w} [Ring k] [TopologicalSpace k]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The forward component of `continuousCohomologyFunctorUniverseIso` at `X` is
`(universeIso X n).hom`. -/
@[simp]
theorem continuousCohomologyFunctorUniverseIso_hom_app (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    (continuousCohomologyFunctorUniverseIso.{w, u, v} k G n).hom.app X =
      (universeIso.{w, u, v} X n).hom :=
  (rfl)

/-- The inverse component of `continuousCohomologyFunctorUniverseIso` at `X` is
`(universeIso X n).inv`. -/
@[simp]
theorem continuousCohomologyFunctorUniverseIso_inv_app (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    (continuousCohomologyFunctorUniverseIso.{w, u, v} k G n).inv.app X =
      (universeIso.{w, u, v} X n).inv :=
  (rfl)

end FunctorApp

/-! ### Invariance of group-theoretic properties -/

section Invariance

variable {k : Type w} [Ring k] [TopologicalSpace k]
  {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Vanishing of `continuousCohomology n X` does not depend on replacing the auxiliary universe
parameter `v` by `max u v`. -/
theorem subsingleton_continuousCohomology_max_universe_iff (X : TopRep.{max u v, w, u} k G)
    (n : ℕ) :
    Subsingleton (continuousCohomology.{w, u, max u v} n X) ↔
      Subsingleton (continuousCohomology.{w, u, v} n X) :=
  (universeEquiv.{w, u, v} X n).toEquiv.subsingleton_congr

/-- Nontriviality of `continuousCohomology n X` does not depend on replacing the auxiliary universe
parameter `v` by `max u v`. -/
theorem nontrivial_continuousCohomology_max_universe_iff (X : TopRep.{max u v, w, u} k G)
    (n : ℕ) :
    Nontrivial (continuousCohomology.{w, u, max u v} n X) ↔
      Nontrivial (continuousCohomology.{w, u, v} n X) :=
  (universeEquiv.{w, u, v} X n).toEquiv.nontrivial_congr

/-- The cardinality of `continuousCohomology n X` does not depend on replacing the auxiliary
universe parameter `v` by `max u v`. -/
theorem natCard_continuousCohomology_max_universe_eq (X : TopRep.{max u v, w, u} k G) (n : ℕ) :
    Nat.card (continuousCohomology.{w, u, max u v} n X) =
      Nat.card (continuousCohomology.{w, u, v} n X) :=
  Nat.card_congr (universeEquiv.{w, u, v} X n).toEquiv

/-- Vanishing of the `p`-primary component of `continuousCohomology n X` does not depend on
replacing the auxiliary universe parameter `v` by `max u v`. -/
theorem primaryComponent_continuousCohomology_max_universe_eq_bot_iff
    (X : TopRep.{max u v, w, u} k G) (n p : ℕ) :
    AddCommGroup.primaryComponent (continuousCohomology.{w, u, max u v} n X) p = ⊥ ↔
      AddCommGroup.primaryComponent (continuousCohomology.{w, u, v} n X) p = ⊥ := by
  let e := universeEquiv.{w, u, v} X n
  simp only [AddSubgroup.eq_bot_iff_forall, AddCommGroup.mem_primaryComponent]
  exact ⟨fun h y ⟨m, hm⟩ ↦ e.symm.injective (by
      rw [map_zero]
      exact h (e.symm y) ⟨m, by rw [← map_nsmul, hm, map_zero]⟩),
    fun h x ⟨m, hm⟩ ↦ e.injective (by
      rw [map_zero]
      exact h (e x) ⟨m, by rw [← map_nsmul, hm, map_zero]⟩)⟩

/-- For `X : TopRep.{u, w, u} k G`, vanishing of `continuousCohomology n X` agrees at the auxiliary
universe parameters `u` and `0`. -/
theorem subsingleton_continuousCohomology_universe_iff (X : TopRep.{u, w, u} k G) (n : ℕ) :
    Subsingleton (continuousCohomology.{w, u, u} n X) ↔
      Subsingleton (continuousCohomology.{w, u, 0} n X) :=
  subsingleton_continuousCohomology_max_universe_iff.{w, u, 0} X n

/-- For `X : TopRep.{u, w, u} k G`, nontriviality of `continuousCohomology n X` agrees at the
auxiliary universe parameters `u` and `0`. -/
theorem nontrivial_continuousCohomology_universe_iff (X : TopRep.{u, w, u} k G) (n : ℕ) :
    Nontrivial (continuousCohomology.{w, u, u} n X) ↔
      Nontrivial (continuousCohomology.{w, u, 0} n X) :=
  nontrivial_continuousCohomology_max_universe_iff.{w, u, 0} X n

/-- For `X : TopRep.{u, w, u} k G`, the cardinality of `continuousCohomology n X` agrees at the
auxiliary universe parameters `u` and `0`. -/
theorem natCard_continuousCohomology_universe_eq (X : TopRep.{u, w, u} k G) (n : ℕ) :
    Nat.card (continuousCohomology.{w, u, u} n X) =
      Nat.card (continuousCohomology.{w, u, 0} n X) :=
  natCard_continuousCohomology_max_universe_eq.{w, u, 0} X n

/-- For `X : TopRep.{u, w, u} k G`, vanishing of the `p`-primary component of
`continuousCohomology n X` agrees at the auxiliary universe parameters `u` and `0`. -/
theorem primaryComponent_continuousCohomology_universe_eq_bot_iff (X : TopRep.{u, w, u} k G)
    (n p : ℕ) :
    AddCommGroup.primaryComponent (continuousCohomology.{w, u, u} n X) p = ⊥ ↔
      AddCommGroup.primaryComponent (continuousCohomology.{w, u, 0} n X) p = ⊥ :=
  primaryComponent_continuousCohomology_max_universe_eq_bot_iff.{w, u, 0} X n p

end Invariance

end TauCeti.ContCohomology
