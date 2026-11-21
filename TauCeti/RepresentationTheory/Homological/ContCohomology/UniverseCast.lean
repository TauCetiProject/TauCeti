/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Torsion
public import TauCeti.RepresentationTheory.Homological.ContCohomology.DegreeZero

import TauCeti.Algebra.Homology.CochainComplex.Basic
import TauCeti.CategoryTheory.ConcreteCategory.Basic

/-!
# Independence of continuous cohomology from the extra coefficient universe

For a topological ring `R : Type u` and a topological group `G : Type v`, Mathlib defines the
coinduced resolution `TopRep.resolutionX`, the homogeneous cochain complex
`TopRep.homogeneousCochains`, and continuous cohomology `continuousCohomology` for representations
`X : TopRep.{max v w} R G` parameterized by an auxiliary universe `w`. The universe of continuous
maps `C(G, V)` from `G : Type v` into a module `V : Type (max v w)` is already `max v w`, and
replacing `w` by `max v w` leaves `max v (max v w)` definitionally equal to `max v w`. Thus
`TopRep.homogeneousCochains.{u, v, max v w} X` and `TopRep.homogeneousCochains.{u, v, w} X` have
the exact same type `CochainComplex (TopModuleCat.{max v w} R) ℕ`, and
`continuousCohomology.{u, v, max v w} n X` and `continuousCohomology.{u, v, w} n X` have the exact
same type `TopModuleCat.{max v w} R`.

However, the recursive definitions `TopRep.resolutionX` and `TopRep.d` record `w` directly in their
equation-compiler auxiliaries, so the two complexes and cohomology objects are not definitionally
equal unless `max v w` and `w` coincide, and Mathlib's `ContinuousCohomology.map` requires a single
shared parameter `w` on both source and target. In particular, for `X : TopRep.{v} R G` (such as a
discrete `G`-module in `Type v`), the cohomology objects formed at `w = v` and at `w = 0` cannot be
identified by `rfl`.

This file proves the propositional equalities at the level of resolution terms, differentials,
cochain complexes, cocycles, and continuous cohomology, both in general (`max v w` against `w`) and
at `w = 0` (`v` against `0`, which avoids higher-order universe unification when rewriting). From
the equality of homogeneous cochain complexes it packages the canonical chain isomorphism
`TopRep.homogeneousCochainsUniverseCast` and its induced isomorphisms on cocycles
(`TauCeti.ContinuousCohomology.cocyclesUniverseCast`) and on continuous cohomology
(`TauCeti.ContinuousCohomology.universeCast`), and shows that `universeCast` preserves classes of
cocycles, commutes with `ContinuousCohomology.zeroIso` and `degreeZeroClass`, and is natural with
respect to compatible-pair maps (`ContinuousCohomology.map`, `coeffMap`, `res`, and `infl`).

Universe parameters are ordered `w u v` so that `u` and `v` are inferred from `X : TopRep R G` when
instantiating the extra universe `w` explicitly (for example, `universeCast.{0} X n`).

## Main definitions

* `TopRep.homogeneousCochainsUniverseCast`: the canonical chain isomorphism
  `TopRep.homogeneousCochains.{u, v, max v w} X ≅ TopRep.homogeneousCochains.{u, v, w} X`.
* `TauCeti.ContinuousCohomology.cocyclesUniverseCast`: the induced isomorphism on continuous
  `n`-cocycles.
* `TauCeti.ContinuousCohomology.universeCast`: the induced isomorphism
  `continuousCohomology.{u, v, max v w} n X ≅ continuousCohomology.{u, v, w} n X` in
  `TopModuleCat R`.
* `TauCeti.ContinuousCohomology.continuousCohomologyFunctorUniverseCast`: the natural isomorphism
  between `continuousCohomologyFunctor` at extra universe parameters `max v w` and `w`.

## Main results

* `TopRep.homogeneousCochains_max_universe_eq`, `TopRep.homogeneousCochains_universe_eq`:
  propositional independence of the homogeneous cochain complex from the extra universe parameter.
* `TauCeti.ContinuousCohomology.continuousCohomology_max_universe_eq`,
  `TauCeti.ContinuousCohomology.continuousCohomology_universe_eq`: propositional independence of
  `continuousCohomology n X` from the extra universe parameter.
* `TauCeti.ContinuousCohomology.universeCast_hom_π`,
  `TauCeti.ContinuousCohomology.universeCast_hom_cochainClass`: `universeCast` sends the class of a
  homogeneous cocycle to the class of the corresponding cocycle.
* `TauCeti.ContinuousCohomology.universeCast_hom_comp_zeroIso_hom`,
  `TauCeti.ContinuousCohomology.universeCast_hom_degreeZeroClass`: compatibility of `universeCast`
  with degree-zero invariants.
* `TauCeti.ContinuousCohomology.map_comp_universeCast_hom`,
  `TauCeti.ContinuousCohomology.coeffMap_comp_universeCast_hom`,
  `TauCeti.ContinuousCohomology.res_comp_universeCast_hom`,
  `TauCeti.ContinuousCohomology.infl_comp_universeCast_hom`: compatibility of `universeCast` with
  compatible-pair functoriality and its named specializations.
* `TauCeti.ContinuousCohomology.subsingleton_continuousCohomology_max_universe_iff`,
  `TauCeti.ContinuousCohomology.primaryComponent_continuousCohomology_eq_bot_max_universe_iff`:
  triviality and `p`-primary component vanishing of `continuousCohomology n X` are independent of
  the extra universe parameter.
-/

public section

open CategoryTheory

namespace TopRep

universe w u v

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-! ### Independence of the coinduced resolution and homogeneous cochain complex -/

-- None of the `*_max_universe_eq` or `*_universe_eq` lemmas below is marked `@[simp]`: at `w = v`
-- (respectively `v = 0`) the two sides are syntactically identical, so `simp` would loop.

/-- Every term `TopRep.resolutionX X n` of the coinduced resolution is independent of the extra
universe parameter `w`. -/
theorem resolutionX_max_universe_eq (X : TopRep.{max v w} R G) (n : ℕ) :
    resolutionX.{u, v, max v w} X n = resolutionX.{u, v, w} X n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg coind₁ ih

/-- For `X : TopRep.{v} R G`, every term of `TopRep.resolutionX` at extra universe `v` equals that
at extra universe `0`. -/
theorem resolutionX_universe_eq (X : TopRep.{v} R G) (n : ℕ) :
    resolutionX.{u, v, v} X n = resolutionX.{u, v, 0} X n :=
  X.resolutionX_max_universe_eq.{0} n

/-- Every differential `TopRep.d X n` of the coinduced resolution is heterogeneously independent of
the extra universe parameter `w`. -/
theorem d_max_universe_heq (X : TopRep.{max v w} R G) (n : ℕ) :
    d.{u, v, max v w} X n ≍ d.{u, v, w} X n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [d_succ]
    exact congr_arg_heq
      (fun p : Σ A : TopRep.{max v w} R G, A ⟶ A.coind₁ ↦
        ofHom p.1.coind₁.ρ.coind₁ι - (coind₁Functor R G).map p.2)
      (Sigma.ext (X.resolutionX_max_universe_eq.{w} n) ih : ⟨_, _⟩ = ⟨_, _⟩)

/-- For `X : TopRep.{v} R G`, every differential `TopRep.d` at extra universe `v` is
heterogeneously equal to that at extra universe `0`. -/
theorem d_universe_heq (X : TopRep.{v} R G) (n : ℕ) :
    d.{u, v, v} X n ≍ d.{u, v, 0} X n :=
  X.d_max_universe_heq.{0} n

/-- The coinduced resolution `TopRep.resolution X` is independent of the extra universe parameter
`w`. -/
theorem resolution_max_universe_eq (X : TopRep.{max v w} R G) :
    resolution.{u, v, max v w} X = resolution.{u, v, w} X :=
  CochainComplex.of_eq (X.resolutionX_max_universe_eq.{w}) (X.d_max_universe_heq.{w})

/-- For `X : TopRep.{v} R G`, `TopRep.resolution X` at extra universe `v` equals that at extra
universe `0`. -/
theorem resolution_universe_eq (X : TopRep.{v} R G) :
    resolution.{u, v, v} X = resolution.{u, v, 0} X :=
  X.resolution_max_universe_eq.{0}

/-- The shifted coinduced resolution `TopRep.resolution' X` is independent of the extra universe
parameter `w`. -/
theorem resolution'_max_universe_eq (X : TopRep.{max v w} R G) :
    resolution'.{u, v, max v w} X = resolution'.{u, v, w} X :=
  CochainComplex.of_eq (fun n ↦ X.resolutionX_max_universe_eq.{w} (n + 1))
    (fun n ↦ X.d_max_universe_heq.{w} (n + 1))

/-- For `X : TopRep.{v} R G`, `TopRep.resolution' X` at extra universe `v` equals that at extra
universe `0`. -/
theorem resolution'_universe_eq (X : TopRep.{v} R G) :
    resolution'.{u, v, v} X = resolution'.{u, v, 0} X :=
  X.resolution'_max_universe_eq.{0}

/-- The homogeneous cochain complex `TopRep.homogeneousCochains X` is independent of the extra
universe parameter `w`. -/
theorem homogeneousCochains_max_universe_eq (X : TopRep.{max v w} R G) :
    homogeneousCochains.{u, v, max v w} X = homogeneousCochains.{u, v, w} X :=
  congrArg ((invariantsFunctor R G).mapHomologicalComplex _).obj (X.resolution'_max_universe_eq.{w})

/-- For `X : TopRep.{v} R G`, `TopRep.homogeneousCochains X` at extra universe `v` equals that at
extra universe `0`. -/
theorem homogeneousCochains_universe_eq (X : TopRep.{v} R G) :
    homogeneousCochains.{u, v, v} X = homogeneousCochains.{u, v, 0} X :=
  X.homogeneousCochains_max_universe_eq.{0}

/-! ### Chain isomorphism on homogeneous cochains -/

/-- The canonical isomorphism of homogeneous cochain complexes comparing extra universe parameters
`max v w` and `w`. -/
noncomputable def homogeneousCochainsUniverseCast (X : TopRep.{max v w} R G) :
    homogeneousCochains.{u, v, max v w} X ≅ homogeneousCochains.{u, v, w} X :=
  eqToIso (X.homogeneousCochains_max_universe_eq.{w})

/-- `homogeneousCochainsUniverseCast` is `eqToIso` of `homogeneousCochains_max_universe_eq`. -/
theorem homogeneousCochainsUniverseCast_eq_eqToIso (X : TopRep.{max v w} R G) :
    X.homogeneousCochainsUniverseCast.{w} = eqToIso (X.homogeneousCochains_max_universe_eq.{w}) :=
  (rfl)

/-- At `max v w`, `homogeneousCochainsUniverseCast` is the identity isomorphism. -/
theorem homogeneousCochainsUniverseCast_max_self (X : TopRep.{max v w} R G) :
    X.homogeneousCochainsUniverseCast.{max v w} = Iso.refl _ := by
  simp [homogeneousCochainsUniverseCast_eq_eqToIso]

/-- At `w = v`, `homogeneousCochainsUniverseCast` is the identity isomorphism. -/
@[simp]
theorem homogeneousCochainsUniverseCast_self (X : TopRep.{v} R G) :
    X.homogeneousCochainsUniverseCast.{v} = Iso.refl _ :=
  X.homogeneousCochainsUniverseCast_max_self.{0}

/-- `homogeneousCochainsUniverseCast` preserves homogeneous cochains in every degree up to
heterogeneous equality. -/
theorem homogeneousCochainsUniverseCast_hom_f_apply_heq (X : TopRep.{max v w} R G) (n : ℕ)
    (a : (homogeneousCochains.{u, v, max v w} X).X n) :
    (X.homogeneousCochainsUniverseCast.{w}).hom.f n a ≍ a := by
  rw [homogeneousCochainsUniverseCast_eq_eqToIso, eqToIso.hom, HomologicalComplex.eqToHom_f]
  apply TauCeti.eqToHom_apply_heq

/-- The inverse of `homogeneousCochainsUniverseCast` preserves homogeneous cochains in every degree
up to heterogeneous equality. -/
theorem homogeneousCochainsUniverseCast_inv_f_apply_heq (X : TopRep.{max v w} R G) (n : ℕ)
    (a : (homogeneousCochains.{u, v, w} X).X n) :
    (X.homogeneousCochainsUniverseCast.{w}).inv.f n a ≍ a := by
  rw [homogeneousCochainsUniverseCast_eq_eqToIso, eqToIso.inv, HomologicalComplex.eqToHom_f]
  apply TauCeti.eqToHom_apply_heq

-- Not `@[simp]`: `simp` rewrites the implicit carrier `(homogeneousCochains X).X k` through
-- `CategoryTheory.Functor.mapHomologicalComplex_obj_X`, so these statements are for `rw`.

/-- In degree `0`, `homogeneousCochainsUniverseCast` acts as the identity on cochains. -/
theorem homogeneousCochainsUniverseCast_hom_f_zero_apply (X : TopRep.{max v w} R G)
    (a : (homogeneousCochains.{u, v, max v w} X).X 0) :
    (X.homogeneousCochainsUniverseCast.{w}).hom.f 0 a = a :=
  eq_of_heq (X.homogeneousCochainsUniverseCast_hom_f_apply_heq.{w} 0 a)

/-- In degree `0`, the inverse of `homogeneousCochainsUniverseCast` acts as the identity on
cochains. -/
theorem homogeneousCochainsUniverseCast_inv_f_zero_apply (X : TopRep.{max v w} R G)
    (a : (homogeneousCochains.{u, v, w} X).X 0) :
    (X.homogeneousCochainsUniverseCast.{w}).inv.f 0 a = a :=
  eq_of_heq (X.homogeneousCochainsUniverseCast_inv_f_apply_heq.{w} 0 a)

/-- In degree `1`, `homogeneousCochainsUniverseCast` acts as the identity on cochains. -/
theorem homogeneousCochainsUniverseCast_hom_f_one_apply (X : TopRep.{max v w} R G)
    (a : (homogeneousCochains.{u, v, max v w} X).X 1) :
    (X.homogeneousCochainsUniverseCast.{w}).hom.f 1 a = a :=
  eq_of_heq (X.homogeneousCochainsUniverseCast_hom_f_apply_heq.{w} 1 a)

/-- In degree `1`, the inverse of `homogeneousCochainsUniverseCast` acts as the identity on
cochains. -/
theorem homogeneousCochainsUniverseCast_inv_f_one_apply (X : TopRep.{max v w} R G)
    (a : (homogeneousCochains.{u, v, w} X).X 1) :
    (X.homogeneousCochainsUniverseCast.{w}).inv.f 1 a = a :=
  eq_of_heq (X.homogeneousCochainsUniverseCast_inv_f_apply_heq.{w} 1 a)

/-- In degree `2`, `homogeneousCochainsUniverseCast` acts as the identity on cochains. -/
theorem homogeneousCochainsUniverseCast_hom_f_two_apply (X : TopRep.{max v w} R G)
    (a : (homogeneousCochains.{u, v, max v w} X).X 2) :
    (X.homogeneousCochainsUniverseCast.{w}).hom.f 2 a = a :=
  eq_of_heq (X.homogeneousCochainsUniverseCast_hom_f_apply_heq.{w} 2 a)

/-- In degree `2`, the inverse of `homogeneousCochainsUniverseCast` acts as the identity on
cochains. -/
theorem homogeneousCochainsUniverseCast_inv_f_two_apply (X : TopRep.{max v w} R G)
    (a : (homogeneousCochains.{u, v, w} X).X 2) :
    (X.homogeneousCochainsUniverseCast.{w}).inv.f 2 a = a :=
  eq_of_heq (X.homogeneousCochainsUniverseCast_inv_f_apply_heq.{w} 2 a)

end TopRep

namespace TauCeti.ContinuousCohomology

open _root_.ContinuousCohomology TopRep

universe w u v

variable {R : Type u} [Ring R] [TopologicalSpace R]
  {G H : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-! ### Independence and transport of cocycles and continuous cohomology -/

/-- Continuous cocycles `ContinuousCohomology.cocycles X n` are independent of the extra universe
parameter `w`. -/
theorem cocycles_max_universe_eq (X : TopRep.{max v w} R G) (n : ℕ) :
    cocycles.{u, v, max v w} X n = cocycles.{u, v, w} X n :=
  congrArg (HomologicalComplex.cycles · n) (X.homogeneousCochains_max_universe_eq.{w})

/-- For `X : TopRep.{v} R G`, `ContinuousCohomology.cocycles X n` at extra universe `v` equals that
at extra universe `0`. -/
theorem cocycles_universe_eq (X : TopRep.{v} R G) (n : ℕ) :
    cocycles.{u, v, v} X n = cocycles.{u, v, 0} X n :=
  cocycles_max_universe_eq.{0} X n

/-- Continuous cohomology `continuousCohomology n X` is independent of the extra universe parameter
`w`. -/
theorem continuousCohomology_max_universe_eq (X : TopRep.{max v w} R G) (n : ℕ) :
    continuousCohomology.{u, v, max v w} n X = continuousCohomology.{u, v, w} n X :=
  congrArg (HomologicalComplex.homology · n) (X.homogeneousCochains_max_universe_eq.{w})

/-- For `X : TopRep.{v} R G`, `continuousCohomology n X` at extra universe `v` equals that at extra
universe `0`. -/
theorem continuousCohomology_universe_eq (X : TopRep.{v} R G) (n : ℕ) :
    continuousCohomology.{u, v, v} n X = continuousCohomology.{u, v, 0} n X :=
  continuousCohomology_max_universe_eq.{0} X n

/-- The canonical isomorphism of continuous `n`-cocycles comparing extra universe parameters
`max v w` and `w`, induced by `TopRep.homogeneousCochainsUniverseCast`. -/
noncomputable def cocyclesUniverseCast (X : TopRep.{max v w} R G) (n : ℕ) :
    cocycles.{u, v, max v w} X n ≅ cocycles.{u, v, w} X n :=
  (HomologicalComplex.cyclesFunctor (TopModuleCat R) (ComplexShape.up ℕ) n).mapIso
    (X.homogeneousCochainsUniverseCast.{w})

/-- `cocyclesUniverseCast` agrees with `eqToIso` of `cocycles_max_universe_eq`. -/
theorem cocyclesUniverseCast_eq_eqToIso (X : TopRep.{max v w} R G) (n : ℕ) :
    cocyclesUniverseCast.{w} X n = eqToIso (cocycles_max_universe_eq.{w} X n) := by
  rw [cocyclesUniverseCast, homogeneousCochainsUniverseCast_eq_eqToIso, eqToIso_map]

/-- At `max v w`, `cocyclesUniverseCast` is the identity isomorphism. -/
theorem cocyclesUniverseCast_max_self (X : TopRep.{max v w} R G) (n : ℕ) :
    cocyclesUniverseCast.{max v w} X n = Iso.refl _ := by
  simp [cocyclesUniverseCast_eq_eqToIso]

/-- At `w = v`, `cocyclesUniverseCast` is the identity isomorphism. -/
@[simp]
theorem cocyclesUniverseCast_self (X : TopRep.{v} R G) (n : ℕ) :
    cocyclesUniverseCast.{v} X n = Iso.refl _ :=
  cocyclesUniverseCast_max_self.{0} X n

/-- **Transport of continuous cohomology across the extra universe parameter**: the canonical
isomorphism `continuousCohomology.{u, v, max v w} n X ≅ continuousCohomology.{u, v, w} n X` in
`TopModuleCat R` induced on homology by `TopRep.homogeneousCochainsUniverseCast`. -/
noncomputable def universeCast (X : TopRep.{max v w} R G) (n : ℕ) :
    continuousCohomology.{u, v, max v w} n X ≅ continuousCohomology.{u, v, w} n X :=
  (HomologicalComplex.homologyFunctor (TopModuleCat R) (ComplexShape.up ℕ) n).mapIso
    (X.homogeneousCochainsUniverseCast.{w})

/-- `universeCast` agrees with `eqToIso` of `continuousCohomology_max_universe_eq`. -/
theorem universeCast_eq_eqToIso (X : TopRep.{max v w} R G) (n : ℕ) :
    universeCast.{w} X n = eqToIso (continuousCohomology_max_universe_eq.{w} X n) := by
  rw [universeCast, homogeneousCochainsUniverseCast_eq_eqToIso, eqToIso_map]

/-- At `max v w`, `universeCast` is the identity isomorphism. -/
theorem universeCast_max_self (X : TopRep.{max v w} R G) (n : ℕ) :
    universeCast.{max v w} X n = Iso.refl _ := by
  simp [universeCast_eq_eqToIso]

/-- At `w = v`, `universeCast` is the identity isomorphism. -/
@[simp]
theorem universeCast_self (X : TopRep.{v} R G) (n : ℕ) :
    universeCast.{v} X n = Iso.refl _ :=
  universeCast_max_self.{0} X n

/-- `universeCast` preserves classes up to heterogeneous equality. -/
theorem universeCast_hom_apply_heq (X : TopRep.{max v w} R G) (n : ℕ)
    (x : continuousCohomology.{u, v, max v w} n X) :
    (universeCast.{w} X n).hom x ≍ x := by
  rw [universeCast_eq_eqToIso, eqToIso.hom]
  apply TauCeti.eqToHom_apply_heq

/-- The inverse of `universeCast` preserves classes up to heterogeneous equality. -/
theorem universeCast_inv_apply_heq (X : TopRep.{max v w} R G) (n : ℕ)
    (x : continuousCohomology.{u, v, w} n X) :
    (universeCast.{w} X n).inv x ≍ x := by
  rw [universeCast_eq_eqToIso, eqToIso.inv]
  apply TauCeti.eqToHom_apply_heq

/-! ### Compatibility with cocycles and homogeneous cocycle classes -/

/-- `universeCast` commutes with the cohomology class projection `ContinuousCohomology.π`. -/
@[reassoc]
theorem π_comp_universeCast_hom (X : TopRep.{max v w} R G) (n : ℕ) :
    π.{u, v, max v w} X n ≫ (universeCast.{w} X n).hom =
      (cocyclesUniverseCast.{w} X n).hom ≫ π.{u, v, w} X n :=
  HomologicalComplex.homologyπ_naturality (X.homogeneousCochainsUniverseCast.{w}).hom n

/-- The inverse of `universeCast` commutes with `ContinuousCohomology.π`. -/
@[reassoc]
theorem π_comp_universeCast_inv (X : TopRep.{max v w} R G) (n : ℕ) :
    π.{u, v, w} X n ≫ (universeCast.{w} X n).inv =
      (cocyclesUniverseCast.{w} X n).inv ≫ π.{u, v, max v w} X n :=
  HomologicalComplex.homologyπ_naturality (X.homogeneousCochainsUniverseCast.{w}).inv n

/-- `universeCast` sends the class of a cocycle to the class of its image under
`cocyclesUniverseCast`. -/
@[simp]
theorem universeCast_hom_π (X : TopRep.{max v w} R G) (n : ℕ)
    (z : cocycles.{u, v, max v w} X n) :
    (universeCast.{w} X n).hom (π.{u, v, max v w} X n z) =
      π.{u, v, w} X n ((cocyclesUniverseCast.{w} X n).hom z) :=
  ConcreteCategory.congr_hom (π_comp_universeCast_hom.{w} X n) z

/-- The inverse of `universeCast` sends the class of a cocycle to the class of its image under the
inverse of `cocyclesUniverseCast`. -/
@[simp]
theorem universeCast_inv_π (X : TopRep.{max v w} R G) (n : ℕ)
    (z : cocycles.{u, v, w} X n) :
    (universeCast.{w} X n).inv (π.{u, v, w} X n z) =
      π.{u, v, max v w} X n ((cocyclesUniverseCast.{w} X n).inv z) :=
  ConcreteCategory.congr_hom (π_comp_universeCast_inv.{w} X n) z

-- Not `@[simp]`: `simp` rewrites the implicit carrier `(homogeneousCochains X).X n` through
-- `CategoryTheory.Functor.mapHomologicalComplex_obj_X`, so these statements are for `rw`.

/-- The underlying homogeneous cochain of a cocycle transported by `cocyclesUniverseCast` is its
image under `homogeneousCochainsUniverseCast`. -/
theorem iCycles_cocyclesUniverseCast_hom_apply (X : TopRep.{max v w} R G) (n : ℕ)
    (z : cocycles.{u, v, max v w} X n) :
    (homogeneousCochains.{u, v, w} X).iCycles n ((cocyclesUniverseCast.{w} X n).hom z) =
      (X.homogeneousCochainsUniverseCast.{w}).hom.f n
        ((homogeneousCochains.{u, v, max v w} X).iCycles n z) := by
  rw [cocyclesUniverseCast, Functor.mapIso_hom, HomologicalComplex.cyclesFunctor_map]
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (X.homogeneousCochainsUniverseCast.{w}).hom n) z
  simp only [ConcreteCategory.comp_apply] at h
  exact h

/-- The underlying homogeneous cochain of a cocycle transported by the inverse of
`cocyclesUniverseCast` is its image under the inverse of `homogeneousCochainsUniverseCast`. -/
theorem iCycles_cocyclesUniverseCast_inv_apply (X : TopRep.{max v w} R G) (n : ℕ)
    (z : cocycles.{u, v, w} X n) :
    (homogeneousCochains.{u, v, max v w} X).iCycles n ((cocyclesUniverseCast.{w} X n).inv z) =
      (X.homogeneousCochainsUniverseCast.{w}).inv.f n
        ((homogeneousCochains.{u, v, w} X).iCycles n z) := by
  rw [cocyclesUniverseCast, Functor.mapIso_inv, HomologicalComplex.cyclesFunctor_map]
  have h := ConcreteCategory.congr_hom
    (HomologicalComplex.cyclesMap_i (X.homogeneousCochainsUniverseCast.{w}).inv n) z
  simp only [ConcreteCategory.comp_apply] at h
  exact h

/-- `universeCast` sends the class of a homogeneous cocycle `a` to the class of any heterogeneously
equal homogeneous cocycle `a'`. -/
theorem universeCast_hom_cochainClass (X : TopRep.{max v w} R G) (n : ℕ)
    (a : (homogeneousCochains.{u, v, max v w} X).X n)
    (ha : ((homogeneousCochains.{u, v, max v w} X).d n (n + 1)).hom a = 0)
    (a' : (homogeneousCochains.{u, v, w} X).X n)
    (ha' : ((homogeneousCochains.{u, v, w} X).d n (n + 1)).hom a' = 0)
    (haa' : a ≍ a') :
    (universeCast.{w} X n).hom (TopRep.cochainClass.{u, v, max v w} X n a ha) =
      TopRep.cochainClass.{u, v, w} X n a' ha' := by
  obtain rfl : ((X.homogeneousCochainsUniverseCast.{w}).hom.f n).hom a = a' :=
    eq_of_heq ((X.homogeneousCochainsUniverseCast_hom_f_apply_heq.{w} n a).trans haa')
  rw [cochainClass_def, cochainClass_def, universeCast, Functor.mapIso_hom,
    HomologicalComplex.homologyFunctor_map]
  exact HomologicalComplex.homologyMap_homologyπ_cyclesMkOfEq
    (X.homogeneousCochainsUniverseCast.{w}).hom a (n + 1) (CochainComplex.next ℕ n) ha

/-- The inverse of `universeCast` sends the class of a homogeneous cocycle `a'` to the class of any
heterogeneously equal homogeneous cocycle `a`. -/
theorem universeCast_inv_cochainClass (X : TopRep.{max v w} R G) (n : ℕ)
    (a' : (homogeneousCochains.{u, v, w} X).X n)
    (ha' : ((homogeneousCochains.{u, v, w} X).d n (n + 1)).hom a' = 0)
    (a : (homogeneousCochains.{u, v, max v w} X).X n)
    (ha : ((homogeneousCochains.{u, v, max v w} X).d n (n + 1)).hom a = 0)
    (haa' : a' ≍ a) :
    (universeCast.{w} X n).inv (TopRep.cochainClass.{u, v, w} X n a' ha') =
      TopRep.cochainClass.{u, v, max v w} X n a ha := by
  rw [← universeCast_hom_cochainClass.{w} X n a ha a' ha' haa'.symm, Iso.hom_inv_id_apply]

/-- In degree `0`, `universeCast` preserves the class of any homogeneous cocycle. -/
@[simp]
theorem universeCast_hom_cochainClass_zero (X : TopRep.{max v w} R G)
    (a : (homogeneousCochains.{u, v, w} X).X 0)
    (ha : ((homogeneousCochains.{u, v, w} X).d 0 (0 + 1)).hom a = 0) :
    (universeCast.{w} X 0).hom (TopRep.cochainClass.{u, v, max v w} X 0 a ha) =
      TopRep.cochainClass.{u, v, w} X 0 a ha :=
  universeCast_hom_cochainClass.{w} X 0 a ha a ha HEq.rfl

/-- In degree `0`, the inverse of `universeCast` preserves the class of any homogeneous cocycle. -/
@[simp]
theorem universeCast_inv_cochainClass_zero (X : TopRep.{max v w} R G)
    (a : (homogeneousCochains.{u, v, w} X).X 0)
    (ha : ((homogeneousCochains.{u, v, w} X).d 0 (0 + 1)).hom a = 0) :
    (universeCast.{w} X 0).inv (TopRep.cochainClass.{u, v, w} X 0 a ha) =
      TopRep.cochainClass.{u, v, max v w} X 0 a ha :=
  universeCast_inv_cochainClass.{w} X 0 a ha a ha HEq.rfl

/-- In degree `1`, `universeCast` preserves the class of any homogeneous cocycle. -/
@[simp]
theorem universeCast_hom_cochainClass_one (X : TopRep.{max v w} R G)
    (a : (homogeneousCochains.{u, v, w} X).X 1)
    (ha : ((homogeneousCochains.{u, v, w} X).d 1 (1 + 1)).hom a = 0) :
    (universeCast.{w} X 1).hom (TopRep.cochainClass.{u, v, max v w} X 1 a ha) =
      TopRep.cochainClass.{u, v, w} X 1 a ha :=
  universeCast_hom_cochainClass.{w} X 1 a ha a ha HEq.rfl

/-- In degree `1`, the inverse of `universeCast` preserves the class of any homogeneous cocycle. -/
@[simp]
theorem universeCast_inv_cochainClass_one (X : TopRep.{max v w} R G)
    (a : (homogeneousCochains.{u, v, w} X).X 1)
    (ha : ((homogeneousCochains.{u, v, w} X).d 1 (1 + 1)).hom a = 0) :
    (universeCast.{w} X 1).inv (TopRep.cochainClass.{u, v, w} X 1 a ha) =
      TopRep.cochainClass.{u, v, max v w} X 1 a ha :=
  universeCast_inv_cochainClass.{w} X 1 a ha a ha HEq.rfl

/-- In degree `2`, `universeCast` preserves the class of any homogeneous cocycle. -/
@[simp]
theorem universeCast_hom_cochainClass_two (X : TopRep.{max v w} R G)
    (a : (homogeneousCochains.{u, v, w} X).X 2)
    (ha : ((homogeneousCochains.{u, v, w} X).d 2 (2 + 1)).hom a = 0) :
    (universeCast.{w} X 2).hom (TopRep.cochainClass.{u, v, max v w} X 2 a ha) =
      TopRep.cochainClass.{u, v, w} X 2 a ha :=
  universeCast_hom_cochainClass.{w} X 2 a ha a ha HEq.rfl

/-- In degree `2`, the inverse of `universeCast` preserves the class of any homogeneous cocycle. -/
@[simp]
theorem universeCast_inv_cochainClass_two (X : TopRep.{max v w} R G)
    (a : (homogeneousCochains.{u, v, w} X).X 2)
    (ha : ((homogeneousCochains.{u, v, w} X).d 2 (2 + 1)).hom a = 0) :
    (universeCast.{w} X 2).inv (TopRep.cochainClass.{u, v, w} X 2 a ha) =
      TopRep.cochainClass.{u, v, max v w} X 2 a ha :=
  universeCast_inv_cochainClass.{w} X 2 a ha a ha HEq.rfl

/-! ### Compatibility with degree zero -/

/-- In degree `0`, `universeCast` commutes with Mathlib's `ContinuousCohomology.zeroIso`. -/
@[reassoc (attr := simp)]
theorem universeCast_hom_comp_zeroIso_hom (X : TopRep.{max v w} R G) :
    (universeCast.{w} X 0).hom ≫ (zeroIso.{u, v, w} X).hom =
      (zeroIso.{u, v, max v w} X).hom := by
  rw [← cancel_epi (π.{u, v, max v w} X 0), π_comp_universeCast_hom_assoc]
  ext σ
  simp only [ConcreteCategory.comp_apply]
  rw [coe_zeroIso_hom_π, coe_zeroIso_hom_π, iCycles_cocyclesUniverseCast_hom_apply,
    homogeneousCochainsUniverseCast_hom_f_zero_apply]

/-- In degree `0`, the inverse of `universeCast` commutes with `ContinuousCohomology.zeroIso`. -/
@[reassoc (attr := simp)]
theorem universeCast_inv_comp_zeroIso_hom (X : TopRep.{max v w} R G) :
    (universeCast.{w} X 0).inv ≫ (zeroIso.{u, v, max v w} X).hom =
      (zeroIso.{u, v, w} X).hom := by
  rw [Iso.inv_comp_eq, universeCast_hom_comp_zeroIso_hom]

/-- The inverse of `zeroIso` followed by `universeCast` is the inverse of `zeroIso`. -/
@[reassoc (attr := simp)]
theorem zeroIso_inv_comp_universeCast_hom (X : TopRep.{max v w} R G) :
    (zeroIso.{u, v, max v w} X).inv ≫ (universeCast.{w} X 0).hom =
      (zeroIso.{u, v, w} X).inv := by
  rw [Iso.inv_comp_eq, ← universeCast_hom_comp_zeroIso_hom, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The inverse of `zeroIso` followed by the inverse of `universeCast` is the inverse of
`zeroIso`. -/
@[reassoc (attr := simp)]
theorem zeroIso_inv_comp_universeCast_inv (X : TopRep.{max v w} R G) :
    (zeroIso.{u, v, w} X).inv ≫ (universeCast.{w} X 0).inv =
      (zeroIso.{u, v, max v w} X).inv := by
  rw [Iso.comp_inv_eq, zeroIso_inv_comp_universeCast_hom]

/-- `universeCast` preserves the degree-zero class of every invariant vector. -/
@[simp]
theorem universeCast_hom_degreeZeroClass (X : TopRep.{max v w} R G) (x : X.V)
    (hx : ∀ g : G, X.ρ g x = x) :
    (universeCast.{w} X 0).hom (degreeZeroClass.{u, v, max v w} X x hx) =
      degreeZeroClass.{u, v, w} X x hx := by
  rw [← (zeroIso.{u, v, w} X).hom_inv_id_apply
      ((universeCast.{w} X 0).hom (degreeZeroClass.{u, v, max v w} X x hx)),
    ← (zeroIso.{u, v, w} X).hom_inv_id_apply (degreeZeroClass.{u, v, w} X x hx)]
  congr 1
  apply Subtype.ext
  have h := ConcreteCategory.congr_hom (universeCast_hom_comp_zeroIso_hom.{w} X)
    (degreeZeroClass.{u, v, max v w} X x hx)
  simp only [ConcreteCategory.comp_apply] at h
  rw [h, coe_zeroIso_hom_degreeZeroClass, coe_zeroIso_hom_degreeZeroClass]

/-- The inverse of `universeCast` preserves the degree-zero class of every invariant vector. -/
@[simp]
theorem universeCast_inv_degreeZeroClass (X : TopRep.{max v w} R G) (x : X.V)
    (hx : ∀ g : G, X.ρ g x = x) :
    (universeCast.{w} X 0).inv (degreeZeroClass.{u, v, w} X x hx) =
      degreeZeroClass.{u, v, max v w} X x hx := by
  rw [← universeCast_hom_degreeZeroClass.{w} X x hx, Iso.hom_inv_id_apply]

/-! ### Compatibility with functoriality -/

/-- Every degree of `ContinuousCohomology.resolutionMap` is heterogeneously independent of the extra
universe parameter `w`. -/
theorem resolutionMap_max_universe_heq (φ : H →ₜ* G)
    {X : TopRep.{max v w} R G} {Y : TopRep.{max v w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.resolutionMap.{u, v, max v w} φ f n ≍
      _root_.ContinuousCohomology.resolutionMap.{u, v, w} φ f n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [_root_.ContinuousCohomology.resolutionMap_succ]
    exact congr_arg_heq
      (fun p : Σ AB : TopRep.{max v w} R G × TopRep.{max v w} R H,
          TopRep.res (φ : H →* G) AB.1 ⟶ AB.2 ↦
        ofHom (ContRepresentation.coind₁ResMap φ p.2.hom))
      (Sigma.ext (Prod.ext (X.resolutionX_max_universe_eq.{w} n)
        (Y.resolutionX_max_universe_eq.{w} n)) ih : ⟨(_, _), _⟩ = ⟨(_, _), _⟩)

/-- For `X : TopRep.{v} R G` and `Y : TopRep.{v} R H`, `ContinuousCohomology.resolutionMap` at extra
universe `v` is heterogeneously equal to that at extra universe `0`. -/
theorem resolutionMap_universe_heq (φ : H →ₜ* G)
    {X : TopRep.{v} R G} {Y : TopRep.{v} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.resolutionMap.{u, v, v} φ f n ≍
      _root_.ContinuousCohomology.resolutionMap.{u, v, 0} φ f n :=
  resolutionMap_max_universe_heq.{0} φ f n

/-- The compatible-pair chain map `ContinuousCohomology.cochainsMap` is heterogeneously independent
of the extra universe parameter `w`. -/
theorem cochainsMap_max_universe_heq (φ : H →ₜ* G)
    {X : TopRep.{max v w} R G} {Y : TopRep.{max v w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) :
    _root_.ContinuousCohomology.cochainsMap.{u, v, max v w} φ f ≍
      _root_.ContinuousCohomology.cochainsMap.{u, v, w} φ f := by
  rw [← conj_eqToHom_iff_heq _ _ (X.homogeneousCochains_max_universe_eq.{w})
    (Y.homogeneousCochains_max_universe_eq.{w})]
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ?_
  simp only [HomologicalComplex.comp_f, HomologicalComplex.eqToHom_f,
    _root_.ContinuousCohomology.cochainsMap_f]
  exact (conj_eqToHom_iff_heq' _ _ _ _).2 <| by
    grind [X.resolutionX_max_universe_eq.{w} (n + 1),
      Y.resolutionX_max_universe_eq.{w} (n + 1),
      resolutionMap_max_universe_heq.{w} φ f (n + 1)]

/-- For `X : TopRep.{v} R G` and `Y : TopRep.{v} R H`, `ContinuousCohomology.cochainsMap` at extra
universe `v` is heterogeneously equal to that at extra universe `0`. -/
theorem cochainsMap_universe_heq (φ : H →ₜ* G)
    {X : TopRep.{v} R G} {Y : TopRep.{v} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) :
    _root_.ContinuousCohomology.cochainsMap.{u, v, v} φ f ≍
      _root_.ContinuousCohomology.cochainsMap.{u, v, 0} φ f :=
  cochainsMap_max_universe_heq.{0} φ f

/-- `homogeneousCochainsUniverseCast` commutes with compatible-pair maps on homogeneous cochains. -/
@[reassoc]
theorem cochainsMap_comp_homogeneousCochainsUniverseCast_hom (φ : H →ₜ* G)
    {X : TopRep.{max v w} R G} {Y : TopRep.{max v w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) :
    _root_.ContinuousCohomology.cochainsMap.{u, v, max v w} φ f ≫
        (Y.homogeneousCochainsUniverseCast.{w}).hom =
      (X.homogeneousCochainsUniverseCast.{w}).hom ≫
        _root_.ContinuousCohomology.cochainsMap.{u, v, w} φ f := by
  rw [homogeneousCochainsUniverseCast_eq_eqToIso, homogeneousCochainsUniverseCast_eq_eqToIso,
    eqToIso.hom, eqToIso.hom, comp_eqToHom_iff, Category.assoc]
  exact (conj_eqToHom_iff_heq' _ _ _ _).2 (cochainsMap_max_universe_heq.{w} φ f)

/-- The inverse of `homogeneousCochainsUniverseCast` commutes with compatible-pair maps on
homogeneous cochains. -/
@[reassoc]
theorem cochainsMap_comp_homogeneousCochainsUniverseCast_inv (φ : H →ₜ* G)
    {X : TopRep.{max v w} R G} {Y : TopRep.{max v w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) :
    _root_.ContinuousCohomology.cochainsMap.{u, v, w} φ f ≫
        (Y.homogeneousCochainsUniverseCast.{w}).inv =
      (X.homogeneousCochainsUniverseCast.{w}).inv ≫
        _root_.ContinuousCohomology.cochainsMap.{u, v, max v w} φ f := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
    cochainsMap_comp_homogeneousCochainsUniverseCast_hom]

/-- `cocyclesUniverseCast` commutes with compatible-pair maps on cocycles. -/
@[reassoc]
theorem cocyclesMap_comp_cocyclesUniverseCast_hom (φ : H →ₜ* G)
    {X : TopRep.{max v w} R G} {Y : TopRep.{max v w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    cocyclesMap.{u, v, max v w} φ f n ≫ (cocyclesUniverseCast.{w} Y n).hom =
      (cocyclesUniverseCast.{w} X n).hom ≫ cocyclesMap.{u, v, w} φ f n := by
  simp only [cocyclesMap, cocyclesUniverseCast, Functor.mapIso_hom,
    HomologicalComplex.cyclesFunctor_map, ← HomologicalComplex.cyclesMap_comp,
    cochainsMap_comp_homogeneousCochainsUniverseCast_hom]

/-- The inverse of `cocyclesUniverseCast` commutes with compatible-pair maps on cocycles. -/
@[reassoc]
theorem cocyclesMap_comp_cocyclesUniverseCast_inv (φ : H →ₜ* G)
    {X : TopRep.{max v w} R G} {Y : TopRep.{max v w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    cocyclesMap.{u, v, w} φ f n ≫ (cocyclesUniverseCast.{w} Y n).inv =
      (cocyclesUniverseCast.{w} X n).inv ≫ cocyclesMap.{u, v, max v w} φ f n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, cocyclesMap_comp_cocyclesUniverseCast_hom]

/-- **Compatible-pair functoriality commutes with `universeCast`.** -/
@[reassoc]
theorem map_comp_universeCast_hom (φ : H →ₜ* G)
    {X : TopRep.{max v w} R G} {Y : TopRep.{max v w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.map.{u, v, max v w} φ f n ≫ (universeCast.{w} Y n).hom =
      (universeCast.{w} X n).hom ≫ _root_.ContinuousCohomology.map.{u, v, w} φ f n := by
  simp only [_root_.ContinuousCohomology.map, universeCast, Functor.mapIso_hom,
    HomologicalComplex.homologyFunctor_map, ← HomologicalComplex.homologyMap_comp,
    cochainsMap_comp_homogeneousCochainsUniverseCast_hom]

/-- Compatible-pair functoriality commutes with the inverse of `universeCast`. -/
@[reassoc]
theorem map_comp_universeCast_inv (φ : H →ₜ* G)
    {X : TopRep.{max v w} R G} {Y : TopRep.{max v w} R H}
    (f : TopRep.res (φ : H →* G) X ⟶ Y) (n : ℕ) :
    _root_.ContinuousCohomology.map.{u, v, w} φ f n ≫ (universeCast.{w} Y n).inv =
      (universeCast.{w} X n).inv ≫ _root_.ContinuousCohomology.map.{u, v, max v w} φ f n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, map_comp_universeCast_hom]

/-- Coefficient maps commute with `universeCast`. -/
@[reassoc]
theorem coeffMap_comp_universeCast_hom {X Y : TopRep.{max v w} R G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap.{u, v, max v w} f n ≫ (universeCast.{w} Y n).hom =
      (universeCast.{w} X n).hom ≫ coeffMap.{u, v, w} f n := by
  rw [coeffMap_def, coeffMap_def]
  exact map_comp_universeCast_hom.{w} (ContinuousMonoidHom.id G) f n

/-- Coefficient maps commute with the inverse of `universeCast`. -/
@[reassoc]
theorem coeffMap_comp_universeCast_inv {X Y : TopRep.{max v w} R G} (f : X ⟶ Y) (n : ℕ) :
    coeffMap.{u, v, w} f n ≫ (universeCast.{w} Y n).inv =
      (universeCast.{w} X n).inv ≫ coeffMap.{u, v, max v w} f n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, coeffMap_comp_universeCast_hom]

/-- Restriction commutes with `universeCast`. -/
@[reassoc]
theorem res_comp_universeCast_hom (S : Subgroup G) (X : TopRep.{max v w} R G) (n : ℕ) :
    res.{u, v, max v w} S X n ≫ (universeCast.{w} (TopRep.res (S.subtype : S →* G) X) n).hom =
      (universeCast.{w} X n).hom ≫ res.{u, v, w} S X n := by
  rw [res_def, res_def]
  exact map_comp_universeCast_hom.{w} (ContinuousMonoidHom.subgroupSubtype S)
    (𝟙 (TopRep.res (S.subtype : S →* G) X)) n

/-- Restriction commutes with the inverse of `universeCast`. -/
@[reassoc]
theorem res_comp_universeCast_inv (S : Subgroup G) (X : TopRep.{max v w} R G) (n : ℕ) :
    res.{u, v, w} S X n ≫ (universeCast.{w} (TopRep.res (S.subtype : S →* G) X) n).inv =
      (universeCast.{w} X n).inv ≫ res.{u, v, max v w} S X n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, res_comp_universeCast_hom]

/-- Inflation commutes with `universeCast`. -/
@[reassoc]
theorem infl_comp_universeCast_hom (N : Subgroup G) [N.Normal] (X : TopRep.{max v w} R G) (n : ℕ) :
    infl.{u, v, max v w} N X n ≫ (universeCast.{w} X n).hom =
      (universeCast.{w} (TopRep.quotientToInvariants X N) n).hom ≫ infl.{u, v, w} N X n := by
  rw [infl_def, infl_def]
  exact map_comp_universeCast_hom.{w} (Subgroup.quotientMkContinuousMonoidHom N) _ n

/-- Inflation commutes with the inverse of `universeCast`. -/
@[reassoc]
theorem infl_comp_universeCast_inv (N : Subgroup G) [N.Normal] (X : TopRep.{max v w} R G) (n : ℕ) :
    infl.{u, v, w} N X n ≫ (universeCast.{w} X n).inv =
      (universeCast.{w} (TopRep.quotientToInvariants X N) n).inv ≫ infl.{u, v, max v w} N X n := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, infl_comp_universeCast_hom]

variable (R G) in
/-- Natural isomorphism between `continuousCohomologyFunctor` at extra universe parameters
`max v w` and `w`. -/
noncomputable def continuousCohomologyFunctorUniverseCast (n : ℕ) :
    continuousCohomologyFunctor.{u, v, max v w} R G n ≅
      continuousCohomologyFunctor.{u, v, w} R G n :=
  NatIso.ofComponents (fun X ↦ universeCast.{w} X n)
    (fun f ↦ coeffMap_comp_universeCast_hom.{w} f n)

/-- The forward components of `continuousCohomologyFunctorUniverseCast` are
`(universeCast X n).hom`. -/
@[simp]
theorem continuousCohomologyFunctorUniverseCast_hom_app (X : TopRep.{max v w} R G) (n : ℕ) :
    (continuousCohomologyFunctorUniverseCast.{w} R G n).hom.app X = (universeCast.{w} X n).hom :=
  (rfl)

/-- The inverse components of `continuousCohomologyFunctorUniverseCast` are
`(universeCast X n).inv`. -/
@[simp]
theorem continuousCohomologyFunctorUniverseCast_inv_app (X : TopRep.{max v w} R G) (n : ℕ) :
    (continuousCohomologyFunctorUniverseCast.{w} R G n).inv.app X = (universeCast.{w} X n).inv :=
  (rfl)

/-- Triviality of `continuousCohomology n X` is independent of the extra universe parameter `w`. -/
theorem subsingleton_continuousCohomology_max_universe_iff (X : TopRep.{max v w} R G) (n : ℕ) :
    Subsingleton (continuousCohomology.{u, v, max v w} n X) ↔
      Subsingleton (continuousCohomology.{u, v, w} n X) :=
  (universeCast.{w} X n).toContinuousLinearEquiv.toEquiv.subsingleton_congr

/-- For `X : TopRep.{v} R G`, triviality of `continuousCohomology n X` at extra universe `v` is
equivalent to triviality at extra universe `0`. -/
theorem subsingleton_continuousCohomology_universe_iff (X : TopRep.{v} R G) (n : ℕ) :
    Subsingleton (continuousCohomology.{u, v, v} n X) ↔
      Subsingleton (continuousCohomology.{u, v, 0} n X) :=
  subsingleton_continuousCohomology_max_universe_iff.{0} X n

/-- Vanishing of the `p`-primary component of `continuousCohomology n X` is independent of the
extra universe parameter `w`. -/
theorem primaryComponent_continuousCohomology_eq_bot_max_universe_iff
    (X : TopRep.{max v w} R G) (p n : ℕ) :
    AddCommGroup.primaryComponent (continuousCohomology.{u, v, max v w} n X) p = ⊥ ↔
      AddCommGroup.primaryComponent (continuousCohomology.{u, v, w} n X) p = ⊥ := by
  rw [continuousCohomology_max_universe_eq.{w} X n]

/-- For `X : TopRep.{v} R G`, vanishing of the `p`-primary component of `continuousCohomology n X`
at extra universe `v` is equivalent to vanishing at extra universe `0`. -/
theorem primaryComponent_continuousCohomology_eq_bot_universe_iff
    (X : TopRep.{v} R G) (p n : ℕ) :
    AddCommGroup.primaryComponent (continuousCohomology.{u, v, v} n X) p = ⊥ ↔
      AddCommGroup.primaryComponent (continuousCohomology.{u, v, 0} n X) p = ⊥ :=
  primaryComponent_continuousCohomology_eq_bot_max_universe_iff.{0} X p n

end TauCeti.ContinuousCohomology
