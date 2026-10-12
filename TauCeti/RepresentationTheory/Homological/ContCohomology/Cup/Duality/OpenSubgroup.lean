/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.InternalHom
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Shapiro
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ProjectionFormula

import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Restriction

/-!
# The evaluation pairings and an open subgroup: restriction, corestriction and Shapiro

Let `U` be an open subgroup of finite index of a topological group `G`, let `M` be a finite discrete
`G`-module and `N` a discrete `G`-module. The evaluation pairings
`⟨-, -⟩_G : Hⁱ(G, Hom(M, N)) × H²⁻ⁱ(G, M) → H²(G, N)` of
`TauCeti/RepresentationTheory/Homological/ContCohomology/Cup/Duality/Basic.lean` are compatible
with the change of group to `U` in three ways.

* **Restriction preserves them**: `res ⟨φ, b⟩_G = ⟨res φ, res b⟩_U`. The restriction of a class of
  `Hⁱ(G, InternalHom G M N)` is a class of `Hⁱ(U, InternalHom G M N)`, the internal hom of the
  `G`-modules with the restricted action; `TauCeti.InternalHom.restrict` identifies that module with
  the internal hom `InternalHom U M N` of the `U`-modules, and on it the `U`-pairing is the cup
  along the evaluation pairing of `G` (`explicitDualityPairing02_explicitCoeff0_restrict` and its
  two companions).
* **Restriction and corestriction are adjoint**: `cor ⟨res φ, b⟩_U = ⟨φ, cor b⟩_G`, the projection
  formula for the evaluation pairings. A class of `U` paired against a restricted class of `G` is
  detected, after corestriction, by the pairing of `G`; this is the identity through which the
  duality of an open subgroup is compared with that of the ambient group.
* **Shapiro's lemma transports them**: for a discrete `U`-module `A` and `G` profinite, the dual of
  the coinduced module `Coind_U^G A` is again coinduced,
  `Hom(Coind_U^G A, N) ≅ Coind_U^G Hom(A, N)` through `TauCeti.DiscreteCoind.toInternalHom` (a
  bijection when the conjugation action of `U` on `Hom(A, N)` is continuous, as it is for a finite
  `A`), and Shapiro's lemma identifies the cohomology of both coinduced modules with that of `U`.
  Under these identifications the `(1,1)` evaluation pairing of `G` is the corestriction of the
  evaluation pairing of `U`:

  ```text
  ⟨toInternalHom F, x⟩_G = cor_U^G ⟨sh F, sh x⟩_U.
  ```

  This is the identity through which a duality statement for the finite modules of `G` is read
  on the open subgroup `U`: a class of `H¹(U, A)` is detected by the pairing of `U` as soon as its
  inverse Shapiro image is detected by the pairing of `G`. The same identity holds in the `(0,2)`
  shape, and there it says that injectivity of Tate's duality map `α₂` descends from `G` to `U`:
  if `α₂` of `G` is injective on the coinduced module `Coind_U^G A`, then `α₂` of `U` is injective
  on `A`, for every discrete `U`-module `A` whose internal hom `Hom(A, N)` carries a continuous
  conjugation action.

The first two are the specializations to the evaluation pairing of the general statements for the
explicit cup products, compatibility with restriction from
`TauCeti/RepresentationTheory/Homological/ContCohomology/Cup/Restriction.lean` and the projection
formula from `TauCeti/RepresentationTheory/Homological/ContCohomology/ProjectionFormula.lean`,
through the naturality of the cup product in the pairing. In the `(2,0)` shape the restricted class
is the degree-two one, so the projection formula used is the one with restriction on the cocycle
factor, `TauCeti.ContCohomology.explicitCup_projection20_res_left`. For the third, the evaluation
pairing of `G` on the coinduced modules is the trace of the pointwise evaluation pairing
(`TauCeti.DiscreteCoind.toAddMonoidHom_toInternalHom_apply`), the cup product is natural in the
pairing, and the corestriction of a cup product of `U` is the trace of the cup product of `G`
along the pointwise pairing of the inverse Shapiro images
(`TauCeti.ContCohomology.explicitCor2_explicitCup02` in the `(0,2)` shape and
`explicitCor2_explicitCup11` in the `(1,1)` shape).

## Main statements

* `TauCeti.ContCohomology.explicitDualityPairing02_explicitCoeff0_restrict`,
  `explicitDualityPairing11_explicitCoeff1_restrict` and
  `explicitDualityPairing20_explicitCoeff2_restrict`: on the restricted internal hom, the
  evaluation pairing of the `U`-modules is the cup along the evaluation pairing of `G`.
* `TauCeti.ContCohomology.explicitRes2_explicitDualityPairing02`,
  `explicitRes2_explicitDualityPairing11` and `explicitRes2_explicitDualityPairing20`:
  **restriction preserves the evaluation pairings.**
* `TauCeti.ContCohomology.explicitDualityPairing02_projection`,
  `explicitDualityPairing11_projection` and `explicitDualityPairing20_projection`:
  **the projection formula** `cor ⟨res φ, b⟩_U = ⟨φ, cor b⟩_G` for the evaluation pairings.
* `TauCeti.ContCohomology.explicitDualityPairing11_explicitCoeff1_toInternalHom` and
  `explicitDualityPairing02_explicitCoeff0_toInternalHom` and
  `explicitDualityPairing20_explicitCoeff2_toInternalHom`: **the evaluation pairing of a
  coinduced module** is the corestriction of the corresponding evaluation pairing of `U` on the
  Shapiro images.
* `TauCeti.ContCohomology.dualityMap0_bijective_discreteCoind_of_bijective`,
  `dualityMap1_bijective_discreteCoind_of_bijective` and
  `dualityMap2_bijective_discreteCoind_of_bijective`: **perfect duality is transported by
  Shapiro's lemma** from an open subgroup to a coinduced module, when corestriction on the target
  is bijective.
* `TauCeti.ContCohomology.dualityMap2_injective_of_injective_discreteCoind`: **injectivity of
  Tate's duality map `α₂` descends to an open subgroup**: if `α₂` of `G` is injective on
  `Coind_U^G A`, then `α₂` of `U` is injective on `A`.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9: the duality of an open subgroup of a Demushkin group is compared
  with that of the group through restriction and corestriction, and §9.2: the cohomology of the
  open subgroup is read through the coinduced module.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.3)(i) and
  (iv): compatibility of the cup product with restriction, and the projection formula.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM uN uA

section ZeroTwo

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (U : Subgroup G)

/-- Multiplication on the subgroup `U` is continuous for the subspace topology. -/
local instance : ContinuousMul U := U.toSubmonoid.continuousMul

/-- On the restricted internal hom, the `(0,2)` evaluation pairing of the `U`-modules is the
explicit `(0,2)` cup along the evaluation pairing of `G`. -/
theorem explicitDualityPairing02_explicitCoeff0_restrict (a : H0 U (InternalHom G M N))
    (b : H2 U M) :
    explicitDualityPairing02 U M N
        (explicitCoeff0 U (InternalHom G M N) (InternalHom.restrict U) a) b =
      explicitCup02 U (InternalHom G M N) M N (InternalHom.evalPairing G)
        continuous_of_discreteTopology
        (fun u φ m => InternalHom.evalPairing_equivariant (u : G) φ m) a b := by
  have h := explicitCoeff2_explicitCup02 U (InternalHom G M N) M N (InternalHom U M N) M N
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (fun u φ m => InternalHom.evalPairing_equivariant (u : G) φ m) (InternalHom.evalPairing U)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := U))
    (InternalHom.restrict U) (DistribMulActionHom.id U) (DistribMulActionHom.id U)
    continuous_id continuous_id (fun φ m => (InternalHom.evalPairing_restrict U φ m).symm) a b
  simp only [explicitCoeff2_id, AddMonoidHom.id_apply] at h
  rw [explicitDualityPairing02_def, ← h]

/-- **Restriction preserves the `(0,2)` evaluation pairing**: `res ⟨φ, b⟩_G = ⟨res φ, res b⟩_U`,
where the restricted invariant is read in the internal hom of the `U`-modules through
`TauCeti.InternalHom.restrict`. -/
@[simp]
theorem explicitRes2_explicitDualityPairing02 (a : H0 G (InternalHom G M N)) (b : H2 G M) :
    explicitRes2 G N U (explicitDualityPairing02 G M N a b) =
      explicitDualityPairing02 U M N
        (explicitCoeff0 U (InternalHom G M N) (InternalHom.restrict U)
          (explicitRes0 G (InternalHom G M N) U a))
        (explicitRes2 G M U b) := by
  rw [explicitDualityPairing02_explicitCoeff0_restrict, explicitDualityPairing02_def,
    explicitRes2_explicitCup02]

end ZeroTwo

section ZeroTwoProjection

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))

/-- **The projection formula for the `(0,2)` evaluation pairing**,
`cor² ⟨res⁰ φ, b⟩_U = ⟨φ, cor² b⟩_G`, for an open subgroup `U` of finite index. -/
theorem explicitDualityPairing02_projection (a : H0 G (InternalHom G M N)) (b : H2 U M) :
    explicitCor2 G N U hU
        (explicitDualityPairing02 U M N
          (explicitCoeff0 U (InternalHom G M N) (InternalHom.restrict U)
            (explicitRes0 G (InternalHom G M N) U a)) b) =
      explicitDualityPairing02 G M N a (explicitCor2 G M U hU b) := by
  rw [explicitDualityPairing02_explicitCoeff0_restrict, explicitDualityPairing02_def]
  exact explicitCup_projection02 G (InternalHom G M N) M N U hU (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b

end ZeroTwoProjection

section OneOneAndTwoZero

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction G M] [ContinuousSMul G M] [Finite M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (U : Subgroup G)

/-- On the restricted internal hom, the `(1,1)` evaluation pairing of the `U`-modules is the
explicit `(1,1)` cup along the evaluation pairing of `G`. -/
theorem explicitDualityPairing11_explicitCoeff1_restrict (a : H1 U (InternalHom G M N))
    (b : H1 U M) :
    explicitDualityPairing11 U M N
        (explicitCoeff1 U (InternalHom G M N) (InternalHom.restrict U)
          continuous_of_discreteTopology a) b =
      explicitCup11 U (InternalHom G M N) M N (InternalHom.evalPairing G)
        continuous_of_discreteTopology
        (fun u φ m => InternalHom.evalPairing_equivariant (u : G) φ m) a b := by
  have h := explicitCoeff2_explicitCup11 U (InternalHom G M N) M N (InternalHom U M N) M N
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (fun u φ m => InternalHom.evalPairing_equivariant (u : G) φ m) (InternalHom.evalPairing U)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := U))
    (InternalHom.restrict U) (DistribMulActionHom.id U) (DistribMulActionHom.id U)
    continuous_of_discreteTopology continuous_id continuous_id
    (fun φ m => (InternalHom.evalPairing_restrict U φ m).symm) a b
  simp only [explicitCoeff2_id, explicitCoeff1_id, AddMonoidHom.id_apply] at h
  rw [explicitDualityPairing11_def, ← h]

/-- On the restricted internal hom, the `(2,0)` evaluation pairing of the `U`-modules is the
explicit `(2,0)` cup along the evaluation pairing of `G`. -/
theorem explicitDualityPairing20_explicitCoeff2_restrict (a : H2 U (InternalHom G M N))
    (b : H0 U M) :
    explicitDualityPairing20 U M N
        (explicitCoeff2 U (InternalHom G M N) (InternalHom.restrict U)
          continuous_of_discreteTopology a) b =
      explicitCup20 U (InternalHom G M N) M N (InternalHom.evalPairing G)
        continuous_of_discreteTopology
        (fun u φ m => InternalHom.evalPairing_equivariant (u : G) φ m) a b := by
  have h := explicitCoeff2_explicitCup20 U (InternalHom G M N) M N (InternalHom U M N) M N
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (fun u φ m => InternalHom.evalPairing_equivariant (u : G) φ m) (InternalHom.evalPairing U)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := U))
    (InternalHom.restrict U) (DistribMulActionHom.id U) (DistribMulActionHom.id U)
    continuous_of_discreteTopology continuous_id
    (fun φ m => (InternalHom.evalPairing_restrict U φ m).symm) a b
  have hb : explicitCoeff0 U M (DistribMulActionHom.id U) b = b :=
    Subtype.ext (coe_explicitCoeff0 U M _ b)
  simp only [explicitCoeff2_id, AddMonoidHom.id_apply, hb] at h
  rw [explicitDualityPairing20_def, ← h]

/-- **Restriction preserves the `(1,1)` evaluation pairing**: `res ⟨φ, b⟩_G = ⟨res φ, res b⟩_U`,
where the restricted class is read in the internal hom of the `U`-modules through
`TauCeti.InternalHom.restrict`. -/
@[simp]
theorem explicitRes2_explicitDualityPairing11 (a : H1 G (InternalHom G M N)) (b : H1 G M) :
    explicitRes2 G N U (explicitDualityPairing11 G M N a b) =
      explicitDualityPairing11 U M N
        (explicitCoeff1 U (InternalHom G M N) (InternalHom.restrict U)
          continuous_of_discreteTopology (explicitRes1 G (InternalHom G M N) U a))
        (explicitRes1 G M U b) := by
  rw [explicitDualityPairing11_explicitCoeff1_restrict, explicitDualityPairing11_def,
    explicitRes2_explicitCup11]

/-- **Restriction preserves the `(2,0)` evaluation pairing**: `res ⟨φ, b⟩_G = ⟨res φ, res b⟩_U`,
where the restricted class is read in the internal hom of the `U`-modules through
`TauCeti.InternalHom.restrict`. -/
@[simp]
theorem explicitRes2_explicitDualityPairing20 (a : H2 G (InternalHom G M N)) (b : H0 G M) :
    explicitRes2 G N U (explicitDualityPairing20 G M N a b) =
      explicitDualityPairing20 U M N
        (explicitCoeff2 U (InternalHom G M N) (InternalHom.restrict U)
          continuous_of_discreteTopology (explicitRes2 G (InternalHom G M N) U a))
        (explicitRes0 G M U b) := by
  rw [explicitDualityPairing20_explicitCoeff2_restrict, explicitDualityPairing20_def,
    explicitRes2_explicitCup20]

variable [U.FiniteIndex] (hU : IsOpen (U : Set G))

/-- **The projection formula for the `(1,1)` evaluation pairing**,
`cor² ⟨res¹ φ, b⟩_U = ⟨φ, cor¹ b⟩_G`, for an open subgroup `U` of finite index. -/
theorem explicitDualityPairing11_projection (a : H1 G (InternalHom G M N)) (b : H1 U M) :
    explicitCor2 G N U hU
        (explicitDualityPairing11 U M N
          (explicitCoeff1 U (InternalHom G M N) (InternalHom.restrict U)
            continuous_of_discreteTopology (explicitRes1 G (InternalHom G M N) U a)) b) =
      explicitDualityPairing11 G M N a (explicitCor1 G M U hU b) := by
  rw [explicitDualityPairing11_explicitCoeff1_restrict, explicitDualityPairing11_def]
  exact explicitCup_projection11 G (InternalHom G M N) M N U hU (InternalHom.evalPairing G)
    continuous_of_discreteTopology (InternalHom.evalPairing_equivariant (G := G)) a b

/-- **The projection formula for the `(2,0)` evaluation pairing**,
`cor² ⟨res² φ, b⟩_U = ⟨φ, cor⁰ b⟩_G`, for an open subgroup `U` of finite index. Here the restricted
class is the degree-two one, so this is the instance of the projection formula with restriction on
the cocycle factor, `TauCeti.ContCohomology.explicitCup_projection20_res_left`. -/
theorem explicitDualityPairing20_projection (a : H2 G (InternalHom G M N)) (b : H0 U M) :
    explicitCor2 G N U hU
        (explicitDualityPairing20 U M N
          (explicitCoeff2 U (InternalHom G M N) (InternalHom.restrict U)
            continuous_of_discreteTopology (explicitRes2 G (InternalHom G M N) U a)) b) =
      explicitDualityPairing20 G M N a (explicitCor0 G M U b) := by
  rw [explicitDualityPairing20_explicitCoeff2_restrict, explicitDualityPairing20_def]
  exact explicitCup_projection20_res_left G (InternalHom G M N) M N U hU
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) a b

end OneOneAndTwoZero

section TracePairing

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G] (U : Subgroup G)
  [U.FiniteIndex] (A : Type uA) [AddCommGroup A] [DistribMulAction U A]
  (N : Type uN) [AddCommGroup N] [DistribMulAction G N]

/-- The pairing `(F, f) ↦ tr (g ↦ F g (f g))` of the coinduced modules `Coind_U^G Hom(A, N)` and
`Coind_U^G A`, with values in `N`: the evaluation pairing of `G` read through
`TauCeti.DiscreteCoind.toInternalHom`. It is the trace of the pointwise evaluation pairing
(`tracePairing_apply`), which is what lets the naturality of the cup product in the pairing compare
the two sides of the Shapiro identities below. -/
private noncomputable def tracePairing :
    DiscreteCoind G U (InternalHom U A N) →+ DiscreteCoind G U A →+ N :=
  (InternalHom.evalPairing G).comp (DiscreteCoind.toInternalHom U A N).toAddMonoidHom

private theorem tracePairing_eq_evalPairing_toInternalHom
    (F : DiscreteCoind G U (InternalHom U A N)) (f : DiscreteCoind G U A) :
    tracePairing G U A N F f =
      InternalHom.evalPairing G (DiscreteCoind.toInternalHom U A N F) f :=
  rfl

private theorem tracePairing_apply (F : DiscreteCoind G U (InternalHom U A N))
    (f : DiscreteCoind G U A) :
    tracePairing G U A N F f = DiscreteCoind.trace G U N
      (DiscreteCoind.pointwisePairing U (InternalHom.evalPairing U)
        (InternalHom.evalPairing_equivariant (G := U)) F f) := by
  rw [tracePairing_eq_evalPairing_toInternalHom, InternalHom.evalPairing_apply,
    DiscreteCoind.toAddMonoidHom_toInternalHom_apply]

private theorem tracePairing_smul (g : G) (F : DiscreteCoind G U (InternalHom U A N))
    (f : DiscreteCoind G U A) :
    tracePairing G U A N (g • F) (g • f) = g • tracePairing G U A N F f := by
  rw [tracePairing_eq_evalPairing_toInternalHom,
    _root_.map_smul (DiscreteCoind.toInternalHom U A N) g F, InternalHom.evalPairing_equivariant,
    tracePairing_eq_evalPairing_toInternalHom]

end TracePairing

section Shapiro

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
  (A : Type uA) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction U A] [ContinuousSMul U A] [Finite A]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction G N] [ContinuousSMul G N]

/-- **The evaluation pairing of a coinduced module is the corestriction of the evaluation pairing
of the subgroup.** For an open subgroup `U` of finite index of a profinite group `G`, a finite
discrete `U`-module `A` and a discrete `G`-module `N`, a class `F` of
`H¹(G, Coind_U^G Hom(A, N))`, read in `H¹(G, Hom(Coind_U^G A, N))` through
`TauCeti.DiscreteCoind.toInternalHom`, pairs with a class `x` of `H¹(G, Coind_U^G A)` to the
corestriction of the evaluation pairing of `U` of the Shapiro images of `F` and `x`:
`⟨toInternalHom F, x⟩_G = cor_U^G ⟨sh F, sh x⟩_U`. -/
theorem explicitDualityPairing11_explicitCoeff1_toInternalHom
    (F : H1 G (DiscreteCoind G U (InternalHom U A N))) (x : H1 G (DiscreteCoind G U A)) :
    explicitDualityPairing11 G (DiscreteCoind G U A) N
        (explicitCoeff1 G (DiscreteCoind G U (InternalHom U A N))
          (DiscreteCoind.toInternalHom U A N) continuous_of_discreteTopology F) x =
      explicitCor2 G N U hU
        (explicitDualityPairing11 U A N
          (explicitShapiro1 G U (InternalHom U A N) (U.isClosed_of_isOpen hU) F)
          (explicitShapiro1 G U A (U.isClosed_of_isOpen hU) x)) := by
  rw [explicitDualityPairing11_def, explicitDualityPairing11_def, explicitCor2_explicitCup11,
    AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  -- Both sides are the `(1,1)` cup along the trace pairing of the coinduced modules, by naturality
  -- of the cup product in the pairing: the left one through `toInternalHom`, the right one through
  -- the trace.
  have h₁ := explicitCoeff2_explicitCup11 G (DiscreteCoind G U (InternalHom U A N))
    (DiscreteCoind G U A) N (InternalHom G (DiscreteCoind G U A) N) (DiscreteCoind G U A) N
    (tracePairing G U A N) continuous_of_discreteTopology (tracePairing_smul G U A N)
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (DiscreteCoind.toInternalHom U A N)
    (DistribMulActionHom.id G) (DistribMulActionHom.id G) continuous_of_discreteTopology
    continuous_id continuous_id (fun F' f ↦ by
      simp only [DistribMulActionHom.id_apply, tracePairing_eq_evalPairing_toInternalHom]) F x
  have h₂ := explicitCoeff2_explicitCup11 G (DiscreteCoind G U (InternalHom U A N))
    (DiscreteCoind G U A) (DiscreteCoind G U N) (DiscreteCoind G U (InternalHom U A N))
    (DiscreteCoind G U A) N
    (DiscreteCoind.pointwisePairing U (InternalHom.evalPairing U)
      (InternalHom.evalPairing_equivariant (G := U))) continuous_of_discreteTopology
    (fun g f f' ↦ DiscreteCoind.pointwisePairing_smul U (InternalHom.evalPairing U)
      (InternalHom.evalPairing_equivariant (G := U)) g f f') (tracePairing G U A N)
    continuous_of_discreteTopology (tracePairing_smul G U A N)
    (DistribMulActionHom.id G) (DistribMulActionHom.id G) (DiscreteCoind.trace G U N)
    continuous_id continuous_id DiscreteCoind.continuous_trace (fun F' f ↦ by
      simp only [DistribMulActionHom.id_apply, tracePairing_apply]) F x
  simp only [explicitCoeff2_id, explicitCoeff1_id, AddMonoidHom.id_apply] at h₁ h₂
  exact h₁.symm.trans h₂.symm

/-- **The `(2,0)` evaluation pairing of a coinduced module is the corestriction of the `(2,0)`
evaluation pairing of the subgroup**: a degree-two class with values in the coinduced internal
hom, read in `Hom(Coind_U^G A, N)` through `TauCeti.DiscreteCoind.toInternalHom`, pairs with an
invariant coinduced element to the corestriction of the pairing of their Shapiro images. -/
theorem explicitDualityPairing20_explicitCoeff2_toInternalHom
    (F : H2 G (DiscreteCoind G U (InternalHom U A N))) (x : H0 G (DiscreteCoind G U A)) :
    explicitDualityPairing20 G (DiscreteCoind G U A) N
        (explicitCoeff2 G (DiscreteCoind G U (InternalHom U A N))
          (DiscreteCoind.toInternalHom U A N) continuous_of_discreteTopology F) x =
      explicitCor2 G N U hU
        (explicitDualityPairing20 U A N
          (explicitShapiro2 G U (InternalHom U A N) (U.isClosed_of_isOpen hU) F)
          (explicitShapiro0 G U A x)) := by
  rw [explicitDualityPairing20_def, explicitDualityPairing20_def, explicitCor2_explicitCup20,
    AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  have h₁ := explicitCoeff2_explicitCup20 G (DiscreteCoind G U (InternalHom U A N))
    (DiscreteCoind G U A) N (InternalHom G (DiscreteCoind G U A) N)
    (DiscreteCoind G U A) N (tracePairing G U A N) continuous_of_discreteTopology
    (tracePairing_smul G U A N) (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (DiscreteCoind.toInternalHom U A N)
    (DistribMulActionHom.id G) (DistribMulActionHom.id G) continuous_of_discreteTopology
    continuous_id (fun F' f ↦ by
      simp only [DistribMulActionHom.id_apply, tracePairing_eq_evalPairing_toInternalHom]) F x
  have h₂ := explicitCoeff2_explicitCup20 G (DiscreteCoind G U (InternalHom U A N))
    (DiscreteCoind G U A) (DiscreteCoind G U N)
    (DiscreteCoind G U (InternalHom U A N)) (DiscreteCoind G U A) N
    (DiscreteCoind.pointwisePairing U (InternalHom.evalPairing U)
      (InternalHom.evalPairing_equivariant (G := U))) continuous_of_discreteTopology
    (fun g f f' ↦ DiscreteCoind.pointwisePairing_smul U (InternalHom.evalPairing U)
      (InternalHom.evalPairing_equivariant (G := U)) g f f') (tracePairing G U A N)
    continuous_of_discreteTopology (tracePairing_smul G U A N)
    (DistribMulActionHom.id G) (DistribMulActionHom.id G) (DiscreteCoind.trace G U N)
    continuous_id DiscreteCoind.continuous_trace (fun F' f ↦ by
      simp only [DistribMulActionHom.id_apply, tracePairing_apply]) F x
  simp only [explicitCoeff2_id, explicitCoeff0_id, AddMonoidHom.id_apply] at h₁ h₂
  exact h₁.symm.trans h₂.symm

omit [Finite A] in
/-- **The `(0,2)` evaluation pairing of a coinduced module is the corestriction of the `(0,2)`
evaluation pairing of the subgroup**: for an invariant `F` of `Coind_U^G Hom(A, N)`, read in
`Hom(Coind_U^G A, N)` through `TauCeti.DiscreteCoind.toInternalHom`, and a class `x` of
`H²(G, Coind_U^G A)`, `⟨toInternalHom F, x⟩_G = cor_U^G ⟨sh F, sh x⟩_U`. -/
theorem explicitDualityPairing02_explicitCoeff0_toInternalHom
    (F : H0 G (DiscreteCoind G U (InternalHom U A N))) (x : H2 G (DiscreteCoind G U A)) :
    explicitDualityPairing02 G (DiscreteCoind G U A) N
        (explicitCoeff0 G (DiscreteCoind G U (InternalHom U A N))
          (DiscreteCoind.toInternalHom U A N) F) x =
      explicitCor2 G N U hU
        (explicitDualityPairing02 U A N (explicitShapiro0 G U (InternalHom U A N) F)
          (explicitShapiro2 G U A (U.isClosed_of_isOpen hU) x)) := by
  rw [explicitDualityPairing02_def, explicitDualityPairing02_def, explicitCor2_explicitCup02,
    AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  -- As in the `(1,1)` shape, both sides are the `(0,2)` cup along the trace pairing.
  have h₁ := explicitCoeff2_explicitCup02 G (DiscreteCoind G U (InternalHom U A N))
    (DiscreteCoind G U A) N (InternalHom G (DiscreteCoind G U A) N) (DiscreteCoind G U A) N
    (tracePairing G U A N) continuous_of_discreteTopology (tracePairing_smul G U A N)
    (InternalHom.evalPairing G) continuous_of_discreteTopology
    (InternalHom.evalPairing_equivariant (G := G)) (DiscreteCoind.toInternalHom U A N)
    (DistribMulActionHom.id G) (DistribMulActionHom.id G) continuous_id continuous_id
    (fun F' f ↦ by
      simp only [DistribMulActionHom.id_apply, tracePairing_eq_evalPairing_toInternalHom]) F x
  have h₂ := explicitCoeff2_explicitCup02 G (DiscreteCoind G U (InternalHom U A N))
    (DiscreteCoind G U A) (DiscreteCoind G U N) (DiscreteCoind G U (InternalHom U A N))
    (DiscreteCoind G U A) N
    (DiscreteCoind.pointwisePairing U (InternalHom.evalPairing U)
      (InternalHom.evalPairing_equivariant (G := U))) continuous_of_discreteTopology
    (fun g f f' ↦ DiscreteCoind.pointwisePairing_smul U (InternalHom.evalPairing U)
      (InternalHom.evalPairing_equivariant (G := U)) g f f') (tracePairing G U A N)
    continuous_of_discreteTopology (tracePairing_smul G U A N)
    (DistribMulActionHom.id G) (DistribMulActionHom.id G) (DiscreteCoind.trace G U N)
    continuous_id DiscreteCoind.continuous_trace (fun F' f ↦ by
      simp only [DistribMulActionHom.id_apply, tracePairing_apply]) F x
  simp only [explicitCoeff2_id, explicitCoeff0_id, AddMonoidHom.id_apply] at h₁ h₂
  exact h₁.symm.trans h₂.symm

section Descent

omit [Finite A]
variable [ContinuousSMul U (InternalHom U A N)]
include hU

/-- **Injectivity of Tate's duality map `α₂` descends to an open subgroup.** If
`α₂ : H²(G, Coind_U^G A) → Hom(H⁰(G, Hom(Coind_U^G A, N)), H²(G, N))` is injective, then so is
`α₂ : H²(U, A) → Hom(H⁰(U, Hom(A, N)), H²(U, N))`: a class of `H²(U, A)` killed by every invariant
of `Hom(A, N)` has, by `explicitDualityPairing02_explicitCoeff0_toInternalHom`, an inverse Shapiro
image killed by every invariant of `Hom(Coind_U^G A, N)`, all of which are coinduced. The
continuity of the conjugation action of `U` on `Hom(A, N)`, automatic for a finite `A`, is what
makes `toInternalHom` surjective. -/
theorem dualityMap2_injective_of_injective_discreteCoind
    (h : Function.Injective (dualityMap2 G (DiscreteCoind G U A) N)) :
    Function.Injective (dualityMap2 U A N) := by
  have hUc : IsClosed (U : Set G) := U.isClosed_of_isOpen hU
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  rw [← (explicitShapiro2 G U A hUc).symm.map_eq_zero_iff]
  refine (injective_iff_map_eq_zero _).1 h _ (AddMonoidHom.ext fun Φ ↦ ?_)
  obtain ⟨F, rfl⟩ := (explicitCoeff0_bijective G _
    (DiscreteCoind.toInternalHom_bijective U A N hU)).2 Φ
  rw [dualityMap2_eq_explicitDualityPairing02,
    explicitDualityPairing02_explicitCoeff0_toInternalHom G U hU, AddEquiv.apply_symm_apply,
    ← dualityMap2_eq_explicitDualityPairing02, hx, AddMonoidHom.zero_apply, map_zero,
    AddMonoidHom.zero_apply]

end Descent

section Ascent

variable [ContinuousSMul U (InternalHom U A N)]
include hU

/-- **Perfectness of `α₀` ascends from an open subgroup to a coinduced module.** If
corestriction on `H²(-, N)` is bijective and `α₀` is bijective for the `U`-module `A`, then
`α₀` is bijective for `Coind_U^G A`. -/
theorem dualityMap0_bijective_discreteCoind_of_bijective
    (hcor : Function.Bijective (explicitCor2 G N U hU))
    (h : Function.Bijective (dualityMap0 U A N)) :
    Function.Bijective (dualityMap0 G (DiscreteCoind G U A) N) := by
  let c := explicitCoeff2 G (DiscreteCoind G U (InternalHom U A N))
    (DiscreteCoind.toInternalHom U A N) continuous_of_discreteTopology
  let ec := AddEquiv.ofBijective c
    (explicitCoeff2_bijective G _ (DiscreteCoind.toInternalHom_bijective U A N hU))
  let eY : H2 G (InternalHom G (DiscreteCoind G U A) N) →+
      H2 U (InternalHom U A N) :=
    (explicitShapiro2 G U (InternalHom U A N) (U.isClosed_of_isOpen hU)).toAddMonoidHom.comp
      ec.symm.toAddMonoidHom
  refine AddMonoidHom.bijective_of_bijective_pairing (dualityMap0 U A N)
    (dualityMap0 G (DiscreteCoind G U A) N) (explicitShapiro0 G U A).toAddMonoidHom eY
    (explicitCor2 G N U hU) (explicitShapiro0 G U A).bijective ?_ hcor h fun x y ↦ ?_
  · exact (explicitShapiro2 G U (InternalHom U A N)
      (U.isClosed_of_isOpen hU)).bijective.comp ec.symm.bijective
  · rw [dualityMap0_eq_explicitDualityPairing20,
      dualityMap0_eq_explicitDualityPairing20]
    have hc : c (ec.symm y) = y := ec.apply_symm_apply y
    have hec : ec.symm (c (ec.symm y)) = ec.symm y := congrArg ec.symm hc
    rw [← hc, explicitDualityPairing20_explicitCoeff2_toInternalHom G U hU]
    simp only [eY, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hec]

/-- **Perfectness of `α₁` ascends from an open subgroup to a coinduced module.** -/
theorem dualityMap1_bijective_discreteCoind_of_bijective
    (hcor : Function.Bijective (explicitCor2 G N U hU))
    (h : Function.Bijective (dualityMap1 U A N)) :
    Function.Bijective (dualityMap1 G (DiscreteCoind G U A) N) := by
  let c := explicitCoeff1 G (DiscreteCoind G U (InternalHom U A N))
    (DiscreteCoind.toInternalHom U A N) continuous_of_discreteTopology
  let ec := AddEquiv.ofBijective c
    (explicitCoeff1_bijective G _ (DiscreteCoind.toInternalHom_bijective U A N hU))
  let eY : H1 G (InternalHom G (DiscreteCoind G U A) N) →+
      H1 U (InternalHom U A N) :=
    (explicitShapiro1 G U (InternalHom U A N)
      (U.isClosed_of_isOpen hU)).toAddMonoidHom.comp ec.symm.toAddMonoidHom
  refine AddMonoidHom.bijective_of_bijective_pairing (dualityMap1 U A N)
    (dualityMap1 G (DiscreteCoind G U A) N)
    (explicitShapiro1 G U A (U.isClosed_of_isOpen hU)).toAddMonoidHom eY
    (explicitCor2 G N U hU) (explicitShapiro1 G U A
      (U.isClosed_of_isOpen hU)).bijective ?_ hcor h fun x y ↦ ?_
  · exact (explicitShapiro1 G U (InternalHom U A N)
      (U.isClosed_of_isOpen hU)).bijective.comp ec.symm.bijective
  · rw [dualityMap1_eq_neg_explicitDualityPairing11,
      dualityMap1_eq_neg_explicitDualityPairing11]
    have hc : c (ec.symm y) = y := ec.apply_symm_apply y
    have hec : ec.symm (c (ec.symm y)) = ec.symm y := congrArg ec.symm hc
    rw [← hc, explicitDualityPairing11_explicitCoeff1_toInternalHom G U hU, map_neg]
    simp only [eY, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hec]

omit [Finite A] in
/-- **Perfectness of `α₂` ascends from an open subgroup to a coinduced module.** -/
theorem dualityMap2_bijective_discreteCoind_of_bijective
    (hcor : Function.Bijective (explicitCor2 G N U hU))
    (h : Function.Bijective (dualityMap2 U A N)) :
    Function.Bijective (dualityMap2 G (DiscreteCoind G U A) N) := by
  let c := explicitCoeff0 G (DiscreteCoind G U (InternalHom U A N))
    (DiscreteCoind.toInternalHom U A N)
  let ec := AddEquiv.ofBijective c
    (explicitCoeff0_bijective G _ (DiscreteCoind.toInternalHom_bijective U A N hU))
  let eY : H0 G (InternalHom G (DiscreteCoind G U A) N) →+
      H0 U (InternalHom U A N) :=
    (explicitShapiro0 G U (InternalHom U A N)).toAddMonoidHom.comp ec.symm.toAddMonoidHom
  refine AddMonoidHom.bijective_of_bijective_pairing (dualityMap2 U A N)
    (dualityMap2 G (DiscreteCoind G U A) N)
    (explicitShapiro2 G U A (U.isClosed_of_isOpen hU)).toAddMonoidHom eY
    (explicitCor2 G N U hU) (explicitShapiro2 G U A
      (U.isClosed_of_isOpen hU)).bijective ?_ hcor h fun x y ↦ ?_
  · exact (explicitShapiro0 G U (InternalHom U A N)).bijective.comp ec.symm.bijective
  · rw [dualityMap2_eq_explicitDualityPairing02,
      dualityMap2_eq_explicitDualityPairing02]
    have hc : c (ec.symm y) = y := ec.apply_symm_apply y
    have hec : ec.symm (c (ec.symm y)) = ec.symm y := congrArg ec.symm hc
    rw [← hc, explicitDualityPairing02_explicitCoeff0_toInternalHom G U hU]
    simp only [eY, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, hec]

end Ascent

end Shapiro

end TauCeti.ContCohomology
