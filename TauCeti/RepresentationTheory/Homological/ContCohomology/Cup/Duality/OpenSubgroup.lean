/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Duality.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ProjectionFormula

import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality
import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Restriction

/-!
# The evaluation pairings and an open subgroup: restriction and corestriction

Let `U` be an open subgroup of finite index of a topological group `G`, let `M` be a finite discrete
`G`-module and `N` a discrete `G`-module. The evaluation pairings
`⟨-, -⟩_G : Hⁱ(G, Hom(M, N)) × H²⁻ⁱ(G, M) → H²(G, N)` of
`TauCeti/RepresentationTheory/Homological/ContCohomology/Cup/Duality/Basic.lean` are compatible
with the change of group to `U` in two ways.

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

Both are the specializations to the evaluation pairing of the general statements for the explicit
cup products, compatibility with restriction from
`TauCeti/RepresentationTheory/Homological/ContCohomology/Cup/Restriction.lean` and the projection
formula from `TauCeti/RepresentationTheory/Homological/ContCohomology/ProjectionFormula.lean`,
through the naturality of the cup product in the pairing. In the `(2,0)` shape the restricted class
is the degree-two one, so the projection formula used is the one with restriction on the cocycle
factor, `TauCeti.ContCohomology.explicitCup_projection20_res_left`.

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

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9: the duality of an open subgroup of a Demushkin group is compared
  with that of the group through restriction and corestriction.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.3)(i) and
  (iv): compatibility of the cup product with restriction, and the projection formula.
-/

public section

namespace TauCeti.ContCohomology

universe uG uM uN

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

end TauCeti.ContCohomology
