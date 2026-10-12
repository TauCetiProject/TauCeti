/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Pairing
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Trace.DegreeOne
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Trace.DegreeTwo
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality

/-!
# Shapiro's isomorphism and the cup product

Let `U` be a subgroup of a compact group `G` and let `μ : A →+ B →+ C` be a `U`-equivariant
pairing of discrete `U`-modules. The pointwise pairing
`TauCeti.DiscreteCoind.pointwisePairing` of the coinduced modules is a `G`-equivariant pairing
`Coind_U^G A × Coind_U^G B → Coind_U^G C`, and the explicit Shapiro maps are **multiplicative** for
it:

```text
sh (a ⌣ b) = sh a ⌣ sh b,
```

where the left cup is taken over `G` along the pointwise pairing and the right cup over `U` along
`μ`. The forward Shapiro map is the compatible-pair pullback along `U ↪ G` and evaluation at `1`,
and evaluation at `1` intertwines the two pairings, so each of the six low-degree statements is an
instance of the naturality of the cup product in compatible pairs
(`TauCeti/RepresentationTheory/Homological/ContCohomology/Cup/Naturality.lean`).

When `U` is open in a profinite group `G`, `A` and `B` are discrete `U`-modules and the target `C`
is a discrete `G`-module restricted to `U`, corestriction is inverse Shapiro followed by the
coefficient map of the trace, and the multiplicativity turns into the **corestriction of a cup
product of `U`**:

```text
cor (a ⌣_U b) = tr_* (sh⁻¹ a ⌣_G sh⁻¹ b).
```

The right-hand side is the cup over `G` of the inverse Shapiro images along the pointwise pairing
of coinduced modules, pushed to `P` by the trace `Coind_U^G P → P`. For `𝔽_p`-coefficients and
`μ` the multiplication, `tr ∘ pointwisePairing` is the standard `G`-invariant symmetric form on the
permutation module `𝔽_p[G ⧸ U]`, and the formula reads the cup product of `U` on the cohomology of
`G` with coefficients in that module. This is how the duality of an open subgroup of a Demushkin
group is read from the duality of the group itself.

## Main results

* `TauCeti.ContCohomology.explicitShapiro0_explicitCup00`,
  `explicitShapiroMap1_explicitCup01`, `explicitShapiroMap1_explicitCup10`,
  `explicitShapiroMap2_explicitCup02`, `explicitShapiroMap2_explicitCup11` and
  `explicitShapiroMap2_explicitCup20`: **the Shapiro maps are multiplicative**, in each bidegree
  `(p, q)` with `p + q ≤ 2`.
* `TauCeti.ContCohomology.explicitCor0_explicitCup00`, `explicitCor1_explicitCup01`,
  `explicitCor1_explicitCup10`, `explicitCor2_explicitCup02`, `explicitCor2_explicitCup11` and
  `explicitCor2_explicitCup20`: **the corestriction of a cup product of an open subgroup** is the
  trace of the cup product over `G` of the inverse Shapiro images.

## References

* J.-P. Serre, *Structure de certains pro-p-groupes (d'après Demuškin)*, Séminaire Bourbaki 8
  (1962/63), exposé 252, §9.2: the duality of an open subgroup is deduced from that of the group
  through Shapiro's lemma.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (1.4.2), (1.5.3) and (1.6.4): naturality of the cup product, its behaviour under the change of
  group, and Shapiro's lemma.
-/

public section

namespace TauCeti.ContCohomology

universe uG uA uB uC

section Multiplicativity

/-! ### The Shapiro maps are multiplicative -/

section DegreeZero

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G] (U : Subgroup G)
  (A : Type uA) [AddCommGroup A] [DistribMulAction U A]
  (B : Type uB) [AddCommGroup B] [DistribMulAction U B]
  (C : Type uC) [AddCommGroup C] [DistribMulAction U C]
  (μ : A →+ B →+ C) (hμ : ∀ (u : U) (a : A) (b : B), μ (u • a) (u • b) = u • μ a b)

/-- **The degree-zero Shapiro isomorphism is multiplicative** for the `(0,0)` cup product. -/
@[simp]
theorem explicitShapiro0_explicitCup00 (a : H0 G (DiscreteCoind G U A))
    (b : H0 G (DiscreteCoind G U B)) :
    explicitShapiro0 G U C
        (explicitCup00 G (DiscreteCoind G U A) (DiscreteCoind G U B) (DiscreteCoind G U C)
          (DiscreteCoind.pointwisePairing U μ hμ) (DiscreteCoind.pointwisePairing_smul U μ hμ)
          a b) =
      explicitCup00 U A B C μ hμ (explicitShapiro0 G U A a) (explicitShapiro0 G U B b) := by
  simp only [explicitShapiro0_eq_explicitMap0]
  exact explicitMap0_explicitCup00 G (DiscreteCoind G U A) (DiscreteCoind G U B)
    (DiscreteCoind G U C) (DiscreteCoind.pointwisePairing U μ hμ)
    (DiscreteCoind.pointwisePairing_smul U μ hμ) U A B C μ hμ
    (ContinuousMonoidHom.subgroupSubtype U : U →* G) (DiscreteCoind.eval G U A)
    (DiscreteCoind.eval G U B) (DiscreteCoind.eval G U C) (fun u f => DiscreteCoind.eval_smul u f)
    (fun u f => DiscreteCoind.eval_smul u f) (fun u f => DiscreteCoind.eval_smul u f)
    (DiscreteCoind.eval_pointwisePairing U μ hμ) a b

end DegreeZero

section PositiveDegree

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (U : Subgroup G)
  (A : Type uA) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
    [DistribMulAction U A] [ContinuousSMul U A]
  (B : Type uB) [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B]
    [DistribMulAction U B] [ContinuousSMul U B]
  (C : Type uC) [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
    [DistribMulAction U C] [ContinuousSMul U C]
  (μ : A →+ B →+ C) (hμ : ∀ (u : U) (a : A) (b : B), μ (u • a) (u • b) = u • μ a b)

/-- Multiplication on the subgroup `U` is continuous for the subspace topology. -/
local instance instContinuousMulSubgroupMultiplicativity : ContinuousMul U :=
  U.toSubmonoid.continuousMul

omit [ContinuousSMul U A] in
/-- **The Shapiro maps are multiplicative** for the `(0,1)` cup product. -/
@[simp]
theorem explicitShapiroMap1_explicitCup01 (a : H0 G (DiscreteCoind G U A))
    (b : H1 G (DiscreteCoind G U B)) :
    explicitShapiroMap1 G U C
        (explicitCup01 G (DiscreteCoind G U A) (DiscreteCoind G U B) (DiscreteCoind G U C)
          (DiscreteCoind.pointwisePairing U μ hμ) continuous_of_discreteTopology
          (DiscreteCoind.pointwisePairing_smul U μ hμ) a b) =
      explicitCup01 U A B C μ continuous_of_discreteTopology hμ
        (explicitShapiro0 G U A a) (explicitShapiroMap1 G U B b) := by
  rw [explicitShapiro0_eq_explicitMap0]
  exact explicitMap1_explicitCup01 G (DiscreteCoind G U A) (DiscreteCoind G U B)
    (DiscreteCoind G U C) (DiscreteCoind.pointwisePairing U μ hμ) continuous_of_discreteTopology
    (DiscreteCoind.pointwisePairing_smul U μ hμ) U A B C μ continuous_of_discreteTopology hμ
    (ContinuousMonoidHom.subgroupSubtype U) (DiscreteCoind.eval G U A) (DiscreteCoind.eval G U B)
    (DiscreteCoind.eval G U C) DiscreteCoind.continuous_eval DiscreteCoind.continuous_eval
    (eval_subgroupSubtype_smul G U A) (eval_subgroupSubtype_smul G U B)
    (eval_subgroupSubtype_smul G U C) (DiscreteCoind.eval_pointwisePairing U μ hμ) a b

omit [ContinuousSMul U B] in
/-- **The Shapiro maps are multiplicative** for the `(1,0)` cup product. -/
@[simp]
theorem explicitShapiroMap1_explicitCup10 (a : H1 G (DiscreteCoind G U A))
    (b : H0 G (DiscreteCoind G U B)) :
    explicitShapiroMap1 G U C
        (explicitCup10 G (DiscreteCoind G U A) (DiscreteCoind G U B) (DiscreteCoind G U C)
          (DiscreteCoind.pointwisePairing U μ hμ) continuous_of_discreteTopology
          (DiscreteCoind.pointwisePairing_smul U μ hμ) a b) =
      explicitCup10 U A B C μ continuous_of_discreteTopology hμ
        (explicitShapiroMap1 G U A a) (explicitShapiro0 G U B b) := by
  rw [explicitShapiro0_eq_explicitMap0]
  exact explicitMap1_explicitCup10 G (DiscreteCoind G U A) (DiscreteCoind G U B)
    (DiscreteCoind G U C) (DiscreteCoind.pointwisePairing U μ hμ) continuous_of_discreteTopology
    (DiscreteCoind.pointwisePairing_smul U μ hμ) U A B C μ continuous_of_discreteTopology hμ
    (ContinuousMonoidHom.subgroupSubtype U) (DiscreteCoind.eval G U A) (DiscreteCoind.eval G U B)
    (DiscreteCoind.eval G U C) DiscreteCoind.continuous_eval DiscreteCoind.continuous_eval
    (eval_subgroupSubtype_smul G U A) (eval_subgroupSubtype_smul G U B)
    (eval_subgroupSubtype_smul G U C) (DiscreteCoind.eval_pointwisePairing U μ hμ) a b

omit [ContinuousSMul U A] in
/-- **The Shapiro maps are multiplicative** for the `(0,2)` cup product. -/
@[simp]
theorem explicitShapiroMap2_explicitCup02 (a : H0 G (DiscreteCoind G U A))
    (b : H2 G (DiscreteCoind G U B)) :
    explicitShapiroMap2 G U C
        (explicitCup02 G (DiscreteCoind G U A) (DiscreteCoind G U B) (DiscreteCoind G U C)
          (DiscreteCoind.pointwisePairing U μ hμ) continuous_of_discreteTopology
          (DiscreteCoind.pointwisePairing_smul U μ hμ) a b) =
      explicitCup02 U A B C μ continuous_of_discreteTopology hμ
        (explicitShapiro0 G U A a) (explicitShapiroMap2 G U B b) := by
  rw [explicitShapiro0_eq_explicitMap0, explicitShapiroMap2_def, explicitShapiroMap2_def]
  exact explicitMap2_explicitCup02 G (DiscreteCoind G U A) (DiscreteCoind G U B)
    (DiscreteCoind G U C) (DiscreteCoind.pointwisePairing U μ hμ) continuous_of_discreteTopology
    (DiscreteCoind.pointwisePairing_smul U μ hμ) U A B C μ continuous_of_discreteTopology hμ
    (ContinuousMonoidHom.subgroupSubtype U) (DiscreteCoind.eval G U A) (DiscreteCoind.eval G U B)
    (DiscreteCoind.eval G U C) DiscreteCoind.continuous_eval DiscreteCoind.continuous_eval
    (eval_subgroupSubtype_smul G U A) (eval_subgroupSubtype_smul G U B)
    (eval_subgroupSubtype_smul G U C) (DiscreteCoind.eval_pointwisePairing U μ hμ) a b

/-- **The Shapiro maps are multiplicative** for the `(1,1)` cup product: `sh (a ⌣ b) = sh a ⌣ sh b`,
with the cup over `G` taken along the pointwise pairing of the coinduced modules. -/
@[simp]
theorem explicitShapiroMap2_explicitCup11 (a : H1 G (DiscreteCoind G U A))
    (b : H1 G (DiscreteCoind G U B)) :
    explicitShapiroMap2 G U C
        (explicitCup11 G (DiscreteCoind G U A) (DiscreteCoind G U B) (DiscreteCoind G U C)
          (DiscreteCoind.pointwisePairing U μ hμ) continuous_of_discreteTopology
          (DiscreteCoind.pointwisePairing_smul U μ hμ) a b) =
      explicitCup11 U A B C μ continuous_of_discreteTopology hμ
        (explicitShapiroMap1 G U A a) (explicitShapiroMap1 G U B b) := by
  rw [explicitShapiroMap2_def]
  exact explicitMap2_explicitCup11 G (DiscreteCoind G U A) (DiscreteCoind G U B)
    (DiscreteCoind G U C) (DiscreteCoind.pointwisePairing U μ hμ) continuous_of_discreteTopology
    (DiscreteCoind.pointwisePairing_smul U μ hμ) U A B C μ continuous_of_discreteTopology hμ
    (ContinuousMonoidHom.subgroupSubtype U) (DiscreteCoind.eval G U A) (DiscreteCoind.eval G U B)
    (DiscreteCoind.eval G U C) DiscreteCoind.continuous_eval DiscreteCoind.continuous_eval
    DiscreteCoind.continuous_eval (eval_subgroupSubtype_smul G U A)
    (eval_subgroupSubtype_smul G U B) (eval_subgroupSubtype_smul G U C)
    (DiscreteCoind.eval_pointwisePairing U μ hμ) a b

omit [ContinuousSMul U B] in
/-- **The Shapiro maps are multiplicative** for the `(2,0)` cup product. -/
@[simp]
theorem explicitShapiroMap2_explicitCup20 (a : H2 G (DiscreteCoind G U A))
    (b : H0 G (DiscreteCoind G U B)) :
    explicitShapiroMap2 G U C
        (explicitCup20 G (DiscreteCoind G U A) (DiscreteCoind G U B) (DiscreteCoind G U C)
          (DiscreteCoind.pointwisePairing U μ hμ) continuous_of_discreteTopology
          (DiscreteCoind.pointwisePairing_smul U μ hμ) a b) =
      explicitCup20 U A B C μ continuous_of_discreteTopology hμ
        (explicitShapiroMap2 G U A a) (explicitShapiro0 G U B b) := by
  rw [explicitShapiro0_eq_explicitMap0, explicitShapiroMap2_def, explicitShapiroMap2_def]
  exact explicitMap2_explicitCup20 G (DiscreteCoind G U A) (DiscreteCoind G U B)
    (DiscreteCoind G U C) (DiscreteCoind.pointwisePairing U μ hμ) continuous_of_discreteTopology
    (DiscreteCoind.pointwisePairing_smul U μ hμ) U A B C μ continuous_of_discreteTopology hμ
    (ContinuousMonoidHom.subgroupSubtype U) (DiscreteCoind.eval G U A) (DiscreteCoind.eval G U B)
    (DiscreteCoind.eval G U C) DiscreteCoind.continuous_eval DiscreteCoind.continuous_eval
    (eval_subgroupSubtype_smul G U A) (eval_subgroupSubtype_smul G U B)
    (eval_subgroupSubtype_smul G U C) (DiscreteCoind.eval_pointwisePairing U μ hμ) a b

end PositiveDegree

end Multiplicativity

section Corestriction

/-! ### The corestriction of a cup product of an open subgroup

Here `M` and `N` are discrete `U`-modules, `P` is a discrete `G`-module restricted to the open
subgroup `U`, and `μ` is a `U`-equivariant pairing `M × N → P`; only the target `P` needs the
ambient `G`-action, for the corestriction and the trace. Corestriction is inverse Shapiro followed
by the trace
(`TauCeti.ContCohomology.explicitCor2_eq_explicitCoeff2_trace` and its lower-degree companions),
so the multiplicativity above computes the corestriction of a cup product of `U`. -/

section DegreeZero

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G] (U : Subgroup G)
  [U.FiniteIndex]
  (M : Type uA) [AddCommGroup M] [DistribMulAction U M]
  (N : Type uB) [AddCommGroup N] [DistribMulAction U N]
  (P : Type uC) [AddCommGroup P] [DistribMulAction G P]
  (μ : M →+ N →+ P) (hμ : ∀ (u : U) (m : M) (n : N), μ (u • m) (u • n) = u • μ m n)

/-- **The corestriction of a `(0,0)` cup product of `U`** is the trace of the `(0,0)` cup product
over `G` of the inverse Shapiro images, along the pointwise pairing of the coinduced modules. -/
theorem explicitCor0_explicitCup00 (a : H0 U M) (b : H0 U N) :
    explicitCor0 G P U (explicitCup00 U M N P μ hμ a b) =
      explicitCoeff0 G (DiscreteCoind G U P) (DiscreteCoind.trace G U P)
        (explicitCup00 G (DiscreteCoind G U M) (DiscreteCoind G U N) (DiscreteCoind G U P)
          (DiscreteCoind.pointwisePairing U μ hμ)
          (DiscreteCoind.pointwisePairing_smul U μ hμ)
          ((explicitShapiro0 G U M).symm a) ((explicitShapiro0 G U N).symm b)) := by
  rw [explicitCor0_eq_explicitCoeff0_trace, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
  congr 1
  apply (explicitShapiro0 G U P).injective
  rw [AddEquiv.apply_symm_apply, explicitShapiro0_explicitCup00, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

end DegreeZero

section PositiveDegree

variable (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
  (M : Type uA) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction U M] [ContinuousSMul U M]
  (N : Type uB) [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]
    [DistribMulAction U N] [ContinuousSMul U N]
  (P : Type uC) [AddCommGroup P] [TopologicalSpace P] [DiscreteTopology P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (μ : M →+ N →+ P) (hμ : ∀ (u : U) (m : M) (n : N), μ (u • m) (u • n) = u • μ m n)

/-- Multiplication on the subgroup `U` is continuous for the subspace topology. -/
local instance instContinuousMulSubgroupCorestriction : ContinuousMul U :=
  U.toSubmonoid.continuousMul

omit [ContinuousSMul U M] in
/-- **The corestriction of a `(0,1)` cup product of `U`** is the trace of the `(0,1)` cup product
over `G` of the inverse Shapiro images, along the pointwise pairing of the coinduced modules. -/
theorem explicitCor1_explicitCup01 (a : H0 U M) (b : H1 U N) :
    explicitCor1 G P U hU
        (explicitCup01 U M N P μ continuous_of_discreteTopology hμ a b) =
      explicitCoeff1 G (DiscreteCoind G U P) (DiscreteCoind.trace G U P)
        DiscreteCoind.continuous_trace
        (explicitCup01 G (DiscreteCoind G U M) (DiscreteCoind G U N) (DiscreteCoind G U P)
          (DiscreteCoind.pointwisePairing U μ hμ) continuous_of_discreteTopology
          (DiscreteCoind.pointwisePairing_smul U μ hμ)
          ((explicitShapiro0 G U M).symm a)
          ((explicitShapiro1 G U N (U.isClosed_of_isOpen hU)).symm b)) := by
  rw [explicitCor1_eq_explicitCoeff1_trace hU, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  congr 1
  apply (explicitShapiro1 G U P (U.isClosed_of_isOpen hU)).injective
  rw [AddEquiv.apply_symm_apply, explicitShapiro1_apply, explicitShapiroMap1_explicitCup01,
    AddEquiv.apply_symm_apply, ← explicitShapiro1_apply G U N (U.isClosed_of_isOpen hU),
    AddEquiv.apply_symm_apply]

omit [ContinuousSMul U N] in
/-- **The corestriction of a `(1,0)` cup product of `U`** is the trace of the `(1,0)` cup product
over `G` of the inverse Shapiro images, along the pointwise pairing of the coinduced modules. -/
theorem explicitCor1_explicitCup10 (a : H1 U M) (b : H0 U N) :
    explicitCor1 G P U hU
        (explicitCup10 U M N P μ continuous_of_discreteTopology hμ a b) =
      explicitCoeff1 G (DiscreteCoind G U P) (DiscreteCoind.trace G U P)
        DiscreteCoind.continuous_trace
        (explicitCup10 G (DiscreteCoind G U M) (DiscreteCoind G U N) (DiscreteCoind G U P)
          (DiscreteCoind.pointwisePairing U μ hμ) continuous_of_discreteTopology
          (DiscreteCoind.pointwisePairing_smul U μ hμ)
          ((explicitShapiro1 G U M (U.isClosed_of_isOpen hU)).symm a)
          ((explicitShapiro0 G U N).symm b)) := by
  rw [explicitCor1_eq_explicitCoeff1_trace hU, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  congr 1
  apply (explicitShapiro1 G U P (U.isClosed_of_isOpen hU)).injective
  rw [AddEquiv.apply_symm_apply, explicitShapiro1_apply, explicitShapiroMap1_explicitCup10,
    AddEquiv.apply_symm_apply, ← explicitShapiro1_apply G U M (U.isClosed_of_isOpen hU),
    AddEquiv.apply_symm_apply]

omit [ContinuousSMul U M] in
/-- **The corestriction of a `(0,2)` cup product of `U`** is the trace of the `(0,2)` cup product
over `G` of the inverse Shapiro images, along the pointwise pairing of the coinduced modules. -/
theorem explicitCor2_explicitCup02 (a : H0 U M) (b : H2 U N) :
    explicitCor2 G P U hU
        (explicitCup02 U M N P μ continuous_of_discreteTopology hμ a b) =
      explicitCoeff2 G (DiscreteCoind G U P) (DiscreteCoind.trace G U P)
        DiscreteCoind.continuous_trace
        (explicitCup02 G (DiscreteCoind G U M) (DiscreteCoind G U N) (DiscreteCoind G U P)
          (DiscreteCoind.pointwisePairing U μ hμ) continuous_of_discreteTopology
          (DiscreteCoind.pointwisePairing_smul U μ hμ)
          ((explicitShapiro0 G U M).symm a)
          ((explicitShapiro2 G U N (U.isClosed_of_isOpen hU)).symm b)) := by
  rw [explicitCor2_eq_explicitCoeff2_trace hU, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  congr 1
  apply (explicitShapiro2 G U P (U.isClosed_of_isOpen hU)).injective
  rw [AddEquiv.apply_symm_apply, explicitShapiro2_apply, explicitShapiroMap2_explicitCup02,
    AddEquiv.apply_symm_apply, ← explicitShapiro2_apply G U N (U.isClosed_of_isOpen hU),
    AddEquiv.apply_symm_apply]

/-- **The corestriction of a `(1,1)` cup product of `U`** is the trace of the `(1,1)` cup product
over `G` of the inverse Shapiro images, along the pointwise pairing of the coinduced modules:
`cor (a ⌣_U b) = tr_* (sh⁻¹ a ⌣_G sh⁻¹ b)`. -/
theorem explicitCor2_explicitCup11 (a : H1 U M) (b : H1 U N) :
    explicitCor2 G P U hU
        (explicitCup11 U M N P μ continuous_of_discreteTopology hμ a b) =
      explicitCoeff2 G (DiscreteCoind G U P) (DiscreteCoind.trace G U P)
        DiscreteCoind.continuous_trace
        (explicitCup11 G (DiscreteCoind G U M) (DiscreteCoind G U N) (DiscreteCoind G U P)
          (DiscreteCoind.pointwisePairing U μ hμ) continuous_of_discreteTopology
          (DiscreteCoind.pointwisePairing_smul U μ hμ)
          ((explicitShapiro1 G U M (U.isClosed_of_isOpen hU)).symm a)
          ((explicitShapiro1 G U N (U.isClosed_of_isOpen hU)).symm b)) := by
  rw [explicitCor2_eq_explicitCoeff2_trace hU, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  congr 1
  apply (explicitShapiro2 G U P (U.isClosed_of_isOpen hU)).injective
  rw [AddEquiv.apply_symm_apply, explicitShapiro2_apply, explicitShapiroMap2_explicitCup11,
    ← explicitShapiro1_apply G U M (U.isClosed_of_isOpen hU),
    ← explicitShapiro1_apply G U N (U.isClosed_of_isOpen hU), AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

omit [ContinuousSMul U N] in
/-- **The corestriction of a `(2,0)` cup product of `U`** is the trace of the `(2,0)` cup product
over `G` of the inverse Shapiro images, along the pointwise pairing of the coinduced modules. -/
theorem explicitCor2_explicitCup20 (a : H2 U M) (b : H0 U N) :
    explicitCor2 G P U hU
        (explicitCup20 U M N P μ continuous_of_discreteTopology hμ a b) =
      explicitCoeff2 G (DiscreteCoind G U P) (DiscreteCoind.trace G U P)
        DiscreteCoind.continuous_trace
        (explicitCup20 G (DiscreteCoind G U M) (DiscreteCoind G U N) (DiscreteCoind G U P)
          (DiscreteCoind.pointwisePairing U μ hμ) continuous_of_discreteTopology
          (DiscreteCoind.pointwisePairing_smul U μ hμ)
          ((explicitShapiro2 G U M (U.isClosed_of_isOpen hU)).symm a)
          ((explicitShapiro0 G U N).symm b)) := by
  rw [explicitCor2_eq_explicitCoeff2_trace hU, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  congr 1
  apply (explicitShapiro2 G U P (U.isClosed_of_isOpen hU)).injective
  rw [AddEquiv.apply_symm_apply, explicitShapiro2_apply, explicitShapiroMap2_explicitCup20,
    AddEquiv.apply_symm_apply, ← explicitShapiro2_apply G U M (U.isClosed_of_isOpen hU),
    AddEquiv.apply_symm_apply]

end PositiveDegree

end Corestriction

end TauCeti.ContCohomology
