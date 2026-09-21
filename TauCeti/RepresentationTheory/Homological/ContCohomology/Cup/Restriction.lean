/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Cup.Naturality

/-!
# Restriction preserves explicit low-degree cup products

Restriction along a subgroup preserves each of the six cup products on explicit continuous
cohomology:

```text
res (a ⌣ b) = res a ⌣ res b.
```

This is the low-degree inhomogeneous form of the naturality of the cup product: each of the six
statements below is the instance, at the compatible pair `(U ↪ G, id)`, of the corresponding
theorem of
`TauCeti/RepresentationTheory/Homological/ContCohomology/Cup/Naturality.lean`, and together they
expose that compatibility in every bidegree `(p, q)` with `p + q ≤ 2`.

## Main statements

* `TauCeti.ContCohomology.explicitRes0_explicitCup00`, `explicitRes1_explicitCup01`,
  `explicitRes1_explicitCup10`, `explicitRes2_explicitCup02`, `explicitRes2_explicitCup11`, and
  `explicitRes2_explicitCup20`: restriction preserves the corresponding explicit cup product.

## Reference

J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.3)(i).
-/

public section

namespace TauCeti.ContCohomology

universe uG uM uN uP

section DegreeZero

variable (G : Type uG) [Group G]
  (M : Type uM) [AddCommGroup M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [DistribMulAction G N]
  (P : Type uP) [AddCommGroup P] [DistribMulAction G P]
  (U : Subgroup G)
  (μ : M →+ N →+ P)
  (hequiv : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n)

/-- **Restriction preserves the `(0,0)` cup product.** -/
@[simp]
theorem explicitRes0_explicitCup00 (a : H0 G M) (b : H0 G N) :
    explicitRes0 G P U (explicitCup00 G M N P μ hequiv a b) =
      explicitCup00 U M N P μ (fun u m n => hequiv (u : G) m n)
        (explicitRes0 G M U a) (explicitRes0 G N U b) := by
  simp only [explicitRes0_eq_explicitMap0]
  exact explicitMap0_explicitCup00 G M N P μ hequiv U M N P μ (fun u m n => hequiv (u : G) m n)
    U.subtype (AddMonoidHom.id M) (AddMonoidHom.id N) (AddMonoidHom.id P) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) a b

end DegreeZero

section DegreeOne

variable (G : Type uG) [Group G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (U : Subgroup G)
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n)

include hμ hequiv

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- **Restriction preserves the `(0,1)` cup product.** -/
@[simp]
theorem explicitRes1_explicitCup01 (a : H0 G M) (b : H1 G N) :
    explicitRes1 G P U (explicitCup01 G M N P μ hμ hequiv a b) =
      explicitCup01 U M N P μ hμ (fun u m n => hequiv (u : G) m n)
        (explicitRes0 G M U a) (explicitRes1 G N U b) := by
  simp only [explicitRes0_eq_explicitMap0, explicitRes1_eq_explicitMap1]
  exact explicitMap1_explicitCup01 G M N P μ hμ hequiv U M N P μ hμ
    (fun u m n => hequiv (u : G) m n) (ContinuousMonoidHom.subgroupSubtype U)
    (AddMonoidHom.id M) (AddMonoidHom.id N) (AddMonoidHom.id P) continuous_id continuous_id
    (id_subgroupSubtype_smul G M U) (id_subgroupSubtype_smul G N U)
    (id_subgroupSubtype_smul G P U) (fun _ _ => rfl) a b

omit [IsTopologicalAddGroup N] [ContinuousSMul G N] in
/-- **Restriction preserves the `(1,0)` cup product.** -/
@[simp]
theorem explicitRes1_explicitCup10 (a : H1 G M) (b : H0 G N) :
    explicitRes1 G P U (explicitCup10 G M N P μ hμ hequiv a b) =
      explicitCup10 U M N P μ hμ (fun u m n => hequiv (u : G) m n)
        (explicitRes1 G M U a) (explicitRes0 G N U b) := by
  simp only [explicitRes0_eq_explicitMap0, explicitRes1_eq_explicitMap1]
  exact explicitMap1_explicitCup10 G M N P μ hμ hequiv U M N P μ hμ
    (fun u m n => hequiv (u : G) m n) (ContinuousMonoidHom.subgroupSubtype U)
    (AddMonoidHom.id M) (AddMonoidHom.id N) (AddMonoidHom.id P) continuous_id continuous_id
    (id_subgroupSubtype_smul G M U) (id_subgroupSubtype_smul G N U)
    (id_subgroupSubtype_smul G P U) (fun _ _ => rfl) a b

end DegreeOne

section DegreeTwo

variable (G : Type uG) [Group G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M] [ContinuousSMul G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (U : Subgroup G)
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n)

local instance : ContinuousMul U := U.toSubmonoid.continuousMul

include hμ hequiv

omit [IsTopologicalAddGroup M] [ContinuousSMul G M] in
/-- **Restriction preserves the `(0,2)` cup product.** -/
@[simp]
theorem explicitRes2_explicitCup02 (a : H0 G M) (b : H2 G N) :
    explicitRes2 G P U (explicitCup02 G M N P μ hμ hequiv a b) =
      explicitCup02 U M N P μ hμ (fun u m n => hequiv (u : G) m n)
        (explicitRes0 G M U a) (explicitRes2 G N U b) := by
  simp only [explicitRes0_eq_explicitMap0, explicitRes2_eq_explicitMap2]
  exact explicitMap2_explicitCup02 G M N P μ hμ hequiv U M N P μ hμ
    (fun u m n => hequiv (u : G) m n) (ContinuousMonoidHom.subgroupSubtype U)
    (AddMonoidHom.id M) (AddMonoidHom.id N) (AddMonoidHom.id P) continuous_id continuous_id
    (id_subgroupSubtype_smul G M U) (id_subgroupSubtype_smul G N U)
    (id_subgroupSubtype_smul G P U) (fun _ _ => rfl) a b

/-- **Restriction preserves the `(1,1)` cup product.** -/
@[simp]
theorem explicitRes2_explicitCup11 (a : H1 G M) (b : H1 G N) :
    explicitRes2 G P U (explicitCup11 G M N P μ hμ hequiv a b) =
      explicitCup11 U M N P μ hμ (fun u m n => hequiv (u : G) m n)
        (explicitRes1 G M U a) (explicitRes1 G N U b) := by
  simp only [explicitRes1_eq_explicitMap1, explicitRes2_eq_explicitMap2]
  exact explicitMap2_explicitCup11 G M N P μ hμ hequiv U M N P μ hμ
    (fun u m n => hequiv (u : G) m n) (ContinuousMonoidHom.subgroupSubtype U)
    (AddMonoidHom.id M) (AddMonoidHom.id N) (AddMonoidHom.id P) continuous_id continuous_id
    continuous_id (id_subgroupSubtype_smul G M U) (id_subgroupSubtype_smul G N U)
    (id_subgroupSubtype_smul G P U) (fun _ _ => rfl) a b

omit [IsTopologicalAddGroup N] [ContinuousSMul G N] in
/-- **Restriction preserves the `(2,0)` cup product.** -/
@[simp]
theorem explicitRes2_explicitCup20 (a : H2 G M) (b : H0 G N) :
    explicitRes2 G P U (explicitCup20 G M N P μ hμ hequiv a b) =
      explicitCup20 U M N P μ hμ (fun u m n => hequiv (u : G) m n)
        (explicitRes2 G M U a) (explicitRes0 G N U b) := by
  simp only [explicitRes0_eq_explicitMap0, explicitRes2_eq_explicitMap2]
  exact explicitMap2_explicitCup20 G M N P μ hμ hequiv U M N P μ hμ
    (fun u m n => hequiv (u : G) m n) (ContinuousMonoidHom.subgroupSubtype U)
    (AddMonoidHom.id M) (AddMonoidHom.id N) (AddMonoidHom.id P) continuous_id continuous_id
    (id_subgroupSubtype_smul G M U) (id_subgroupSubtype_smul G N U)
    (id_subgroupSubtype_smul G P U) (fun _ _ => rfl) a b

end DegreeTwo

end TauCeti.ContCohomology
