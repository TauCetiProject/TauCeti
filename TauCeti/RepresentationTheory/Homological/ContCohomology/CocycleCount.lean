/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree

/-!
# Counting cocycles and coboundaries in low degrees

The explicit low-degree complex of `TauCeti.ContCohomology` presents `H¹(G, M)` and `H²(G, M)`
as the quotients `Z¹/B¹` and `Z²/B²`, and its two coboundary groups are images of differentials:
`B¹ = d⁰(M)` with kernel `H⁰(G, M) = M^G`, and `B² = d¹(C¹)` with kernel `Z¹`. Lagrange's theorem
and the first isomorphism theorem therefore relate the orders of all of these groups:

```text
#Z¹ = #H¹ · #B¹,   #B¹ · #H⁰ = #M,   #Z² = #H² · #B²,   #C¹ = #B² · #Z¹.
```

Counting arguments with finite coefficients, such as bounds on Selmer groups or the
Greenberg–Wiles comparison of a Selmer group with its dual, are often carried out on cocycles,
while Euler characteristic formulas and duality theorems count classes. The first two identities
convert between the two: `#Z¹ · #H⁰ = #H¹ · #M`.

All statements are about `Nat.card`, so they hold with no finiteness hypothesis: when one side is
infinite, `Nat.card` of it is `0` and so is the other side.

## Main results

* `TauCeti.ContCohomology.natCard_Z1`: `#Z¹ = #H¹ · #B¹`.
* `TauCeti.ContCohomology.natCard_B1_mul_natCard_H0`: `#B¹ · #H⁰ = #M`, from
  `TauCeti.ContCohomology.ker_d0` and `TauCeti.ContCohomology.range_d0`, which identify the
  kernel and the image of `d⁰` with `H⁰` and `B¹`.
* `TauCeti.ContCohomology.natCard_Z1_mul_natCard_H0`: `#Z¹ · #H⁰ = #H¹ · #M`.
* `TauCeti.ContCohomology.natCard_Z2`: `#Z² = #H² · #B²`.
* `TauCeti.ContCohomology.natCard_C1`: `#C¹ = #B² · #Z¹`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Ch. I, §2: the
  inhomogeneous complex of continuous cochains.
-/

public section

namespace TauCeti.ContCohomology

universe u v

section DegreeZero

variable (G : Type u) [Monoid G] (M : Type v) [AddCommGroup M] [DistribMulAction G M]

/-- **Counting `1`-coboundaries.** `#B¹ · #H⁰ = #M`: the coboundary map `d⁰` has kernel `H⁰` and
image `B¹`. -/
theorem natCard_B1_mul_natCard_H0 : Nat.card (B1 G M) * Nat.card (H0 G M) = Nat.card M := by
  rw [mul_comm, ← ker_d0, ← range_d0, AddSubgroup.card_ker_mul_card_range]

end DegreeZero

section DegreeOne

variable (G : Type u) [Monoid G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- **Counting `1`-cocycles.** `#Z¹ = #H¹ · #B¹`. -/
theorem natCard_Z1 : Nat.card (Z1 G M) = Nat.card (H1 G M) * Nat.card (B1 G M) := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ((B1 G M).addSubgroupOf (Z1 G M))]
  exact congrArg _ (Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (B1_le_Z1 G M)).toEquiv)

/-- **Cocycles against classes in degree `1`.** `#Z¹ · #H⁰ = #H¹ · #M`, so that, for finite
coefficients, counting `1`-cocycles and counting `1`-classes differ by the factor `#M / #H⁰`. -/
theorem natCard_Z1_mul_natCard_H0 :
    Nat.card (Z1 G M) * Nat.card (H0 G M) = Nat.card (H1 G M) * Nat.card M := by
  rw [natCard_Z1, mul_assoc, natCard_B1_mul_natCard_H0]

end DegreeOne

section DegreeTwo

variable (G : Type u) [Monoid G] [TopologicalSpace G] [ContinuousMul G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]

/-- **Counting `2`-cocycles.** `#Z² = #H² · #B²`. -/
theorem natCard_Z2 : Nat.card (Z2 G M) = Nat.card (H2 G M) * Nat.card (B2 G M) := by
  rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup ((B2 G M).addSubgroupOf (Z2 G M))]
  exact congrArg _ (Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (B2_le_Z2 G M)).toEquiv)

end DegreeTwo

section Cochains

variable (G : Type u) [Mul G] [TopologicalSpace G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribSMul G M]

/-- **Counting `2`-coboundaries.** `#C¹ = #B² · #Z¹`: `d¹` restricted to the continuous
`1`-cochains has image `B²` and kernel `Z¹`. -/
theorem natCard_C1 : Nat.card (C1 G M) = Nat.card (B2 G M) * Nat.card (Z1 G M) := by
  let f := (d1 G M).comp (C1 G M).subtype
  have hker : f.ker = (Z1 G M).addSubgroupOf (C1 G M) := by
    ext c
    simp [f, AddSubgroup.mem_addSubgroupOf, mem_Z1_iff, mem_C1_iff.1 c.property]
  have hrange : f.range = B2 G M := by
    ext x
    simp [f, mem_B2_iff, mem_C1_iff]
  rw [← AddSubgroup.card_ker_mul_card_range f, hker, hrange, mul_comm,
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (Z1_le_C1 G M)).toEquiv]

end Cochains

end TauCeti.ContCohomology
