/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree
import Mathlib.Topology.Instances.ZMod

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
convert between the two: `#Z¹ · #H⁰ = #H¹ · #M`. More generally, a group `W ≤ Z¹` of cocycles cut
out by conditions (local conditions of a Selmer group, say) is counted by its group of classes
`π(W) ≤ H¹` and by the coboundaries it contains, `#W = #π(W) · #(W ⊓ B¹)`; when the conditions
are invariant under coboundaries, `B¹ ≤ W` and `#W · #H⁰ = #π(W) · #M`.

All statements are about `Nat.card`, so they hold with no finiteness hypothesis: when one side is
infinite, `Nat.card` of it is `0` and so is the other side.

## Main results

* `TauCeti.ContCohomology.natCard_Z1`: `#Z¹ = #H¹ · #B¹`.
* `TauCeti.ContCohomology.natCard_B1_mul_natCard_H0`: `#B¹ · #H⁰ = #M`, from
  `TauCeti.ContCohomology.ker_d0` and `TauCeti.ContCohomology.range_d0`, which identify the
  kernel and the image of `d⁰` with `H⁰` and `B¹`.
* `TauCeti.ContCohomology.natCard_Z1_mul_natCard_H0`: `#Z¹ · #H⁰ = #H¹ · #M`.
* `TauCeti.ContCohomology.natCard_of_le_Z1`: for `W ≤ Z¹`, `#W = #π(W) · #(W ⊓ B¹)`, where
  `π(W) ≤ H¹` is the image of `W` under the class map `TauCeti.ContCohomology.H1pi`;
  `TauCeti.ContCohomology.natCard_addSubgroup_Z1` is the same count for a subgroup of the
  subtype `Z¹`.
* `TauCeti.ContCohomology.natCard_of_B1_le_of_le_Z1` and
  `TauCeti.ContCohomology.natCard_mul_natCard_H0_of_B1_le_of_le_Z1`: for `B¹ ≤ W ≤ Z¹`,
  `#W = #π(W) · #B¹` and `#W · #H⁰ = #π(W) · #M`.
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

variable {G M}

/-- **Counting a group of `1`-cocycles by classes.** For a subgroup `W` of `Z¹(G, M)`,
`#W = #π(W) · #(W ⊓ B¹)`, where `π : Z¹ → H¹` is the class map `H1pi`: the restriction of `π`
to `W` has image `π(W)` and kernel `W ⊓ B¹`. -/
theorem natCard_addSubgroup_Z1 (W : AddSubgroup (Z1 G M)) :
    Nat.card W =
      Nat.card (W.map (H1pi G M)) * Nat.card (W ⊓ (B1 G M).addSubgroupOf (Z1 G M) :) := by
  rw [← AddSubgroup.relIndex_mul_card (H1pi G M).ker W, AddSubgroup.relIndex_ker, ker_H1pi,
    inf_comm]

/-- **Cocycle counts from class counts.** For a group `W ≤ Z¹(G, M)` of `1`-cocycles,
`#W = #π(W) · #(W ⊓ B¹)`, where `π(W) ≤ H¹(G, M)` is the group of classes of elements of `W`. -/
theorem natCard_of_le_Z1 {W : AddSubgroup (G → M)} (hW : W ≤ Z1 G M) :
    Nat.card W = Nat.card ((W.addSubgroupOf (Z1 G M)).map (H1pi G M)) *
      Nat.card (W ⊓ B1 G M :) := by
  have hinf : W.addSubgroupOf (Z1 G M) ⊓ (B1 G M).addSubgroupOf (Z1 G M) =
      (W ⊓ B1 G M).addSubgroupOf (Z1 G M) := by
    ext; simp [AddSubgroup.mem_addSubgroupOf]
  rw [← Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hW).toEquiv, natCard_addSubgroup_Z1,
    hinf, Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (inf_le_left.trans hW)).toEquiv]

/-- **Cocycle counts from class counts, containing the coboundaries.** For a group
`B¹(G, M) ≤ W ≤ Z¹(G, M)` of `1`-cocycles, `#W = #π(W) · #B¹`, where `π(W) ≤ H¹(G, M)` is the
group of classes of elements of `W`. -/
theorem natCard_of_B1_le_of_le_Z1 {W : AddSubgroup (G → M)} (hB : B1 G M ≤ W)
    (hW : W ≤ Z1 G M) :
    Nat.card W = Nat.card ((W.addSubgroupOf (Z1 G M)).map (H1pi G M)) * Nat.card (B1 G M) := by
  rw [natCard_of_le_Z1 hW, inf_eq_right.2 hB]

/-- **Cocycle counts from class counts, against the coefficients.** For a group
`B¹(G, M) ≤ W ≤ Z¹(G, M)` of `1`-cocycles, `#W · #H⁰ = #π(W) · #M`, where `π(W) ≤ H¹(G, M)` is
the group of classes of elements of `W`. -/
theorem natCard_mul_natCard_H0_of_B1_le_of_le_Z1 {W : AddSubgroup (G → M)} (hB : B1 G M ≤ W)
    (hW : W ≤ Z1 G M) :
    Nat.card W * Nat.card (H0 G M) =
      Nat.card ((W.addSubgroupOf (Z1 G M)).map (H1pi G M)) * Nat.card M := by
  rw [natCard_of_B1_le_of_le_Z1 hB hW, mul_assoc, natCard_B1_mul_natCard_H0]

end DegreeOne

/-! ### Checks

For `C₂ = ℤˣ` acting on `𝔽₂` (necessarily trivially), `Z¹ = H¹` has two elements and `B¹ = 0`.
For `C₂ = ℤˣ` acting on `ℤ/3` by sign, `Z¹ = B¹` has three elements and `H¹ = 0`. The zero
subgroup gives `1 = 1 · 1`. -/

section Checks

example : Nat.card (Z1 ℤˣ (ZMod 2)) = 2 ∧ Nat.card (B1 ℤˣ (ZMod 2)) = 1 ∧
    Nat.card (((Z1 ℤˣ (ZMod 2)).addSubgroupOf (Z1 ℤˣ (ZMod 2))).map (H1pi ℤˣ (ZMod 2))) = 2 := by
  have hsmul (g : ℤˣ) (m : ZMod 2) : g • m = m := by
    rcases Int.units_eq_one_or g with rfl | rfl
    · exact one_smul _ m
    · rw [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul]
      exact (by decide : ∀ m : ZMod 2, -m = m) m
  have hB : B1 ℤˣ (ZMod 2) = ⊥ := B1_eq_bot_of_smul_eq_self hsmul
  -- A cocycle for the trivial action is determined by its value at `-1`, which is arbitrary.
  let e : Z1 ℤˣ (ZMod 2) →+ ZMod 2 :=
    { toFun f := (f : ℤˣ → ZMod 2) (-1), map_zero' := rfl, map_add' _ _ := rfl }
  have hZ : Nat.card (Z1 ℤˣ (ZMod 2)) = 2 := by
    refine (Nat.card_eq_of_bijective e ⟨fun f f' h ↦ Subtype.ext (funext fun g ↦ ?_),
      fun m ↦ ?_⟩).trans (Nat.card_zmod 2)
    · rcases Int.units_eq_one_or g with rfl | rfl
      · rw [map_one_of_mem_Z1 f.property, map_one_of_mem_Z1 f'.property]
      · exact h
    · refine ⟨⟨fun g ↦ if g = 1 then 0 else m,
        mem_Z1_iff.2 ⟨continuous_of_discreteTopology, fun g h ↦ ?_⟩⟩, ?_⟩
      · rw [hsmul]
        rcases Int.units_eq_one_or g with rfl | rfl <;>
          rcases Int.units_eq_one_or h with rfl | rfl <;>
          simp [show (-1 : ℤˣ) ≠ 1 by decide, CharTwo.add_self_eq_zero]
      · simp [e, show (-1 : ℤˣ) ≠ 1 by decide]
  have hinf : (Z1 ℤˣ (ZMod 2) ⊓ B1 ℤˣ (ZMod 2) : AddSubgroup _) = ⊥ := by rw [hB, inf_bot_eq]
  refine ⟨hZ, by rw [hB, AddSubgroup.card_bot], ?_⟩
  rwa [natCard_of_le_Z1 le_rfl, hinf, AddSubgroup.card_bot, mul_one] at hZ

example : Nat.card (Z1 ℤˣ (ZMod 3)) = 3 ∧ Nat.card (B1 ℤˣ (ZMod 3)) = 3 ∧
    Nat.card (((Z1 ℤˣ (ZMod 3)).addSubgroupOf (Z1 ℤˣ (ZMod 3))).map (H1pi ℤˣ (ZMod 3))) = 1 := by
  -- `H¹` is killed by `#C₂ = 2` and by `3`.
  have hH1 (x : H1 ℤˣ (ZMod 3)) : x = 0 := by
    have h3 : (3 : ℕ) • x = 0 := nsmul_H1_eq_zero (fun m ↦ by fin_cases m <;> decide) x
    have h2 : (2 : ℕ) • x = 0 := by simpa using natCard_nsmul_H1_eq_zero x
    simpa [succ_nsmul, h2] using h3
  have hH0 : H0 ℤˣ (ZMod 3) = ⊥ := by
    ext m
    refine ⟨fun h ↦ ?_, fun h ↦ (AddSubgroup.mem_bot.1 h) ▸ (H0 ℤˣ (ZMod 3)).zero_mem⟩
    have := (FixedPoints.mem_addSubgroup _ _ m).1 h (-1)
    rw [Units.smul_def, Units.val_neg, Units.val_one, neg_smul, one_smul] at this
    exact (by decide : ∀ m : ZMod 3, -m = m → m = 0) m this
  have hπ : Nat.card (((Z1 ℤˣ (ZMod 3)).addSubgroupOf (Z1 ℤˣ (ZMod 3))).map
      (H1pi ℤˣ (ZMod 3))) = 1 :=
    Nat.card_eq_one_iff_unique.2
      ⟨⟨fun a b ↦ Subtype.ext ((hH1 a).trans (hH1 b).symm)⟩, ⟨0⟩⟩
  have hW := natCard_mul_natCard_H0_of_B1_le_of_le_Z1 (B1_le_Z1 ℤˣ (ZMod 3)) le_rfl
  have hB := natCard_of_B1_le_of_le_Z1 (B1_le_Z1 ℤˣ (ZMod 3)) le_rfl
  rw [hH0, hπ, AddSubgroup.card_bot, Nat.card_zmod] at hW
  rw [hπ] at hB
  omega

example : Nat.card (((⊥ : AddSubgroup (ℤˣ → ZMod 3)).addSubgroupOf (Z1 ℤˣ (ZMod 3))).map
      (H1pi ℤˣ (ZMod 3))) * Nat.card ((⊥ : AddSubgroup (ℤˣ → ZMod 3)) ⊓ B1 ℤˣ (ZMod 3) :) = 1 := by
  rw [← natCard_of_le_Z1 bot_le, AddSubgroup.card_bot]

end Checks

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
