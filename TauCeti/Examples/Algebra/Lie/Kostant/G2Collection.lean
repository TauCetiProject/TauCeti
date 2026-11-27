/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.G2.Collection
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.Basic

/-!
# G₂ collection on the integral root table

The two exceptional shapes are checked with a supplied Chevalley table, retaining its actual
signs. Degrees `(3, 2)` in the triple string and `(1, 2)` in the short pair both detect the
highest-root coefficient. These are identities in the rational enveloping algebra of the
Chevalley algebra with its full cocharacter lattice.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open scoped TensorProduct
open TauCeti.Associative RootPairing.ChevalleyLieAlgebra

namespace TauCeti.Examples

variable (c : DynkinType.g2SimplyConnectedRootDatum.ChevalleyConstants)

local notation "e" => (fun i : Fin 12 ↦ _root_.UniversalEnvelopingAlgebra.ι ℚ
  ((1 : ℚ) ⊗ₜ[ℤ] root c i))
local notation "a" => c.structConst 0 1
local notation "b" => Int.sign (c.structConst 0 2)
local notation "d" => Int.sign (c.structConst 0 3)
local notation "f" => Int.sign (c.structConst 3 2)

private theorem g2_root_equations :
    DynkinType.g2SimplyConnectedRootDatum.root 2 =
        DynkinType.g2SimplyConnectedRootDatum.root 0 +
          DynkinType.g2SimplyConnectedRootDatum.root 1 ∧
      DynkinType.g2SimplyConnectedRootDatum.root 3 =
        DynkinType.g2SimplyConnectedRootDatum.root 0 +
          DynkinType.g2SimplyConnectedRootDatum.root 2 ∧
      DynkinType.g2SimplyConnectedRootDatum.root 4 =
        DynkinType.g2SimplyConnectedRootDatum.root 0 +
          DynkinType.g2SimplyConnectedRootDatum.root 3 ∧
      DynkinType.g2SimplyConnectedRootDatum.root 5 =
        DynkinType.g2SimplyConnectedRootDatum.root 3 +
          DynkinType.g2SimplyConnectedRootDatum.root 2 := by
  simp only [DynkinType.g2SimplyConnectedRootDatum_root, DynkinType.g2Root_apply]
  decide +kernel

/-- The four-factor collection detects the separate highest-root bracket sign. -/
theorem g2_triple_degree_three_two :
    dividedPower 3 (e 0) * dividedPower 2 (e 1) =
      dividedPower 2 (e 1) * dividedPower 3 (e 0) +
        (a ^ 2 * b * f) • e 5 +
        (a * b * d) • (e 1 * e 4) +
        (a * b) • (e 1 * e 3 * e 0) +
        a • (e 1 * e 2 * dividedPower 2 (e 0)) +
        (a ^ 2 * b) • (e 2 * e 3) +
        a ^ 2 • (dividedPower 2 (e 2) * e 0) := by
  obtain ⟨h₂, h₃, h₄, h₅⟩ := g2_root_equations
  have hi : chainG2Index 3 2 =
      {(0, 0, 0, 0), (0, 0, 0, 1), (0, 0, 1, 0), (0, 1, 0, 0),
        (1, 0, 0, 0), (1, 1, 0, 0), (2, 0, 0, 0)} := by
    ext ⟨i, j, k, l⟩
    simp only [mem_chainG2Index, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [dividedPower_root_mul_of_g2_triple c h₂ h₃ h₄ h₅, hi]
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, zero_ne_one,
    and_false, and_true, and_self, OfNat.zero_ne_ofNat, or_self, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton, pow_zero, pow_one, tsub_zero, tsub_self,
    mul_zero, dividedPower_zero, dividedPower_one, one_mul, mul_one, one_ne_zero,
    Nat.add_one_sub_one, Nat.reduceSub, OfNat.one_ne_ofNat, add_assoc, mul_assoc, pow_two]
  module

/-- The short-pair highest-root coefficient is the product of the two actual bracket signs. -/
theorem g2_short_pair_degree_one_two :
    dividedPower 1 (e 0) * dividedPower 2 (e 2) =
      dividedPower 2 (e 2) * e 0 + (2 * b) • (e 2 * e 3) + (3 * (b * f)) • e 5 := by
  obtain ⟨_, h₃, h₄, h₅⟩ := g2_root_equations
  have hi : g2ShortPairIndex 1 2 = {(0, 0, 0), (0, 0, 1), (1, 0, 0)} := by
    ext ⟨i, j, k⟩
    simp only [mem_g2ShortPairIndex, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [dividedPower_root_mul_of_g2_short_pair c h₃ h₄ h₅, hi]
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, zero_ne_one,
    and_false, and_true, and_self, or_self, not_false_eq_true,
    Finset.sum_insert, Finset.sum_singleton, pow_zero, pow_one, add_zero, zero_add,
    tsub_zero, tsub_self, mul_zero, dividedPower_zero, dividedPower_one, one_mul, mul_one,
    one_ne_zero, Nat.add_one_sub_one, mul_assoc, add_assoc]
  abel

namespace Embedded

open RootPairing.EmbeddedG2

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] [Finite ι]
  (P : RootPairing ι ℤ X Y) [P.EmbeddedG2] (c : P.ChevalleyConstants)

local notation "E" => (fun i : ι ↦ _root_.UniversalEnvelopingAlgebra.ι ℚ
  ((1 : ℚ) ⊗ₜ[ℤ] root c i))

private theorem root_equations :
    P.root (shortAddLong P) = P.root (short P) + P.root (long P) ∧
      P.root (twoShortAddLong P) = P.root (short P) + P.root (shortAddLong P) ∧
      P.root (threeShortAddLong P) = P.root (short P) + P.root (twoShortAddLong P) ∧
      P.root (threeShortAddTwoLong P) =
        P.root (twoShortAddLong P) + P.root (shortAddLong P) := by
  have h₂ := shortAddLongRoot_eq P
  have h₃ := twoShortAddLongRoot_eq P
  have h₄ := threeShortAddLongRoot_eq P
  have h₅ := threeShortAddTwoLongRoot_eq P
  simp only [shortRoot, longRoot, shortAddLongRoot, twoShortAddLongRoot,
    threeShortAddLongRoot, threeShortAddTwoLongRoot] at h₂ h₃ h₄ h₅
  refine ⟨h₂, ?_, ?_, ?_⟩
  · rw [h₃, h₂]
    module
  · rw [h₄, h₃]
    module
  · rw [h₅, h₃, h₂]
    module

-- The distinguished pairs instantiate the formulas in an arbitrary ambient root pairing.

example (m n : ℕ) :
    dividedPower m (E (short P)) * dividedPower n (E (long P)) =
      ∑ p ∈ chainG2Index m n,
        (c.structConst (short P) (long P) ^ p.1 *
          (c.structConst (short P) (long P) * (c.structConst (short P) (shortAddLong P)).sign) ^
            p.2.1 *
          (c.structConst (short P) (long P) * (c.structConst (short P) (shortAddLong P)).sign *
            (c.structConst (short P) (twoShortAddLong P)).sign) ^ p.2.2.1 *
          (c.structConst (short P) (long P) ^ 2 * (c.structConst (short P) (shortAddLong P)).sign *
            (c.structConst (twoShortAddLong P) (shortAddLong P)).sign) ^ p.2.2.2) •
          (dividedPower (n - p.1 - p.2.1 - p.2.2.1 - 2 * p.2.2.2) (E (long P)) *
            dividedPower p.1 (E (shortAddLong P)) * dividedPower p.2.1 (E (twoShortAddLong P)) *
            dividedPower p.2.2.1 (E (threeShortAddLong P)) * dividedPower p.2.2.2 (E
              (threeShortAddTwoLong P)) *
            dividedPower (m - p.1 - 2 * p.2.1 - 3 * p.2.2.1 - 3 * p.2.2.2) (E (short P))) := by
  obtain ⟨h₂, h₃, h₄, h₅⟩ := root_equations P
  exact dividedPower_root_mul_of_g2_triple c h₂ h₃ h₄ h₅ m n

example (m n : ℕ) :
    dividedPower m (E (short P)) * dividedPower n (E (shortAddLong P)) =
      ∑ p ∈ g2ShortPairIndex m n,
        ((2 ^ p.1 * 3 ^ (p.2.1 + p.2.2) : ℤ) *
          (c.structConst (short P) (shortAddLong P)).sign ^ p.1 *
          ((c.structConst (short P) (shortAddLong P)).sign * (c.structConst (short P)
            (twoShortAddLong P)).sign) ^ p.2.1 *
          ((c.structConst (short P) (shortAddLong P)).sign * (c.structConst (twoShortAddLong P)
            (shortAddLong P)).sign) ^ p.2.2) •
          (dividedPower (n - p.1 - p.2.1 - 2 * p.2.2) (E (shortAddLong P)) *
            dividedPower p.1 (E (twoShortAddLong P)) * dividedPower p.2.1 (E (threeShortAddLong P))
              *
            dividedPower p.2.2 (E (threeShortAddTwoLong P)) *
            dividedPower (m - p.1 - 2 * p.2.1 - p.2.2) (E (short P))) := by
  obtain ⟨_, h₃, h₄, h₅⟩ := root_equations P
  exact dividedPower_root_mul_of_g2_short_pair c h₃ h₄ h₅ m n

end Embedded

end TauCeti.Examples
