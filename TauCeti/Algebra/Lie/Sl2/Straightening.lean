/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Associative
public import Mathlib.RingTheory.Binomial
public import TauCeti.Algebra.Module.Rat
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Algebra.Polynomial.Semiconj
import TauCeti.RingTheory.Binomial
import Mathlib.Tactic.NoncommRing

/-!
# Rank-one Kostant straightening

This file proves the rank-one straightening formula for divided powers in an associative
`ℚ`-algebra. If `H`, `E`, and `F` satisfy the `sl₂` commutator relations, then

```text
E * F - F * E = H,   H * E - E * H = 2 • E,   H * F - F * H = -(2 • F),

E⁽ᵐ⁾ F⁽ⁿ⁾ =
  ∑ k ≤ min(m,n), F⁽ⁿ⁻ᵏ⁾ (H - m - n + 2k choose k) E⁽ᵐ⁻ᵏ⁾.
```

All coefficients are generalized binomial coefficients, so the formula is integral even though
the individual divided powers are defined using rational factorial denominators. This is the
rank-one normal-ordering relation needed for the integral PBW theorem for a Kostant form.

The proof follows the usual induction on `m`. Moving one additional `E` through the lowering
divided power produces two adjacent summands. `TauCeti.Ring.mul_weighted_choose_add_mul_choose`
combines their Cartan coefficients without division.

## Main results

* `TauCeti.Sl2.dividedPower_e_mul_dividedPower_f`: the rank-one Kostant straightening formula in an
  arbitrary associative `ℚ`-algebra satisfying the three displayed commutator relations.
* `TauCeti.Sl2.dividedPower_ι_e_mul_dividedPower_ι_f`: its specialization to the canonical map
  into a universal enveloping algebra, stated from the corresponding Lie-bracket relations.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.2.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Sl2

open Finset
open Associative

universe u

attribute [local instance] TauCeti.moduleNNRat

variable {A : Type u} [Ring A] [Algebra ℚ A]

private noncomputable def straighteningSummand (H E F : A) (m n k : ℕ) : A :=
  dividedPower (n - k) F *
    Ring.choose (H - (m + n : ℕ) + (2 * k : ℕ)) k *
      dividedPower (m - k) E

private theorem straighteningSummand_zero_left (H E F : A) (n : ℕ) :
    straighteningSummand H E F 0 n 0 = dividedPower n F := by
  simp [straighteningSummand]

private theorem shifted_cartan_mul_e {R : Type*} [NonAssocRing R] {H E : R}
    (hhe : H * E - E * H = 2 • E) (a b : ℕ) :
    (H - (a : R) + (b : R)) * E = E * (H - (a : R) + (b : R) + 2) := by
  have h : SemiconjBy E (H + 2) H := by
    simpa only [SemiconjBy, mul_add, nsmul_eq_mul', Nat.cast_ofNat] using
      ((sub_eq_iff_eq_add').mp hhe).symm
  simpa only [add_sub_right_comm, add_right_comm] using
    ((h.sub_right (Nat.cast_commute a E).symm).add_right
      (Nat.cast_commute b E).symm).eq.symm

private noncomputable def raisedStraighteningSummand (H E F : A) (m n k : ℕ) : A :=
  dividedPower (n - (k + 1)) F *
    ((H - (m + 1 + n : ℕ) + (2 * (k + 1) : ℕ)) + (m - k : ℕ)) *
      Ring.choose (H - (m + n : ℕ) + (2 * k : ℕ)) k *
        dividedPower (m - k) E

private noncomputable def keptStraighteningSummand (H E F : A) (m n k : ℕ) : A :=
  (m + 1 - k) •
    (dividedPower (n - k) F *
      Ring.choose (H - (m + 1 + n : ℕ) + (2 * k : ℕ) - 1) k *
        dividedPower (m + 1 - k) E)

private theorem e_mul_straighteningSummand_of_lt {H E F : A}
    (hef : E * F - F * E = H) (hhe : H * E - E * H = 2 • E)
    (hhf : H * F - F * H = -(2 • F)) {m n k : ℕ} (hk : k ≤ m) (hkn : k < n) :
    E * straighteningSummand H E F m n k =
      keptStraighteningSummand H E F m n k +
        raisedStraighteningSummand H E F m n k := by
  have hnk : n - k = (n - k - 1) + 1 := by omega
  have harg :
      H - (m + n : ℕ) + (2 * k : ℕ) - 2 =
        H - (m + 1 + n : ℕ) + (2 * k : ℕ) - 1 := by
    push_cast
    have htwo : (2 : A) = 1 + 1 := by norm_num
    simp only [htwo]
    noncomm_ring
  have hfactor :
      H - ((n - k - 1 : ℕ) : A) =
        (H - (m + 1 + n : ℕ) + (2 * (k + 1) : ℕ)) + (m - k : ℕ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ n - k), Nat.cast_sub (Nat.le_of_lt hkn),
      Nat.cast_sub hk]
    push_cast
    have htwo : (2 : A) = 1 + 1 := by norm_num
    simp only [htwo]
    noncomm_ring
    norm_num
  have hm : m + 1 - k = m - k + 1 := by omega
  have hmove := pow_mul_ringChoose k
    (shifted_cartan_mul_e hhe (m + n) (2 * k)) (Nat.cast_commute 2 E) 1
  simp only [pow_one, one_nsmul] at hmove
  have hfirst :
      E * (Ring.choose (H - (m + n : ℕ) + (2 * k : ℕ)) k *
          dividedPower (m - k) E) =
        (m - k + 1) •
          (Ring.choose (H - (m + 1 + n : ℕ) + (2 * k : ℕ) - 1) k *
            dividedPower (m + 1 - k) E) := by
    rw [← mul_assoc, hmove, harg, mul_assoc, self_mul_dividedPower, hm]
    simp only [nsmul_eq_mul']
    rw [mul_assoc]
  rw [straighteningSummand, mul_assoc, ← mul_assoc E]
  rw [hnk, e_mul_dividedPower_succ_f hef hhf]
  rw [add_mul]
  rw [mul_assoc (dividedPower (n - k - 1 + 1) F), hfirst]
  simp only [nsmul_eq_mul']
  rw [mul_assoc]
  simp only [keptStraighteningSummand, raisedStraighteningSummand]
  rw [hfactor]
  have hsub : n - (k + 1) = n - k - 1 := by omega
  rw [hnk, hsub]
  simp only [nsmul_eq_mul']
  rw [hm]
  noncomm_ring

private theorem e_mul_straighteningSummand_of_eq {H E F : A}
    (hhe : H * E - E * H = 2 • E) {m n k : ℕ} (hk : k ≤ m) (hkn : k = n) :
    E * straighteningSummand H E F m n k =
      keptStraighteningSummand H E F m n k := by
  subst n
  have harg :
      H - (m + k : ℕ) + (2 * k : ℕ) - 2 =
        H - (m + 1 + k : ℕ) + (2 * k : ℕ) - 1 := by
    push_cast
    have htwo : (2 : A) = 1 + 1 := by norm_num
    simp only [htwo]
    noncomm_ring
  simp only [straighteningSummand, Nat.sub_self, dividedPower_zero, one_mul]
  have hmove := pow_mul_ringChoose k
    (shifted_cartan_mul_e hhe (m + k) (2 * k)) (Nat.cast_commute 2 E) 1
  simp only [pow_one, one_nsmul] at hmove
  rw [← mul_assoc, hmove, harg, mul_assoc, self_mul_dividedPower]
  have hm : m + 1 - k = m - k + 1 := by omega
  simp only [keptStraighteningSummand, Nat.sub_self, dividedPower_zero, one_mul]
  rw [hm]
  simp only [nsmul_eq_mul']
  rw [mul_assoc]

private theorem keptStraighteningSummand_zero (H E F : A) (m n : ℕ) :
    keptStraighteningSummand H E F m n 0 =
      (m + 1) • straighteningSummand H E F (m + 1) n 0 := by
  simp [keptStraighteningSummand, straighteningSummand]

private theorem kept_add_raised_pred {H E F : A} (m n j : ℕ) (hj0 : 0 < j)
    (hjm : j ≤ m + 1) :
    keptStraighteningSummand H E F m n j +
        raisedStraighteningSummand H E F m n (j - 1) =
      (m + 1) • straighteningSummand H E F (m + 1) n j := by
  let r : A := H - (m + 1 + n : ℕ) + (2 * j : ℕ)
  have hj : (j - 1) + 1 = j := by omega
  have hcoef := TauCeti.Ring.mul_weighted_choose_add_mul_choose
    r (m + 1 - j : ℕ) (j - 1)
  simp only [hj, ← nsmul_eq_mul] at hcoef
  rw [← add_nsmul, Nat.sub_add_cancel hjm] at hcoef
  have hm : m - (j - 1) = m + 1 - j := by omega
  have harg :
      H - (m + n : ℕ) + (2 * (j - 1) : ℕ) = r - 1 := by
    dsimp only [r]
    push_cast [Nat.cast_sub (by omega : 1 ≤ j)]
    noncomm_ring
  have htargetArg : H - (m + 1 + n : ℕ) + (2 * j : ℕ) = r := by rfl
  simp only [keptStraighteningSummand, raisedStraighteningSummand,
    straighteningSummand, hj, hm, harg, htargetArg]
  simpa only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_assoc] using
    congrArg (fun c ↦ dividedPower (n - j) F * c * dividedPower (m + 1 - j) E) hcoef

private theorem straightening_step {H E F : A}
    (hef : E * F - F * E = H) (hhe : H * E - E * H = 2 • E)
    (hhf : H * F - F * H = -(2 • F)) (m n : ℕ)
    (ih : dividedPower m E * dividedPower n F =
      ∑ k ∈ range (min m n + 1), straighteningSummand H E F m n k) :
    dividedPower (m + 1) E * dividedPower n F =
      ∑ k ∈ range (min (m + 1) n + 1), straighteningSummand H E F (m + 1) n k := by
  -- Cancel the extra factor after moving one raising generator through the sum.
  let := HasUniqueDiv.of_module_rat A
  apply (nsmul_right_inj (n := m + 1) (by omega)).mp
  have hleft :
      (m + 1) • (dividedPower (m + 1) E * dividedPower n F) =
        E * ∑ k ∈ range (min m n + 1), straighteningSummand H E F m n k := by
    rw [succ_nsmul_dividedPower_succ_mul, ih]
  rw [hleft, mul_sum]
  let K := keptStraighteningSummand H E F m n
  let R := raisedStraighteningSummand H E F m n
  let T := fun k ↦ (m + 1) • straighteningSummand H E F (m + 1) n k
  -- The new endpoint vanishes when the raising degree limits the range.
  by_cases hmn : m < n
  · have hmin : min m n = m := min_eq_left (Nat.le_of_lt hmn)
    have hminSucc : min (m + 1) n = m + 1 := min_eq_left hmn
    rw [hmin, hminSucc]
    have hcombine :
        ∑ j ∈ range (m + 2), T j = ∑ k ∈ range (m + 1), (K k + R k) := by
      have h := Finset.sum_range_succ_eq_sum_range_add
        (f := T) (g := K) (h := R) (n := m + 1)
        (keptStraighteningSummand_zero H E F m n).symm
        (fun k hk ↦ by
          simpa only [Nat.add_sub_cancel] using
            (kept_add_raised_pred m n (k + 1) (by omega) (by omega)).symm)
      have hbound : K (m + 1) = 0 := by simp [K, keptStraighteningSummand]
      simpa only [hbound, add_zero] using h
    rw [Finset.smul_sum]
    rw [hcombine]
    apply sum_congr rfl
    intro k hk
    have hkm := mem_range.mp hk
    dsimp only [K, R]
    exact e_mul_straighteningSummand_of_lt hef hhe hhf
      (Nat.le_of_lt_succ hkm) (by omega)
  -- Otherwise the lowering degree limits the range, retaining the last kept summand.
  · have hnm : n ≤ m := by omega
    have hmin : min m n = n := min_eq_right hnm
    have hminSucc : min (m + 1) n = n := min_eq_right (by omega)
    rw [hmin, hminSucc]
    have hcombine :
        ∑ j ∈ range (n + 1), T j = (∑ k ∈ range n, (K k + R k)) + K n := by
      apply Finset.sum_range_succ_eq_sum_range_add
      · exact (keptStraighteningSummand_zero H E F m n).symm
      · intro k hk
        simpa only [Nat.add_sub_cancel] using
          (kept_add_raised_pred m n (k + 1) (by omega) (by omega)).symm
    rw [Finset.smul_sum]
    rw [hcombine, sum_range_succ]
    congr 1
    · apply sum_congr rfl
      intro k hk
      have hkn := mem_range.mp hk
      exact e_mul_straighteningSummand_of_lt hef hhe hhf
        (by omega) hkn
    · exact e_mul_straighteningSummand_of_eq hhe hnm rfl

/-- **The rank-one Kostant straightening formula.** If `H`, `E`, and `F` satisfy the `sl₂`
commutator relations in an associative `ℚ`-algebra, then the product of a raising divided power
and a lowering divided power is an integral sum in PBW order `F`, `H`, `E`.

The argument of the Cartan binomial is written as `H - (m + n) + 2 * k`; the natural numbers are
coerced to the algebra, so this is the standard coefficient `(H - m - n + 2k choose k)`. -/
theorem dividedPower_e_mul_dividedPower_f {H E F : A}
    (hef : E * F - F * E = H) (hhe : H * E - E * H = 2 • E)
    (hhf : H * F - F * H = -(2 • F)) (m n : ℕ) :
    dividedPower m E * dividedPower n F =
      ∑ k ∈ range (min m n + 1),
        dividedPower (n - k) F *
          Ring.choose (H - (m + n : ℕ) + (2 * k : ℕ)) k *
            dividedPower (m - k) E := by
  suffices dividedPower m E * dividedPower n F =
      ∑ k ∈ range (min m n + 1), straighteningSummand H E F m n k by
    simpa only [straighteningSummand]
  induction m with
  | zero => simp [straighteningSummand_zero_left]
  | succ m ih => exact straightening_step hef hhe hhf m n ih

section UniversalEnveloping

open _root_.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {h e f : L}

/-- The rank-one Kostant straightening formula in a universal enveloping algebra over `ℚ`,
stated from the three `sl₂` Lie-bracket relations. -/
theorem dividedPower_ι_e_mul_dividedPower_ι_f (hef : ⁅e, f⁆ = h) (hhe : ⁅h, e⁆ = 2 • e)
    (hhf : ⁅h, f⁆ = -(2 • f)) (m n : ℕ) :
    dividedPower m (ι ℚ e) * dividedPower n (ι ℚ f) =
      ∑ k ∈ range (min m n + 1),
        dividedPower (n - k) (ι ℚ f) *
          Ring.choose (ι ℚ h - (m + n : ℕ) + (2 * k : ℕ)) k *
            dividedPower (m - k) (ι ℚ e) := by
  apply dividedPower_e_mul_dividedPower_f
  · simpa only [LieRing.of_associative_ring_bracket, hef] using ((ι ℚ).map_lie e f).symm
  · simpa only [LieRing.of_associative_ring_bracket, hhe, map_nsmul] using
      ((ι ℚ).map_lie h e).symm
  · simpa only [LieRing.of_associative_ring_bracket, hhf, map_neg, map_nsmul] using
      ((ι ℚ).map_lie h f).symm

end UniversalEnveloping

end TauCeti.Sl2
