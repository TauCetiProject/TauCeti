/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DividedPowers.RootString.G2.Basic

/-!
# Normal ordering divided powers for the short pair in type `G₂`

Let `x`, `y`, `z`, `w`, and `s` belong to an associative algebra over `ℚ`, with

```text
x * y = y * x + 2 • z,   x * z = z * x + 3 • w,   z * y = y * z + 3 • s,
```

`w` and `s` commuting with `x`, `s` commuting with `y`, and `z`, `w`, `s` commuting pairwise.
This is the second configuration of positive roots in type `G₂`: if `x` and `y` are the root
vectors of `α` and `α + β`, respectively, then `z`, `w`, and `s` belong to the root spaces of
`2α + β`, `3α + β`, and `3α + 2β`. The last root has coordinates `(1, 2)` relative to the pair
`α`, `α + β`, and enters through the bracket of `z` with `y`.

For these canonically normalized Chevalley root vectors, the resulting straightening rule is

```text
x⁽ᵐ⁾ y⁽ⁿ⁾ = ∑ b + c + 2d ≤ n, b + 2c + d ≤ m,
              2ᵇ 3ᶜ⁺ᵈ • y⁽ⁿ⁻ᵇ⁻ᶜ⁻²ᵈ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ s⁽ᵈ⁾ x⁽ᵐ⁻ᵇ⁻²ᶜ⁻ᵈ⁾.
```

Its displayed coefficients are natural numbers. Together with
`TauCeti.Associative.dividedPower_mul_dividedPower_of_commutator_eq_three_nsmul`, this covers the
two nontrivial normal-ordering configurations needed for type `G₂`.

## Main results

* `TauCeti.Associative.dividedPower_mul_dividedPower_of_g2_short_pair`: the Chevalley-basis
  straightening rule for the pair `α`, `α + β` in type `G₂`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

namespace TauCeti.Associative

open Finset

variable {A : Type*} [Semiring A] [Algebra ℚ A] {x y z w s : A}

/-! ## Moving one element across a normal-ordered monomial -/

-- Moving `x` across `y⁽ᵃ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ s⁽ᵈ⁾` releases one term for each of the three positive
-- combinations of the roots represented by `x` and `y`.
private theorem mul_dividedPower_shortPairMonomial (hxy : x * y = y * x + z)
    (hxz : x * z = z * x + 2 • w) (hzy : z * y = y * z + 2 • s) (hxw : Commute x w)
    (hxs : Commute x s) (hys : Commute y s) (hzw : Commute z w) (hzs : Commute z s)
    (hws : Commute w s) (a b c d : ℕ) :
    x * (dividedPower a y * (dividedPower b z * (dividedPower c w * dividedPower d s))) =
      dividedPower a y * (dividedPower b z * (dividedPower c w * dividedPower d s)) * x +
        (if 0 < a then (b + 1) • (dividedPower (a - 1) y *
          (dividedPower (b + 1) z * (dividedPower c w * dividedPower d s))) else 0) +
        (if 0 < b then (2 * (c + 1)) • (dividedPower a y *
          (dividedPower (b - 1) z * (dividedPower (c + 1) w * dividedPower d s))) else 0) +
        (if 1 < a then (d + 1) • (dividedPower (a - 2) y *
          (dividedPower b z * (dividedPower c w * dividedPower (d + 1) s))) else 0) := by
  have hxW : Commute x (dividedPower c w) := by
    simpa using commute_dividedPower_dividedPower hxw 1 c
  have hxS : Commute x (dividedPower d s) := by
    simpa using commute_dividedPower_dividedPower hxs 1 d
  have hsZ : Commute s (dividedPower b z) := by
    simpa using commute_dividedPower_dividedPower hzs.symm 1 b
  have hsW : Commute s (dividedPower c w) := by
    simpa using commute_dividedPower_dividedPower hws.symm 1 c
  have e0 : x * (dividedPower c w * dividedPower d s) =
      dividedPower c w * dividedPower d s * x := by
    rw [← mul_assoc, hxW.eq, mul_assoc, hxS.eq, ← mul_assoc]
  have e1 : x * (dividedPower b z * (dividedPower c w * dividedPower d s)) =
      dividedPower b z * (dividedPower c w * dividedPower d s) * x +
        (if 0 < b then dividedPower (b - 1) z * (2 • w) else 0) *
          (dividedPower c w * dividedPower d s) := by
    rw [← mul_assoc, mul_dividedPower_of_commutator_eq' hxz (hzw.smul_right 2) b, add_mul,
      mul_assoc, e0, ← mul_assoc]
  rw [← mul_assoc, mul_dividedPower_of_commutator_eq_two_nsmul hxy hzy hys a, add_mul,
    add_mul, mul_assoc, e1, mul_add, ← mul_assoc]
  have tA : (if 0 < a then dividedPower (a - 1) y * z else 0) *
      (dividedPower b z * (dividedPower c w * dividedPower d s)) =
      if 0 < a then (b + 1) • (dividedPower (a - 1) y *
        (dividedPower (b + 1) z * (dividedPower c w * dividedPower d s))) else 0 := by
    split_ifs with ha
    · rw [mul_assoc, ← mul_assoc z, self_mul_dividedPower, smul_mul_assoc, mul_smul_comm]
    · rw [zero_mul]
  have tB : dividedPower a y * ((if 0 < b then dividedPower (b - 1) z * (2 • w) else 0) *
      (dividedPower c w * dividedPower d s)) =
      if 0 < b then (2 * (c + 1)) • (dividedPower a y *
        (dividedPower (b - 1) z * (dividedPower (c + 1) w * dividedPower d s))) else 0 := by
    split_ifs with hb
    · rw [mul_assoc, smul_mul_assoc, ← mul_assoc w, self_mul_dividedPower, smul_mul_assoc,
        smul_smul, mul_smul_comm, mul_smul_comm]
    · rw [zero_mul, mul_zero]
  have hmove : s * (dividedPower b z * (dividedPower c w * dividedPower d s)) =
      (d + 1) • (dividedPower b z * (dividedPower c w * dividedPower (d + 1) s)) := by
    rw [← mul_assoc, hsZ.eq, mul_assoc, ← mul_assoc s, hsW.eq, mul_assoc,
      self_mul_dividedPower, mul_smul_comm, mul_smul_comm]
  have tC : (if 1 < a then dividedPower (a - 2) y * s else 0) *
      (dividedPower b z * (dividedPower c w * dividedPower d s)) =
      if 1 < a then (d + 1) • (dividedPower (a - 2) y *
        (dividedPower b z * (dividedPower c w * dividedPower (d + 1) s))) else 0 := by
    split_ifs with ha
    · rw [mul_assoc, hmove, mul_smul_comm]
    · rw [zero_mul]
  rw [tA, tB, tC]
  abel

/-! ## The divided-power series of the inner derivation -/

/-- The exponents in the `k`-th divided power of `ad x` applied to `y⁽ⁿ⁾`: triples `(b, c, d)`
with `b + c + 2d ≤ n` and `b + 2c + d = k`. -/
private def g2ShortPairSeriesIndex (n k : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  {p ∈ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1) |
    p.1 + p.2.1 + 2 * p.2.2 ≤ n ∧ p.1 + 2 * p.2.1 + p.2.2 = k}

private theorem mem_g2ShortPairSeriesIndex {n k : ℕ} {p : ℕ × ℕ × ℕ} :
    p ∈ g2ShortPairSeriesIndex n k ↔
      p.1 + p.2.1 + 2 * p.2.2 ≤ n ∧ p.1 + 2 * p.2.1 + p.2.2 = k := by
  simp only [g2ShortPairSeriesIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- The normal-ordered monomial attached to a triple of short-pair root exponents. -/
private noncomputable def g2ShortPairMonomial (y z w s : A) (n : ℕ) (p : ℕ × ℕ × ℕ) : A :=
  dividedPower (n - p.1 - p.2.1 - 2 * p.2.2) y *
    (dividedPower p.1 z * (dividedPower p.2.1 w * dividedPower p.2.2 s))

/-- The `k`-th divided power of `ad x` applied to `y⁽ⁿ⁾`, expressed in normal order. -/
private noncomputable def g2ShortPairSeries (y z w s : A) (n k : ℕ) : A :=
  ∑ p ∈ g2ShortPairSeriesIndex n k, g2ShortPairMonomial y z w s n p

private theorem g2ShortPairSeries_zero (n : ℕ) :
    g2ShortPairSeries y z w s n 0 = dividedPower n y := by
  have hindex : g2ShortPairSeriesIndex n 0 = {(0, 0, 0)} := by
    ext ⟨b, c, d⟩
    simp only [mem_g2ShortPairSeriesIndex, Finset.mem_singleton, Prod.mk.injEq]
    omega
  rw [g2ShortPairSeries, hindex]
  simp [g2ShortPairMonomial]

private theorem mem_filter_g2ShortPairSeriesIndex {n k : ℕ}
    {P : (ℕ × ℕ × ℕ) → Prop} [DecidablePred P] {p : ℕ × ℕ × ℕ} :
    p ∈ {p ∈ g2ShortPairSeriesIndex n k | P p} ↔
      (p.1 + p.2.1 + 2 * p.2.2 ≤ n ∧ p.1 + 2 * p.2.1 + p.2.2 = k) ∧ P p := by
  rw [Finset.mem_filter, mem_g2ShortPairSeriesIndex]

private theorem sum_g2ShortPairMonomial_shift {n k : ℕ}
    {P Q : (ℕ × ℕ × ℕ) → Prop} [DecidablePred P] [DecidablePred Q]
    (f finv : (ℕ × ℕ × ℕ) → (ℕ × ℕ × ℕ)) (coeff : (ℕ × ℕ × ℕ) → ℕ)
    (hf : ∀ p, (p.1 + p.2.1 + 2 * p.2.2 ≤ n ∧
        p.1 + 2 * p.2.1 + p.2.2 = k) ∧ P p →
      ((f p).1 + (f p).2.1 + 2 * (f p).2.2 ≤ n ∧
        (f p).1 + 2 * (f p).2.1 + (f p).2.2 = k + 1) ∧ Q (f p))
    (hfinv : ∀ q, (q.1 + q.2.1 + 2 * q.2.2 ≤ n ∧
        q.1 + 2 * q.2.1 + q.2.2 = k + 1) ∧ Q q →
      ((finv q).1 + (finv q).2.1 + 2 * (finv q).2.2 ≤ n ∧
        (finv q).1 + 2 * (finv q).2.1 + (finv q).2.2 = k) ∧ P (finv q))
    (hleft : ∀ p, (p.1 + p.2.1 + 2 * p.2.2 ≤ n ∧
        p.1 + 2 * p.2.1 + p.2.2 = k) ∧ P p → finv (f p) = p)
    (hright : ∀ q, (q.1 + q.2.1 + 2 * q.2.2 ≤ n ∧
        q.1 + 2 * q.2.1 + q.2.2 = k + 1) ∧ Q q → f (finv q) = q) :
    ∑ p ∈ {p ∈ g2ShortPairSeriesIndex n k | P p},
        (coeff (f p)) • g2ShortPairMonomial y z w s n (f p) =
      ∑ q ∈ {q ∈ g2ShortPairSeriesIndex n (k + 1) | Q q},
        coeff q • g2ShortPairMonomial y z w s n q :=
  Finset.sum_nbij' f finv
    (fun _ hp =>
      mem_filter_g2ShortPairSeriesIndex.mpr
        (hf _ (mem_filter_g2ShortPairSeriesIndex.mp hp)))
    (fun _ hq =>
      mem_filter_g2ShortPairSeriesIndex.mpr
        (hfinv _ (mem_filter_g2ShortPairSeriesIndex.mp hq)))
    (fun _ hp => hleft _ (mem_filter_g2ShortPairSeriesIndex.mp hp))
    (fun _ hq => hright _ (mem_filter_g2ShortPairSeriesIndex.mp hq))
    (fun _ _ => rfl)

private theorem mul_g2ShortPairMonomial (hxy : x * y = y * x + z)
    (hxz : x * z = z * x + 2 • w) (hzy : z * y = y * z + 2 • s) (hxw : Commute x w)
    (hxs : Commute x s) (hys : Commute y s) (hzw : Commute z w) (hzs : Commute z s)
    (hws : Commute w s) (n : ℕ) (p : ℕ × ℕ × ℕ) :
    x * g2ShortPairMonomial y z w s n p = g2ShortPairMonomial y z w s n p * x +
      (if 0 < n - p.1 - p.2.1 - 2 * p.2.2 then
        (p.1 + 1) • g2ShortPairMonomial y z w s n (p.1 + 1, p.2.1, p.2.2) else 0) +
      (if 0 < p.1 then (2 * (p.2.1 + 1)) •
        g2ShortPairMonomial y z w s n (p.1 - 1, p.2.1 + 1, p.2.2) else 0) +
      (if 1 < n - p.1 - p.2.1 - 2 * p.2.2 then
        (p.2.2 + 1) • g2ShortPairMonomial y z w s n (p.1, p.2.1, p.2.2 + 1) else 0) := by
  obtain ⟨b, c, d⟩ := p
  have hA : n - (b + 1) - c - 2 * d = n - b - c - 2 * d - 1 := by omega
  have hB : 0 < b → n - (b - 1) - (c + 1) - 2 * d = n - b - c - 2 * d := by omega
  have hC : 1 < n - b - c - 2 * d →
      n - b - c - 2 * (d + 1) = n - b - c - 2 * d - 2 := by omega
  have eqB : (if 0 < b then (2 * (c + 1)) •
        (dividedPower (n - (b - 1) - (c + 1) - 2 * d) y *
          (dividedPower (b - 1) z * (dividedPower (c + 1) w * dividedPower d s))) else 0) =
      (if 0 < b then (2 * (c + 1)) • (dividedPower (n - b - c - 2 * d) y *
        (dividedPower (b - 1) z * (dividedPower (c + 1) w * dividedPower d s))) else 0) := by
    split_ifs with hb
    · rw [hB hb]
    · rfl
  have eqC : (if 1 < n - b - c - 2 * d then (d + 1) •
        (dividedPower (n - b - c - 2 * (d + 1)) y *
          (dividedPower b z * (dividedPower c w * dividedPower (d + 1) s))) else 0) =
      (if 1 < n - b - c - 2 * d then (d + 1) •
        (dividedPower (n - b - c - 2 * d - 2) y *
          (dividedPower b z * (dividedPower c w * dividedPower (d + 1) s))) else 0) := by
    split_ifs with hc
    · rw [hC hc]
    · rfl
  simp only [g2ShortPairMonomial]
  rw [mul_dividedPower_shortPairMonomial hxy hxz hzy hxw hxs hys hzw hzs hws
    (n - b - c - 2 * d) b c d, hA, eqB, eqC]

private theorem mul_g2ShortPairSeries (hxy : x * y = y * x + z)
    (hxz : x * z = z * x + 2 • w) (hzy : z * y = y * z + 2 • s) (hxw : Commute x w)
    (hxs : Commute x s) (hys : Commute y s) (hzw : Commute z w) (hzs : Commute z s)
    (hws : Commute w s) (n k : ℕ) :
    x * g2ShortPairSeries y z w s n k =
      g2ShortPairSeries y z w s n k * x + (k + 1) • g2ShortPairSeries y z w s n (k + 1) := by
  classical
  -- The reindexing architecture follows Claude's proof of the other type-`G₂` configuration in
  -- `TauCeti.RingTheory.DividedPowers.RootString.G2.Basic`.
  have hshiftA : ∑ p ∈ {p ∈ g2ShortPairSeriesIndex n k |
        0 < n - p.1 - p.2.1 - 2 * p.2.2},
        (p.1 + 1) • g2ShortPairMonomial y z w s n (p.1 + 1, p.2.1, p.2.2) =
      ∑ q ∈ {q ∈ g2ShortPairSeriesIndex n (k + 1) | 0 < q.1},
        q.1 • g2ShortPairMonomial y z w s n q := by
    refine sum_g2ShortPairMonomial_shift (fun p => (p.1 + 1, p.2.1, p.2.2))
      (fun q => (q.1 - 1, q.2.1, q.2.2)) (fun q => q.1) ?_ ?_ ?_ ?_
    · rintro ⟨b, c, d⟩ hp
      dsimp at *; omega
    · rintro ⟨b, c, d⟩ hq
      dsimp at *; omega
    · rintro ⟨b, c, d⟩ _
      simp
    · rintro ⟨b, c, d⟩ hq
      simp [Nat.sub_add_cancel hq.2]
  have hshiftB : ∑ p ∈ {p ∈ g2ShortPairSeriesIndex n k | 0 < p.1},
        (2 * (p.2.1 + 1)) •
          g2ShortPairMonomial y z w s n (p.1 - 1, p.2.1 + 1, p.2.2) =
      ∑ q ∈ {q ∈ g2ShortPairSeriesIndex n (k + 1) | 0 < q.2.1},
        (2 * q.2.1) • g2ShortPairMonomial y z w s n q := by
    refine sum_g2ShortPairMonomial_shift (fun p => (p.1 - 1, p.2.1 + 1, p.2.2))
      (fun q => (q.1 + 1, q.2.1 - 1, q.2.2)) (fun q => 2 * q.2.1) ?_ ?_ ?_ ?_
    · rintro ⟨b, c, d⟩ hp
      dsimp at *; omega
    · rintro ⟨b, c, d⟩ hq
      dsimp at *; omega
    · rintro ⟨b, c, d⟩ hp
      simp [Nat.sub_add_cancel hp.2]
    · rintro ⟨b, c, d⟩ hq
      simp [Nat.sub_add_cancel hq.2]
  have hshiftC : ∑ p ∈ {p ∈ g2ShortPairSeriesIndex n k |
        1 < n - p.1 - p.2.1 - 2 * p.2.2},
        (p.2.2 + 1) • g2ShortPairMonomial y z w s n (p.1, p.2.1, p.2.2 + 1) =
      ∑ q ∈ {q ∈ g2ShortPairSeriesIndex n (k + 1) | 0 < q.2.2},
        q.2.2 • g2ShortPairMonomial y z w s n q := by
    refine sum_g2ShortPairMonomial_shift (fun p => (p.1, p.2.1, p.2.2 + 1))
      (fun q => (q.1, q.2.1, q.2.2 - 1)) (fun q => q.2.2) ?_ ?_ ?_ ?_
    · rintro ⟨b, c, d⟩ hp
      dsimp at *; omega
    · rintro ⟨b, c, d⟩ hq
      dsimp at *; omega
    · rintro ⟨b, c, d⟩ _
      simp
    · rintro ⟨b, c, d⟩ hq
      simp [Nat.sub_add_cancel hq.2]
  have hcombine : ∑ q ∈ {q ∈ g2ShortPairSeriesIndex n (k + 1) | 0 < q.1},
        q.1 • g2ShortPairMonomial y z w s n q +
      ∑ q ∈ {q ∈ g2ShortPairSeriesIndex n (k + 1) | 0 < q.2.1},
        (2 * q.2.1) • g2ShortPairMonomial y z w s n q +
      ∑ q ∈ {q ∈ g2ShortPairSeriesIndex n (k + 1) | 0 < q.2.2},
        q.2.2 • g2ShortPairMonomial y z w s n q =
      (k + 1) • g2ShortPairSeries y z w s n (k + 1) := by
    rw [Finset.sum_filter_of_ne (fun q _ hq => Nat.pos_of_ne_zero fun h => hq (by simp [h])),
      Finset.sum_filter_of_ne (fun q _ hq => Nat.pos_of_ne_zero fun h => hq (by simp [h])),
      Finset.sum_filter_of_ne (fun q _ hq => Nat.pos_of_ne_zero fun h => hq (by simp [h])),
      g2ShortPairSeries, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [← add_smul, ← add_smul]
    congr 1
    have := (mem_g2ShortPairSeriesIndex.mp hq).2
    omega
  rw [g2ShortPairSeries, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_congr rfl fun p _ =>
      mul_g2ShortPairMonomial hxy hxz hzy hxw hxs hys hzw hzs hws n p]
  simp only [Finset.sum_add_distrib, ← Finset.sum_filter]
  rw [hshiftA, hshiftB, hshiftC, add_assoc, add_assoc, ← add_assoc, ← hcombine]
  abel

/-! ## The straightening rule -/

/-- The triples of exponents in the short-pair straightening rule for type `G₂`, corresponding to
the roots `2α + β`, `3α + β`, and `3α + 2β`. -/
def g2ShortPairIndex (m n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  {p ∈ range (n + 1) ×ˢ range (n + 1) ×ˢ range (n + 1) |
    p.1 + p.2.1 + 2 * p.2.2 ≤ n ∧ p.1 + 2 * p.2.1 + p.2.2 ≤ m}

/-- Membership in `g2ShortPairIndex` in terms of its two mathematical inequalities. -/
@[simp]
theorem mem_g2ShortPairIndex {m n : ℕ} {p : ℕ × ℕ × ℕ} :
    p ∈ g2ShortPairIndex m n ↔
      p.1 + p.2.1 + 2 * p.2.2 ≤ n ∧ p.1 + 2 * p.2.1 + p.2.2 ≤ m := by
  simp only [g2ShortPairIndex, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  omega

/-- Auxiliary coefficient-one normal ordering for the scaled short-pair root vectors in type
`G₂`. -/
private theorem dividedPower_mul_dividedPower_of_g2_short_pair_scaled
    (hxy : x * y = y * x + z)
    (hxz : x * z = z * x + 2 • w) (hzy : z * y = y * z + 2 • s) (hxw : Commute x w)
    (hxs : Commute x s) (hys : Commute y s) (hzw : Commute z w) (hzs : Commute z s)
    (hws : Commute w s) (m n : ℕ) :
    dividedPower m x * dividedPower n y =
      ∑ p ∈ g2ShortPairIndex m n,
        dividedPower (n - p.1 - p.2.1 - 2 * p.2.2) y * dividedPower p.1 z *
          dividedPower p.2.1 w * dividedPower p.2.2 s *
          dividedPower (m - p.1 - 2 * p.2.1 - p.2.2) x := by
  classical
  have hseries := dividedPower_mul_of_ad_dividedPower_series (x := x)
    (d := g2ShortPairSeries y z w s n)
    (fun k => mul_g2ShortPairSeries hxy hxz hzy hxw hxs hys hzw hzs hws n k) m
  rw [g2ShortPairSeries_zero] at hseries
  rw [hseries]
  simp only [mul_assoc]
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun p : ℕ × ℕ × ℕ => p.1 + 2 * p.2.1 + p.2.2) (t := range (m + 1))
    (fun p hp => Finset.mem_range.mpr (by have := mem_g2ShortPairIndex.mp hp; omega))
    (fun p => dividedPower (n - p.1 - p.2.1 - 2 * p.2.2) y *
      (dividedPower p.1 z * (dividedPower p.2.1 w * (dividedPower p.2.2 s *
        dividedPower (m - p.1 - 2 * p.2.1 - p.2.2) x))))]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkm : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hfib : {p ∈ g2ShortPairIndex m n | p.1 + 2 * p.2.1 + p.2.2 = k} =
      g2ShortPairSeriesIndex n k := by
    ext p
    simp only [Finset.mem_filter, mem_g2ShortPairIndex, mem_g2ShortPairSeriesIndex]
    omega
  rw [hfib, g2ShortPairSeries, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := (mem_g2ShortPairSeriesIndex.mp hp).2
  have hq : m - p.1 - 2 * p.2.1 - p.2.2 = m - k := by omega
  rw [hq, g2ShortPairMonomial]
  simp only [mul_assoc]

/-- **Chevalley-basis normal ordering for the short pair in type `G₂`.** Suppose

```text
x * y = y * x + 2 • z,   x * z = z * x + 3 • w,   z * y = y * z + 3 • s,
```

that `w` and `s` commute with `x`, `s` commutes with `y`, and `z`, `w`, `s` commute pairwise. Then

```text
x⁽ᵐ⁾ y⁽ⁿ⁾ = ∑ b + c + 2d ≤ n, b + 2c + d ≤ m,
              2ᵇ 3ᶜ⁺ᵈ • y⁽ⁿ⁻ᵇ⁻ᶜ⁻²ᵈ⁾ z⁽ᵇ⁾ w⁽ᶜ⁾ s⁽ᵈ⁾ x⁽ᵐ⁻ᵇ⁻²ᶜ⁻ᵈ⁾.
```

Here `x`, `y`, `z`, `w`, and `s` model Chevalley root vectors for `α`, `α + β`, `2α + β`,
`3α + β`, and `3α + 2β`, respectively. The powers of `2` and `3` are the structure constants
introduced by passing from the scaled vectors `2 • z`, `3 • w`, and `3 • s` back to the
Chevalley basis. In particular, every displayed coefficient is a natural number. -/
theorem dividedPower_mul_dividedPower_of_g2_short_pair (hxy : x * y = y * x + 2 • z)
    (hxz : x * z = z * x + 3 • w) (hzy : z * y = y * z + 3 • s) (hxw : Commute x w)
    (hxs : Commute x s) (hys : Commute y s) (hzw : Commute z w) (hzs : Commute z s)
    (hws : Commute w s) (m n : ℕ) :
    dividedPower m x * dividedPower n y =
      ∑ p ∈ g2ShortPairIndex m n,
        (2 ^ p.1 * 3 ^ (p.2.1 + p.2.2)) •
          (dividedPower (n - p.1 - p.2.1 - 2 * p.2.2) y * dividedPower p.1 z *
            dividedPower p.2.1 w * dividedPower p.2.2 s *
            dividedPower (m - p.1 - 2 * p.2.1 - p.2.2) x) := by
  classical
  have hxy' : x * y = y * x + (2 : ℚ) • z := by
    simpa only [← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_ofNat] using hxy
  have hxz' : x * ((2 : ℚ) • z) = (2 : ℚ) • z * x + 2 • ((3 : ℚ) • w) := by
    rw [mul_smul_comm, smul_mul_assoc, hxz, smul_add]
    simp only [← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_ofNat]
  have hzy' : (2 : ℚ) • z * y = y * ((2 : ℚ) • z) + 2 • ((3 : ℚ) • s) := by
    rw [smul_mul_assoc, mul_smul_comm, hzy, smul_add]
    simp only [← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_ofNat]
  have h := dividedPower_mul_dividedPower_of_g2_short_pair_scaled hxy' hxz' hzy'
    (hxw.smul_right (3 : ℚ)) (hxs.smul_right (3 : ℚ)) (hys.smul_right (3 : ℚ))
    ((hzw.smul_left (2 : ℚ)).smul_right (3 : ℚ))
    ((hzs.smul_left (2 : ℚ)).smul_right (3 : ℚ))
    ((hws.smul_left (3 : ℚ)).smul_right (3 : ℚ)) m n
  rw [h]
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [dividedPower_smul, mul_assoc, mul_smul_comm, smul_mul_assoc, smul_smul,
    ← Nat.cast_smul_eq_nsmul ℚ]
  congr 1
  norm_num
  ring

end TauCeti.Associative
