/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.CosetMinimum

/-!
# Orders and pairings of Conway--Sloane glue labels

A printed glue label `a` of a simply-laced Dynkin type `t` names the class
`t.glueLabelEquiv ht a` of the glue alphabet `t.glueAlphabet ht`, which is the discriminant
quadratic module of the root lattice of `t` (`TauCeti.DynkinType.glueAlphabetIsometry`).  The
shortest norm and half-norm of each label are computed in
`TauCeti.LinearAlgebra.IntegralLattice.RootLattice.GlueAlphabet.CosetMinimum`.  This file records
the two remaining invariants of the labels, as computable functions of the printed labels, and
checks them against the glue alphabet.

The **additive order** of the class of a label is `glueLabelOrder`:

| type | label `a` | order |
| --- | --- | --- |
| `Aₙ` | `0 ≤ a ≤ n` | `(n + 1) / gcd(n + 1, a)` |
| `Dₙ` | `0`, spinor `1`, vector `2`, cospinor `3` | `1`, `2` or `4`, `2`, `2` or `4` |
| `E₆` | `0`, `1`, `2` | `1`, `3`, `3` |
| `E₇` | `0`, `1` | `1`, `2` |
| `E₈` | `0` | `1` |

where the spinor classes of `Dₙ` have order `2` for even `n` and `4` for odd `n`.

The **discriminant pairing** of the classes of two labels is the reduction modulo `ℤ` of the
Conway--Sloane value `glueLabelPairing`:

| type | labels `a`, `b` | value |
| --- | --- | --- |
| `Aₙ` | `0 ≤ a ≤ b ≤ n` | `a (n + 1 - b) / (n + 1)` |
| `Dₙ` | `1·1`, `3·3`; `2·2`; `1·2`, `2·3`; `1·3` | `n/4`; `1`; `1/2`; `(n - 2)/4` |
| `E₆` | `1·1`, `2·2`; `1·2` | `4/3`; `2/3` |
| `E₇` | `1·1` | `3/2` |

with value `0` whenever one of the labels is `0`.  On the diagonal the value is the shortest
norm `glueLabelMinimum` of the label (`glueLabelPairing_self`), consistently with the half-norm
computation `TauCeti.DynkinType.quadratic_glueAlphabet_eq_glueMinimum_div_two`.

The pairing is derived from the polar identity `b(x, y) = q(x + y) - q(x) - q(y)`, the label
addition `TauCeti.DynkinType.glueLabelAdd` and the half-norms `q(a) = μ(a)/2`; what remains is a
finite rational computation for each family, with the rank of `Dₙ` kept symbolic.

## Main declarations

* `TauCeti.DynkinType.glueLabelOrder`, `TauCeti.DynkinType.addOrderOf_glueLabelEquiv`: the
  additive order of the class of a printed label.
* `TauCeti.DynkinType.glueLabelPairing`, `TauCeti.DynkinType.pairing_glueLabelEquiv`: the
  discriminant pairing of the classes of two printed labels.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §§6--8,
  and Chapter 16, §1.
-/

public section

namespace TauCeti.DynkinType

/-! ## Orders of labels -/

/-- **The additive order of the class of the Conway--Sloane label** `a` of a simply-laced Dynkin
type (`addOrderOf_glueLabelEquiv`): `(n + 1) / gcd(n + 1, a)` for `Aₙ`; for `Dₙ`, `1` for the
label `0`, `2` for the vector label `2` and for the spinor labels `1`, `3` when `n` is even, and
`4` for the spinor labels when `n` is odd; `3` and `2` for the nonzero labels of `E₆` and `E₇`;
`1` for the only label of `E₈`.  The non-simply-laced types, which have no labels, are sent to
`1`. -/
@[expose] def glueLabelOrder : DynkinType → ℕ → ℕ
  | A n, a => (n + 1) / (n + 1).gcd a
  | D n, a => if a = 0 then 1 else if a = 2 ∨ Even n then 2 else 4
  | E6, a => if a = 0 then 1 else 3
  | E7, a => if a = 0 then 1 else 2
  | _, _ => 1

/-- The label `a` of `Aₙ` has order `(n + 1) / gcd(n + 1, a)`. -/
@[simp]
theorem glueLabelOrder_A (n a : ℕ) : (A n).glueLabelOrder a = (n + 1) / (n + 1).gcd a :=
  (rfl)

/-- The vector label of `Dₙ` has order `2`; the spinor labels have order `2` for even `n` and `4`
for odd `n`. -/
@[simp]
theorem glueLabelOrder_D (n a : ℕ) :
    (D n).glueLabelOrder a = if a = 0 then 1 else if a = 2 ∨ Even n then 2 else 4 :=
  (rfl)

/-- The nonzero labels of `E₆` have order `3`. -/
@[simp]
theorem glueLabelOrder_E6 (a : ℕ) : E6.glueLabelOrder a = if a = 0 then 1 else 3 :=
  (rfl)

/-- The nonzero label of `E₇` has order `2`. -/
@[simp]
theorem glueLabelOrder_E7 (a : ℕ) : E7.glueLabelOrder a = if a = 0 then 1 else 2 :=
  (rfl)

/-- The only label of `E₈` has order `1`. -/
@[simp]
theorem glueLabelOrder_E8 (a : ℕ) : E8.glueLabelOrder a = 1 :=
  (rfl)

/-- **The order of the class of a label is the order read off the printed label.** -/
@[simp]
theorem addOrderOf_glueLabelEquiv (t : DynkinType) (ht : t.IsSimplyLaced)
    (a : Fin t.glueLabelCount) :
    addOrderOf (t.glueLabelEquiv ht a) = t.glueLabelOrder a := by
  obtain ⟨a, ha⟩ := a
  cases t with
  | A n =>
    rw [glueLabelEquiv_A]
    exact ZMod.addOrderOf_coe a n.succ_ne_zero
  | D n =>
    simp only [glueLabelCount] at ha
    rcases Nat.even_or_odd n with hn | hn
    · let e := FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_even n ht hn)
      rw [← addOrderOf_injective (AddMonoidHom.ofClass e) (EquivLike.injective e),
        AddMonoidHom.coe_ofClass, glueLabelEquiv_D_of_even n ht hn]
      -- The carrier of the Klein four model is `ZMod 2 × ZMod 2` by definition.
      refine (Prod.addOrderOf_mk (a := ((a / 2 : ℕ) : ZMod 2)) (b := ((a % 2 : ℕ) : ZMod 2))).trans
        ?_
      interval_cases a <;> simp [hn, ZMod.addOrderOf_one]
    · let e := FiniteQuadraticModule.Isometry.ofEq (glueAlphabet_D_of_odd n ht hn)
      rw [← addOrderOf_injective (AddMonoidHom.ofClass e) (EquivLike.injective e),
        AddMonoidHom.coe_ofClass, glueLabelEquiv_D_of_odd n ht hn]
      -- The carrier of the odd model is `ZMod 4` by definition.
      refine (ZMod.addOrderOf_coe a four_ne_zero).trans ?_
      interval_cases a <;> simp [Nat.not_even_iff_odd.mpr hn]
  | E6 =>
    rw [glueLabelEquiv_E6]
    simp only [glueLabelCount] at ha
    -- The `E₆` alphabet is `ZMod 3` by definition.
    refine (ZMod.addOrderOf_coe a three_ne_zero).trans ?_
    interval_cases a <;> rfl
  | E7 =>
    rw [glueLabelEquiv_E7]
    simp only [glueLabelCount] at ha
    -- The `E₇` alphabet is `ZMod 2` by definition.
    refine (ZMod.addOrderOf_coe a two_ne_zero).trans ?_
    interval_cases a <;> rfl
  | E8 => rw [glueLabelEquiv_E8, addOrderOf_zero, glueLabelOrder_E8]
  | B n => exact absurd ht (not_isSimplyLaced_B n)
  | C n => exact absurd ht (not_isSimplyLaced_C n)
  | F4 => exact absurd ht not_isSimplyLaced_F4
  | G2 => exact absurd ht not_isSimplyLaced_G2

/-! ## Pairings of labels -/

/-- **The Conway--Sloane pairing value of the labels** `a` and `b` of a simply-laced Dynkin type,
whose reduction modulo `ℤ` is the discriminant pairing of their classes
(`pairing_glueLabelEquiv`): `min(a, b) (n + 1 - max(a, b)) / (n + 1)` for `Aₙ`; for `Dₙ`, `n/4`
for two equal spinor labels, `1` for two vector labels, `1/2` for a vector and a spinor label and
`(n - 2)/4` for the two different spinor labels; `4/3` and `2/3` for equal and different nonzero
labels of `E₆`; `3/2` for the nonzero label of `E₇`; and `0` whenever a label is `0`, for `E₈`, and
for the non-simply-laced types, which have no labels. -/
@[expose] def glueLabelPairing : DynkinType → ℕ → ℕ → ℚ
  | A n, a, b => (min a b : ℕ) * (n + 1 - (max a b : ℕ)) / (n + 1)
  | D n, a, b =>
    if a = 0 ∨ b = 0 then 0 else if a = 2 ∧ b = 2 then 1 else if a = 2 ∨ b = 2 then 1 / 2
    else if a = b then (n : ℚ) / 4 else ((n : ℚ) - 2) / 4
  | E6, a, b => if a = 0 ∨ b = 0 then 0 else if a = b then 4 / 3 else 2 / 3
  | E7, a, b => if a = 0 ∨ b = 0 then 0 else 3 / 2
  | _, _, _ => 0

/-- The labels `a` and `b` of `Aₙ` pair to `min(a, b) (n + 1 - max(a, b)) / (n + 1)`. -/
@[simp]
theorem glueLabelPairing_A (n a b : ℕ) :
    (A n).glueLabelPairing a b = (min a b : ℕ) * (n + 1 - (max a b : ℕ)) / (n + 1) :=
  (rfl)

/-- The pairing values of the labels `0`, spinor `1`, vector `2`, cospinor `3` of `Dₙ`. -/
@[simp]
theorem glueLabelPairing_D (n a b : ℕ) :
    (D n).glueLabelPairing a b =
      if a = 0 ∨ b = 0 then 0 else if a = 2 ∧ b = 2 then 1 else if a = 2 ∨ b = 2 then 1 / 2
      else if a = b then (n : ℚ) / 4 else ((n : ℚ) - 2) / 4 :=
  (rfl)

/-- The nonzero labels of `E₆` pair to `4/3` when equal and to `2/3` when different. -/
@[simp]
theorem glueLabelPairing_E6 (a b : ℕ) :
    E6.glueLabelPairing a b = if a = 0 ∨ b = 0 then 0 else if a = b then 4 / 3 else 2 / 3 :=
  (rfl)

/-- The nonzero label of `E₇` pairs with itself to `3/2`. -/
@[simp]
theorem glueLabelPairing_E7 (a b : ℕ) :
    E7.glueLabelPairing a b = if a = 0 ∨ b = 0 then 0 else 3 / 2 :=
  (rfl)

/-- The only label of `E₈` pairs to `0`. -/
@[simp]
theorem glueLabelPairing_E8 (a b : ℕ) : E8.glueLabelPairing a b = 0 :=
  (rfl)

/-- The pairing value of two labels is symmetric. -/
theorem glueLabelPairing_comm (t : DynkinType) (a b : ℕ) :
    t.glueLabelPairing a b = t.glueLabelPairing b a := by
  cases t with
  | A n => rw [glueLabelPairing_A, glueLabelPairing_A, min_comm, max_comm]
  | D n =>
    simp only [glueLabelPairing_D]
    split_ifs <;> first | rfl | omega
  | E6 =>
    simp only [glueLabelPairing_E6]
    split_ifs <;> first | rfl | omega
  | E7 => simp only [glueLabelPairing_E7, or_comm]
  | E8 | B _ | C _ | F4 | G2 => rfl

/-- **The pairing value of a label with itself is its shortest norm.** -/
@[simp]
theorem glueLabelPairing_self (t : DynkinType) (a : ℕ) :
    t.glueLabelPairing a a = t.glueLabelMinimum a := by
  cases t with
  | A n => simp
  | D n => by_cases h0 : a = 0 <;> by_cases h2 : a = 2 <;> simp [h0, h2]
  | E6 | E7 => simp
  | E8 | B _ | C _ | F4 | G2 => rfl

/-- In `Aₙ`, the pairing value of two labels differs by an integer from half the defect
`μ(a + b) - μ(a) - μ(b)` of their shortest norms. -/
private theorem exists_intCast_eq_glueLabelPairing_sub_A (n : ℕ) {a b : ℕ} (ha : a < n + 1)
    (hb : b < n + 1) :
    ∃ k : ℤ, (k : ℚ) = (A n).glueLabelPairing a b - ((A n).glueLabelMinimum
      ((A n).glueLabelAdd a b) - (A n).glueLabelMinimum a - (A n).glueLabelMinimum b) / 2 := by
  -- The statement is symmetric in the two labels, so we may assume `a ≤ b`.
  wlog hab : a ≤ b generalizing a b
  · obtain ⟨k, hk⟩ := this hb ha (by omega)
    refine ⟨k, ?_⟩
    rw [hk, glueLabelPairing_comm, glueLabelAdd_A, glueLabelAdd_A, Nat.add_comm b a,
      sub_right_comm _ ((A n).glueLabelMinimum b)]
  have hN : (n : ℚ) + 1 ≠ 0 := by positivity
  simp only [glueLabelPairing_A, glueLabelMinimum_A, glueLabelAdd_A, min_eq_left hab,
    max_eq_right hab]
  -- Split on whether the sum `a + b` wraps around `n + 1`.
  rcases lt_or_ge (a + b) (n + 1) with hs | hs
  · refine ⟨a, ?_⟩
    rw [Nat.mod_eq_of_lt hs]
    push_cast
    field_simp
    ring
  · refine ⟨n + 1 - b, ?_⟩
    rw [Nat.mod_eq_sub_mod hs, Nat.mod_eq_of_lt (by omega), Nat.cast_sub hs]
    push_cast
    field_simp
    ring

/-- In `Dₙ`, the pairing value of two labels differs by an integer from half the defect
`μ(a + b) - μ(a) - μ(b)` of their shortest norms. -/
private theorem exists_intCast_eq_glueLabelPairing_sub_D (n : ℕ) {a b : ℕ} (ha : a < 4)
    (hb : b < 4) :
    ∃ k : ℤ, (k : ℚ) = (D n).glueLabelPairing a b - ((D n).glueLabelMinimum
      ((D n).glueLabelAdd a b) - (D n).glueLabelMinimum a - (D n).glueLabelMinimum b) / 2 := by
  -- Write `n = 2m` or `n = 2m + 1`; the differences `0` and `1` are closed by `norm_num`, and the
  -- others are `2`, `m` and (for even `n` and the two spinor labels) `m - 1`.
  rcases Nat.even_or_odd n with hn | hn
  · obtain ⟨m, rfl⟩ := hn
    have hn : Even (m + m) := ⟨m, rfl⟩
    interval_cases a <;> interval_cases b <;>
      simp only [glueLabelPairing_D, glueLabelMinimum_D, glueLabelAdd_D, hn] <;>
      norm_num
    -- The remaining labels are `1·1`, `1·3`, `2·2`, `3·1`, `3·3`.
    all_goals first
      | (refine ⟨2, ?_⟩; push_cast; ring1)
      | (refine ⟨m, ?_⟩; push_cast; ring1)
      | (refine ⟨m - 1, ?_⟩; push_cast; ring1)
  · obtain ⟨m, rfl⟩ := hn
    have hn : ¬Even (2 * m + 1) := Nat.not_even_iff_odd.mpr (odd_two_mul_add_one m)
    interval_cases a <;> interval_cases b <;>
      simp only [glueLabelPairing_D, glueLabelMinimum_D, glueLabelAdd_D, hn] <;>
      norm_num
    -- The remaining labels are `1·1`, `1·3`, `2·2`, `3·1`, `3·3`.
    all_goals first
      | (refine ⟨2, ?_⟩; push_cast; ring1)
      | (refine ⟨m, ?_⟩; push_cast; ring1)

/-- The pairing value of two labels differs by an integer from half the defect
`μ(a + b) - μ(a) - μ(b)` of their shortest norms, where `a + b` is the label sum. -/
private theorem exists_intCast_eq_glueLabelPairing_sub (t : DynkinType) {a b : ℕ}
    (ha : a < t.glueLabelCount) (hb : b < t.glueLabelCount) :
    ∃ k : ℤ, (k : ℚ) = t.glueLabelPairing a b - (t.glueLabelMinimum (t.glueLabelAdd a b) -
      t.glueLabelMinimum a - t.glueLabelMinimum b) / 2 := by
  cases t with
  | A n => exact exists_intCast_eq_glueLabelPairing_sub_A n ha hb
  | D n => exact exists_intCast_eq_glueLabelPairing_sub_D n ha hb
  | E6 =>
    -- The three nonzero differences are all `2`.
    simp only [glueLabelCount] at ha hb
    interval_cases a <;> interval_cases b <;> norm_num [glueLabelPairing_E6]
    all_goals exact ⟨2, by norm_num⟩
  | E7 =>
    simp only [glueLabelCount] at ha hb
    -- The only nonzero difference is `3`.
    interval_cases a <;> interval_cases b <;> norm_num [glueLabelPairing_E7]
    exact ⟨3, by norm_num⟩
  | E8 | B _ | C _ | F4 | G2 => exact ⟨0, by simp [glueLabelPairing, glueLabelMinimum]⟩

/-- **The discriminant pairing of the classes of two labels is the Conway--Sloane value**
`glueLabelPairing a b`, reduced modulo `ℤ`. -/
@[simp]
theorem pairing_glueLabelEquiv (t : DynkinType) (ht : t.IsSimplyLaced)
    (a b : Fin t.glueLabelCount) :
    (t.glueAlphabet ht).toFiniteBilinearModule.pairing (t.glueLabelEquiv ht a)
        (t.glueLabelEquiv ht b) = (t.glueLabelPairing a b : AddCircle (1 : ℚ)) := by
  rw [← FiniteQuadraticModule.polar_eq_pairing, QuadraticMap.polar, ← glueLabelEquiv_glueLabelAdd]
  simp only [quadratic_glueAlphabet_eq_glueMinimum_div_two, glueMinimum_glueLabelEquiv,
    ← AddCircle.coe_sub]
  -- Both sides are classes of rationals that differ by an integer.
  obtain ⟨k, hk⟩ := t.exists_intCast_eq_glueLabelPairing_sub a.isLt b.isLt
  rw [eq_comm, ← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  exact ⟨k, by rw [zsmul_eq_mul, mul_one, hk]; ring⟩

end TauCeti.DynkinType
