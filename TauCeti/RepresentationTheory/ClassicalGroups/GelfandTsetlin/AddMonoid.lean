/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Basic
public import Mathlib.Algebra.Order.Monoid.Basic
public import Mathlib.Algebra.Order.Pi

/-!
# The additive monoid of Gelfand-Tsetlin patterns

The interlacing inequalities defining a Gelfand-Tsetlin pattern are homogeneous linear
inequalities between entries, so patterns can be added entrywise: `TauCeti.GTPattern n` is an
ordered cancellative commutative monoid for the pointwise addition and order of its entries.  It is
not a group, since negating a pattern reverses its inequalities.  The polynomial patterns are the
nonnegative ones for this order: those whose top weight is polynomial.

## Main definitions

* `TauCeti.GTPattern.instAddCancelCommMonoid`, `TauCeti.GTPattern.instPartialOrder` and
  `TauCeti.GTPattern.instIsOrderedCancelAddMonoid`: the entrywise additive and order structures.
* `TauCeti.GTPattern.coeFnAddMonoidHom`: the array of entries, as an additive monoid homomorphism.
* `TauCeti.GTPattern.const n m`: the pattern all of whose informative entries equal `m`.

## Main results

* `TauCeti.GTPattern.zero_le_iff_topRow`: a pattern is nonnegative exactly when its top row is.
* `TauCeti.GTPattern.zero_le_iff_isPolynomial`: a pattern is nonnegative exactly when its top
  weight is polynomial.
-/

public section

namespace TauCeti

namespace GTPattern

variable {n : ℕ}

/-! ### The entrywise additive monoid -/

instance : Zero (GTPattern n) where
  zero := ⟨0, fun _ => rfl, fun _ _ => ⟨le_rfl, le_rfl⟩⟩

instance : Add (GTPattern n) where
  add P Q :=
    ⟨⇑P + ⇑Q, fun h => by simp [P.entry_eq_zero h, Q.entry_eq_zero h], fun hij hj =>
      ⟨add_le_add (P.entry_le_entry_succ_row hij hj) (Q.entry_le_entry_succ_row hij hj),
        add_le_add (P.entry_succ_succ_le_entry hj) (Q.entry_succ_succ_le_entry hj)⟩⟩

instance : SMul ℕ (GTPattern n) where
  smul k P :=
    ⟨k • ⇑P, fun h => by simp [P.entry_eq_zero h], fun hij hj => by
      simp only [Pi.smul_apply]
      exact ⟨by gcongr; exact P.entry_le_entry_succ_row hij hj,
        by gcongr; exact P.entry_succ_succ_le_entry hj⟩⟩

@[simp, norm_cast]
theorem coe_zero : ⇑(0 : GTPattern n) = 0 :=
  (rfl)

@[simp, norm_cast]
theorem coe_add (P Q : GTPattern n) : ⇑(P + Q) = ⇑P + ⇑Q :=
  (rfl)

@[simp, norm_cast]
theorem coe_nsmul (k : ℕ) (P : GTPattern n) : ⇑(k • P) = k • ⇑P :=
  (rfl)

theorem zero_apply (i j : ℕ) : (0 : GTPattern n) i j = 0 :=
  (rfl)

theorem add_apply (P Q : GTPattern n) (i j : ℕ) : (P + Q) i j = P i j + Q i j :=
  (rfl)

theorem nsmul_apply (k : ℕ) (P : GTPattern n) (i j : ℕ) : (k • P) i j = k • P i j :=
  (rfl)

/-- Gelfand-Tsetlin patterns form a cancellative commutative monoid under entrywise addition. -/
instance instAddCancelCommMonoid : AddCancelCommMonoid (GTPattern n) :=
  DFunLike.coe_injective.addCancelCommMonoid _ coe_zero coe_add fun _ _ => coe_nsmul _ _

/-- The array of entries of a pattern, as an additive monoid homomorphism. -/
def coeFnAddMonoidHom : GTPattern n →+ ℕ → ℕ → ℤ where
  toFun := (⇑)
  map_zero' := coe_zero
  map_add' := coe_add

@[simp]
theorem coeFnAddMonoidHom_apply (P : GTPattern n) : coeFnAddMonoidHom P = ⇑P :=
  (rfl)

@[simp, norm_cast]
theorem coe_sum {ι : Type*} (s : Finset ι) (P : ι → GTPattern n) :
    ⇑(∑ i ∈ s, P i) = ∑ i ∈ s, ⇑(P i) :=
  map_sum coeFnAddMonoidHom P s

@[simp]
theorem topRow_zero : (0 : GTPattern n).topRow = 0 := by
  funext i
  rw [topRow_apply, zero_apply, Pi.zero_apply]

@[simp]
theorem topRow_add (P Q : GTPattern n) : (P + Q).topRow = P.topRow + Q.topRow := by
  funext i
  rw [topRow_apply, add_apply, Pi.add_apply, topRow_apply, topRow_apply]

@[simp]
theorem topRow_nsmul (k : ℕ) (P : GTPattern n) : (k • P).topRow = k • P.topRow := by
  funext i
  rw [topRow_apply, nsmul_apply, Pi.smul_apply, topRow_apply]

/-! ### Constant patterns -/

/-- The constant pattern: every informative entry equals `m`.  Adding it to a pattern is the
determinant shift by `m` (`TauCeti.GTPattern.shift_eq_add_const`). -/
def const (n : ℕ) (m : ℤ) : GTPattern n where
  entry i j := if i < j ∧ j ≤ n then m else 0
  zeros' h := by
    rw [ite_eq_right_iff]
    omega
  interlacing' hij hj := by
    constructor <;> split_ifs <;> omega

theorem const_apply (m : ℤ) (i j : ℕ) : const n m i j = if i < j ∧ j ≤ n then m else 0 :=
  (rfl)

@[simp]
theorem const_apply_of_lt_of_le (m : ℤ) {i j : ℕ} (hij : i < j) (hj : j ≤ n) :
    const n m i j = m := by
  rw [const_apply, ite_eq_left_iff.2 fun h => absurd ⟨hij, hj⟩ h]

@[simp]
theorem topRow_const (m : ℤ) : (const n m).topRow = fun _ => m := by
  funext i
  rw [topRow_apply]
  exact const_apply_of_lt_of_le m i.2 le_rfl

@[simp]
theorem const_zero : const n 0 = 0 := by
  ext i j
  rw [const_apply, zero_apply, ite_self]

theorem const_add (m m' : ℤ) : const n (m + m') = const n m + const n m' := by
  ext i j
  rw [add_apply, const_apply, const_apply, const_apply]
  split_ifs <;> simp

/-! ### The entrywise order -/

/-- Gelfand-Tsetlin patterns are ordered entrywise. -/
instance instPartialOrder : PartialOrder (GTPattern n) :=
  PartialOrder.lift (⇑) DFunLike.coe_injective

@[simp, norm_cast]
theorem coe_le_coe {P Q : GTPattern n} : ⇑P ≤ ⇑Q ↔ P ≤ Q :=
  Iff.rfl

theorem le_def {P Q : GTPattern n} : P ≤ Q ↔ ∀ i j, P i j ≤ Q i j :=
  Iff.rfl

/-- The entrywise order is compatible with entrywise addition. -/
instance instIsOrderedCancelAddMonoid : IsOrderedCancelAddMonoid (GTPattern n) :=
  Function.Injective.isOrderedCancelAddMonoid _ coe_add coe_le_coe

theorem zero_le_iff {P : GTPattern n} : 0 ≤ P ↔ ∀ i j, 0 ≤ P i j :=
  le_def

/-- A pattern is nonnegative exactly when its top row is: every entry dominates an entry of the
top row. -/
theorem zero_le_iff_topRow {P : GTPattern n} : 0 ≤ P ↔ ∀ i, 0 ≤ P.topRow i :=
  ⟨fun h i => by rw [topRow_apply]; exact zero_le_iff.1 h _ _,
    fun h => zero_le_iff.2 (P.entry_nonneg h)⟩

/-- The nonnegative patterns are those whose top weight is polynomial. -/
theorem zero_le_iff_isPolynomial {P : GTPattern n} : 0 ≤ P ↔ P.topWeight.IsPolynomial := by
  rw [DominantWeight.isPolynomial_def, topWeight_coe]
  exact zero_le_iff_topRow

end GTPattern

end TauCeti
