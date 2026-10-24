/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.EReal.Operations

/-!
# Operations on extended real numbers

This file supplements Mathlib's API for arithmetic operations on `EReal`. The common theme is
subtraction in which one operand is a *real* number: both `a - (r : EReal)` and `(r : EReal) - a`
are defined for every extended real `a`, are never of the form `∞ - ∞`, and behave like real
subtraction in the ways recorded here. The first two results below have a real subtrahend and
the last two a real minuend. The file also records that adding a finite extended nonnegative real
to a real number is real addition, how the positive part `ENNReal.ofReal` of a real number
compares with the number itself in `EReal`, and that the coercion from `ℝ≥0∞` commutes with
infima. The named inclusion `WithTop.toEReal` embeds real heights with a possible top value
into `EReal` without installing a coercion; it is additive.

## Main results

* `EReal.iInf_sub_coe` and `EReal.iSup_sub_coe` — subtracting a real constant commutes with an
  infimum and with a supremum in `EReal`;
* `EReal.coe_sub_add_coe` — subtracting a sum whose final term is real can be reassociated when
  the minuend is real;
* `EReal.coe_sub_le_comm` — the two subtrahends of a real minuend can be exchanged across an
  inequality, as in `sub_le_comm` for groups;
* `EReal.neg_sub_coe` and `EReal.neg_coe_sub` — negating a difference with one real operand
  exchanges the operands, with no finiteness hypothesis on the other;
* `EReal.sub_sub_coe_eq_add_coe_sub` and `EReal.sub_coe_add_eq_add_sub` — a real subtrahend
  moves freely through sums and differences, as in `sub_sub_eq_add_sub` and `sub_add_eq_add_sub`
  for groups;
* `EReal.sub_coe_eq_iff_eq_add_coe` — a real subtrahend can be moved across an equation, as in
  `sub_eq_iff_eq_add` for groups;
* `EReal.add_eq_coe_iff_neg_add_neg_eq` — an equation between a sum and a real number can be
  negated term by term;
* `EReal.coe_le_coe_add_coe_ennreal_iff` — an inequality `x ≤ y + I` with `x`, `y` real and `I` a
  finite extended nonnegative real is the corresponding inequality between reals.
* `EReal.coe_add_coe_ennreal_le_coe_add_coe_ennreal_iff` — likewise for an inequality
  `x + I ≤ y + J` with `I`, `J` finite extended nonnegative reals.
* `EReal.coe_le_coe_ennreal_of_ofReal_le` — a real number whose positive part is at most
  `a : ℝ≥0∞` is at most `a` in `EReal`.
* `EReal.coe_ennreal_iInf` — the coercion from `ℝ≥0∞` to `EReal` commutes with infima.
* `EReal.coe_mul_add_coe_mul_eq_top` — a combination `s a + t b` with positive real weights is `⊤`
  when neither `a` nor `b` is `⊥` and one of them is `⊤`.
* `WithTop.toEReal_add` and `WithTop.toEReal_add_sub_coe_add` — the inclusion of `WithTop ℝ` into
  `EReal` is additive, and subtracting a real sum from the image of a sum splits termwise.
-/

public section

noncomputable section

open scoped ENNReal

namespace TauCeti

/-- Regard a real number with a possible top value as an extended real. This inclusion
preserves `⊤` and never takes the value `⊥`. -/
def _root_.WithTop.toEReal (x : WithTop ℝ) : EReal := WithBot.some x

/-- The inclusion into `EReal` agrees with the real coercion at finite values. -/
@[simp]
theorem _root_.WithTop.toEReal_coe (r : ℝ) : (r : WithTop ℝ).toEReal = (r : EReal) := (rfl)

/-- The inclusion into `EReal` preserves `⊤`. -/
@[simp]
theorem _root_.WithTop.toEReal_top : (⊤ : WithTop ℝ).toEReal = ⊤ := (rfl)

/-- The inclusion into `EReal` never takes the value `⊥`. -/
@[simp]
theorem _root_.WithTop.toEReal_ne_bot (x : WithTop ℝ) : x.toEReal ≠ ⊥ := WithBot.coe_ne_bot

/-- The inclusion into `EReal` preserves and reflects order. -/
@[simp]
theorem _root_.WithTop.toEReal_le_toEReal_iff {x y : WithTop ℝ} :
    x.toEReal ≤ y.toEReal ↔ x ≤ y := WithBot.coe_le_coe

/-- The inclusion into `EReal` preserves and reflects strict order. -/
@[simp]
theorem _root_.WithTop.toEReal_lt_toEReal_iff {x y : WithTop ℝ} :
    x.toEReal < y.toEReal ↔ x < y := WithBot.coe_lt_coe

/-- The inclusion from `WithTop ℝ` into `EReal` is injective. -/
theorem _root_.WithTop.toEReal_injective : Function.Injective WithTop.toEReal :=
  WithBot.coe_injective

/-- A height maps to `⊤` in `EReal` exactly when it was already `⊤`. -/
@[simp]
theorem _root_.WithTop.toEReal_eq_top_iff {x : WithTop ℝ} :
    x.toEReal = ⊤ ↔ x = ⊤ := WithBot.coe_eq_top

/-- The inclusion into `EReal` is additive. -/
@[simp]
theorem _root_.WithTop.toEReal_add (x y : WithTop ℝ) :
    (x + y).toEReal = x.toEReal + y.toEReal := by
  induction x using WithTop.recTopCoe <;> induction y using WithTop.recTopCoe <;>
    simp [← WithTop.coe_add, ← EReal.coe_add]

/-- Subtracting a sum of two reals from the image of a sum of two heights gives the sum of the
two separate differences. -/
theorem _root_.WithTop.toEReal_add_sub_coe_add (x y : WithTop ℝ) (a b : ℝ) :
    (x + y).toEReal - ((a + b : ℝ) : EReal) = (x.toEReal - a) + (y.toEReal - b) := by
  induction x using WithTop.recTopCoe <;> induction y using WithTop.recTopCoe
  case coe.coe r s =>
    simp only [WithTop.toEReal_add, WithTop.toEReal_coe]
    norm_cast
    ring
  all_goals simp [← EReal.coe_sub]

/-- Subtracting a real constant commutes with an infimum in `EReal`; both sides are `⊤` when the
index type is empty. -/
theorem _root_.EReal.iInf_sub_coe {ι : Sort*} (f : ι → EReal) (a : ℝ) :
    (⨅ i, (f i - (a : EReal))) = (⨅ i, f i) - (a : EReal) := by
  refine le_antisymm ?_ (le_iInf fun i => EReal.sub_le_sub (iInf_le f i) le_rfl)
  rw [EReal.le_sub_iff_add_le (.inl (EReal.coe_ne_bot a)) (.inl (EReal.coe_ne_top a))]
  exact le_iInf fun i => EReal.add_le_of_le_sub (iInf_le _ i)

/-- Subtracting a real constant commutes with a supremum in `EReal`; both sides are `⊥` when the
index type is empty. -/
theorem _root_.EReal.iSup_sub_coe {ι : Sort*} (f : ι → EReal) (a : ℝ) :
    (⨆ i, (f i - (a : EReal))) = (⨆ i, f i) - (a : EReal) := by
  refine le_antisymm (iSup_le fun i => EReal.sub_le_sub (le_iSup f i) le_rfl) ?_
  rw [EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot a)) (.inl (EReal.coe_ne_top a))]
  exact iSup_le fun i =>
    (EReal.sub_le_iff_le_add (.inl (EReal.coe_ne_bot a)) (.inl (EReal.coe_ne_top a))).1
      (le_iSup (fun i => f i - (a : EReal)) i)

/-- Subtracting a sum whose final term is real can be reassociated when the minuend is real. -/
theorem _root_.EReal.coe_sub_add_coe (b : EReal) (d a : ℝ) :
    (d : EReal) - (b + (a : EReal)) = (d : EReal) - b - (a : EReal) := by
  induction b with
  | bot => simp
  | coe b => norm_cast; ring
  | top => simp

/-- With a real minuend, the subtrahend and the right-hand side of an inequality can be
exchanged: `r - a ≤ b ↔ r - b ≤ a`. This is `sub_le_comm` for `EReal`, and it holds with no
finiteness hypothesis on `a` or `b`. -/
theorem _root_.EReal.coe_sub_le_comm {r : ℝ} {a b : EReal} :
    (r : EReal) - a ≤ b ↔ (r : EReal) - b ≤ a := by
  induction a <;> induction b <;> simp [← EReal.coe_sub, add_comm]

/-- Negating a difference with a real subtrahend exchanges the operands, for every extended-real
minuend. -/
theorem _root_.EReal.neg_sub_coe (b : EReal) (r : ℝ) : -(b - (r : EReal)) = (r : EReal) - b := by
  rw [EReal.neg_sub (.inr (EReal.coe_ne_bot r)) (.inr (EReal.coe_ne_top r)), add_comm,
    sub_eq_add_neg]

/-- Negating a difference with a real minuend exchanges the operands, for every extended-real
subtrahend. -/
theorem _root_.EReal.neg_coe_sub (r : ℝ) (b : EReal) : -((r : EReal) - b) = b - (r : EReal) := by
  rw [← EReal.neg_sub_coe, neg_neg]

/-- A real subtrahend inside a subtrahend can be pulled out as a summand, for all extended-real
`x` and `y`: this is `sub_sub_eq_add_sub` for `EReal`, with no finiteness hypothesis. -/
theorem _root_.EReal.sub_sub_coe_eq_add_coe_sub (x y : EReal) (a : ℝ) :
    x - (y - (a : EReal)) = x + (a : EReal) - y := by
  rw [sub_eq_add_neg x, EReal.neg_sub_coe, sub_eq_add_neg, ← add_assoc, ← sub_eq_add_neg]

/-- A real subtrahend commutes past a summand, for all extended-real `x` and `y`: this is
`sub_add_eq_add_sub` for `EReal`, with no finiteness hypothesis. -/
theorem _root_.EReal.sub_coe_add_eq_add_sub (x y : EReal) (a : ℝ) :
    x - (a : EReal) + y = x + y - (a : EReal) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_right_comm]

/-- A real subtrahend can be moved across an equation in `EReal`, for all extended-real `x` and
`y`: this is `sub_eq_iff_eq_add` for `EReal`, with no finiteness hypothesis. -/
theorem _root_.EReal.sub_coe_eq_iff_eq_add_coe {x y : EReal} {a : ℝ} :
    x - (a : EReal) = y ↔ x = y + (a : EReal) :=
  ⟨fun h => by rw [← h, EReal.sub_add_cancel], fun h => by rw [h, EReal.add_sub_cancel_right]⟩

/-- An equation between a sum of extended reals and a real number can be negated term by term.
Both sides force `x` and `y` to be real, so no finiteness hypothesis is needed, even though
`-(x + y) = -x + -y` fails in `EReal` when `x` and `y` are opposite infinities. -/
theorem _root_.EReal.add_eq_coe_iff_neg_add_neg_eq {x y : EReal} {r : ℝ} :
    x + y = (r : EReal) ↔ -x + -y = ((-r : ℝ) : EReal) := by
  induction x <;> induction y <;> simp [← EReal.coe_add, ← EReal.coe_neg, ← neg_add, -neg_add_rev]

/-- Adding a finite `I : ℝ≥0∞` to a real number in `EReal` is real addition: the inequality
`x ≤ y + I` between extended reals is `x ≤ y + I.toReal` between reals. -/
theorem _root_.EReal.coe_le_coe_add_coe_ennreal_iff {x y : ℝ} {I : ℝ≥0∞} (hI : I ≠ ∞) :
    (x : EReal) ≤ y + I ↔ x ≤ y + I.toReal := by
  rw [← EReal.coe_ennreal_toReal hI, ← EReal.coe_add, EReal.coe_le_coe_iff]

/-- Adding finite elements of `ℝ≥0∞` to real numbers in `EReal` is real addition: the inequality
`x + I ≤ y + J` between extended reals is `x + I.toReal ≤ y + J.toReal` between reals. -/
theorem _root_.EReal.coe_add_coe_ennreal_le_coe_add_coe_ennreal_iff {x y : ℝ} {I J : ℝ≥0∞}
    (hI : I ≠ ∞) (hJ : J ≠ ∞) :
    (x : EReal) + I ≤ y + J ↔ x + I.toReal ≤ y + J.toReal := by
  rw [← EReal.coe_ennreal_toReal hI, ← EReal.coe_ennreal_toReal hJ, ← EReal.coe_add,
    ← EReal.coe_add, EReal.coe_le_coe_iff]

/-- A real number whose positive part is at most `a : ℝ≥0∞` is at most `a` in `EReal`. -/
theorem _root_.EReal.coe_le_coe_ennreal_of_ofReal_le {x : ℝ} {a : ℝ≥0∞}
    (h : ENNReal.ofReal x ≤ a) : (x : EReal) ≤ (a : EReal) := by
  calc
    (x : EReal) ≤ (ENNReal.ofReal x : EReal) := by
      rw [EReal.coe_ennreal_ofReal]
      exact le_max_left (x : EReal) 0
    _ ≤ (a : EReal) := EReal.coe_ennreal_le_coe_ennreal_iff.2 h

/-- The coercion from `ℝ≥0∞` to `EReal` commutes with infima; both sides are `⊤` when the index
type is empty. -/
@[norm_cast]
theorem _root_.EReal.coe_ennreal_iInf {ι : Sort*} (f : ι → ℝ≥0∞) :
    ((⨅ i, f i : ℝ≥0∞) : EReal) = ⨅ i, (f i : EReal) := by
  apply le_antisymm
  · exact le_iInf fun i ↦ EReal.coe_ennreal_le_coe_ennreal_iff.2 (iInf_le f i)
  · have hnonneg : 0 ≤ (⨅ i, (f i : EReal)) :=
      le_iInf fun i ↦ EReal.coe_ennreal_nonneg (f i)
    rw [← EReal.coe_toENNReal hnonneg]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.2 <| le_iInf fun i ↦
      (EReal.toENNReal_le_toENNReal (iInf_le (fun j ↦ (f j : EReal)) i)).trans_eq
        EReal.toENNReal_coe

/-- A combination `s a + t b` with positive real weights `s`, `t` is `⊤` when neither `a` nor `b`
is `⊥` and one of them is `⊤`. -/
theorem _root_.EReal.coe_mul_add_coe_mul_eq_top {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {a b : EReal}
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) (h : a = ⊤ ∨ b = ⊤) : (s : EReal) * a + (t : EReal) * b = ⊤ := by
  rcases h with rfl | rfl
  · rw [EReal.coe_mul_top_of_pos hs]
    refine EReal.top_add_of_ne_bot ?_
    exact (EReal.mul_ne_bot _ _).2 ⟨.inl (EReal.coe_ne_bot _), .inr hb, .inl (EReal.coe_ne_top _),
      .inl (EReal.coe_nonneg.2 ht.le)⟩
  · rw [EReal.coe_mul_top_of_pos ht]
    refine EReal.add_top_of_ne_bot ?_
    exact (EReal.mul_ne_bot _ _).2 ⟨.inl (EReal.coe_ne_bot _), .inr ha, .inl (EReal.coe_ne_top _),
      .inl (EReal.coe_nonneg.2 hs.le)⟩

end TauCeti

end

end
