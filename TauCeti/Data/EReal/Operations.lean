/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.EReal.Operations
import Mathlib.Data.EReal.Inv

/-!
# Operations on extended real numbers

This file supplements Mathlib's API for arithmetic operations on `EReal`. The common theme is
subtraction in which one operand is a *real* number: both `a - (r : EReal)` and `(r : EReal) - a`
are defined for every extended real `a`, are never of the form `∞ - ∞`, and behave like real
subtraction in the ways recorded here. The first two results below have a real subtrahend and
the last two a real minuend. The file also records that adding a finite extended nonnegative real
to a real number is real addition, how the positive part `ENNReal.ofReal` of a real number
compares with the number itself in `EReal`, that the coercion from `ℝ≥0∞` commutes with
infima, how combinations `s a + t b - r` with real weights and subtrahend behave, and that
negation distributes over a nonnegative combination in `ℝ≥0∞` read in `EReal`. The named
inclusion `WithTop.toEReal` embeds real heights with a possible top value into `EReal` without
installing a coercion; it is additive. Finally, the adjunction `a + b ≤ c ↔ b ≤ c - a` is
recorded for arbitrary operands, with `c - a` replaced by `⊤` in the cases `c = ⊤` or `a = ⊥`.

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
* `EReal.coe_mul_add_coe_mul_sub_coe_ne_top` — a combination `s a + t b - r` with nonnegative
  real weights and a real subtrahend is `≠ ⊤` when `a` and `b` are.
* `EReal.coe_mul_add_coe_mul_sub_le_of_le` — such weighted combinations are monotone in their
  endpoint values.
* `EReal.coe_mul_add_coe_mul_sub_add_sub_comm` — two such combinations with the same weights add
  termwise.
* `EReal.neg_coe_ennreal_ofReal_mul_add_ofReal_mul` — negating a nonnegative combination
  `a x + b y` of extended nonnegative reals gives the same combination of `-x` and `-y`.

* `EReal.coe_mul_coe_mul_add_coe_mul_sub` — nonnegative real scaling distributes through a
  weighted sum with a real subtrahend.
* `EReal.ne_top_of_coe_mul_ne_top` — a positive real multiple can be `≠ ⊤` only if its operand is.
* `EReal.coe_add_add_eq_of_add_add_eq` — an equation between two sums of an extended nonnegative
  real and two real numbers follows from an equation of `ℝ≥0∞` sums and of real differences.
* `EReal.coe_mul_le_coe_mul_iff` — multiplication by a positive real preserves and reflects `≤`.
* `EReal.add_le_iff_le_ite` — `a + b ≤ c` is equivalent to `b ≤ c - a` with no finiteness
  hypothesis, once `c - a` is replaced by `⊤` when `c = ⊤` or `a = ⊥`.
* `WithTop.toEReal_add` and `WithTop.toEReal_add_sub_coe_add` — the inclusion of `WithTop ℝ` into
  `EReal` is additive, and subtracting a real sum from the image of a sum splits termwise.
-/

public section

open scoped ENNReal

namespace WithTop

/-- Regard a real number with a possible top value as an extended real. This inclusion
preserves `⊤` and never takes the value `⊥`. -/
def toEReal (x : WithTop ℝ) : EReal := WithBot.some x

/-- The inclusion into `EReal` agrees with the real coercion at finite values. -/
@[simp]
theorem toEReal_coe (r : ℝ) : (r : WithTop ℝ).toEReal = (r : EReal) := (rfl)

/-- The inclusion into `EReal` preserves `⊤`. -/
@[simp]
theorem toEReal_top : (⊤ : WithTop ℝ).toEReal = ⊤ := (rfl)

/-- The inclusion into `EReal` never takes the value `⊥`. -/
@[simp]
theorem toEReal_ne_bot (x : WithTop ℝ) : x.toEReal ≠ ⊥ := WithBot.coe_ne_bot

/-- The inclusion into `EReal` preserves and reflects order. -/
@[simp]
theorem toEReal_le_toEReal_iff {x y : WithTop ℝ} :
    x.toEReal ≤ y.toEReal ↔ x ≤ y := WithBot.coe_le_coe

/-- The inclusion into `EReal` preserves and reflects strict order. -/
@[simp]
theorem toEReal_lt_toEReal_iff {x y : WithTop ℝ} :
    x.toEReal < y.toEReal ↔ x < y := WithBot.coe_lt_coe

/-- The inclusion from `WithTop ℝ` into `EReal` is injective. -/
theorem toEReal_injective : Function.Injective toEReal :=
  WithBot.coe_injective

/-- A height maps to `⊤` in `EReal` exactly when it was already `⊤`. -/
@[simp]
theorem toEReal_eq_top_iff {x : WithTop ℝ} :
    x.toEReal = ⊤ ↔ x = ⊤ := WithBot.coe_eq_top

/-- The inclusion into `EReal` is additive. -/
@[simp]
theorem toEReal_add (x y : WithTop ℝ) :
    (x + y).toEReal = x.toEReal + y.toEReal := by
  induction x using recTopCoe <;> induction y using recTopCoe <;>
    simp [← coe_add, ← EReal.coe_add]

/-- Subtracting a sum of two reals from the image of a sum of two heights gives the sum of the
two separate differences. -/
theorem toEReal_add_sub_coe_add (x y : WithTop ℝ) (a b : ℝ) :
    (x + y).toEReal - ((a + b : ℝ) : EReal) = (x.toEReal - a) + (y.toEReal - b) := by
  induction x using recTopCoe <;> induction y using recTopCoe
  case coe.coe r s =>
    simp only [toEReal_add, toEReal_coe]
    norm_cast
    ring
  all_goals simp [← EReal.coe_sub]

end WithTop

namespace EReal

/-- Subtracting a real constant commutes with an infimum in `EReal`; both sides are `⊤` when the
index type is empty. -/
theorem iInf_sub_coe {ι : Sort*} (f : ι → EReal) (a : ℝ) :
    (⨅ i, (f i - (a : EReal))) = (⨅ i, f i) - (a : EReal) := by
  refine le_antisymm ?_ (le_iInf fun i => sub_le_sub (iInf_le f i) le_rfl)
  rw [le_sub_iff_add_le (.inl (coe_ne_bot a)) (.inl (coe_ne_top a))]
  exact le_iInf fun i => add_le_of_le_sub (iInf_le _ i)

/-- Subtracting a real constant commutes with a supremum in `EReal`; both sides are `⊥` when the
index type is empty. -/
theorem iSup_sub_coe {ι : Sort*} (f : ι → EReal) (a : ℝ) :
    (⨆ i, (f i - (a : EReal))) = (⨆ i, f i) - (a : EReal) := by
  refine le_antisymm (iSup_le fun i => sub_le_sub (le_iSup f i) le_rfl) ?_
  rw [sub_le_iff_le_add (.inl (coe_ne_bot a)) (.inl (coe_ne_top a))]
  exact iSup_le fun i =>
    (sub_le_iff_le_add (.inl (coe_ne_bot a)) (.inl (coe_ne_top a))).1
      (le_iSup (fun i => f i - (a : EReal)) i)

/-- Subtracting a sum whose final term is real can be reassociated when the minuend is real. -/
theorem coe_sub_add_coe (b : EReal) (d a : ℝ) :
    (d : EReal) - (b + (a : EReal)) = (d : EReal) - b - (a : EReal) := by
  induction b with
  | bot => simp
  | coe b => norm_cast; ring
  | top => simp

/-- With a real minuend, the subtrahend and the right-hand side of an inequality can be
exchanged: `r - a ≤ b ↔ r - b ≤ a`. This is `sub_le_comm` for `EReal`, and it holds with no
finiteness hypothesis on `a` or `b`. -/
theorem coe_sub_le_comm {r : ℝ} {a b : EReal} :
    (r : EReal) - a ≤ b ↔ (r : EReal) - b ≤ a := by
  induction a <;> induction b <;> simp [← coe_sub, add_comm]

/-- Negating a difference with a real subtrahend exchanges the operands, for every extended-real
minuend. -/
theorem neg_sub_coe (b : EReal) (r : ℝ) : -(b - (r : EReal)) = (r : EReal) - b := by
  rw [neg_sub (.inr (coe_ne_bot r)) (.inr (coe_ne_top r)), add_comm,
    sub_eq_add_neg]

/-- Negating a difference with a real minuend exchanges the operands, for every extended-real
subtrahend. -/
theorem neg_coe_sub (r : ℝ) (b : EReal) : -((r : EReal) - b) = b - (r : EReal) := by
  rw [← neg_sub_coe, neg_neg]

/-- A real subtrahend inside a subtrahend can be pulled out as a summand, for all extended-real
`x` and `y`: this is `sub_sub_eq_add_sub` for `EReal`, with no finiteness hypothesis. -/
theorem sub_sub_coe_eq_add_coe_sub (x y : EReal) (a : ℝ) :
    x - (y - (a : EReal)) = x + (a : EReal) - y := by
  rw [sub_eq_add_neg x, neg_sub_coe, sub_eq_add_neg, ← add_assoc, ← sub_eq_add_neg]

/-- A real subtrahend commutes past a summand, for all extended-real `x` and `y`: this is
`sub_add_eq_add_sub` for `EReal`, with no finiteness hypothesis. -/
theorem sub_coe_add_eq_add_sub (x y : EReal) (a : ℝ) :
    x - (a : EReal) + y = x + y - (a : EReal) := by
  rw [sub_eq_add_neg, sub_eq_add_neg, add_right_comm]

/-- A real subtrahend can be moved across an equation in `EReal`, for all extended-real `x` and
`y`: this is `sub_eq_iff_eq_add` for `EReal`, with no finiteness hypothesis. -/
theorem sub_coe_eq_iff_eq_add_coe {x y : EReal} {a : ℝ} :
    x - (a : EReal) = y ↔ x = y + (a : EReal) :=
  ⟨fun h => by rw [← h, sub_add_cancel], fun h => by rw [h, add_sub_cancel_right]⟩

/-- An equation between a sum of extended reals and a real number can be negated term by term.
Both sides force `x` and `y` to be real, so no finiteness hypothesis is needed, even though
`-(x + y) = -x + -y` fails in `EReal` when `x` and `y` are opposite infinities. -/
theorem add_eq_coe_iff_neg_add_neg_eq {x y : EReal} {r : ℝ} :
    x + y = (r : EReal) ↔ -x + -y = ((-r : ℝ) : EReal) := by
  induction x <;> induction y <;>
    simp [← coe_add, ← coe_neg, ← _root_.neg_add, -neg_add_rev]

/-- Adding a finite `I : ℝ≥0∞` to a real number in `EReal` is real addition: the inequality
`x ≤ y + I` between extended reals is `x ≤ y + I.toReal` between reals. -/
theorem coe_le_coe_add_coe_ennreal_iff {x y : ℝ} {I : ℝ≥0∞} (hI : I ≠ ∞) :
    (x : EReal) ≤ y + I ↔ x ≤ y + I.toReal := by
  rw [← coe_ennreal_toReal hI, ← coe_add, EReal.coe_le_coe_iff]

/-- Adding finite elements of `ℝ≥0∞` to real numbers in `EReal` is real addition: the inequality
`x + I ≤ y + J` between extended reals is `x + I.toReal ≤ y + J.toReal` between reals. -/
theorem coe_add_coe_ennreal_le_coe_add_coe_ennreal_iff {x y : ℝ} {I J : ℝ≥0∞}
    (hI : I ≠ ∞) (hJ : J ≠ ∞) :
    (x : EReal) + I ≤ y + J ↔ x + I.toReal ≤ y + J.toReal := by
  rw [← coe_ennreal_toReal hI, ← coe_ennreal_toReal hJ, ← coe_add,
    ← coe_add, EReal.coe_le_coe_iff]

/-- A real number whose positive part is at most `a : ℝ≥0∞` is at most `a` in `EReal`. -/
theorem coe_le_coe_ennreal_of_ofReal_le {x : ℝ} {a : ℝ≥0∞}
    (h : ENNReal.ofReal x ≤ a) : (x : EReal) ≤ (a : EReal) := by
  calc
    (x : EReal) ≤ (ENNReal.ofReal x : EReal) := by
      rw [coe_ennreal_ofReal]
      exact le_max_left (x : EReal) 0
    _ ≤ (a : EReal) := coe_ennreal_le_coe_ennreal_iff.2 h

/-- The coercion from `ℝ≥0∞` to `EReal` commutes with infima; both sides are `⊤` when the index
type is empty. -/
@[norm_cast]
theorem coe_ennreal_iInf {ι : Sort*} (f : ι → ℝ≥0∞) :
    ((⨅ i, f i : ℝ≥0∞) : EReal) = ⨅ i, (f i : EReal) := by
  apply le_antisymm
  · exact le_iInf fun i ↦ coe_ennreal_le_coe_ennreal_iff.2 (iInf_le f i)
  · have hnonneg : 0 ≤ (⨅ i, (f i : EReal)) :=
      le_iInf fun i ↦ coe_ennreal_nonneg (f i)
    rw [← coe_toENNReal hnonneg]
    exact coe_ennreal_le_coe_ennreal_iff.2 <| le_iInf fun i ↦
      (toENNReal_le_toENNReal (iInf_le (fun j ↦ (f j : EReal)) i)).trans_eq
        toENNReal_coe

/-- A combination `s a + t b` with positive real weights `s`, `t` is `⊤` when neither `a` nor `b`
is `⊥` and one of them is `⊤`. -/
theorem coe_mul_add_coe_mul_eq_top {s t : ℝ} (hs : 0 < s) (ht : 0 < t) {a b : EReal}
    (ha : a ≠ ⊥) (hb : b ≠ ⊥) (h : a = ⊤ ∨ b = ⊤) : (s : EReal) * a + (t : EReal) * b = ⊤ := by
  rcases h with rfl | rfl
  · rw [coe_mul_top_of_pos hs]
    refine top_add_of_ne_bot ?_
    exact (mul_ne_bot _ _).2 ⟨.inl (coe_ne_bot _), .inr hb, .inl (coe_ne_top _),
      .inl (EReal.coe_nonneg.2 ht.le)⟩
  · rw [coe_mul_top_of_pos ht]
    refine add_top_of_ne_bot ?_
    exact (mul_ne_bot _ _).2 ⟨.inl (coe_ne_bot _), .inr ha, .inl (coe_ne_top _),
      .inl (EReal.coe_nonneg.2 hs.le)⟩

/-- A combination `s a + t b - r` with nonnegative real weights `s`, `t` and a real subtrahend
`r` is `≠ ⊤` when `a` and `b` are. -/
theorem coe_mul_add_coe_mul_sub_coe_ne_top {a b : EReal} (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    {s t r : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (s : EReal) * a + (t : EReal) * b - (r : EReal) ≠ ⊤ := by
  rw [sub_eq_add_neg, ← coe_neg]
  exact add_ne_top (add_ne_top (by simp [mul_ne_top, hs, ha])
    (by simp [mul_ne_top, ht, hb])) (coe_ne_top _)

/-- A weighted sum with nonnegative real weights and a fixed subtrahend is monotone in both
endpoint values. -/
theorem coe_mul_add_coe_mul_sub_le_of_le {a b a' b' : EReal}
    (ha : a ≤ a') (hb : b ≤ b') {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (r : EReal) :
    (s : EReal) * a + (t : EReal) * b - r ≤ (s : EReal) * a' + (t : EReal) * b' - r :=
  sub_le_sub (add_le_add
    (mul_le_mul_of_nonneg_left ha (EReal.coe_nonneg.2 hs))
    (mul_le_mul_of_nonneg_left hb (EReal.coe_nonneg.2 ht))) le_rfl

/-- Two combinations `s a + t b - r` with the same nonnegative real weights `s`, `t` and real
subtrahends add termwise, as in `sub_add_sub_comm` for groups. -/
theorem coe_mul_add_coe_mul_sub_add_sub_comm (a b a' b' : EReal) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (r r' : ℝ) :
    (s : EReal) * a + (t : EReal) * b - (r : EReal) + ((s : EReal) * a' + (t : EReal) * b' - r') =
      (s : EReal) * (a + a') + (t : EReal) * (b + b') - ((r + r' : ℝ) : EReal) := by
  rw [left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 hs) (coe_ne_top _),
    left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 ht) (coe_ne_top _)]
  simp only [sub_eq_add_neg, ← coe_neg]
  rw [_root_.neg_add, coe_add]
  abel

/-- The negative of a nonnegative combination `a x + b y` in `ℝ≥0∞`, read in `EReal`, is the
same combination of `-x` and `-y`. -/
theorem neg_coe_ennreal_ofReal_mul_add_ofReal_mul {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (x y : ℝ≥0∞) :
    -((ENNReal.ofReal a * x + ENNReal.ofReal b * y : ℝ≥0∞) : EReal) =
      (a : EReal) * -(x : EReal) + (b : EReal) * -(y : EReal) := by
  rw [coe_ennreal_add,
    neg_add (.inl (coe_ennreal_ne_bot _)) (.inr (coe_ennreal_ne_bot _))]
  simp [coe_ennreal_ofReal, ha, hb, sub_eq_add_neg]

/-- Nonnegative real scaling distributes through a weighted sum with a real subtrahend. -/
theorem coe_mul_coe_mul_add_coe_mul_sub (a b : EReal) {c : ℝ} (hc : 0 ≤ c)
    (s t r : ℝ) :
    (c : EReal) * ((s : EReal) * a + (t : EReal) * b - (r : EReal)) =
      (s : EReal) * ((c : EReal) * a) + (t : EReal) * ((c : EReal) * b) -
        ((c * r : ℝ) : EReal) := by
  rw [mul_sub_of_nonneg_of_ne_top (EReal.coe_nonneg.2 hc) (coe_ne_top _),
    left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 hc) (coe_ne_top _),
    mul_left_comm, mul_left_comm (c : EReal) (t : EReal), ← coe_mul]

/-- If a positive real multiple is not `⊤`, neither is the original extended real. -/
theorem ne_top_of_coe_mul_ne_top {c : ℝ} (hc : 0 < c) {d : EReal}
    (hd : (c : EReal) * d ≠ ⊤) : d ≠ ⊤ := by
  rintro rfl
  exact hd (coe_mul_top_of_pos hc)

/-- If two sums `A + px + py` and `B + nx + ny` of extended nonnegative reals agree, with all
summands but `A` and `B` finite, and the real differences `px - nx + (py - ny)` and
`a + b - (a' + b')` agree, then `A + a + b = B + a' + b'` in `EReal`. -/
theorem coe_add_add_eq_of_add_add_eq {A B px nx py ny : ℝ≥0∞}
    (hpx : px ≠ ⊤) (hnx : nx ≠ ⊤) (hpy : py ≠ ⊤) (hny : ny ≠ ⊤)
    (hres : A + px + py = B + nx + ny) {a b a' b' : ℝ}
    (hdiff : px.toReal - nx.toReal + (py.toReal - ny.toReal) = a + b - (a' + b')) :
    (A : EReal) + (a : EReal) + (b : EReal) = (B : EReal) + (a' : EReal) + (b' : EReal) := by
  have hres' : (A : EReal) + ((px.toReal + py.toReal : ℝ) : EReal) =
      (B : EReal) + ((nx.toReal + ny.toReal : ℝ) : EReal) := by
    simpa [coe_ennreal_add, coe_add, coe_ennreal_toReal, hpx, hnx, hpy, hny,
      add_assoc] using congrArg (fun t : ℝ≥0∞ ↦ (t : EReal)) hres
  calc
    (A : EReal) + (a : EReal) + (b : EReal) =
        ((A : EReal) + ((px.toReal + py.toReal : ℝ) : EReal)) +
          ((a + b - (px.toReal + py.toReal) : ℝ) : EReal) := by
      simp only [← coe_add, add_assoc]
      ring_nf
    _ = ((B : EReal) + ((nx.toReal + ny.toReal : ℝ) : EReal)) +
          ((a + b - (px.toReal + py.toReal) : ℝ) : EReal) := by
      rw [hres']
    _ = (B : EReal) + (a' : EReal) + (b' : EReal) := by
      simp only [← coe_add, add_assoc]
      congr 1
      norm_cast
      linarith

/-- Multiplication by a positive real number `c` preserves and reflects the order of `EReal`. -/
@[simp]
theorem coe_mul_le_coe_mul_iff {c : ℝ} (hc : 0 < c) (a b : EReal) :
    (c : EReal) * a ≤ (c : EReal) * b ↔ a ≤ b := by
  have hc' : 0 < (c : EReal) := EReal.coe_pos.2 hc
  rw [← div_le_iff_le_mul hc' (coe_ne_top c), ← mul_div,
    mul_div_cancel (coe_ne_bot c) (coe_ne_top c) hc'.ne']

/-- Unconditional form of `EReal.le_sub_iff_add_le`: `a + b ≤ c` bounds `b` by `c - a`, except
that there is no bound when `c = ⊤` or `a = ⊥`. For each `a` this is a Galois connection between
`(a + ·)` and the right-hand side. -/
theorem add_le_iff_le_ite {a b c : EReal} :
    a + b ≤ c ↔ b ≤ if c = ⊤ ∨ a = ⊥ then ⊤ else c - a := by
  by_cases h : c = ⊤ ∨ a = ⊥
  · rcases h with rfl | rfl <;> simp
  · rw [ite_eq_right h, le_sub_iff_add_le (.inl (not_or.mp h).2) (.inr (not_or.mp h).1), add_comm]

end EReal

end
