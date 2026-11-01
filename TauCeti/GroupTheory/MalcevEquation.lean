/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.CSA

/-!
# Vaught's condition and Malcev's equation

A group `H` satisfies *Vaught's condition* when `x ^ 2 * y ^ 2 * z ^ 2 = 1` forces `x`, `y` and
`z` to commute pairwise; by Lyndon's theorem every free group does. In a torsion-free CSA group
satisfying Vaught's condition and containing two noncommuting elements `a` and `b`, Malcev's
equation `x ^ 2 * a * x ^ 2 * a⁻¹ = (y * b * y * b⁻¹) ^ 2` has only the trivial solution
`x = y = 1`. Thus the single word `malcevWord a b x y` vanishes exactly when both `x` and `y` do.
In a CSA group, `x = 1 ∨ y = 1` holds exactly when `x` commutes with `y`, `a * y * a⁻¹` and
`b * y * b⁻¹` (`Group.IsCSA.eq_one_or_eq_one_iff_commute_conj`); combining these three
commutators with Malcev's word gives one word `malcevOrWord a b x y` that vanishes exactly when
`x` or `y` does. These words reduce conjunctions and disjunctions of equations to a single
equation; see `TauCeti.GroupTheory.GroupAlgGeom.SingleEquation`.

## Main definitions

* `Group.IsVaught G`: Vaught's condition `x ^ 2 * y ^ 2 * z ^ 2 = 1 → [x, y] = [x, z] = [y, z] = 1`.
* `TauCeti.malcevWord a b x y`: Malcev's word `x ^ 2 * a * x ^ 2 * a⁻¹ * ((y * b * y * b⁻¹) ^ 2)⁻¹`.
* `TauCeti.malcevOrWord a b x y`: a word vanishing exactly when `x` or `y` does.

## Main results

* `Group.IsVaught.malcevWord_eq_one_iff`: Malcev's equation has only the trivial solution.
* `Group.IsVaught.malcevOrWord_eq_one_iff`: the disjunction as a single word.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §3.1, Definition 7, Lemmas 3–4.
* G. S. Makanin, *Decidability of the universal and positive theories of a free group*,
  Math. USSR Izv. 25 (1985), §4, Lemmas 3–4.
* R. C. Lyndon, *The equation `a²b² = c²` in free groups*, Michigan Math. J. 6 (1959).
-/

public section

open scoped commutatorElement

namespace Group

variable (G : Type*) [Group G]

/-- A group satisfies *Vaught's condition* when `x ^ 2 * y ^ 2 * z ^ 2 = 1` forces `x`, `y` and
`z` to commute pairwise. By Lyndon's theorem every free group satisfies it. -/
def IsVaught : Prop :=
  ∀ x y z : G, x ^ 2 * y ^ 2 * z ^ 2 = 1 → Commute x y ∧ Commute x z ∧ Commute y z

/-- The defining condition for Vaught's condition. -/
theorem isVaught_iff : IsVaught G ↔
    ∀ x y z : G, x ^ 2 * y ^ 2 * z ^ 2 = 1 → Commute x y ∧ Commute x z ∧ Commute y z :=
  Iff.rfl

end Group

namespace TauCeti

open Group

variable {G H : Type*} [Group G] [Group H]

/-- Malcev's word `x ^ 2 * a * x ^ 2 * a⁻¹ * ((y * b * y * b⁻¹) ^ 2)⁻¹`. It vanishes exactly when
`x ^ 2 * a * x ^ 2 * a⁻¹ = (y * b * y * b⁻¹) ^ 2`, which in a torsion-free CSA group satisfying
Vaught's condition, with `a` and `b` not commuting, means `x = 1` and `y = 1`. -/
def malcevWord (a b x y : G) : G :=
  x ^ 2 * a * x ^ 2 * a⁻¹ * ((y * b * y * b⁻¹) ^ 2)⁻¹

/-- A word in `x` and `y` with constants `a` and `b`, built from Malcev's word and the
commutators of `x` with `y`, `a * y * a⁻¹` and `b * y * b⁻¹`. In a torsion-free CSA group
satisfying Vaught's condition, with `a` and `b` not commuting, it vanishes exactly when `x = 1`
or `y = 1`. -/
def malcevOrWord (a b x y : G) : G :=
  malcevWord a b ⁅x, y⁆ (malcevWord a b ⁅x, a * y * a⁻¹⁆ ⁅x, b * y * b⁻¹⁆)

/-- The defining equation of Malcev's word, in every group. -/
theorem malcevWord_def (a b x y : G) :
    malcevWord a b x y = x ^ 2 * a * x ^ 2 * a⁻¹ * ((y * b * y * b⁻¹) ^ 2)⁻¹ := (rfl)

/-- The defining equation of `malcevOrWord` in terms of Malcev's word, in every group. -/
theorem malcevOrWord_def (a b x y : G) :
    malcevOrWord a b x y =
      malcevWord a b ⁅x, y⁆ (malcevWord a b ⁅x, a * y * a⁻¹⁆ ⁅x, b * y * b⁻¹⁆) := (rfl)

/-- Malcev's word vanishes exactly when Malcev's equation holds. -/
theorem malcevWord_eq_one_iff_eq {a b x y : G} :
    malcevWord a b x y = 1 ↔ x ^ 2 * a * x ^ 2 * a⁻¹ = (y * b * y * b⁻¹) ^ 2 :=
  mul_inv_eq_one

@[simp]
theorem map_malcevWord {F : Type*} [FunLike F G H] [MonoidHomClass F G H] (f : F)
    (a b x y : G) : f (malcevWord a b x y) = malcevWord (f a) (f b) (f x) (f y) := by
  simp [malcevWord]

@[simp]
theorem map_malcevOrWord {F : Type*} [FunLike F G H] [MonoidHomClass F G H] (f : F)
    (a b x y : G) : f (malcevOrWord a b x y) = malcevOrWord (f a) (f b) (f x) (f y) := by
  simp [malcevOrWord, map_commutatorElement]

/-- The trivial solution of Malcev's equation, in every group. -/
@[simp]
theorem malcevWord_one_one (a b : G) : malcevWord a b 1 1 = 1 := by
  simp [malcevWord]

/-- `malcevOrWord a b x y` vanishes when `x = 1`, in every group. -/
@[simp]
theorem malcevOrWord_one_left (a b y : G) : malcevOrWord a b 1 y = 1 := by
  simp [malcevOrWord]

/-- `malcevOrWord a b x y` vanishes when `y = 1`, in every group. -/
@[simp]
theorem malcevOrWord_one_right (a b x : G) : malcevOrWord a b x 1 = 1 := by
  simp [malcevOrWord]

/-- **Malcev's equation** (Kharlampovich–Myasnikov, Lemma 3). In a torsion-free CSA group
satisfying Vaught's condition, if `a` and `b` do not commute, then
`x ^ 2 * a * x ^ 2 * a⁻¹ = (y * b * y * b⁻¹) ^ 2` holds only for `x = y = 1`. -/
theorem _root_.Group.IsVaught.malcevWord_eq_one_iff [IsMulTorsionFree G] (hV : IsVaught G)
    (hG : IsCSA G) {a b x y : G} (hab : ¬Commute a b) :
    malcevWord a b x y = 1 ↔ x = 1 ∧ y = 1 := by
  refine ⟨fun h => ?_, fun ⟨hx, hy⟩ => by simp [hx, hy]⟩
  have hT := (isCommTransitive_iff G).1 hG.isCommTransitive
  have := hG.isCommTransitive.hasUniqueRoots
  have hconj := (isCSA_iff_isCommTransitive_and_commute_conj.1 hG).2
  set r := y * b * y * b⁻¹ with hr
  have heq : x ^ 2 * a * x ^ 2 * a⁻¹ = r ^ 2 := malcevWord_eq_one_iff_eq.1 h
  -- Vaught's condition for `x`, `a * x * a⁻¹` and `r⁻¹` makes `x` commute with `a * x * a⁻¹`.
  have h₁ : x ^ 2 * (a * x * a⁻¹) ^ 2 * r⁻¹ ^ 2 = 1 := by
    rw [conj_pow, inv_pow, mul_inv_eq_one, ← heq]
    group
  obtain ⟨hxa, -, -⟩ := hV _ _ _ h₁
  obtain rfl | hx := eq_or_ne x 1
  · -- Then `r ^ 2 = 1`, so `r = 1`, that is `(y * b) ^ 2 = b ^ 2`, and `y * b = b`.
    have hr₁ : y * b * y * b⁻¹ = 1 := (pow_eq_one_iff_left two_ne_zero).1 <| by
      rw [← hr, ← heq]
      group
    have hyb : (y * b) ^ 2 = b ^ 2 :=
      calc (y * b) ^ 2 = y * b * y * b := by rw [sq]; group
        _ = b ^ 2 := by rw [mul_inv_eq_one.1 hr₁, sq]
    exact ⟨rfl, mul_eq_right.1 (pow_left_injective two_ne_zero hyb)⟩
  · -- Otherwise `x` commutes with `a`, so `r ^ 2 = x ^ 4` and `r = x ^ 2`. Vaught's condition for
    -- `y * b`, `b⁻¹` and `x⁻¹` then makes `x` commute with `b`, hence `a` with `b`.
    have hax : Commute a (x ^ 2) := (hconj x a hx hxa).symm.pow_right 2
    have hrx : r = x ^ 2 := pow_left_injective two_ne_zero (by
      rw [← heq, mul_assoc (x ^ 2), hax.eq, ← mul_assoc, mul_inv_cancel_right, sq (x ^ 2)] :
        r ^ 2 = (x ^ 2) ^ 2)
    have h₂ : (y * b) ^ 2 * b⁻¹ ^ 2 * x⁻¹ ^ 2 = 1 := by
      rw [inv_pow, inv_pow, ← hrx, hr, sq (y * b)]
      group
    obtain ⟨-, -, hbx⟩ := hV _ _ _ h₂
    exact (hab (hT a x b hx (hconj x a hx hxa).symm (Commute.inv_inv_iff.1 hbx).symm)).elim

/-- In a torsion-free CSA group satisfying Vaught's condition, if `a` and `b` do not commute,
then `malcevOrWord a b x y` vanishes exactly when `x = 1` or `y = 1`. -/
theorem _root_.Group.IsVaught.malcevOrWord_eq_one_iff [IsMulTorsionFree G] (hV : IsVaught G)
    (hG : IsCSA G) {a b x y : G} (hab : ¬Commute a b) :
    malcevOrWord a b x y = 1 ↔ x = 1 ∨ y = 1 := by
  rw [hG.eq_one_or_eq_one_iff_commute_conj hab, malcevOrWord, hV.malcevWord_eq_one_iff hG hab,
    hV.malcevWord_eq_one_iff hG hab]
  simp only [commutatorElement_eq_one_iff_commute]

end TauCeti
