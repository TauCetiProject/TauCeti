/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Sturm.Sequence
public import TauCeti.Algebra.Polynomial.Sturm.Signs
import TauCeti.Algebra.Polynomial.FieldDivision

/-!
# Variations of a Sturm sequence at a point

The variation of a signed Euclidean remainder sequence is the number used in
Sturm's root-counting formula. Mathlib's `Polynomial.sturmSeq` supplies the
sequence and `TauCeti.Sturm.signVariationsAt` counts its evaluated sign changes.
At a zero of the nonzero second polynomial where the first is nonzero, the first and third
values are opposite, so deleting the zero reveals exactly one sign change. This file
records that local calculation alongside the sequence recurrence. The existing
empty-list and singleton variation lemmas supply the zero cases. The calculation works over
any ordered field; it does not require real closedness.
Negating both inputs or multiplying them by a polynomial nonzero at the
evaluation point leaves the variation unchanged, while a common root makes it zero.
The evaluated variation uses the existing `TauCeti.Sturm.signVariationsAt` API
on `Polynomial.sturmSeq p q`.
-/

public section

namespace TauCeti.Sturm

open _root_.Polynomial

variable {K : Type*} [Field K] [LinearOrder K]

/-- Evaluation of the first entry gives the recursion for Sturm variations. -/
private theorem signVariationsAt_sturmSeq_cons {p : K[X]} (hp : p ≠ 0) (q : K[X]) (x : K) :
    signVariationsAt (sturmSeq p q) x =
      (p.eval x :: (sturmSeq q (-p % q)).map (fun r => r.eval x)).signVariations := by
  simp only [signVariationsAt_def, sturmSeq_cons hp, List.map_cons]

/-- A zero first value is deleted when counting Sturm variations. -/
theorem signVariationsAt_sturmSeq_eq_of_eval_eq_zero {p q : K[X]} {x : K}
    (hp : p.eval x = 0) :
    signVariationsAt (sturmSeq p q) x = signVariationsAt (sturmSeq q (-p % q)) x := by
  by_cases hp0 : p = 0
  · simp only [hp0, neg_zero, EuclideanDomain.zero_mod, sturmSeq_zero_left, sturmSeq_zero_right]
    split_ifs <;> simp only [signVariationsAt_nil, signVariationsAt_singleton]
  · rw [signVariationsAt_sturmSeq_cons hp0]
    simp only [hp, List.signVariations_zero_cons, signVariationsAt_def]

/-- When the first two evaluations are nonzero, a Sturm variation step adds
one exactly when their signs differ. -/
theorem signVariationsAt_sturmSeq_eq_add_of_eval_ne_zero {p q : K[X]} {x : K}
    (hp : p.eval x ≠ 0) (hq : q.eval x ≠ 0) :
    signVariationsAt (sturmSeq p q) x = signVariationsAt (sturmSeq q (-p % q)) x +
      (if SignType.sign (p.eval x) = SignType.sign (q.eval x) then 0 else 1) := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have hq0 : q ≠ 0 := by rintro rfl; simp at hq
  rw [signVariationsAt_sturmSeq_cons hp0, signVariationsAt_sturmSeq_cons hq0, sturmSeq_cons hq0,
    List.map_cons, List.signVariations_cons_cons_of_ne_zero _ hp hq]

variable [IsStrictOrderedRing K]

/-- At a zero of the nonzero second polynomial that is not a zero of the first,
the first Sturm variation step contributes exactly one sign change. -/
theorem signVariationsAt_sturmSeq_eq_add_one_of_eval_ne_zero_of_eval_eq_zero
    {p q : K[X]} {x : K}
    (hp : p.eval x ≠ 0) (hq0 : q ≠ 0) (hq : q.eval x = 0) :
    signVariationsAt (sturmSeq p q) x = signVariationsAt (sturmSeq q (-p % q)) x + 1 := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  rw [signVariationsAt_sturmSeq_cons hp0, signVariationsAt_sturmSeq_cons hq0,
    sturmSeq_cons hq0]
  have hr : (-p % q).eval x = -p.eval x := by
    simpa only [eval_neg] using TauCeti.Polynomial.eval_mod_of_eval_eq_zero (p := -p) hq
  have hr0 : -p % q ≠ 0 := by
    intro hz
    apply neg_ne_zero.mpr hp
    rw [← hr, hz, eval_zero]
  rw [sturmSeq_cons hr0]
  simp only [List.map_cons, hq, hr]
  rw [List.signVariations_cons_zero_cons, List.signVariations_zero_cons,
    List.signVariations_cons_cons_of_ne_zero _ hp (neg_ne_zero.mpr hp)]
  have hs : SignType.sign (p.eval x) ≠ SignType.sign (-p.eval x) := by
    rw [Left.sign_neg]
    exact mt SignType.self_eq_neg_iff.mp (sign_ne_zero.mpr hp)
  simp only [hs, ite_false]

/-- Multiplying both inputs by a common polynomial does not alter their
Sturm variation away from its roots. -/
@[simp] theorem signVariationsAt_sturmSeq_mul_left {r : K[X]} (p q : K[X]) {x : K}
    (hrx : r.eval x ≠ 0) :
    signVariationsAt (sturmSeq (r * p) (r * q)) x = signVariationsAt (sturmSeq p q) x := by
  have hr : r ≠ 0 := by rintro rfl; simp at hrx
  rw [sturmSeq_mul_left hr]
  exact signVariationsAt_map_mul (sturmSeq p q) hrx

/-- Negating both inputs preserves their Sturm variation. -/
@[simp] theorem signVariationsAt_sturmSeq_neg_neg (p q : K[X]) (x : K) :
    signVariationsAt (sturmSeq (-p) (-q)) x = signVariationsAt (sturmSeq p q) x := by
  simpa only [neg_one_mul] using
    (signVariationsAt_sturmSeq_mul_left (r := -(1 : K[X])) p q (x := x) (by simp))

omit [IsStrictOrderedRing K] in
/-- A common root of the two input polynomials annihilates every entry of
their Sturm sequence, so its variation at that point is zero. -/
@[simp] theorem signVariationsAt_sturmSeq_eq_zero_of_eval_eq_zero_of_eval_eq_zero
    {p q : K[X]} {x : K}
    (hp : p.eval x = 0) (hq : q.eval x = 0) : signVariationsAt (sturmSeq p q) x = 0 := by
  have hpd : X - C x ∣ p := dvd_iff_isRoot.mpr hp
  have hqd : X - C x ∣ q := dvd_iff_isRoot.mpr hq
  have hz (s : K[X]) (hs : s ∈ sturmSeq p q) : s.eval x = 0 :=
    (dvd_iff_isRoot.mp (dvd_of_mem_sturmSeq hpd hqd hs))
  rw [signVariationsAt_def, ← List.signVariations_filter_ne_zero,
    List.filter_eq_nil_iff.mpr, List.signVariations_nil]
  simpa [List.forall_mem_map] using hz

end TauCeti.Sturm
