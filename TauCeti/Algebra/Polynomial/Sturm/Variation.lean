/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Sturm.Sequence
public import Mathlib.Data.List.SignVariations

/-!
# Variations of a Sturm sequence at a point

The variation of a signed Euclidean remainder sequence is the number used in
Sturm's root-counting formula. Mathlib's `Polynomial.sturmSeq` supplies the
sequence and `List.signVariations` counts its sign changes. At a zero of the
second polynomial where the first is nonzero, the first and third values are
opposite, so deleting the zero reveals exactly one sign change. This file
records that local calculation alongside the sequence recurrence and the zero
cases. The calculation works over any ordered field; it does not require real
closedness.
Use `TauCeti.Polynomial.sturmVariation p q x` to access the evaluated variation.
After `open TauCeti`, the same call can be written `p.sturmVariation q x`.
-/

public section

namespace TauCeti
namespace Polynomial

open _root_.Polynomial

variable {K : Type*} [Field K] [LinearOrder K]

/-- The number of sign changes in the nonzero values of a signed Euclidean
remainder sequence at `x`. -/
noncomputable def sturmVariation (p q : K[X]) (x : K) : ℕ :=
  ((sturmSeq p q).map (fun r => r.eval x)).signVariations

/-- An empty Sturm sequence has no variations. -/
@[simp] theorem sturmVariation_zero_left (q : K[X]) (x : K) :
    sturmVariation 0 q x = 0 := by
  simp [sturmVariation, sturmSeq_zero_left]

/-- A singleton Sturm sequence has no variations, even at a root of its entry. -/
@[simp] theorem sturmVariation_zero_right (p : K[X]) (x : K) :
    sturmVariation p 0 x = 0 := by
  by_cases hp : p = 0
  · simp [hp]
  · simp [sturmVariation, sturmSeq_zero_right, hp]

/-- Evaluation of the first entry gives the recursion for Sturm variations. -/
theorem sturmVariation_cons {p : K[X]} (hp : p ≠ 0) (q : K[X]) (x : K) :
    sturmVariation p q x =
      (p.eval x :: (sturmSeq q (-p % q)).map (fun r => r.eval x)).signVariations := by
  simp only [sturmVariation, sturmSeq_cons hp, List.map_cons]

/-- A zero first value is deleted when counting Sturm variations. -/
@[simp] theorem sturmVariation_of_eval_eq_zero {p q : K[X]} {x : K}
    (hp : p.eval x = 0) :
    sturmVariation p q x = sturmVariation q (-p % q) x := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · rw [sturmVariation_cons hp0]
    simp only [hp, List.signVariations_zero_cons, sturmVariation]

omit [LinearOrder K] in
private theorem ne_zero_of_eval_ne_zero {p : K[X]} {x : K} (hp : p.eval x ≠ 0) :
    p ≠ 0 := fun h => hp (by simp [h])

/-- When the first two evaluations are nonzero, a Sturm variation step adds
one exactly when their signs differ. -/
theorem sturmVariation_eq_add_of_eval_ne_zero {p q : K[X]} {x : K}
    (hp : p.eval x ≠ 0) (hq : q.eval x ≠ 0) :
    sturmVariation p q x = sturmVariation q (-p % q) x +
      (if SignType.sign (p.eval x) = SignType.sign (q.eval x) then 0 else 1) := by
  have hp0 : p ≠ 0 := ne_zero_of_eval_ne_zero hp
  have hq0 : q ≠ 0 := ne_zero_of_eval_ne_zero hq
  rw [sturmVariation_cons hp0, sturmVariation_cons hq0, sturmSeq_cons hq0,
    List.map_cons, List.signVariations_cons_cons_of_ne_zero _ hp hq]

variable [IsStrictOrderedRing K]

/-- At a zero of the second polynomial that is not a zero of the first,
the first Sturm variation step contributes exactly one sign change. -/
@[simp] theorem sturmVariation_eq_add_one_of_eval_ne_zero_of_eval_eq_zero
    {p q : K[X]} {x : K}
    (hp : p.eval x ≠ 0) (hq0 : q ≠ 0) (hq : q.eval x = 0) :
    sturmVariation p q x = sturmVariation q (-p % q) x + 1 := by
  have hp0 : p ≠ 0 := ne_zero_of_eval_ne_zero hp
  rw [sturmVariation_cons hp0, sturmVariation_cons hq0,
    sturmSeq_cons hq0]
  have hr : (-p % q).eval x = -p.eval x := by
    simp [EuclideanDomain.mod_eq_sub_mul_div, hq]
  have hr0 : -p % q ≠ 0 := by
    intro hz
    have := congrArg (fun r : K[X] => r.eval x) hz
    rw [hr, eval_zero] at this
    exact hp (neg_eq_zero.mp this)
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
@[simp] theorem sturmVariation_mul_left {r : K[X]} (p q : K[X]) {x : K}
    (hrx : r.eval x ≠ 0) :
    sturmVariation (r * p) (r * q) x = sturmVariation p q x := by
  have hr : r ≠ 0 := by
    intro h
    simp [h] at hrx
  have hmap : ((sturmSeq (r * p) (r * q)).map (fun s => s.eval x)) =
      ((sturmSeq p q).map (fun s => s.eval x)).map (fun a => r.eval x * a) := by
    simp [sturmSeq_mul_left hr, List.map_map, Function.comp_def, eval_mul]
  simp only [sturmVariation, hmap]
  by_cases hpos : 0 < r.eval x
  · exact List.signVariations_map (fun a => by simp [sign_mul, sign_pos hpos]) _
  · have hneg : r.eval x < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hrx
    exact List.signVariations_map_of_sign_eq_neg
      (fun a => by simp [sign_mul, sign_neg hneg]) _

omit [IsStrictOrderedRing K] in
/-- A common root of the two input polynomials annihilates every entry of
their Sturm sequence, so its variation at that point is zero. -/
@[simp] theorem sturmVariation_eq_zero_of_eval_eq_zero_of_eval_eq_zero {p q : K[X]} {x : K}
    (hp : p.eval x = 0) (hq : q.eval x = 0) : sturmVariation p q x = 0 := by
  have hpd : X - C x ∣ p := dvd_iff_isRoot.mpr hp
  have hqd : X - C x ∣ q := dvd_iff_isRoot.mpr hq
  have hz (s : K[X]) (hs : s ∈ sturmSeq p q) : s.eval x = 0 :=
    (dvd_iff_isRoot.mp (dvd_of_mem_sturmSeq hpd hqd hs))
  have hmap : (sturmSeq p q).map (fun s => s.eval x) =
      List.replicate (sturmSeq p q).length 0 := by
    calc
      (sturmSeq p q).map (fun s => s.eval x) =
          (sturmSeq p q).map (fun _ => (0 : K)) := by
            apply List.map_congr_left
            intro s hs
            exact hz s hs
      _ = List.replicate (sturmSeq p q).length 0 := by simp
  have hzero (n : ℕ) : (List.replicate n (0 : K)).signVariations = 0 := by
    cases n with
    | zero => simp
    | succ n => simpa only [List.replicate_succ] using
        List.signVariations_cons_replicate_zero (0 : K) n
  simpa only [sturmVariation, hmap] using hzero (sturmSeq p q).length

end Polynomial
end TauCeti
