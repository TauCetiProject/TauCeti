/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.OrderExtension
public import Mathlib.RingTheory.PowerBasis

/-! # Polynomial sums of weighted squares

The leading terms of sums of nonnegatively weighted squares cannot cancel.
This is the degree argument needed for odd-degree order extension.
`PowerBasis.exists_aeval_eq_of_mem_extensionCone` lifts cone certificates in a
nontrivial algebra with a power basis to polynomial certificates of degree less
than twice the dimension. The imported `extensionCone.map_mem` from `OrderExtension`
specializes these certificates into any algebra over the base ring.
-/

public section

namespace TauCeti.RealClosure

open Polynomial

variable {R : Type*}

section Degree

variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]

/-- A polynomial sum of nonnegatively weighted squares has even degree and
nonnegative leading coefficient. -/
private theorem extensionCone.degree {p : R[X]} (hp : p ∈ extensionCone (C : R →+* R[X])) :
    Even p.natDegree ∧ 0 ≤ p.leadingCoeff := by
  induction hp using extensionCone.induction _ with
  | mem p hp =>
    obtain ⟨a, ha, q, rfl⟩ := (mem_weightedSquares _).mp hp
    by_cases ha0 : a = 0
    · simp [ha0]
    constructor
    · rw [natDegree_C_mul ha0, natDegree_pow]
      exact even_two_mul _
    · simpa only [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow] using
        mul_nonneg ha (sq_nonneg q.leadingCoeff)
  | zero => simp
  | add p q _ _ hp hq =>
    by_cases hp0 : p = 0
    · simpa [hp0] using hq
    by_cases hq0 : q = 0
    · simpa [hq0] using hp
    have hp' : 0 < p.leadingCoeff := lt_of_le_of_ne hp.2 (leadingCoeff_ne_zero.mpr hp0).symm
    have hq' : 0 < q.leadingCoeff := lt_of_le_of_ne hq.2 (leadingCoeff_ne_zero.mpr hq0).symm
    rcases lt_trichotomy p.degree q.degree with hlt | heq | hgt
    · rw [natDegree_add_eq_right_of_degree_lt hlt, leadingCoeff_add_of_degree_lt hlt]
      exact hq
    · have hsum := add_pos hp' hq'
      have hd : (p + q).natDegree = p.natDegree := by
        apply natDegree_eq_of_degree_eq
        rw [degree_add_eq_of_leadingCoeff_add_ne_zero hsum.ne', heq, max_self]
      rw [hd, leadingCoeff_add_of_degree_eq heq hsum.ne']
      exact ⟨hp.1, hsum.le⟩
    · rw [natDegree_add_eq_left_of_degree_lt hgt, leadingCoeff_add_of_degree_lt' hgt]
      exact hp

/-- A polynomial sum of weighted squares has even degree. -/
theorem extensionCone.even_natDegree {p : R[X]}
    (hp : p ∈ extensionCone (C : R →+* R[X])) : Even p.natDegree :=
  (extensionCone.degree hp).1

/-- A polynomial sum of weighted squares has nonnegative leading coefficient. -/
theorem extensionCone.leadingCoeff_nonneg {p : R[X]}
    (hp : p ∈ extensionCone (C : R →+* R[X])) : 0 ≤ p.leadingCoeff :=
  (extensionCone.degree hp).2

end Degree

/-- Evaluation of a polynomial sum of weighted squares is nonnegative. -/
theorem extensionCone.eval_nonneg [CommSemiring R] [LinearOrder R] [IsOrderedRing R]
    [ExistsAddOfLE R] {p : R[X]} (hp : p ∈ extensionCone (C : R →+* R[X]))
    (x : R) : 0 ≤ p.eval x :=
  extensionCone.map_nonneg C (evalRingHom x).toAddMonoidHom
    (fun a ha q => by simpa using mul_nonneg ha (sq_nonneg (q.eval x))) hp

end TauCeti.RealClosure

namespace PowerBasis

open Polynomial TauCeti.RealClosure

/-- A weighted-square certificate in a nontrivial algebra with a power basis lifts to a
polynomial weighted-square certificate of degree less than twice the basis dimension. -/
theorem exists_aeval_eq_of_mem_extensionCone
    {R S : Type*} [CommRing R] [PartialOrder R] [IsOrderedRing R] [CommRing S]
    [Algebra R S] [Nontrivial S] (pb : PowerBasis R S)
    {x : S} (hx : x ∈ extensionCone (algebraMap R S)) :
    ∃ q : R[X], q ∈ extensionCone (C : R →+* R[X]) ∧
      q.natDegree < 2 * pb.dim ∧ aeval pb.gen q = x := by
  induction hx using extensionCone.induction _ with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := (mem_weightedSquares _).mp hx
    obtain ⟨q, hq, hy⟩ := pb.exists_eq_aeval y
    refine ⟨C a * q ^ 2,
      extensionCone.weightedSquares_subset _ ((mem_weightedSquares _).mpr ⟨a, ha, q, rfl⟩), ?_, ?_⟩
    · exact (natDegree_C_mul_le a (q ^ 2)).trans_lt
        (natDegree_pow_le.trans_lt (Nat.mul_lt_mul_of_pos_left hq (by decide)))
    · simpa only [map_mul, map_pow, aeval_C] using
        congrArg (fun z => algebraMap R S a * z ^ 2) hy.symm
  | zero =>
    exact ⟨0, zero_mem _, by simpa using Nat.mul_pos (by decide : 0 < 2) pb.dim_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨q, hq, hqd, hqx⟩ := hx
    obtain ⟨r, hr, hrd, hry⟩ := hy
    exact ⟨q + r, add_mem hq hr,
      (natDegree_add_le q r).trans_lt (max_lt hqd hrd), by simp only [map_add, hqx, hry]⟩

end PowerBasis
