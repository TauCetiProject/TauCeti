/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.FieldTheory.RealClosure.OrderExtension
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.RingTheory.AdjoinRoot

/-! # Polynomial sums of weighted squares

The leading terms of sums of nonnegatively weighted squares cannot cancel.
This is the degree argument needed for odd-degree order extension.
`extensionCone.exists_aeval_root_eq` lifts cone certificates in `AdjoinRoot p`
to polynomial certificates of bounded degree. The imported `extensionCone.map_mem`
from `OrderExtension` specializes these certificates into any algebra over the base field.
-/

public section

namespace TauCeti.RealClosure

open Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A polynomial sum of nonnegatively weighted squares has even degree and
nonnegative leading coefficient. -/
private theorem extensionCone.degree {p : K[X]} (hp : p ∈ extensionCone (C : K →+* K[X])) :
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
theorem extensionCone.even_natDegree {p : K[X]}
    (hp : p ∈ extensionCone (C : K →+* K[X])) : Even p.natDegree :=
  (extensionCone.degree hp).1

/-- A polynomial sum of weighted squares has nonnegative leading coefficient. -/
theorem extensionCone.leadingCoeff_nonneg {p : K[X]}
    (hp : p ∈ extensionCone (C : K →+* K[X])) : 0 ≤ p.leadingCoeff :=
  (extensionCone.degree hp).2

/-- Evaluation of a polynomial sum of weighted squares is nonnegative. -/
theorem extensionCone.eval_nonneg {p : K[X]} (hp : p ∈ extensionCone (C : K →+* K[X]))
    (x : K) : 0 ≤ p.eval x :=
  extensionCone.map_nonneg C (evalRingHom x).toAddMonoidHom
    (fun a ha q => by simpa using mul_nonneg ha (sq_nonneg (q.eval x))) hp

/-- A weighted-square certificate in a simple algebraic extension lifts to a
polynomial weighted-square certificate of degree less than twice the defining degree. -/
theorem extensionCone.exists_aeval_root_eq (p : K[X]) (hdeg : 0 < p.natDegree)
    {x : AdjoinRoot p} (hx : x ∈ extensionCone (algebraMap K (AdjoinRoot p))) :
    ∃ q : K[X], q ∈ extensionCone (C : K →+* K[X]) ∧
      q.natDegree < 2 * p.natDegree ∧ aeval (AdjoinRoot.root p) q = x := by
  have hp : p ≠ 0 := ne_zero_of_natDegree_gt hdeg
  have := AdjoinRoot.nontrivial p (natDegree_pos_iff_degree_pos.mp hdeg).ne'
  induction hx using extensionCone.induction _ with
  | mem x hx =>
    obtain ⟨a, ha, y, rfl⟩ := (mem_weightedSquares _).mp hx
    obtain ⟨q, hq, hy⟩ := (AdjoinRoot.powerBasis hp).exists_eq_aeval y
    refine ⟨C a * q ^ 2,
      extensionCone.weightedSquares_subset _ ((mem_weightedSquares _).mpr ⟨a, ha, q, rfl⟩), ?_, ?_⟩
    · have hq' : q.natDegree < p.natDegree := by
        simpa only [AdjoinRoot.powerBasis_dim] using hq
      exact (natDegree_C_mul_le a (q ^ 2)).trans_lt (by rw [natDegree_pow]; omega)
    · simpa only [map_mul, map_pow, aeval_C, AdjoinRoot.powerBasis_gen] using
        congrArg (fun z => algebraMap K (AdjoinRoot p) a * z ^ 2) hy.symm
  | zero => exact ⟨0, zero_mem _, by simpa using Nat.mul_pos (by decide : 0 < 2) hdeg, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨q, hq, hqd, hqx⟩ := hx
    obtain ⟨r, hr, hrd, hry⟩ := hy
    exact ⟨q + r, add_mem hq hr,
      (natDegree_add_le q r).trans_lt (max_lt hqd hrd), by simp only [map_add, hqx, hry]⟩

end TauCeti.RealClosure
