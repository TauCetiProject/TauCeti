/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.NonwanderingSet
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Topology.UnitInterval

/-!
# Checks for the non-wandering set

* The translation `x ↦ x + 1` of `ℝ` has empty non-wandering set
  (`TauCeti.Examples.NonwanderingSet.nonwanderingSet_add_one`): the open interval of length `1`
  about a point is disjoint from all its translates.
* The map `(x, y) ↦ (x, y²)` of the closed cylinder `AddCircle 1 × [0, 1]` has non-wandering set
  the two boundary circles `y = 0` and `y = 1`
  (`TauCeti.Examples.NonwanderingSet.nonwanderingSet_sqMap`). The boundary points are fixed. For
  `0 < y < 1`, choose `a < y < b` with `b² < a`; every point of the band `a < y' < b` is sent by
  each iterate below `b² < a`, so the band never returns to itself.
-/

open Set Function Filter Topology unitInterval

public noncomputable section

namespace TauCeti.Examples.NonwanderingSet

/-- **The translation of the line by `1` has no non-wandering point.** -/
theorem nonwanderingSet_add_one : nonwanderingSet (· + 1 : ℝ → ℝ) = ∅ := by
  refine eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨n, hn, y, hy, hny⟩ := mem_nonwanderingSet_iff_exists_iterate_mem.1 hx
    (Ioo (x - 1 / 2) (x + 1 / 2)) (Ioo_mem_nhds (by linarith) (by linarith))
  rw [add_right_iterate_apply, nsmul_eq_mul, mul_one] at hny
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith [hy.1, hny.2]

/-- The map `(x, y) ↦ (x, y²)` of the closed cylinder `AddCircle 1 × [0, 1]`. -/
def sqMap (p : AddCircle (1 : ℝ) × I) : AddCircle (1 : ℝ) × I :=
  (p.1, p.2 * p.2)

/-- The second coordinate of an iterate of `sqMap` is the `2ⁿ`-th power. -/
theorem coe_iterate_sqMap_snd (n : ℕ) (p : AddCircle (1 : ℝ) × I) :
    ((sqMap^[n] p).2 : ℝ) = (p.2 : ℝ) ^ (2 ^ n) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    rw [iterate_succ_apply', sqMap, Set.Icc.coe_mul, ih]
    ring

/-- **The non-wandering set of `(x, y) ↦ (x, y²)`** on `AddCircle 1 × [0, 1]` is the union of the
two boundary circles `y = 0` and `y = 1`. -/
theorem nonwanderingSet_sqMap :
    nonwanderingSet sqMap = {p | (p.2 : ℝ) = 0 ∨ (p.2 : ℝ) = 1} := by
  ext ⟨x, y⟩
  simp only [mem_ofPred_eq]
  constructor
  · intro h
    by_contra hy
    push Not at hy
    have hy0 : 0 < (y : ℝ) := lt_of_le_of_ne y.property.1 (Ne.symm hy.1)
    have hy1 : (y : ℝ) < 1 := lt_of_le_of_ne y.property.2 hy.2
    -- The band `a < y' < b` with `b² < a < y < b`.
    set b : ℝ := (y : ℝ) + ((y : ℝ) - (y : ℝ) ^ 2) / 3
    set a : ℝ := (b ^ 2 + y) / 2
    have hε : 0 < (y : ℝ) - (y : ℝ) ^ 2 := by nlinarith
    have hb : (y : ℝ) < b := by simp only [b]; linarith
    have hb2 : b ^ 2 < y := by simp only [b]; nlinarith
    have ha : a < y := by simp only [a]; linarith
    have hU : {p : AddCircle (1 : ℝ) × I | (p.2 : ℝ) ∈ Ioo a b} ∈ 𝓝 (x, y) :=
      (isOpen_Ioo.preimage (continuous_subtypeVal.comp continuous_snd)).mem_nhds ⟨ha, hb⟩
    obtain ⟨n, hn, q, hq, hnq⟩ := mem_nonwanderingSet_iff_exists_iterate_mem.1 h _ hU
    have hq0 : 0 ≤ (q.2 : ℝ) := q.2.property.1
    have hq1 : (q.2 : ℝ) ≤ 1 := q.2.property.2
    have hnq' : (q.2 : ℝ) ^ (2 ^ n) ∈ Ioo a b := by
      rw [← coe_iterate_sqMap_snd]
      exact hnq
    have hpow : (q.2 : ℝ) ^ (2 ^ n) ≤ (q.2 : ℝ) ^ 2 :=
      pow_le_pow_of_le_one hq0 hq1 (by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
    have hq2 : (q.2 : ℝ) ^ 2 < b ^ 2 := by
      have := hq.2
      gcongr
    have : b ^ 2 < a := by simp only [a]; linarith
    linarith [hnq'.1]
  · rintro (h | h) <;> exact IsFixedPt.mem_nonwanderingSet (by ext <;> simp [sqMap, h])

end TauCeti.Examples.NonwanderingSet
