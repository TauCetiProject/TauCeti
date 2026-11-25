/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Pointwise
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.BigOperators
import TauCeti.Data.Int.CardIntervalMod

/-!
# Integer points of a dilated bounded region in prescribed residue classes

Let `B ⊆ ℝ^ι` be bounded, with `ι` finite of cardinality `n`. For `r ≥ q ≥ 1` the dilate `r • B`
lies in a cube of side `O(r)`, which is covered by `O((r / q) ^ n)` cubes of side `q`, and each of
these contains one integer point of every residue class modulo `q`. So the integer points
`a ∈ r • B` whose reduction modulo `q` lies in a set `S ⊆ (ℤ/qℤ)^ι` number at most
`C · #S · (r / q) ^ n`, with `C` depending only on `B`.

This is the counting step of the small-prime half of the geometric sieve: with `q = p` prime and
`S = Y(𝔽_p)` of size `O(p ^ (n - k))`, the prime `p` contributes `O(r ^ n / p ^ k)` points.

## Main results

* `Bornology.IsBounded.finite_setOf_intCast_mem`: a bounded subset of `ℝ^ι` contains only finitely
  many integer points.
* `Bornology.IsBounded.exists_ncard_reduction_mem_le`: the residue-class count above.

## References

* M. Bhargava, *The geometric sieve and the density of squarefree values of invariant
  polynomials*, arXiv:1402.0031, proof of Theorem 3.3, display (16).
-/

public section

open Finset
open scoped Pointwise

namespace Bornology.IsBounded

variable {ι : Type*} {B : Set (ι → ℝ)}

/-- A bounded subset of `ℝ^ι` lies in a cube `[-R, R]^ι`. -/
private theorem exists_abs_le [Finite ι] (hB : IsBounded B) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ B, ∀ i, |x i| ≤ R := by
  have := Fintype.ofFinite ι
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hB
  exact ⟨max C 0, le_max_right _ _, fun x hx i ↦
    (Real.norm_eq_abs (x i) ▸ norm_le_pi_norm x i).trans ((hC x hx).trans (le_max_left _ _))⟩

/-- An integer of absolute value at most `R` lies in `[-⌊R⌋, ⌊R⌋]`. -/
private theorem mem_Ico_floor {R : ℝ} {a : ℤ} (ha : |(a : ℝ)| ≤ R) :
    a ∈ Ico (-⌊R⌋) (⌊R⌋ + 1) := by
  have h := abs_le.mp ha
  rw [mem_Ico, Int.lt_add_one_iff, neg_le, Int.le_floor, Int.le_floor]
  push_cast
  exact ⟨by linarith, h.2⟩

/-- For `1 ≤ q ≤ r` and `R ≥ 0`, each residue class modulo `q` meets `[-⌊r R⌋, ⌊r R⌋]` in at most
`(2 R + 2) · (r / q)` integers. -/
private theorem card_Ico_floor_filter_modEq_le {R r : ℝ} (hR : 0 ≤ R) {q : ℕ} (hq : 0 < q)
    (hqr : (q : ℝ) ≤ r) (v : ℤ) :
    (#{x ∈ Ico (-⌊r * R⌋) (⌊r * R⌋ + 1) | x ≡ v [ZMOD q]} : ℝ) ≤ (2 * R + 2) * (r / q) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hr : 0 ≤ r := by linarith
  have hL0 : (0 : ℤ) ≤ ⌊r * R⌋ := Int.floor_nonneg.mpr (mul_nonneg hr hR)
  have hLr : (⌊r * R⌋ : ℝ) ≤ r * R := Int.floor_le _
  have hrq : 1 ≤ r / q := (one_le_div (by positivity)).mpr hqr
  have h₁ : ((#{x ∈ Ico (-⌊r * R⌋) (⌊r * R⌋ + 1) | x ≡ v [ZMOD q]} : ℚ) : ℝ) ≤
      ((((⌊r * R⌋ + 1 - -⌊r * R⌋ : ℤ) : ℚ) / ((q : ℤ) : ℚ) + 1 : ℚ) : ℝ) := by
    exact_mod_cast Int.card_Ico_filter_modEq_le (by exact_mod_cast hq) (by omega) _
  push_cast at h₁
  calc _ ≤ ((⌊r * R⌋ : ℝ) + 1 - -⌊r * R⌋) / q + 1 := h₁
    _ = 2 * ⌊r * R⌋ / q + 1 / q + 1 := by ring
    _ ≤ 2 * (r * R) / q + 1 + r / q := by
      gcongr
      exact div_le_one_of_le₀ hq' (by positivity)
    _ = 2 * R * (r / q) + 1 + r / q := by ring
    _ ≤ (2 * R + 2) * (r / q) := by nlinarith

/-- A bounded subset of `ℝ^ι` contains only finitely many integer points. -/
theorem finite_setOf_intCast_mem [Finite ι] (hB : IsBounded B) :
    {a : ι → ℤ | (fun i ↦ (a i : ℝ)) ∈ B}.Finite := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨R, -, hRB⟩ := hB.exists_abs_le
  exact (Fintype.piFinset fun _ : ι ↦ Ico (-⌊R⌋) (⌊R⌋ + 1)).finite_toSet.subset
    fun a ha ↦ Fintype.mem_piFinset.mpr fun i ↦ mem_Ico_floor (hRB _ ha i)

/-- For a bounded `B ⊆ ℝ^ι` there is a constant `C` such that, whenever `1 ≤ q ≤ r`, the integer
points of `r • B` whose reduction modulo `q` lies in `S ⊆ (ℤ/qℤ)^ι` number at most
`C · #S · (r / q) ^ n`, where `n` is the cardinality of `ι`. -/
theorem exists_ncard_reduction_mem_le [Fintype ι] (hB : IsBounded B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (q : ℕ) (S : Set (ι → ZMod q)), 0 < q → (q : ℝ) ≤ r →
      ({a : ι → ℤ | (fun i ↦ (a i : ℝ)) ∈ r • B ∧ (fun i ↦ (a i : ZMod q)) ∈ S}.ncard : ℝ) ≤
        C * S.ncard * (r / q) ^ Fintype.card ι := by
  classical
  obtain ⟨R, hR, hRB⟩ := hB.exists_abs_le
  refine ⟨(2 * R + 2) ^ Fintype.card ι, by positivity, fun r q S hq hqr ↦ ?_⟩
  have : NeZero q := ⟨hq.ne'⟩
  have hr : 0 ≤ r := (Nat.cast_nonneg q).trans hqr
  -- Every integer point of `r • B` lies in the box `[-L, L]^ι` with `L = ⌊r R⌋`.
  set L : ℤ := ⌊r * R⌋
  have hL : ∀ a : ι → ℤ, (fun i ↦ (a i : ℝ)) ∈ r • B → ∀ i, a i ∈ Ico (-L) (L + 1) := by
    intro a ha i
    obtain ⟨x, hx, hxa⟩ := Set.mem_smul_set.mp ha
    refine mem_Ico_floor ?_
    rw [← congrFun hxa i, Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hr]
    exact mul_le_mul_of_nonneg_left (hRB x hx i) hr
  -- Group the points by their residue `s ∈ S`; each class meets the box in a product of
  -- one-dimensional residue classes.
  set box : (ι → ZMod q) → Finset (ι → ℤ) := fun s ↦
    Fintype.piFinset fun i ↦ {x ∈ Ico (-L) (L + 1) | x ≡ ((s i).val : ℤ) [ZMOD q]}
  have hsub : {a : ι → ℤ | (fun i ↦ (a i : ℝ)) ∈ r • B ∧ (fun i ↦ (a i : ZMod q)) ∈ S} ⊆
      ↑(S.toFinset.biUnion box) := by
    rintro a ⟨ha, haS⟩
    rw [coe_biUnion, Set.mem_iUnion₂]
    refine ⟨_, Set.mem_toFinset.mpr haS, Fintype.mem_piFinset.mpr fun i ↦
      mem_filter.mpr ⟨hL a ha i, ?_⟩⟩
    rw [← ZMod.intCast_eq_intCast_iff, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hbox : ∀ s, ((box s).card : ℝ) ≤ ((2 * R + 2) * (r / q)) ^ Fintype.card ι := by
    intro s
    rw [Fintype.card_piFinset, Nat.cast_prod]
    exact (Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun i _ ↦
      card_Ico_floor_filter_modEq_le hR hq hqr _).trans_eq (Finset.prod_const _)
  calc ((Set.ncard _ : ℕ) : ℝ) ≤ (S.toFinset.biUnion box).card := by
        exact_mod_cast (Set.ncard_le_ncard hsub (Finset.finite_toSet _)).trans
          (Set.ncard_coe_finset _).le
    _ ≤ ∑ s ∈ S.toFinset, ((box s).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ s ∈ S.toFinset, ((2 * R + 2) * (r / q)) ^ Fintype.card ι :=
        Finset.sum_le_sum fun s _ ↦ hbox s
    _ = (2 * R + 2) ^ Fintype.card ι * S.ncard * (r / q) ^ Fintype.card ι := by
        rw [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card', mul_pow]
        ring

end Bornology.IsBounded
