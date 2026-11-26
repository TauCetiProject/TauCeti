/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

import TauCeti.Analysis.Normed.Lp.PiLp.Basic
import TauCeti.Analysis.Normed.Module.FiniteSpan
import TauCeti.Analysis.Normed.Module.Normalize

/-!
# Compressible and incompressible vectors

A unit vector is compressible if it is within a prescribed distance of a vector supported on
at most `k` coordinates. The approximating sparse vector need not be a unit vector.
For `0 ≤ ρ`, incompressibility is characterized by the squared mass outside every set of at most
`k` coordinates. It forces more than `(k + 1) ρ² / 2` coordinates to have norms between
`ρ / √(2n)` and `1 / √(k + 1)`, where `n` is the number of coordinates. These facts reduce lower
bounds for a matrix on incompressible vectors to distances of columns from the spans of the
other columns.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), §3.1 and Lemma 3.4.
-/

public section

open Finset Metric Set

namespace TauCeti

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι]

/-- A compressible vector is a unit vector within distance `ρ` of a vector supported on at most
`k` coordinates. The sparse approximant is not required to have norm one. -/
def IsCompressibleVector (k : ℕ) (ρ : ℝ) (x : EuclideanSpace 𝕜 ι) : Prop :=
  ‖x‖ = 1 ∧ ∃ s : Finset ι, s.card ≤ k ∧
    ∃ y : EuclideanSpace 𝕜 ι, (∀ i ∉ s, y i = 0) ∧ ‖x - y‖ ≤ ρ

/-- An incompressible vector is a unit vector which is not compressible. -/
def IsIncompressibleVector (k : ℕ) (ρ : ℝ) (x : EuclideanSpace 𝕜 ι) : Prop :=
  ‖x‖ = 1 ∧ ¬IsCompressibleVector k ρ x

variable {k l : ℕ} {ρ σ : ℝ} {x : EuclideanSpace 𝕜 ι}

/-- Compressibility is equivalent to unit norm and approximation within radius `ρ` by a vector
supported on at most `k` coordinates. -/
theorem isCompressibleVector_iff :
    IsCompressibleVector k ρ x ↔ ‖x‖ = 1 ∧ ∃ s : Finset ι, s.card ≤ k ∧
      ∃ y : EuclideanSpace 𝕜 ι, (∀ i ∉ s, y i = 0) ∧ ‖x - y‖ ≤ ρ := (Iff.rfl)

/-- Incompressibility is equivalent to unit norm and failure of compressibility. -/
@[grind =] theorem isIncompressibleVector_iff :
    IsIncompressibleVector k ρ x ↔ ‖x‖ = 1 ∧ ¬IsCompressibleVector k ρ x := (Iff.rfl)

/-- A compressible vector has unit norm. -/
@[grind →] theorem IsCompressibleVector.norm_eq_one (hx : IsCompressibleVector k ρ x) :
    ‖x‖ = 1 := hx.1

/-- An incompressible vector has unit norm. -/
@[grind →] theorem IsIncompressibleVector.norm_eq_one (hx : IsIncompressibleVector k ρ x) :
    ‖x‖ = 1 := hx.1

/-- An incompressible vector is not compressible at the same parameters. -/
theorem IsIncompressibleVector.not_isCompressibleVector (hx : IsIncompressibleVector k ρ x) :
    ¬IsCompressibleVector k ρ x := hx.2

/-- A compressible vector is not incompressible at the same parameters. -/
theorem IsCompressibleVector.not_isIncompressibleVector (hx : IsCompressibleVector k ρ x) :
    ¬IsIncompressibleVector k ρ x := fun hi ↦ hi.2 hx

/-- Compressibility and incompressibility are disjoint. -/
@[simp] theorem not_isCompressibleVector_and_isIncompressibleVector :
    ¬(IsCompressibleVector k ρ x ∧ IsIncompressibleVector k ρ x) :=
  fun ⟨hc, hi⟩ ↦ hi.not_isCompressibleVector hc

/-- The zero vector is not compressible because it is not a unit vector. -/
@[simp] theorem not_isCompressibleVector_zero :
    ¬IsCompressibleVector k ρ (0 : EuclideanSpace 𝕜 ι) := by
  intro hx
  simpa using hx.norm_eq_one

/-- The zero vector is not incompressible because it is not a unit vector. -/
@[simp] theorem not_isIncompressibleVector_zero :
    ¬IsIncompressibleVector k ρ (0 : EuclideanSpace 𝕜 ι) := by
  intro hx
  simpa using hx.norm_eq_one

/-- Compressible and incompressible vectors partition the unit sphere. -/
@[simp] theorem isCompressibleVector_or_isIncompressibleVector_iff :
    IsCompressibleVector k ρ x ∨ IsIncompressibleVector k ρ x ↔ ‖x‖ = 1 := by
  simp only [IsIncompressibleVector, IsCompressibleVector]
  tauto

/-- Increasing the sparsity bound or the approximation radius preserves compressibility. -/
theorem IsCompressibleVector.mono (hx : IsCompressibleVector k ρ x) (hkl : k ≤ l) (hρσ : ρ ≤ σ) :
    IsCompressibleVector l σ x := by
  obtain ⟨hn, s, hs, y, hy, hd⟩ := hx
  exact ⟨hn, s, hs.trans hkl, y, hy, hd.trans hρσ⟩

/-- Decreasing the sparsity bound or the approximation radius preserves incompressibility. -/
theorem IsIncompressibleVector.mono (hx : IsIncompressibleVector l σ x)
    (hkl : k ≤ l) (hρσ : ρ ≤ σ) :
    IsIncompressibleVector k ρ x :=
  ⟨hx.1, fun h ↦ hx.2 (h.mono hkl hρσ)⟩

/-- Sparse approximation is equivalent to a bound on the squared mass outside a set of at most
`k` coordinates. This includes zero radius and zero sparsity. -/
theorem isCompressibleVector_iff_sum_compl_le [DecidableEq ι] (hρ : 0 ≤ ρ) :
    IsCompressibleVector k ρ x ↔ ‖x‖ = 1 ∧
      ∃ s : Finset ι, s.card ≤ k ∧ (∑ i ∈ sᶜ, ‖x i‖ ^ 2) ≤ ρ ^ 2 := by
  classical
  constructor
  · rintro ⟨hn, s, hs, y, hy, hd⟩
    refine ⟨hn, s, hs, ?_⟩
    calc
      ∑ i ∈ sᶜ, ‖x i‖ ^ 2 = ∑ i ∈ sᶜ, ‖(x - y) i‖ ^ 2 := by
        apply sum_congr rfl
        intro i hi
        simp [hy i (mem_compl.mp hi)]
      _ ≤ ∑ i, ‖(x - y) i‖ ^ 2 := sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
      _ = ‖x - y‖ ^ 2 := (EuclideanSpace.norm_sq_eq _).symm
      _ ≤ ρ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  · rintro ⟨hn, s, hs, ht⟩
    let y : EuclideanSpace 𝕜 ι := WithLp.toLp 2 fun i ↦ if i ∈ s then x i else 0
    refine ⟨hn, s, hs, y, (fun i hi ↦ by simp [y, hi]), ?_⟩
    apply (sq_le_sq₀ (norm_nonneg _) hρ).mp
    have heq : ‖x - y‖ ^ 2 = ∑ i ∈ sᶜ, ‖x i‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      conv_rhs => rw [← Finset.univ_inter sᶜ, ← Finset.sum_ite_mem]
      apply sum_congr rfl
      intro i _
      by_cases hi : i ∈ s <;> simp [y, hi]
    rwa [heq]

/-- An incompressible vector has squared mass greater than `ρ²` outside every set of at most
`k` coordinates. -/
theorem isIncompressibleVector_iff_sum_compl_gt [DecidableEq ι] (hρ : 0 ≤ ρ) :
    IsIncompressibleVector k ρ x ↔ ‖x‖ = 1 ∧
      ∀ s : Finset ι, s.card ≤ k → ρ ^ 2 < ∑ i ∈ sᶜ, ‖x i‖ ^ 2 := by
  rw [IsIncompressibleVector, isCompressibleVector_iff_sum_compl_le hρ]
  simp only [not_and, not_exists, not_le]
  tauto

/-- At radius zero, compressibility means that the unit vector itself has at most `k` nonzero
coordinates. -/
theorem isCompressibleVector_zero_right_iff :
    IsCompressibleVector k 0 x ↔ ‖x‖ = 1 ∧ ∃ s : Finset ι, s.card ≤ k ∧ ∀ i ∉ s, x i = 0 := by
  constructor
  · rintro ⟨hn, s, hs, y, hy, hd⟩
    have hxy : x = y := sub_eq_zero.mp (norm_le_zero_iff.mp hd)
    exact ⟨hn, s, hs, hxy ▸ hy⟩
  · rintro ⟨hn, s, hs, hx⟩
    exact ⟨hn, s, hs, x, hx, by simp⟩

/-- A compressible vector at radius less than one is within twice that radius of a sparse
unit vector with the same sparsity budget. -/
theorem IsCompressibleVector.exists_isCompressibleVector_zero_dist_le
    (hx : IsCompressibleVector k ρ x) (hρ : ρ < 1) :
    ∃ y : EuclideanSpace 𝕜 ι, IsCompressibleVector k 0 y ∧ dist x y ≤ 2 * ρ := by
  obtain ⟨hn, s, hs, y, hy, hxy⟩ := isCompressibleVector_iff.mp hx
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp [hn] at hxy
    linarith
  let u := NormedSpace.normalize y
  have hu : ‖u‖ = 1 := NormedSpace.norm_normalize hy0
  refine ⟨u, isCompressibleVector_zero_right_iff.mpr
    ⟨hu, s, hs, fun i hi ↦ by simp [u, NormedSpace.normalize, hy i hi]⟩, ?_⟩
  rw [← dist_eq_norm] at hxy
  exact (NormedSpace.dist_normalize_le_two_mul_dist hn y).trans (by linarith)

/-- At radius zero, an incompressible unit vector has more than `k` nonzero coordinates. -/
theorem isIncompressibleVector_zero_right_iff :
    IsIncompressibleVector k 0 x ↔ ‖x‖ = 1 ∧
      ∀ s : Finset ι, s.card ≤ k → ∃ i ∉ s, x i ≠ 0 := by
  rw [isIncompressibleVector_iff, isCompressibleVector_zero_right_iff]
  push Not
  tauto

/-- With zero sparsity budget, a unit vector is compressible exactly at radii at least one. -/
theorem isCompressibleVector_zero_left_iff :
    IsCompressibleVector 0 ρ x ↔ ‖x‖ = 1 ∧ 1 ≤ ρ := by
  constructor
  · rintro ⟨hn, s, hs, y, hy, hd⟩
    have hs : s = ∅ := Finset.card_eq_zero.mp (by omega)
    have hy : y = 0 := by
      ext i
      exact hy i (by simp [hs])
    simpa [hy, hn] using And.intro hn hd
  · rintro ⟨hn, hρ⟩
    exact ⟨hn, ∅, by simp, 0, by simp, by simpa [hn] using hρ⟩

/-- With zero sparsity budget, a unit vector is incompressible exactly at radii below one. -/
theorem isIncompressibleVector_zero_left_iff :
    IsIncompressibleVector 0 ρ x ↔ ‖x‖ = 1 ∧ ρ < 1 := by
  rw [isIncompressibleVector_iff, isCompressibleVector_zero_left_iff]
  simp only [not_and, not_le]
  tauto

/-- If all coordinates are allowed, every unit vector is compressible at any nonnegative
radius. -/
theorem isCompressibleVector_of_card_le (hn : ‖x‖ = 1) (hk : Fintype.card ι ≤ k) (hρ : 0 ≤ ρ) :
    IsCompressibleVector k ρ x := by
  classical
  exact ⟨hn, univ, by simpa using hk, x, by simp, by simpa using hρ⟩

/-- Allowing all coordinates rules out incompressibility at nonnegative radii. -/
theorem not_isIncompressibleVector_of_card_le (hk : Fintype.card ι ≤ k) (hρ : 0 ≤ ρ) :
    ¬IsIncompressibleVector k ρ x :=
  fun hx ↦ hx.not_isCompressibleVector (isCompressibleVector_of_card_le hx.norm_eq_one hk hρ)

/-- Radius at least one makes every unit vector compressible, even with zero allowed
coordinates. -/
theorem isCompressibleVector_of_one_le (hn : ‖x‖ = 1) (hρ : 1 ≤ ρ) :
    IsCompressibleVector k ρ x :=
  ⟨hn, ∅, by simp, 0, by simp, by simpa [hn] using hρ⟩

/-- Radii at least one rule out incompressibility at every sparsity budget. -/
theorem not_isIncompressibleVector_of_one_le (hρ : 1 ≤ ρ) :
    ¬IsIncompressibleVector k ρ x :=
  fun hx ↦ hx.not_isCompressibleVector (isCompressibleVector_of_one_le hx.norm_eq_one hρ)

/-- An incompressible vector is spread: the coordinates with norm in `(a, b]` carry squared mass
greater than `ρ² - n a²`, provided at most `k` coordinates have norm exceeding `b`. -/
theorem IsIncompressibleVector.lt_sum_filter_norm (hx : IsIncompressibleVector k ρ x) (hρ : 0 ≤ ρ)
    {a b : ℝ} (hb : (univ.filter fun i ↦ b < ‖x i‖).card ≤ k) :
    ρ ^ 2 - (Fintype.card ι : ℝ) * a ^ 2 <
      ∑ i ∈ univ.filter (fun i ↦ a < ‖x i‖ ∧ ‖x i‖ ≤ b), ‖x i‖ ^ 2 := by
  classical
  let s := univ.filter fun i ↦ b < ‖x i‖
  have ht := (isIncompressibleVector_iff_sum_compl_gt hρ).mp hx |>.2 s hb
  have hsplit : ∑ i ∈ sᶜ, ‖x i‖ ^ 2 ≤
      (Fintype.card ι : ℝ) * a ^ 2 +
        ∑ i ∈ univ.filter (fun i ↦ a < ‖x i‖ ∧ ‖x i‖ ≤ b), ‖x i‖ ^ 2 := by
    calc
      ∑ i ∈ sᶜ, ‖x i‖ ^ 2 ≤
          ∑ i, (a ^ 2 + if a < ‖x i‖ ∧ ‖x i‖ ≤ b then ‖x i‖ ^ 2 else 0) := by
        conv_lhs => rw [← Finset.univ_inter sᶜ, ← Finset.sum_ite_mem]
        apply sum_le_sum
        intro i _
        by_cases hi : i ∈ sᶜ
        · have hib : ‖x i‖ ≤ b := by simpa [s] using hi
          by_cases hia : a < ‖x i‖
          · simp only [hi, ↓reduceIte, hia, hib, and_self]
            linarith [sq_nonneg a]
          · have hle := pow_le_pow_left₀ (norm_nonneg (x i)) (le_of_not_gt hia) 2
            simp only [hi, ↓reduceIte, hia, false_and]
            linarith
        · simp only [hi, ↓reduceIte]
          positivity
      _ = _ := by rw [sum_add_distrib]; simp [sum_filter]
  linarith

/-- More than `k` coordinates of an incompressible vector have norm exceeding a threshold `a`
satisfying `n a² ≤ ρ²`. -/
theorem IsIncompressibleVector.lt_card_filter_norm (hx : IsIncompressibleVector k ρ x) (hρ : 0 ≤ ρ)
    {a : ℝ} (haρ : (Fintype.card ι : ℝ) * a ^ 2 ≤ ρ ^ 2) :
    k < (univ.filter fun i ↦ a < ‖x i‖).card := by
  classical
  by_contra h
  have hsum := hx.lt_sum_filter_norm hρ (a := a) (b := a) (Nat.le_of_not_gt h)
  rw [Finset.filter_eq_empty_iff.mpr (fun _ _ hi ↦ hi.1.not_ge hi.2), sum_empty] at hsum
  linarith

/-- An incompressible vector has more than `(k + 1) ρ² / 2` coordinates with norms between
`ρ / √(2n)` and `1 / √(k + 1)`, where `n` is the number of coordinates.
This is the spread lemma of Rudelson–Vershynin, including zero sparsity. -/
theorem IsIncompressibleVector.exists_finset_lt_card_and_forall_norm
    (hx : IsIncompressibleVector k ρ x) (hρ : 0 ≤ ρ) :
    ∃ s : Finset ι, (k + 1 : ℝ) * ρ ^ 2 / 2 < (s.card : ℝ) ∧
      ∀ i ∈ s, ρ / Real.sqrt (2 * Fintype.card ι) < ‖x i‖ ∧
        ‖x i‖ ≤ 1 / Real.sqrt (k + 1) := by
  classical
  let s := univ.filter fun i ↦ ρ / Real.sqrt (2 * Fintype.card ι) < ‖x i‖ ∧
    ‖x i‖ ≤ 1 / Real.sqrt (k + 1)
  refine ⟨s, ?_, fun i hi ↦ (mem_filter.mp hi).2⟩
  have hkp : (0 : ℝ) < k + 1 := by positivity
  have hsqrt : (Real.sqrt (k + 1 : ℝ)) ^ 2 = k + 1 := Real.sq_sqrt hkp.le
  -- Remove the small coordinates from the mass outside the large coordinates.
  have hmass := hx.lt_sum_filter_norm hρ (a := ρ / Real.sqrt (2 * Fintype.card ι))
    (PiLp.card_filter_lt_norm_le (k := k) (t := 1 / Real.sqrt (k + 1))
      (by positivity) (by
      rw [hx.norm_eq_one, div_pow, one_pow, hsqrt]
      exact (mul_one_div_cancel (ne_of_gt hkp)).ge))
  have hsmall : (Fintype.card ι : ℝ) * (ρ / Real.sqrt (2 * Fintype.card ι)) ^ 2 =
      ρ ^ 2 / 2 := by
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by
      have := lt_of_not_ge (fun h ↦ not_isIncompressibleVector_of_card_le h hρ hx)
      exact_mod_cast (Nat.ne_zero_of_lt this)
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp [hn]
  rw [hsmall] at hmass
  -- Bound each remaining squared coordinate by 1/(k + 1) to count the spread coordinates.
  have hbound : ∑ i ∈ s, ‖x i‖ ^ 2 ≤ (s.card : ℝ) / (k + 1) := by
    calc
      _ ≤ ∑ _i ∈ s, (1 / Real.sqrt (k + 1 : ℝ)) ^ 2 :=
        sum_le_sum fun i hi ↦ pow_le_pow_left₀ (norm_nonneg _) (mem_filter.mp hi).2.2 2
      _ = _ := by simp [hsqrt, div_eq_mul_inv]
  have hfinal := (lt_div_iff₀ hkp).mp (hmass.trans_le hbound)
  nlinarith

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] in
/-- A small linear combination with incompressible coefficients forces more than `k` column
distances to be small. The threshold `a` may be any nonnegative number with `n a² ≤ ρ²`. -/
theorem IsIncompressibleVector.lt_card_filter_infDist_span_range_ne
    {k : ℕ} {ρ a ε : ℝ} {x : EuclideanSpace 𝕜 ι} (hx : IsIncompressibleVector k ρ x)
    (hρ : 0 ≤ ρ) (ha : 0 ≤ a) (haρ : (Fintype.card ι : ℝ) * a ^ 2 ≤ ρ ^ 2)
    (v : ι → E) (hv : ‖∑ i, x i • v i‖ < a * ε) :
    k < (univ.filter fun i ↦ infDist (v i)
      (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v j) : Set E) < ε).card := by
  apply (hx.lt_card_filter_norm hρ haρ).trans_le
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  have hd := norm_mul_infDist_span_range_ne_le v (fun j ↦ x j) i
  have he : 0 < ε := by nlinarith [norm_nonneg (∑ j, x j • v j)]
  by_contra h
  have hεd : ε ≤ infDist (v i)
      (Submodule.span 𝕜 (range fun j : {j // j ≠ i} ↦ v j) : Set E) := le_of_not_gt h
  have hm := mul_le_mul_of_nonneg_left hεd (norm_nonneg (x i))
  nlinarith

end TauCeti
