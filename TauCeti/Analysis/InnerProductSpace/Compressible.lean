/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Compressible and incompressible vectors

A unit vector is compressible if it is within a prescribed distance of a vector supported on
at most `k` coordinates. The approximating sparse vector need not be a unit vector.
Incompressibility is characterized by the squared mass outside every set of `k` coordinates.
It forces many coordinates to be large, and a positive proportion to lie between two explicit
thresholds. These facts reduce lower bounds for a matrix on incompressible vectors to distances
of columns from the spans of the other columns.

## References

* M. Rudelson and R. Vershynin, *The Littlewood–Offord problem and invertibility of random
  matrices*, Advances in Mathematics 218 (2008), §3.1 and Lemma 3.4.
-/

public section

open Finset

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
@[simp] theorem isCompressibleVector_zero_iff :
    IsCompressibleVector k 0 x ↔ ‖x‖ = 1 ∧ ∃ s : Finset ι, s.card ≤ k ∧ ∀ i ∉ s, x i = 0 := by
  constructor
  · rintro ⟨hn, s, hs, y, hy, hd⟩
    have hxy : x = y := sub_eq_zero.mp (norm_le_zero_iff.mp hd)
    exact ⟨hn, s, hs, hxy ▸ hy⟩
  · rintro ⟨hn, s, hs, hx⟩
    exact ⟨hn, s, hs, x, hx, by simp⟩

/-- If all coordinates are allowed, every unit vector is compressible at any nonnegative
radius. -/
theorem isCompressibleVector_of_card_le (hn : ‖x‖ = 1) (hk : Fintype.card ι ≤ k) (hρ : 0 ≤ ρ) :
    IsCompressibleVector k ρ x := by
  classical
  exact ⟨hn, univ, by simpa using hk, x, by simp, by simpa using hρ⟩

/-- Radius at least one makes every unit vector compressible, even with zero allowed
coordinates. -/
theorem isCompressibleVector_of_one_le (hn : ‖x‖ = 1) (hρ : 1 ≤ ρ) :
    IsCompressibleVector k ρ x :=
  ⟨hn, ∅, by simp, 0, by simp, by simpa [hn] using hρ⟩

/-- More than `k` coordinates of an incompressible vector exceed a threshold whose total
squared mass is at most `ρ²`. -/
theorem IsIncompressibleVector.lt_card_filter_norm (hx : IsIncompressibleVector k ρ x) (hρ : 0 ≤ ρ)
    {a : ℝ} (haρ : (Fintype.card ι : ℝ) * a ^ 2 ≤ ρ ^ 2) :
    k < (univ.filter fun i ↦ a < ‖x i‖).card := by
  classical
  by_contra h
  let s := univ.filter fun i ↦ a < ‖x i‖
  have hs : s.card ≤ k := Nat.le_of_not_gt h
  have htail := (isIncompressibleVector_iff_sum_compl_gt hρ).mp hx |>.2 s hs
  have hbound : ∑ i ∈ sᶜ, ‖x i‖ ^ 2 ≤ (Fintype.card ι : ℝ) * a ^ 2 := by
    calc
      ∑ i ∈ sᶜ, ‖x i‖ ^ 2 ≤ ∑ i ∈ sᶜ, a ^ 2 := by
        apply sum_le_sum
        intro i hi
        have hi' : ‖x i‖ ≤ a := by simpa [s] using mem_compl.mp hi
        exact pow_le_pow_left₀ (norm_nonneg _) hi' 2
      _ ≤ (Fintype.card ι : ℝ) * a ^ 2 := by
        simpa using sum_le_univ_sum_of_nonneg (s := sᶜ) (fun _ ↦ sq_nonneg a)
  linarith

/-- An incompressible vector is spread: the coordinates between `a` and `b` carry squared mass
greater than `ρ² - n a²`, provided at most `k` coordinates exceed `b`. -/
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

/-- An incompressible vector has more than `k ρ² / 2` coordinates with norms between
`ρ / √(2n)` and `1 / √k`. This is the spread lemma of Rudelson–Vershynin. -/
theorem IsIncompressibleVector.exists_spread (hx : IsIncompressibleVector k ρ x)
    (hρ : 0 ≤ ρ) (hk : 0 < k) :
    ∃ s : Finset ι, (k : ℝ) * ρ ^ 2 / 2 < (s.card : ℝ) ∧
      ∀ i ∈ s, ρ / Real.sqrt (2 * Fintype.card ι) < ‖x i‖ ∧
        ‖x i‖ ≤ 1 / Real.sqrt k := by
  classical
  refine ⟨univ.filter (fun i ↦ ρ / Real.sqrt (2 * Fintype.card ι) < ‖x i‖ ∧
    ‖x i‖ ≤ 1 / Real.sqrt k), ?_, fun i hi ↦ (mem_filter.mp hi).2⟩
  -- A unit vector has at most k coordinates above the upper threshold.
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  have hn : 0 < Fintype.card ι := by
    by_contra h
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp (by omega)
    have : x = 0 := Subsingleton.elim _ _
    simpa [this] using hx.1
  have hsqrt : (Real.sqrt (k : ℝ)) ^ 2 = k := Real.sq_sqrt hkp.le
  have hlarge : (univ.filter fun i ↦ 1 / Real.sqrt k < ‖x i‖).card ≤ k := by
    by_contra h
    let s := univ.filter fun i ↦ 1 / Real.sqrt k < ‖x i‖
    have hcard : k < s.card := Nat.lt_of_not_ge h
    have hsum : (s.card : ℝ) * (1 / (k : ℝ)) ≤ ∑ i ∈ s, ‖x i‖ ^ 2 := by
      calc
        _ = ∑ _i ∈ s, (1 / Real.sqrt (k : ℝ)) ^ 2 := by
          simp [hsqrt]
        _ ≤ _ := sum_le_sum fun i hi ↦
          pow_le_pow_left₀ (by positivity) ((mem_filter.mp hi).2.le) 2
    have htotal : ∑ i ∈ s, ‖x i‖ ^ 2 ≤ 1 := by
      calc _ ≤ ∑ i, ‖x i‖ ^ 2 := sum_le_univ_sum_of_nonneg fun _ ↦ sq_nonneg _
           _ = 1 := by rw [← EuclideanSpace.norm_sq_eq, hx.1]; norm_num
    have : (s.card : ℝ) ≤ k := by nlinarith [(div_le_iff₀ hkp).mp (by
      simpa [div_eq_mul_inv] using hsum.trans htotal)]
    exact (by exact_mod_cast hcard : (k : ℝ) < s.card).not_ge this
  -- Remove the small coordinates from the mass outside those large coordinates.
  have hmass := hx.lt_sum_filter_norm hρ (a := ρ / Real.sqrt (2 * Fintype.card ι))
    hlarge
  have hsmall : (Fintype.card ι : ℝ) * (ρ / Real.sqrt (2 * Fintype.card ι)) ^ 2 =
      ρ ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]
    field_simp
  rw [hsmall] at hmass
  -- Bound each remaining squared coordinate by 1/k to count the spread coordinates.
  have hbound :
      ∑ i ∈ univ.filter (fun i ↦ ρ / Real.sqrt (2 * Fintype.card ι) < ‖x i‖ ∧
        ‖x i‖ ≤ 1 / Real.sqrt k), ‖x i‖ ^ 2 ≤
      ((univ.filter fun i ↦ ρ / Real.sqrt (2 * Fintype.card ι) < ‖x i‖ ∧
        ‖x i‖ ≤ 1 / Real.sqrt k).card : ℝ) / k := by
    calc
      _ ≤ ∑ _i ∈ univ.filter (fun i ↦ ρ / Real.sqrt (2 * Fintype.card ι) < ‖x i‖ ∧
          ‖x i‖ ≤ 1 / Real.sqrt k), (1 / Real.sqrt (k : ℝ)) ^ 2 :=
        sum_le_sum fun i hi ↦ pow_le_pow_left₀ (norm_nonneg _) (mem_filter.mp hi).2.2 2
      _ = _ := by simp [hsqrt, div_eq_mul_inv]
  have hfinal := (lt_div_iff₀ hkp).mp (hmass.trans_le hbound)
  nlinarith

end TauCeti
