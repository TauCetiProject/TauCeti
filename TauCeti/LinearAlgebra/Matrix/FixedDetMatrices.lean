/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

/-!
# Upper-triangular representatives of integral matrices of fixed determinant

Mathlib's `FixedDetMatrices.reps n` is the set of integral matrices `(a b; 0 d)` with `ad = n`,
`0 < a` and `0 ≤ b < |d|`, and Mathlib proves (`FixedDetMatrices.reduce_mem_reps`) that, for
`n ≠ 0`, the reduction algorithm carries every determinant-`n` matrix into it. This file completes
that to the statement that `FixedDetMatrices.reps n` is a set of representatives for the action of
`SL(2, ℤ)` by left multiplication on the determinant-`n` matrices, `n ≠ 0`, and counts it.

## Main results

* `FixedDetMatrices.exists_smul_mem_reps`: for `n ≠ 0`, every determinant-`n` matrix can be moved
  into `FixedDetMatrices.reps n` by `SL(2, ℤ)`.
* `FixedDetMatrices.eq_of_smul_eq_of_mem_reps`: two matrices of `FixedDetMatrices.reps n` in the
  same `SL(2, ℤ)`-orbit are equal.
* `FixedDetMatrices.card_reps`: `FixedDetMatrices.reps n` has `σ₁(|n|)` elements.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. 762 (2020), 105--122, arXiv:1711.00327, Sections 1–2: these are the
  representatives `ℳₙ^∞` of `Γ \ ℳₙ` fixing `∞`.
-/

public section

open Matrix
open scoped MatrixGroups

namespace FixedDetMatrices

variable {n : ℤ}

/-- Every determinant-`n` matrix can be moved into `reps n` by left
multiplication by `SL(2, ℤ)`, when `n ≠ 0`. -/
theorem exists_smul_mem_reps (hn : n ≠ 0) (A : FixedDetMatrix (Fin 2) ℤ n) :
    ∃ g : SL(2, ℤ), g • A ∈ reps n := by
  induction A using induction_on hn with
  | h0 A h₁₀ h₀₀ h₀₁ h₁₁ => exact ⟨1, by simpa using ⟨h₁₀, h₀₀, h₀₁, h₁₁⟩⟩
  | hS B hB | hT B hB =>
    obtain ⟨g, hg⟩ := hB
    exact ⟨g * _⁻¹, by rwa [mul_smul, inv_smul_smul]⟩

private lemma val_smul_apply (g : SL(2, ℤ)) (A : FixedDetMatrix (Fin 2) ℤ n) (i j : Fin 2) :
    (g • A).1 i j = g i 0 * A.1 0 j + g i 1 * A.1 1 j := by
  rw [smul_coe, mul_apply, Fin.sum_univ_two]

private lemma unitriangular_of_smul_mem_reps {A : FixedDetMatrix (Fin 2) ℤ n} {g : SL(2, ℤ)}
    (hA : A ∈ reps n) (hgA : g • A ∈ reps n) : g 0 0 = 1 ∧ g 1 0 = 0 ∧ g 1 1 = 1 := by
  obtain ⟨h₁₀, h₀₀, -⟩ := hgA
  simp only [val_smul_apply, hA.1, mul_zero, add_zero, mul_eq_zero, hA.2.1.ne', or_false] at h₁₀ h₀₀
  have hdet : g 0 0 * g 1 1 = 1 := by
    simpa only [det_fin_two, h₁₀, mul_zero, sub_zero] using g.det_coe
  have hg₀₀ := Int.eq_one_of_mul_eq_one_right (nonneg_of_mul_nonneg_left h₀₀.le hA.2.1) hdet
  exact ⟨hg₀₀, h₁₀, by rwa [hg₀₀, one_mul] at hdet⟩

/-- Two matrices of `reps n` in the same `SL(2, ℤ)`-orbit are equal. -/
theorem eq_of_smul_eq_of_mem_reps {A B : FixedDetMatrix (Fin 2) ℤ n} {g : SL(2, ℤ)}
    (hA : A ∈ reps n) (hB : B ∈ reps n) (h : g • A = B) : A = B := by
  subst h
  obtain ⟨hg₀₀, hg₁₀, hg₁₁⟩ := unitriangular_of_smul_mem_reps hA hB
  obtain ⟨hA₁₀, -, hA₀₁, hA₁₁⟩ := hA
  obtain ⟨-, -, hB₀₁, hB₁₁⟩ := hB
  simp only [val_smul_apply, hg₀₀, hg₁₀, hg₁₁, one_mul, zero_mul, zero_add] at hB₀₁ hB₁₁
  -- `g 0 1 * A 1 1` is a multiple of `|A 1 1|` of absolute value less than `|A 1 1|`
  have hg₀₁ : g 0 1 * A.1 1 1 = 0 :=
    Int.eq_zero_of_abs_lt_dvd ((abs_dvd _ _).2 (dvd_mul_left _ _)) <| by
      simpa only [add_sub_cancel_left] using abs_sub_lt_of_nonneg_of_lt hB₀₁
        ((le_abs_self _).trans_lt hB₁₁) hA₀₁ ((le_abs_self _).trans_lt hA₁₁)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [val_smul_apply, hg₀₀, hg₀₁, hg₁₀, hg₁₁, hA₁₀]

/-- The diagonal entries of an upper-triangular representative multiply to `n`. -/
lemma apply_zero_zero_mul_apply_one_one_of_mem_reps {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps n) : A.1 0 0 * A.1 1 1 = n := by
  simpa only [det_fin_two, hA.1, mul_zero, sub_zero] using A.2

private lemma card_reps_eq_card_sigma (hn : n ≠ 0) :
    Nat.card (reps n) = (n.natAbs.divisorsAntidiagonal.sigma fun p ↦ Finset.range p.2).card := by
  rw [Nat.card_eq_card_toFinset]
  -- record `(a b; 0 d)` by its diagonal `(|a|, |d|)` and its entry `|b|`; conversely,
  -- `((a, d), b)` is the representative `(a b; 0 ±d)` with the sign of `n` on `d`
  refine Finset.card_bij' (fun A _ ↦ ⟨((A.1 0 0).natAbs, (A.1 1 1).natAbs), (A.1 0 1).natAbs⟩)
    (fun x hx ↦ ⟨!![(x.1.1 : ℤ), x.2; 0, n.sign * x.1.2], by
      calc _ = n.sign * ((x.1.1 * x.1.2 : ℕ) : ℤ) := by simp [mul_left_comm]
        _ = n := by
          rw [(Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).1).1, Int.sign_mul_natAbs]⟩)
    (fun A hA ↦ ?_) (fun x hx ↦ ?_) (fun A hA ↦ ?_) (fun x hx ↦ ?_)
  · rw [Set.mem_toFinset] at hA
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal, Finset.mem_range]
    refine ⟨⟨by rw [← Int.natAbs_mul, apply_zero_zero_mul_apply_one_one_of_mem_reps hA],
      Int.natAbs_ne_zero.mpr hn⟩, ?_⟩
    zify
    exact hA.2.2.2
  · obtain ⟨hmem, hlt⟩ := Finset.mem_sigma.mp hx
    exact Set.mem_toFinset.mpr ⟨rfl, Nat.cast_pos.mpr (Nat.pos_of_ne_zero
      (Nat.left_ne_zero_of_mem_divisorsAntidiagonal hmem)), Int.natCast_nonneg _,
      by simpa [abs_mul, Int.abs_sign_of_ne_zero hn] using Finset.mem_range.mp hlt⟩
  · rw [Set.mem_toFinset] at hA
    ext i j
    fin_cases i <;> fin_cases j
    -- the lower-right entry has the sign of `n`, since `n = a * d` with `0 < a`
    exacts [Int.natAbs_of_nonneg hA.2.1.le, Int.natAbs_of_nonneg hA.2.2.1, hA.1.symm, by
      simp [← apply_zero_zero_mul_apply_one_one_of_mem_reps hA, Int.sign_eq_one_of_pos hA.2.1,
        Int.sign_mul_abs]]
  · simp [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hn]

/-- **The number of upper-triangular representatives**: the set `reps n` has `σ₁(|n|)`
elements, one for each divisor `d` of `|n|` and each `0 ≤ b < d`. -/
theorem card_reps (n : ℤ) : Nat.card (reps n) = ArithmeticFunction.sigma 1 n.natAbs := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [card_reps_eq_card_sigma hn, Finset.card_sigma, ArithmeticFunction.sigma_one_apply,
    ← Nat.sum_divisorsAntidiagonal' fun _ d ↦ d]
  simp

end FixedDetMatrices
