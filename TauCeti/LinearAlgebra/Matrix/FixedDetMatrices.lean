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
`0 < a` and `0 ≤ b < |d|`, and Mathlib proves (`FixedDetMatrices.reduce_mem_reps`) that the
reduction algorithm carries every determinant-`n` matrix into it. This file completes that to the
statement that `FixedDetMatrices.reps n` is a set of representatives for the action of `SL(2, ℤ)`
by left multiplication on the determinant-`n` matrices, `n ≠ 0`, and counts it.

## Main results

* `FixedDetMatrices.exists_smul_mem_reps`: for `n ≠ 0`, every determinant-`n` matrix can be moved
  into `FixedDetMatrices.reps n` by `SL(2, ℤ)`.
* `FixedDetMatrices.eq_of_smul_eq_of_mem_reps`: two matrices of `FixedDetMatrices.reps n` in the
  same `SL(2, ℤ)`-orbit are equal.
* `FixedDetMatrices.card_reps`: for `n ≠ 0`, `FixedDetMatrices.reps n` has `σ₁(|n|)` elements.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. 762 (2020), 105--122, arXiv:1711.00327, Section 2: these are the
  representatives `ℳₙ^∞` of `Γ \ ℳₙ`.
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
  | h0 A h₁₀ h₀₀ h₀₁ h₁₁ => exact ⟨1, by rw [one_smul]; exact ⟨h₁₀, h₀₀, h₀₁, h₁₁⟩⟩
  | hS B hB =>
    obtain ⟨g, hg⟩ := hB
    exact ⟨g * ModularGroup.S⁻¹, by rwa [mul_smul, inv_smul_smul]⟩
  | hT B hB =>
    obtain ⟨g, hg⟩ := hB
    exact ⟨g * ModularGroup.T⁻¹, by rwa [mul_smul, inv_smul_smul]⟩

/-- The entries of `g • A`, for `g : SL(2, ℤ)`. -/
private lemma val_smul_apply (g : SL(2, ℤ)) (A : FixedDetMatrix (Fin 2) ℤ n) (i j : Fin 2) :
    (g • A).1 i j = g i 0 * A.1 0 j + g i 1 * A.1 1 j := by
  rw [smul_coe, Matrix.mul_apply, Fin.sum_univ_two]

/-- An element of `SL(2, ℤ)` carrying one matrix of `reps n` into
`reps n` is upper unitriangular. -/
private lemma unitriangular_of_smul_mem_reps {A : FixedDetMatrix (Fin 2) ℤ n} {g : SL(2, ℤ)}
    (hA : A ∈ reps n) (hgA : g • A ∈ reps n) :
    g 0 0 = 1 ∧ g 1 0 = 0 ∧ g 1 1 = 1 := by
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    rw [← Matrix.det_fin_two]
    exact g.2
  have h₁₀ := hgA.1
  have h₀₀ := hgA.2.1
  rw [val_smul_apply, hA.1, mul_zero, add_zero] at h₁₀ h₀₀
  have hg₁₀ : g 1 0 = 0 := (mul_eq_zero.mp h₁₀).resolve_right hA.2.1.ne'
  rw [hg₁₀, mul_zero, sub_zero] at hdet
  have hg₀₀ := Int.eq_one_of_mul_eq_one_right (pos_of_mul_pos_left h₀₀ hA.2.1.le).le hdet
  exact ⟨hg₀₀, hg₁₀, by rwa [hg₀₀, one_mul] at hdet⟩

/-- Two matrices of `reps n` in the same `SL(2, ℤ)`-orbit are equal. -/
theorem eq_of_smul_eq_of_mem_reps {A B : FixedDetMatrix (Fin 2) ℤ n} {g : SL(2, ℤ)}
    (hA : A ∈ reps n) (hB : B ∈ reps n) (h : g • A = B) :
    A = B := by
  subst h
  obtain ⟨hg₀₀, hg₁₀, hg₁₁⟩ := unitriangular_of_smul_mem_reps hA hB
  obtain ⟨hA₁₀, -, hA₀₁, hA₁₁⟩ := hA
  obtain ⟨-, -, hB₀₁, hB₁₁⟩ := hB
  simp only [val_smul_apply, hg₀₀, hg₁₀, hg₁₁, one_mul, zero_mul, zero_add] at hB₀₁ hB₁₁
  have hg₀₁ : g 0 1 = 0 := by
    have hd : 0 < |A.1 1 1| := (abs_nonneg _).trans_lt hA₁₁
    rw [abs_of_nonneg hA₀₁] at hA₁₁
    rw [abs_of_nonneg hB₀₁] at hB₁₁
    have hq : |g 0 1| * |A.1 1 1| < 1 * |A.1 1 1| := by
      rw [← abs_mul, one_mul]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    exact Int.abs_lt_one_iff.mp (lt_of_mul_lt_mul_right hq hd.le)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [val_smul_apply, hg₀₀, hg₀₁, hg₁₀, hg₁₁, hA₁₀]

/-- The diagonal entries of an upper-triangular representative multiply to `n`. -/
private lemma mul_eq_of_mem_reps {A : FixedDetMatrix (Fin 2) ℤ n} (hA : A ∈ reps n) :
    A.1 0 0 * A.1 1 1 = n := by
  have h := A.2
  rwa [Matrix.det_fin_two, hA.1, mul_zero, sub_zero] at h

/-- The lower-right entry of an upper-triangular representative has the sign of `n`. -/
private lemma sign_mul_natAbs_eq_of_mem_reps {A : FixedDetMatrix (Fin 2) ℤ n}
    (hA : A ∈ reps n) : n.sign * ((A.1 1 1).natAbs : ℤ) = A.1 1 1 := by
  have h := congrArg Int.sign (mul_eq_of_mem_reps hA)
  rw [Int.sign_mul, Int.sign_eq_one_of_pos hA.2.1, one_mul] at h
  rw [← h, Int.sign_mul_natAbs]

/-- An upper-triangular representative, recorded by its diagonal `(|a|, |d|)` and its entry
`|b|`. -/
private def repsToSigma (hn : n ≠ 0) (A : reps n) :
    Σ p : n.natAbs.divisorsAntidiagonal, Finset.range p.1.2 :=
  ⟨⟨((A.1.1 0 0).natAbs, (A.1.1 1 1).natAbs), by
      rw [Nat.mem_divisorsAntidiagonal, ← Int.natAbs_mul, mul_eq_of_mem_reps A.2]
      exact ⟨rfl, Int.natAbs_ne_zero.mpr hn⟩⟩,
    ⟨(A.1.1 0 1).natAbs, by
      rw [Finset.mem_range, ← Int.ofNat_lt, Int.natCast_natAbs, Int.natCast_natAbs]
      exact A.2.2.2.2⟩⟩

/-- The upper-triangular representative `(a b; 0 ±d)` with the sign of `n` on `d`. -/
private def sigmaToReps (hn : n ≠ 0) (x : Σ p : n.natAbs.divisorsAntidiagonal, Finset.range p.1.2) :
    reps n :=
  ⟨⟨!![(x.1.1.1 : ℤ), (x.2.1 : ℤ); 0, n.sign * x.1.1.2], by
      have h : ((x.1.1.1 * x.1.1.2 : ℕ) : ℤ) = n.natAbs :=
        congrArg _ (Nat.mem_divisorsAntidiagonal.mp x.1.2).1
      rw [Matrix.det_fin_two_of, mul_zero, sub_zero, mul_left_comm, ← Nat.cast_mul, h,
        Int.sign_mul_natAbs]⟩, by
    have hmem := Nat.mem_divisorsAntidiagonal.mp x.1.2
    refine ⟨rfl, ?_, Int.natCast_nonneg _, ?_⟩
    · have : x.1.1.1 ≠ 0 := left_ne_zero_of_mul (hmem.1 ▸ Int.natAbs_ne_zero.mpr hn)
      simpa [Nat.pos_iff_ne_zero] using this
    · simpa [abs_mul, Int.abs_sign_of_ne_zero hn] using Finset.mem_range.mp x.2.2⟩

/-- Upper-triangular representatives are recorded by their diagonal and upper-right entry. -/
private def repsEquivSigma (hn : n ≠ 0) :
    reps n ≃ Σ p : n.natAbs.divisorsAntidiagonal, Finset.range p.1.2 where
  toFun := repsToSigma hn
  invFun := sigmaToReps hn
  left_inv A := by
    obtain ⟨A, h₁₀, h₀₀, h₀₁, -⟩ := A
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j
    · exact Int.natAbs_of_nonneg h₀₀.le
    · exact Int.natAbs_of_nonneg h₀₁
    · exact h₁₀.symm
    · exact sign_mul_natAbs_eq_of_mem_reps ⟨h₁₀, h₀₀, h₀₁, ‹_›⟩
  right_inv x := by
    refine Sigma.subtype_ext (Subtype.ext (Prod.ext ?_ ?_)) ?_
    · exact Int.natAbs_natCast _
    · simp [repsToSigma, sigmaToReps, Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hn]
    · exact Int.natAbs_natCast _

/-- **The number of upper-triangular representatives**: for `n ≠ 0`, the set
`reps n` has `σ₁(|n|)` elements, one for each divisor `d` of `|n|` and each
`0 ≤ b < d`. -/
theorem card_reps (hn : n ≠ 0) :
    Nat.card (reps n) = ArithmeticFunction.sigma 1 n.natAbs := by
  rw [Nat.card_congr (repsEquivSigma hn), Nat.card_sigma, ArithmeticFunction.sigma_one_apply,
    ← Nat.sum_divisorsAntidiagonal' fun _ d ↦ d]
  simp only [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_range, Finset.sum_coe_sort]

end FixedDetMatrices
