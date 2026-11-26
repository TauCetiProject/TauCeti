/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Spectrum.Box

/-!
# Multiplicities of the Dirichlet eigenvalues of the square `(0, π)²`

On the square `(0, π)²` the Dirichlet eigenvalues of `-Δ` are the sums `k² + l²` of two squares of
positive integers (`TauCeti.PDE.isDirichletEigenvalue_laplacian_boxDomain_iff`), and the
multiplicity of such a value is the number of ordered pairs `(k, l)` that represent it
(`TauCeti.PDE.finrank_eigenspace_dirichletSolutionOperator_boxDomain`). This file reads off two
cases. The least eigenvalue `2 = 1² + 1²` is simple, while `5 = 1² + 2² = 2² + 1²` has
multiplicity `2`, with eigenfunctions `sin x sin 2y` and `sin 2x sin y`. So a Dirichlet eigenvalue
of `-Δ` need not be simple, even on a convex domain; on a connected domain only the least one is
always simple.

The multiplicity is the dimension of the eigenspace of the Dirichlet solution operator
`(-Δ)⁻¹` on `L²((0, π)²)` for the reciprocal eigenvalue (`TauCeti.PDE.dirichletSolutionOperator`),
for any additive Haar measure on the plane.

## Main declarations

* `TauCeti.Examples.DirichletSquare.finrank_eigenspace_dirichletSolutionOperator_two`: the
  eigenvalue `2` is simple.
* `TauCeti.Examples.DirichletSquare.finrank_eigenspace_dirichletSolutionOperator_five`: the
  eigenvalue `5` has multiplicity `2`.
-/

public section

namespace TauCeti.Examples.DirichletSquare

open MeasureTheory Module PDE

variable {mu : Measure (EuclideanSpace ℝ (Fin 2))} [mu.IsAddHaarMeasure]

/-- On `(0, π)²` the multiplicity of a nonzero natural number `κ` as a Dirichlet eigenvalue is the
number of ordered pairs of positive integers `(k₀, k₁)` with `k₀² + k₁² = κ`. -/
private theorem finrank_eigenspace_eq_ncard
    (hcoeff : MemLp (fun x ↦ energyIntegrand ((fun _ ↦ (1 : Matrix (Fin 2) (Fin 2) ℝ)) x)
      ((0 : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) x)
      ((0 : EuclideanSpace ℝ (Fin 2) → ℝ) x)) ⊤
      (mu.restrict (boxDomain (fun _ : Fin 2 ↦ (0 : ℝ)) (fun _ ↦ Real.pi) :
        Set (EuclideanSpace ℝ (Fin 2)))))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) {κ : ℕ} (hκ : κ ≠ 0) :
    finrank ℝ (Module.End.eigenspace (dirichletSolutionOperator hcoeff hcoercive :
      Lp ℝ 2 (mu.restrict (boxDomain (fun _ : Fin 2 ↦ (0 : ℝ)) (fun _ ↦ Real.pi) :
        Set (EuclideanSpace ℝ (Fin 2)))) →ₗ[ℝ]
        Lp ℝ 2 (mu.restrict (boxDomain (fun _ : Fin 2 ↦ (0 : ℝ)) (fun _ ↦ Real.pi) :
          Set (EuclideanSpace ℝ (Fin 2))))) (κ : ℝ)⁻¹) =
      {k : Fin 2 → ℕ | (∀ i, 0 < k i) ∧ k 0 ^ 2 + k 1 ^ 2 = κ}.ncard := by
  rw [finrank_eigenspace_dirichletSolutionOperator_boxDomain (fun _ ↦ Real.pi_pos) hcoeff
    hcoercive (Nat.cast_ne_zero.mpr hκ)]
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq, sub_zero, Fin.sum_univ_two,
    mul_div_cancel_right₀ _ Real.pi_ne_zero]
  norm_cast

/-- The positive solutions of `k₀² + k₁² = κ` are at most `2` when `κ ≤ 8`, which reduces the two
cases below to a finite check. -/
private theorem le_two_of_sq_add_sq_le {k : Fin 2 → ℕ} {κ : ℕ} (hκ : κ ≤ 8)
    (h : k 0 ^ 2 + k 1 ^ 2 = κ) (i : Fin 2) : k i ≤ 2 := by
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> nlinarith

/-- **The least Dirichlet eigenvalue of the square is simple**: `2 = 1² + 1²` in one way only. -/
theorem finrank_eigenspace_dirichletSolutionOperator_two
    (hcoeff : MemLp (fun x ↦ energyIntegrand ((fun _ ↦ (1 : Matrix (Fin 2) (Fin 2) ℝ)) x)
      ((0 : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) x)
      ((0 : EuclideanSpace ℝ (Fin 2) → ℝ) x)) ⊤
      (mu.restrict (boxDomain (fun _ : Fin 2 ↦ (0 : ℝ)) (fun _ ↦ Real.pi) :
        Set (EuclideanSpace ℝ (Fin 2)))))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    finrank ℝ (Module.End.eigenspace (dirichletSolutionOperator hcoeff hcoercive :
      Lp ℝ 2 (mu.restrict (boxDomain (fun _ : Fin 2 ↦ (0 : ℝ)) (fun _ ↦ Real.pi) :
        Set (EuclideanSpace ℝ (Fin 2)))) →ₗ[ℝ]
        Lp ℝ 2 (mu.restrict (boxDomain (fun _ : Fin 2 ↦ (0 : ℝ)) (fun _ ↦ Real.pi) :
          Set (EuclideanSpace ℝ (Fin 2))))) 2⁻¹) = 1 := by
  have hS : {k : Fin 2 → ℕ | (∀ i, 0 < k i) ∧ k 0 ^ 2 + k 1 ^ 2 = 2} = {![1, 1]} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    refine ⟨fun ⟨hpos, hk⟩ ↦ ?_, fun hk ↦ by subst hk; simp⟩
    have h0 := le_two_of_sq_add_sq_le (by norm_num) hk 0
    have h1 := le_two_of_sq_add_sq_le (by norm_num) hk 1
    have p0 := hpos 0
    have p1 := hpos 1
    interval_cases hk0 : k 0 <;> interval_cases hk1 : k 1 <;> simp at hk
    ext i
    fin_cases i <;> simp [hk0, hk1]
  have h := finrank_eigenspace_eq_ncard hcoeff hcoercive (κ := 2) two_ne_zero
  rw [hS, Set.ncard_singleton] at h
  exact_mod_cast h

/-- **A multiple Dirichlet eigenvalue of the square**: `5 = 1² + 2² = 2² + 1²` has multiplicity
`2`, with eigenfunctions `sin x sin 2y` and `sin 2x sin y`. -/
theorem finrank_eigenspace_dirichletSolutionOperator_five
    (hcoeff : MemLp (fun x ↦ energyIntegrand ((fun _ ↦ (1 : Matrix (Fin 2) (Fin 2) ℝ)) x)
      ((0 : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) x)
      ((0 : EuclideanSpace ℝ (Fin 2) → ℝ) x)) ⊤
      (mu.restrict (boxDomain (fun _ : Fin 2 ↦ (0 : ℝ)) (fun _ ↦ Real.pi) :
        Set (EuclideanSpace ℝ (Fin 2)))))
    (hcoercive : IsCoercive (energyFormH1L0 hcoeff)) :
    finrank ℝ (Module.End.eigenspace (dirichletSolutionOperator hcoeff hcoercive :
      Lp ℝ 2 (mu.restrict (boxDomain (fun _ : Fin 2 ↦ (0 : ℝ)) (fun _ ↦ Real.pi) :
        Set (EuclideanSpace ℝ (Fin 2)))) →ₗ[ℝ]
        Lp ℝ 2 (mu.restrict (boxDomain (fun _ : Fin 2 ↦ (0 : ℝ)) (fun _ ↦ Real.pi) :
          Set (EuclideanSpace ℝ (Fin 2))))) 5⁻¹) = 2 := by
  have hS : {k : Fin 2 → ℕ | (∀ i, 0 < k i) ∧ k 0 ^ 2 + k 1 ^ 2 = 5} = {![1, 2], ![2, 1]} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    refine ⟨fun ⟨hpos, hk⟩ ↦ ?_, fun hk ↦ by rcases hk with rfl | rfl <;> simp⟩
    have h0 := le_two_of_sq_add_sq_le (by norm_num) hk 0
    have h1 := le_two_of_sq_add_sq_le (by norm_num) hk 1
    have p0 := hpos 0
    have p1 := hpos 1
    interval_cases hk0 : k 0 <;> interval_cases hk1 : k 1 <;> simp at hk
    · left
      ext i
      fin_cases i <;> simp [hk0, hk1]
    · right
      ext i
      fin_cases i <;> simp [hk0, hk1]
  have h := finrank_eigenspace_eq_ncard hcoeff hcoercive (κ := 5) (by norm_num)
  rw [hS, Set.ncard_pair (by decide)] at h
  exact_mod_cast h

end TauCeti.Examples.DirichletSquare
