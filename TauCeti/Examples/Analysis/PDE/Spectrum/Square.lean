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

/-- For `κ ≤ 8` the positive solutions of `k₀² + k₁² = κ` lie in `{1, 2}²`, so counting them is a
finite search, which reduces the two cases below to `decide`. -/
private theorem ncard_setOf_sq_add_sq_eq {κ : ℕ} (hκ : κ ≤ 8) :
    {k : Fin 2 → ℕ | (∀ i, 0 < k i) ∧ k 0 ^ 2 + k 1 ^ 2 = κ}.ncard =
      {p ∈ Finset.Icc 1 2 ×ˢ Finset.Icc 1 2 | p.1 ^ 2 + p.2 ^ 2 = κ}.card := by
  have hS : {k : Fin 2 → ℕ | (∀ i, 0 < k i) ∧ k 0 ^ 2 + k 1 ^ 2 = κ} =
      (fun p : ℕ × ℕ ↦ ![p.1, p.2]) ''
        ↑{p ∈ Finset.Icc 1 2 ×ˢ Finset.Icc 1 2 | p.1 ^ 2 + p.2 ^ 2 = κ} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.coe_filter, Finset.mem_product,
      Finset.mem_Icc, Fin.forall_fin_two, Prod.exists]
    constructor
    · rintro ⟨⟨h0, h1⟩, hk⟩
      refine ⟨k 0, k 1, ⟨⟨⟨h0, by nlinarith⟩, h1, by nlinarith⟩, hk⟩, ?_⟩
      ext i
      fin_cases i <;> rfl
    · rintro ⟨m, n, ⟨⟨⟨hm, -⟩, hn, -⟩, hmn⟩, rfl⟩
      exact ⟨⟨hm, hn⟩, hmn⟩
  rw [hS, Set.ncard_image_of_injective _ fun p q h ↦ Prod.ext (congrFun h 0) (congrFun h 1),
    Set.ncard_coe_finset]

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
  have h := finrank_eigenspace_eq_ncard hcoeff hcoercive (κ := 2) two_ne_zero
  rw [ncard_setOf_sq_add_sq_eq (by norm_num)] at h
  exact_mod_cast h.trans (by decide)

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
  have h := finrank_eigenspace_eq_ncard hcoeff hcoercive (κ := 5) (by norm_num)
  rw [ncard_setOf_sq_add_sq_eq (by norm_num)] at h
  exact_mod_cast h.trans (by decide)

end TauCeti.Examples.DirichletSquare
