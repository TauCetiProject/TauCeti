/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The multiplicative rank of exponentials of `ℚ`-linearly independent numbers

Let `λ₁, …, λₘ ∈ ℂ` be linearly independent over `ℚ` and `αⱼ = exp λⱼ`. An exponent vector
`s ∈ ℤᵐ` with `α₁ ^ s₁ ⋯ αₘ ^ sₘ = 1` has `s₁ λ₁ + ⋯ + sₘ λₘ ∈ 2πiℤ`. Since `s ↦ Σ sⱼ λⱼ` is
injective, these vectors form a subgroup of `ℤᵐ` embedding into `2πiℤ`, so of rank at most one.
By rank-nullity, the `αⱼ` generate a subgroup of `ℂˣ` of rank at least `m - 1`.

The bound `m - 1` cannot be improved to `m`: for `λ₁ = 2πi` the exponential `α₁ = 1` is torsion.
This is why Waldschmidt's rank argument (Proposition 9.16) assumes only that the
`αⱼ` have multiplicative rank at least `m - 1`.

## Main results

* `LinearIndependent.le_finrank_span_ofMul_add_one_of_coe_eq_exp`: if `λ₁, …, λₘ` are linearly
  independent over `ℚ` and `αⱼ = exp λⱼ`, then the `αⱼ` generate a subgroup of `ℂˣ` of rank at
  least `m - 1`.

## References

* M. Waldschmidt, *Diophantine Approximation on Linear Algebraic Groups*, Springer (2000),
  §9.2.3, Proposition 9.16.
-/

public section

open LinearMap Module Submodule

namespace LinearIndependent

/-- If `λ₁, …, λₘ ∈ ℂ` are linearly independent over `ℚ`, then `αⱼ = exp λⱼ` generate a subgroup
of `ℂˣ` of rank at least `m - 1`. -/
theorem le_finrank_span_ofMul_add_one_of_coe_eq_exp {m : ℕ} {l : Fin m → ℂ}
    (hl : LinearIndependent ℚ l) (α : Fin m → ℂˣ) (hα : ∀ j, (α j : ℂ) = Complex.exp (l j)) :
    m ≤ finrank ℤ (span ℤ (Set.range fun j ↦ Additive.ofMul (α j))) + 1 := by
  set φ := Fintype.linearCombination ℤ fun j ↦ Additive.ofMul (α j)
  set ψ := Fintype.linearCombination ℤ l
  have hψ : Function.Injective ψ :=
    linearIndependent_iff_injective_fintypeLinearCombination.mp (hl.restrict_scalars' ℤ)
  have hφ (s : Fin m → ℤ) : ((Additive.toMul (φ s) : ℂˣ) : ℂ) = Complex.exp (ψ s) := by
    simp [φ, ψ, Fintype.linearCombination_apply, Complex.exp_sum, toMul_sum, Units.coe_prod,
      hα, ← Complex.exp_intCast_mul]
  have hker (s : ker φ) : ψ.domRestrict (ker φ) s ∈ span ℤ {2 * Real.pi * Complex.I} := by
    obtain ⟨s, hs⟩ := s
    have h1 : Complex.exp (ψ s) = 1 := by
      rw [← hφ, LinearMap.mem_ker.mp hs, toMul_zero, Units.val_one]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
    rw [domRestrict_apply, hn, mem_span_singleton]
    exact ⟨n, by simp⟩
  have hinj : Function.Injective ((ψ.domRestrict (ker φ)).codRestrict _ hker) := fun s t hst ↦
    Subtype.ext (hψ (congrArg Subtype.val hst))
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hspan : finrank ℤ (span ℤ {2 * Real.pi * Complex.I}) ≤ 1 :=
    (finrank_span_le_card _).trans (by simp)
  have h := φ.finrank_range_add_finrank_ker
  rw [finrank_fin_fun, Fintype.range_linearCombination] at h
  omega

end LinearIndependent
