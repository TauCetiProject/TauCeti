/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.LaurentSeries
public import Mathlib.Algebra.Order.Antidiag.Prod
public import Mathlib.Data.Finset.NatAntidiagonal

/-!
# The higher Leibniz rule for Laurent series

The Hasse derivatives of Laurent series satisfy the product rule
`D^[k](f g) = ∑ i + j = k, D^[i](f) D^[j](g)` over any ring, including in positive
characteristic. Unlike iterated ordinary derivatives, Hasse derivatives require no division
by factorials. The ordinary product rule is the case `k = 1`.

The proof applies the integer Chu–Vandermonde identity to the finite convolution defining each
coefficient. Translating the summation indices accounts for the shifts of exponents, including
negative exponents. Terms killed by binomial coefficients are omitted using
`Finset.sum_bij_ne_zero`, so no domain hypothesis is needed.

Adapted from Moritz Firsching's Mathlib PR #42471, *add Leibniz rule*:
https://github.com/leanprover-community/mathlib4/pull/42471 . The argument here also works over
noncommutative rings and uses a nonzero-term reindexing of the coefficient sums.
-/

public section

open HahnSeries Finset.HasAntidiagonal
open scoped LaurentSeries

namespace LaurentSeries

variable {R : Type*} [Ring R]

/-- The coefficient of a product of Hasse derivatives, with the convolution indexed by the
supports of the original Laurent series. -/
private theorem coeff_hasseDeriv_mul (i j : ℕ) (f g : R⸨X⸩) (n : ℤ) :
    (hasseDeriv R i f * hasseDeriv R j g).coeff n =
      ∑ x ∈ Finset.antidiagonal f.isPWO_support g.isPWO_support (n + (i + j : ℕ)),
        (Ring.choose x.1 i • f.coeff x.1) * (Ring.choose x.2 j • g.coeff x.2) := by
  classical
  rw [coeff_mul]
  symm
  refine Finset.sum_bij_ne_zero (fun x _ _ ↦ (x.1 - (i : ℤ), x.2 - (j : ℤ)))
    ?_ ?_ ?_ ?_
  · intro x hx hne
    obtain ⟨_, _, hx⟩ := Finset.mem_antidiagonal.mp hx
    refine Finset.mem_antidiagonal.mpr ⟨?_, ?_, by push_cast at hx; omega⟩
    · rw [mem_support, hasseDeriv_coeff, sub_add_cancel]
      exact left_ne_zero_of_mul hne
    · rw [mem_support, hasseDeriv_coeff, sub_add_cancel]
      exact right_ne_zero_of_mul hne
  · intro x _ _ y _ _ h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    exact Prod.ext (by dsimp at h₁; omega) (by dsimp at h₂; omega)
  · intro y hy hne
    obtain ⟨hy₁, hy₂, hy⟩ := Finset.mem_antidiagonal.mp hy
    simp only [mem_support, hasseDeriv_coeff] at hy₁ hy₂
    refine ⟨(y.1 + (i : ℤ), y.2 + (j : ℤ)),
      Finset.mem_antidiagonal.mpr ⟨?_, ?_, by push_cast; omega⟩, ?_, ?_⟩
    · exact (mem_support _ _).mpr (right_ne_zero_of_smul hy₁)
    · exact (mem_support _ _).mpr (right_ne_zero_of_smul hy₂)
    · simpa only [hasseDeriv_coeff] using hne
    · simp
  · intro x _ _
    simp only [hasseDeriv_coeff, sub_add_cancel]

/-- **The higher Leibniz rule.** The `k`-th Hasse derivative of a product of Laurent series is
`∑ i + j = k, D^[i](f) D^[j](g)`. This holds over any ring and in every characteristic. -/
theorem hasseDeriv_mul (k : ℕ) (f g : R⸨X⸩) :
    hasseDeriv R k (f * g) =
      ∑ ij ∈ antidiagonal k, hasseDeriv R ij.1 f * hasseDeriv R ij.2 g := by
  classical
  ext n
  rw [hasseDeriv_coeff, coeff_mul, Finset.smul_sum]
  have hterm (x : ℤ × ℤ)
      (hx : x ∈ Finset.antidiagonal f.isPWO_support g.isPWO_support (n + k)) :
      Ring.choose (n + k) k • (f.coeff x.1 * g.coeff x.2) =
        ∑ ij ∈ antidiagonal k,
          (Ring.choose x.1 ij.1 • f.coeff x.1) *
            (Ring.choose x.2 ij.2 • g.coeff x.2) := by
    obtain ⟨_, _, hx⟩ := Finset.mem_antidiagonal.mp hx
    rw [← hx, Ring.add_choose_eq k (Commute.all x.1 x.2), Finset.sum_smul]
    exact Finset.sum_congr rfl fun ij _ ↦ by rw [smul_mul_smul_comm, mul_smul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_comm, coeff_sum]
  refine Finset.sum_congr rfl fun ij hij ↦ ?_
  rw [coeff_hasseDeriv_mul, mem_antidiagonal.mp hij]

/-- **The product rule** for ordinary Laurent differentiation, over any ring. -/
theorem derivative_mul (f g : R⸨X⸩) :
    derivative R (f * g) = derivative R f * g + f * derivative R g := by
  simpa [Finset.Nat.antidiagonal_succ, ← derivative_apply, add_comm] using
    hasseDeriv_mul 1 f g

end LaurentSeries
