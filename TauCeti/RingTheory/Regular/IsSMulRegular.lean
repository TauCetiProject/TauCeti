/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Regularity on quotients by divisible submodules

Let `R` be a commutative ring and `r : R`. If multiplication by `r` is injective on an `R`-module
`M` and a submodule `P` is `r`-divisible, that is `P ≤ r • P`, then multiplication by `r` stays
injective on `M ⧸ P`. The divisibility of `P` cannot be dropped: `ℤ ⊆ ℚ` is not `p`-divisible,
and `ℚ ⧸ ℤ` has nonzero `p`-torsion. A divisible submodule of this kind is `⋂ₙ rⁿ M`: if `r`
is regular on `M`, then `r (⋂ₙ rⁿ M) = ⋂ₙ rⁿ M`.

For `R = ℤ` this passes the unique divisibility of a tensor power of the multiplicative group of
an algebraically closed field to its quotient by a divisible group of relations, as in the unique
divisibility of its Milnor K-groups in degrees at least two.

## Main results

* `IsSMulRegular.quotient_of_le_smul`: multiplication by `r` stays injective on the quotient by
  an `r`-divisible submodule.
* `IsSMulRegular.smul_iInf_pow_smul_top`: for regular `r`, `⋂ₙ rⁿ M` is divisible by `r`.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, Proposition 6.4.1 and Exercise 7.3.
-/

public section

open scoped Pointwise

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {r : R}

/-- If multiplication by `r` is injective on `M` and the submodule `P` is `r`-divisible, that is
`P ≤ r • P`, then multiplication by `r` is injective on `M ⧸ P`. -/
theorem IsSMulRegular.quotient_of_le_smul (h : IsSMulRegular M r) {P : Submodule R M}
    (hP : P ≤ r • P) : IsSMulRegular (M ⧸ P) r :=
  (h.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul P).2 (inf_le_right.trans hP)

open Submodule in
/-- **`⋂ₙ rⁿ M` is divisible by `r`.** If `r` is regular on `M`, every element of `⋂ₙ rⁿ M` is
`r` times an element of `⋂ₙ rⁿ M`. -/
theorem IsSMulRegular.smul_iInf_pow_smul_top (hM : IsSMulRegular M r) :
    r • ⨅ n : ℕ, (r ^ n • ⊤ : Submodule R M) = ⨅ n : ℕ, r ^ n • ⊤ := by
  refine le_antisymm (fun x hx ↦ ?_) fun x hx ↦ ?_
  · obtain ⟨y, hy, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp hx
    refine (mem_iInf _).mpr fun n ↦ ?_
    obtain ⟨z, -, rfl⟩ := (mem_smul_pointwise_iff_exists _ _ _).mp ((mem_iInf _).mp hy n)
    exact (mem_smul_pointwise_iff_exists _ _ _).mpr ⟨r • z, trivial, smul_comm _ _ _⟩
  · simp only [mem_iInf, mem_smul_pointwise_iff_exists, mem_top, true_and] at hx
    obtain ⟨y, hy⟩ := hx 1
    rw [pow_one] at hy
    refine ⟨y, (mem_iInf _).mpr fun n ↦ ?_, hy⟩
    -- `x = rⁿ⁺¹ • z`, and cancelling `r` from `r • y = r • (rⁿ • z)` gives `y = rⁿ • z`.
    obtain ⟨z, hz⟩ := hx (n + 1)
    refine (mem_smul_pointwise_iff_exists _ _ _).mpr ⟨z, trivial, hM ?_⟩
    beta_reduce
    rw [hy, ← hz, pow_succ', mul_smul]
