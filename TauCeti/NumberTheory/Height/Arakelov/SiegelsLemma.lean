/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.Arakelov.BombieriVaaler

/-!
# Siegel's lemma in the sup norm, after Bombieri and Vaaler

A nonzero subspace `V` of `ℚ^ι` of dimension `k` contains a nonzero integral vector `z` with
`‖z‖ ≤ H(V) ^ (1 / k)`, where `‖z‖ = max_i |z i|` is the sup norm and `H(V)` is the absolute
Euclidean height `Submodule.subspaceHeight V`. For the space of solutions of a system `A x = 0`
of `p` independent linear equations with integer coefficients in `n > p` unknowns, this is
Bombieri and Vaaler's sup-norm form of Siegel's lemma: there is a nonzero integral solution with
`‖x‖ ≤ (√det (A Aᵀ) / g) ^ (1 / (n - p))`, where `g` is the greatest common divisor of the
maximal minors of `A`. The classical bound of Siegel, in Mathlib as
`Int.Matrix.exists_ne_zero_int_vec_norm_le`, is
`‖x‖ ≤ (n · max 1 (max |A i j|)) ^ (p / (n - p))`. By
Hadamard's inequality, `√det (A Aᵀ)` is at most the product of the Euclidean norms of the rows of
`A`, so the bound here is at most `(√n · max |A i j|) ^ (p / (n - p))`; and unlike the classical
bound, it depends on `A` only through its rational row space, since it is the height of the
solution space.

The independent primitive vectors of
`Submodule.exists_linearIndependent_intPoints_prod_norm_le` have product of sup norms at most
`H(V)`. At least one has norm at most the kth root of that bound. Thus this theorem is the
smallest-vector corollary of the existing product theorem and uses the same cube-slicing and
Minkowski second-theorem implementation.

## Main results

* `Submodule.exists_ne_zero_mem_intPoints_norm_le`: a nonzero integral point of `V` of sup norm at
  most `H(V) ^ (1 / k)`.
* `Matrix.exists_ne_zero_mulVec_eq_zero_norm_le`: Bombieri and Vaaler's Theorem 1 over `ℤ`.

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32,
  Theorem 1.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  §2.9.
-/

public section

noncomputable section

open Module TauCeti

private theorem exists_le_rpow_inv_of_prod_le {k : ℕ} (hk : 0 < k) {f : Fin k → ℝ}
    {B : ℝ} (hB : 0 < B) (hle : ∏ i, f i ≤ B) : ∃ i, f i ≤ B ^ (k : ℝ)⁻¹ := by
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  by_contra! h
  have hprod := Finset.prod_lt_prod_of_nonempty₀
    (fun _ _ => Real.rpow_pos_of_pos hB _) (fun i _ => h i) Finset.univ_nonempty
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Real.rpow_inv_natCast_pow hB.le hk.ne'] at hprod
  exact hprod.not_ge hle

namespace Submodule

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- **Siegel's lemma for a rational subspace, in the sup norm.** A nonzero subspace `V` of `ℚ^ι`
contains a nonzero integral point `z` whose sup norm is at most `H(V) ^ (1 / k)`, where `H(V)` is
the absolute Euclidean height of `V` and `k` its dimension. -/
theorem exists_ne_zero_mem_intPoints_norm_le {V : Submodule ℚ (ι → ℚ)} (hV : V ≠ ⊥) :
    ∃ z ∈ V.intPoints, z ≠ 0 ∧ ‖z‖ ≤ V.subspaceHeight ^ (finrank ℚ V : ℝ)⁻¹ := by
  have : Nontrivial V := Submodule.nontrivial_iff_ne_bot.mpr hV
  obtain ⟨z, hz, hzV, _, hle⟩ := V.exists_linearIndependent_intPoints_prod_norm_le
  obtain ⟨i, hi⟩ := exists_le_rpow_inv_of_prod_le finrank_pos (Submodule.subspaceHeight_pos V) hle
  exact ⟨z i, hzV i, hz.ne_zero i, hi⟩

end Submodule

namespace Matrix

variable {ι : Type*} [Fintype ι] {p : ℕ}

/-- **Bombieri and Vaaler's Siegel lemma over `ℤ`, in the sup norm.** Let `A` be a `p × n` integer
matrix with linearly independent rows and `p < n`, and let `g` be the greatest common divisor of
its maximal minors. Then `A x = 0` has a nonzero integral solution `x` with
`‖x‖ ≤ (√det (A Aᵀ) / g) ^ (1 / (n - p))`, where `‖x‖ = max_i |x i|`. -/
theorem exists_ne_zero_mulVec_eq_zero_norm_le {A : Matrix (Fin p) ι ℤ}
    (hA : LinearIndependent ℚ (A.map ((↑) : ℤ → ℚ)).row) (hp : p < Fintype.card ι) :
    ∃ x : ι → ℤ, x ≠ 0 ∧ A *ᵥ x = 0 ∧
      ‖x‖ ≤ (√((A * Aᵀ).det : ℝ) / (A.minorGcd : ℝ)) ^
        ((Fintype.card ι : ℝ) - p)⁻¹ := by
  obtain ⟨x, hx, hxker, _, hle⟩ := exists_linearIndependent_mulVec_eq_zero_prod_norm_le hA
  have hB : 0 < √((A * Aᵀ).det : ℝ) / (A.minorGcd : ℝ) :=
    lt_of_lt_of_le (Finset.prod_pos fun i _ => norm_pos_iff.mpr (hx.ne_zero i)) hle
  obtain ⟨i, hi⟩ := exists_le_rpow_inv_of_prod_le (Nat.sub_pos_of_lt hp) hB hle
  refine ⟨x i, hx.ne_zero i, hxker i, ?_⟩
  simpa only [Nat.cast_sub hp.le] using hi

end Matrix
