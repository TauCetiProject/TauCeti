/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Gram
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Minkowski
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Reduction

/-!
# The entries of a reduced Gram matrix are bounded by the determinant

Let `L` be a positive definite integral lattice of rank `n` and let `b` be a Minkowski-reduced
basis of `L`. Its norms satisfy `β(b i, b i) ≤ (i!)² λᵢ`
(`TauCeti.IntegralLattice.IsMinkowskiReduced.integralNorm_le_factorial_sq_mul_successiveMinimum`),
so Minkowski's second theorem bounds the product of the diagonal entries of the Gram matrix of
`b` by the determinant:

```text
β(b 0, b 0) ⋯ β(b (n - 1), b (n - 1)) ≤ (0! ⋯ (n - 1)!)² · cₙⁿ · det L,
cₙ = (4 / π) · Γ(n / 2 + 1) ^ (2 / n).
```

The diagonal entries are positive integers, so each of them is at most their product, and every
off-diagonal entry is at most half of a diagonal entry in absolute value. Hence every entry of a
reduced Gram matrix is bounded explicitly in terms of the rank and the determinant. Since every
positive definite lattice has a reduced basis
(`TauCeti.IntegralLattice.IsPosSemidef.exists_isMinkowskiReduced`), every positive definite
lattice of given rank and determinant has a Gram matrix whose entries lie in an explicit bounded
range.

As in `TauCeti.LinearAlgebra.IntegralLattice.PosDef.Minkowski`, the bounds are stated without real
powers, multiplied through by `πⁿ`.

## Main results

* `TauCeti.IntegralLattice.IsMinkowskiReduced.prod_integralNorm_mul_pi_pow_le`: the product of the
  norms of a reduced basis is at most `(∏ᵢ i!)² · 4ⁿ · Γ(n/2 + 1)² · det L / πⁿ`.
* `TauCeti.IntegralLattice.IsMinkowskiReduced.abs_gramMatrix_mul_pi_pow_le`: every entry of the
  Gram matrix of a reduced basis is bounded in absolute value by the same quantity.

## References

* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 12, §1.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §10.
-/

public section

open Module
open scoped Nat

namespace TauCeti.IntegralLattice

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

namespace IsMinkowskiReduced

variable {b : Basis (Fin (finrank ℤ L)) ℤ L}

/-- **The product of the norms of a reduced basis.** For a Minkowski-reduced basis `b` of a
positive definite integral lattice of rank `n`,
`(∏ᵢ β(b i, b i)) · πⁿ ≤ (∏ᵢ i!)² · 4ⁿ · Γ(n/2 + 1)² · det L`. -/
theorem prod_integralNorm_mul_pi_pow_le (hL : L.IsPosDef) (hb : L.IsMinkowskiReduced b) :
    (∏ i, (L.integralNorm (b i) : ℝ)) * Real.pi ^ finrank ℤ L ≤
      (∏ i : Fin (finrank ℤ L), ((i : ℕ)! : ℝ)) ^ 2 * 4 ^ finrank ℤ L *
        Real.Gamma (finrank ℤ L / 2 + 1) ^ 2 * L.determinant := by
  have hle : ∏ i, (L.integralNorm (b i) : ℝ) ≤
      (∏ i : Fin (finrank ℤ L), ((i : ℕ)! : ℝ)) ^ 2 * ∏ i, (L.successiveMinimum i : ℝ) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun i _ ↦ ?_) fun i _ ↦ ?_
    · exact_mod_cast hL.isPosSemidef.integralNorm_nonneg (b i)
    · exact_mod_cast hb.integralNorm_le_factorial_sq_mul_successiveMinimum hL.isPosSemidef i
  calc (∏ i, (L.integralNorm (b i) : ℝ)) * Real.pi ^ finrank ℤ L
      ≤ (∏ i : Fin (finrank ℤ L), ((i : ℕ)! : ℝ)) ^ 2 *
          ((∏ i, (L.successiveMinimum i : ℝ)) * Real.pi ^ finrank ℤ L) := by
        rw [← mul_assoc]
        gcongr
    _ ≤ (∏ i : Fin (finrank ℤ L), ((i : ℕ)! : ℝ)) ^ 2 *
          (4 ^ finrank ℤ L * Real.Gamma (finrank ℤ L / 2 + 1) ^ 2 * L.determinant) := by
        exact mul_le_mul_of_nonneg_left hL.prod_successiveMinimum_mul_pi_pow_le (by positivity)
    _ = _ := by ring

/-- **The entries of a reduced Gram matrix are bounded.** For a Minkowski-reduced basis `b` of a
positive definite integral lattice of rank `n`, every entry `β(b j, b k)` of the Gram matrix of `b`
satisfies `|β(b j, b k)| · πⁿ ≤ (∏ᵢ i!)² · 4ⁿ · Γ(n/2 + 1)² · det L`. -/
theorem abs_gramMatrix_mul_pi_pow_le (hL : L.IsPosDef) (hb : L.IsMinkowskiReduced b)
    (j k : Fin (finrank ℤ L)) :
    |(L.gramMatrix b j k : ℝ)| * Real.pi ^ finrank ℤ L ≤
      (∏ i : Fin (finrank ℤ L), ((i : ℕ)! : ℝ)) ^ 2 * 4 ^ finrank ℤ L *
        Real.Gamma (finrank ℤ L / 2 + 1) ^ 2 * L.determinant := by
  refine le_trans ?_ (hb.prod_integralNorm_mul_pi_pow_le hL)
  gcongr
  -- The norms of the basis vectors are positive integers.
  have hone (i : Fin (finrank ℤ L)) : (1 : ℝ) ≤ L.integralNorm (b i) := by
    exact_mod_cast hL.posDef_integralNorm (b i) (b.ne_zero i)
  -- Each entry is at most a diagonal entry in absolute value, which is at most the product.
  have hjk : |(L.gramMatrix b j k : ℝ)| ≤ L.integralNorm (b j) := by
    rw [gramMatrix_apply]
    obtain rfl | hjk := eq_or_ne j k
    · rw [← integralNorm_apply, abs_of_nonneg (zero_le_one.trans (hone j))]
    · have h := hb.two_mul_abs_integralForm_le hjk
      have h₀ := hL.isPosSemidef.integralNorm_nonneg (b j)
      rw [← Int.cast_abs]
      exact_mod_cast (by linarith : |L.integralForm (b j) (b k)| ≤ L.integralNorm (b j))
  refine hjk.trans ?_
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  exact le_mul_of_one_le_right (zero_le_one.trans (hone j))
    (Finset.one_le_prod₀ fun i _ ↦ hone i)

end IsMinkowskiReduced

end TauCeti.IntegralLattice
