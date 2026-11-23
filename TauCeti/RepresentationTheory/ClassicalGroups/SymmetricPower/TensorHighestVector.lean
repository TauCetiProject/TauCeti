/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Bihomogeneous
public import TauCeti.RingTheory.MvPolynomial.BinaryMonomial

/-!
# Highest weight vectors in tensor products of binary forms

Write `x = X 0` and `y = X 1` for the two variables, so that the forms of degree `d` are the
symmetric power `Symᵈ(R²)` of the standard representation, on which a matrix acts by the
substitution of standard vectors `TauCeti.polynomialAction`. In the tensor product of the forms of
degree `m` with those of degree `n`, for `r ≤ min m n`, the vector

`v_r = (x ⊗ y - y ⊗ x) ^ r * (x ^ (m - r) ⊗ x ^ (n - r))`

(`TauCeti.polynomialTensorHighest`), computed in the commutative ring `R[x, y] ⊗ R[x, y]`, is a
highest weight vector. In the bihomogeneous model of `MvPolynomial.tensorEquivFinTwoProd` it is the
polynomial `(x₁ y₂ - y₁ x₂) ^ r * x₁ ^ (m - r) * x₂ ^ (n - r)` in two pairs of variables, and in the
monomial basis it is `∑ⱼ (-1) ^ j (r choose j) e_j^m ⊗ e_(r-j)^n`, where
`e_i^d = x ^ (d - i) * y ^ i` is the binary monomial `TauCeti.polynomialMonomial`.

The determinant `x ⊗ y - y ⊗ x` is multiplied by `det g` under the substitution by `g` in both
factors, while `x` is only rescaled by an upper triangular matrix. Hence the upper triangular matrix
`!![a, b; 0, d]` multiplies `v_r` by `a ^ (m + n - r) * d ^ r`: the vector `v_r` is fixed by the
upper unipotent subgroup and has weight `(m + n - r, r)` for the diagonal torus of `GL₂`, so weight
`m + n - 2 r` for the diagonal torus of `SL₂`. Over a field of characteristic zero these are the
highest weight vectors of the summands `det ^ r ⊗ Sym^(m + n - 2 r)(R²)` of the Clebsch–Gordan
decomposition of `Symᵐ(R²) ⊗ Symⁿ(R²)`; that decomposition is not proved here. The abstract
counterparts in the coordinate model `TauCeti.Sl2Std` of the `sl₂`-modules are the vectors
`TauCeti.Sl2Std.cgVector`; the vectors here live on the polynomial model, on which the group acts
by substitution.

## Main definitions

* `TauCeti.polynomialTensorHighest R m n r`: the vector `v_r`, zero unless `r ≤ m` and `r ≤ n`.

## Main results

* `TauCeti.polynomialTensorHighest_eq_sum`: the expansion of `v_r` in binary monomials.
* `TauCeti.tensorEquivFinTwoProd_polynomialTensorHighest`: `v_r` as a bihomogeneous polynomial in
  two pairs of variables.
* `TauCeti.polynomialTensorHighest_mem_range`: `v_r` lies in the tensor product of the forms of
  degrees `m` and `n`.
* `TauCeti.polynomialTensorHighest_ne_zero`: `v_r` is nonzero for `r ≤ min m n`.
* `TauCeti.map_polynomialAction_polynomialTensorHighest`: the substitution by `g` in both factors
  sends `v_r` to `det g ^ r` times `(x ⊗ y - y ⊗ x) ^ r * (g x) ^ (m - r) ⊗ (g x) ^ (n - r)`.
* `TauCeti.map_polynomialAction_upperTriangular_polynomialTensorHighest`: the upper triangular
  matrix `!![a, b; 0, d]` multiplies `v_r` by `a ^ (m + n - r) * d ^ r`, with the special cases
  `TauCeti.map_polynomialAction_unipotent_polynomialTensorHighest` (invariance under the upper
  unipotent subgroup), `TauCeti.map_polynomialAction_diagonal_polynomialTensorHighest` (weight
  `(m + n - r, r)`) and `TauCeti.map_polynomialAction_diagonal_inv_polynomialTensorHighest`
  (weight `m + n - 2 r` for `SL₂`).

## References

* P. Etingof, *Lie Groups and Lie Algebras*, arXiv:2201.09397v5, §11.4, pp. 62–65: the
  representations of `SL₂` on binary forms and the decomposition of their tensor products.
-/

public section

open MvPolynomial Matrix
open scoped TensorProduct

namespace TauCeti

variable (R : Type*) [CommRing R]

/-- The highest weight vector `v_r = (x ⊗ y - y ⊗ x) ^ r * (x ^ (m - r) ⊗ x ^ (n - r))` of weight
`(m + n - r, r)` in the tensor product of the binary forms of degrees `m` and `n`, for `r ≤ m` and
`r ≤ n`; it is zero otherwise. Here `x = X 0` and `y = X 1`. -/
noncomputable def polynomialTensorHighest (m n r : ℕ) :
    MvPolynomial (Fin 2) R ⊗[R] MvPolynomial (Fin 2) R :=
  if r ≤ m ∧ r ≤ n then (X 0 ⊗ₜ X 1 - X 1 ⊗ₜ X 0) ^ r * ((X 0 ^ (m - r)) ⊗ₜ (X 0 ^ (n - r))) else 0

variable {R} {m n r : ℕ}

theorem polynomialTensorHighest_of_le (hm : r ≤ m) (hn : r ≤ n) :
    polynomialTensorHighest R m n r =
      (X 0 ⊗ₜ X 1 - X 1 ⊗ₜ X 0) ^ r * ((X 0 ^ (m - r)) ⊗ₜ (X 0 ^ (n - r))) := by
  simp [polynomialTensorHighest, hm, hn]

theorem polynomialTensorHighest_of_not_le (h : ¬(r ≤ m ∧ r ≤ n)) :
    polynomialTensorHighest R m n r = 0 := by
  simp [polynomialTensorHighest, h]

variable (R m n) in
/-- For `r = 0` the highest weight vector is `x ^ m ⊗ x ^ n`. -/
@[simp]
theorem polynomialTensorHighest_zero : polynomialTensorHighest R m n 0 =
    (X 0 ^ m) ⊗ₜ (X 0 ^ n) := by
  simp [polynomialTensorHighest]

/-- The highest weight vector `v_r` in the bihomogeneous model: the polynomial
`(x₁ y₂ - y₁ x₂) ^ r * x₁ ^ (m - r) * x₂ ^ (n - r)` in two pairs of variables. -/
theorem tensorEquivFinTwoProd_polynomialTensorHighest (hm : r ≤ m) (hn : r ≤ n) :
    tensorEquivFinTwoProd (Fin 2) R (polynomialTensorHighest R m n r) =
      (X (0, 0) * X (1, 1) - X (0, 1) * X (1, 0)) ^ r * X (0, 0) ^ (m - r) *
        X (1, 0) ^ (n - r) := by
  simp [polynomialTensorHighest_of_le hm hn, tensorEquivFinTwoProd_tmul, mul_assoc]

/-- The product `(x ⊗ y) ^ (r - j) * (y ⊗ x) ^ j * (x ^ (m - r) ⊗ x ^ (n - r))` is the tensor
product of binary monomials `e_j^m ⊗ e_(r-j)^n`. -/
private theorem tmul_pow_mul_tmul_pow_mul_tmul {j : ℕ} (hj : j ≤ r) (hm : r ≤ m) (hn : r ≤ n) :
    (X 0 ⊗ₜ[R] X 1 : MvPolynomial (Fin 2) R ⊗[R] MvPolynomial (Fin 2) R) ^ (r - j) *
        (X 1 ⊗ₜ X 0) ^ j * ((X 0 ^ (m - r)) ⊗ₜ (X 0 ^ (n - r))) =
      polynomialMonomial R m j ⊗ₜ polynomialMonomial R n (r - j) := by
  rw [polynomialMonomial_of_le (hj.trans hm), polynomialMonomial_of_le ((Nat.sub_le r j).trans hn),
    Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow,
    Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul]
  congr 1
  · rw [show m - j = r - j + (m - r) by omega, pow_add]
    ring
  · rw [show n - (r - j) = j + (n - r) by omega, pow_add]
    ring

/-- **The expansion of the highest weight vector in binary monomials**:
`v_r = ∑ⱼ (-1) ^ j (r choose j) e_j^m ⊗ e_(r-j)^n`. -/
theorem polynomialTensorHighest_eq_sum (hm : r ≤ m) (hn : r ≤ n) :
    polynomialTensorHighest R m n r =
      ∑ j ∈ Finset.range (r + 1),
        ((-1) ^ j * (r.choose j : R)) •
          (polynomialMonomial R m j ⊗ₜ polynomialMonomial R n (r - j)) := by
  rw [polynomialTensorHighest_of_le hm hn, sub_eq_neg_add, add_pow, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  have hj : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [← tmul_pow_mul_tmul_pow_mul_tmul hj hm hn, ← smul_one_mul, ← Algebra.algebraMap_eq_smul_one]
  rw [map_mul, map_pow, map_neg, map_one, map_natCast]
  ring

/-- The highest weight vector `v_r` lies in the tensor product of the forms of degree `m` with the
forms of degree `n`. -/
theorem polynomialTensorHighest_mem_range :
    polynomialTensorHighest R m n r ∈ LinearMap.range (TensorProduct.map
      (homogeneousSubmodule (Fin 2) R m).subtype (homogeneousSubmodule (Fin 2) R n).subtype) := by
  by_cases h : r ≤ m ∧ r ≤ n
  · rw [polynomialTensorHighest_eq_sum h.1 h.2]
    refine Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ ⟨
      ⟨_, polynomialMonomial_mem_homogeneousSubmodule R m j⟩ ⊗ₜ
        ⟨_, polynomialMonomial_mem_homogeneousSubmodule R n (r - j)⟩, ?_⟩
    simp
  · rw [polynomialTensorHighest_of_not_le h]
    exact Submodule.zero_mem _

/-- The highest weight vector `v_r` is nonzero for `r ≤ min m n`, over a nontrivial ring. -/
theorem polynomialTensorHighest_ne_zero [Nontrivial R] (hm : r ≤ m) (hn : r ≤ n) :
    polynomialTensorHighest R m n r ≠ 0 := by
  intro h
  -- The bihomogeneous polynomial of `v_r` takes the value `1` at `x₁ = x₂ = y₂ = 1`, `y₁ = 0`.
  have := congr(eval (fun p : Fin 2 × Fin 2 ↦ if p = (0, 1) then 0 else 1)
    (tensorEquivFinTwoProd (Fin 2) R $h))
  simp [tensorEquivFinTwoProd_polynomialTensorHighest hm hn] at this

/-- The substitution of standard vectors by `g` in both factors multiplies the determinant
`x ⊗ y - y ⊗ x` by `det g`. -/
theorem map_polynomialAction_tmul_sub_tmul (g : Matrix (Fin 2) (Fin 2) R) :
    Algebra.TensorProduct.map (polynomialAction g) (polynomialAction g)
        (X 0 ⊗ₜ X 1 - X 1 ⊗ₜ X 0) =
      g.det • (X 0 ⊗ₜ X 1 - X 1 ⊗ₜ X 0) := by
  apply (tensorEquivFinTwoProd (Fin 2) R).injective
  simp only [map_sub, map_smul, Algebra.TensorProduct.map_tmul, tensorEquivFinTwoProd_tmul,
    polynomialAction_X, Fin.sum_univ_two, map_add, map_mul, rename_C, rename_X, det_fin_two,
    smul_eq_C_mul, map_sub, map_mul]
  ring

/-- **The action on the highest weight vector**: the substitution of standard vectors by `g` in
both factors sends `v_r` to `det g ^ r • (x ⊗ y - y ⊗ x) ^ r * ((g x) ^ (m - r) ⊗ (g x) ^ (n - r))`,
where `g x = g₀₀ x + g₁₀ y` is the image of the first standard vector. -/
theorem map_polynomialAction_polynomialTensorHighest (g : Matrix (Fin 2) (Fin 2) R)
    (hm : r ≤ m) (hn : r ≤ n) :
    Algebra.TensorProduct.map (polynomialAction g) (polynomialAction g)
        (polynomialTensorHighest R m n r) =
      g.det ^ r • ((X 0 ⊗ₜ X 1 - X 1 ⊗ₜ X 0) ^ r *
        (polynomialAction g (X 0) ^ (m - r)) ⊗ₜ (polynomialAction g (X 0) ^ (n - r))) := by
  rw [polynomialTensorHighest_of_le hm hn, map_mul, map_pow, map_polynomialAction_tmul_sub_tmul,
    smul_pow, Algebra.TensorProduct.map_tmul, map_pow, map_pow, smul_mul_assoc]

/-- **The Borel subgroup scales the highest weight vector**: the upper triangular matrix
`!![a, b; 0, d]` multiplies `v_r` by `a ^ (m + n - r) * d ^ r`. -/
theorem map_polynomialAction_upperTriangular_polynomialTensorHighest (a b d : R) :
    Algebra.TensorProduct.map (polynomialAction !![a, b; 0, d]) (polynomialAction !![a, b; 0, d])
        (polynomialTensorHighest R m n r) =
      (a ^ (m + n - r) * d ^ r) • polynomialTensorHighest R m n r := by
  by_cases h : r ≤ m ∧ r ≤ n
  · obtain ⟨hm, hn⟩ := h
    have hx : polynomialAction !![a, b; 0, d] (X 0 : MvPolynomial (Fin 2) R) = a • X 0 := by
      simp [smul_eq_C_mul]
    rw [map_polynomialAction_polynomialTensorHighest _ hm hn, hx,
      polynomialTensorHighest_of_le hm hn, show m + n - r = r + (m - r) + (n - r) by omega]
    simp only [smul_pow, TensorProduct.smul_tmul_smul, mul_smul_comm, smul_smul, det_fin_two_of]
    module
  · simp [polynomialTensorHighest_of_not_le h]

/-- **The highest weight vector is fixed by the upper unipotent subgroup.** -/
theorem map_polynomialAction_unipotent_polynomialTensorHighest (b : R) :
    Algebra.TensorProduct.map (polynomialAction !![1, b; 0, 1]) (polynomialAction !![1, b; 0, 1])
        (polynomialTensorHighest R m n r) =
      polynomialTensorHighest R m n r := by
  simp [map_polynomialAction_upperTriangular_polynomialTensorHighest]

/-- **The weight of the highest weight vector is `(m + n - r, r)`**: the diagonal matrix
`diag(t₀, t₁)` multiplies `v_r` by `t₀ ^ (m + n - r) * t₁ ^ r`. -/
theorem map_polynomialAction_diagonal_polynomialTensorHighest (t : Fin 2 → R) :
    Algebra.TensorProduct.map (polynomialAction (diagonal t)) (polynomialAction (diagonal t))
        (polynomialTensorHighest R m n r) =
      (t 0 ^ (m + n - r) * t 1 ^ r) • polynomialTensorHighest R m n r := by
  rw [diagonal_fin_two, map_polynomialAction_upperTriangular_polynomialTensorHighest]

/-- **The `SL₂`-weight of the highest weight vector is `m + n - 2 r`**: the diagonal matrix
`diag(t, t⁻¹)` of determinant one multiplies `v_r` by `t ^ (m + n - 2 r)`. -/
theorem map_polynomialAction_diagonal_inv_polynomialTensorHighest (t : Rˣ) :
    Algebra.TensorProduct.map (polynomialAction (diagonal ![(t : R), ↑t⁻¹]))
        (polynomialAction (diagonal ![(t : R), ↑t⁻¹])) (polynomialTensorHighest R m n r) =
      ((t : R) ^ (m + n - 2 * r)) • polynomialTensorHighest R m n r := by
  by_cases h : r ≤ m ∧ r ≤ n
  · rw [map_polynomialAction_diagonal_polynomialTensorHighest]
    congr 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show m + n - r = m + n - 2 * r + r by omega, pow_add, mul_assoc, ← mul_pow, Units.mul_inv,
      one_pow, mul_one]
  · simp [polynomialTensorHighest_of_not_le h]

end TauCeti
