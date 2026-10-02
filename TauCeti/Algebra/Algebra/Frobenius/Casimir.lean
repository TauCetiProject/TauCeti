/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# The Casimir element of a trace

Let `φ : A →ₗ[k] k` be a trace on a `k`-algebra `A`, so `φ (a * b) = φ (b * a)`, and let `x` and
`y` be finite families dual to each other for the pairing `(a, b) ↦ φ (a * b)`, in the sense that
every element expands in either family with coefficients read off by pairing against the other:

```text
a = ∑ i, φ (a * y i) • x i,        a = ∑ i, φ (x i * a) • y i.
```

For a symmetric Frobenius algebra these are a basis and its dual basis. The **Casimir element**
`∑ i, x i ⊗ y i` of `A ⊗[k] A` then commutes with `A` in the bimodule sense:

```text
∑ i, (a * x i) ⊗ y i = ∑ i, x i ⊗ (y i * a).
```

This is what makes `1 ↦ ∑ i, x i ⊗ y i` a map of `A`-bimodules `A → A ⊗[k] A`, the coevaluation of
a symmetric Frobenius algebra; for a Frobenius coalgebra in Mathlib's sense
(`Coalgebra.IsFrobenius`) the element is the comultiplication of `1`.

## Main results

* `TauCeti.sum_mul_tmul_eq_sum_tmul_mul`: the Casimir element of a trace commutes with `A`.

## References

* L. Kadison, *New examples of Frobenius extensions*, University Lecture Series 14, AMS, 1999
  (dual bases of Frobenius algebras and extensions, and their Casimir elements).
-/

public section

namespace TauCeti

open scoped TensorProduct

variable {k A : Type*} [CommSemiring k] [Semiring A] [Algebra k A]

/-- **The Casimir element of a trace commutes with the algebra.** If `φ` is a trace on `A` and the
finite families `x` and `y` are dual for `(a, b) ↦ φ (a * b)`, then
`∑ i, (a * x i) ⊗ y i = ∑ i, x i ⊗ (y i * a)` for every `a : A`. -/
theorem sum_mul_tmul_eq_sum_tmul_mul {ι : Type*} [Fintype ι] (φ : A →ₗ[k] k)
    (hφ : ∀ a b : A, φ (a * b) = φ (b * a)) {x y : ι → A}
    (hx : ∀ a : A, ∑ i, φ (a * y i) • x i = a) (hy : ∀ a : A, ∑ i, φ (x i * a) • y i = a)
    (a : A) :
    ∑ i, (a * x i) ⊗ₜ[k] y i = ∑ i, x i ⊗ₜ[k] (y i * a) := by
  -- Expand each `a * x i` in the family `x`; the coefficients then match those of the expansion
  -- of `y j * a` in the family `y`, by the trace property.
  have expand (i : ι) :
      (a * x i) ⊗ₜ[k] y i = ∑ j, x j ⊗ₜ[k] (φ (x i * (y j * a)) • y i) := by
    conv_lhs => rw [← hx (a * x i)]
    rw [TensorProduct.sum_tmul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul, mul_assoc, hφ, mul_assoc]
  simp_rw [expand]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← TensorProduct.tmul_sum, hy]

end TauCeti
