/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import TauCeti.Algebra.MvPolynomial.HasseDeriv.Basic
public import TauCeti.Data.Finsupp.Weight

/-!
# Hasse derivatives of weighted homogeneous polynomials

The Hasse derivative `∂^j` lowers the weight of every monomial by the weight of `j`: since
`[X^c] ∂^j φ` is a multiple of `[X^(c + j)] φ`, a polynomial `φ` that is weighted homogeneous of
weight `m` has `∂^j φ` weighted homogeneous of weight `m - weight w j`. When the weights are
canonically ordered (for instance natural numbers), a nonzero derivative `∂^j φ ≠ 0` forces
`weight w j ≤ m`. The residual-weight formula also applies to ordered additive groups, allowing
negative weights.

With the indicator weight of a block `b` of variables `X_{b,l}`, weighted homogeneity of weight
`d` is homogeneity of degree `d` in the variables of block `b`. For such a polynomial, a nonzero
jet `∂^j F` has order `∑ₗ j_{b,l} ≤ d` in block `b`, and is homogeneous of the residual degree
`d - ∑ₗ j_{b,l}` there. These are the degree constraints on the jets of a block-homogeneous
auxiliary polynomial in Schmidt's subspace theorem.

## Main results

* `MvPolynomial.IsWeightedHomogeneous.hasseDeriv`: if `n + weight w j = m`, then `∂^j φ` is
  weighted homogeneous of weight `n`.
* `MvPolynomial.IsWeightedHomogeneous.weight_le_of_hasseDeriv_ne_zero`: for canonically ordered
  weights, `∂^j φ ≠ 0` forces `weight w j ≤ m`.
* `MvPolynomial.IsWeightedHomogeneous.hasseDeriv_tsub`: `∂^j φ` is weighted homogeneous of weight
  `m - weight w j`.
* `MvPolynomial.IsWeightedHomogeneous.sum_le_of_hasseDeriv_ne_zero`,
  `MvPolynomial.IsWeightedHomogeneous.hasseDeriv_sub_sum`: the block forms, for a polynomial
  homogeneous of degree `d` in block `b`.

## References

* J.-H. Evertse, *An improvement of the quantitative subspace theorem*, Compositio Math. 101
  (1996), §7, Lemma 26.
-/

public section

namespace MvPolynomial

variable {R σ M : Type*} [CommSemiring R] [AddCommMonoid M] {w : σ → M}
  {φ : MvPolynomial σ R} {m : M}

section AddCancel

variable [IsRightCancelAdd M]

/-- If `φ` is weighted homogeneous of weight `m` and `n + weight w j = m`, then the Hasse
derivative `∂^j φ` is weighted homogeneous of weight `n`. -/
theorem IsWeightedHomogeneous.hasseDeriv (hφ : φ.IsWeightedHomogeneous w m) (j : σ →₀ ℕ)
    {n : M} (hn : n + Finsupp.weight w j = m) :
    (MvPolynomial.hasseDeriv j φ).IsWeightedHomogeneous w n := by
  intro c hc
  rw [hasseDeriv_coeff] at hc
  have h := hφ (right_ne_zero_of_mul hc)
  rw [map_add] at h
  exact add_right_cancel (h.trans hn.symm)

end AddCancel

section CanonicallyOrdered

variable [LE M] [CanonicallyOrderedAdd M]

/-- A nonzero Hasse derivative `∂^j φ` of a weighted homogeneous polynomial of weight `m` has
order of weight at most `m`. -/
theorem IsWeightedHomogeneous.weight_le_of_hasseDeriv_ne_zero
    (hφ : φ.IsWeightedHomogeneous w m) {j : σ →₀ ℕ} (hj : MvPolynomial.hasseDeriv j φ ≠ 0) :
    Finsupp.weight w j ≤ m := by
  obtain ⟨c, hc⟩ := ne_zero_iff.mp hj
  rw [hasseDeriv_coeff] at hc
  rw [← hφ (right_ne_zero_of_mul hc), map_add]
  exact le_add_self

end CanonicallyOrdered

section OrderedSub

variable [PartialOrder M] [Sub M] [OrderedSub M] [AddLeftReflectLE M]

/-- The Hasse derivative `∂^j φ` of a weighted homogeneous polynomial of weight `m` is weighted
homogeneous of the residual weight `m - weight w j`. -/
theorem IsWeightedHomogeneous.hasseDeriv_tsub
    (hφ : φ.IsWeightedHomogeneous w m) (j : σ →₀ ℕ) :
    (MvPolynomial.hasseDeriv j φ).IsWeightedHomogeneous w (m - Finsupp.weight w j) := by
  intro c hc
  rw [hasseDeriv_coeff] at hc
  apply eq_tsub_of_add_eq
  simpa only [map_add] using hφ (right_ne_zero_of_mul hc)

end OrderedSub

section Block

variable {ι κ : Type*} [Fintype κ] [DecidableEq ι] {F : MvPolynomial (ι × κ) R} {b : ι} {d : ℕ}

/-- If `F` is homogeneous of degree `d` in the variables `X_{b,l}` of block `b`, a nonzero Hasse
derivative `∂^j F` has order `∑ₗ j_{b,l} ≤ d` in block `b`. -/
theorem IsWeightedHomogeneous.sum_le_of_hasseDeriv_ne_zero
    (hF : F.IsWeightedHomogeneous (fun p : ι × κ ↦ if p.1 = b then 1 else 0) d)
    {j : ι × κ →₀ ℕ} (hj : MvPolynomial.hasseDeriv j F ≠ 0) : ∑ l, j (b, l) ≤ d := by
  rw [← Finsupp.weight_ite_fst_eq_sum]
  exact hF.weight_le_of_hasseDeriv_ne_zero hj

/-- If `F` is homogeneous of degree `d` in the variables `X_{b,l}` of block `b`, the Hasse
derivative `∂^j F` is homogeneous of the residual degree `d - ∑ₗ j_{b,l}` in block `b`. -/
theorem IsWeightedHomogeneous.hasseDeriv_sub_sum
    (hF : F.IsWeightedHomogeneous (fun p : ι × κ ↦ if p.1 = b then 1 else 0) d)
    (j : ι × κ →₀ ℕ) :
    (MvPolynomial.hasseDeriv j F).IsWeightedHomogeneous (fun p : ι × κ ↦ if p.1 = b then 1 else 0)
      (d - ∑ l, j (b, l)) := by
  rw [← Finsupp.weight_ite_fst_eq_sum]
  exact hF.hasseDeriv_tsub j

end Block

end MvPolynomial
