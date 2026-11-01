/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.ToricIdeal.Basic
public import TauCeti.RingTheory.MvPolynomial.Ideal

/-!
# Computing toric ideals by elimination

For exponents `a : ι → σ →₀ ℕ`, the toric ideal is the contraction of the graph ideal
`(Y i - X^(a i))` in the polynomial ring with variables `σ ⊕ ι`. Thus a Gröbner basis of
this graph ideal, for an order eliminating the `σ` variables, computes both generators and
a Gröbner basis of the toric ideal. A remainder of a polynomial in the `Y` variables modulo
the graph ideal also tests toric-ideal membership.

The contraction identity holds over every commutative coefficient ring, without finite-variable
hypotheses, including redundant or constant monomial generators. To extract a Gröbner basis or
generators, import `TauCeti.RingTheory.MvPolynomial.Groebner.Elimination`, rewrite with
`TauCeti.toricIdeal_eq_comap_graph`, then apply `MonomialOrder.IsGroebnerBasis.comap_rename` or
`MonomialOrder.IsGroebnerBasis.comap_rename_eq_span` with the order-compatibility and elimination
hypotheses. For the membership test, rewrite with the same identity and `Ideal.mem_comap`, then
apply `MonomialOrder.IsGroebnerBasis.remainder_eq_zero_iff_mem`; no elimination order is needed.
This construction concerns nonnegative exponent vectors; no Laurent variables are implicit.

## References

* B. Sturmfels, *Gröbner Bases and Convex Polytopes*, Chapter 4, the elimination construction
  of toric ideals.
* D. Cox, J. Little, D. O'Shea, *Ideals, Varieties, and Algorithms*, Chapter 3, §3,
  implicitization by elimination.
-/

public section

open MvPolynomial

namespace TauCeti

variable {σ ι R : Type*} [CommRing R]

/-- Eliminate the ambient variables from the graph equations `Y i - X^(a i)` to compute
all relations of the monomial map, over an arbitrary commutative coefficient ring. -/
theorem toricIdeal_eq_comap_graph (a : ι → σ →₀ ℕ) :
    toricIdeal R a =
      (Ideal.span (Set.range fun i ↦ X (Sum.inr i) -
        rename Sum.inl (monomial (a i) (1 : R)))).comap (rename (R := R) Sum.inr) := by
  rw [← ker_aeval_eq_comap_graph]
  ext p
  simp only [mem_toricIdeal_iff, RingHom.mem_ker, single_eq_monomial]

end TauCeti
