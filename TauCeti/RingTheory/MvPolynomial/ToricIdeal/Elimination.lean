/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.ToricIdeal.Basic
public import TauCeti.RingTheory.MvPolynomial.Ideal
public import TauCeti.RingTheory.MvPolynomial.Groebner.Elimination

/-!
# Computing toric ideals by elimination

For exponents `a : ι → σ →₀ ℕ`, the toric ideal is the contraction of the graph ideal
`(Y i - X^(a i))` in the polynomial ring with variables `σ ⊕ ι`. Thus a Gröbner basis of
this graph ideal, for an order eliminating the `σ` variables, computes both generators and
a Gröbner basis of the toric ideal. A remainder of a polynomial in the `Y` variables modulo
the graph ideal also tests toric-ideal membership.

The contraction identity and membership test hold over every commutative coefficient ring,
without finite-variable hypotheses. The Gröbner-basis extraction uses the existing elimination
theorem, with its explicit order-compatibility and elimination hypotheses. In particular this
applies to finite monomial maps, including redundant or constant monomial generators.
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

namespace MonomialOrder

variable {σ ι R : Type*} [CommRing R]
  {m : MonomialOrder (σ ⊕ ι)} {m' : MonomialOrder ι}
  {G : Set (MvPolynomial (σ ⊕ ι) R)} {a : ι → σ →₀ ℕ}

/-- A remainder modulo the graph equations tests membership in the toric ideal. The order
need not be an elimination order for this membership test. -/
theorem IsGroebnerBasis.remainder_eq_zero_iff_mem_toricIdeal
    (h : m.IsGroebnerBasis G (Ideal.span (Set.range fun i ↦ X (Sum.inr i) -
      rename Sum.inl (monomial (a i) (1 : R)))))
    {p : MvPolynomial ι R} {r : MvPolynomial (σ ⊕ ι) R}
    (hr : m.IsRemainder (rename Sum.inr p) G r) :
    r = 0 ↔ p ∈ TauCeti.toricIdeal R a := by
  rw [TauCeti.toricIdeal_eq_comap_graph, Ideal.mem_comap]
  exact h.remainder_eq_zero_iff_mem hr

/-- For an elimination order, the members of a graph Gröbner basis involving only the
parameter variables form a Gröbner basis of the toric ideal. -/
theorem IsGroebnerBasis.toricIdeal
    (h : m.IsGroebnerBasis G (Ideal.span (Set.range fun i ↦ X (Sum.inr i) -
      rename Sum.inl (monomial (a i) (1 : R)))))
    (hm : ∀ u v : ι →₀ ℕ, u ≼[m'] v ↔
      u.mapDomain Sum.inr ≼[m] v.mapDomain Sum.inr)
    (helim : ∀ u v : (σ ⊕ ι) →₀ ℕ, u ≼[m] v →
      ↑v.support ⊆ Set.range (Sum.inr : ι → σ ⊕ ι) →
        ↑u.support ⊆ Set.range (Sum.inr : ι → σ ⊕ ι)) :
    m'.IsGroebnerBasis (rename Sum.inr ⁻¹' G) (TauCeti.toricIdeal R a) := by
  rw [TauCeti.toricIdeal_eq_comap_graph]
  exact h.comap_rename hm helim

/-- Elimination computes generators for a toric ideal from a Gröbner basis of the graph
ideal. No division of coefficients is needed for this extraction. -/
theorem IsGroebnerBasis.toricIdeal_eq_span
    (h : m.IsGroebnerBasis G (Ideal.span (Set.range fun i ↦ X (Sum.inr i) -
      rename Sum.inl (monomial (a i) (1 : R)))))
    (hm : ∀ u v : ι →₀ ℕ, u ≼[m'] v ↔
      u.mapDomain Sum.inr ≼[m] v.mapDomain Sum.inr)
    (helim : ∀ u v : (σ ⊕ ι) →₀ ℕ, u ≼[m] v →
      ↑v.support ⊆ Set.range (Sum.inr : ι → σ ⊕ ι) →
        ↑u.support ⊆ Set.range (Sum.inr : ι → σ ⊕ ι)) :
    TauCeti.toricIdeal R a = Ideal.span (rename Sum.inr ⁻¹' G) :=
  (h.toricIdeal hm helim).ideal_eq_span

end MonomialOrder
