/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Multiset
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.PolynomialRep
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.LeadingTerm

/-!
# Evaluation of the PBW polynomial representation

The polynomial representation attached to an ordered basis of a Lie algebra gives a linear map
from its enveloping algebra to polynomials by applying an operator to `1`. An ordered word of
basis vectors evaluates to the monomial with exactly those multiplicities. This normalization
identifies the ordered PBW basis with the usual polynomial monomials as modules.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.4.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

namespace Module.Basis

open MvPolynomial TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {R : Type u} {L : Type v} {ι : Type w}
  [CommRing R] [LieRing L] [LieAlgebra R L] [LinearOrder ι] (b : Basis ι R L)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Apply the PBW polynomial representation of the enveloping algebra to the constant `1`. -/
noncomputable def pbwEval : _root_.UniversalEnvelopingAlgebra R L →ₗ[R] MvPolynomial ι R :=
  LinearMap.applyₗ (1 : MvPolynomial ι R) ∘ₗ
    (_root_.UniversalEnvelopingAlgebra.lift R b.pbwPolynomialRep).toLinearMap

@[simp]
theorem pbwEval_one : b.pbwEval 1 = 1 := by
  simp [pbwEval]

/-- Left multiplication by a generator becomes its action on polynomials. -/
theorem pbwEval_ι_mul (x : L) (a : _root_.UniversalEnvelopingAlgebra R L) :
    b.pbwEval (_root_.UniversalEnvelopingAlgebra.ι R x * a) =
      b.pbwPolynomialRep x (b.pbwEval a) := by
  simp [pbwEval]

/-- An ordered word evaluates to the polynomial monomial with the same multiplicities. -/
theorem pbwEval_pbwMonomial {word : List ι} (hword : word.Pairwise (· ≤ ·)) :
    b.pbwEval (pbwMonomial R L b word) = monomial (Multiset.toFinsupp (word : Multiset ι)) 1 := by
  induction word with
  | nil => simp [Multiset.toFinsupp_zero]
  | cons i word ih =>
      obtain ⟨hle, htail⟩ := List.pairwise_cons.1 hword
      rw [pbwMonomial_cons, pbwEval_ι_mul, ih htail,
        pbwPolynomialRep_basis_monomial_of_le b (fun j hj ↦ hle j (by simpa using hj))]
      simp only [← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
        Multiset.toFinsupp_singleton, X, monomial_mul_monomial, one_mul]

end Module.Basis
