/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariant
public import TauCeti.NumberTheory.RamificationInertia.HilbertTheory.IntermediateRing

/-!
# Inertia indices in the invariant-ring double-coset law

Let a finite Galois group `G` act on a finite flat extension of domains `B/A`, and let `C` be
the invariant ring of a subgroup `H`. For a maximal ideal `Q` of `B` with separable residue
extension over `A`, the prime of `C` indexed by the double coset of `σ` has ramification index

`[σ I(Q) σ⁻¹ : H ∩ σ I(Q) σ⁻¹]`.

This supplies the ramification-index component of the double-coset splitting law, expressing the
index at every prime represented by a double coset in terms of its conjugate inertia group. It does
not assume that the residue fields are finite or perfect.

## Main results

* `Ideal.ramificationIdx_doubleCosetQuotientEquivPrimesOverOfIsInvariant_eq_relIndex_inertia`:
  the ramification-index formula for the prime attached to a double coset.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9, page 55.
* G. J. Janusz, *Algebraic Number Fields*, Chapter I.
-/

public section

open MulAction
open scoped Pointwise

namespace Ideal

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

variable [IsDomain A] [IsDomain B] [IsGaloisGroup G A B]
  [Module.Finite A B] [Module.Flat A B]

variable [Finite G] (p : Ideal A) (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver p]
  (H : Subgroup G) (C : Type*) [CommRing C] [IsDomain C]
  [Algebra A C] [Algebra C B] [IsScalarTower A C B]
  [IsGaloisGroup H C B] [Module.Flat C B]
  [Algebra.IsSeparable (A ⧸ Q.under A) (B ⧸ Q)]

/-- The ramification index of the prime attached to a double coset is the relative index of the
corresponding conjugate inertia group. The representative `q.out` is immaterial because the
left-hand side depends only on the double coset. -/
theorem ramificationIdx_doubleCosetQuotientEquivPrimesOverOfIsInvariant_eq_relIndex_inertia
    (q : DoubleCoset.Quotient (H : Set G) (stabilizer G Q : Set G)) :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C q : Ideal C).ramificationIdx A =
      H.relIndex (MulAut.conj q.out • Q.inertia G) := by
  conv_lhs => rw [← DoubleCoset.out_eq' q,
    Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk p H C]
  exact Q.ramificationIdx_under_smul_eq_relIndex_inertia H C q.out

end Ideal
