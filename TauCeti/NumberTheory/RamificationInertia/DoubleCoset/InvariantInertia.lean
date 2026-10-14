/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Pointwise
public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariant
public import TauCeti.NumberTheory.RamificationInertia.HilbertTheory.IntermediateRing
public import TauCeti.NumberTheory.RamificationInertia.ResidueSeparable

/-!
# Inertia indices in the invariant-ring double-coset law

Let a finite Galois group `G` act on a finite flat extension of domains `B/A`, and let `C` be
the invariant ring of a subgroup `H`. For a maximal ideal `Q` of `B` with separable residue
extension over `A`, the ramification index of the contraction of `σ • Q` to `C` is

`[σ I(Q) σ⁻¹ : H ∩ σ I(Q) σ⁻¹]`.

This is the inertia half of the double-coset splitting law over an arbitrary invariant ring. It
does not assume that the residue fields are finite or perfect. The proof transports residue
separability from `Q` to `σ • Q`, using `Ideal.Quotient.isSeparable_smul`, and then applies the
intermediate-ring ramification-index formula at the translated prime.

## Main results

* `Ideal.ramificationIdx_under_smul_eq_relIndex_inertia`: the ramification index below a
  translated prime is the relative index of the conjugate inertia group.
* `Ideal.ramificationIdx_under_smul_eq_one_iff_inertia_le`: the translated prime is unramified
  in the ramification-index sense exactly when its conjugate inertia group lies in `H`.
* `Ideal.ramificationIdx_doubleCosetQuotientEquivPrimesOverOfIsInvariant_eq_relIndex_inertia`:
  the same formula for the prime attached to a double coset.

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

/-- The ramification index below a translate of `Q` is the relative index of the conjugate
inertia group. Separability is required only for the selected residue extension at `Q`; the
group action transports it to every translate. -/
theorem ramificationIdx_under_smul_eq_relIndex_inertia (Q : Ideal B) [Q.IsMaximal]
    (H : Subgroup G) (C : Type*) [CommRing C] [IsDomain C]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [IsGaloisGroup H C B] [Module.Flat C B]
    [Algebra.IsSeparable (A ⧸ Q.under A) (B ⧸ Q)] (σ : G) :
    ((σ • Q).under C).ramificationIdx A =
      H.relIndex (MulAut.conj σ • Q.inertia G) := by
  let : Algebra.IsSeparable (A ⧸ (σ • Q).under A) (B ⧸ σ • Q) :=
    Quotient.isSeparable_smul Q σ
  let _ : (σ • Q).IsMaximal := by
    rw [pointwise_smul_eq_comap]
    infer_instance
  rw [ramificationIdx_under_eq_relIndex_inertia (σ • Q) H C, inertia_smul,
    TauCeti.map_conj_eq_conj_smul]

/-- The contraction of a translated prime has ramification index one exactly when its conjugate
inertia group is contained in the subgroup fixing the intermediate ring. -/
theorem ramificationIdx_under_smul_eq_one_iff_inertia_le (Q : Ideal B) [Q.IsMaximal]
    (H : Subgroup G) (C : Type*) [CommRing C] [IsDomain C]
    [Algebra A C] [Algebra C B] [IsScalarTower A C B]
    [IsGaloisGroup H C B] [Module.Flat C B]
    [Algebra.IsSeparable (A ⧸ Q.under A) (B ⧸ Q)] (σ : G) :
    ((σ • Q).under C).ramificationIdx A = 1 ↔
      MulAut.conj σ • Q.inertia G ≤ H := by
  rw [Q.ramificationIdx_under_smul_eq_relIndex_inertia H C σ, Subgroup.relIndex_eq_one]

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
