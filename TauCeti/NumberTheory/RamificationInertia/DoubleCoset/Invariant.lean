/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.RamificationInertia.SeparableDegree
public import TauCeti.GroupTheory.DoubleCoset.Identity
public import TauCeti.GroupTheory.DoubleCoset.Map
public import TauCeti.GroupTheory.DoubleCoset.Orbits

/-!
# The double-coset splitting law over invariant rings

Let a finite group `G` act on a commutative ring `B` with invariant ring `A`, and let `C` be an
intermediate ring of invariants for a subgroup `H` of `G`. For a prime `Q` of `B` above
`p` in `A`, contraction identifies the primes of `C` above `p` with the double cosets
`H \ G / D`, where `D` is the stabilizer of `Q`. The class of `σ` corresponds to
`(σ • Q).under C`.

This formulation applies to integral closures over an arbitrary Dedekind base. The bijection
itself needs neither a Dedekind hypothesis nor residue-field separability: transitivity on prime
fibres and lying over are supplied by Mathlib's invariant-ring theory. The intermediate ring is
an explicit parameter, so the same construction works for any realization of the fixed ring,
including `FixedPoints.subalgebra A B H`.

## Main definitions

* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsInvariant`: the contraction bijection over
  an invariant ring.

## Main results

* `Ideal.under_smul_eq_iff_doubleCosetMk_eq`: the fibres of translated contraction are exactly
  the double cosets.
* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk`: the value at a double-coset
  representative.
* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsInvariant_symm_apply_eq_mk_iff`:
  characterization of the inverse.
* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsInvariant_natural`: enlarging the subgroup
  agrees with contracting primes to the smaller invariant ring.
* `Ideal.ramificationIdx_mul_inertiaDeg_under_eq_relIndex`: the local degree below `Q` is
  `[D(Q) : H ∩ D(Q)]`, including inseparable residue extensions.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9, page 55.
* G. J. Janusz, *Algebraic Number Fields*, Chapter I.

The construction generalizes the number-field double-coset law in
`TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Basic`, using Mathlib's
`Algebra.IsInvariant.exists_smul_of_under_eq` and `Algebra.IsInvariant.orbit_eq_primesOver`.
-/

public section

open MulAction
open scoped Pointwise

namespace Ideal

variable {A B G : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Group G] [MulSemiringAction G B]

section Fibres

variable (Q : Ideal B) [Q.IsPrime] (H : Subgroup G) (C : Type*) [CommRing C] [Algebra C B]
  [Finite H] [Algebra.IsInvariant C B H] [SMulCommClass H C B]

/-- Two translates of a prime contract to the same prime of the `H`-invariant ring exactly
when their translating elements belong to the same `H`-decomposition double coset. -/
theorem under_smul_eq_iff_doubleCosetMk_eq (σ τ : G) :
    (σ • Q).under C = (τ • Q).under C ↔
      DoubleCoset.mk H (stabilizer G Q) σ = DoubleCoset.mk H (stabilizer G Q) τ := by
  rw [TauCeti.doubleCosetMk_eq_mk_iff_mem,
    ← TauCeti.orbitRel_smul_iff_mem_doubleCoset_stabilizer, orbitRel_apply, mem_orbit_iff]
  constructor
  · intro h
    obtain ⟨h, hh⟩ := Algebra.IsInvariant.exists_smul_of_under_eq C B H (τ • Q) (σ • Q) h.symm
    exact ⟨h, hh.symm⟩
  · rintro ⟨h, hh⟩
    rw [← hh]
    exact under_smul (G := H) C (τ • Q) h

end Fibres

section Equivalence

variable [Finite G] [hAB : Algebra.IsInvariant A B G] [SMulCommClass G A B]
  (Q : Ideal B) [Q.IsPrime] (p : Ideal A) [Q.LiesOver p]
  (H : Subgroup G) (C : Type*) [CommRing C] [Algebra A C] [Algebra C B]
  [IsScalarTower A C B] [hCB : FaithfulSMul C B]
  [Algebra.IsInvariant C B H] [SMulCommClass H C B]

/-- The prime above `p` obtained by contracting a translate of `Q` to `C`. -/
private def translatedPrime (σ : G) : p.primesOver C :=
  ⟨(σ • Q).under C, inferInstance,
    ⟨by rw [under_under]; exact (inferInstance : (σ • Q).LiesOver p).over⟩⟩

/-- **The double-coset splitting law over invariant rings.** The primes of the intermediate
`H`-invariant ring `C` above `p` are indexed by `H \ G / stabilizer G Q`. The class of `σ`
is sent to the contraction of `σ • Q`, without any residue-field hypothesis. -/
noncomputable def doubleCosetQuotientEquivPrimesOverOfIsInvariant :
    DoubleCoset.Quotient (H : Set G) (stabilizer G Q : Set G) ≃ p.primesOver C :=
  Equiv.ofBijective
    (fun q ↦ q.liftOn' (translatedPrime Q p C) fun σ τ hστ ↦
      Subtype.ext ((Q.under_smul_eq_iff_doubleCosetMk_eq H C σ τ).mpr (Quotient.sound' hστ)))
    ⟨by
      intro q r hqr
      induction q using Quotient.inductionOn' with | h σ =>
      induction r using Quotient.inductionOn' with | h τ =>
      exact (Q.under_smul_eq_iff_doubleCosetMk_eq H C σ τ).mp (Subtype.ext_iff.mp hqr), by
      have : Algebra.IsIntegral C B := Algebra.IsInvariant.isIntegral C B H
      rintro ⟨q, hq, hqp⟩
      obtain ⟨⟨R, hR, hRq⟩⟩ := q.nonempty_primesOver (S := B)
      have : R.LiesOver p := LiesOver.trans R q p
      have hRp : R ∈ p.primesOver B := ⟨hR, inferInstance⟩
      rw [← Algebra.IsInvariant.orbit_eq_primesOver A B G p Q, mem_orbit_iff] at hRp
      obtain ⟨σ, hσ⟩ := hRp
      refine ⟨DoubleCoset.mk H _ σ, Subtype.ext ?_⟩
      -- Reduce the quotient lift at its representative and the private subtype constructor.
      change (σ • Q).under C = q
      rw [hσ]
      exact hRq.over.symm⟩

include hAB hCB in
/-- The class of `σ` is sent to the contraction of `σ • Q`. -/
@[simp]
theorem doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk (σ : G) :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C
      (DoubleCoset.mk H _ σ) : Ideal C) = (σ • Q).under C :=
  (rfl)

/-- The inverse sends a prime `q` to the class of `σ` exactly when `q` is the contraction of
`σ • Q`. This characterizes the inverse without exposing the choice of a prime above `q`. -/
@[simp]
theorem doubleCosetQuotientEquivPrimesOverOfIsInvariant_symm_apply_eq_mk_iff
    (q : p.primesOver C) (σ : G) :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C).symm q = DoubleCoset.mk H _ σ ↔
      q.1 = (σ • Q).under C := by
  rw [Equiv.symm_apply_eq, Subtype.ext_iff, doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk]

/-- Enlarging the subgroup and contracting to its invariant ring give the same prime under
the double-coset splitting bijection. The scalar towers express the two inclusions of `C'`
into `B` through `A` and `C`. -/
theorem doubleCosetQuotientEquivPrimesOverOfIsInvariant_natural {H' : Subgroup G} (h : H ≤ H')
    (C' : Type*) [CommRing C'] [Algebra A C'] [Algebra C' C] [Algebra C' B]
    [IsScalarTower A C' B] [IsScalarTower C' C B]
    [FaithfulSMul C' B] [Algebra.IsInvariant C' B H'] [SMulCommClass H' C' B]
    (q : DoubleCoset.Quotient (H : Set G) (stabilizer G Q : Set G)) :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H' C'
        (DoubleCoset.quotientMapOfLELeft h (stabilizer G Q) q)).1 =
      (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C q).1.under C' := by
  induction q using Quotient.inductionOn' with
  | h σ =>
    simp only [DoubleCoset.quotientMapOfLELeft_apply_mk,
      doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk,
      under_under]

end Equivalence

section LocalDegree

variable (Q : Ideal B) [Q.IsMaximal] (H : Subgroup G) (C : Type*) [CommRing C]
  [Algebra A C] [Algebra C B] [IsScalarTower A C B]
  [Finite G] [IsDomain A] [IsDomain B] [IsDomain C]
  [Module.Finite A B] [Module.Flat A B] [Module.Flat C B]
  [IsGaloisGroup G A B] [IsGaloisGroup H C B]

/-- **The local-degree index formula over invariant rings.** The ramification index times
residue degree of the contraction to an intermediate `H`-invariant ring is the index of
`H ∩ D(Q)` in `D(Q)`. No separability hypothesis on the residue extension is needed. -/
theorem ramificationIdx_mul_inertiaDeg_under_eq_relIndex :
    (Q.under C).ramificationIdx A * (Q.under C).inertiaDeg A =
      H.relIndex (stabilizer G Q) := by
  have : Module.Finite C B := Module.Finite.right A C B
  have hcard : Nat.card (H ⊓ stabilizer G Q : Subgroup G) =
      Q.ramificationIdx C * Q.inertiaDeg C := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : H ⊓ stabilizer G Q ≤ H)).toEquiv,
      Subgroup.inf_subgroupOf_left, stabilizer_subgroupOf]
    exact Q.card_stabilizer_eq_ramificationIdx_mul_inertiaDeg (R := C) (G := H)
  have hidx := H.relIndex_mul_card (stabilizer G Q)
  rw [hcard, Q.card_stabilizer_eq_ramificationIdx_mul_inertiaDeg (R := A) (G := G)] at hidx
  have htower :
      ((Q.under C).ramificationIdx A * (Q.under C).inertiaDeg A) *
          (Q.ramificationIdx C * Q.inertiaDeg C) =
        Q.ramificationIdx A * Q.inertiaDeg A := by
    rw [ramificationIdx_tower (R := A) (Q.under C) Q,
      inertiaDeg_tower (R := A) (Q.under C) Q]
    ring
  exact mul_right_cancel₀ (mul_ne_zero (ramificationIdx_pos C Q).ne'
    (inertiaDeg_pos Q C).ne') (htower.trans hidx.symm)

end LocalDegree

end Ideal
