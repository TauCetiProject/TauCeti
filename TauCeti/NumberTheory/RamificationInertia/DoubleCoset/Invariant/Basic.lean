/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.RamificationInertia.SeparableDegree
public import TauCeti.GroupTheory.DoubleCoset.Identity
public import TauCeti.GroupTheory.DoubleCoset.Map
public import TauCeti.RepresentationTheory.Induction.Mackey.Subgroup
public import TauCeti.RingTheory.Ideal.Pointwise
public import TauCeti.RingTheory.Invariant.Basic

/-!
# The double-coset splitting law over invariant rings

Let a finite group `G` act on a commutative ring `B` with invariant ring `A`, and let `C` be an
intermediate ring of invariants for a subgroup `H` of `G`. For a prime `Q` of `B` above
`p` in `A`, contraction identifies the primes of `C` above `p` with the double cosets
`H \ G / D`, where `D` is the stabilizer of `Q`. The class of `σ` corresponds to
`(σ • Q).under C`.

This formulation applies to integral closures over an arbitrary Dedekind base, once
`IsGaloisGroup.of_isIntegralClosure` and `IsGaloisGroup.of_isIntegralClosure_fixedField` supply
the invariance, and directly, through instances, to the rings of integers `𝓞 K`, `𝓞 M` and
`𝓞 (M ^ H)` of number fields. The bijection
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
* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsInvariant_smul_mk`: compatibility with the
  action of `G`, moving the base prime `Q` to `τ • Q`.
* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsInvariant_natural`: enlarging the subgroup
  agrees with contracting primes to the smaller invariant ring.
* `Ideal.ramificationIdx_mul_inertiaDeg_under_eq_relIndex`: the local degree below `Q` is
  `[D(Q) : H ∩ D(Q)]`, including inseparable residue extensions.
* `Ideal.ramificationIdx_under_eq_one_of_stabilizer_le` and
  `Ideal.inertiaDeg_under_eq_one_of_stabilizer_le`: if `D(Q) ≤ H`, then `Q ∩ C` has
  `e = f = 1` over `A`.
* `Ideal.sum_ramificationIdx_mul_inertiaDeg_doubleCosetOfIsInvariant_eq_index`: the local
  degrees indexed by double cosets sum to `[G : H]`.
* `Ideal.sum_ramificationIdx_mul_inertiaDeg_doubleCosetOfIsInvariant_eq_finrank`: the same
  sum is the rank of the intermediate invariant ring over the base.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9, page 55.
* G. J. Janusz, *Algebraic Number Fields*, Chapter I.

The construction uses Mathlib's
`Algebra.IsInvariant.exists_smul_of_under_eq` and `Algebra.IsInvariant.orbit_eq_primesOver`,
and the rank identity is reindexed from Mathlib's
`Ideal.sum_ramification_inertia_eq_finrank`.
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
    ← TauCeti.orbitRel_smul_iff_mem_doubleCoset_stabilizer, orbitRel_apply,
    under_eq_iff_mem_orbit H C]

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
      rintro ⟨q, hq, hqp⟩
      obtain ⟨σ, hσ⟩ := Q.exists_smul_under_eq G p C q
      refine ⟨DoubleCoset.mk H _ σ, Subtype.ext ?_⟩
      -- Reduce the quotient lift at its representative and the private subtype constructor.
      change (σ • Q).under C = q
      exact hσ⟩

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

/-- **The double-coset law is compatible with the action of `G`.** Indexing the primes of `C`
above `p` through the translate `τ • Q` instead of `Q` sends the class of `σ` to the prime that
the indexing through `Q` attaches to the class of `σ * τ`. -/
theorem doubleCosetQuotientEquivPrimesOverOfIsInvariant_smul_mk (τ σ : G) :
    (τ • Q).doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C (DoubleCoset.mk H _ σ) =
      Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C (DoubleCoset.mk H _ (σ * τ)) :=
  Subtype.ext <| by simp only [doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk, mul_smul]

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

/-- The local degree below a translate of `Q` is the relative index of the conjugate
decomposition group. -/
theorem ramificationIdx_mul_inertiaDeg_under_smul_eq_relIndex (sigma : G) :
    ((sigma • Q).under C).ramificationIdx A * ((sigma • Q).under C).inertiaDeg A =
      H.relIndex (MulAut.conj sigma • stabilizer G Q) := by
  rw [ramificationIdx_mul_inertiaDeg_under_eq_relIndex (Q := sigma • Q) (H := H) (C := C),
    stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    TauCeti.map_conj_eq_conj_smul]

variable {H}

/-- **Above the decomposition group the ramification index is one.** If `H` contains the
decomposition group `D(Q)`, then the prime `Q ∩ C` of the `H`-invariant ring `C` has
ramification index one over `A`. No hypothesis on the residue extension is needed. -/
theorem ramificationIdx_under_eq_one_of_stabilizer_le (hH : stabilizer G Q ≤ H) :
    (Q.under C).ramificationIdx A = 1 :=
  (mul_eq_one.1 <| (Q.ramificationIdx_mul_inertiaDeg_under_eq_relIndex H C).trans
    (Subgroup.relIndex_eq_one.2 hH)).1

/-- **Above the decomposition group the residue degree is one.** If `H` contains the
decomposition group `D(Q)`, then the prime `Q ∩ C` of the `H`-invariant ring `C` has residue
degree one over `A`. No hypothesis on the residue extension is needed. -/
theorem inertiaDeg_under_eq_one_of_stabilizer_le (hH : stabilizer G Q ≤ H) :
    (Q.under C).inertiaDeg A = 1 :=
  (mul_eq_one.1 <| (Q.ramificationIdx_mul_inertiaDeg_under_eq_relIndex H C).trans
    (Subgroup.relIndex_eq_one.2 hH)).2

end LocalDegree

section FundamentalIdentity

variable [Finite G] [IsDomain A] [IsDomain B]
  (p : Ideal A) (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver p]
  (H : Subgroup G) (C : Type*) [CommRing C] [IsDomain C]
  [Algebra A C] [Algebra C B] [IsScalarTower A C B]
  [Module.Finite A B] [Module.Flat A B] [Module.Flat C B]
  [IsGaloisGroup G A B] [IsGaloisGroup H C B]

/-- The local degree below a translate, multiplied by `|H|`, is the cardinality of its
double coset. -/
theorem ramificationIdx_mul_inertiaDeg_under_smul_mul_card (sigma : G) :
    ((sigma • Q).under C).ramificationIdx A * ((sigma • Q).under C).inertiaDeg A * Nat.card H =
      Nat.card (DoubleCoset.doubleCoset sigma (H : Set G) (stabilizer G Q : Set G)) := by
  rw [Q.ramificationIdx_mul_inertiaDeg_under_smul_eq_relIndex H C,
    TauCeti.card_doubleCoset_eq_card_mul_relIndex, mul_comm]

variable [FaithfulSMul C B]

/-- The local degree of the prime attached to a double coset, multiplied by `|H|`, is the
cardinality of that double coset. -/
theorem ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOverOfIsInvariant_mul_card
    (q : DoubleCoset.Quotient (H : Set G) (stabilizer G Q : Set G)) :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C q : Ideal C).ramificationIdx A *
        (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C q : Ideal C).inertiaDeg A *
          Nat.card H = Nat.card (DoubleCoset.quotToDoubleCoset H (stabilizer G Q) q) := by
  conv_lhs => rw [← DoubleCoset.out_eq' q,
    Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk p H C]
  rw [Q.ramificationIdx_mul_inertiaDeg_under_smul_mul_card (H := H) (C := C),
    DoubleCoset.quotToDoubleCoset]

/-- The local degree of the prime attached to a double coset is its cardinality divided by
the order of `H`. -/
theorem ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOverOfIsInvariant_eq_card_div
    (q : DoubleCoset.Quotient (H : Set G) (stabilizer G Q : Set G)) :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C q : Ideal C).ramificationIdx A *
        (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C q : Ideal C).inertiaDeg A =
      Nat.card (DoubleCoset.quotToDoubleCoset H (stabilizer G Q) q) / Nat.card H := by
  rw [← Q.ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOverOfIsInvariant_mul_card
    (p := p) (H := H) (C := C) q, Nat.mul_div_cancel _ Nat.card_pos]

/-- The local degrees indexed by the invariant-ring double-coset law sum to the index of
`H` in `G`. -/
theorem sum_ramificationIdx_mul_inertiaDeg_doubleCosetOfIsInvariant_eq_index :
    (∑ᶠ q : DoubleCoset.Quotient (H : Set G) (stabilizer G Q : Set G),
      (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C q : Ideal C).ramificationIdx A *
        (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C q : Ideal C).inertiaDeg A) =
      H.index := by
  classical
  let _ := Fintype.ofFinite
    (DoubleCoset.Quotient (H : Set G) (stabilizer G Q : Set G))
  rw [finsum_eq_sum_of_fintype]
  calc
    _ = ∑ q, Nat.card (DoubleCoset.quotToDoubleCoset H (stabilizer G Q) q) / Nat.card H :=
      Finset.sum_congr rfl fun q _ =>
        Q.ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOverOfIsInvariant_eq_card_div
          (p := p) (H := H) (C := C) q
    _ = H.index := Subgroup.sum_card_quotToDoubleCoset_div_card_eq_index H (stabilizer G Q)

end FundamentalIdentity

section RankIdentity

variable [Finite G] [Algebra.IsInvariant A B G] [SMulCommClass G A B]
  (p : Ideal A) (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p]
  (H : Subgroup G) (C : Type*) [CommRing C] [Algebra A C] [Algebra C B]
  [IsScalarTower A C B] [FaithfulSMul C B]
  [Algebra.IsInvariant C B H] [SMulCommClass H C B]
  [IsDomain A] [Module.Finite A C] [Module.Flat A C]

/-- **The fundamental identity in invariant-ring double-coset coordinates.** The local degrees
of the primes of `C` above `p` sum to the rank of `C` over `A`. -/
theorem sum_ramificationIdx_mul_inertiaDeg_doubleCosetOfIsInvariant_eq_finrank :
    (∑ᶠ q : DoubleCoset.Quotient (H : Set G) (stabilizer G Q : Set G),
      (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C q : Ideal C).ramificationIdx A *
        (Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C q : Ideal C).inertiaDeg A) =
      Module.finrank A C := by
  classical
  let _ : p.IsPrime := Ideal.isPrime_of_liesOver (P := Q) (p := p)
  let e := Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C
  let _ := Fintype.ofFinite
    (DoubleCoset.Quotient (H : Set G) (stabilizer G Q : Set G))
  let _ : Fintype (p.primesOver C) := Fintype.ofEquiv _ e
  rw [finsum_eq_sum_of_fintype]
  rw [e.sum_comp fun q : p.primesOver C =>
    q.1.ramificationIdx A * q.1.inertiaDeg A]
  exact Ideal.sum_ramification_inertia_eq_finrank p C

end RankIdentity

end Ideal
