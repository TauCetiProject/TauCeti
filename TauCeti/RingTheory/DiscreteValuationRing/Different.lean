/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import TauCeti.RingTheory.DedekindDomain.Different.Monogenic
public import TauCeti.RingTheory.DiscreteValuationRing.Monogenic
public import TauCeti.RingTheory.Invariant.Minpoly
public import TauCeti.RingTheory.LocalRing.RamificationGroup
public import TauCeti.RingTheory.Valuation.AddValuation
import TauCeti.RingTheory.IsGaloisGroup.Dedekind

/-!
# Hilbert's different formula for discrete valuation rings

Let a finite group `G` act faithfully on a discrete valuation ring `B`, with invariant ring a
DVR `A`. If the residue extension is separable, then

`differentIdeal A B = maximalIdeal B ^ (∑ᶠ i : ℕ, (Nat.card (ramificationGroup G B i) - 1))`.

No completeness or residue-field finiteness is required. The monogenic version also applies
without residue separability, over any integrally closed base domain, whenever an algebra
generator is supplied. The different is
computed from the derivative of its minimal polynomial, and the local-ring counting identity
converts the sum of displacement valuations into the sum of ramification-group orders.

This follows Serre, *Local Fields*, IV §1, Proposition 4. The proof adapts the argument in
`TauCeti/NumberTheory/LocalField/Different/Hilbert.lean`, using the orbit polynomial directly on
`B` in place of automorphisms of its fraction field.
-/

public section

noncomputable section

open IsLocalRing Polynomial

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

variable (A B : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [FaithfulSMul A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B]
  [Algebra.IsInvariant A B G] [FaithfulSMul G B]

/-- **Hilbert's different formula for a monogenic DVR over an integrally closed domain.**
An algebra generator suffices; no residue separability is required. -/
theorem differentIdeal_eq_pow_maximalIdeal_of_adjoin_eq_top {x : B}
    (hx : Algebra.adjoin A {x} = ⊤) :
    differentIdeal A B = maximalIdeal B ^
      (∑ᶠ i : ℕ, (Nat.card (IsLocalRing.ramificationGroup G B (i : ℤ)) - 1)) := by
  classical
  let := Fintype.ofFinite G
  let : IsGaloisGroup G A B := ⟨inferInstance, inferInstance, inferInstance⟩
  let := IsFractionRing.mulSemiringAction G B (FractionRing B)
  have := IsGaloisGroup.isGalois G (FractionRing A) (FractionRing B)
  have := IsGaloisGroup.finiteDimensional G (FractionRing A) (FractionRing B)
  have := Algebra.IsInvariant.isIntegral A B G
  rw [differentIdeal_eq_span_aeval_derivative_minpoly A (FractionRing A) (FractionRing B) B x hx,
    TauCeti.MulSemiringAction.aeval_derivative_minpoly_eq_prod_of_adjoin_eq_top (G := G) hx]
  have hval : _root_.IsDiscreteValuationRing.addVal B
      (∏ g ∈ (Finset.univ : Finset G).erase 1, (x - g • x)) =
      ((∑ᶠ i : ℕ, (Nat.card (IsLocalRing.ramificationGroup G B (i : ℤ)) - 1) : ℕ) : ℕ∞) := by
    rw [AddValuation.map_prod]
    simpa only [AddValuation.map_sub_swap] using
      (IsLocalRing.sum_addVal_smul_sub_eq_finsum_card_ramificationGroup_sub_one
        (G := G) hx)
  ext y
  rw [Ideal.mem_span_singleton, ← _root_.IsDiscreteValuationRing.addVal_le_iff_dvd, hval,
    IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal]

omit [IsIntegrallyClosed A] in
/-- **Hilbert's different formula.** For a faithful finite group action on DVRs with invariants
`A` and separable residue extension, the different ideal is the power of the maximal ideal with
exponent `∑ᶠ i : ℕ, (#G_i - 1)`. Neither completeness nor a finite residue field is assumed. -/
theorem differentIdeal_eq_pow_maximalIdeal_of_separable_residue
    [IsDiscreteValuationRing A] [IsLocalHom (algebraMap A B)]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)] :
    differentIdeal A B = maximalIdeal B ^
      (∑ᶠ i : ℕ, (Nat.card (IsLocalRing.ramificationGroup G B (i : ℤ)) - 1)) := by
  let : IsGaloisGroup G A B := ⟨inferInstance, inferInstance, inferInstance⟩
  have := IsGaloisGroup.moduleFinite G A B
  obtain ⟨x, hx⟩ := IsDiscreteValuationRing.exists_adjoin_eq_top (R := A) (S := B)
  exact differentIdeal_eq_pow_maximalIdeal_of_adjoin_eq_top A B G hx

end TauCeti
