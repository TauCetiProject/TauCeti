/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.RingTheory.MvPolynomial.QuotientBasis
public import TauCeti.RingTheory.RingHom.FiniteLocallyFree

/-!
# Finite locally free polynomial quotients

A prescribed finite polynomial basis gives a finite locally free quotient algebra. This
condition is invariant under a polynomial presentation of the target coordinate ring.
-/

public section

noncomputable section

variable {A B : Type*} [CommRing A] [CommRing B]

namespace TauCeti.PolynomialQuotient

/-- A polynomial quotient with a prescribed finite basis is finite locally free of rank
equal to the cardinality of the basis. -/
lemma IsQuotientBasis.isFiniteLocallyFreeOfRank {R : Type*} [CommRing R] {n : Type*}
    {ι : Type*} [Fintype ι]
    {w : ι → MvPolynomial n R} [Algebra R A] {I : Ideal (MvPolynomial n A)}
    (hI : IsQuotientBasis w I) :
    RingHom.IsFiniteLocallyFreeOfRank (Fintype.card ι)
      (algebraMap A (MvPolynomial n A ⧸ I)) := by
  let b := hI.basis
  have : Module.Free A (MvPolynomial n A ⧸ I) := .of_basis b
  have : Module.Finite A (MvPolynomial n A ⧸ I) := .of_basis b
  rw [RingHom.isFiniteLocallyFreeOfRank_algebraMap_iff]
  refine ⟨inferInstance, inferInstance, fun p ↦ ?_⟩
  have : Nontrivial A := p.nontrivial
  rw [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Module.finrank_eq_card_basis b,
    Nat.cast_id]

end TauCeti.PolynomialQuotient

namespace MvPolynomial

/-- Transport of a finite locally free polynomial quotient along a coordinate-ring isomorphism. -/
lemma isFiniteLocallyFreeOfRank_quotient_iff {n : Type*} {d : ℕ} (E : MvPolynomial n A ≃+* B)
    (σ : A →+* B) (hσ : E.toRingHom.comp MvPolynomial.C = σ) (K : Ideal B) :
    RingHom.IsFiniteLocallyFreeOfRank d ((Ideal.Quotient.mk K).comp σ) ↔
      RingHom.IsFiniteLocallyFreeOfRank d (algebraMap A (MvPolynomial n A ⧸ K.comap E)) := by
  let e := Ideal.quotientEquiv (K.comap E) K E (Ideal.map_comap_of_surjective _ E.surjective K).symm
  rw [← RingHom.isFiniteLocallyFreeOfRank_ringEquiv_comp_iff _ e]
  congr! 1
  ext a
  rw [← hσ]
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply A (MvPolynomial n A)]
  rw [Ideal.Quotient.algebraMap_eq, MvPolynomial.algebraMap_eq]
  simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
  exact (Ideal.quotientEquiv_mk (K.comap E) K E
    (Ideal.map_comap_of_surjective _ E.surjective K).symm (MvPolynomial.C a)).symm


end MvPolynomial
