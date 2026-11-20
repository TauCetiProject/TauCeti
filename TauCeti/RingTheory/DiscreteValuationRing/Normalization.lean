/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DiscreteValuationRing.FiniteProduct
import Mathlib.RingTheory.Etale.Field

/-!
# Étaleness of the normalization of a discrete valuation ring

For a finite étale algebra over the fraction field, one can test whether the normalization is
étale using the residue fields of its points. This is the pointwise form of unramifiedness used
in [Stacks, Section 58.31](https://stacks.math.columbia.edu/tag/0BSE).
-/

public section

namespace TauCeti.Algebra

/-- Unramifiedness with respect to a local ring is invariant under an isomorphism of the
extension fields over that ring. -/
theorem isUnramifiedWRT_iff_of_algEquiv {A L M : Type*} [CommRing A] [IsLocalRing A]
    [Field L] [Field M] [Algebra A L] [Algebra A M] (e : L ≃ₐ[A] M) :
    IsUnramifiedWRT A L ↔ IsUnramifiedWRT A M := by
  let B := integralClosure A L
  let : Algebra B M := (e.toRingHom.comp (algebraMap B L)).toAlgebra
  have : IsScalarTower A B M := .of_algebraMap_eq fun a ↦ (e.commutes a).symm
  have : IsIntegralClosure B A M := IsIntegralClosure.of_algEquiv B e fun _ ↦ rfl
  exact (isUnramifiedWRT_iff_of_isIntegralClosure (L := L) B).trans
    (isUnramifiedWRT_iff_of_isIntegralClosure (L := M) B).symm

universe u

variable (A : Type*) (K : Type*) (S : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  [CommRing S] [Algebra K S] [Algebra A S] [IsScalarTower A K S] [Algebra.Etale K S]

include K in
/-- The normalization in a finite étale generic fibre is étale if and only if the residue field
at each point of the generic fibre is unramified with respect to the base. -/
theorem etale_integralClosure_iff_forall_residueField :
    Algebra.Etale A (integralClosure A S) ↔
      ∀ p : PrimeSpectrum S, IsUnramifiedWRT A p.asIdeal.ResidueField := by
  have : Module.Finite K S := Algebra.FormallyUnramified.finite_of_free K S
  have : IsArtinianRing S := .of_finite K S
  have : IsReduced S := Algebra.FormallyUnramified.isReduced_of_field K S
  let L (m : MaximalSpectrum S) := S ⧸ m.asIdeal
  let (m : MaximalSpectrum S) : Field (L m) := Ideal.Quotient.field m.asIdeal
  have (m : MaximalSpectrum S) : Module.Finite K (L m) := inferInstanceAs (Module.Finite K (S ⧸ _))
  have (m : MaximalSpectrum S) : Algebra.IsSeparable K (L m) :=
    inferInstanceAs (Algebra.IsSeparable K (S ⧸ m.asIdeal))
  let e := (IsArtinianRing.equivPi S).restrictScalars A
  have etale_iff {B C : Type u} [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
      (e : B ≃ₐ[A] C) : Algebra.Etale A B ↔ Algebra.Etale A C :=
    ⟨fun _ ↦ .of_equiv e, fun _ ↦ .of_equiv e.symm⟩
  rw [etale_iff e.mapIntegralClosure, etale_integralClosure_pi_iff A K L]
  refine ((IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := S)).forall_congr ?_).symm
  intro p
  let q := p.asIdeal
  have : q.IsMaximal := IsArtinianRing.isMaximal_of_isPrime q
  let : Field (S ⧸ q) := Ideal.Quotient.field q
  let φ : (S ⧸ q) →ₐ[A] q.ResidueField := IsScalarTower.toAlgHom A (S ⧸ q) q.ResidueField
  let e' := AlgEquiv.ofBijective φ (Ideal.bijective_algebraMap_quotient_residueField q)
  exact (isUnramifiedWRT_iff_of_algEquiv e').symm

end TauCeti.Algebra
