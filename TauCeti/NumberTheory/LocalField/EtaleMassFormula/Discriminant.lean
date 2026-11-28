/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Field
public import TauCeti.NumberTheory.LocalField.EtaleMassFormula.EtaleWeight
import TauCeti.RingTheory.Discriminant.Basis
import TauCeti.RingTheory.Discriminant.Pi
import TauCeti.RingTheory.IntegralClosure.Pi
import TauCeti.RingTheory.Valuation.AddValuation

/-!
# The integral discriminant of a finite étale algebra

The orbit discriminant exponent of a finite étale algebra over a nonarchimedean local
field equals the normalized valuation of the trace discriminant of any basis of its
integral closure. Thus the exponent in the étale mass is the exponent of the
discriminant ideal of the maximal order.

The comparison uses Mathlib's `Algebra.Etale.iff_exists_algEquiv_prod` to obtain field factors.
`TauCeti.integralClosurePiAlgEquiv` and `TauCeti.integerRingEquivIntegralClosure` identify the
integral order with the product of their rings of integers. Then
`TauCeti.addVal_discr_eq_discriminantExponent` computes each factor's discriminant valuation,
and `TauCeti.etaleDiscriminantExponent_pi` and `TauCeti.Algebra.discr_pi_basis` assemble the
comparison. It includes the zero algebra, whose empty integral basis has discriminant one.

## References

* M. Bhargava, *Mass formulae for extensions of local fields, and conjectures on the density of
  number field discriminants*, IMRN **2007**, rnm052, Theorem 1.1 and §2.
-/

public section

open ValuativeRel IsDiscreteValuationRing IsLocalRing TauCeti

namespace Module.Basis

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- On any integral basis of a finite étale algebra, the normalized valuation of the trace
discriminant equals the discriminant weight of its Galois set of embeddings. -/
theorem addVal_discr_eq_etaleDiscriminantExponent {A : Type*} [CommRing A] [Algebra K A]
    [Algebra.Etale K A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝒪[K] (integralClosure 𝒪[K] A)) :
    addVal 𝒪[K] (Algebra.discr 𝒪[K] b) = etaleDiscriminantExponent K A := by
  classical
  -- Realize the field factors inside the separable closure to compute the orbit weight.
  obtain ⟨I, _, F, _, _, e, hF⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  let := Fintype.ofFinite I
  have (i : I) : Algebra.IsSeparable K (F i) := (hF i).2
  let f (i : I) : F i →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let L (i : I) := (f i).fieldRange
  have (i : I) : Module.Finite K (L i) :=
    have := (hF i).1
    .equiv (f i).equivFieldRange.toLinearEquiv
  let eL : A ≃ₐ[K] ∀ i, L i := e.trans (AlgEquiv.piCongrRight fun i ↦ (f i).equivFieldRange)
  let (i : I) := finiteIntermediateFieldValuativeRel K (SeparableClosure K) (L i)
  let (i : I) := finiteIntermediateFieldTopology K (SeparableClosure K) (L i)
  have (i : I) := finiteIntermediateField_isNonarchimedeanLocalField K (SeparableClosure K) (L i)
  have (i : I) := finiteIntermediateField_valuativeExtension K (SeparableClosure K) (L i)
  -- Compare the transported integral basis with the product of bases in the factors.
  let eInt : integralClosure 𝒪[K] A ≃ₐ[𝒪[K]] ∀ i, 𝒪[L i] :=
    ((eL.restrictScalars 𝒪[K]).mapIntegralClosure.trans (integralClosurePiAlgEquiv 𝒪[K] _)).trans
      (AlgEquiv.piCongrRight fun i ↦ (integerRingEquivIntegralClosure K (L i)).symm)
  let c := b.map eInt.toLinearEquiv
  let c₀ (i : I) := Module.finBasis 𝒪[K] 𝒪[L i]
  calc
    addVal 𝒪[K] (Algebra.discr 𝒪[K] b) = addVal 𝒪[K] (Algebra.discr 𝒪[K] c) :=
      congrArg (addVal 𝒪[K]) (Algebra.discr_eq_discr_of_algEquiv b eInt)
    _ = addVal 𝒪[K] (Algebra.discr 𝒪[K] (Pi.basis c₀)) := c.addVal_discr_eq _
    _ = ∑ i, addVal 𝒪[K] (Algebra.discr 𝒪[K] (c₀ i)) := by
      rw [TauCeti.Algebra.discr_pi_basis, AddValuation.map_prod]
    _ = ∑ i, ((L i).discriminantExponent : ℕ∞) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [IntermediateField.discriminantExponent_eq]
      exact TauCeti.addVal_discr_eq_discriminantExponent (c₀ i)
    _ = etaleDiscriminantExponent K A := by
      rw [etaleDiscriminantExponent_eq_of_algEquiv K eL, etaleDiscriminantExponent_pi,
        Nat.cast_sum]

/-- The discriminant of any integral basis generates the power of the maximal ideal given by
the étale discriminant exponent. This extends `TauCeti.span_discr_eq_discriminantIdeal`
from field extensions, using the same DVR valuation-to-ideal comparison. -/
theorem span_discr_eq_maximalIdeal_pow_etaleDiscriminantExponent {A : Type*} [CommRing A]
    [Algebra K A] [Algebra.Etale K A] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι 𝒪[K] (integralClosure 𝒪[K] A)) :
    Ideal.span {Algebra.discr 𝒪[K] b} = 𝓂[K] ^ etaleDiscriminantExponent K A := by
  exact TauCeti.IsDiscreteValuationRing.span_singleton_eq_maximalIdeal_pow_of_addVal_eq
    b.addVal_discr_eq_etaleDiscriminantExponent

end Module.Basis
