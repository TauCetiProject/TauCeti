/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.ProjectiveCover.Simple
public import TauCeti.RingTheory.MatlisDuality.Nakayama.Basic

import TauCeti.Algebra.Module.Injective.Envelope.Indecomposable

/-!
# Nakayama dualization of a simple module's projective cover

For an Artin algebra, the Nakayama module of the projective cover of a simple module `S` is an
injective envelope of `S`. Thus the same simple module indexes the projective cover and the
corresponding indecomposable injective under the Nakayama equivalence.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*,
  Proposition II.4.6, p. 42.
-/

public section

namespace TauCeti

open MatlisDual

universe v

variable {R : Type*} [CommRing R] [IsArtinianRing R]
  {E : Type v} [AddCommGroup E] [Module R E] [Small.{v} R]
  {ι : R ⧸ Ring.jacobson R →ₗ[R] E} {A : Type*} [Ring A] [Algebra R A] [Module.Finite R A]
  {P S : Type*} [AddCommGroup P] [Module A P] [AddCommGroup S] [Module A S] [IsSimpleModule A S]

/-- If `P` is the projective cover of a simple module `S`, its Nakayama module
`D_R (Hom_A(P, A))` is the target of an injective envelope of `S`. -/
theorem IsProjectiveCover.exists_isInjectiveEnvelope_nakayama {q : P →ₗ[A] S}
    (hq : IsProjectiveCover q) (hE : IsInjectiveEnvelope ι) :
    ∃ i : S →ₗ[A] MatlisDual R E (Module.Dual A P), IsInjectiveEnvelope i := by
  have : Module.Projective A P := hq.projective
  have : Module.Finite A P := hq.finite
  have : Module.Injective R E := hE.moduleInjective
  have : IsLocalRing (Module.End A P) := hq.isLocalRing_end
  have := (hE.nakayamaEndRingEquiv (A := A) P).isLocalRing
  have hI : IsIndecomposableModule A (MatlisDual R E (Module.Dual A P)) :=
    isIndecomposableModule_of_isLocalRing_end
  let : Module R S := Module.compHom S (algebraMap R A)
  have : IsScalarTower R A S := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Nontrivial S := IsSimpleModule.nontrivial A S
  -- A dual basis for a preimage of a nonzero element of `S` gives a matrix coefficient
  -- that is detected by a functional into the Matlis cogenerator.
  obtain ⟨s, hs⟩ := exists_ne (0 : S)
  obtain ⟨x, rfl⟩ := hq.surjective s
  obtain ⟨χ, hχ⟩ := exists_apply_ne_zero_of_forall_isMaximal
    (nontrivial_linearMap_of_isMaximal hE.length_quotient_linearMap_eq_one) hs
  obtain ⟨n, b, φ, hsum⟩ := exists_sum_dual_smul_eq_self (R := A) x
  have hsum' : ∑ j, χ (φ j x • q (b j)) = χ (q x) := by
    simpa only [map_sum, map_smul] using congrArg (fun y ↦ χ (q y)) hsum
  obtain ⟨j, hj⟩ : ∃ j, χ (φ j x • q (b j)) ≠ 0 := by
    by_contra! hall
    exact hχ (hsum' ▸ by simp [hall])
  let i : S →ₗ[A] MatlisDual R E (Module.Dual A P) :=
    mapOp (opDualEval A P x) ∘ₗ equivLinearMapDualRegular ((equivLinearMap R E S).symm χ)
  have hi : i ≠ 0 := by
    intro heq
    apply hj
    simpa [i] using congrArg (fun g : S →ₗ[A] MatlisDual R E (Module.Dual A P) ↦
      equivLinearMap R E _ (g (q (b j))) (φ j)) heq
  exact ⟨i, hI.isInjectiveEnvelope_of_injective (LinearMap.injective_of_ne_zero hi)⟩

end TauCeti
