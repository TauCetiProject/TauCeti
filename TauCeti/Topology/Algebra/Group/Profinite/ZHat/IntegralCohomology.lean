/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Bockstein.Rational
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.RationalCharacter

/-!
# Integral second cohomology of the profinite integers

The inverse of the connecting isomorphism of `0 → ℤ → ℚ → ℚ/ℤ → 0`, followed by
evaluation of rational characters at the canonical generator, gives `H²(zHat, ℤ) ≃+ ℚ/ℤ`.
Thus second integral cohomology is nonzero, although second cohomology with torsion coefficients
vanishes.

The cohomology carrier is Mathlib's continuous cohomology. The integers and rationals are
lifted to the universe of `zHat`, and the rational circle may be any discrete model in that
universe. All three coefficient actions are trivial. The normalization theorem specifies
the value of every class obtained by the connecting map from a continuous character.

The construction combines `TauCeti.ContCohomology.rationalIntegralDeltaIso` with evaluation
of rational characters of `zHat`; it does not construct a new cohomology theory.

## References

* J.-P. Serre, *Local Fields*, Chapter XIII, §1, Propositions 1–2.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*,
  2nd ed., (1.3.2), (1.6.1) and (1.7.7).
-/

public noncomputable section

namespace TauCeti.zHat

open ContCohomology

universe u

variable [DistribMulAction zHat.{u} (ULift.{u} ℤ)]
  [DistribMulAction zHat.{u} (ULift.{u} ℚ)]
  [TopologicalSpace (ULift.{u} ℚ)] [DiscreteTopology (ULift.{u} ℚ)]
  (C : Type u) [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C]
  [DistribMulAction zHat.{u} C]
  (e : C ≃+ AddCircle (1 : ℚ))
  (hℤ : ∀ (g : zHat.{u}) (x : ULift.{u} ℤ), g • x = x)
  (hℚ : ∀ (g : zHat.{u}) (x : ULift.{u} ℚ), g • x = x)
  (hC : ∀ (g : zHat.{u}) (x : C), g • x = x)

/-- Second integral continuous cohomology of the profinite integers is the rational circle.
The inverse sends a rational-circle value to the connecting class of the unique continuous
character taking that value at the canonical generator. -/
def h2EquivRatCircle :
    continuousCohomology 2 (ofDiscreteModule ℤ zHat.{u} (ULift.{u} ℤ)) ≃+
      AddCircle (1 : ℚ) := by
  letI : ContinuousSMul zHat.{u} (ULift.{u} ℚ) :=
    ⟨continuous_snd.congr fun p ↦ (hℚ p.1 p.2).symm⟩
  letI : ContinuousSMul zHat.{u} C :=
    ⟨continuous_snd.congr fun p ↦ (hC p.1 p.2).symm⟩
  exact AddEquiv.ofBijective
    ({ toFun := fun x ↦ e (Multiplicative.toAdd
          (Additive.toMul (continuousCohomologyTwoIntEquivContinuousMonoidHom
            zHat.{u} C e hℤ hℚ hC x) gen))
       map_zero' := by simp
       map_add' := by intros; simp } : _ →+ _) <|
    (bijective_ratCircleCharacterEvaluation C e).comp
      (continuousCohomologyTwoIntEquivContinuousMonoidHom zHat.{u} C e hℤ hℚ hC).bijective

section CharacterNormalization

variable [ContinuousSMul zHat.{u} (ULift.{u} ℚ)] [ContinuousSMul zHat.{u} C]

/-- The integral degree-two equivalence evaluates the corresponding rational character
at the canonical generator. -/
theorem h2EquivRatCircle_apply
    (x : continuousCohomology 2 (ofDiscreteModule ℤ zHat.{u} (ULift.{u} ℤ))) :
    h2EquivRatCircle C e hℤ hℚ hC x = e (Multiplicative.toAdd
      (Additive.toMul (continuousCohomologyTwoIntEquivContinuousMonoidHom
        zHat.{u} C e hℤ hℚ hC x) gen)) := (rfl)

/-- The connecting class of a continuous rational-circle cocycle is normalized by its value
at the generator. This fixes the sign of the identification with the rational circle. -/
@[simp] theorem h2EquivRatCircle_delta_cocycle (f : Z1 zHat.{u} C) :
    h2EquivRatCircle C e hℤ hℚ hC
      ((rationalIntegralShortExact zHat.{u} C e hℤ hℚ hC).delta 1
        ((TopRep.homogeneousCochains (ofDiscreteModule ℤ zHat.{u} C)).homologyπ 1
          (cocycleEquiv1 zHat.{u} C f))) = e ((f : zHat.{u} → C) gen) := by
  rw [← explicitH1AddEquivContinuousCohomology_apply]
  have h := continuousCohomologyTwoIntEquivContinuousMonoidHom_symm_apply
    zHat.{u} C e hℤ hℚ hC (H1EquivOfSmulEqSelf hC (f : H1 zHat.{u} C))
  simp only [AddEquiv.symm_apply_apply] at h
  rw [← h, h2EquivRatCircle_apply, AddEquiv.apply_symm_apply]
  simp only [H1EquivOfSmulEqSelf_mk, Z1EquivOfSmulEqSelf_apply, toAdd_ofAdd]

/-- Conversely, the connecting class of a character is the inverse image of its
value at the generator. -/
theorem h2EquivRatCircle_symm_apply_character
    (χ : Additive (zHat.{u} →ₜ* Multiplicative C)) :
    (h2EquivRatCircle C e hℤ hℚ hC).symm
        (e (Multiplicative.toAdd (Additive.toMul χ gen))) =
      (rationalIntegralShortExact zHat.{u} C e hℤ hℚ hC).delta 1
        (explicitH1AddEquivContinuousCohomology zHat.{u} C
          ((H1EquivOfSmulEqSelf hC).symm χ)) := by
  apply (h2EquivRatCircle C e hℤ hℚ hC).injective
  simp only [AddEquiv.apply_symm_apply, H1EquivOfSmulEqSelf_symm_apply,
    explicitH1AddEquivContinuousCohomology_apply, h2EquivRatCircle_delta_cocycle,
    Z1EquivOfSmulEqSelf_symm_apply]

end CharacterNormalization

/-- The class corresponding to `1/n` has additive order `n`. In particular, second
integral cohomology contains elements of every finite order. -/
theorem addOrderOf_h2EquivRatCircle_symm_toRatAddCircle (n : ℕ) [NeZero n] :
    addOrderOf ((h2EquivRatCircle C e hℤ hℚ hC).symm (ZMod.toRatAddCircle n 1)) = n := by
  rw [AddEquiv.addOrderOf_eq]
  rw [addOrderOf_injective _ (ZMod.toRatAddCircle_injective n), ZMod.addOrderOf_one]

include e hℤ hℚ hC in
/-- Second integral continuous cohomology of the profinite integers is nontrivial:
the class of invariant `1/2` has order two. -/
theorem nontrivial_continuousCohomology_two_int :
    Nontrivial (continuousCohomology 2 (ofDiscreteModule ℤ zHat.{u} (ULift.{u} ℤ))) := by
  let x := (h2EquivRatCircle C e hℤ hℚ hC).symm (ZMod.toRatAddCircle 2 1)
  have hx : addOrderOf x = 2 :=
    addOrderOf_h2EquivRatCircle_symm_toRatAddCircle C e hℤ hℚ hC 2
  refine nontrivial_of_ne x 0 fun h ↦ ?_
  simp [h] at hx

end TauCeti.zHat
