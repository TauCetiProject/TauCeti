/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Algebraic

/-!
# Norm twists of algebraic Hecke characters

The norm-power character `c ↦ ‖c‖ ^ s` is algebraic exactly when `s` is an integer.
Consequently, twisting by an integral norm power preserves and reflects algebraicity,
and these are the only norm-power twists that preserve an algebraic character.

At a complex place the modulus exponent is `2 * s`. Integrality of this exponent alone
would only force `s` to be a half-integer. The vanishing angular frequency forces the two
conjugate embedding exponents to agree, giving integrality of `s` itself. At a real place,
the sign parity of the norm character is zero even for odd integral `s`; algebraicity
compares parameters on the identity component and therefore permits this sign discrepancy.

## References

* A. Weil, *Basic Number Theory*, Chapter VII, §3.
-/

public section
noncomputable section

open NumberField

namespace TauCeti.GlobalNumberFields.HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

/-- A norm-power Hecke character is algebraic exactly when its complex exponent is an integer.
This holds also for totally imaginary fields: zero angular frequency forces equal exponents
at the two conjugate embeddings of a complex place. -/
@[simp]
theorem isAlgebraic_normPow_iff {s : ℂ} :
    (normPow K s).IsAlgebraic ↔ ∃ m : ℤ, s = m := by
  constructor
  · intro hs
    obtain ⟨n, e, hn⟩ := isAlgebraic_iff.mp hs
    rw [infinityType_normPow] at hn
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
    rcases w.isReal_or_isComplex with hw | hw
    · refine ⟨n w.embedding, ?_⟩
      simpa using congrArg (fun t : ContinuousInfinityType K ↦ t.realExponent ⟨w, hw⟩) hn
    · have hsum := congrArg
        (fun t : ContinuousInfinityType K ↦ t.complexExponent ⟨w, hw⟩) hn
      have hdiff := congrArg
        (fun t : ContinuousInfinityType K ↦ t.complexAngularFrequency ⟨w, hw⟩) hn
      simp only [ContinuousInfinityType.add_complexExponent, Pi.add_apply,
        AlgebraicInfinityType.toContinuous_complexExponent,
        FiniteOrderInfinityType.toContinuous_complexExponent, add_zero] at hsum
      simp only [ContinuousInfinityType.add_complexAngularFrequency, Pi.add_apply,
        AlgebraicInfinityType.toContinuous_complexAngularFrequency,
        FiniteOrderInfinityType.toContinuous_complexAngularFrequency, add_zero] at hdiff
      have heq : n w.embedding = n (ComplexEmbedding.conjugate w.embedding) := by
        simpa using (sub_eq_zero.mp hdiff.symm)
      refine ⟨n w.embedding, ?_⟩
      rw [← heq] at hsum
      linear_combination hsum / 2
  · rintro ⟨m, rfl⟩
    -- Use the identity-component criterion: odd integers need not have the same real parity
    -- as a norm power, but this does not affect algebraicity.
    rw [isAlgebraic_iff]
    refine ⟨fun _ ↦ m, fun _ ↦ -(m : ZMod 2), ?_⟩
    rw [infinityType_normPow]
    ext w <;> simp [two_mul, CharTwo.add_self_eq_zero]

/-- Twisting by an integral power of the idele norm preserves and reflects algebraicity.
No algebraicity assumption on the original character is needed. -/
@[simp]
theorem isAlgebraic_mul_normPow_int_iff (χ : HeckeCharacter K) (m : ℤ) :
    (χ * normPow K (m : ℂ)).IsAlgebraic ↔ χ.IsAlgebraic := by
  have hm : (normPow K (m : ℂ)).IsAlgebraic := isAlgebraic_normPow_iff.mpr ⟨m, rfl⟩
  exact hm.mul_iff_left

/-- For an algebraic Hecke character, a norm-power twist is algebraic exactly when the
exponent of the twist is an integer. -/
@[simp]
theorem IsAlgebraic.mul_normPow_iff {χ : HeckeCharacter K} (hχ : χ.IsAlgebraic) {s : ℂ} :
    (χ * normPow K s).IsAlgebraic ↔ ∃ m : ℤ, s = m := by
  rw [hχ.mul_iff_right, isAlgebraic_normPow_iff]

end TauCeti.GlobalNumberFields.HeckeCharacter
