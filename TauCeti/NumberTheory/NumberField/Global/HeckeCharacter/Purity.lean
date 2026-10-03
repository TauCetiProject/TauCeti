/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.NormTwist

/-!
# Purity of algebraic Hecke characters

Let `χ` be an algebraic Hecke character of a number field `K`, described on the identity component
by integer exponents `n σ` at the embeddings `σ : K → ℂ`.  Then `χ` is **pure**: the sum
`n σ + n (conjugate σ)` of the exponents at an embedding and its conjugate is the same integer
`w` for every `σ`, the **weight** of `n`.  On the idele class group, `|χ| = ‖·‖ ^ (w / 2)`.
Consequently, an exponent at a real embedding is the shift of `χ` itself.  Thus, over a field with
a real place, the shift of an algebraic character is an integer, and its unitary part is again
algebraic.

The weight is read off from the archimedean components: the shift `σ` of `χ` is the real part of
the modulus exponent at every real place and half of it at every complex place
(`HeckeCharacter.re_realExponent_infinityType`, `HeckeCharacter.re_complexExponent_infinityType`).
The global input is the existence of the shift, that is, the triviality of `|χ|` on the compact
norm-one idele class group, whose compactness is the adelic form of Dirichlet's unit theorem and
the finiteness of the class group.

## Main results

* `TauCeti.GlobalNumberFields.HeckeCharacter.add_conjugate_eq_two_mul_shift`: the exponents at an
  embedding and its conjugate add up to twice the shift.
* `TauCeti.GlobalNumberFields.HeckeCharacter.add_conjugate_eq_add_conjugate`: purity, the sum
  `n σ + n (conjugate σ)` does not depend on `σ`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.IsAlgebraic.exists_intCast_eq_two_mul_shift`: twice
  the shift of an algebraic character is an integer.
* `TauCeti.GlobalNumberFields.HeckeCharacter.IsAlgebraic.exists_intCast_eq_shift_of_isReal`: over
  a field with a real place, the shift of an algebraic character is an integer.
* `TauCeti.GlobalNumberFields.HeckeCharacter.IsAlgebraic.isAlgebraic_unitaryPart_iff`: the unitary
  part of an algebraic character is algebraic exactly when its shift is an integer.

## References

* A. Weil, *Basic Number Theory*, Chapter VII, §3.
* A. Weil, *On a certain type of characters of the idèle-class group of an algebraic
  number-field*, Proceedings of the International Symposium on Algebraic Number Theory,
  Tokyo–Nikko, 1955.
-/

public section

open NumberField

namespace TauCeti.GlobalNumberFields.HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

/-- **Purity of an algebraic Hecke character, with its weight.**  If integer exponents `n`
describe `χ` on the identity component, then for every embedding `σ` the exponents at `σ` and at
its complex conjugate add up to twice the shift of `χ`. -/
theorem add_conjugate_eq_two_mul_shift {χ : HeckeCharacter K} {n : AlgebraicInfinityType K}
    (hn : χ.infinityType.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n))
    (σ : K →+* ℂ) :
    (n σ : ℝ) + n (ComplexEmbedding.conjugate σ) = 2 * χ.shift := by
  obtain ⟨e, he⟩ :=
    (ContinuousInfinityType.agreesOnIdentityComponent_iff_exists_finiteOrderInfinityType _ _).mp hn
  rcases (InfinitePlace.mk σ).isReal_or_isComplex with hw | hw
  · have hσ : ComplexEmbedding.IsReal σ := InfinitePlace.isReal_mk_iff.mp hw
    have h := χ.re_realExponent_infinityType ⟨_, hw⟩
    simp only [he, ContinuousInfinityType.add_realExponent, Pi.add_apply,
      AlgebraicInfinityType.toContinuous_realExponent,
      FiniteOrderInfinityType.toContinuous_realExponent, add_zero,
      InfinitePlace.embedding_mk_eq_of_isReal hσ, Complex.intCast_re] at h
    rw [ComplexEmbedding.isReal_iff.mp hσ, h, two_mul]
  · have h := χ.re_complexExponent_infinityType ⟨_, hw⟩
    simp only [he, ContinuousInfinityType.add_complexExponent, Pi.add_apply,
      AlgebraicInfinityType.toContinuous_complexExponent,
      FiniteOrderInfinityType.toContinuous_complexExponent, add_zero, Complex.add_re,
      Complex.intCast_re] at h
    rcases InfinitePlace.embedding_mk_eq σ with he | he
    · rwa [he] at h
    · simpa only [he, ComplexEmbedding.conjugate, star_star, add_comm] using h

/-- **Purity of an algebraic Hecke character.**  If integer exponents `n` describe `χ` on the
identity component, then the sum `n σ + n (conjugate σ)` of the exponents at an embedding and its
conjugate is the same for all embeddings `σ`. -/
theorem add_conjugate_eq_add_conjugate {χ : HeckeCharacter K} {n : AlgebraicInfinityType K}
    (hn : χ.infinityType.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n))
    (σ τ : K →+* ℂ) :
    n σ + n (ComplexEmbedding.conjugate σ) = n τ + n (ComplexEmbedding.conjugate τ) := by
  have h := (add_conjugate_eq_two_mul_shift hn σ).trans (add_conjugate_eq_two_mul_shift hn τ).symm
  exact_mod_cast h

/-- At a real embedding, the exponent of an algebraic Hecke character is its shift. -/
theorem intCast_eq_shift_of_isReal {χ : HeckeCharacter K} {n : AlgebraicInfinityType K}
    (hn : χ.infinityType.AgreesOnIdentityComponent (AlgebraicInfinityType.toContinuous n))
    {σ : K →+* ℂ} (hσ : ComplexEmbedding.IsReal σ) :
    (n σ : ℝ) = χ.shift := by
  have h := add_conjugate_eq_two_mul_shift hn σ
  rw [ComplexEmbedding.isReal_iff.mp hσ] at h
  linarith

/-- **Twice the shift of an algebraic Hecke character is an integer**, the weight of its infinity
type. -/
theorem IsAlgebraic.exists_intCast_eq_two_mul_shift {χ : HeckeCharacter K} (hχ : χ.IsAlgebraic) :
    ∃ m : ℤ, (m : ℝ) = 2 * χ.shift := by
  obtain ⟨n, e, he⟩ := isAlgebraic_iff.mp hχ
  have hn := (ContinuousInfinityType.agreesOnIdentityComponent_iff_exists_finiteOrderInfinityType
    _ _).mpr ⟨e, he⟩
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  exact ⟨n w.embedding + n (ComplexEmbedding.conjugate w.embedding), by
    push_cast
    exact add_conjugate_eq_two_mul_shift hn w.embedding⟩

/-- **Over a field with a real place, the shift of an algebraic Hecke character is an
integer.**  For a totally imaginary field the shift can be a half-integer. -/
theorem IsAlgebraic.exists_intCast_eq_shift_of_isReal {χ : HeckeCharacter K}
    (hχ : χ.IsAlgebraic) {w : InfinitePlace K} (hw : w.IsReal) :
    ∃ m : ℤ, (m : ℝ) = χ.shift := by
  obtain ⟨n, e, he⟩ := isAlgebraic_iff.mp hχ
  have hn := (ContinuousInfinityType.agreesOnIdentityComponent_iff_exists_finiteOrderInfinityType
    _ _).mpr ⟨e, he⟩
  exact ⟨n w.embedding, intCast_eq_shift_of_isReal hn (InfinitePlace.isReal_iff.mp hw)⟩

/-- The unitary part of an algebraic Hecke character is algebraic exactly when the shift is an
integer. -/
theorem IsAlgebraic.isAlgebraic_unitaryPart_iff {χ : HeckeCharacter K} (hχ : χ.IsAlgebraic) :
    χ.unitaryPart.IsAlgebraic ↔ ∃ m : ℤ, (m : ℝ) = χ.shift := by
  rw [unitaryPart_def, hχ.mul_normPow_iff]
  refine ⟨fun ⟨m, hm⟩ ↦ ⟨-m, ?_⟩, fun ⟨m, hm⟩ ↦ ⟨-m, ?_⟩⟩
  · have h := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.ofReal_re, Complex.intCast_re] at h
    push_cast
    linarith
  · simp [← hm]

/-- Over a field with a real place, the unitary part of an algebraic Hecke character is
algebraic. -/
theorem IsAlgebraic.unitaryPart_of_isReal {χ : HeckeCharacter K} (hχ : χ.IsAlgebraic)
    {w : InfinitePlace K} (hw : w.IsReal) : χ.unitaryPart.IsAlgebraic :=
  hχ.isAlgebraic_unitaryPart_iff.mpr (hχ.exists_intCast_eq_shift_of_isReal hw)

end TauCeti.GlobalNumberFields.HeckeCharacter
