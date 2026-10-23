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
`m` for every `σ`, the **weight** of `n`.  On the idele class group, `|χ| = ‖·‖ ^ (m / 2)`.
Consequently, an exponent at a real embedding is the shift of `χ` itself.  Thus, over a field with
a real place, the shift of an algebraic character is an integer, and its unitary part is again
algebraic.

The weight is read off from the archimedean components: the shift of `χ` is the real part of
the modulus exponent at every real place and half of it at every complex place
(`HeckeCharacter.re_realExponent_infinityType`, `HeckeCharacter.re_complexExponent_infinityType`).
The global input is the existence of the shift, that is, the triviality of `|χ|` on the compact
norm-one idele class group, whose compactness is the adelic form of Dirichlet's unit theorem and
the finiteness of the class group.

## Main results

* `TauCeti.GlobalNumberFields.HeckeCharacter.intCast_add_intCast_conjugate_eq_two_mul_shift`: the
  exponents at an embedding and its conjugate add up to twice the shift after casting to `ℝ`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.add_conjugate_eq_add_conjugate`: purity, the sum
  `n σ + n (conjugate σ)` does not depend on `σ`.
* `TauCeti.GlobalNumberFields.HeckeCharacter.exists_weight`: the common integer weight controls
  both the embedding exponents and the shift.
* `TauCeti.GlobalNumberFields.HeckeCharacter.IsAlgebraic.exists_intCast_eq_two_mul_shift`: twice
  the shift of an algebraic character is an integer.
* `TauCeti.GlobalNumberFields.HeckeCharacter.IsAlgebraic.exists_intCast_eq_shift_of_isReal`: over
  a field with a real place, the shift of an algebraic character is an integer.
* `TauCeti.GlobalNumberFields.HeckeCharacter.IsAlgebraic.unitaryPart_iff`: the unitary
  part of an algebraic character is algebraic exactly when its shift is an integer.

## References

* A. Weil, *Basic Number Theory*, Chapter VII, §3.
* A. Weil, *On a certain type of characters of the idèle-class group of an algebraic
  number-field*, Proceedings of the International Symposium on Algebraic Number Theory,
  Tokyo–Nikko, 1955.
-/

public section

open NumberField
open scoped NumberField NNReal

namespace TauCeti.GlobalNumberFields.HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

/-- At a real embedding, the exponent of `n` is the shift of `χ` when their real modulus
exponents agree. -/
theorem intCast_eq_shift_of_isReal {χ : HeckeCharacter K} {n : AlgebraicInfinityType K}
    (hr : χ.infinityType.realExponent =
      (AlgebraicInfinityType.toContinuous n).realExponent)
    {σ : K →+* ℂ} (hσ : ComplexEmbedding.IsReal σ) :
    (n σ : ℝ) = χ.shift := by
  have hw : (InfinitePlace.mk σ).IsReal := InfinitePlace.isReal_mk_iff.mpr hσ
  have h := χ.re_realExponent_infinityType ⟨_, hw⟩
  rw [congrFun hr ⟨_, hw⟩] at h
  simpa only [AlgebraicInfinityType.toContinuous_realExponent,
    InfinitePlace.embedding_mk_eq_of_isReal hσ, Complex.intCast_re] using h

/-- **Purity of an algebraic Hecke character, with its weight.**  If the real and complex modulus
exponents of `n` agree with those of `χ`, then for every embedding `σ` the exponents at `σ` and at
its complex conjugate add up to twice the shift of `χ`. -/
theorem intCast_add_intCast_conjugate_eq_two_mul_shift {χ : HeckeCharacter K}
    {n : AlgebraicInfinityType K}
    (hr : χ.infinityType.realExponent =
      (AlgebraicInfinityType.toContinuous n).realExponent)
    (hc : χ.infinityType.complexExponent =
      (AlgebraicInfinityType.toContinuous n).complexExponent)
    (σ : K →+* ℂ) :
    (n σ : ℝ) + n (ComplexEmbedding.conjugate σ) = 2 * χ.shift := by
  rcases (InfinitePlace.mk σ).isReal_or_isComplex with hw | hw
  · have hσ : ComplexEmbedding.IsReal σ := InfinitePlace.isReal_mk_iff.mp hw
    rw [ComplexEmbedding.isReal_iff.mp hσ, intCast_eq_shift_of_isReal hr hσ, two_mul]
  · have h := χ.re_complexExponent_infinityType ⟨_, hw⟩
    rw [congrFun hc ⟨_, hw⟩] at h
    simp only [AlgebraicInfinityType.toContinuous_complexExponent, Complex.add_re,
      Complex.intCast_re] at h
    rcases InfinitePlace.embedding_mk_eq σ with hemb | hemb
    · rwa [hemb] at h
    · simpa only [hemb, ComplexEmbedding.involutive_conjugate K σ, add_comm] using h

/-- **Purity of an algebraic Hecke character.**  If the real and complex modulus exponents of `n`
agree with those of `χ`, then the sum `n σ + n (conjugate σ)` of the exponents at an embedding and
its conjugate is the same for all embeddings `σ`. -/
theorem add_conjugate_eq_add_conjugate {χ : HeckeCharacter K} {n : AlgebraicInfinityType K}
    (hr : χ.infinityType.realExponent =
      (AlgebraicInfinityType.toContinuous n).realExponent)
    (hc : χ.infinityType.complexExponent =
      (AlgebraicInfinityType.toContinuous n).complexExponent)
    (σ τ : K →+* ℂ) :
    n σ + n (ComplexEmbedding.conjugate σ) = n τ + n (ComplexEmbedding.conjugate τ) := by
  have h := (intCast_add_intCast_conjugate_eq_two_mul_shift hr hc σ).trans
    (intCast_add_intCast_conjugate_eq_two_mul_shift hr hc τ).symm
  exact_mod_cast h

/-- **The weight of an algebraic infinity type.**  If the real and complex modulus exponents of
`n` agree with those of `χ`, its conjugate-pair sums have a common integer value whose real cast is
twice the shift of `χ`. -/
theorem exists_weight {χ : HeckeCharacter K} {n : AlgebraicInfinityType K}
    (hr : χ.infinityType.realExponent =
      (AlgebraicInfinityType.toContinuous n).realExponent)
    (hc : χ.infinityType.complexExponent =
      (AlgebraicInfinityType.toContinuous n).complexExponent) :
    ∃ m : ℤ, (∀ σ : K →+* ℂ, n σ + n (ComplexEmbedding.conjugate σ) = m) ∧
      (m : ℝ) = 2 * χ.shift := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  refine ⟨n w.embedding + n (ComplexEmbedding.conjugate w.embedding), ?_, ?_⟩
  · exact fun σ ↦ add_conjugate_eq_add_conjugate hr hc σ w.embedding
  · push_cast
    exact intCast_add_intCast_conjugate_eq_two_mul_shift hr hc w.embedding

/-- **Twice the shift of an algebraic Hecke character is an integer**, the weight of its infinity
type. -/
theorem IsAlgebraic.exists_intCast_eq_two_mul_shift {χ : HeckeCharacter K} (hχ : χ.IsAlgebraic) :
    ∃ m : ℤ, (m : ℝ) = 2 * χ.shift := by
  obtain ⟨n, hn⟩ := isAlgebraic_iff_exists_agreesOnIdentityComponent.mp hχ
  obtain ⟨hr, hc, -⟩ := ContinuousInfinityType.agreesOnIdentityComponent_iff _ _ |>.mp hn
  obtain ⟨m, -, hm⟩ := exists_weight hr hc
  exact ⟨m, hm⟩

/-- **The absolute value of an algebraic Hecke character is a half-integral power of the idele
class norm.**  The numerator is the integer weight of the character. -/
theorem IsAlgebraic.exists_weight_norm_apply {χ : HeckeCharacter K} (hχ : χ.IsAlgebraic) :
    ∃ m : ℤ, ∀ c : IdeleClassGroup (𝓞 K) K,
      ‖(χ c : ℂ)‖ = ((ideleClassNorm c : ℝ≥0) : ℝ) ^ ((m : ℝ) / 2) := by
  obtain ⟨m, hm⟩ := hχ.exists_intCast_eq_two_mul_shift
  refine ⟨m, fun c ↦ ?_⟩
  rw [norm_apply_eq_rpow_shift]
  congr 1
  linarith

/-- **Over a field with a real place, the shift of an algebraic Hecke character is an
integer.**  For a totally imaginary field the shift can be a half-integer. -/
theorem IsAlgebraic.exists_intCast_eq_shift_of_isReal {χ : HeckeCharacter K}
    (hχ : χ.IsAlgebraic) {w : InfinitePlace K} (hw : w.IsReal) :
    ∃ m : ℤ, (m : ℝ) = χ.shift := by
  obtain ⟨n, hn⟩ := isAlgebraic_iff_exists_agreesOnIdentityComponent.mp hχ
  obtain ⟨hr, -, -⟩ := ContinuousInfinityType.agreesOnIdentityComponent_iff _ _ |>.mp hn
  exact ⟨n w.embedding, intCast_eq_shift_of_isReal hr (InfinitePlace.isReal_iff.mp hw)⟩

/-- The unitary part of an algebraic Hecke character is algebraic exactly when the shift is an
integer. -/
theorem IsAlgebraic.unitaryPart_iff {χ : HeckeCharacter K} (hχ : χ.IsAlgebraic) :
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
  hχ.unitaryPart_iff.mpr (hχ.exists_intCast_eq_shift_of_isReal hw)

end TauCeti.GlobalNumberFields.HeckeCharacter
