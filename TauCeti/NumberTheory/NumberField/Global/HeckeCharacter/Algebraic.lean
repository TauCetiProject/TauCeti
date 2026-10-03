/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.InfinityType
public import TauCeti.NumberTheory.NumberField.Global.InfinityType.IdentityComponent

/-!
# Algebraic Hecke characters

A Hecke character is **algebraic** (of Weil type `A₀`) when its archimedean parameters agree
with those of integer exponents at the complex embeddings on the identity component.  Thus signs
at real places are deliberately ignored.  In particular every finite-order Hecke character is
algebraic, including characters with nontrivial real signs.

The unitary norm characters `c ↦ ‖c‖ ^ (it)` provide the basic separation from arbitrary
continuous Hecke characters.  When `t ≠ 0`, their archimedean modulus exponents are nonzero and
purely imaginary, so they are neither algebraic nor of finite order.

## Main definitions

* `TauCeti.GlobalNumberFields.HeckeCharacter.IsAlgebraic`: Weil's type `A₀` condition.
* `TauCeti.GlobalNumberFields.HeckeCharacter.normCharacter`: the unitary norm character
  `c ↦ ‖c‖ ^ (it)`.

## Main results

* `TauCeti.GlobalNumberFields.HeckeCharacter.isAlgebraic_of_isFiniteOrder`: finite-order Hecke
  characters are algebraic.
* `TauCeti.GlobalNumberFields.HeckeCharacter.not_isAlgebraic_normCharacter`: a nontrivial unitary
  norm character is not algebraic.
* `TauCeti.GlobalNumberFields.HeckeCharacter.not_isFiniteOrder_normCharacter`: a nontrivial
  unitary norm character does not have finite order.

## References

* A. Weil, *Basic Number Theory*, Chapter VII, §3.
-/

public section
noncomputable section

open NumberField
open scoped NumberField NNReal

namespace TauCeti.GlobalNumberFields

namespace HeckeCharacter

variable {K : Type*} [Field K] [NumberField K]

/-! ### Algebraicity -/

/-- A Hecke character is **algebraic** (of Weil type `A₀`) when its infinity type agrees with
the continuous infinity type of integer embedding exponents on the identity component.  Real sign
parities are not constrained. -/
def IsAlgebraic (χ : HeckeCharacter K) : Prop :=
  χ.infinityType.IsAlgebraicOnIdentityComponent

/-- Algebraicity is equivalent to an algebraic infinity type together with an unrestricted
finite-order sign twist at the real places. -/
theorem isAlgebraic_iff {χ : HeckeCharacter K} :
    χ.IsAlgebraic ↔
      ∃ (n : AlgebraicInfinityType K) (e : FiniteOrderInfinityType K),
        χ.infinityType =
          AlgebraicInfinityType.toContinuous n + FiniteOrderInfinityType.toContinuous e :=
  ContinuousInfinityType.isAlgebraicOnIdentityComponent_iff χ.infinityType

/-- The trivial Hecke character is algebraic. -/
@[simp]
theorem isAlgebraic_one : (1 : HeckeCharacter K).IsAlgebraic := by
  rw [isAlgebraic_iff]
  exact ⟨0, 0, by simp⟩

/-- A product of algebraic Hecke characters is algebraic. -/
theorem IsAlgebraic.mul {χ ψ : HeckeCharacter K} (hχ : χ.IsAlgebraic)
    (hψ : ψ.IsAlgebraic) : (χ * ψ).IsAlgebraic := by
  rw [isAlgebraic_iff] at hχ hψ ⊢
  obtain ⟨n, e, hn⟩ := hχ
  obtain ⟨m, f, hm⟩ := hψ
  refine ⟨n + m, e + f, ?_⟩
  rw [infinityType_mul, hn, hm, map_add, map_add]
  abel

/-- The inverse of an algebraic Hecke character is algebraic. -/
theorem IsAlgebraic.inv {χ : HeckeCharacter K} (hχ : χ.IsAlgebraic) : χ⁻¹.IsAlgebraic := by
  rw [isAlgebraic_iff] at hχ ⊢
  obtain ⟨n, e, h⟩ := hχ
  refine ⟨-n, -e, ?_⟩
  rw [infinityType_inv, h, map_neg, map_neg]
  abel

/-- Multiplication by an algebraic Hecke character on the right preserves and reflects
algebraicity. -/
theorem IsAlgebraic.mul_iff_left {χ ψ : HeckeCharacter K} (hψ : ψ.IsAlgebraic) :
    (χ * ψ).IsAlgebraic ↔ χ.IsAlgebraic := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mul hψ⟩
  simpa only [mul_inv_cancel_right] using h.mul hψ.inv

/-- Multiplication by an algebraic Hecke character on the left preserves and reflects
algebraicity. -/
theorem IsAlgebraic.mul_iff_right {χ ψ : HeckeCharacter K} (hχ : χ.IsAlgebraic) :
    (χ * ψ).IsAlgebraic ↔ ψ.IsAlgebraic := by
  simpa only [mul_comm χ] using hχ.mul_iff_left (χ := ψ)

/-- Every natural power of an algebraic Hecke character is algebraic. -/
theorem IsAlgebraic.pow {χ : HeckeCharacter K} (hχ : χ.IsAlgebraic) (m : ℕ) :
    (χ ^ m).IsAlgebraic := by
  induction m with
  | zero => simp
  | succ m ih => simpa [pow_succ] using ih.mul hχ

/-- **Every finite-order Hecke character is algebraic.** Its infinity type consists only of real
signs, hence agrees with the zero algebraic infinity type on the identity component. -/
theorem isAlgebraic_of_isFiniteOrder {χ : HeckeCharacter K} (hχ : χ.IsFiniteOrder) :
    χ.IsAlgebraic := by
  obtain ⟨e, he⟩ := exists_finiteOrderInfinityType hχ
  rw [isAlgebraic_iff]
  exact ⟨0, e, by simpa using he⟩

/-- A Hecke character pulled back from a ray class character is algebraic. -/
theorem isAlgebraic_ofRayClassCharacter {m : Modulus K} (e : RayClassCharacter m) :
    (ofRayClassCharacter m e).IsAlgebraic :=
  isAlgebraic_of_isFiniteOrder (isFiniteOrder_ofRayClassCharacter e)

/-! ### A nonalgebraic unitary family -/

/-- The **unitary norm character** `c ↦ ‖c‖ ^ (it)` for `t : ℝ`. -/
def normCharacter (K : Type*) [Field K] [NumberField K] (t : ℝ) : HeckeCharacter K :=
  normPow K (Complex.I * t)

/-- The unitary norm character is the norm-power character with exponent `it`. -/
theorem normCharacter_def (t : ℝ) : normCharacter K t = normPow K (Complex.I * t) :=
  (rfl)

/-- The value of the unitary norm character at an idele class is `‖c‖ ^ (it)`. -/
@[simp]
theorem normCharacter_apply (t : ℝ)
    (c : IdeleClassGroup (NumberField.RingOfIntegers K) K) :
    ((normCharacter K t c : ℂˣ) : ℂ) =
      (((ideleClassNorm c : ℝ≥0) : ℝ) : ℂ) ^ (Complex.I * t) := by
  rw [normCharacter_def, normPow_apply]

/-- The unitary norm character with parameter zero is trivial. -/
@[simp]
theorem normCharacter_zero : normCharacter K 0 = 1 := by
  rw [normCharacter_def]
  simp

/-- Adding parameters multiplies the corresponding unitary norm characters. -/
theorem normCharacter_add (s t : ℝ) :
    normCharacter K (s + t) = normCharacter K s * normCharacter K t := by
  rw [normCharacter_def, normCharacter_def, normCharacter_def]
  push_cast
  rw [mul_add, normPow_add]

/-- Negating the parameter inverts the unitary norm character. -/
theorem normCharacter_neg (t : ℝ) : normCharacter K (-t) = (normCharacter K t)⁻¹ := by
  rw [normCharacter_def, normCharacter_def]
  push_cast
  rw [mul_neg, normPow_neg]

/-- The infinity type of `c ↦ ‖c‖ ^ (it)` has exponent `it` at real places and `2it` at
complex places, with no sign parity or angular frequency. -/
theorem infinityType_normCharacter (t : ℝ) :
    (normCharacter K t).infinityType =
      { realExponent := fun _ ↦ Complex.I * t
        realParity := 0
        complexExponent := fun _ ↦ 2 * (Complex.I * t)
        complexAngularFrequency := 0 } := by
  rw [normCharacter_def, infinityType_normPow]

/-- The unitary norm character has shift zero. -/
@[simp]
theorem shift_normCharacter (t : ℝ) : (normCharacter K t).shift = 0 := by
  simp [normCharacter_def]

/-- **A nontrivial unitary norm character is not algebraic.** Its nonzero purely imaginary
archimedean exponent cannot be the sum of integer embedding exponents. -/
theorem not_isAlgebraic_normCharacter {t : ℝ} (ht : t ≠ 0) :
    ¬ (normCharacter K t).IsAlgebraic := by
  rw [isAlgebraic_iff]
  rintro ⟨n, e, hn⟩
  rw [infinityType_normCharacter] at hn
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  rcases w.isReal_or_isComplex with hw | hw
  · have h := congrArg (fun u : ContinuousInfinityType K ↦ u.realExponent ⟨w, hw⟩) hn
    have him := congrArg Complex.im h
    simp only [Complex.mul_im, Complex.I_re, Complex.ofReal_im, mul_zero, Complex.I_im,
      Complex.ofReal_re, one_mul, zero_add, ContinuousInfinityType.add_realExponent,
      Pi.add_apply, AlgebraicInfinityType.toContinuous_realExponent,
      FiniteOrderInfinityType.toContinuous_realExponent, add_zero, Complex.intCast_im] at him
    exact ht him
  · have h := congrArg (fun u : ContinuousInfinityType K ↦ u.complexExponent ⟨w, hw⟩) hn
    have him := congrArg Complex.im h
    simp only [Complex.mul_im, Complex.re_ofNat, Complex.I_re, Complex.ofReal_im, mul_zero,
      Complex.I_im, Complex.ofReal_re, one_mul, zero_add, Complex.im_ofNat, Complex.mul_re,
      zero_mul, sub_self, ContinuousInfinityType.add_complexExponent, Pi.add_apply,
      AlgebraicInfinityType.toContinuous_complexExponent,
      FiniteOrderInfinityType.toContinuous_complexExponent, Complex.add_im, Complex.intCast_im,
      Complex.zero_im] at him
    exact ht (by linarith)

/-- **A nontrivial unitary norm character does not have finite order.** -/
theorem not_isFiniteOrder_normCharacter {t : ℝ} (ht : t ≠ 0) :
    ¬ (normCharacter K t).IsFiniteOrder := by
  rw [normCharacter_def, isFiniteOrder_normPow_iff]
  simp [ht]

end HeckeCharacter

end TauCeti.GlobalNumberFields
