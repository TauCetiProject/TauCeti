/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Trace characters on residue rings of number fields

The phase in a number-field Gauss sum is `exp (2πi Tr(xy))`. It depends only on
`x mod I` precisely when `y` belongs to the trace dual of `I`, namely
`I⁻¹ 𝔡⁻¹`. This file constructs that additive character as `Ideal.traceAddChar`,
using Mathlib's `Real.fourierChar` and `FractionalIdeal.dual`.

The evaluation lemma `Ideal.traceAddChar_mk` permits any representative of a residue
class. The character is trivial exactly when its parameter lies in the inverse different,
and two parameters give the same character exactly when their difference lies there
(`Ideal.traceAddChar_eq_iff`). Thus no choices of representatives enter the Gauss-sum phase,
including at `I = ⊤`, where the residue ring has one element.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6, (6.3).
-/

public section

noncomputable section

open NumberField
open scoped NumberField nonZeroDivisors

namespace TauCeti

variable (K : Type*) [Field K] [NumberField K]

/-- The standard trace character of a number field, with the positive Fourier sign:
`x ↦ exp (2πi Tr_{K/ℚ}(x))`. -/
def numberFieldTraceChar : AddChar K Circle :=
  Real.fourierChar.compAddMonoidHom
    ((Rat.castHom ℝ).toAddMonoidHom.comp (Algebra.trace ℚ K).toAddMonoidHom)

@[simp]
theorem numberFieldTraceChar_apply (x : K) :
    numberFieldTraceChar K x = Real.fourierChar (Algebra.trace ℚ K x : ℝ) := (rfl)

/-- The trace character is one exactly when the rational trace is an integer. -/
theorem numberFieldTraceChar_eq_one_iff (x : K) :
    numberFieldTraceChar K x = 1 ↔ Algebra.trace ℚ K x ∈ (algebraMap ℤ ℚ).range := by
  rw [numberFieldTraceChar_apply, Real.fourierChar_apply', Circle.exp_eq_one]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : (Algebra.trace ℚ K x : ℝ) = n := by
      nlinarith [Real.pi_pos]
    exact_mod_cast h.symm
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have hn' : (n : ℚ) = Algebra.trace ℚ K x := hn
    rw [← hn', Rat.cast_intCast]
    ring

end TauCeti

namespace Ideal

open TauCeti

variable {K : Type*} [Field K] [NumberField K]
variable (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)

include hI in
/-- The inverse-different condition for the phase to vanish on an integral ideal.
Mathlib's trace dual is `I⁻¹ 𝔡⁻¹`, by `FractionalIdeal.dual_eq_mul_inv`. -/
theorem mem_dual_iff_traceChar_eq_one (y : K) :
    y ∈ FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ a ∈ I, numberFieldTraceChar K (y * algebraMap (𝓞 K) K a) = 1 := by
  rw [FractionalIdeal.mem_dual (FractionalIdeal.coeIdeal_ne_zero.mpr hI)]
  simp only [Algebra.traceForm_apply]
  constructor
  · intro hy a ha
    exact (numberFieldTraceChar_eq_one_iff K _).mpr
      (hy _ ((FractionalIdeal.mem_coeIdeal _).mpr ⟨a, ha, rfl⟩))
  · intro hy a ha
    obtain ⟨b, hb, hab⟩ := (FractionalIdeal.mem_coeIdeal _).mp ha
    rw [← hab]
    exact (numberFieldTraceChar_eq_one_iff K _).mp (hy b hb)

/-- The additive character of `𝓞 K / I` with parameter `y ∈ I⁻¹ 𝔡⁻¹`, given by
`x ↦ exp (2πi Tr(xy))`. The trace-dual condition makes the phase independent of the
representative of `x`. -/
def traceAddChar
    (y : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    AddChar (𝓞 K ⧸ I) ℂ :=
  Circle.coeHom.compAddChar <| AddChar.toAddMonoidHomEquiv.symm <|
    QuotientAddGroup.lift I.toAddSubgroup
      (((numberFieldTraceChar K).mulShift (y : K)).compAddMonoidHom
        (algebraMap (𝓞 K) K).toAddMonoidHom).toAddMonoidHom
      (fun a ha ↦ (I.mem_dual_iff_traceChar_eq_one hI y).mp y.property a ha)

/-- Evaluate the trace character using any representative of a residue class. -/
@[simp]
theorem traceAddChar_mk
    (y : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
    (a : 𝓞 K) :
    I.traceAddChar hI y (Ideal.Quotient.mk I a) =
      (numberFieldTraceChar K ((y : K) * algebraMap (𝓞 K) K a) : ℂ) := (rfl)

/-- The zero parameter gives the trivial residue character. -/
@[simp]
theorem traceAddChar_zero : I.traceAddChar hI 0 = 1 := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- Adding parameters multiplies the residue characters. -/
@[simp]
theorem traceAddChar_add
    (y z : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    I.traceAddChar hI (y + z) = I.traceAddChar hI y * I.traceAddChar hI z := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [traceAddChar_mk, Submodule.coe_add, add_mul, AddChar.map_add_eq_mul,
    Circle.coe_mul, mul_apply]

/-- The phase of the trace character has absolute value one at every residue class. -/
@[simp]
theorem norm_traceAddChar
    (y : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
    (x : 𝓞 K ⧸ I) :
    ‖I.traceAddChar hI y x‖ = 1 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [traceAddChar_mk, Circle.norm_coe]

/-- Characterization of the trivial trace character: its parameter is in the inverse different. -/
@[simp]
theorem traceAddChar_eq_one_iff
    (y : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    I.traceAddChar hI y = 1 ↔
      (y : K) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.mem_dual one_ne_zero]
  constructor
  · intro h a ha
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    apply (numberFieldTraceChar_eq_one_iff K _).mp
    apply Subtype.val_injective
    simpa using DFunLike.congr_fun h (Ideal.Quotient.mk I a)
  · intro hy
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [traceAddChar_mk, one_apply]
    exact congrArg Subtype.val ((numberFieldTraceChar_eq_one_iff K _).mpr
      (hy _ ((FractionalIdeal.mem_one_iff _).mpr ⟨a, rfl⟩)))

/-- Parameters differing by the inverse different define the same residue character, and only
such parameters do. -/
theorem traceAddChar_eq_iff
    (y z : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    I.traceAddChar hI y = I.traceAddChar hI z ↔
      (y : K) - (z : K) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [FractionalIdeal.mem_dual one_ne_zero]
  simp only [Algebra.traceForm_apply]
  constructor
  · intro h a ha
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    apply (numberFieldTraceChar_eq_one_iff K _).mp
    rw [sub_mul, AddChar.map_sub_eq_div, div_eq_one]
    apply Subtype.val_injective
    simpa only [traceAddChar_mk] using DFunLike.congr_fun h (Ideal.Quotient.mk I a)
  · intro hy
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h := (numberFieldTraceChar_eq_one_iff K _).mpr
      (hy _ ((FractionalIdeal.mem_one_iff _).mpr ⟨a, rfl⟩))
    rw [sub_mul, AddChar.map_sub_eq_div, div_eq_one] at h
    exact congrArg Subtype.val h

/-- Multiplying the parameter by an algebraic integer multiplies the residue argument by
its class. This is the change of phase used to reindex number-field Gauss sums. -/
theorem traceAddChar_smul
    (y : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
    (a : 𝓞 K) :
    I.traceAddChar hI (a • y) = (I.traceAddChar hI y).mulShift (Ideal.Quotient.mk I a) := by
  ext x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [AddChar.mulShift_apply, ← map_mul, traceAddChar_mk, traceAddChar_mk]
  simp only [Submodule.coe_smul, Algebra.smul_def, map_mul]
  congr 2
  ring

end Ideal
