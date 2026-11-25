/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.NumberTheory.NumberField.Basic

/-!
# Trace characters on residue rings of number fields

Let `I` be a nonzero ideal of `𝓞 K`. The phase `exp (2πi Tr(xy))`, for `x ∈ 𝓞 K`
and `y ∈ K`, depends only on `x mod I` precisely when `y` belongs to the trace dual
`I⁻¹ 𝔡⁻¹`. This file constructs that additive character as `Ideal.traceAddChar`,
using Mathlib's `Real.fourierChar` and `FractionalIdeal.dual`. The construction also
works for the zero ideal, whose trace dual in Mathlib is zero.

The evaluation lemma `Ideal.traceAddChar_mk` permits any representative of a residue
class. The character is trivial exactly when its parameter lies in the inverse different,
and two parameters give the same character exactly when their difference lies there
(`Ideal.traceAddChar_eq_iff`). Thus no choices of representatives enter the Gauss-sum phase,
including at `I = ⊤`, where the residue ring has one element.

The trace character of `y` is primitive exactly when `z y ∈ 𝔡⁻¹` forces `z ∈ I`
(`Ideal.isPrimitive_traceAddChar_iff`), in particular when the integral ideal `y I 𝔡` is prime
to `I` (`Ideal.isPrimitive_traceAddChar`).

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

/-- Evaluate the trace character by applying the real Fourier character to the rational trace. -/
theorem numberFieldTraceChar_apply (x : K) :
    numberFieldTraceChar K x = Real.fourierChar (Algebra.trace ℚ K x : ℝ) := by
  simp [numberFieldTraceChar]

/-- The trace character takes the value one exactly when the rational trace is an integer. -/
@[simp]
theorem numberFieldTraceChar_apply_eq_one_iff (x : K) :
    numberFieldTraceChar K x = 1 ↔ Algebra.trace ℚ K x ∈ (algebraMap ℤ ℚ).range := by
  rw [numberFieldTraceChar_apply, Real.fourierChar_apply', Circle.exp_eq_one]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h : (Algebra.trace ℚ K x : ℝ) = n := by
      nlinarith [Real.pi_pos]
    rw [eq_intCast]
    exact_mod_cast h.symm
  · rintro ⟨n, hn⟩
    exact ⟨n, by rw [← hn, eq_intCast, Rat.cast_intCast, mul_comm]⟩

end TauCeti

open TauCeti

namespace FractionalIdeal

variable {K : Type*} [Field K] [NumberField K]

/-- A parameter lies in the trace dual of a nonzero fractional ideal `J` exactly when
its trace phase takes the value one on every element of `J`. -/
theorem mem_dual_iff_forall_numberFieldTraceChar_eq_one
    (J : FractionalIdeal (𝓞 K)⁰ K) (hJ : J ≠ 0) (y : K) :
    y ∈ dual ℤ ℚ J ↔ ∀ a ∈ J, numberFieldTraceChar K (y * a) = 1 := by
  rw [mem_dual hJ]
  simp only [Algebra.traceForm_apply, numberFieldTraceChar_apply_eq_one_iff]

end FractionalIdeal

namespace Ideal

variable {K : Type*} [Field K] [NumberField K]
variable (I : Ideal (𝓞 K))

/-- A parameter lies in the trace dual of a nonzero ideal `I` exactly when its trace phase
is one on every algebraic integer in `I`. The trace dual is `I⁻¹ 𝔡⁻¹` by
`FractionalIdeal.dual_eq_mul_inv` and `coeIdeal_differentIdeal`. -/
theorem mem_dual_iff_forall_numberFieldTraceChar_eq_one (hI : I ≠ ⊥) (y : K) :
    y ∈ FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) ↔
      ∀ a ∈ I, numberFieldTraceChar K (y * algebraMap (𝓞 K) K a) = 1 := by
  rw [FractionalIdeal.mem_dual_iff_forall_numberFieldTraceChar_eq_one _
    (FractionalIdeal.coeIdeal_ne_zero.mpr hI)]
  constructor
  · intro hy a ha
    exact hy _ ((FractionalIdeal.mem_coeIdeal _).mpr ⟨a, ha, rfl⟩)
  · intro hy a ha
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp ha
    exact hy b hb

/-- The additive character of `𝓞 K / I` given by `x ↦ exp (2πi Tr(xy))`.
The parameter `y` belongs to the trace dual of `I`, which is `I⁻¹ 𝔡⁻¹` when `I ≠ ⊥`.
This ensures the phase is independent of the representative of `x`. -/
def traceAddChar
    (y : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    AddChar (𝓞 K ⧸ I) ℂ :=
  Circle.coeHom.compAddChar <| AddChar.toAddMonoidHomEquiv.symm <|
    QuotientAddGroup.lift I.toAddSubgroup
      (((numberFieldTraceChar K).mulShift (y : K)).compAddMonoidHom
        (algebraMap (𝓞 K) K).toAddMonoidHom).toAddMonoidHom
      (fun a ha ↦ by
        have haI := (Submodule.mem_toAddSubgroup I).mp ha
        simp only [AddMonoidHom.mem_ker, AddChar.toAddMonoidHom_apply,
          AddChar.compAddMonoidHom_apply, AddChar.mulShift_apply, ofMul_eq_zero]
        by_cases hI : I = ⊥
        · have h : a = 0 := Ideal.mem_bot.mp (hI ▸ haI)
          simp [h]
        · exact (I.mem_dual_iff_forall_numberFieldTraceChar_eq_one hI y).mp y.property a haI)

/-- Evaluate the trace character using any representative of a residue class. -/
@[simp]
theorem traceAddChar_mk
    (y : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
    (a : 𝓞 K) :
    I.traceAddChar y (Ideal.Quotient.mk I a) =
      (numberFieldTraceChar K ((y : K) * algebraMap (𝓞 K) K a) : ℂ) := by
  rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.quotientAddGroupMk_eq_mk]
  rw [traceAddChar, MonoidHom.coe_compAddChar]
  -- The lift uses the additive-group quotient, definitionally the same as the ideal quotient.
  erw [Function.comp_apply, AddChar.toAddMonoidHomEquiv_symm_apply, QuotientAddGroup.lift_mk']
  -- `Circle.coeHom` is the coercion to `ℂ`, and `Additive.toMul` removes only a type tag.
  rfl

/-- The zero parameter gives the trivial residue character. -/
@[simp]
theorem traceAddChar_zero : I.traceAddChar 0 = 1 := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp

/-- Adding parameters multiplies the residue characters. -/
@[simp]
theorem traceAddChar_add
    (y z : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    I.traceAddChar (y + z) = I.traceAddChar y * I.traceAddChar z := by
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [traceAddChar_mk, Submodule.coe_add, add_mul, AddChar.map_add_eq_mul,
    Circle.coe_mul, mul_apply]

/-- Negating the parameter inverts the residue character. -/
@[simp]
theorem traceAddChar_neg
    (y : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    I.traceAddChar (-y) = (I.traceAddChar y)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← traceAddChar_add, neg_add_cancel, traceAddChar_zero]

/-- Subtracting parameters divides the residue characters. -/
@[simp]
theorem traceAddChar_sub
    (y z : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    I.traceAddChar (y - z) = I.traceAddChar y / I.traceAddChar z := by
  rw [sub_eq_add_neg, traceAddChar_add, traceAddChar_neg, div_eq_mul_inv]

/-- The phase of the trace character has absolute value one at every residue class. -/
@[simp]
theorem norm_traceAddChar
    (y : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
    (x : 𝓞 K ⧸ I) :
    ‖I.traceAddChar y x‖ = 1 := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [traceAddChar_mk, Circle.norm_coe]

/-- Two parameters define the same residue character exactly when their difference lies in
the inverse different. -/
theorem traceAddChar_eq_iff
    (y z : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    I.traceAddChar y = I.traceAddChar z ↔
      (y : K) - (z : K) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [← div_eq_one, ← traceAddChar_sub, AddChar.eq_one_iff, Ideal.Quotient.mk_surjective.forall,
    ← FractionalIdeal.coeIdeal_top (𝓞 K)⁰,
    mem_dual_iff_forall_numberFieldTraceChar_eq_one ⊤ top_ne_bot]
  simp only [traceAddChar_mk, Circle.coe_eq_one, Submodule.coe_sub, Submodule.mem_top,
    forall_true_left]

/-- Characterization of the trivial trace character: its parameter is in the inverse different. -/
@[simp]
theorem traceAddChar_eq_one_iff
    (y : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    I.traceAddChar y = 1 ↔
      (y : K) ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  simpa only [traceAddChar_zero, Submodule.coe_zero, sub_zero] using I.traceAddChar_eq_iff y 0

/-- Multiplying the parameter by an algebraic integer multiplies the residue argument by
its class. This is the change of phase used to reindex number-field Gauss sums. -/
theorem traceAddChar_smul
    (y : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
    (a : 𝓞 K) :
    I.traceAddChar (a • y) = (I.traceAddChar y).mulShift (Ideal.Quotient.mk I a) := by
  ext x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [AddChar.mulShift_apply, ← map_mul, traceAddChar_mk, traceAddChar_mk]
  simp only [Submodule.coe_smul, Algebra.smul_def, map_mul]
  congr 2
  ring

/-! ### Primitivity of the trace character -/

/-- **Primitivity of the trace character.** The trace character of `y` is primitive exactly when
every `z ∈ 𝓞 K` with `z y` in the inverse different `𝔡⁻¹ = (𝓞 K)^∨` lies in `I`. -/
theorem isPrimitive_traceAddChar_iff
    (y : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)) :
    (I.traceAddChar y).IsPrimitive ↔
      ∀ z : 𝓞 K, (z : K) * y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) →
        z ∈ I := by
  -- The shift by the class of `z` is the trace character of `z • y = z y`.
  have hshift (z : 𝓞 K) : (I.traceAddChar y).mulShift (Ideal.Quotient.mk I z) = 1 ↔
      (z : K) * y ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [← traceAddChar_smul, traceAddChar_eq_one_iff, Submodule.coe_smul, Algebra.smul_def]
  refine ⟨fun h z hz ↦ ?_, fun h x hx ↦ ?_⟩
  · by_contra hzI
    exact h (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]) ((hshift z).mpr hz)
  · obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ne, hshift]
    exact fun hz ↦ hx (Ideal.Quotient.eq_zero_iff_mem.mpr (h z hz))

variable {I} in
/-- **The trace character is primitive when `y I 𝔡` is prime to `I`**, `𝔡` the different of `K`:
if the integral ideal `y I 𝔡` and `I` generate the unit ideal, the trace character of `y` is a
primitive additive character of `𝓞 K ⧸ I`. -/
theorem isPrimitive_traceAddChar
    {y : (FractionalIdeal.dual ℤ ℚ (I : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)}
    (hy : FractionalIdeal.spanSingleton (𝓞 K)⁰ (y : K) * I *
      (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) + I = 1) :
    (traceAddChar I y).IsPrimitive := by
  rw [isPrimitive_traceAddChar_iff]
  intro z hz
  have hd : FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) *
      (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) = 1 := by
    rw [coeIdeal_differentIdeal ℤ ℚ,
      mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ one_ne_zero)]
  have hz1 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (z : K) ≤ 1 :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr ((FractionalIdeal.mem_one_iff _).mpr ⟨z, rfl⟩)
  have hzy : FractionalIdeal.spanSingleton (𝓞 K)⁰ ((z : K) * y) ≤
      FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr hz
  -- `(z) = (z) (y I 𝔡 + I) = (z y) 𝔡 I + (z) I ≤ 𝔡⁻¹ 𝔡 I + I = I`.
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ (z : K) ≤ I := by
    calc FractionalIdeal.spanSingleton (𝓞 K)⁰ (z : K)
        = FractionalIdeal.spanSingleton (𝓞 K)⁰ (z : K) *
          (FractionalIdeal.spanSingleton (𝓞 K)⁰ (y : K) * I *
            (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) + I) := by rw [hy, mul_one]
      _ = FractionalIdeal.spanSingleton (𝓞 K)⁰ ((z : K) * y) *
            (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) * I +
          FractionalIdeal.spanSingleton (𝓞 K)⁰ (z : K) * I := by
          rw [mul_add, map_mul]
          ring
      _ ≤ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) *
            (differentIdeal ℤ (𝓞 K) : FractionalIdeal (𝓞 K)⁰ K) * I + 1 * I := by
          gcongr
      _ = I := by rw [hd, one_mul, ← FractionalIdeal.coeIdeal_sup, sup_idem]
  obtain ⟨z', hz', hzz'⟩ :=
    (FractionalIdeal.mem_coeIdeal _).mp (hle (FractionalIdeal.mem_spanSingleton_self _ _))
  rwa [← RingOfIntegers.coe_injective hzz']

end Ideal
