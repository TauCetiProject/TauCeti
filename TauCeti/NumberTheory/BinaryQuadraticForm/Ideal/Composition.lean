/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Reflection
import Mathlib.Tactic.LinearCombination

/-!
# Dirichlet composition and the principal form

This file identifies the group law of the Picard group of a quadratic order with the classical
operations on primitive binary quadratic forms.

*Composition.* Two forms `f = (a, B, a'C)` and `g = (a', B, aC)` sharing the middle coefficient
`B` have Dirichlet composition `h = (aa', B, C)`, of the same discriminant `D = B² - 4aa'C`. Every
pair of united forms (`gcd(a, a', (b + b')/2) = 1`) is properly equivalent to a pair of this shape
(Cox, Lemma 3.2), and conversely a primitive `f` of this shape forces `gcd(a, a', B) = 1`.

All three ideals `aℤ + τℤ`, `a'ℤ + τℤ`, `aa'ℤ + τℤ` share the second generator `τ = (-B + √D)/2`,
and `τ² = -Bτ - aa'C`. For nonsquare `D` and primitive `f` the product of the first two ideals is
the third (`fractionalIdeal_mk_mul_fractionalIdeal_mk`): the products of
generators are `aa'`, `aτ`, `a'τ` and `τ²`, and `gcd(a, a', B) = 1` recovers `τ`. If `f` and `g`
are primitive so is `h` (`isPrimitive_mk_mul_of_isPrimitive`), and the Picard class of `h` is the
product of those of `f` and `g` (`picClass_mul_picClass_of_united`).

*The principal form.* The principal form of discriminant `D ≡ 0, 1 mod 4` is
`x² + δxy + ((δ - D)/4)y²` with `δ = D mod 2` (`principalForm`). Every primitive form with leading
coefficient `1` has the unit ideal and so the trivial Picard class (`picClass_eq_one_of_a_eq_one`).

On proper classes of primitive positive definite forms of discriminant `-n` these give the group
law of `Pic(O_{-n})` through the bijection `posDefProperClassToPic`: the class of a Dirichlet
composition maps to the product (`posDefProperClassToPic_mk_mul_of_united`), the opposite form to
the inverse (`posDefProperClassToPic_mk_eq_inv_of_eq_reflected`), and a class maps to `1` exactly
when it is the class of the principal form (`posDefProperClassToPic_mk_eq_one_iff`).

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §3, Lemma 3.2 and the definition of Dirichlet
  composition, and §7, Theorem 7.7.
-/

public section

open QuadraticAlgebra FractionalIdeal MulAction
open scoped MatrixGroups nonZeroDivisors

namespace TauCeti.BinaryQuadraticForm

open GlobalNumberFields

/-! ### Dirichlet composition of united forms -/

section Composition

variable {D : ℤ} {a a' B C : ℤ}

/-- The forms `(a, B, a'C)` and `(aa', B, C)` have the same discriminant `B² - 4aa'C`. -/
theorem discrim_mk_mul_left (a a' B C : ℤ) :
    (⟨a, B, a' * C⟩ : BinaryQuadraticForm ℤ).discrim =
      (⟨a * a', B, C⟩ : BinaryQuadraticForm ℤ).discrim := by
  simp only [discrim_def, discrim]
  ring

/-- The forms `(a', B, aC)` and `(aa', B, C)` have the same discriminant `B² - 4aa'C`. -/
theorem discrim_mk_mul_right (a a' B C : ℤ) :
    (⟨a', B, a * C⟩ : BinaryQuadraticForm ℤ).discrim =
      (⟨a * a', B, C⟩ : BinaryQuadraticForm ℤ).discrim := by
  simp only [discrim_def, discrim]
  ring

/-- **The Dirichlet composition of primitive united forms is primitive.** If `(a, B, a'C)` and
`(a', B, aC)` are primitive, then so is `(aa', B, C)`. -/
theorem isPrimitive_mk_mul_of_isPrimitive
    (hf : (⟨a, B, a' * C⟩ : BinaryQuadraticForm ℤ).IsPrimitive)
    (hg : (⟨a', B, a * C⟩ : BinaryQuadraticForm ℤ).IsPrimitive) :
    (⟨a * a', B, C⟩ : BinaryQuadraticForm ℤ).IsPrimitive := by
  obtain ⟨u, v, w, huvw⟩ := hf.exists_linearCombination_eq_one
  obtain ⟨u', v', w', huvw'⟩ := hg.exists_linearCombination_eq_one
  -- every monomial of the product of the two Bézout relations is a multiple of `aa'`, `B` or `C`
  refine isPrimitive_of_linearCombination_eq_one _ (u * u' + w * w' * C ^ 2)
    (u * v' * a + v * u' * a' + v * v' * B + v * w' * a * C + w * v' * a' * C)
    (u * w' * a ^ 2 + w * u' * a' ^ 2) ?_
  linear_combination (u' * a' + v' * B + w' * (a * C)) * huvw + huvw'

variable [Fact (¬ IsSquare D)]

/-- **Dirichlet composition multiplies form ideals.** For a nonsquare discriminant
`D = B² - 4aa'C` and a primitive form `(a, B, a'C)`, the ideals of `(a, B, a'C)` and `(a', B, aC)`
multiply to the ideal of `(aa', B, C)`:
`(aℤ + τℤ)(a'ℤ + τℤ) = aa'ℤ + τℤ` with `τ = (-B + √D)/2`. -/
theorem fractionalIdeal_mk_mul_fractionalIdeal_mk
    (hD : (⟨a * a', B, C⟩ : BinaryQuadraticForm ℤ).discrim = D)
    (hprim : (⟨a, B, a' * C⟩ : BinaryQuadraticForm ℤ).IsPrimitive) :
    (⟨a, B, a' * C⟩ : BinaryQuadraticForm ℤ).fractionalIdeal D
        ((discrim_mk_mul_left a a' B C).trans hD) *
      (⟨a', B, a * C⟩ : BinaryQuadraticForm ℤ).fractionalIdeal D
        ((discrim_mk_mul_right a a' B C).trans hD) =
      (⟨a * a', B, C⟩ : BinaryQuadraticForm ℤ).fractionalIdeal D hD := by
  set f : BinaryQuadraticForm ℤ := ⟨a, B, a' * C⟩
  set g : BinaryQuadraticForm ℤ := ⟨a', B, a * C⟩
  set h : BinaryQuadraticForm ℤ := ⟨a * a', B, C⟩
  have hf : f.discrim = D := (discrim_mk_mul_left a a' B C).trans hD
  have hg : g.discrim = D := (discrim_mk_mul_right a a' B C).trans hD
  -- The three forms share the second ideal generator `τ`, and `τ² = -Bτ - aa'C`.
  have hτf : f.idealGenerator D = h.idealGenerator D := by ext <;> simp [f, h]
  have hτg : g.idealGenerator D = h.idealGenerator D := by ext <;> simp [g, h]
  have hτ := idealGenerator_mul_self h D hD
  simp only [h, zsmul_eq_mul, Int.cast_mul, Int.cast_neg, mul_one] at hτ
  apply le_antisymm
  · -- Each product of generators is an integral combination of `aa'` and `τ`.
    rw [mul_le]
    intro i hi j hj
    obtain ⟨m, n, rfl⟩ := (mem_fractionalIdeal_iff f D hf i).mp hi
    obtain ⟨m', n', rfl⟩ := (mem_fractionalIdeal_iff g D hg j).mp hj
    refine (mem_fractionalIdeal_iff h D hD _).mpr
      ⟨m * m' - n * n' * C, m * n' * a + n * m' * a' - n * n' * B, ?_⟩
    rw [hτf, hτg]
    simp only [f, g, h, zsmul_eq_mul, Int.cast_mul, Int.cast_sub, Int.cast_add]
    linear_combination (-(n : QuadraticAlgebra ℚ (D : ℚ) 0) * n') * hτ
  · -- Conversely `aa' = a · a'` and `τ = u (aτ) + v (τa') - w (τ² + C aa')` for a Bézout
    -- relation `u a + v a' + w B = 1` extracted from the primitivity of `(a, B, a'C)`.
    obtain ⟨u, w, v, huvw⟩ := hprim.exists_linearCombination_eq_one
    have h1 : (u : QuadraticAlgebra ℚ (D : ℚ) 0) * a + v * C * a' + w * B = 1 := by
      have : (u : QuadraticAlgebra ℚ (D : ℚ) 0) * a + w * B + v * (a' * C) = 1 := by
        exact_mod_cast huvw
      linear_combination this
    have hα : (a : QuadraticAlgebra ℚ (D : ℚ) 0) ∈ f.fractionalIdeal D hf :=
      a_mem_fractionalIdeal f D hf
    have hα' : (a' : QuadraticAlgebra ℚ (D : ℚ) 0) ∈ g.fractionalIdeal D hg :=
      a_mem_fractionalIdeal g D hg
    have hβ : h.idealGenerator D ∈ f.fractionalIdeal D hf :=
      hτf ▸ idealGenerator_mem_fractionalIdeal f D hf
    have hβ' : h.idealGenerator D ∈ g.fractionalIdeal D hg :=
      hτg ▸ idealGenerator_mem_fractionalIdeal g D hg
    have hαα' := mem_coe.mpr (mul_mem_mul hα hα')
    intro z hz
    obtain ⟨m, n, rfl⟩ := (mem_fractionalIdeal_iff h D hD z).mp hz
    have key : m • ((h.a : ℤ) : QuadraticAlgebra ℚ (D : ℚ) 0) + n • h.idealGenerator D =
        m • ((a : QuadraticAlgebra ℚ (D : ℚ) 0) * a') +
          n • (u • ((a : QuadraticAlgebra ℚ (D : ℚ) 0) * h.idealGenerator D) +
            (v * C) • (h.idealGenerator D * a') -
            w • (h.idealGenerator D * h.idealGenerator D +
              C • ((a : QuadraticAlgebra ℚ (D : ℚ) 0) * a'))) := by
      simp only [h, zsmul_eq_mul, Int.cast_mul]
      linear_combination (n : QuadraticAlgebra ℚ (D : ℚ) 0) * (-h.idealGenerator D * h1 + w * hτ)
    rw [key, ← mem_coe]
    exact add_mem (zsmul_mem hαα' _) (zsmul_mem (sub_mem
      (add_mem (zsmul_mem (mem_coe.mpr (mul_mem_mul hα hβ')) _)
        (zsmul_mem (mem_coe.mpr (mul_mem_mul hβ hα')) _))
      (zsmul_mem (add_mem (mem_coe.mpr (mul_mem_mul hβ hβ')) (zsmul_mem hαα' _)) _)) _)

end Composition

/-! ### Picard classes -/

section Pic

variable (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1) [Fact (¬ IsSquare D)]

/-- **Dirichlet composition is the Picard group law.** If primitive forms `f = (a, B, a'C)` and
`g = (a', B, aC)` of nonsquare discriminant `D` have Dirichlet composition `h = (aa', B, C)`, then
the Picard class of `h` is the product of those of `f` and `g`. -/
theorem picClass_mul_picClass_of_united {a a' B C : ℤ} {f g h : primitiveForms D}
    (hf : (f : BinaryQuadraticForm ℤ) = ⟨a, B, a' * C⟩)
    (hg : (g : BinaryQuadraticForm ℤ) = ⟨a', B, a * C⟩)
    (hh : (h : BinaryQuadraticForm ℤ) = ⟨a * a', B, C⟩) :
    picClass D hD f * picClass D hD g = picClass D hD h := by
  obtain ⟨f, hfm⟩ := f
  obtain ⟨g, hgm⟩ := g
  obtain ⟨h, hhm⟩ := h
  simp only at hf hg hh
  subst hf hg hh
  obtain ⟨hfD, hfp⟩ := (mem_primitiveForms D _).mp hfm
  obtain ⟨hhD, -⟩ := (mem_primitiveForms D _).mp hhm
  simp only [picClass_def, ← map_mul]
  congr 1
  apply Units.ext
  rw [Units.val_mul, coe_invertibleFractionalIdeal, coe_invertibleFractionalIdeal,
    coe_invertibleFractionalIdeal]
  exact fractionalIdeal_mk_mul_fractionalIdeal_mk hhD hfp

/-- The ideal of a form with leading coefficient `1` is the unit ideal. -/
theorem fractionalIdeal_eq_one_of_a_eq_one {f : BinaryQuadraticForm ℤ} (hf : f.discrim = D)
    (ha : f.a = 1) : f.fractionalIdeal D hf = 1 :=
  le_antisymm (fractionalIdeal_le_one f D hf) <| FractionalIdeal.one_le.mpr <|
    (mem_fractionalIdeal_iff f D hf _).mpr ⟨1, 0, by simp [ha]⟩

/-- **A form with leading coefficient `1` has trivial Picard class.** -/
theorem picClass_eq_one_of_a_eq_one {f : primitiveForms D}
    (ha : (f : BinaryQuadraticForm ℤ).a = 1) : picClass D hD f = 1 := by
  have h1 : (f : BinaryQuadraticForm ℤ).invertibleFractionalIdeal D
      ((mem_primitiveForms D f).mp f.2).1 ((mem_primitiveForms D f).mp f.2).2 = 1 :=
    Units.ext (by
      rw [coe_invertibleFractionalIdeal, Units.val_one, fractionalIdeal_eq_one_of_a_eq_one D _ ha])
  rw [picClass_def, h1, map_one]

end Pic

/-! ### The principal form -/

section Principal

/-- **The principal form** of discriminant `D`, `x² + δxy + ((δ - D)/4)y²` with `δ = D mod 2`.
For `D ≡ 0, 1 mod 4` it has discriminant `D` (`discrim_principalForm`). -/
def principalForm (D : ℤ) : BinaryQuadraticForm ℤ :=
  ⟨1, D % 2, (D % 2 - D) / 4⟩

/-- The leading coefficient of the principal form is `1`. -/
@[simp] theorem principalForm_a (D : ℤ) : (principalForm D).a = 1 := (rfl)

/-- The middle coefficient of the principal form is `D mod 2`. -/
@[simp] theorem principalForm_b (D : ℤ) : (principalForm D).b = D % 2 := (rfl)

/-- The last coefficient of the principal form is `(D mod 2 - D) / 4`. -/
@[simp] theorem principalForm_c (D : ℤ) : (principalForm D).c = (D % 2 - D) / 4 := (rfl)

/-- The principal form of discriminant `D ≡ 0, 1 mod 4` has discriminant `D`. -/
theorem discrim_principalForm {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) :
    (principalForm D).discrim = D := by
  have h4 : 4 * ((D % 2 - D) / 4) = D % 2 - D :=
    Int.mul_ediv_cancel' (Int.dvd_iff_emod_eq_zero.mpr (by omega))
  have hsq : D % 2 * (D % 2) = D % 2 := by
    rcases Int.emod_two_eq_zero_or_one D with h | h <;> rw [h] <;> norm_num
  rw [discrim_def, discrim, principalForm_a, principalForm_b, principalForm_c]
  linear_combination hsq - h4

/-- The principal form is primitive. -/
theorem isPrimitive_principalForm (D : ℤ) : (principalForm D).IsPrimitive :=
  isPrimitive_of_linearCombination_eq_one _ 1 0 0 (by simp)

/-- The principal form is a primitive form of discriminant `D ≡ 0, 1 mod 4`. -/
theorem principalForm_mem_primitiveForms {D : ℤ} (hD : D % 4 = 0 ∨ D % 4 = 1) :
    principalForm D ∈ primitiveForms D :=
  (mem_primitiveForms D _).mpr ⟨discrim_principalForm hD, isPrimitive_principalForm D⟩

/-- **The principal form has trivial Picard class.** -/
@[simp] theorem picClass_principalForm (D : ℤ) (hD : D % 4 = 0 ∨ D % 4 = 1)
    [Fact (¬ IsSquare D)] :
    picClass D hD ⟨principalForm D, principalForm_mem_primitiveForms hD⟩ = 1 :=
  picClass_eq_one_of_a_eq_one D hD (principalForm_a D)

end Principal

/-! ### The group law on positive definite proper classes -/

section PosDef

variable (n : ℕ) [NeZero n] (hn : (-n : ℤ) % 4 = 0 ∨ (-n : ℤ) % 4 = 1)

/-- **Dirichlet composition of positive definite classes.** If primitive positive definite forms
`f = (a, B, a'C)` and `g = (a', B, aC)` of discriminant `-n` have Dirichlet composition
`h = (aa', B, C)`, then the Picard class of the proper class of `h` is the product of those of `f`
and `g`. -/
theorem posDefProperClassToPic_mk_mul_of_united {a a' B C : ℤ}
    {f g h : ↥(posDef n ⊓ primitiveForms (-n))}
    (hf : (f : BinaryQuadraticForm ℤ) = ⟨a, B, a' * C⟩)
    (hg : (g : BinaryQuadraticForm ℤ) = ⟨a', B, a * C⟩)
    (hh : (h : BinaryQuadraticForm ℤ) = ⟨a * a', B, C⟩) :
    posDefProperClassToPic n hn (Quotient.mk _ f) * posDefProperClassToPic n hn (Quotient.mk _ g) =
      posDefProperClassToPic n hn (Quotient.mk _ h) := by
  simp only [posDefProperClassToPic_mk]
  exact picClass_mul_picClass_of_united (-n) hn hf hg hh

/-- **The opposite form represents the inverse positive definite class.** -/
theorem posDefProperClassToPic_mk_eq_inv_of_eq_reflected
    {f g : ↥(posDef n ⊓ primitiveForms (-n))}
    (hg : (g : BinaryQuadraticForm ℤ) = (f : BinaryQuadraticForm ℤ).reflected) :
    posDefProperClassToPic n hn (Quotient.mk _ g) =
      (posDefProperClassToPic n hn (Quotient.mk _ f))⁻¹ := by
  obtain ⟨hfD, -, hfp⟩ := (mem_posDef_inf_primitiveForms n).mp f.2
  obtain ⟨g, hgm⟩ := g
  simp only at hg
  subst hg
  simp only [posDefProperClassToPic_mk]
  exact picClass_reflected hn hfD hfp

include hn in
/-- The principal form of discriminant `-n` is primitive positive definite. -/
theorem principalForm_mem_posDef_inf_primitiveForms :
    principalForm (-n) ∈ posDef n ⊓ primitiveForms (-n) :=
  (mem_posDef_inf_primitiveForms n).mpr
    ⟨discrim_principalForm hn, by simp, isPrimitive_principalForm _⟩

/-- **The trivial Picard class is the class of the principal form.** A primitive positive definite
form of discriminant `-n` has trivial Picard class exactly when it is properly equivalent to the
principal form. -/
theorem posDefProperClassToPic_mk_eq_one_iff (f : ↥(posDef n ⊓ primitiveForms (-n))) :
    posDefProperClassToPic n hn (Quotient.mk _ f) = 1 ↔
      ∃ γ : SL(2, ℤ), γ • (f : BinaryQuadraticForm ℤ) = principalForm (-n) := by
  obtain ⟨-, hfa, -⟩ := (mem_posDef_inf_primitiveForms n).mp f.2
  have hneg : (-n : ℤ) < 0 := by simpa using NeZero.pos n
  rw [posDefProperClassToPic_mk, ← picClass_principalForm (-n) hn,
    picClass_eq_picClass_iff_of_neg (-n) hn hneg hfa (by simp)]
  simp only [Subtype.ext_iff, SubMulAction.val_smul]

end PosDef

end TauCeti.BinaryQuadraticForm
