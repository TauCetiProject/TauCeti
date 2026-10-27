/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.BinaryQuadraticForm.Ideal.Class
import Mathlib.Tactic.LinearCombination

/-!
# Dirichlet composition and the principal form in the Picard group

This file computes the Picard product of classes of primitive binary quadratic forms presented
in Dirichlet shape, and the identity via the principal form.

*Composition.* Two forms `f = (a, B, a'C)` and `g = (a', B, aC)` sharing the middle coefficient
`B` have Dirichlet composition `h = (aa', B, C)`, of the same discriminant `D = B² - 4aa'C`. A
primitive `f` of this shape forces `gcd(a, a', B) = 1`. Every pair of united forms is properly
equivalent to a pair of this shape (Cox, Lemma 3.2); that reduction is cited for context and is
not formalized here.

All three ideals `aℤ + τℤ`, `a'ℤ + τℤ`, `aa'ℤ + τℤ` share the second generator `τ = (-B + √D)/2`,
and `τ² = -Bτ - aa'C`. For nonsquare `D` and primitive `f` the product of the first two ideals is
the third (`fractionalIdeal_mk_mul_fractionalIdeal_mk`): the products of
generators are `aa'`, `aτ`, `a'τ` and `τ²`, and `gcd(a, a', B) = 1` recovers `τ`. Hence the
Picard class of `h` is the product of those of `f` and `g` (`picClass_mul_picClass_of_united`).

*The principal form.* The principal form (`principalForm`) has leading coefficient `1`, hence
the unit ideal and the trivial Picard class (`picClass_principalForm`).

On proper classes of primitive positive definite forms of discriminant `-n`, through the
bijection `posDefProperClassToPic`, the class of a Dirichlet composition maps to the product
(`posDefProperClassToPic_mk_mul_of_united`), and a class maps to `1` exactly when it is the class
of the principal form (`posDefProperClassToPic_eq_one_iff`). The inverse via the opposite form is
`posDefProperClassToPic_mk_eq_inv_of_eq_reflected`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §3, Lemma 3.2 and the definition of Dirichlet
  composition, and §7, Theorem 7.7.
-/

public section

open QuadraticAlgebra FractionalIdeal MulAction
open scoped MatrixGroups nonZeroDivisors

namespace TauCeti.BinaryQuadraticForm

open GlobalNumberFields

/-! ### Dirichlet composition of form ideals -/

section Composition

variable {D : ℤ} {a a' B C : ℤ} [Fact (¬ IsSquare D)]

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
  · -- The products of generators are `aa'`, `aτ`, `τa'` and `τ² = -Bτ - aa'C`.
    rw [fractionalIdeal_mul_fractionalIdeal_le_iff, hτf, hτg]
    simp only [mem_fractionalIdeal_iff, h, zsmul_eq_mul, Int.cast_mul]
    exact ⟨⟨1, 0, by ring⟩, ⟨0, a, by ring⟩, ⟨0, a', by ring⟩,
      ⟨-C, -B, by push_cast; linear_combination -hτ⟩⟩
  · -- Conversely `aa' = a · a'` and `τ = u (aτ) + v (τa') - w (τ² + C aa')` for a Bézout
    -- relation `u a + v a' + w B = 1` extracted from the primitivity of `(a, B, a'C)`.
    obtain ⟨u, w, v, huvw⟩ := hprim.exists_linearCombination_eq_one
    have h1 : (u : QuadraticAlgebra ℚ (D : ℚ) 0) * a + v * C * a' + w * B = 1 := by
      have : (u : QuadraticAlgebra ℚ (D : ℚ) 0) * a + w * B + v * (a' * C) = 1 := by
        exact_mod_cast huvw
      linear_combination this
    have hα := a_mem_fractionalIdeal f D hf
    have hα' := a_mem_fractionalIdeal g D hg
    have hβ := hτf ▸ idealGenerator_mem_fractionalIdeal f D hf
    have hβ' := hτg ▸ idealGenerator_mem_fractionalIdeal g D hg
    have hmul := fun {x y : QuadraticAlgebra ℚ (D : ℚ) 0} (hx : x ∈ f.fractionalIdeal D hf)
        (hy : y ∈ g.fractionalIdeal D hg) ↦ mem_coe.mpr (mul_mem_mul hx hy)
    have key : h.idealGenerator D =
        u • ((a : QuadraticAlgebra ℚ (D : ℚ) 0) * h.idealGenerator D) +
          (v * C) • (h.idealGenerator D * a') -
          w • (h.idealGenerator D * h.idealGenerator D +
            C • ((a : QuadraticAlgebra ℚ (D : ℚ) 0) * a')) := by
      simp only [zsmul_eq_mul, Int.cast_mul]
      linear_combination -h.idealGenerator D * h1 + (w : QuadraticAlgebra ℚ (D : ℚ) 0) * hτ
    rw [fractionalIdeal_le_iff, ← mem_coe, ← mem_coe, key]
    refine ⟨by simpa [f, g, h] using hmul hα hα', sub_mem
      (add_mem (zsmul_mem (hmul hα hβ') _) (zsmul_mem (hmul hβ hα') _))
      (zsmul_mem (add_mem (hmul hβ hβ') (zsmul_mem (hmul hα hα') _)) _)⟩

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

/-- **The principal form has trivial Picard class.** -/
@[simp] theorem picClass_principalForm :
    picClass D hD ⟨principalForm D, principalForm_mem_primitiveForms hD⟩ = 1 :=
  picClass_eq_one_of_isUnit_a D hD (by simp)

end Pic

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

/-- **The principal proper class has trivial Picard class.** -/
theorem posDefProperClassToPic_principalForm :
    posDefProperClassToPic n hn
      (Quotient.mk _ ⟨principalForm (-n), principalForm_mem_posDef_inf_primitiveForms n hn⟩) =
        1 := by
  rw [posDefProperClassToPic_mk]
  exact picClass_principalForm (-n) hn

/-- **The trivial Picard class is the class of the principal form.** A proper class of primitive
positive definite forms of discriminant `-n` has trivial Picard class exactly when it is the class
of the principal form. -/
theorem posDefProperClassToPic_eq_one_iff (q : PosDefProperClass n) :
    posDefProperClassToPic n hn q = 1 ↔
      q = Quotient.mk _ ⟨principalForm (-n), principalForm_mem_posDef_inf_primitiveForms n hn⟩ := by
  rw [← posDefProperClassToPic_principalForm n hn, (posDefProperClassToPic_injective n hn).eq_iff]

end PosDef

end TauCeti.BinaryQuadraticForm
