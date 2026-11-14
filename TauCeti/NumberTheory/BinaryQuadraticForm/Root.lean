/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import TauCeti.NumberTheory.BinaryQuadraticForm.Basic
public import TauCeti.NumberTheory.BinaryQuadraticForm.Reflection
import TauCeti.Analysis.Complex.UpperHalfPlane.MoebiusAction

/-!
# The root of a positive definite binary quadratic form

A positive definite integral form `f = a x² + b x y + c y²` of discriminant `-D < 0` has exactly
one root `τ` in the upper half-plane, `τ = (-b + i √D) / (2 a)`: the quadratic `a z² + b z + c` has
the two conjugate roots `(-b ± i √D) / (2 a)`, and `a > 0` puts the one with `+` in `ℍ`. This file
defines `τ` as `TauCeti.BinaryQuadraticForm.root` and shows that it is compatible with the actions
of `SL(2, ℤ)`: `root (γ • f) = γ • root f`, where `γ • f = f ∘ γ⁻¹` is the action of
`TauCeti.BinaryQuadraticForm.Basic` and `γ • τ` is the Möbius action. Since `root` is moreover
injective for fixed `D`, it identifies the stabiliser of `f` with that of `τ`.

This is how the reduction theory of positive definite forms is transported to the upper half-plane:
`f` is reduced exactly when `τ` lies in the standard fundamental domain (up to the boundary
identifications), and the automorphism group of `f` is the stabiliser of `τ`, of order `4` when `τ`
lies in the `SL(2, ℤ)`-orbit of `i`, `6` when it lies in that of `ρ`, and `2` otherwise
(`TauCeti.ModularGroup.card_stabilizer_of_orbit_eq_I`, `card_stabilizer_of_orbit_eq_ρ` and
`card_stabilizer_eq_two_of_orbit_ne_I_of_orbit_ne_ρ`).

## Main definitions

* `TauCeti.BinaryQuadraticForm.root`: the root `(-b + i √D) / (2 a)` in `ℍ` of a form in
  `posDef D`.

## Main results

* `TauCeti.BinaryQuadraticForm.eq_root_iff`: `root f` is the only point of `ℍ` at which
  `a z² + b z + c` vanishes.
* `TauCeti.BinaryQuadraticForm.discrim_neg_of_quadratic_upperHalfPlane`: an integral quadratic
  relation `a τ² + b τ + c = 0` satisfied by `τ ∈ ℍ` with `a ≠ 0` has negative discriminant.
* `TauCeti.BinaryQuadraticForm.root_smul`: `root (γ • f) = γ • root f`.
* `TauCeti.BinaryQuadraticForm.root_injective`: for fixed `D`, a form is determined by its root.
* `TauCeti.BinaryQuadraticForm.normSq_root`: `|root f|² = c / a`.
* `TauCeti.BinaryQuadraticForm.conj_denom_mul_denom_root`:
  `conj (denom γ (root f)) * denom γ (root f) = (γ • f).a / f.a`.
* `TauCeti.BinaryQuadraticForm.stabilizer_root`: the stabiliser of `root f` in `SL(2, ℤ)` is
  the stabiliser of `f`.
* `TauCeti.BinaryQuadraticForm.root_of_eq_reflected`: the root of the reflected form
  `a x² - b x y + c y²` is the reflection `-conj τ` of the root `τ` of `a x² + b x y + c y²`.
* `TauCeti.BinaryQuadraticForm.root_eq_root_of_eq_primPart`: a positive definite form and its
  primitive part have the same root in `ℍ`.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, Graduate Texts in Mathematics
  138, Springer, 1993, §5.3.
* D. Zagier, *Zetafunktionen und quadratische Körper*, Springer, 1981, §8.
-/

public section

open Complex ComplexConjugate
open UpperHalfPlane hiding I
open scoped MatrixGroups

namespace TauCeti

namespace BinaryQuadraticForm

variable {D : ℕ} [NeZero D]

/-- The root `(-b + i √D) / (2 a)` in the upper half-plane of a positive definite form
`a x² + b x y + c y²` of discriminant `-D`. -/
noncomputable def root (f : posDef D) : ℍ :=
  ⟨⟨-(f.1.b : ℝ) / (2 * f.1.a), √(D : ℝ) / (2 * f.1.a)⟩,
    by have := NeZero.pos D; have := (mem_posDef.1 f.2).2; positivity⟩

/-- The real part of the root of `a x² + b x y + c y²` is `-b / (2 a)`. -/
@[simp]
theorem re_root (f : posDef D) : (root f).re = -(f.1.b : ℝ) / (2 * f.1.a) :=
  (rfl)

/-- The imaginary part of the root of `a x² + b x y + c y²` is `√D / (2 a)`. -/
@[simp]
theorem im_root (f : posDef D) : (root f).im = √(D : ℝ) / (2 * f.1.a) :=
  (rfl)

/-- As a complex number, the root of `a x² + b x y + c y²` is `(-b + i √D) / (2 a)`. -/
theorem coe_root (f : posDef D) : (root f : ℂ) = (-(f.1.b : ℂ) + √(D : ℝ) * I) / (2 * f.1.a) := by
  simp [← (root f).re_add_im, add_div, mul_div_right_comm]

/-- `root f` is the only point of the upper half-plane at which `a z² + b z + c` vanishes: the
other root `(-b - i √D) / (2 a)` lies in the lower half-plane. -/
theorem eq_root_iff (f : posDef D) (z : ℍ) :
    z = root f ↔ (f.1.a : ℂ) * z ^ 2 + f.1.b * z + f.1.c = 0 := by
  obtain ⟨hD, ha⟩ := mem_posDef.1 f.2
  -- Over `ℂ` the discriminant `-D` of a form in `posDef D` is the square of `i √D`.
  have hd : discrim (f.1.a : ℂ) f.1.b f.1.c = (√(D : ℝ) * I) * (√(D : ℝ) * I) := by
    rw [mul_mul_mul_comm, ← ofReal_mul, Real.mul_self_sqrt D.cast_nonneg]
    simpa [discrim, discrim_def] using congrArg (Int.cast : ℤ → ℂ) hD
  rw [sq, quadratic_eq_zero_iff (mod_cast ha.ne') hd, ← coe_root, UpperHalfPlane.ext_iff,
    or_iff_left fun h ↦ z.coe_im_pos.not_ge ?_]
  simp [h, div_im, div_nonpos_iff, ha.le, mul_nonneg]

/-- An integral quadratic relation `a τ² + b τ + c = 0` satisfied by `τ ∈ ℍ` with `a ≠ 0` has
strictly negative discriminant `b² - 4 a c < 0`. -/
theorem discrim_neg_of_quadratic_upperHalfPlane {τ : ℍ} {a b c : ℤ} (ha : a ≠ 0)
    (hrel : (a : ℂ) * (τ : ℂ) ^ 2 + b * (τ : ℂ) + c = 0) :
    (⟨a, b, c⟩ : BinaryQuadraticForm ℤ).discrim < 0 := by
  have him := congrArg Complex.im hrel
  have hre := congrArg Complex.re hrel
  simp only [sq, add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, coe_re, coe_im,
    add_re, mul_re, sub_zero, zero_im, zero_re] at him hre
  have him' : (2 * (a : ℝ) * τ.re + b) * τ.im = 0 := by linear_combination him
  have h2ax : 2 * (a : ℝ) * τ.re + b = 0 := (mul_eq_zero.mp him').resolve_right τ.im_ne_zero
  have hdiscR : ((b ^ 2 - 4 * a * c : ℤ) : ℝ) = -(4 * (a : ℝ) ^ 2 * τ.im ^ 2) := by
    push_cast
    linear_combination (2 * (a : ℝ) * τ.re + b) * h2ax - 4 * (a : ℝ) * hre
  have : (a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hnegR : ((b ^ 2 - 4 * a * c : ℤ) : ℝ) < 0 := by
    rw [hdiscR]
    have hpos : 0 < 4 * (a : ℝ) ^ 2 * τ.im ^ 2 := by positivity
    linarith
  rw [discrim_def, discrim]
  exact_mod_cast hnegR

/-- The root map is `SL(2, ℤ)`-equivariant: `root (γ • f) = γ • root f`, with the action
`γ • f = f ∘ γ⁻¹` on forms and the Möbius action on `ℍ`. -/
@[simp]
theorem root_smul (γ : SL(2, ℤ)) (f : posDef D) : root (γ • f) = γ • root f := by
  have hden : (γ 1 0 : ℂ) * root f + γ 1 1 ≠ 0 := denom_ne_zero γ (root f)
  rw [eq_comm, eq_root_iff]
  push_cast [coe_specialLinearGroup_apply, smul_a, smul_b, smul_c, eq_intCast]
  -- `(γ • f)(γ • τ, 1) (r τ + s)² = (det γ)² f(τ, 1)` for `γ = !![p, q; r, s]` and `τ = root f`
  grind [(eq_root_iff f _).1 rfl]

/-- For fixed `D`, a positive definite form is determined by its root. -/
theorem root_injective : Function.Injective (root (D := D)) := by
  rintro ⟨⟨a, b, c⟩, hf⟩ ⟨⟨a', b', c'⟩, hg⟩ h
  obtain ⟨hdf, ha : 0 < a⟩ := mem_posDef.1 hf
  obtain ⟨hdg, -⟩ := mem_posDef.1 hg
  -- the imaginary part `√D / (2 a)` of the root gives `a`
  obtain rfl : a = a' := by simpa [div_eq_mul_inv, NeZero.ne] using congrArg UpperHalfPlane.im h
  -- the real part `-b / (2 a)` then gives `b`
  obtain rfl : b = b' := by simpa [ha.ne'] using congrArg UpperHalfPlane.re h
  -- and the discriminant `b² - 4 a c = -D` gives `c`
  obtain rfl : c = c' := by simpa [discrim_def, discrim, ha.ne'] using hdf.trans hdg.symm
  rfl

/-- The squared absolute value of the root of `a x² + b x y + c y²` is `c / a`. -/
@[simp]
theorem normSq_root (f : posDef D) : Complex.normSq (root f) = f.1.c / f.1.a := by
  obtain ⟨hdf, hfa⟩ := mem_posDef.1 f.2
  have hD : (f.1.b : ℝ) ^ 2 - 4 * f.1.a * f.1.c = -D := mod_cast hdf
  rw [Complex.normSq_apply, coe_re, coe_im, re_root, im_root]
  field_simp
  linear_combination hD + Real.sq_sqrt D.cast_nonneg

/-- The product `conj (denom γ (root f)) · denom γ (root f)` equals the ratio `(γ • f).a / f.a` of
leading coefficients. -/
theorem conj_denom_mul_denom_root (f : posDef D) (γ : SL(2, ℤ)) :
    conj (denom γ (root f)) * denom γ (root f) = ((γ • f).1.a : ℂ) / (f.1.a : ℂ) := by
  have hfa : (f.1.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (mem_posDef.mp f.2).2.ne'
  have hgfa : ((γ • f).1.a : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (mem_posDef.mp (γ • f).2).2.ne'
  have hsqrt : √(D : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (NeZero.pos D))).ne'
  have hden : Complex.normSq (denom γ (root f)) ≠ 0 :=
    (Complex.normSq_pos.mpr (denom_ne_zero γ (root f))).ne'
  have him : √(D : ℝ) / (2 * (γ • f).1.a) =
      (√(D : ℝ) / (2 * f.1.a)) / Complex.normSq (denom γ (root f)) := by
    simpa only [im_root, _root_.ModularGroup.im_smul_eq_div_normSq] using
      congrArg UpperHalfPlane.im (root_smul γ f)
  have hnorm : Complex.normSq (denom γ (root f)) = ((γ • f).1.a : ℝ) / (f.1.a : ℝ) := by
    field_simp at him ⊢
    linarith
  rw [mul_comm, Complex.mul_conj, hnorm]
  push_cast
  rfl

/-- The stabiliser of the root of `f` in `SL(2, ℤ)` is the stabiliser of `f`. -/
@[simp]
theorem stabilizer_root (f : posDef D) :
    MulAction.stabilizer SL(2, ℤ) (root f) = MulAction.stabilizer SL(2, ℤ) f := by
  ext γ
  simp only [MulAction.mem_stabilizer_iff, ← root_smul, root_injective.eq_iff]

/-- The root of the reflected form `a x² - b x y + c y²` is the reflection `J • τ = -conj τ` of
the root `τ` of `a x² + b x y + c y²`. -/
theorem root_of_eq_reflected {f g : posDef D} (hg : g.1 = f.1.reflected) :
    root g = J • root f := by
  refine UpperHalfPlane.ext_re_im ?_ ?_
  · rw [re_root, J_smul_re, re_root, hg, reflected_a, reflected_b]
    push_cast
    ring
  · rw [im_root, J_smul_im, im_root, hg, reflected_a]

/-- A positive definite form and its primitive part have the same root in the upper half-plane. -/
theorem root_eq_root_of_eq_primPart {D' : ℕ} [NeZero D'] {f : posDef D} {g : posDef D'}
    (hg : g.1 = f.1.primPart) : root g = root f := by
  symm
  rw [eq_root_iff]
  have hf0 : f.1 ≠ 0 := fun h ↦ (mem_posDef.mp f.2).2.ne' (by simp [h])
  have hc : (f.1.content : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ((f.1.content_pos_iff).mpr hf0).ne'
  have hsmul := f.1.content_smul_primPart
  have ha : (f.1.content : ℤ) * g.1.a = f.1.a := by
    simpa only [hg, smul_a', nsmul_eq_mul] using congrArg BinaryQuadraticForm.a hsmul
  have hb : (f.1.content : ℤ) * g.1.b = f.1.b := by
    simpa only [hg, smul_b', nsmul_eq_mul] using congrArg BinaryQuadraticForm.b hsmul
  have hc' : (f.1.content : ℤ) * g.1.c = f.1.c := by
    simpa only [hg, smul_c', nsmul_eq_mul] using congrArg BinaryQuadraticForm.c hsmul
  have hrel := (eq_root_iff f (root f)).mp rfl
  rw [← ha, ← hb, ← hc'] at hrel
  push_cast at hrel
  have hfac : (f.1.content : ℂ) * ((g.1.a : ℂ) * (root f : ℂ) ^ 2 + g.1.b * (root f : ℂ) +
      g.1.c) = 0 := by linear_combination hrel
  exact (mul_eq_zero.mp hfac).resolve_left hc

end BinaryQuadraticForm

end TauCeti
