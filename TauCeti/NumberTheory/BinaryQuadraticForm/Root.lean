/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import TauCeti.NumberTheory.BinaryQuadraticForm.Basic
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic

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
identifications), and the automorphism group of `f` is the stabiliser of `τ`, of order `4` at
`τ = i`, `6` at `τ = ρ` and `2` otherwise.

## Main definitions

* `TauCeti.BinaryQuadraticForm.root`: the root `(-b + i √D) / (2 a)` in `ℍ` of a form in
  `posDef D`.

## Main results

* `TauCeti.BinaryQuadraticForm.eq_root_iff`: `root f` is the only point of `ℍ` at which
  `a z² + b z + c` vanishes.
* `TauCeti.BinaryQuadraticForm.root_smul`: `root (γ • f) = γ • root f`.
* `TauCeti.BinaryQuadraticForm.root_injective`: for fixed `D`, a form is determined by its root.
* `TauCeti.BinaryQuadraticForm.normSq_root`: `|root f|² = c / a`.
* `TauCeti.BinaryQuadraticForm.stabilizer_root`: the stabiliser of `root f` in `SL(2, ℤ)` is
  the stabiliser of `f`.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, Graduate Texts in Mathematics
  138, Springer, 1993, §5.3.
* D. Zagier, *Zetafunktionen und quadratische Körper*, Springer, 1981, §8.
-/

@[expose] public section

open Complex
open UpperHalfPlane hiding I
open scoped ComplexConjugate MatrixGroups

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
  rfl

/-- The imaginary part of the root of `a x² + b x y + c y²` is `√D / (2 a)`. -/
@[simp]
theorem im_root (f : posDef D) : (root f).im = √(D : ℝ) / (2 * f.1.a) :=
  rfl

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

/-- The root map is `SL(2, ℤ)`-equivariant: `root (γ • f) = γ • root f`, with the action
`γ • f = f ∘ γ⁻¹` on forms and the Möbius action on `ℍ`. -/
theorem root_smul (γ : SL(2, ℤ)) (f : posDef D) : root (γ • f) = γ • root f := by
  have hden : (γ 1 0 : ℂ) * root f + γ 1 1 ≠ 0 := denom_ne_zero γ (root f)
  rw [eq_comm, eq_root_iff]
  push_cast [coe_specialLinearGroup_apply, smul_a, smul_b, smul_c, eq_intCast]
  -- `(γ • f)(γ • τ, 1) (r τ + s)² = (det γ)² f(τ, 1)` for `γ = !![p, q; r, s]` and `τ = root f`
  grind [(eq_root_iff f _).1 rfl]

/-- For fixed `D`, a positive definite form is determined by its root: the imaginary part of the
root gives `a`, the real part then gives `b`, and the discriminant gives `c`. -/
theorem root_injective : Function.Injective (root (D := D)) := by
  intro f g h
  obtain ⟨hdf, hfa⟩ := mem_posDef.1 f.2
  obtain ⟨hdg, hga'⟩ := mem_posDef.1 g.2
  have ha : (f.1.a : ℝ) ≠ 0 := by exact_mod_cast hfa.ne'
  have hga : (g.1.a : ℝ) ≠ 0 := by exact_mod_cast hga'.ne'
  have him := congrArg UpperHalfPlane.im h
  have hre := congrArg UpperHalfPlane.re h
  simp only [im_root, re_root] at him hre
  rw [div_eq_div_iff (by positivity) (by positivity)] at him hre
  have haa : f.1.a = g.1.a := by
    have := mul_left_cancel₀ (Real.sqrt_pos.2 <| Nat.cast_pos.2 <| NeZero.pos D).ne' him
    exact_mod_cast (by linarith : (f.1.a : ℝ) = g.1.a)
  rw [← haa] at hre
  have hbb : f.1.b = g.1.b := by
    have := mul_right_cancel₀ (by positivity : (2 * f.1.a : ℝ) ≠ 0) hre
    exact_mod_cast neg_inj.1 this
  have hcc : f.1.c = g.1.c := by
    rw [discrim_def, discrim, haa, hbb] at hdf
    rw [discrim_def, discrim] at hdg
    have : (4 * g.1.a) * (f.1.c - g.1.c) = 0 := by linear_combination hdg - hdf
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (by omega))
  exact Subtype.ext (BinaryQuadraticForm.ext haa hbb hcc)

/-- The squared absolute value of the root of `a x² + b x y + c y²` is `c / a`. -/
theorem normSq_root (f : posDef D) : Complex.normSq (root f) = f.1.c / f.1.a := by
  obtain ⟨hdf, hfa⟩ := mem_posDef.1 f.2
  have ha : (f.1.a : ℝ) ≠ 0 := by exact_mod_cast hfa.ne'
  have hD : ((f.1.b : ℝ) ^ 2 - 4 * f.1.a * f.1.c) = -D := by
    rw [discrim_def, discrim] at hdf
    exact_mod_cast hdf
  rw [Complex.normSq_apply, coe_re, coe_im, re_root, im_root]
  field_simp
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  linear_combination hD

/-- The stabiliser of the root of `f` in `SL(2, ℤ)` is the stabiliser of `f`. -/
theorem stabilizer_root (f : posDef D) :
    MulAction.stabilizer SL(2, ℤ) (root f) = MulAction.stabilizer SL(2, ℤ) f := by
  ext γ
  rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff, ← root_smul,
    root_injective.eq_iff]

end BinaryQuadraticForm

end TauCeti
