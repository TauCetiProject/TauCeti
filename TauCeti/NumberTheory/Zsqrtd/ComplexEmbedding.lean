/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.NumberTheory.Zsqrtd.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import TauCeti.Analysis.Complex.Sqrt

/-!
# Complex embeddings of `ℤ√d`

For any integer `d : ℤ`, the quadratic order `ℤ√d` admits two ring homomorphisms into `ℂ`, sending
`⟨a, b⟩` to `a + b * Complex.sqrt d` (`Zsqrtd.embPos d`) and `a - b * Complex.sqrt d`
(`Zsqrtd.embNeg d`). They are conjugate under the source involution `star` on `ℤ√d`
(`⟨a, b⟩ ↦ ⟨a, -b⟩`): `embPos d (star u) = embNeg d u` and `embNeg d (star u) = embPos d u` for
every `d`. (By contrast, complex conjugation on the target `ℂ` exchanges them when `d < 0`, while
fixing both real images when `d ≥ 0`.) When `¬ IsSquare d`, both embeddings are injective.

The parallelogram law on `ℂ` relates the squared complex norms of the two embeddings to the
trace-type quadratic form `2 * (re ^ 2 + |d| * im ^ 2)` uniformly in the sign of `d`.

## Main results

* `Zsqrtd.embPos`, `Zsqrtd.embNeg`: the two complex embeddings `ℤ√d →+* ℂ`.
* `Zsqrtd.embPos_star`, `Zsqrtd.embNeg_star`: source conjugation `star` on `ℤ√d` exchanges
  `embPos d` and `embNeg d`.
* `Zsqrtd.embPos_injective`, `Zsqrtd.embNeg_injective`: injectivity whenever `¬ IsSquare d`.
* `Zsqrtd.two_mul_re_sq_add_im_sq_eq`: parallelogram identity
  `2 * (u.re ^ 2 + |d| * u.im ^ 2) = ‖embPos d u‖ ^ 2 + ‖embNeg d u‖ ^ 2`.
-/

public section

namespace Zsqrtd

/-- The complex embedding `a + b√d ↦ a + b * Complex.sqrt d` of `ℤ√d`. -/
noncomputable def embPos (d : ℤ) : ℤ√d →+* ℂ :=
  Zsqrtd.lift ⟨Complex.sqrt d, by rw [← sq, Complex.sq_sqrt]⟩

/-- The conjugate complex embedding `a + b√d ↦ a - b * Complex.sqrt d` of `ℤ√d`, obtained by
precomposing `Zsqrtd.embPos d` with the algebraic conjugation `star` on `ℤ√d`. -/
noncomputable def embNeg (d : ℤ) : ℤ√d →+* ℂ :=
  Zsqrtd.lift ⟨-Complex.sqrt d, by rw [neg_mul_neg, ← sq, Complex.sq_sqrt]⟩

/-- Value of `Zsqrtd.embPos d` on an element `u : ℤ√d`. -/
theorem embPos_apply (d : ℤ) (u : ℤ√d) :
    embPos d u = (u.re : ℂ) + (u.im : ℂ) * Complex.sqrt d := by
  rfl

/-- Value of `Zsqrtd.embNeg d` on an element `u : ℤ√d`. -/
theorem embNeg_apply (d : ℤ) (u : ℤ√d) :
    embNeg d u = (u.re : ℂ) + (u.im : ℂ) * (-Complex.sqrt d) := by
  rfl

/-- Source conjugation `star` on `ℤ√d` sends `Zsqrtd.embPos d` to `Zsqrtd.embNeg d`. -/
@[simp]
theorem embPos_star (d : ℤ) (u : ℤ√d) : embPos d (star u) = embNeg d u := by
  simp only [embPos_apply, embNeg_apply, re_star, im_star, Int.cast_neg]
  ring

/-- Source conjugation `star` on `ℤ√d` sends `Zsqrtd.embNeg d` to `Zsqrtd.embPos d`. -/
@[simp]
theorem embNeg_star (d : ℤ) (u : ℤ√d) : embNeg d (star u) = embPos d u := by
  simp only [embPos_apply, embNeg_apply, re_star, im_star, Int.cast_neg]
  ring

/-- `Zsqrtd.embPos d` is injective whenever `d` is not a square in `ℤ`. -/
theorem embPos_injective {d : ℤ} (hd : ¬ IsSquare d) : Function.Injective (embPos d) :=
  Zsqrtd.lift_injective _ fun n hn ↦ hd ⟨n, hn⟩

/-- `Zsqrtd.embNeg d` is injective whenever `d` is not a square in `ℤ`. -/
theorem embNeg_injective {d : ℤ} (hd : ¬ IsSquare d) : Function.Injective (embNeg d) :=
  Zsqrtd.lift_injective _ fun n hn ↦ hd ⟨n, hn⟩

/-- Parallelogram identity relating the weighted coordinate norm on `ℤ√d` to the two complex
embeddings, uniformly in the sign of `d`. -/
theorem two_mul_re_sq_add_im_sq_eq (d : ℤ) (u : ℤ√d) :
    2 * ((u.re : ℝ) ^ 2 + (d.natAbs : ℝ) * (u.im : ℝ) ^ 2) =
      ‖embPos d u‖ ^ 2 + ‖embNeg d u‖ ^ 2 := by
  have hpar := parallelogram_law_with_norm ℂ (u.re : ℂ) ((u.im : ℂ) * Complex.sqrt d)
  have hsq : ‖Complex.sqrt (d : ℂ)‖ ^ 2 = (d.natAbs : ℝ) := by
    rw [Complex.norm_sqrt_intCast, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [embPos_apply, embNeg_apply, mul_neg, ← sub_eq_add_neg, hpar, Complex.norm_intCast,
    Complex.norm_mul, Complex.norm_intCast, mul_pow, sq_abs, sq_abs, hsq]
  ring

end Zsqrtd
