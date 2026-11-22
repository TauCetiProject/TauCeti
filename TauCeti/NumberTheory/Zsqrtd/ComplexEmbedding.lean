/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.RCLike.Sqrt
public import Mathlib.NumberTheory.Zsqrtd.Basic
public import TauCeti.NumberTheory.NumberField.Quadratic.EmbeddingBound
public import TauCeti.NumberTheory.Zsqrtd.QuadraticAlgebra
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

Along the canonical equivalence `Zsqrtd.equivQuadraticAlgebra d : ℤ√d ≃+* QuadraticAlgebra ℤ d 0`
and scalar extension to `ℚ`, these maps agree with `QuadraticAlgebra.sqrtEmbedding (d : ℚ)` and
`QuadraticAlgebra.negSqrtEmbedding (d : ℚ)`, transporting the coordinate bound
`‖embPos d u‖, ‖embNeg d u‖ ≤ |u.re| + |u.im| * √|d|`.

The parallelogram law on `ℂ` relates the squared complex norms of the two embeddings to the
weighted Euclidean quadratic form `2 * (re ^ 2 + |d| * im ^ 2)` uniformly in the sign of `d`.

## Main results

* `Zsqrtd.embPos`, `Zsqrtd.embNeg`: the two complex embeddings `ℤ√d →+* ℂ`.
* `Zsqrtd.embPos_sqrtd`, `Zsqrtd.embNeg_sqrtd`: values on the generator `Zsqrtd.sqrtd`.
* `Zsqrtd.embPos_star`, `Zsqrtd.embNeg_star`: source conjugation `star` on `ℤ√d` exchanges
  `embPos d` and `embNeg d`.
* `Zsqrtd.embPos_injective`, `Zsqrtd.embNeg_injective`: injectivity whenever `¬ IsSquare d`.
* `Zsqrtd.embPos_eq_sqrtEmbedding`, `Zsqrtd.embNeg_eq_negSqrtEmbedding`: agreement with
  `QuadraticAlgebra.sqrtEmbedding` and `QuadraticAlgebra.negSqrtEmbedding`.
* `Zsqrtd.norm_embPos_le`, `Zsqrtd.norm_embNeg_le`: coordinate norm bounds transported from
  `QuadraticAlgebra.norm_embedding_algebraMap_le`.
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

/-- `Zsqrtd.embPos d` sends the generator `Zsqrtd.sqrtd` to `Complex.sqrt d`. -/
@[simp]
theorem embPos_sqrtd (d : ℤ) : embPos d sqrtd = Complex.sqrt d := by
  simp [embPos]

/-- `Zsqrtd.embNeg d` sends the generator `Zsqrtd.sqrtd` to `-Complex.sqrt d`. -/
@[simp]
theorem embNeg_sqrtd (d : ℤ) : embNeg d sqrtd = -Complex.sqrt d := by
  simp [embNeg]

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

/-- Real coordinate of the scalar-extended element `equivQuadraticAlgebra d u` viewed in
`QuadraticAlgebra ℚ d 0`; isolates the definitional conversion from parameter `((0 : ℤ) : ℚ)` to
`0`. -/
private theorem re_algebraMap_equivQuadraticAlgebra (d : ℤ) (u : ℤ√d) :
    ((algebraMap (QuadraticAlgebra ℤ d 0) (QuadraticAlgebra ℚ d ((0 : ℤ) : ℚ))
        (equivQuadraticAlgebra d u) : QuadraticAlgebra ℚ d 0).re) = (u.re : ℚ) := by
  -- `((0 : ℤ) : ℚ)` and `0 : ℚ` are definitionally equal, so `.re` agrees across the type cast.
  rw [QuadraticAlgebra.Int.re_algebraMap (a := d) (b := 0), re_equivQuadraticAlgebra]

/-- Imaginary coordinate of the scalar-extended element `equivQuadraticAlgebra d u` viewed in
`QuadraticAlgebra ℚ d 0`; isolates the definitional conversion from parameter `((0 : ℤ) : ℚ)` to
`0`. -/
private theorem im_algebraMap_equivQuadraticAlgebra (d : ℤ) (u : ℤ√d) :
    ((algebraMap (QuadraticAlgebra ℤ d 0) (QuadraticAlgebra ℚ d ((0 : ℤ) : ℚ))
        (equivQuadraticAlgebra d u) : QuadraticAlgebra ℚ d 0).im) = (u.im : ℚ) := by
  -- `((0 : ℤ) : ℚ)` and `0 : ℚ` are definitionally equal, so `.im` agrees across the type cast.
  rw [QuadraticAlgebra.Int.im_algebraMap (a := d) (b := 0), im_equivQuadraticAlgebra]

/-- `Zsqrtd.embPos d` agrees with `QuadraticAlgebra.sqrtEmbedding (d : ℚ)` via
`Zsqrtd.equivQuadraticAlgebra d` and scalar extension to `ℚ`. -/
theorem embPos_eq_sqrtEmbedding (d : ℤ) (u : ℤ√d) :
    embPos d u =
      QuadraticAlgebra.sqrtEmbedding (d : ℚ)
        (algebraMap (QuadraticAlgebra ℤ d 0) (QuadraticAlgebra ℚ d ((0 : ℤ) : ℚ))
          (equivQuadraticAlgebra d u)) := by
  rw [embPos_apply, QuadraticAlgebra.sqrtEmbedding_apply,
    re_algebraMap_equivQuadraticAlgebra, im_algebraMap_equivQuadraticAlgebra]
  simp only [Rat.cast_intCast]

/-- `Zsqrtd.embNeg d` agrees with `QuadraticAlgebra.negSqrtEmbedding (d : ℚ)` via
`Zsqrtd.equivQuadraticAlgebra d` and scalar extension to `ℚ`. -/
theorem embNeg_eq_negSqrtEmbedding (d : ℤ) (u : ℤ√d) :
    embNeg d u =
      QuadraticAlgebra.negSqrtEmbedding (d : ℚ)
        (algebraMap (QuadraticAlgebra ℤ d 0) (QuadraticAlgebra ℚ d ((0 : ℤ) : ℚ))
          (equivQuadraticAlgebra d u)) := by
  rw [embNeg_apply, QuadraticAlgebra.negSqrtEmbedding_apply,
    re_algebraMap_equivQuadraticAlgebra, im_algebraMap_equivQuadraticAlgebra]
  simp only [Rat.cast_intCast, sub_eq_add_neg, mul_neg]

/-- Coordinate norm bound for `Zsqrtd.embPos`, transported from
`QuadraticAlgebra.norm_embedding_algebraMap_le`. -/
theorem norm_embPos_le (d : ℤ) (u : ℤ√d) :
    ‖embPos d u‖ ≤ |(u.re : ℝ)| + |(u.im : ℝ)| * Real.sqrt d.natAbs := by
  rw [embPos_eq_sqrtEmbedding]
  simpa [Nat.cast_natAbs, Int.cast_abs] using
    QuadraticAlgebra.norm_embedding_algebraMap_le
      (QuadraticAlgebra.sqrtEmbedding (d : ℚ)) (equivQuadraticAlgebra d u)

/-- Coordinate norm bound for `Zsqrtd.embNeg`, transported from
`QuadraticAlgebra.norm_embedding_algebraMap_le`. -/
theorem norm_embNeg_le (d : ℤ) (u : ℤ√d) :
    ‖embNeg d u‖ ≤ |(u.re : ℝ)| + |(u.im : ℝ)| * Real.sqrt d.natAbs := by
  rw [embNeg_eq_negSqrtEmbedding]
  simpa [Nat.cast_natAbs, Int.cast_abs] using
    QuadraticAlgebra.norm_embedding_algebraMap_le
      (QuadraticAlgebra.negSqrtEmbedding (d : ℚ)) (equivQuadraticAlgebra d u)

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
