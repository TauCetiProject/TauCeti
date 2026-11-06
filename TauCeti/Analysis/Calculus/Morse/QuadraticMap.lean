/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import TauCeti.Analysis.Calculus.FDeriv.QuadraticMap
public import TauCeti.Analysis.Calculus.Morse.Basic
public import TauCeti.Analysis.Calculus.Morse.Index
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Signature

/-!
# Morse data of a quadratic form

A quadratic form `Q` on a finite-dimensional real normed space, viewed as a function, is the
model of a critical point: its Hessian quadratic form is `2 • Q` at every point
(`QuadraticMap.hessianQuadraticForm_eq_two_smul`), so its Morse index is the negative index of
inertia `sigNeg Q` at every point (`QuadraticMap.morseIndex_eq_sigNeg`), and the origin is a
nondegenerate critical point exactly when `Q` is nondegenerate
(`QuadraticMap.isNondegenerateCriticalPoint_zero_iff`).

These identify the Morse data of a function which, after a change of coordinates, is a constant
plus a quadratic form, such as a diagonal form `QuadraticMap.weightedSumSquares`, whose
negative index of inertia Mathlib computes as the number of negative weights
(`QuadraticForm.sigNeg_weightedSumSquares`).

The quotient `z ↦ (c + ∑ₖ bₖ zₖ²) / (1 + ∑ₖ zₖ²)` of diagonal forms is an example: the substitution
`φ(z) = z / √(1 + ∑ₖ zₖ²)`, whose derivative at the origin is the identity, carries it onto
`c + ∑ₖ (bₖ - c) yₖ²` exactly. So when no weight `bₖ` equals `c`, its only critical point is the
origin (`QuadraticMap.eq_zero_of_fderiv_const_add_weightedSumSquares_div_eq_zero`), which is
nondegenerate (`QuadraticMap.isNondegenerateCriticalPoint_const_add_weightedSumSquares_div`) of
Morse index `#{k | bₖ < c}` (`QuadraticMap.morseIndex_const_add_weightedSumSquares_div`). This is
the weighted sum of squares on real projective space read in an affine chart.
-/

public section

open TauCeti
open scoped ContDiff

namespace QuadraticMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Hessian quadratic form of a quadratic form `Q` is `2 • Q`, at every point. -/
@[simp]
theorem hessianQuadraticForm_eq_two_smul (Q : QuadraticForm ℝ E) (x : E) :
    hessianQuadraticForm Q x = (2 : ℝ) • Q := by
  ext v
  rw [hessianQuadraticForm_apply, fderiv_fderiv_apply, polar_self, smul_apply, two_nsmul,
    two_smul]

/-- The Morse index of a quadratic form `Q` is its negative index of inertia, at every point. -/
@[simp]
theorem morseIndex_eq_sigNeg (Q : QuadraticForm ℝ E) (x : E) : morseIndex Q x = sigNeg Q := by
  rw [morseIndex_def, hessianQuadraticForm_eq_two_smul,
    QuadraticForm.sigNeg_smul_of_pos _ two_pos]

/-- The origin is a nondegenerate critical point of a quadratic form exactly when the form is
nondegenerate. -/
theorem isNondegenerateCriticalPoint_zero_iff (Q : QuadraticForm ℝ E) :
    IsNondegenerateCriticalPoint Q 0 ↔ Q.Nondegenerate := by
  have h₁ : fderiv ℝ Q 0 = 0 := by
    ext v
    simp [fderiv_apply]
  have h₂ : (fderiv ℝ (fderiv ℝ Q) 0).toBilinForm = polarBilin Q := by
    ext v w
    simp [fderiv_fderiv_apply]
  rw [isNondegenerateCriticalPoint_iff_separatingLeft, h₂, nondegenerate_iff_radical_eq_bot,
    radical_eq_ker_polarBilin, ← LinearMap.separatingLeft_iff_ker_eq_bot]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨Q.contDiff.contDiffAt, h₁, h⟩⟩

end QuadraticMap

/-! ### A quotient of diagonal forms -/

namespace QuadraticMap

variable {ι : Type*} [Fintype ι]

private theorem one_add_weightedSumSquares_one_pos (z : ι → ℝ) :
    0 < 1 + weightedSumSquares ℝ (1 : ι → ℝ) z := by
  have : 0 ≤ weightedSumSquares ℝ (1 : ι → ℝ) z := by
    rw [weightedSumSquares_apply]
    exact Finset.sum_nonneg fun k _ ↦ by simpa using mul_self_nonneg (z k)
  linarith

/-- The quotient `z ↦ (c + ∑ₖ bₖ zₖ²) / (1 + ∑ₖ zₖ²)` of diagonal forms is smooth. -/
theorem contDiff_const_add_weightedSumSquares_div (b : ι → ℝ) (c : ℝ) {r : ℕ∞ω} :
    ContDiff ℝ r fun z ↦
      (c + weightedSumSquares ℝ b z) / (1 + weightedSumSquares ℝ (1 : ι → ℝ) z) :=
  (contDiff_const.add (weightedSumSquares ℝ b).contDiff).div
    (contDiff_const.add (weightedSumSquares ℝ (1 : ι → ℝ)).contDiff)
    fun z ↦ (one_add_weightedSumSquares_one_pos z).ne'

/-- If no weight `bₖ` equals `c`, the only critical point of
`g(z) = (c + ∑ₖ bₖ zₖ²) / (1 + ∑ₖ zₖ²)` is the origin. Differentiating `g · (1 + N) = c + P`
gives `bₖ zₖ = g(z) zₖ` at a critical point, and summing these against `zₖ` shows `g(z) = c`. -/
theorem eq_zero_of_fderiv_const_add_weightedSumSquares_div_eq_zero {b : ι → ℝ} {c : ℝ}
    (hb : ∀ k, b k ≠ c) {z : ι → ℝ}
    (hz : fderiv ℝ
      (fun y ↦ (c + weightedSumSquares ℝ b y) / (1 + weightedSumSquares ℝ (1 : ι → ℝ) y)) z = 0) :
    z = 0 := by
  classical
  set P := weightedSumSquares ℝ b
  set N := weightedSumSquares ℝ (1 : ι → ℝ)
  set g := fun y ↦ (c + P y) / (1 + N y) with hg_def
  have hD (y : ι → ℝ) := (one_add_weightedSumSquares_one_pos y).ne'
  have hg : HasFDerivAt g (0 : (ι → ℝ) →L[ℝ] ℝ) z := by
    rw [← hz]
    exact ((contDiff_const_add_weightedSumSquares_div b c (r := 1)).differentiable one_ne_zero
      z).hasFDerivAt
  -- Differentiating `g * (1 + N) = c + P` at `z` gives `P'(z) = g(z) • N'(z)`.
  have hprod : HasFDerivAt (fun y ↦ c + P y) (g z • fderiv ℝ N z) z := by
    have h := hg.mul ((N.hasFDerivAt z).const_add 1)
    rw [smul_zero, add_zero] at h
    convert h using 1
    · funext y
      exact (div_mul_cancel₀ _ (hD y)).symm
    · simp [(N.hasFDerivAt z).fderiv]
  -- On a basis vector, the derivative of a diagonal form is twice its associated bilinear form.
  have hpolar (a : ι → ℝ) (k : ι) :
      fderiv ℝ (weightedSumSquares ℝ a) z (Pi.single k 1) = 2 * (a k * z k) := by
    have h := congrArg (fun B ↦ B z (Pi.single k 1))
      (two_nsmul_associated ℝ (weightedSumSquares ℝ a))
    simp only [LinearMap.smul_apply, polarBilin_apply_apply, associated_weightedSumSquares] at h
    rw [fderiv_apply, ← h]
    simp [Pi.single_apply]
  have hcoord (k : ι) : b k * z k = g z * z k := by
    have h := congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ ↦ L (Pi.single k 1))
      ((P.hasFDerivAt z).const_add c |>.unique hprod)
    simp only [← (P.hasFDerivAt z).fderiv, _root_.smul_apply, smul_eq_mul, P, N,
      hpolar, Pi.one_apply, one_mul] at h
    linarith
  -- Summing `bₖ zₖ² = g(z) zₖ²` gives `P z = g(z) N z`, hence `g(z) = c`.
  have hsum : P z = g z * N z := by
    simp only [P, N, weightedSumSquares_apply, smul_eq_mul, Pi.one_apply, one_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← mul_assoc, hcoord k, mul_assoc]
  have hgc : g z = c := by
    have h : g z * (1 + N z) = c + P z := div_mul_cancel₀ _ (hD z)
    rw [hsum] at h
    linarith
  funext k
  have h := hcoord k
  rw [hgc] at h
  exact (mul_eq_zero.1 (by linarith : (b k - c) * z k = 0)).resolve_left (sub_ne_zero.2 (hb k))

/-- The substitution `φ(z) = z / √(1 + ∑ₖ zₖ²)`, which carries the quotient
`z ↦ (c + ∑ₖ bₖ zₖ²) / (1 + ∑ₖ zₖ²)` onto a constant plus a diagonal quadratic form. -/
private noncomputable def quotientSubstitution (z : ι → ℝ) : ι → ℝ :=
  (√(1 + weightedSumSquares ℝ (1 : ι → ℝ) z))⁻¹ • z

private theorem contDiff_quotientSubstitution_scale {r : ℕ∞ω} :
    ContDiff ℝ r fun z : ι → ℝ ↦ (√(1 + weightedSumSquares ℝ (1 : ι → ℝ) z))⁻¹ :=
  ((contDiff_const.add (weightedSumSquares ℝ (1 : ι → ℝ)).contDiff).sqrt
    fun z ↦ (one_add_weightedSumSquares_one_pos z).ne').inv
      fun z ↦ (Real.sqrt_pos.2 (one_add_weightedSumSquares_one_pos z)).ne'

private theorem contDiff_quotientSubstitution {r : ℕ∞ω} :
    ContDiff ℝ r (quotientSubstitution (ι := ι)) :=
  contDiff_quotientSubstitution_scale.smul contDiff_id

private theorem quotientSubstitution_zero : quotientSubstitution (0 : ι → ℝ) = 0 := by
  simp [quotientSubstitution]

/-- The substitution `φ` has derivative the identity at the origin. -/
private theorem fderiv_quotientSubstitution_zero :
    fderiv ℝ (quotientSubstitution (ι := ι)) 0 = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  have h := ((contDiff_quotientSubstitution_scale (r := 1)).differentiable one_ne_zero
    0).hasFDerivAt.smul (hasFDerivAt_id (𝕜 := ℝ) (0 : ι → ℝ))
  refine h.fderiv.trans ?_
  ext v
  simp

/-- After the substitution `φ`, the quotient `z ↦ (c + ∑ₖ bₖ zₖ²) / (1 + ∑ₖ zₖ²)` is the
constant `c` plus the diagonal form with weights `bₖ - c`. -/
private theorem const_add_weightedSumSquares_div_eq_comp (b : ι → ℝ) (c : ℝ) :
    (fun z ↦ (c + weightedSumSquares ℝ b z) / (1 + weightedSumSquares ℝ (1 : ι → ℝ) z)) =
      (fun y ↦ weightedSumSquares ℝ (fun k ↦ b k - c) y + c) ∘ quotientSubstitution := by
  funext z
  have hD := one_add_weightedSumSquares_one_pos z
  have hsq : (√(1 + weightedSumSquares ℝ (1 : ι → ℝ) z))⁻¹ *
      (√(1 + weightedSumSquares ℝ (1 : ι → ℝ) z))⁻¹ =
        (1 + weightedSumSquares ℝ (1 : ι → ℝ) z)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hD.le]
  have hsplit : weightedSumSquares ℝ (fun k ↦ b k - c) z =
      weightedSumSquares ℝ b z - c * weightedSumSquares ℝ (1 : ι → ℝ) z := by
    simp only [weightedSumSquares_apply, smul_eq_mul, Pi.one_apply, one_mul, Finset.mul_sum,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  simp only [Function.comp_apply, quotientSubstitution, QuadraticMap.map_smul, smul_eq_mul, hsq,
    hsplit]
  field_simp
  ring

/-- The origin is a nondegenerate critical point of `z ↦ (c + ∑ₖ bₖ zₖ²) / (1 + ∑ₖ zₖ²)` of
Morse index `#{k | bₖ < c}`, when no `bₖ` equals `c`: the substitution `φ` carries this function
onto `c + ∑ₖ (bₖ - c) yₖ²`. -/
private theorem isNondegenerateCriticalPoint_and_morseIndex_const_add_weightedSumSquares_div
    {b : ι → ℝ} {c : ℝ}
    (hb : ∀ k, b k ≠ c) :
    IsNondegenerateCriticalPoint
        (fun z ↦ (c + weightedSumSquares ℝ b z) / (1 + weightedSumSquares ℝ (1 : ι → ℝ) z)) 0 ∧
      morseIndex
          (fun z ↦ (c + weightedSumSquares ℝ b z) / (1 + weightedSumSquares ℝ (1 : ι → ℝ) z)) 0 =
        {k | b k < c}.ncard := by
  set Q := weightedSumSquares ℝ (fun k ↦ b k - c)
  have hQ : ContDiffAt ℝ 2 (fun y ↦ Q y + c) (quotientSubstitution 0) :=
    (Q.contDiff.add contDiff_const).contDiffAt
  have hφ : ContDiffAt ℝ 2 (quotientSubstitution (ι := ι)) 0 :=
    contDiff_quotientSubstitution.contDiffAt
  have hinv : (fderiv ℝ (quotientSubstitution (ι := ι)) 0).IsInvertible := by
    rw [fderiv_quotientSubstitution_zero]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  have hnd : IsNondegenerateCriticalPoint Q 0 :=
    (isNondegenerateCriticalPoint_zero_iff Q).2 <|
      nondegenerate_weightedSumSquares fun k ↦ isRegular_iff_ne_zero.2 (sub_ne_zero.2 (hb k))
  rw [const_add_weightedSumSquares_div_eq_comp]
  refine ⟨(isNondegenerateCriticalPoint_comp_iff hQ hφ hinv).2 ?_, ?_⟩
  · rw [quotientSubstitution_zero, isNondegenerateCriticalPoint_add_const_iff]
    exact hnd
  · have hcrit : fderiv ℝ (fun y ↦ Q y + c) (quotientSubstitution 0) = 0 := by
      rw [fderiv_add_const, quotientSubstitution_zero]
      exact hnd.fderiv_eq_zero
    rw [morseIndex_comp hQ hφ hcrit hinv, quotientSubstitution_zero, morseIndex_add_const,
      morseIndex_eq_sigNeg, QuadraticForm.sigNeg_weightedSumSquares]
    simp only [sub_neg]

/-- If no weight `bₖ` equals `c`, the origin is a nondegenerate critical point of
`z ↦ (c + ∑ₖ bₖ zₖ²) / (1 + ∑ₖ zₖ²)`. -/
theorem isNondegenerateCriticalPoint_const_add_weightedSumSquares_div {b : ι → ℝ} {c : ℝ}
    (hb : ∀ k, b k ≠ c) :
    IsNondegenerateCriticalPoint
      (fun z ↦ (c + weightedSumSquares ℝ b z) / (1 + weightedSumSquares ℝ (1 : ι → ℝ) z)) 0 :=
  (isNondegenerateCriticalPoint_and_morseIndex_const_add_weightedSumSquares_div hb).1

/-- If no weight `bₖ` equals `c`, the Morse index of `z ↦ (c + ∑ₖ bₖ zₖ²) / (1 + ∑ₖ zₖ²)` at the
origin is the number `#{k | bₖ < c}` of weights smaller than `c`. -/
theorem morseIndex_const_add_weightedSumSquares_div {b : ι → ℝ} {c : ℝ} (hb : ∀ k, b k ≠ c) :
    morseIndex (fun z ↦ (c + weightedSumSquares ℝ b z) / (1 + weightedSumSquares ℝ (1 : ι → ℝ) z))
      0 = {k | b k < c}.ncard :=
  (isNondegenerateCriticalPoint_and_morseIndex_const_add_weightedSumSquares_div hb).2

end QuadraticMap
