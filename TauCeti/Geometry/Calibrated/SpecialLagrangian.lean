/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Alternating
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Complex
import TauCeti.Analysis.Normed.Module.Alternating.TopDegree
import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# Special Lagrangian linear algebra on complex Euclidean space

On complex Euclidean space `ℂⁿ = EuclideanSpace ℂ (Fin n)`, the holomorphic volume form
`Ω = dz₁ ∧ ⋯ ∧ dzₙ` sends an `n`-tuple of vectors `v` to the complex determinant of the `n × n`
matrix whose rows are the complex coordinate vectors of `v`. Viewed on the underlying real inner
product space of dimension `2n`, `Ω` is a continuous `ℝ`-alternating `n`-form with values in `ℂ`
(`TauCeti.standardComplexVolume`), complex-linear in each argument individually.

Rotating `Ω` by a phase `e^(-iθ)` and taking the real part produces the **special Lagrangian form**
`φ_θ v = Re(e^(-iθ) Ω v) = cos θ Re(Ω v) + sin θ Im(Ω v)` (`TauCeti.standardSpecialLagrangianForm`),
a real continuous alternating `n`-form on `ℂⁿ`.

By Hadamard's inequality in the standard complex orthonormal basis of `ℂⁿ`, any `ℝ`-orthonormal
`n`-frame `v` satisfies `‖Ω v‖ ≤ ∏ i, ‖v i‖ = 1`, so `|φ_θ v| ≤ ‖Ω v‖ ≤ 1` and `‖φ_θ‖ ≤ 1` in every
dimension `n`. When `1 ≤ n`, rotating the first vector of the standard basis by `e^(iθ)` produces a
unitary (hence `ℝ`-orthonormal) frame on which `φ_θ` evaluates to `1`, so `φ_θ` has comass
`‖φ_θ‖ = 1` (`TauCeti.norm_standardSpecialLagrangianForm`). By contrast, in degree zero `Ω ![] = 1`
and `φ_θ ![] = cos θ` has norm `|cos θ|` (`TauCeti.norm_standardSpecialLagrangianForm_zero`), so
`1 ≤ n` is sharp.

Equality in Hadamard's inequality characterizes the calibrated planes
(`TauCeti.specialLagrangianFrame_iff`): an `ℝ`-orthonormal `n`-frame `v` (for every `n`, including
`n = 0`) satisfies `φ_θ v = 1` if and only if `Ω v = e^(iθ)`
(`TauCeti.standardSpecialLagrangianForm_apply_eq_one_iff_standardComplexVolume_eq`), equivalently:
1. `Im ⟪v i, v j⟫_ℂ = 0` for all `i, j` (the real span of `v` is Lagrangian, making `v` unitary
   and forcing `‖Ω v‖ = 1`);
2. `Im(e^(-iθ) Ω v) = 0` (the phase matches `θ` modulo `π`); and
3. `0 < Re(e^(-iθ) Ω v)` (the orientation agrees with the positive branch rather than `-1`).

For `2 ≤ n`, all three conditions are independent: non-Lagrangian frames can have real positive
`e^(-iθ) Ω v` with modulus strictly below `1`, Lagrangian frames of intermediate phases can satisfy
`0 < Re(e^(-iθ) Ω v)` while `Im(e^(-iθ) Ω v) ≠ 0`, and reversing orientation negates `e^(-iθ) Ω v`
while preserving the first two equations. In low dimensions condition (1) degenerates: for `n = 1`
every real line in `ℂ¹` is automatically Lagrangian (`Im ⟪v 0, v 0⟫_ℂ = 0`) while conditions (2)
and (3) remain independent across unit vectors, and for `n = 0` condition (1) is vacuous and the
unique frame `![]` fixes `Ω ![] = 1`. For an arbitrary `ℝ`-linearly independent `n`-frame `v`,
Gram–Schmidt reduction on its real span yields the coordinate-free calibrated-plane criterion
`φ_θ v = ‖v₁ ∧ ⋯ ∧ vₙ‖` under the same three conditions
(`TauCeti.standardSpecialLagrangianForm_apply_eq_norm_ιMulti_iff`).

## Main declarations

* `TauCeti.standardComplexVolume`: the complex volume form `Ω` on `EuclideanSpace ℂ (Fin n)` as an
  `ℝ`-continuous alternating `n`-form with values in `ℂ`.
* `TauCeti.norm_standardComplexVolume`: `‖standardComplexVolume n‖ = 1` for every `n`.
* `TauCeti.standardSpecialLagrangianForm`: the phase-`θ` special Lagrangian calibration form
  `φ_θ v = Re(e^(-iθ) Ω v)` on `EuclideanSpace ℂ (Fin n)`.
* `TauCeti.norm_standardSpecialLagrangianForm`: `‖standardSpecialLagrangianForm n θ‖ = 1` for
  `1 ≤ n`.
* `TauCeti.specialLagrangianFrame_iff`: characterization of `ℝ`-orthonormal frames with
  `φ_θ v = 1` in every dimension `n`.
* `TauCeti.standardSpecialLagrangianForm_apply_eq_norm_ιMulti_iff`: characterization of arbitrary
  `ℝ`-linearly independent `n`-frames achieving equality `φ_θ v = ‖v₁ ∧ ⋯ ∧ vₙ‖`.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Theorem III.1.10 and Corollary III.1.11.
* R. C. McLean, *Deformations of calibrated submanifolds*, Comm. Anal. Geom. **6** (1998),
  705–747, Proposition 3.2.
* D. Joyce, *Lectures on special Lagrangian geometry*, in *Global Theory of Minimal Surfaces*,
  Clay Math. Proc. **2**, AMS, 2005, Propositions 2.3 and 2.4.
-/

public section

noncomputable section

open Module
open scoped InnerProductSpace

namespace TauCeti

/-! ### The standard complex volume form -/

/-- The complex volume form `Ω = dz₁ ∧ ⋯ ∧ dzₙ` on `ℂⁿ` as a real continuous alternating
`n`-form with values in `ℂ`: `Ω v` is the determinant of the complex matrix whose rows are the
coordinate vectors of `v`. -/
def standardComplexVolume (n : ℕ) : EuclideanSpace ℂ (Fin n) [⋀^Fin n]→L[ℝ] ℂ :=
  ContinuousAlternatingMap.restrictScalars ℝ
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.continuousDet

/-- `standardComplexVolume n` agrees with the complex coordinate determinant in the standard
orthonormal basis `EuclideanSpace.basisFun (Fin n) ℂ`. -/
theorem standardComplexVolume_eq_det_basisFun (n : ℕ)
    (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    standardComplexVolume n v = (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.det v := by
  rw [standardComplexVolume, ContinuousAlternatingMap.coe_restrictScalars,
    Module.Basis.continuousDet_apply]

/-- Evaluating `standardComplexVolume n` on an `n`-tuple gives the determinant of the complex
matrix of its row coordinates. -/
theorem standardComplexVolume_apply (n : ℕ) (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    standardComplexVolume n v = (Matrix.of fun i j ↦ v i j).det := by
  have hv : v = fun i ↦ WithLp.toLp 2 (fun j ↦ v i j) := by
    ext i j; rfl
  rw [standardComplexVolume_eq_det_basisFun]
  conv_lhs => rw [hv]
  exact Matrix.basisFun_toBasis_det_toLp (Matrix.of fun i j ↦ v i j)

/-- On the standard complex orthonormal basis of `ℂⁿ`, the complex volume form evaluates to `1`. -/
@[simp]
theorem standardComplexVolume_basisFun (n : ℕ) :
    standardComplexVolume n (EuclideanSpace.basisFun (Fin n) ℂ) = 1 := by
  rw [standardComplexVolume_eq_det_basisFun]
  exact (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.det_self

/-- In dimension zero, `standardComplexVolume 0` is the constant `1`. -/
@[simp]
theorem standardComplexVolume_zero_apply (v : Fin 0 → EuclideanSpace ℂ (Fin 0)) :
    standardComplexVolume 0 v = 1 := by
  simp [standardComplexVolume_apply]

/-- In complex dimension one, `standardComplexVolume 1` reads the single complex coordinate. -/
theorem standardComplexVolume_one_apply (v : Fin 1 → EuclideanSpace ℂ (Fin 1)) :
    standardComplexVolume 1 v = v 0 0 := by
  simp [standardComplexVolume_apply]

/-- Although typed as an `ℝ`-multilinear map, `standardComplexVolume n` is `ℂ`-linear in every
slot. -/
@[simp]
theorem standardComplexVolume_update_smul (n : ℕ) (v : Fin n → EuclideanSpace ℂ (Fin n))
    (i : Fin n) (c : ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    standardComplexVolume n (Function.update v i (c • x)) =
      c * standardComplexVolume n (Function.update v i x) := by
  rw [standardComplexVolume_eq_det_basisFun, standardComplexVolume_eq_det_basisFun,
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.det.map_update_smul, smul_eq_mul]

/-- Scaling each vector of an `n`-frame by a complex scalar multiplies `standardComplexVolume n` by
the product of the scalars. -/
theorem standardComplexVolume_smul_univ (n : ℕ) (c : Fin n → ℂ)
    (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    standardComplexVolume n (fun i ↦ c i • v i) = (∏ i, c i) * standardComplexVolume n v := by
  rw [standardComplexVolume_eq_det_basisFun, standardComplexVolume_eq_det_basisFun,
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.det.map_smul_univ, smul_eq_mul]

/-- Pulling `standardComplexVolume n` back along a complex-linear endomorphism `L` multiplies by
the complex determinant `LinearMap.det L`. -/
theorem standardComplexVolume_comp_linearMap (n : ℕ)
    (L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))
    (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    standardComplexVolume n (L ∘ v) = LinearMap.det L * standardComplexVolume n v := by
  rw [standardComplexVolume_eq_det_basisFun, standardComplexVolume_eq_det_basisFun,
    (EuclideanSpace.basisFun (Fin n) ℂ).toBasis.det_comp]

/-- **Hadamard's inequality for the complex volume form**: `‖Ω v‖ ≤ ∏ i, ‖v i‖`. -/
theorem norm_standardComplexVolume_apply_le_prod_norm (n : ℕ)
    (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    ‖standardComplexVolume n v‖ ≤ ∏ i, ‖v i‖ := by
  rw [standardComplexVolume_eq_det_basisFun]
  exact (EuclideanSpace.basisFun (Fin n) ℂ).norm_det_le_prod_norm v

/-- Equality `‖Ω v‖ = ∏ i, ‖v i‖` holds if and only if some vector is zero or the vectors are
pairwise `ℂ`-orthogonal. -/
theorem norm_standardComplexVolume_apply_eq_prod_norm_iff (n : ℕ)
    (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    ‖standardComplexVolume n v‖ = ∏ i, ‖v i‖ ↔
      (∃ i, v i = 0) ∨ Pairwise fun i j ↦ ⟪v i, v j⟫_ℂ = 0 := by
  rw [standardComplexVolume_eq_det_basisFun]
  exact (EuclideanSpace.basisFun (Fin n) ℂ).norm_det_eq_prod_norm_iff v

/-- For an `n`-tuple of unit vectors in `ℂⁿ`, `‖Ω v‖ = 1` if and only if `v` is `ℂ`-orthonormal
(unitary). -/
theorem norm_standardComplexVolume_apply_eq_one_iff_orthonormal_complex (n : ℕ)
    {v : Fin n → EuclideanSpace ℂ (Fin n)} (hv : ∀ i, ‖v i‖ = 1) :
    ‖standardComplexVolume n v‖ = 1 ↔ Orthonormal ℂ v := by
  rw [standardComplexVolume_eq_det_basisFun]
  exact (EuclideanSpace.basisFun (Fin n) ℂ).norm_det_eq_one_iff_orthonormal hv

/-- When every vector of `v` has norm at most `1`, the complex volume form has modulus at most
`1`. -/
theorem norm_standardComplexVolume_apply_le_one (n : ℕ)
    {v : Fin n → EuclideanSpace ℂ (Fin n)} (hv : ∀ i, ‖v i‖ ≤ 1) :
    ‖standardComplexVolume n v‖ ≤ 1 := by
  calc ‖standardComplexVolume n v‖
      ≤ ∏ i, ‖v i‖ := norm_standardComplexVolume_apply_le_prod_norm n v
    _ ≤ ∏ _i : Fin n, (1 : ℝ) := by gcongr with i; exact hv i
    _ = 1 := by simp

/-- On an `ℝ`-orthonormal `n`-frame `v` in `ℂⁿ`, `‖Ω v‖ = 1` if and only if the span of `v` is
Lagrangian (`Im ⟪v i, v j⟫_ℂ = 0` for all `i, j`). -/
theorem norm_standardComplexVolume_apply_eq_one_iff (n : ℕ)
    {v : Fin n → EuclideanSpace ℂ (Fin n)} (hv : Orthonormal ℝ v) :
    ‖standardComplexVolume n v‖ = 1 ↔ ∀ i j, (⟪v i, v j⟫_ℂ).im = 0 := by
  rw [norm_standardComplexVolume_apply_eq_one_iff_orthonormal_complex n hv.1,
    hv.complex_iff_forall_im_inner_eq_zero]

/-- The operator norm (comass) of `standardComplexVolume n` equals `1` in every dimension `n`,
including `n = 0`. -/
@[simp]
theorem norm_standardComplexVolume (n : ℕ) : ‖standardComplexVolume n‖ = 1 := by
  refine le_antisymm ?_ ?_
  · exact (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal zero_le_one).mpr fun v hv ↦
      norm_standardComplexVolume_apply_le_one n fun i ↦ (hv.1 i).le
  · let b : Fin n → EuclideanSpace ℂ (Fin n) := EuclideanSpace.basisFun (Fin n) ℂ
    have hb : ∀ i, ‖b i‖ = 1 := (EuclideanSpace.basisFun (Fin n) ℂ).orthonormal.1
    simpa [b, hb] using (standardComplexVolume n).le_opNorm b

/-- The modulus of `Ω v` is bounded by the real `n`-dimensional parallelepiped volume
`‖v₁ ∧ ⋯ ∧ vₙ‖` of `v`. -/
theorem norm_standardComplexVolume_apply_le_norm_ιMulti (n : ℕ)
    (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    ‖standardComplexVolume n v‖ ≤ ‖exteriorPower.ιMulti ℝ n v‖ := by
  simpa using (standardComplexVolume n).le_opNorm_mul_norm_ιMulti v

/-! ### The standard special Lagrangian calibration form -/

/-- The special Lagrangian form of phase `θ` on `ℂⁿ`: `φ_θ v = Re (e^(−iθ) Ω v)`. -/
def standardSpecialLagrangianForm (n : ℕ) (θ : ℝ) :
    EuclideanSpace ℂ (Fin n) [⋀^Fin n]→L[ℝ] ℝ :=
  (Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ (Complex.exp (-(θ : ℂ) * Complex.I))))
    |>.compContinuousAlternatingMap (standardComplexVolume n)

/-- Pointwise formula for `standardSpecialLagrangianForm`: `φ_θ v = Re(e^(-iθ) Ω v)`. -/
theorem standardSpecialLagrangianForm_apply (n : ℕ) (θ : ℝ)
    (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    standardSpecialLagrangianForm n θ v =
      (Complex.exp (-(θ : ℂ) * Complex.I) * standardComplexVolume n v).re :=
  (rfl)

/-- Trigonometric expansion `φ_θ v = cos θ Re(Ω v) + sin θ Im(Ω v)`. -/
theorem standardSpecialLagrangianForm_apply_eq_cos_mul_re_add_sin_mul_im (n : ℕ) (θ : ℝ)
    (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    standardSpecialLagrangianForm n θ v =
      Real.cos θ * (standardComplexVolume n v).re +
        Real.sin θ * (standardComplexVolume n v).im := by
  have hre : (Complex.exp (-(θ : ℂ) * Complex.I)).re = Real.cos θ := by
    simpa using Complex.exp_ofReal_mul_I_re (-θ)
  have him : (Complex.exp (-(θ : ℂ) * Complex.I)).im = -Real.sin θ := by
    simpa using Complex.exp_ofReal_mul_I_im (-θ)
  rw [standardSpecialLagrangianForm_apply, Complex.mul_re, hre, him]
  ring

/-- At phase `0`, `standardSpecialLagrangianForm n 0` is `Re Ω`. -/
@[simp]
theorem standardSpecialLagrangianForm_zero_right_apply (n : ℕ)
    (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    standardSpecialLagrangianForm n 0 v = (standardComplexVolume n v).re := by
  simp [standardSpecialLagrangianForm_apply]

/-- Shifting the phase by `π` reverses the sign of `standardSpecialLagrangianForm`. -/
@[simp]
theorem standardSpecialLagrangianForm_add_pi (n : ℕ) (θ : ℝ) :
    standardSpecialLagrangianForm n (θ + Real.pi) = -standardSpecialLagrangianForm n θ := by
  ext v
  simp only [ContinuousAlternatingMap.neg_apply,
    standardSpecialLagrangianForm_apply_eq_cos_mul_re_add_sin_mul_im,
    Real.cos_add_pi, Real.sin_add_pi]
  ring

/-- `standardSpecialLagrangianForm n θ` is `2π`-periodic in the phase `θ`. -/
@[simp]
theorem standardSpecialLagrangianForm_add_two_pi (n : ℕ) (θ : ℝ) :
    standardSpecialLagrangianForm n (θ + 2 * Real.pi) = standardSpecialLagrangianForm n θ := by
  ext v
  simp [standardSpecialLagrangianForm_apply_eq_cos_mul_re_add_sin_mul_im,
    Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Shifting the phase by `π / 2` gives the imaginary part `Im(e^(-iθ) Ω v)`. -/
theorem standardSpecialLagrangianForm_add_pi_div_two_apply (n : ℕ) (θ : ℝ)
    (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    standardSpecialLagrangianForm n (θ + Real.pi / 2) v =
      (Complex.exp (-(θ : ℂ) * Complex.I) * standardComplexVolume n v).im := by
  have hre : (Complex.exp (-(θ : ℂ) * Complex.I)).re = Real.cos θ := by
    simpa using Complex.exp_ofReal_mul_I_re (-θ)
  have him : (Complex.exp (-(θ : ℂ) * Complex.I)).im = -Real.sin θ := by
    simpa using Complex.exp_ofReal_mul_I_im (-θ)
  rw [standardSpecialLagrangianForm_apply_eq_cos_mul_re_add_sin_mul_im,
    Complex.mul_im, hre, him, Real.cos_add_pi_div_two, Real.sin_add_pi_div_two]
  ring

/-- At phase `π / 2`, `standardSpecialLagrangianForm n (π / 2)` is `Im Ω`. -/
@[simp]
theorem standardSpecialLagrangianForm_pi_div_two_apply (n : ℕ)
    (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    standardSpecialLagrangianForm n (Real.pi / 2) v = (standardComplexVolume n v).im := by
  simpa using standardSpecialLagrangianForm_add_pi_div_two_apply n 0 v

/-- In dimension zero, `standardSpecialLagrangianForm 0 θ` is the constant `cos θ`. -/
@[simp]
theorem standardSpecialLagrangianForm_zero_left_apply (θ : ℝ)
    (v : Fin 0 → EuclideanSpace ℂ (Fin 0)) :
    standardSpecialLagrangianForm 0 θ v = Real.cos θ := by
  simp [standardSpecialLagrangianForm_apply_eq_cos_mul_re_add_sin_mul_im]

/-- In complex dimension one, `standardSpecialLagrangianForm 1 θ` evaluates to
`Re(e^(-iθ) v 0 0)`. -/
theorem standardSpecialLagrangianForm_one_apply (θ : ℝ)
    (v : Fin 1 → EuclideanSpace ℂ (Fin 1)) :
    standardSpecialLagrangianForm 1 θ v =
      (Complex.exp (-(θ : ℂ) * Complex.I) * v 0 0).re := by
  rw [standardSpecialLagrangianForm_apply, standardComplexVolume_one_apply]

/-- Pulling `standardSpecialLagrangianForm n θ` back along a complex-linear endomorphism `L` with
`det L = e^(iα)` shifts the phase to `θ - α`. -/
theorem standardSpecialLagrangianForm_comp_linearMap_of_det_eq_exp (n : ℕ) (θ α : ℝ)
    {L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)}
    (hL : LinearMap.det L = Complex.exp ((α : ℂ) * Complex.I))
    (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    standardSpecialLagrangianForm n θ (L ∘ v) =
      standardSpecialLagrangianForm n (θ - α) v := by
  have hexp :
      -(θ : ℂ) * Complex.I + (α : ℂ) * Complex.I = -((θ - α : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  simp only [standardSpecialLagrangianForm_apply, standardComplexVolume_comp_linearMap, hL,
    ← mul_assoc, ← Complex.exp_add, hexp]

/-- `SL(n, ℂ)`-invariance (and hence `SU(n)`-invariance) of `standardSpecialLagrangianForm`: pulling
back along a complex-linear endomorphism of complex determinant `1` preserves `φ_θ`. -/
theorem standardSpecialLagrangianForm_comp_linearMap_of_det_eq_one (n : ℕ) (θ : ℝ)
    {L : EuclideanSpace ℂ (Fin n) →ₗ[ℂ] EuclideanSpace ℂ (Fin n)}
    (hL : LinearMap.det L = 1)
    (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    standardSpecialLagrangianForm n θ (L ∘ v) =
      standardSpecialLagrangianForm n θ v := by
  simpa using standardSpecialLagrangianForm_comp_linearMap_of_det_eq_exp n θ 0
    (by simpa using hL) v

/-- Pointwise bound `|φ_θ v| ≤ ‖Ω v‖`. -/
theorem abs_standardSpecialLagrangianForm_apply_le_norm_standardComplexVolume (n : ℕ) (θ : ℝ)
    (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    |standardSpecialLagrangianForm n θ v| ≤ ‖standardComplexVolume n v‖ := by
  have hnorm : ‖Complex.exp (-(θ : ℂ) * Complex.I)‖ = 1 := by
    simpa using Complex.norm_exp_ofReal_mul_I (-θ)
  calc
    |standardSpecialLagrangianForm n θ v|
      ≤ ‖Complex.exp (-(θ : ℂ) * Complex.I) * standardComplexVolume n v‖ :=
        Complex.abs_re_le_norm _
    _ = ‖standardComplexVolume n v‖ := by rw [norm_mul, hnorm, one_mul]

/-- **Linear calibration bound** for `standardSpecialLagrangianForm` against the real wedge volume:
`|φ_θ v| ≤ ‖v₁ ∧ ⋯ ∧ vₙ‖`. -/
theorem abs_standardSpecialLagrangianForm_apply_le_norm_ιMulti (n : ℕ) (θ : ℝ)
    (v : Fin n → EuclideanSpace ℂ (Fin n)) :
    |standardSpecialLagrangianForm n θ v| ≤ ‖exteriorPower.ιMulti ℝ n v‖ :=
  (abs_standardSpecialLagrangianForm_apply_le_norm_standardComplexVolume n θ v).trans
    (norm_standardComplexVolume_apply_le_norm_ιMulti n v)

/-- The operator norm (comass) of `standardSpecialLagrangianForm n θ` is at most `1` in every
dimension `n`, including `n = 0`. -/
theorem norm_standardSpecialLagrangianForm_le_one (n : ℕ) (θ : ℝ) :
    ‖standardSpecialLagrangianForm n θ‖ ≤ 1 := by
  refine (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal zero_le_one).mpr fun v hv ↦ ?_
  rw [Real.norm_eq_abs]
  exact (abs_standardSpecialLagrangianForm_apply_le_norm_standardComplexVolume n θ v).trans
    (norm_standardComplexVolume_apply_le_one n fun i ↦ (hv.1 i).le)

/-- In dimension zero, `standardSpecialLagrangianForm 0 θ` has operator norm `|cos θ|`, showing that
`1 ≤ n` is required in `norm_standardSpecialLagrangianForm`. -/
@[simp]
theorem norm_standardSpecialLagrangianForm_zero (θ : ℝ) :
    ‖standardSpecialLagrangianForm 0 θ‖ = |Real.cos θ| := by
  refine le_antisymm ?_ ?_
  · refine (ContinuousAlternatingMap.opNorm_le_iff_le_orthonormal (abs_nonneg _)).mpr fun v _ ↦ ?_
    simp
  · simpa using (standardSpecialLagrangianForm 0 θ).le_opNorm ![]

/-- When `1 ≤ n`, there exists a `ℂ`-orthonormal `n`-frame in `ℂⁿ` on which
`standardSpecialLagrangianForm n θ` evaluates to `1`. -/
theorem exists_orthonormal_complex_standardSpecialLagrangianForm_apply_eq_one
    {n : ℕ} (hn : 1 ≤ n) (θ : ℝ) :
    ∃ v : Fin n → EuclideanSpace ℂ (Fin n),
      Orthonormal ℂ v ∧ standardSpecialLagrangianForm n θ v = 1 := by
  -- Rotate the first vector of the standard complex basis by `e^(iθ)`.
  let b : Fin n → EuclideanSpace ℂ (Fin n) := EuclideanSpace.basisFun (Fin n) ℂ
  have hb : Orthonormal ℂ b := (EuclideanSpace.basisFun (Fin n) ℂ).orthonormal
  let i₀ : Fin n := ⟨0, hn⟩
  let u : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hu : ‖u‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  let v : Fin n → EuclideanSpace ℂ (Fin n) := Function.update b i₀ (u • b i₀)
  refine ⟨v, ⟨fun i ↦ ?_, fun {i j} hij ↦ ?_⟩, ?_⟩
  · by_cases hi : i = i₀
    · subst hi; simp [v, norm_smul, hu, hb.1 i₀]
    · simp [v, hi, hb.1 i]
  · dsimp only
    by_cases hi : i = i₀ <;> by_cases hj : j = i₀
    · exact absurd (hi.trans hj.symm) hij
    · subst hi; simp [v, hj, inner_smul_left, hb.2 hij]
    · subst hj; simp [v, hi, inner_smul_right, hb.2 hij]
    · simp [v, hi, hj, hb.2 hij]
  · have hΩ : standardComplexVolume n v = u := by
      dsimp only [v]
      rw [standardComplexVolume_update_smul, Function.update_eq_self]
      simp [b]
    have hmul : Complex.exp (-(θ : ℂ) * Complex.I) * u = 1 := by
      dsimp only [u]
      rw [← Complex.exp_add]
      simp
    rw [standardSpecialLagrangianForm_apply, hΩ, hmul, Complex.one_re]

/-- For `n ≥ 1` the special Lagrangian form of every phase has comass one
(Harvey–Lawson 1982, Theorem III.1.10). -/
theorem norm_standardSpecialLagrangianForm (n : ℕ) (hn : 1 ≤ n) (θ : ℝ) :
    ‖standardSpecialLagrangianForm n θ‖ = 1 := by
  refine le_antisymm (norm_standardSpecialLagrangianForm_le_one n θ) ?_
  obtain ⟨v, hv, hval⟩ := exists_orthonormal_complex_standardSpecialLagrangianForm_apply_eq_one hn θ
  have hle := (standardSpecialLagrangianForm n θ).le_opNorm v
  simpa [hv.1, hval] using hle

/-- Simp version of `norm_standardSpecialLagrangianForm` for positive dimensions `n + 1`. -/
@[simp]
theorem norm_standardSpecialLagrangianForm_succ (n : ℕ) (θ : ℝ) :
    ‖standardSpecialLagrangianForm (n + 1) θ‖ = 1 :=
  norm_standardSpecialLagrangianForm (n + 1) (Nat.succ_pos n) θ

/-! ### Characterization of special Lagrangian frames and planes -/

/-- For an `n`-tuple `v` in `ℂⁿ` of vectors of norm at most `1`, `φ_θ v = 1` if and only if its
complex determinant `Ω v` equals `e^(iθ)`. Holds in every dimension `n`, including `n = 0`. -/
theorem standardSpecialLagrangianForm_apply_eq_one_iff_standardComplexVolume_eq (n : ℕ) (θ : ℝ)
    {v : Fin n → EuclideanSpace ℂ (Fin n)} (hv : ∀ i, ‖v i‖ ≤ 1) :
    standardSpecialLagrangianForm n θ v = 1 ↔
      standardComplexVolume n v = Complex.exp ((θ : ℂ) * Complex.I) := by
  set z : ℂ := Complex.exp (-(θ : ℂ) * Complex.I) * standardComplexVolume n v
  have hexp_mul :
      Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-(θ : ℂ) * Complex.I) = 1 := by
    rw [← Complex.exp_add]
    simp
  have hexp_mul' :
      Complex.exp (-(θ : ℂ) * Complex.I) * Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
    rw [mul_comm]
    exact hexp_mul
  refine ⟨fun hre ↦ ?_, fun hΩ ↦ ?_⟩
  · have hnorm_z : ‖z‖ ≤ 1 := by
      have hnorm : ‖Complex.exp (-(θ : ℂ) * Complex.I)‖ = 1 := by
        simpa using Complex.norm_exp_ofReal_mul_I (-θ)
      dsimp only [z]
      rw [norm_mul, hnorm, one_mul]
      exact norm_standardComplexVolume_apply_le_one n hv
    have hre' : z.re = 1 := by simpa [standardSpecialLagrangianForm_apply, z] using hre
    have hz : z = 1 := by
      simpa [hre'] using (RCLike.re_eq_self_of_le (K := ℂ) (hnorm_z.trans_eq hre'.symm)).symm
    calc
      standardComplexVolume n v
        = Complex.exp ((θ : ℂ) * Complex.I) * z := by
            dsimp only [z]
            rw [← mul_assoc, hexp_mul, one_mul]
      _ = Complex.exp ((θ : ℂ) * Complex.I) := by rw [hz, mul_one]
  · rw [standardSpecialLagrangianForm_apply, hΩ, hexp_mul', Complex.one_re]

/-- The equality planes of the special Lagrangian form: a real-orthonormal ordered frame `v` of
`n` vectors in `ℂⁿ` satisfies `φ_θ v = 1` exactly when it spans a Lagrangian plane
(`Im ⟪v i, v j⟫_ℂ = 0` for all `i, j`), `Im (e^(−iθ) Ω v) = 0`, and the orientation is positive,
`Re (e^(−iθ) Ω v) > 0` (Harvey–Lawson 1982, Cor. III.1.11; Joyce 2005, Propositions 2.3 and 2.4).
Holds for every `n`, including `n = 0`. -/
theorem specialLagrangianFrame_iff (n : ℕ) (θ : ℝ)
    (v : Fin n → EuclideanSpace ℂ (Fin n)) (hv : Orthonormal ℝ v) :
    standardSpecialLagrangianForm n θ v = 1 ↔
      (∀ i j, (inner ℂ (v i) (v j)).im = 0) ∧
      (Complex.exp (-(θ : ℂ) * Complex.I) * standardComplexVolume n v).im = 0 ∧
      0 < (Complex.exp (-(θ : ℂ) * Complex.I) * standardComplexVolume n v).re := by
  set z : ℂ := Complex.exp (-(θ : ℂ) * Complex.I) * standardComplexVolume n v with hz_def
  have hnorm_exp : ‖Complex.exp (-(θ : ℂ) * Complex.I)‖ = 1 := by
    simpa using Complex.norm_exp_ofReal_mul_I (-θ)
  refine ⟨fun h1 ↦ ?_, fun ⟨hlag, him, hpos⟩ ↦ ?_⟩
  · have hΩ :=
      (standardSpecialLagrangianForm_apply_eq_one_iff_standardComplexVolume_eq n θ
        fun i ↦ (hv.1 i).le).mp h1
    have hnorm_Ω : ‖standardComplexVolume n v‖ = 1 := by
      rw [hΩ]
      exact Complex.norm_exp_ofReal_mul_I θ
    have hz : z = 1 := by
      rw [hz_def, hΩ, ← Complex.exp_add]
      simp
    exact ⟨(norm_standardComplexVolume_apply_eq_one_iff n hv).mp hnorm_Ω,
      by simp [hz], by simp [hz]⟩
  · have hnorm_Ω : ‖standardComplexVolume n v‖ = 1 :=
      (norm_standardComplexVolume_apply_eq_one_iff n hv).mpr hlag
    have hnorm_z : ‖z‖ = 1 := by
      rw [hz_def, norm_mul, hnorm_exp, hnorm_Ω, mul_one]
    rw [standardSpecialLagrangianForm_apply, ← hz_def]
    simpa [abs_of_pos hpos, hnorm_z] using Complex.abs_re_eq_norm.mpr him

/-- **Calibrated-plane criterion for arbitrary linearly independent frames**: an `ℝ`-linearly
independent `n`-frame `v` in `ℂⁿ` achieves equality `φ_θ v = ‖v₁ ∧ ⋯ ∧ vₙ‖` in the calibration
inequality if and only if `Im ⟪v i, v j⟫_ℂ = 0` for all `i, j`, `Im(e^(-iθ) Ω v) = 0`, and
`0 < Re(e^(-iθ) Ω v)`. -/
theorem standardSpecialLagrangianForm_apply_eq_norm_ιMulti_iff (n : ℕ) (θ : ℝ)
    {v : Fin n → EuclideanSpace ℂ (Fin n)} (hv : LinearIndependent ℝ v) :
    standardSpecialLagrangianForm n θ v = ‖exteriorPower.ιMulti ℝ n v‖ ↔
      (∀ i j, (⟪v i, v j⟫_ℂ).im = 0) ∧
      (Complex.exp (-(θ : ℂ) * Complex.I) * standardComplexVolume n v).im = 0 ∧
      0 < (Complex.exp (-(θ : ℂ) * Complex.I) * standardComplexVolume n v).re := by
  set W := Submodule.span ℝ (Set.range v)
  have : FiniteDimensional ℝ W := FiniteDimensional.span_of_finite ℝ (Set.finite_range v)
  let w : Fin n → W := fun i ↦ ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hdim : Module.finrank ℝ W = Fintype.card (Fin n) := finrank_span_eq_card hv
  let e : OrthonormalBasis (Fin n) ℝ W := InnerProductSpace.gramSchmidtOrthonormalBasis hdim w
  let u : Fin n → EuclideanSpace ℂ (Fin n) := fun i ↦ (e i : EuclideanSpace ℂ (Fin n))
  have hu_orth : Orthonormal ℝ u := e.orthonormal.comp_linearIsometry W.subtypeₗᵢ
  -- `e.toBasis.det w` is positive and equals `‖v₁ ∧ ⋯ ∧ vₙ‖`.
  have hdet_nonneg : 0 ≤ e.toBasis.det w := by
    rw [InnerProductSpace.gramSchmidtOrthonormalBasis_det]
    refine Finset.prod_nonneg fun i _ ↦ ?_
    by_cases hi : InnerProductSpace.gramSchmidtNormed ℝ w i = 0
    · rw [InnerProductSpace.inner_gramSchmidtOrthonormalBasis_eq_zero hdim hi]
    · rw [InnerProductSpace.gramSchmidtOrthonormalBasis_apply hdim hi,
        InnerProductSpace.inner_gramSchmidtNormed_eq_norm]
      simp
  have hdet_eq : e.toBasis.det w = ‖exteriorPower.ιMulti ℝ n v‖ := by
    have hgram : Matrix.gram ℝ w = Matrix.gram ℝ v := by
      ext i j; simp [Matrix.gram, w]
    refine (pow_left_inj₀ hdet_nonneg (norm_nonneg _) two_ne_zero).mp ?_
    rw [exteriorPower.norm_ιMulti_sq, ← hgram]
    simpa [Real.norm_eq_abs, sq_abs] using (e.det_gram_eq_norm_det_sq w).symm
  have hdet_pos : 0 < ‖exteriorPower.ιMulti ℝ n v‖ :=
    norm_pos_iff.mpr ((exteriorPower.ιMulti_ne_zero_iff v).mpr hv)
  -- `Ω` restricts to a top-degree `ℝ`-alternating form on `W`, scaling by `e.toBasis.det w`.
  let ΩW : W [⋀^Fin n]→ₗ[ℝ] ℂ :=
    (standardComplexVolume n).toAlternatingMap.compLinearMap W.subtype
  have hΩ_scale : standardComplexVolume n v =
      (‖exteriorPower.ιMulti ℝ n v‖ : ℂ) * standardComplexVolume n u := by
    have h :=
      congrFun (congrArg DFunLike.coe (AlternatingMap.eq_basis_det_smulRight e.toBasis ΩW)) w
    simpa [ΩW, w, u, hdet_eq, e.coe_toBasis, Function.comp_def, Complex.real_smul] using h
  have hz_scale :
      Complex.exp (-(θ : ℂ) * Complex.I) * standardComplexVolume n v =
        (‖exteriorPower.ιMulti ℝ n v‖ : ℂ) *
          (Complex.exp (-(θ : ℂ) * Complex.I) * standardComplexVolume n u) := by
    rw [hΩ_scale]; ring
  have hspan : Submodule.span ℝ (Set.range u) = W := by
    have hu_range : Set.range u = W.subtype '' Set.range e.toBasis := by
      rw [e.coe_toBasis, ← Set.range_comp]
      rfl
    rw [hu_range, ← Submodule.map_span, e.toBasis.span_eq, Submodule.map_top, W.range_subtype]
  have hlag_iff : (∀ i j, (⟪v i, v j⟫_ℂ).im = 0) ↔ ∀ i j, (⟪u i, u j⟫_ℂ).im = 0 :=
    ⟨fun h i j ↦ (Pairwise.range_pairwise (f := v) fun a b _ ↦ h a b).im_inner_eq_zero_of_mem_span
        (e i).2 (e j).2,
      fun h i j ↦ (Pairwise.range_pairwise (f := u) fun a b _ ↦ h a b).im_inner_eq_zero_of_mem_span
        (hspan.symm ▸ Submodule.subset_span (Set.mem_range_self i))
        (hspan.symm ▸ Submodule.subset_span (Set.mem_range_self j))⟩
  have hφ_scale : standardSpecialLagrangianForm n θ v =
      ‖exteriorPower.ιMulti ℝ n v‖ * standardSpecialLagrangianForm n θ u := by
    rw [standardSpecialLagrangianForm_apply, standardSpecialLagrangianForm_apply, hz_scale,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have him_iff :
      (Complex.exp (-(θ : ℂ) * Complex.I) * standardComplexVolume n v).im = 0 ↔
        (Complex.exp (-(θ : ℂ) * Complex.I) * standardComplexVolume n u).im = 0 := by
    rw [hz_scale, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      mul_eq_zero_iff_left hdet_pos.ne']
  have hre_iff :
      0 < (Complex.exp (-(θ : ℂ) * Complex.I) * standardComplexVolume n v).re ↔
        0 < (Complex.exp (-(θ : ℂ) * Complex.I) * standardComplexVolume n u).re := by
    rw [hz_scale, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      mul_pos_iff_of_pos_left hdet_pos]
  rw [hφ_scale, mul_eq_left₀ hdet_pos.ne', specialLagrangianFrame_iff n θ u hu_orth,
    hlag_iff, him_iff, hre_iff]

end TauCeti

end
