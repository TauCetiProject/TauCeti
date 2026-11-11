/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.PosSemidef
public import TauCeti.Analysis.PositiveDefinite.AddGroup
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import TauCeti.Analysis.SpecialFunctions.Exp.Deriv

/-!
# Fourier atoms

This file records the spatial Fourier atom used by the positive-definite and Bochner APIs.
It uses Mathlib's `2π` Fourier convention.

## Main declarations

* `TauCeti.fourierAtom`: the spatial atom `v ↦ exp (-2πi⟪v, q⟫)`.
* `TauCeti.posSemidef_fourierAtom`: the subtraction kernel attached to a
  Fourier atom is positive definite.
* `TauCeti.continuous_fourierAtom`: Fourier atoms are continuous in the spatial variable.
* `TauCeti.contDiff_fourierAtom`: Fourier atoms are smooth in the spatial variable.
* `TauCeti.contDiff_uncurry_fourierAtom`: Fourier atoms are jointly smooth in the frequency and
  the spatial variable.
* `TauCeti.norm_iteratedFDeriv_fourierAtom_le`: the `k`-th derivative of the Fourier atom at
  frequency `q` has norm at most `(2π ‖q‖) ^ k`.
* `TauCeti.contDiff_tsum_mul_fourierAtom`: a series of Fourier atoms whose coefficients decay
  faster than every power of the frequency is smooth.
* `TauCeti.integral_mul_tsum_mul_fourierAtom`: a compactly supported continuous function is
  integrated against an absolutely convergent series of Fourier atoms term by term, giving values
  of its Fourier transform.
* `TauCeti.continuous_and_isPositiveDefiniteSub_fourierAtom`: the Fourier atom
  `v ↦ fourierAtom v ξ` is continuous and positive definite.
* `TauCeti.norm_fourierAtom`: Fourier atoms have unit norm.
* `TauCeti.integrable_fourierAtom`: Fourier atoms are integrable against a finite measure.
* `TauCeti.fourierAtom_add_left` and `TauCeti.fourierAtom_add_right`: a Fourier atom is an
  additive character of each argument.
* `TauCeti.fourierAtom_zero_left` and `TauCeti.fourierAtom_zero_right`: a Fourier atom is `1`
  when either argument is `0`.
-/

public section

open Complex ComplexConjugate
open scoped ComplexOrder

namespace TauCeti

variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Fourier atom at frequency `q`, using Mathlib's `2π` Fourier convention. -/
public noncomputable def fourierAtom (q : V) (v : V) : ℂ :=
  (Real.fourierChar (-(inner ℝ v q)) : ℂ)

/-- The `Real.fourierChar` form of a Fourier atom. -/
theorem fourierAtom_eq_fourierChar (q : V) (v : V) :
    fourierAtom q v = (Real.fourierChar (-(inner ℝ v q)) : ℂ) :=
  by simp [fourierAtom]

/-- The raw exponential form of a Fourier atom. -/
@[simp]
theorem fourierAtom_apply (q : V) (v : V) :
    fourierAtom q v =
      Complex.exp (-2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ v q : ℝ) : ℂ)) := by
  rw [fourierAtom_eq_fourierChar, Real.fourierChar_apply]
  congr 1
  norm_num [Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- A Fourier atom at the zero frequency is `1`.

Not a `@[simp]` lemma: `simp` already proves it through `fourierAtom_apply`, and the simpNF
linter reports the tagged form as a duplicate. -/
theorem fourierAtom_zero_left (v : V) : fourierAtom (0 : V) v = 1 := by
  simp [fourierAtom]

/-- A Fourier atom evaluated at the zero point is `1`. Not a `@[simp]` lemma, for the same
reason as `fourierAtom_zero_left`. -/
theorem fourierAtom_zero_right (q : V) : fourierAtom q (0 : V) = 1 := by
  simp [fourierAtom]

/-- A Fourier atom is an additive character of its first argument. -/
theorem fourierAtom_add_left (q r v : V) :
    fourierAtom (q + r) v = fourierAtom q v * fourierAtom r v := by
  simp only [fourierAtom, inner_add_right, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]

/-- A Fourier atom is an additive character of its second argument. -/
theorem fourierAtom_add_right (q v w : V) :
    fourierAtom q (v + w) = fourierAtom q v * fourierAtom q w := by
  simp only [fourierAtom, inner_add_left, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]

/-- Fourier atoms turn spatial subtraction into a rank-one positive-definite kernel. -/
theorem fourierAtom_sub (q v w : V) :
    fourierAtom q (v - w) =
      conj (Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ v q : ℝ) : ℂ))) *
        Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ w q : ℝ) : ℂ)) := by
  rw [fourierAtom_apply]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [inner_sub_left, Complex.ofReal_sub, map_mul, map_ofNat, Complex.conj_ofReal,
    Complex.conj_I]
  ring_nf

/-- The spatial subtraction kernel supplied by a Fourier atom is positive definite. -/
theorem posSemidef_fourierAtom (q : V) :
    Matrix.PosSemidef fun v w : V => fourierAtom q (v - w) := by
  simp_rw [fourierAtom_sub]
  simpa only [RCLike.star_def] using posSemidef_rankOne
    (fun v : V => Complex.exp (2 * ((Real.pi : ℝ) : ℂ) * Complex.I * ((inner ℝ v q : ℝ) : ℂ)))

/-- Fourier atoms take values on the unit circle.

Not a `@[simp]` lemma: `simp` rewrites the atom through `fourierAtom_apply` first, and the
simpNF linter reports the tagged form as unusable for the same reason as
`fourierAtom_zero_left`. -/
theorem norm_fourierAtom (q v : V) : ‖fourierAtom q v‖ = 1 := by
  rw [fourierAtom_eq_fourierChar, Circle.norm_coe]

/-- Fourier atoms are continuous in the spatial variable. -/
theorem continuous_fourierAtom (q : V) : Continuous (fourierAtom q) := by
  convert
    (by fun_prop :
      Continuous fun v : V => ((Real.fourierChar (-(inner ℝ v q)) : Circle) : ℂ)) using 1
  ext v
  exact (fourierAtom_eq_fourierChar q v).symm

section ContDiff

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] {n : WithTop ℕ∞}

/-- Fourier atoms are jointly smooth in the frequency and the spatial variable. -/
theorem contDiff_uncurry_fourierAtom : ContDiff ℝ n (Function.uncurry (fourierAtom (V := W))) := by
  simp_rw [Function.uncurry_def, fourierAtom_eq_fourierChar, Real.fourierChar_apply]
  exact Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul (contDiff_inner.comp (contDiff_snd.prodMk contDiff_fst)).neg)).mul
        contDiff_const)

/-- Fourier atoms are smooth in the spatial variable. -/
theorem contDiff_fourierAtom (q : W) : ContDiff ℝ n (fourierAtom q) :=
  contDiff_uncurry_fourierAtom.comp (contDiff_const.prodMk contDiff_id)

/-- The `k`-th derivative of the Fourier atom at frequency `q` has norm at most
`(2π ‖q‖) ^ k`. -/
theorem norm_iteratedFDeriv_fourierAtom_le (q x : W) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fourierAtom q) x‖ ≤ (2 * Real.pi * ‖q‖) ^ k := by
  -- The atom is `exp ∘ ℓ` for the purely imaginary linear phase `ℓ y = -2πi ⟪y, q⟫`.
  let ℓ : W →L[ℝ] ℂ := (-2 * Real.pi * Complex.I) • (Complex.ofRealCLM.comp (innerSL ℝ q))
  have hℓ (y : W) : ℓ y = -2 * Real.pi * Complex.I * ((inner ℝ y q : ℝ) : ℂ) := by
    simp [ℓ, real_inner_comm]
  have hfun : fourierAtom q = fun y ↦ Complex.exp (ℓ y) := by
    ext y
    rw [fourierAtom_apply, hℓ]
  have hnorm : ‖ℓ‖ ≤ 2 * Real.pi * ‖q‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y ↦ ?_
    rw [hℓ]
    simp only [norm_mul, norm_neg, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_I, mul_one, abs_of_pos Real.pi_pos]
    have := abs_real_inner_le_norm y q
    nlinarith [Real.pi_pos, norm_nonneg y, norm_nonneg q, abs_nonneg (inner ℝ y q)]
  rw [hfun]
  refine (ℓ.norm_iteratedFDeriv_cexp_comp_le k x).trans ?_
  rw [show Complex.exp (ℓ x) = fourierAtom q x by rw [hfun], norm_fourierAtom, one_mul]
  gcongr

open scoped ContDiff in
/-- A series `x ↦ ∑' i, c i * fourierAtom (q i) x` of Fourier atoms is smooth when its coefficients
decay faster than every power of the frequencies: `∑ ‖c i‖ ‖q i‖ ^ k < ∞` for every `k`. -/
theorem contDiff_tsum_mul_fourierAtom {ι : Type*} (q : ι → W) (c : ι → ℂ)
    (h : ∀ k : ℕ, Summable fun i ↦ ‖c i‖ * ‖q i‖ ^ k) :
    ContDiff ℝ ∞ fun x ↦ ∑' i, c i * fourierAtom (q i) x := by
  refine contDiff_tsum (N := ⊤) (v := fun k i ↦ (2 * Real.pi) ^ k * (‖c i‖ * ‖q i‖ ^ k))
    (fun i ↦ contDiff_const.mul (contDiff_fourierAtom _)) (fun k _ ↦ (h k).mul_left _)
    fun k i x _ ↦ ?_
  have hi : (fun x ↦ c i * fourierAtom (q i) x) = c i • fourierAtom (q i) := by
    ext x
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [hi, iteratedFDeriv_const_smul_apply (contDiff_fourierAtom _).contDiffAt, norm_smul]
  calc ‖c i‖ * ‖iteratedFDeriv ℝ k (fourierAtom (q i)) x‖
      ≤ ‖c i‖ * (2 * Real.pi * ‖q i‖) ^ k := by
        gcongr
        exact norm_iteratedFDeriv_fourierAtom_le _ _ _
    _ = (2 * Real.pi) ^ k * (‖c i‖ * ‖q i‖ ^ k) := by ring

end ContDiff

section Integral

open MeasureTheory
open scoped FourierTransform

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- **Term-by-term integration against a series of Fourier atoms.** For a compactly supported
continuous function `u` and absolutely summable coefficients `c`,
`∫ u x ∑' i, c i fourierAtom (q i) x = ∑' i, c i 𝓕 u (q i)`. -/
theorem integral_mul_tsum_mul_fourierAtom {ι : Type*} [Countable ι] (q : ι → W) {c : ι → ℂ}
    (hc : Summable fun i ↦ ‖c i‖) {u : W → ℂ} (hu : Continuous u) (hus : HasCompactSupport u) :
    ∫ x, u x * ∑' i, c i * fourierAtom (q i) x = ∑' i, c i * 𝓕 u (q i) := by
  have hG (i : ι) : Integrable fun x ↦ u x * (c i * fourierAtom (q i) x) :=
    (hu.mul (continuous_const.mul (continuous_fourierAtom _))).integrable_of_hasCompactSupport
      hus.mul_right
  have hnorm (i : ι) : ∫ x, ‖u x * (c i * fourierAtom (q i) x)‖ = ‖c i‖ * ∫ x, ‖u x‖ := by
    rw [← integral_const_mul]
    congr 1
    ext x
    rw [norm_mul, norm_mul, norm_fourierAtom, mul_one, mul_comm]
  simp_rw [← tsum_mul_left (a := u _)]
  rw [← integral_tsum_of_summable_integral_norm hG (by simpa only [hnorm] using hc.mul_right _)]
  refine tsum_congr fun i ↦ ?_
  rw [Real.fourier_eq, ← integral_const_mul]
  congr 1
  ext x
  rw [fourierAtom_eq_fourierChar, Circle.smul_def, smul_eq_mul]
  ring

end Integral

/-- The Fourier atom `v ↦ fourierAtom v ξ` is continuous and positive definite: by symmetry of
the real inner product it is the atom `fourierAtom ξ`, whose subtraction kernel is positive
definite. -/
theorem continuous_and_isPositiveDefiniteSub_fourierAtom (ξ : V) :
    Continuous (fun v => fourierAtom v ξ) ∧ IsPositiveDefiniteSub (fun v => fourierAtom v ξ) := by
  have h : (fun v => fourierAtom v ξ) = fourierAtom ξ :=
    funext fun v => by simp only [fourierAtom, real_inner_comm]
  rw [h]
  exact ⟨continuous_fourierAtom ξ, .of_posSemidef (posSemidef_fourierAtom ξ)⟩

/-- A Fourier atom, having unit norm and being continuous, is integrable against a finite
measure. -/
theorem integrable_fourierAtom [MeasurableSpace V] [OpensMeasurableSpace V]
    (μ : MeasureTheory.Measure V) [MeasureTheory.IsFiniteMeasure μ] (q : V) :
    MeasureTheory.Integrable (fourierAtom q) μ :=
  (MeasureTheory.integrable_const (1 : ℝ)).mono'
    (continuous_fourierAtom q).aestronglyMeasurable
    (.of_forall fun v => (norm_fourierAtom q v).le)

end TauCeti
