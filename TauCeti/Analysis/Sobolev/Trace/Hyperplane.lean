/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Estimate
public import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Flat traces in `W^{1,1}` and `H¹`

Restriction to `{a} × E` extends uniquely to bounded linear maps from the weak Sobolev spaces
`W^{1,1}(ℝ × E)` to `L¹(E)` and `H¹(ℝ × E)` to `L²(E)`. The ambient product has its
Euclidean norm, represented by `WithLp 2`. Both traces agree with restriction on test functions,
have operator norm at most one, and send Sobolev convergence to convergence of boundary values.
The construction uses the whole-space test-function density theorem and Mathlib's
`LinearMap.extendOfNorm`.

This flat trace is the local model for boundary conditions on strips and on smooth domains.
No pointwise representative of an arbitrary Sobolev function is evaluated: agreement with
classical restriction is first proved on the dense space of test functions.

The proof follows L. C. Evans, *Partial Differential Equations*, Chapter 5, §5.5.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace Topology
open scoped Distributions Gradient ENNReal

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E]

private theorem hyperplane_memLp (p : ℝ≥0∞) (a : ℝ)
    (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) :
    MemLp (fun y ↦ φ (WithLp.toLp 2 (a, y))) p volume := by
  have he : IsClosedEmbedding (fun y : E ↦ WithLp.toLp 2 (a, y)) :=
    (WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
      (.of_isEmbedding_isClosedMap (isEmbedding_prodMkRight a) (isClosedMap_prodMk_left a))
  exact (φ.continuous.comp he.continuous).memLp_of_hasCompactSupport
    (φ.hasCompactSupport.comp_isClosedEmbedding he)

private def hyperplaneTestFunctionₗ (p : ℝ≥0∞) (a : ℝ) :
    𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ) →ₗ[ℝ] Lp ℝ p (volume : Measure E) where
  toFun φ := (hyperplane_memLp p a φ).toLp (fun y ↦ φ (WithLp.toLp 2 (a, y)))
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun y ↦ by simp
  map_smul' c φ := by
    rw [← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall fun y ↦ by simp

omit [MeasurableSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- On each normal line `ℝ × {y}`, the value of a compactly supported `C¹` function at height
`a` is bounded by the line integral of the norm of its derivative. -/
private theorem abs_le_integral_norm_fderiv_line
    {u : WithLp 2 (ℝ × E) → ℝ} (hu : ContDiff ℝ 1 u) (hsupp : HasCompactSupport u)
    (a : ℝ) (y : E) :
    |u (WithLp.toLp 2 (a, y))| ≤ ∫ t : ℝ, ‖fderiv ℝ u (WithLp.toLp 2 (t, y))‖ := by
  have hc := hu.continuous_fderiv one_ne_zero
  have hcsupp : HasCompactSupport (fun x : WithLp 2 (ℝ × E) ↦ ‖fderiv ℝ u x‖) :=
    (hsupp.fderiv ℝ).mono fun _ hx hz ↦ hx <|
      (congrArg (fun A : WithLp 2 (ℝ × E) →L[ℝ] ℝ ↦ ‖A‖) hz).trans <| by
        rw [norm_zero (E := WithLp 2 (ℝ × E) →L[ℝ] ℝ)]
  have he : IsClosedEmbedding (fun t : ℝ ↦ WithLp.toLp 2 (t, y)) :=
    (WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
      (.of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft y) (isClosedMap_prodMk_right y))
  have hpath : ContDiff ℝ 1 (fun t : ℝ ↦ WithLp.toLp 2 (t, y)) :=
    ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.contDiff).comp
      (contDiff_id.prodMk contDiff_const)
  have hg := hu.comp hpath
  have hgs := hsupp.comp_isClosedEmbedding he
  have hd (t : ℝ) : deriv (u ∘ fun s : ℝ ↦ WithLp.toLp 2 (s, y)) t =
      fderiv ℝ u (WithLp.toLp 2 (t, y)) (WithLp.toLp 2 (1, (0 : E))) := by
    have hp : HasDerivAt (fun s : ℝ ↦ WithLp.toLp 2 (s, y))
        (WithLp.toLp 2 (1, (0 : E))) t :=
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.hasFDerivAt).comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
    exact ((hu.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t hp).deriv
  have hderivInt : Integrable (fun t ↦ |deriv (u ∘ fun s : ℝ ↦
      WithLp.toLp 2 (s, y)) t|) volume :=
    (hg.continuous_deriv le_rfl).abs.integrable_of_hasCompactSupport hgs.deriv.abs
  have hfderivInt : Integrable (fun t ↦ ‖fderiv ℝ u (WithLp.toLp 2 (t, y))‖) volume :=
    (hc.comp he.continuous).norm.integrable_of_hasCompactSupport
      (hcsupp.comp_isClosedEmbedding he)
  -- Write the value as the integral of the derivative over `(-∞, a]` and bound the integrand.
  calc
    |u (WithLp.toLp 2 (a, y))| =
        |∫ t in Iic a, deriv (u ∘ fun s : ℝ ↦ WithLp.toLp 2 (s, y)) t| := by
      rw [hgs.integral_Iic_deriv_eq hg a]
      rfl
    _ ≤ ∫ t in Iic a, |deriv (u ∘ fun s : ℝ ↦ WithLp.toLp 2 (s, y)) t| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := volume.restrict (Iic a))
          (fun t ↦ deriv (u ∘ fun s : ℝ ↦ WithLp.toLp 2 (s, y)) t))
    _ ≤ ∫ t : ℝ, |deriv (u ∘ fun s : ℝ ↦ WithLp.toLp 2 (s, y)) t| :=
      setIntegral_le_integral hderivInt (Filter.Eventually.of_forall fun _ ↦ abs_nonneg _)
    _ ≤ ∫ t : ℝ, ‖fderiv ℝ u (WithLp.toLp 2 (t, y))‖ := by
      apply integral_mono hderivInt hfderivInt
      intro t
      simp only [hd t]
      have hb := (fderiv ℝ u (WithLp.toLp 2 (t, y))).le_opNorm
        (WithLp.toLp 2 (1, (0 : E)))
      simpa only [Real.norm_eq_abs, WithLp.norm_toLp_fst, norm_one, mul_one] using hb

/-- The `L¹` norm on a hyperplane is bounded by the whole-space `L¹` norm of the gradient of
a compactly supported `C¹` function. -/
theorem integral_hyperplane_abs_le_integral_norm_fderiv
    {u : WithLp 2 (ℝ × E) → ℝ} (hu : ContDiff ℝ 1 u) (hsupp : HasCompactSupport u)
    (a : ℝ) :
    (∫ y : E, |u (WithLp.toLp 2 (a, y))|) ≤
      ∫ x : WithLp 2 (ℝ × E), ‖fderiv ℝ u x‖ := by
  have hc := hu.continuous_fderiv one_ne_zero
  have hcsupp : HasCompactSupport (fun x : WithLp 2 (ℝ × E) ↦ ‖fderiv ℝ u x‖) :=
    (hsupp.fderiv ℝ).mono fun _ hx hz ↦ hx <|
      (congrArg (fun A : WithLp 2 (ℝ × E) →L[ℝ] ℝ ↦ ‖A‖) hz).trans <| by
        rw [norm_zero (E := WithLp 2 (ℝ × E) →L[ℝ] ℝ)]
  have hint : Integrable (fun x : WithLp 2 (ℝ × E) ↦ ‖fderiv ℝ u x‖) volume :=
    hc.norm.integrable_of_hasCompactSupport hcsupp
  have hprod : Integrable (fun z : ℝ × E ↦ ‖fderiv ℝ u (WithLp.toLp 2 z)‖)
      (volume.prod volume) :=
    (WithLp.volume_preserving_toLp ℝ E).integrable_comp hint.aestronglyMeasurable |>.mpr hint
  -- Integrate the normal-line estimates and use the volume-preserving product coordinates.
  calc
    _ ≤ ∫ y : E, ∫ t : ℝ, ‖fderiv ℝ u (WithLp.toLp 2 (t, y))‖ :=
      integral_mono
        ((hu.continuous.comp
          ((WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
            (.of_isEmbedding_isClosedMap
              (isEmbedding_prodMkRight a) (isClosedMap_prodMk_left a))).continuous).abs
            |>.integrable_of_hasCompactSupport
              ((hsupp.comp_isClosedEmbedding
                ((WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
                  (.of_isEmbedding_isClosedMap
                    (isEmbedding_prodMkRight a) (isClosedMap_prodMk_left a)))).abs))
        hprod.integral_prod_right (abs_le_integral_norm_fderiv_line hu hsupp a)
    _ = _ := by
      rw [← integral_prod_symm _ hprod]
      simpa only [Measure.volume_eq_prod] using
        (WithLp.volume_preserving_toLp ℝ E).integral_comp
          (MeasurableEquiv.toLp 2 (ℝ × E)).measurableEmbedding
          (fun x ↦ ‖fderiv ℝ u x‖)

private theorem norm_hyperplaneTestFunctionOne_le (a : ℝ)
    (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) :
    ‖hyperplaneTestFunctionₗ 1 a φ‖ ≤ ‖W1p.ofTestFunctionₗ volume ⊤ 1 φ‖ := by
  calc
    ‖hyperplaneTestFunctionₗ 1 a φ‖ =
        ∫ y : E, |φ (WithLp.toLp 2 (a, y))| := by
      rw [L1.norm_eq_integral_norm]
      apply integral_congr_ae
      filter_upwards [(hyperplane_memLp 1 a φ).coeFn_toLp] with y hy
      simp only [hyperplaneTestFunctionₗ, LinearMap.coe_mk, AddHom.coe_mk, hy,
        Real.norm_eq_abs]
    _ ≤ ∫ x : WithLp 2 (ℝ × E), ‖fderiv ℝ φ x‖ :=
      integral_hyperplane_abs_le_integral_norm_fderiv
        (φ.contDiff.of_le (by simp)) φ.hasCompactSupport a
    _ = ‖gradientTestFunctionLp (mu := volume) 1 φ‖ := by
      rw [L1.norm_eq_integral_norm]
      simp only [Opens.coe_top, Measure.restrict_univ]
      have hgrad := gradientTestFunctionLp_apply_ae (mu := volume) 1 φ
      simp only [Opens.coe_top, Measure.restrict_univ] at hgrad
      apply integral_congr_ae
      filter_upwards [hgrad] with x hx
      rw [hx, norm_gradient_eq_norm_fderiv]
    _ = ‖W1p.gradient (W1p.ofTestFunctionₗ volume ⊤ 1 φ)‖ := by
      rw [W1p.gradient_ofTestFunctionₗ]
    _ ≤ ‖W1p.ofTestFunctionₗ volume ⊤ 1 φ‖ := W1p.norm_gradient_le _

/-- The `L¹` trace of a whole-space `W^{1,1}` function on the hyperplane `{a} × E`, defined as
the unique continuous extension of restriction of test functions. -/
def W1p.hyperplaneTraceOne (a : ℝ) :
    W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 1 →L[ℝ] Lp ℝ 1 (volume : Measure E) :=
  (hyperplaneTestFunctionₗ 1 a).extendOfNorm (W1p.ofTestFunctionₗ volume ⊤ 1)

/-- On test functions, the `W^{1,1}` hyperplane trace agrees almost everywhere with classical
restriction. -/
theorem W1p.hyperplaneTraceOne_ofTestFunction_apply_ae (a : ℝ)
    (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) :
    ∀ᵐ y ∂(volume : Measure E),
      W1p.hyperplaneTraceOne a (W1p.ofTestFunctionₗ volume ⊤ 1 φ) y =
        φ (WithLp.toLp 2 (a, y)) := by
  rw [W1p.hyperplaneTraceOne, LinearMap.extendOfNorm_eq
    (W1p.denseRange_ofTestFunctionₗ_top
      (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := 1) (by norm_num))
    ⟨1, fun ψ ↦ by simpa only [one_mul] using norm_hyperplaneTestFunctionOne_le a ψ⟩]
  exact (hyperplane_memLp 1 a φ).coeFn_toLp

/-- The flat `W^{1,1}` trace has norm at most the whole-space Sobolev norm. -/
theorem W1p.norm_hyperplaneTraceOne_le (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 1) :
    ‖W1p.hyperplaneTraceOne a u‖ ≤ ‖u‖ := by
  simpa only [W1p.hyperplaneTraceOne, one_mul] using
    (hyperplaneTestFunctionₗ 1 a).norm_extendOfNorm_apply_le
      (W1p.denseRange_ofTestFunctionₗ_top
        (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := 1) (by norm_num)) 1
      (fun φ ↦ by simpa only [one_mul] using norm_hyperplaneTestFunctionOne_le a φ) u

/-- The operator norm of the flat `W^{1,1}` trace is at most one. -/
theorem W1p.opNorm_hyperplaneTraceOne_le (a : ℝ) :
    ‖W1p.hyperplaneTraceOne (E := E) a‖ ≤ 1 := by
  simpa only [W1p.hyperplaneTraceOne] using
    (LinearMap.opNorm_extendOfNorm_le (f := hyperplaneTestFunctionₗ 1 a)
      (W1p.denseRange_ofTestFunctionₗ_top
        (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := 1) (by norm_num)) zero_le_one
      (fun φ ↦ by simpa only [one_mul] using norm_hyperplaneTestFunctionOne_le a φ))

/-- A continuous linear `L¹` boundary operator agreeing with restriction on every test function
is the flat `W^{1,1}` trace. -/
theorem W1p.hyperplaneTraceOne_unique (a : ℝ)
    (T : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 1 →L[ℝ]
      Lp ℝ 1 (volume : Measure E))
    (hT : ∀ φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ),
      ∀ᵐ y ∂(volume : Measure E), T (W1p.ofTestFunctionₗ volume ⊤ 1 φ) y =
        φ (WithLp.toLp 2 (a, y))) : T = W1p.hyperplaneTraceOne a := by
  apply Eq.symm
  unfold W1p.hyperplaneTraceOne
  refine LinearMap.extendOfNorm_unique
    (W1p.denseRange_ofTestFunctionₗ_top
      (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := 1) (by norm_num)) 1
    (fun φ ↦ by simpa only [one_mul] using norm_hyperplaneTestFunctionOne_le a φ) T ?_
  ext φ
  filter_upwards [hT φ, (hyperplane_memLp 1 a φ).coeFn_toLp] with y ht hf
  exact ht.trans hf.symm

/-- The squared `L²` norm on a hyperplane is bounded by the whole-space `H¹` energy of a
compactly supported `C¹` function. -/
theorem integral_hyperplane_sq_le_integral_sq_add_norm_fderiv_sq
    {u : WithLp 2 (ℝ × E) → ℝ} (hu : ContDiff ℝ 1 u) (hsupp : HasCompactSupport u)
    (a : ℝ) :
    (∫ y : E, u (WithLp.toLp 2 (a, y)) ^ 2) ≤
      ∫ x : WithLp 2 (ℝ × E), u x ^ 2 + ‖fderiv ℝ u x‖ ^ 2 := by
  have hc := hu.continuous_fderiv one_ne_zero
  have hs : HasCompactSupport (fun x ↦ u x ^ 2 + ‖fderiv ℝ u x‖ ^ 2) :=
    (hsupp.mono (fun x hx hz ↦ hx (by simp [hz]))).add
      ((hsupp.fderiv ℝ).mono
        (fun x hx hz ↦ hx ((congrArg
          (fun A : WithLp 2 (ℝ × E) →L[ℝ] ℝ ↦ ‖A‖ ^ 2) hz).trans (by
            rw [norm_zero (E := WithLp 2 (ℝ × E) →L[ℝ] ℝ)]
            norm_num))))
  have hint : Integrable (fun x ↦ u x ^ 2 + ‖fderiv ℝ u x‖ ^ 2) volume :=
    ((hu.continuous.pow 2).add (hc.norm.pow 2)).integrable_of_hasCompactSupport hs
  have hprod : Integrable
      (fun z : ℝ × E ↦ u (WithLp.toLp 2 z) ^ 2 + ‖fderiv ℝ u (WithLp.toLp 2 z)‖ ^ 2)
      (volume.prod volume) := by
    exact (WithLp.volume_preserving_toLp ℝ E).integrable_comp hint.aestronglyMeasurable |>.mpr hint
  -- Apply the one-dimensional estimate on each normal line.
  have hline (y : E) : u (WithLp.toLp 2 (a, y)) ^ 2 ≤
      ∫ t : ℝ, u (WithLp.toLp 2 (t, y)) ^ 2 + ‖fderiv ℝ u (WithLp.toLp 2 (t, y))‖ ^ 2 := by
    have he : IsClosedEmbedding (fun t : ℝ ↦ WithLp.toLp 2 (t, y)) :=
      (WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
        (.of_isEmbedding_isClosedMap (isEmbedding_prodMkLeft y) (isClosedMap_prodMk_right y))
    have hpath : ContDiff ℝ 1 (fun t : ℝ ↦ WithLp.toLp 2 (t, y)) :=
      ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.contDiff).comp
        (contDiff_id.prodMk contDiff_const)
    have hg := hu.comp hpath
    have hgs := hsupp.comp_isClosedEmbedding he
    have hd (t : ℝ) : deriv (u ∘ fun s : ℝ ↦ WithLp.toLp 2 (s, y)) t =
        fderiv ℝ u (WithLp.toLp 2 (t, y)) (WithLp.toLp 2 (1, (0 : E))) := by
      have hp : HasDerivAt (fun s : ℝ ↦ WithLp.toLp 2 (s, y))
          (WithLp.toLp 2 (1, (0 : E))) t :=
        ((WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).symm.hasFDerivAt).comp_hasDerivAt t
          ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
      exact ((hu.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt t hp).deriv
    refine (sq_le_integral_sq_add_deriv_sq hg hgs a).trans ?_
    have hgc2 := (hg.continuous.pow 2).add ((hg.continuous_deriv le_rfl).pow 2)
    apply integral_mono
      (hgc2.integrable_of_hasCompactSupport
          ((hgs.mono (fun t ht hz ↦ ht (by
            simp only [Pi.pow_apply, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]))).add
            (hgs.deriv.mono (fun t ht hz ↦ ht (by simp [hz])))))
      (((hu.continuous.comp he.continuous).pow 2).add
        ((hc.comp he.continuous).norm.pow 2) |>.integrable_of_hasCompactSupport
          (hs.comp_isClosedEmbedding he))
    intro t
    dsimp only [Pi.add_apply, Pi.pow_apply, Function.comp_apply]
    rw [hd]
    have hb := (fderiv ℝ u (WithLp.toLp 2 (t, y))).le_opNorm
      (WithLp.toLp 2 (1, (0 : E)))
    simp only [WithLp.norm_toLp_fst, norm_one, mul_one] at hb
    have hsq : (fderiv ℝ u (WithLp.toLp 2 (t, y)) (WithLp.toLp 2 (1, (0 : E)))) ^ 2 ≤
        ‖fderiv ℝ u (WithLp.toLp 2 (t, y))‖ ^ 2 := by
      simpa only [Real.norm_eq_abs, sq_abs] using
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hb)
    exact add_le_add le_rfl hsq
  -- Integrate the slice estimates and use the volume-preserving product coordinates.
  calc
    _ ≤ ∫ y : E, ∫ t : ℝ,
        u (WithLp.toLp 2 (t, y)) ^ 2 + ‖fderiv ℝ u (WithLp.toLp 2 (t, y))‖ ^ 2 :=
      integral_mono
        (by
          have he : IsClosedEmbedding (fun y : E ↦ WithLp.toLp 2 (a, y)) :=
            (WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
              (.of_isEmbedding_isClosedMap
                (isEmbedding_prodMkRight a) (isClosedMap_prodMk_left a))
          exact ((hu.continuous.comp he.continuous).pow 2).integrable_of_hasCompactSupport
            ((hsupp.comp_isClosedEmbedding he).mono
              (fun y hy hz ↦ hy (by
                simp only [Pi.pow_apply, hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]))))
        hprod.integral_prod_right hline
    _ = _ := by
      rw [← integral_prod_symm _ hprod]
      simpa only [Measure.volume_eq_prod] using
        (WithLp.volume_preserving_toLp ℝ E).integral_comp
          (MeasurableEquiv.toLp 2 (ℝ × E)).measurableEmbedding
          (fun x ↦ u x ^ 2 + ‖fderiv ℝ u x‖ ^ 2)

private theorem norm_hyperplaneTestFunction_le (a : ℝ)
    (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) :
    ‖hyperplaneTestFunctionₗ 2 a φ‖ ≤ ‖W1p.ofTestFunctionₗ volume ⊤ 2 φ‖ := by
  have henergy : (∫ x : WithLp 2 (ℝ × E), φ x ^ 2 + ‖fderiv ℝ φ x‖ ^ 2) =
      ‖W1p.ofTestFunctionₗ volume ⊤ 2 φ‖ ^ 2 := by
    rw [W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq]
    simp only [W1p.value_ofTestFunctionₗ, W1p.gradient_ofTestFunctionₗ]
    calc
      _ = ∫ x : WithLp 2 (ℝ × E),
          ‖testFunctionLp (mu := volume) 2 φ x‖ ^ 2 +
            ‖gradientTestFunctionLp (mu := volume) 2 φ x‖ ^ 2 := by
        have hvalue := testFunctionLp_apply_ae (mu := volume) 2 φ
        have hgrad := gradientTestFunctionLp_apply_ae (mu := volume) 2 φ
        simp only [Opens.coe_top, Measure.restrict_univ] at hvalue hgrad
        apply integral_congr_ae
        filter_upwards [hvalue, hgrad] with x hv hg
        simp only [hv, hg, Real.norm_eq_abs, sq_abs, norm_gradient_eq_norm_fderiv]
      _ = _ := by
        rw [← Lp.integral_norm_sq_eq_norm_sq, ← Lp.integral_norm_sq_eq_norm_sq]
        simpa only [Opens.coe_top, Measure.restrict_univ]
          using integral_add
            ((Lp.memLp (testFunctionLp (mu := volume) 2 φ)).integrable_norm_pow (by norm_num))
            ((Lp.memLp (gradientTestFunctionLp (mu := volume) 2 φ)).integrable_norm_pow
              (by norm_num))
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  calc
    _ = ∫ y : E, φ (WithLp.toLp 2 (a, y)) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [(hyperplane_memLp 2 a φ).coeFn_toLp] with y hy
      simp only [hyperplaneTestFunctionₗ, LinearMap.coe_mk, AddHom.coe_mk, hy,
        Real.norm_eq_abs, sq_abs]
    _ ≤ _ := (integral_hyperplane_sq_le_integral_sq_add_norm_fderiv_sq
      (φ.contDiff.of_le (by simp)) φ.hasCompactSupport a).trans_eq henergy

/-- The `L²` trace of a whole-space `H¹` function on the hyperplane `{a} × E`, defined as the
unique continuous extension of restriction of test functions. -/
def W1p.hyperplaneTrace (a : ℝ) :
    W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2 →L[ℝ] Lp ℝ 2 (volume : Measure E) :=
  (hyperplaneTestFunctionₗ 2 a).extendOfNorm (W1p.ofTestFunctionₗ volume ⊤ 2)

/-- On test functions, the hyperplane trace agrees almost everywhere with classical restriction. -/
theorem W1p.hyperplaneTrace_ofTestFunction_apply_ae (a : ℝ)
    (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) :
    ∀ᵐ y ∂(volume : Measure E),
      W1p.hyperplaneTrace a (W1p.ofTestFunctionₗ volume ⊤ 2 φ) y =
        φ (WithLp.toLp 2 (a, y)) := by
  rw [W1p.hyperplaneTrace, LinearMap.extendOfNorm_eq
    (W1p.denseRange_ofTestFunctionₗ_top
      (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := 2) (by norm_num))
    ⟨1, fun ψ ↦ by simpa only [one_mul] using norm_hyperplaneTestFunction_le a ψ⟩]
  exact (hyperplane_memLp 2 a φ).coeFn_toLp

/-- The flat trace has norm at most the whole-space `H¹` norm. -/
theorem W1p.norm_hyperplaneTrace_le (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2) :
    ‖W1p.hyperplaneTrace a u‖ ≤ ‖u‖ := by
  simpa only [W1p.hyperplaneTrace, one_mul] using
    (hyperplaneTestFunctionₗ 2 a).norm_extendOfNorm_apply_le
      (W1p.denseRange_ofTestFunctionₗ_top
        (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := 2) (by norm_num)) 1
      (fun φ ↦ by simpa only [one_mul] using norm_hyperplaneTestFunction_le a φ) u

/-- The operator norm of the hyperplane trace is at most one. -/
theorem W1p.opNorm_hyperplaneTrace_le (a : ℝ) :
    ‖W1p.hyperplaneTrace (E := E) a‖ ≤ 1 := by
  simpa only [W1p.hyperplaneTrace] using
    (LinearMap.opNorm_extendOfNorm_le (f := hyperplaneTestFunctionₗ 2 a)
      (W1p.denseRange_ofTestFunctionₗ_top
        (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := 2) (by norm_num)) zero_le_one
      (fun φ ↦ by simpa only [one_mul] using norm_hyperplaneTestFunction_le a φ))

/-- A continuous linear boundary operator agreeing with restriction on every test function is
the hyperplane trace. -/
theorem W1p.hyperplaneTrace_unique (a : ℝ)
    (T : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 2 →L[ℝ] Lp ℝ 2 (volume : Measure E))
    (hT : ∀ φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ),
      ∀ᵐ y ∂(volume : Measure E), T (W1p.ofTestFunctionₗ volume ⊤ 2 φ) y =
        φ (WithLp.toLp 2 (a, y))) : T = W1p.hyperplaneTrace a := by
  apply Eq.symm
  unfold W1p.hyperplaneTrace
  refine LinearMap.extendOfNorm_unique
    (W1p.denseRange_ofTestFunctionₗ_top
      (mu := (volume : Measure (WithLp 2 (ℝ × E)))) (p := 2) (by norm_num)) 1
    (fun φ ↦ by simpa only [one_mul] using norm_hyperplaneTestFunction_le a φ) T ?_
  ext φ
  filter_upwards [hT φ, (hyperplane_memLp 2 a φ).coeFn_toLp] with y ht hf
  exact ht.trans hf.symm

end TauCeti
