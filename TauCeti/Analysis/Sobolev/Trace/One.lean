/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Trace.Kernel
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Function.Holder

/-!
# Gauss–Green and the kernel of the `W^{1,1}` half-space trace

On the half-space `H = {x | a < x.fst}` in the Euclidean product `ℝ × E`, the trace
`TauCeti.W1p.halfSpaceTraceOne : W^{1,1}(H) → L¹(E)` satisfies the integration-by-parts
formula with outward normal `-e₁`. Its kernel is exactly `W^{1,1}_0(H)`, the closure of
the test functions in the Sobolev norm. Equivalently, a function has zero trace if and
only if its value and gradient extend by zero to a whole-space Sobolev function.

The boundary pairing uses `L¹`–`L∞` duality rather than an `L²` inner product. In particular,
the endpoint `p = 1` needs neither square integrability nor a finite-measure domain.

The argument follows L. C. Evans, *Partial Differential Equations*, §5.5, Theorem 2,
and H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
Proposition 9.18. It uses the existing reflection extension and the characterization
of zero-boundary functions by zero extension on a half-space.
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace Filter Topology
open scoped ContDiff Distributions Gradient ENNReal InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private theorem continuous_halfSpaceBulkPairing_one (a : ℝ)
    {χ : WithLp 2 (ℝ × E) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (v : WithLp 2 (ℝ × E)) :
    Continuous fun w : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace (E := E) a) 1 ↦
      ∫ x in normalHalfSpace (E := E) a,
        (fderiv ℝ χ x v * W1p.value w x + χ x * ⟪v, W1p.gradient w x⟫_ℝ) := by
  have hdc : Continuous fun x ↦ fderiv ℝ χ x v :=
    (hχ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- The fixed test factors pair continuously with the value and gradient in `L¹`.
  have hD : MemLp (fun x ↦ fderiv ℝ χ x v) ∞
      (volume.restrict (normalHalfSpace (E := E) a)) :=
    (hdc.memLp_of_hasCompactSupport (hχc.fderiv_apply (𝕜 := ℝ) v)).restrict _
  have hG : MemLp (fun x ↦ χ x • v) ∞
      (volume.restrict (normalHalfSpace (E := E) a)) :=
    ((hχ.continuous.smul continuous_const).memLp_of_hasCompactSupport hχc.smul_right).restrict _
  let D := (ContinuousLinearMap.mul ℝ ℝ).lpPairing _ ∞ 1 (hD.toLp _)
  let G := (innerSL ℝ).lpPairing _ ∞ 1 (hG.toLp _)
  have hL (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace (E := E) a) 1) :
      ∫ x in normalHalfSpace (E := E) a,
          (fderiv ℝ χ x v * W1p.value w x + χ x * ⟪v, W1p.gradient w x⟫_ℝ) =
        D (W1p.value w) + G (W1p.gradient w) := by
    simp only [D, G, ContinuousLinearMap.lpPairing_eq_integral]
    rw [← integral_add
      (memLp_one_iff_integrable.mp <| (ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 1
        (Lp.memLp (hD.toLp _)) (Lp.memLp (W1p.value w)))
      (memLp_one_iff_integrable.mp <| (innerSL ℝ).memLp_of_bilin 1
        (Lp.memLp (hG.toLp _)) (Lp.memLp (W1p.gradient w)))]
    apply integral_congr_ae
    filter_upwards [hD.coeFn_toLp, hG.coeFn_toLp] with x h1 h2
    simp only [ContinuousLinearMap.mul_apply', h1, h2]
    rw [innerSL_apply_apply]
    exact congrArg ((fderiv ℝ χ x v * W1p.value w x) + ·)
      (real_inner_smul_left v (W1p.gradient w x) (χ x)).symm
  simp_rw [hL]
  exact ((D.comp (W1p.valueL (p := 1))) +
    (G.comp (W1p.gradientL (p := 1)))).continuous.congr fun w ↦ by
      simp only [add_apply, ContinuousLinearMap.comp_apply,
        W1p.valueL_apply, W1p.gradientL_apply]

private theorem continuous_hyperplaneBoundaryPairing_one (a : ℝ)
    {χ : WithLp 2 (ℝ × E) → ℝ} (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    Continuous fun w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 1 ↦
      ∫ y : E, W1p.hyperplaneTraceOne a w y * χ (WithLp.toLp 2 (a, y)) := by
  have he : IsClosedEmbedding (fun y : E ↦ WithLp.toLp 2 (a, y)) :=
    (WithLp.homeomorphProd 2 ℝ E).symm.isClosedEmbedding.comp
      (.of_isEmbedding_isClosedMap (isEmbedding_prodMkRight a) (isClosedMap_prodMk_left a))
  have hT : MemLp (fun y : E ↦ χ (WithLp.toLp 2 (a, y))) ∞ volume :=
    (hχ.comp he.continuous).memLp_of_hasCompactSupport
      (hχc.comp_isClosedEmbedding he)
  let T := (ContinuousLinearMap.mul ℝ ℝ).lpPairing volume ∞ 1 (hT.toLp _)
  have hR (w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 1) :
      ∫ y : E, W1p.hyperplaneTraceOne a w y * χ (WithLp.toLp 2 (a, y)) =
        T (W1p.hyperplaneTraceOne a w) := by
    simp only [T, ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.mul_apply']
    apply integral_congr_ae
    filter_upwards [hT.coeFn_toLp] with y hy
    simp [hy, mul_comm]
  simp_rw [hR]
  exact T.continuous.comp (W1p.hyperplaneTraceOne a).continuous

private theorem setIntegral_restrictL_fderiv_mul_value_add_mul_inner_gradient_one (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 1)
    {χ : WithLp 2 (ℝ × E) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (v : WithLp 2 (ℝ × E)) :
    ∫ x in normalHalfSpace (E := E) a,
        (fderiv ℝ χ x v * W1p.value (W1p.restrictL (U := normalHalfSpace (E := E) a) le_top u) x +
          χ x * ⟪v, W1p.gradient (W1p.restrictL (U := normalHalfSpace (E := E) a) le_top u) x⟫_ℝ) =
      -(v.fst * ∫ y : E, W1p.hyperplaneTraceOne a u y * χ (WithLp.toLp 2 (a, y))) := by
  -- Whole-space test functions are dense; both sides are continuous `L¹` pairings.
  have hcL : Continuous fun w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 1 ↦
      ∫ x in normalHalfSpace (E := E) a,
        (fderiv ℝ χ x v * W1p.value (W1p.restrictL (U := normalHalfSpace (E := E) a) le_top w) x +
          χ x * ⟪v, W1p.gradient (W1p.restrictL (U := normalHalfSpace (E := E) a) le_top w) x⟫_ℝ) :=
    (continuous_halfSpaceBulkPairing_one a hχ hχc v).comp
      (W1p.restrictL (U := normalHalfSpace (E := E) a) (Omega := ⊤)
        (p := 1) (mu := volume) le_top).continuous
  have hcR : Continuous fun w : W1p (volume : Measure (WithLp 2 (ℝ × E))) ⊤ 1 ↦
      -(v.fst * ∫ y : E, W1p.hyperplaneTraceOne a w y * χ (WithLp.toLp 2 (a, y))) :=
    (continuous_const.mul (continuous_hyperplaneBoundaryPairing_one a hχ.continuous hχc)).neg
  refine (W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 1)
    (by norm_num)).induction_on u (isClosed_eq hcL hcR) fun ψ ↦ ?_
  have hψ : ContDiff ℝ 1 (ψ : WithLp 2 (ℝ × E) → ℝ) := ψ.contDiff.of_le (by simp)
  have hval := W1p.value_ofTestFunctionₗ (mu := volume) (Omega := ⊤) (p := 1) ψ
  have hgrad := W1p.gradient_ofTestFunctionₗ (mu := volume) (Omega := ⊤) (p := 1) ψ
  calc
    _ = ∫ x in normalHalfSpace (E := E) a, fderiv ℝ (fun x ↦ χ x * ψ x) x v := by
      apply integral_congr_ae
      have hv := testFunctionLp_apply_ae (mu := volume) 1 ψ
      have hg := gradientTestFunctionLp_apply_ae (mu := volume) 1 ψ
      simp only [Opens.coe_top, Measure.restrict_univ] at hv hg
      filter_upwards [W1p.value_restrictL_ae le_top (W1p.ofTestFunctionₗ volume ⊤ 1 ψ),
        W1p.gradient_restrictL_ae le_top (W1p.ofTestFunctionₗ volume ⊤ 1 ψ),
        ae_restrict_of_ae hv, ae_restrict_of_ae hg] with x hx hy hx' hy'
      rw [hx, hy, hval, hgrad, hx', hy',
        fderiv_fun_mul (hχ.differentiable one_ne_zero x) (hψ.differentiable one_ne_zero x),
        real_inner_comm, inner_gradient_left]
      simp only [add_apply, smul_apply, smul_eq_mul]
      ring
    _ = -(v.fst * ∫ y : E, χ (WithLp.toLp 2 (a, y)) * ψ (WithLp.toLp 2 (a, y))) :=
      setIntegral_normalHalfSpace_fderiv_apply (hχ.mul hψ) hχc.mul_right a v
    _ = _ := by
      congr 2
      apply integral_congr_ae
      filter_upwards [W1p.hyperplaneTraceOne_ofTestFunction_apply_ae a ψ] with y hy
      rw [hy, mul_comm]

/-- **Gauss–Green for `W^{1,1}` on a half-space.** For a compactly supported `C¹` test factor,
the boundary term is the `L¹` trace paired with its restriction to the boundary. The sign
corresponds to the outward normal `-e₁`. -/
theorem W1p.setIntegral_fderiv_mul_value_add_mul_inner_gradient_one (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace (E := E) a) 1)
    {χ : WithLp 2 (ℝ × E) → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ)
    (v : WithLp 2 (ℝ × E)) :
    ∫ x in normalHalfSpace (E := E) a,
        (fderiv ℝ χ x v * W1p.value u x + χ x * ⟪v, W1p.gradient u x⟫_ℝ) =
      -(v.fst * ∫ y : E, W1p.halfSpaceTraceOne a u y * χ (WithLp.toLp 2 (a, y))) := by
  simpa only [W1p.restrictL_extendByReflectionL, ← W1p.halfSpaceTraceOne_apply] using
    setIntegral_restrictL_fderiv_mul_value_add_mul_inner_gradient_one a
      (W1p.extendByReflectionL a u) hχ hχc v

private theorem setIntegral_extendByZero_one_eq (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace (E := E) a) 1)
    (φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ)) (v : WithLp 2 (ℝ × E)) :
    ∫ x in (⊤ : Opens (WithLp 2 (ℝ × E))),
        (lineDeriv ℝ (φ : WithLp 2 (ℝ × E) → ℝ) x v *
            Sobolev1JetLp.value (Sobolev1JetLp.extendByZeroₗᵢ le_top
              (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E)))
                (normalHalfSpace (E := E) a) 1)) x +
          φ x * Sobolev1JetLp.candidateWeakFDeriv (Sobolev1JetLp.extendByZeroₗᵢ le_top
              (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E)))
                (normalHalfSpace (E := E) a) 1))
            x v) =
      -(v.fst * ∫ y : E, W1p.halfSpaceTraceOne a u y * φ (WithLp.toLp 2 (a, y))) := by
  have hH := (normalHalfSpace (E := E) a).isOpen.measurableSet
  have hφ : ContDiff ℝ 1 (φ : WithLp 2 (ℝ × E) → ℝ) := φ.contDiff.of_le (by simp)
  have htop := (⊤ : Opens (WithLp 2 (ℝ × E))).isOpen.measurableSet
  have hsub : (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))) ⊆
      ((⊤ : Opens (WithLp 2 (ℝ × E))) : Set (WithLp 2 (ℝ × E))) := subset_univ _
  have hval := (ae_restrict_iff' htop).1 (coeFn_extendByZeroLpₗᵢ ℝ hH hsub (W1p.value u))
  have hgrad := (ae_restrict_iff' htop).1 (coeFn_extendByZeroLpₗᵢ ℝ hH hsub (W1p.gradient u))
  rw [← W1p.setIntegral_fderiv_mul_value_add_mul_inner_gradient_one a u hφ φ.hasCompactSupport v,
    ← integral_indicator hH, setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦
      (hx (by simp)).elim]
  apply integral_congr_ae
  filter_upwards [hval, hgrad] with x h1 h2
  rw [Sobolev1JetLp.candidateWeakFDeriv_apply, Sobolev1JetLp.value_extendByZeroₗᵢ,
    Sobolev1JetLp.gradient_extendByZeroₗᵢ, ← W1p.value_coe, ← W1p.gradient_coe]
  rw [h1 (by simp), h2 (by simp), (hφ.differentiable one_ne_zero x).lineDeriv_eq_fderiv]
  by_cases hx : x ∈ (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E)))
  · simp only [indicator_of_mem hx]
  · simp only [indicator_of_notMem hx, mul_zero, inner_zero_right, add_zero]

/-- A `W^{1,1}` function on a half-space extends by zero, in both value and weak gradient,
to a whole-space Sobolev function exactly when its `L¹` trace vanishes. -/
theorem W1p.extendByZeroₗᵢ_mem_w1pSubmodule_iff_halfSpaceTraceOne_eq_zero (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace (E := E) a) 1) :
    Sobolev1JetLp.extendByZeroₗᵢ (show normalHalfSpace (E := E) a ≤ ⊤ from le_top)
        (u : Sobolev1JetLp (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace (E := E) a) 1) ∈
          w1pSubmodule volume ⊤ 1 ↔ W1p.halfSpaceTraceOne a u = 0 := by
  rw [mem_w1pSubmodule_iff]
  simp only [setIntegral_extendByZero_one_eq]
  constructor
  · intro h
    -- Product test functions with normal factor equal to one detect the boundary trace.
    have hζ (ζ : E → ℝ) (hζ : ContDiff ℝ ∞ ζ) (hζc : HasCompactSupport ζ) :
        ∫ y, ζ y • W1p.halfSpaceTraceOne a u y = 0 := by
      let η : ContDiffBump a := ⟨1, 2, one_pos, one_lt_two⟩
      have hfst : ContDiff ℝ ∞ fun x : WithLp 2 (ℝ × E) ↦ x.fst :=
        contDiff_fst.comp (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).contDiff
      have hsnd : ContDiff ℝ ∞ fun x : WithLp 2 (ℝ × E) ↦ x.snd :=
        contDiff_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ E).contDiff
      have hc : HasCompactSupport fun x : WithLp 2 (ℝ × E) ↦ η x.fst * ζ x.snd := by
        refine HasCompactSupport.intro ((WithLp.homeomorphProd 2 ℝ E).isCompact_preimage.2
          (η.hasCompactSupport.isCompact.prod hζc.isCompact)) fun x hx ↦ ?_
        simp only [mem_preimage, mem_prod, not_and_or] at hx
        rcases hx with hx | hx
        · exact mul_eq_zero_of_left (image_eq_zero_of_notMem_tsupport hx) _
        · exact mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport hx)
      let φ : 𝓓((⊤ : Opens (WithLp 2 (ℝ × E))), ℝ) :=
        ⟨fun x ↦ η x.fst * ζ x.snd, (η.contDiff.comp hfst).mul (hζ.comp hsnd), hc,
          fun _ _ ↦ trivial⟩
      have h1 := h φ (WithLp.toLp 2 (1, 0))
      have hη : η a = 1 := η.one_of_mem_closedBall (Metric.mem_closedBall_self zero_le_one)
      simp only [WithLp.toLp_fst, one_mul, neg_eq_zero] at h1
      have hφa (y : E) : φ (WithLp.toLp 2 (a, y)) = ζ y := by
        have hcoe : (φ : WithLp 2 (ℝ × E) → ℝ) = fun x ↦ η x.fst * ζ x.snd := TestFunction.coe_mk
        simp only [hcoe, WithLp.toLp_fst, WithLp.toLp_snd, hη, one_mul]
      rw [← h1]
      exact integral_congr_ae (.of_forall fun y ↦ by simp [hφa, smul_eq_mul, mul_comm])
    apply Lp.ext
    filter_upwards [ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((Lp.memLp (W1p.halfSpaceTraceOne a u)).locallyIntegrable (by norm_num)) hζ,
      Lp.coeFn_zero ℝ 1 (volume : Measure E)] with y hy h0
    rw [hy, h0, Pi.zero_apply]
  · intro h φ v
    rw [h, neg_eq_zero, mul_eq_zero]
    right
    refine (integral_congr_ae ?_).trans (integral_zero _ _)
    filter_upwards [Lp.coeFn_zero ℝ 1 (volume : Measure E)] with y hy
    rw [hy, Pi.zero_apply, zero_mul]

/-- **Zero `L¹` trace characterizes `W^{1,1}_0` on a half-space.** No square-integrability
assumption is needed at this endpoint. -/
@[simp]
theorem W1p.mem_w1p0Submodule_iff_halfSpaceTraceOne_eq_zero (a : ℝ)
    (u : W1p (volume : Measure (WithLp 2 (ℝ × E))) (normalHalfSpace (E := E) a) 1) :
    u ∈ w1p0Submodule volume (normalHalfSpace (E := E) a) 1 ↔
      W1p.halfSpaceTraceOne a u = 0 := by
  rw [W1p.mem_w1p0Submodule_normalHalfSpace_iff ENNReal.one_ne_top a u,
    W1p.extendByZeroₗᵢ_mem_w1pSubmodule_iff_halfSpaceTraceOne_eq_zero]

/-- The kernel of the `W^{1,1}` half-space trace is the closure of the test functions. -/
theorem W1p.ker_halfSpaceTraceOne (a : ℝ) :
    LinearMap.ker (W1p.halfSpaceTraceOne (E := E) a).toLinearMap =
      (w1p0Submodule volume (normalHalfSpace (E := E) a) 1).toSubmodule := by
  ext u
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ClosedSubmodule.mem_toSubmodule_iff,
    W1p.mem_w1p0Submodule_iff_halfSpaceTraceOne_eq_zero]

end TauCeti
