/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Index
public import TauCeti.Analysis.PDE.Vortex.SpectralGap
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.PDE.Vortex.FieldSpace
import TauCeti.Analysis.Sobolev.TestFunctionLp.Basic
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The adjoint vortex operator on `H¹`: injective, closed range and index `-2m`

At a field `x`, the formal adjoint `L_x*` of the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.gaugeFixedAdjoint`) has the same shape as `L_x`: a constant-coefficient
first-order part plus a zeroth-order part linear in `x`
(`TauCeti.Vortex.gaugeFixedAdjoint_eq_gaugeFixedAdjointFirstOrder_add`). This file realizes it, as
`TauCeti.Analysis.PDE.Vortex.Sobolev.Realization` realizes `L_x`, as a bounded operator

`TauCeti.Vortex.sobolevGaugeFixedAdjoint a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)`,

whose leading part acts on the weak gradients of the four coordinates and whose coefficient enters
through its `L∞` class `a`. On test fields with a `C¹` representative it is the classical
operator (`TauCeti.Vortex.sobolevGaugeFixedAdjoint_ae_eq_gaugeFixedAdjoint`). It is affine and
smooth in `a` (`TauCeti.Vortex.sobolevGaugeFixedAdjoint_eq_add`,
`TauCeti.Vortex.contDiff_sobolevGaugeFixedAdjoint`), and changing `a` changes only the
zeroth-order part (`TauCeti.Vortex.sobolevGaugeFixedAdjoint_sub_apply_ae`). This is the paired
adjoint block of the gauge-fixed normal model of a plane vortex; the realization of `L_x` is the
other block.

* **Duality.** At a continuous field with `L∞` class `a`, the two realizations are formally
  adjoint for the `L²` pairing of values: `⟪L_x y, η⟫ = ⟪y, L_x* η⟫` for all `y, η ∈ H¹(ℂ)⁴`
  (`TauCeti.Vortex.inner_sobolevGaugeFixedOperator_sobolevFieldValues`). On test fields `η` this
  is integration by parts (`TauCeti.Vortex.integral_inner_sobolevGaugeFixedOperator`), and test
  fields are dense in `H¹(ℂ)`.
* **Coercivity.** At a `C¹` vortex with `|α| → 1`, `‖η‖_{H¹} ≤ C ‖L_x* η‖_{L²}` for every
  `η ∈ H¹(ℂ)⁴` (`TauCeti.Vortex.exists_norm_le_mul_norm_sobolevGaugeFixedAdjoint`). The `L²`
  norm is controlled by the spectral gap of `L_x L_x*`
  (`TauCeti.Vortex.exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint`). The
  gradient is controlled by the first-order part: on test fields
  `∫ ∑ⱼ |∇ηⱼ|² = ∫ |L₀* η|²`, where `L₀*` is the adjoint at the zero field
  (`TauCeti.Vortex.integral_sum_norm_gradient_sq_eq_integral_norm_sq_gaugeFixedAdjoint_zero`,
  in `TauCeti.Analysis.PDE.Vortex.Garding`),
  and `L_x* - L₀*` is bounded by the sup norm of `x`. So the realization is a closed embedding
  (`TauCeti.Vortex.isClosedEmbedding_sobolevGaugeFixedAdjoint`): injective with closed range.
* **Range.** Its range is the `L²`-orthogonal complement of the values of the kernel of the
  realization of `L_x` (`TauCeti.Vortex.range_sobolevGaugeFixedAdjoint`). By duality the range is
  orthogonal to that kernel. Conversely, a class orthogonal to the range solves `L_x y = 0`
  weakly, so by elliptic regularity it is the value of an element of that kernel
  (`TauCeti.Vortex.exists_sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq`).
* **Fredholm and index.** When that kernel is finite dimensional, the description of the range
  identifies the cokernel of the realization of `L_x*` with that kernel
  (`TauCeti.Vortex.sobolevGaugeFixedAdjointCokernelEquiv`). So the realization of `L_x*` is
  Fredholm (`TauCeti.Vortex.isFredholm_sobolevGaugeFixedAdjoint`) with index minus the dimension
  of that kernel, being injective
  (`TauCeti.Vortex.index_sobolevGaugeFixedAdjoint_eq_neg_finrank_ker_sobolevGaugeFixedOperator`).
  At a continuous plane vortex lying in `A_m^k` for every `k` the index is `-2m`
  (`TauCeti.Vortex.index_sobolevGaugeFixedAdjoint_eq_neg_two_mul`), the negative of the index `2m`
  of `L_x` (`TauCeti.Vortex.index_sobolevGaugeFixedOperator_eq_two_mul`).

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Gr ⇒ SW: From pseudo-holomorphic curves to Seiberg–Witten solutions*,
  J. Differential Geom. 51 (1999), 203–334.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter Metric TopologicalSpace Module
open scoped ENNReal NNReal Topology RealInnerProductSpace Gradient Distributions ContDiff

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-! ### The realization -/

/-- The realization `H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` of the formal adjoint `L_x*` of the gauge-fixed vortex
operator, whose zeroth-order coefficients are given by the `L∞` class `a` of the field `x`. The
leading part acts on the weak gradients of the four coordinates. -/
def sobolevGaugeFixedAdjoint (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ :=
  sobolevFirstOrderOperator gaugeFixedAdjointFirstOrder gaugeFixedAdjointZerothOrder a

/-- Almost everywhere, the realization is given by the formula of `L_x*` with the weak gradients
and the values of the coordinates. -/
theorem sobolevGaugeFixedAdjoint_apply_ae (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤)
    (η : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevGaugeFixedAdjoint a η =ᵐ[μ⊤] fun z ↦
      gaugeFixedAdjointFirstOrder (fun j ↦ W1p.gradient (η j) z) +
        gaugeFixedAdjointZerothOrder (a z) (WithLp.toLp 2 fun j ↦ W1p.value (η j) z) :=
  sobolevFirstOrderOperator_apply_ae _ _ a η

/-- On a variation `η` whose coordinates have the coordinates of a `C¹` field `Y` as
representatives, the realization at the `L∞` class of a field `x` is the classical formal adjoint
`L_x* Y`. -/
theorem sobolevGaugeFixedAdjoint_ae_eq_gaugeFixedAdjoint
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hax : a =ᵐ[μ⊤] x) {η : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2}
    {Y : ℂ → EuclideanSpace ℝ (Fin 4)} (hY : ContDiff ℝ 1 Y)
    (hηY : ∀ j, W1p.value (η j) =ᵐ[μ⊤] fun z ↦ Y z j) :
    sobolevGaugeFixedAdjoint a η =ᵐ[μ⊤] gaugeFixedAdjoint x Y := by
  filter_upwards [sobolevFirstOrderOperator_ae_eq _ _ hax hY hηY] with z h
  rw [gaugeFixedAdjoint_eq_gaugeFixedAdjointFirstOrder_add]
  exact h

/-! ### Dependence on the coefficient -/

/-- Changing the coefficient changes the realization only in its zeroth-order part: almost
everywhere, the difference of the realizations at `a` and `b` is the zeroth-order term with
coefficient `a - b`. -/
theorem sobolevGaugeFixedAdjoint_sub_apply_ae (a b : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤)
    (η : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    (sobolevGaugeFixedAdjoint a - sobolevGaugeFixedAdjoint b) η =ᵐ[μ⊤] fun z ↦
      gaugeFixedAdjointZerothOrder (a z - b z) (WithLp.toLp 2 fun j ↦ W1p.value (η j) z) :=
  sobolevFirstOrderOperator_sub_apply_ae _ _ a b η

/-- The realization is affine in the `L∞` class of the coefficient: it is the realization at `0`
plus the zeroth-order part with coefficient `a`. -/
theorem sobolevGaugeFixedAdjoint_eq_add (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    sobolevGaugeFixedAdjoint a = sobolevGaugeFixedAdjoint 0 +
      (gaugeFixedAdjointZerothOrder.holderL μ⊤ ∞ 2 2 a).comp sobolevFieldValues :=
  sobolevFirstOrderOperator_eq_add _ _ a

/-- The realization is a smooth function of the `L∞` class of the coefficient: it is affine in
it, the realization at `0` plus the zeroth-order part with coefficient `a`. -/
theorem contDiff_sobolevGaugeFixedAdjoint {n : WithTop ℕ∞} :
    ContDiff ℝ n sobolevGaugeFixedAdjoint :=
  contDiff_sobolevFirstOrderOperator _ _

/-- The realization depends continuously, in operator norm, on the `L∞` class of the
coefficient. -/
theorem continuous_sobolevGaugeFixedAdjoint : Continuous sobolevGaugeFixedAdjoint :=
  contDiff_sobolevGaugeFixedAdjoint.continuous (n := 0)

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}

/-! ### Duality with the realization of `L_x` -/

/-- **The realizations of `L_x` and `L_x*` on `H¹` are formally adjoint.** Let `x` be a continuous
field with `L∞` class `a`. For all `y, η ∈ H¹(ℂ)⁴`, `⟪L_x y, η⟫ = ⟪y, L_x* η⟫`, the `L²` pairings
being taken on the values of `y` and `η`. -/
theorem inner_sobolevGaugeFixedOperator_sobolevFieldValues (hx : Continuous x)
    (hax : a =ᵐ[μ⊤] x) (y η : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    ⟪sobolevGaugeFixedOperator a y, sobolevFieldValues η⟫ =
      ⟪sobolevFieldValues y, sobolevGaugeFixedAdjoint a η⟫ := by
  -- Both sides are continuous in `η`, and agree on the dense subspace of test fields.
  refine (DenseRange.piMap fun _ : Fin 4 ↦
    W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 2) (by norm_num)).induction_on
      (p := fun η ↦ ⟪sobolevGaugeFixedOperator a y, sobolevFieldValues η⟫ =
        ⟪sobolevFieldValues y, sobolevGaugeFixedAdjoint a η⟫) η ?_ fun φ ↦ ?_
  · exact isClosed_eq (continuous_const.inner sobolevFieldValues.continuous)
      (continuous_const.inner (sobolevGaugeFixedAdjoint a).continuous)
  · have hV := sobolevFieldValues_ofTestFunctionₗ_ae φ
    have hA := sobolevGaugeFixedAdjoint_ae_eq_gaugeFixedAdjoint hax
      (η := fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) ((contDiff_testField φ).of_le (by simp))
      (value_ofTestFunctionₗ_ae_eq_testField φ)
    have hy := sobolevFieldValues_ae_eq y
    have h := integral_inner_sobolevGaugeFixedOperator hx hax y
      ((contDiff_testField φ).of_le (by simp)) (hasCompactSupport_testField φ)
    have hmap : Pi.map (fun _ ↦ ⇑(W1p.ofTestFunctionₗ volume ⊤ 2)) φ =
        fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j) :=
      funext fun j ↦ Pi.map_apply _ _ j
    rw [hmap, L2.inner_def, L2.inner_def]
    simp only [Opens.coe_top, Measure.restrict_univ] at hV hA hy ⊢
    rw [integral_congr_ae (hV.mono fun z hz ↦ by rw [hz]), h]
    refine integral_congr_ae ?_
    filter_upwards [hA, hy] with z h₁ h₂
    rw [h₁, h₂]

/-! ### Coercivity -/

/-- The squared norm of the formal adjoint at the zero field is at most twice that at `x` plus
twice the zeroth-order part, bounded by the sup norm `M` of `x`. -/
private theorem norm_sq_gaugeFixedAdjoint_zero_le {M : ℝ} (hM : ∀ z, ‖x z‖ ≤ M)
    (η : ℂ → EuclideanSpace ℝ (Fin 4)) (z : ℂ) :
    ‖gaugeFixedAdjoint 0 η z‖ ^ 2 ≤
      2 * ‖gaugeFixedAdjoint x η z‖ ^ 2 + 2 * (‖gaugeFixedAdjointZerothOrder‖ * M) ^ 2 *
        ‖η z‖ ^ 2 := by
  have hsplit : gaugeFixedAdjoint 0 η z =
      gaugeFixedAdjoint x η z - gaugeFixedAdjointZerothOrder (x z) (η z) := by
    rw [gaugeFixedAdjoint_eq_gaugeFixedAdjointFirstOrder_add 0,
      gaugeFixedAdjoint_eq_gaugeFixedAdjointFirstOrder_add x]
    simp
  have hZ : ‖gaugeFixedAdjointZerothOrder (x z) (η z)‖ ≤
      ‖gaugeFixedAdjointZerothOrder‖ * M * ‖η z‖ :=
    (gaugeFixedAdjointZerothOrder.le_opNorm₂ _ _).trans (by gcongr; exact hM z)
  rw [hsplit]
  have h₃ : ‖gaugeFixedAdjoint x η z - gaugeFixedAdjointZerothOrder (x z) (η z)‖ ≤
      ‖gaugeFixedAdjoint x η z‖ + ‖gaugeFixedAdjointZerothOrder‖ * M * ‖η z‖ :=
    (norm_sub_le _ _).trans (by gcongr)
  exact (pow_le_pow_left₀ (norm_nonneg _) h₃ 2).trans (add_sq_le.trans_eq (by ring))

/-- The coercive estimate on fields of test functions, from the spectral gap `c` of `L_x L_x*`
and the bound `M` on the field. -/
private theorem norm_sq_le_of_testFunction (hx : Continuous x) {M : ℝ} (hM : ∀ z, ‖x z‖ ≤ M)
    (hax : a =ᵐ[μ⊤] x) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c * ∫ z, ‖η z‖ ^ 2 ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2)
    (φ : Fin 4 → 𝓓((⊤ : Opens ℂ), ℝ)) :
    ‖fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)‖ ^ 2 ≤
      (c⁻¹ * (1 + 2 * (‖gaugeFixedAdjointZerothOrder‖ * M) ^ 2) + 2) *
        ‖sobolevGaugeFixedAdjoint a (fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j))‖ ^ 2 := by
  set Y := testField φ
  set K := ‖gaugeFixedAdjointZerothOrder‖ * M
  have hY : ContDiff ℝ 2 Y := (contDiff_testField φ).of_le (by simp)
  have hYc : HasCompactSupport Y := hasCompactSupport_testField φ
  have hYi : Integrable (fun z ↦ ‖Y z‖ ^ 2) :=
    hY.continuous.integrable_norm_sq_of_hasCompactSupport hYc
  have hAi : Integrable (fun z ↦ ‖gaugeFixedAdjoint x Y z‖ ^ 2) :=
    (continuous_gaugeFixedAdjoint hx (hY.of_le one_le_two)).integrable_norm_sq_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint hYc)
  have hA0i : Integrable (fun z ↦ ‖gaugeFixedAdjoint 0 Y z‖ ^ 2) :=
    (continuous_gaugeFixedAdjoint continuous_const
      (hY.of_le one_le_two)).integrable_norm_sq_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint hYc)
  -- The gradient is controlled by `L₀*`, and `L₀*` by `L_x*` and the zeroth-order part.
  have hgrad : ∫ z, ∑ j : Fin 4, ‖∇ (φ j : ℂ → ℝ) z‖ ^ 2 ≤
      2 * (∫ z, ‖gaugeFixedAdjoint x Y z‖ ^ 2) + 2 * K ^ 2 * ∫ z, ‖Y z‖ ^ 2 := by
    have hcoord (j : Fin 4) : (fun w ↦ Y w j) = φ j := funext fun w ↦ by simp [Y]
    have h := integral_sum_norm_gradient_sq_eq_integral_norm_sq_gaugeFixedAdjoint_zero
      (μ := volume) hY hYc
    simp only [hcoord] at h
    rw [h, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (hAi.const_mul _) (hYi.const_mul _)]
    exact integral_mono hA0i ((hAi.const_mul _).add (hYi.const_mul _))
      fun z ↦ norm_sq_gaugeFixedAdjoint_zero_le hM Y z
  have hgradi : Integrable (fun z ↦ ∑ j : Fin 4, ‖∇ (φ j : ℂ → ℝ) z‖ ^ 2) :=
    integrable_finsetSum _ fun j _ ↦
      (continuous_gradient_testFunction (φ j)).integrable_norm_sq_of_hasCompactSupport
        (φ j).hasCompactSupport.gradient
  have hH := W1p.norm_sq_ofTestFunctionₗ_top_le (mu := volume) φ
  simp only [← norm_testField_sq] at hH
  rw [integral_add hYi hgradi] at hH
  have hgap' := hgap Y hY hYc
  -- The spectral gap bounds `∫ |Y|²` by `c⁻¹ ∫ |L_x* Y|²`.
  have hYle : ∫ z, ‖Y z‖ ^ 2 ≤ c⁻¹ * ∫ z, ‖gaugeFixedAdjoint x Y z‖ ^ 2 := by
    rw [le_inv_mul_iff₀ hc]
    exact hgap'
  have hL : ‖sobolevGaugeFixedAdjoint a (fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j))‖ ^ 2 =
      ∫ z, ‖gaugeFixedAdjoint x Y z‖ ^ 2 := by
    simp_rw [gaugeFixedAdjoint_eq_gaugeFixedAdjointFirstOrder_add]
    exact norm_sobolevFirstOrderOperator_ofTestFunctionₗ_sq _ _ hax φ
  rw [hL]
  nlinarith [mul_le_mul_of_nonneg_left hYle (by positivity : (0 : ℝ) ≤ 1 + 2 * K ^ 2)]

/-- **The coercive estimate for `L_x*` on `H¹`.** At a `C¹` vortex `x` with `|α| → 1` at infinity
and with `L∞` class `a`, there is `C > 0` with `‖η‖_{H¹} ≤ C ‖L_x* η‖_{L²}` for every
`η ∈ H¹(ℂ)⁴`. -/
theorem exists_norm_le_mul_norm_sobolevGaugeFixedAdjoint (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    ∃ C > 0, ∀ η : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2,
      ‖η‖ ≤ C * ‖sobolevGaugeFixedAdjoint a η‖ := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := volume) hx hsol hlim
  have hM (z : ℂ) : ‖x z‖ ≤ ‖a‖ :=
    Lp.norm_le_norm_top_of_ae_eq_of_continuousAt hax hx.continuous.continuousAt
  set C := c⁻¹ * (1 + 2 * (‖gaugeFixedAdjointZerothOrder‖ * ‖a‖) ^ 2) + 2
  have hC : 0 < C := by positivity
  have hsq (η : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
      ‖η‖ ^ 2 ≤ C * ‖sobolevGaugeFixedAdjoint a η‖ ^ 2 :=
    (DenseRange.piMap fun _ : Fin 4 ↦
      W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 2) (by norm_num)).induction_on
        (p := fun η ↦ ‖η‖ ^ 2 ≤ C * ‖sobolevGaugeFixedAdjoint a η‖ ^ 2) η
        (isClosed_le (continuous_norm.pow 2)
          (continuous_const.mul ((sobolevGaugeFixedAdjoint a).continuous.norm.pow 2)))
        fun φ ↦ norm_sq_le_of_testFunction hx.continuous hM hax hc hgap φ
  refine ⟨√C, Real.sqrt_pos.2 hC, fun η ↦ ?_⟩
  rw [← Real.sqrt_sq (norm_nonneg η), ← Real.sqrt_sq (norm_nonneg (sobolevGaugeFixedAdjoint a η)),
    ← Real.sqrt_mul hC.le]
  exact Real.sqrt_le_sqrt (hsq η)

/-- **The realization of `L_x*` on `H¹` is a closed embedding** at a `C¹` vortex `x` with
`|α| → 1` at infinity and with `L∞` class `a`: it is injective with closed range, and a
homeomorphism onto its range. -/
theorem isClosedEmbedding_sobolevGaugeFixedAdjoint (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    Topology.IsClosedEmbedding (sobolevGaugeFixedAdjoint a) := by
  obtain ⟨C, hC, h⟩ := exists_norm_le_mul_norm_sobolevGaugeFixedAdjoint hx hsol hlim hax
  exact ((sobolevGaugeFixedAdjoint a).antilipschitz_of_bound
    (K := C.toNNReal) fun η ↦ by rw [Real.coe_toNNReal _ hC.le]; exact h η).isClosedEmbedding
    (sobolevGaugeFixedAdjoint a).uniformContinuous

/-! ### The range and the index -/

/-- A class `L²`-orthogonal to the range of the realization of `L_x*` solves `L_x u = 0` weakly:
`∫ ⟪u, L_x* η⟫ = 0` for every smooth compactly supported field `η`. -/
private theorem integral_inner_gaugeFixedAdjoint_eq_zero_of_mem_orthogonal (hax : a =ᵐ[μ⊤] x)
    {u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤} (hu : u ∈ (sobolevGaugeFixedAdjoint a).rangeᗮ)
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ = 0 := by
  -- The coordinates of `η` are test functions, and `L_x* η` is the realization at them.
  set φ : Fin 4 → 𝓓((⊤ : Opens ℂ), ℝ) := fun j ↦
    TestFunction.mk (fun z ↦ η z j) ((contDiff_piLp 2).1 hη j)
      (hηc.comp_left (g := fun v : EuclideanSpace ℝ (Fin 4) ↦ v j) rfl) (by simp)
  have hA := sobolevGaugeFixedAdjoint_ae_eq_gaugeFixedAdjoint hax (hη.of_le (by simp))
    (η := fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j))
    fun j ↦ W1p.value_ofTestFunctionₗ_ae (φ j)
  have h0 := (Submodule.mem_orthogonal' _ _).1 hu _
    (LinearMap.mem_range_self _ (fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)))
  rw [L2.inner_def, ContinuousLinearMap.coe_coe] at h0
  simp only [Opens.coe_top, Measure.restrict_univ] at h0 hA
  rw [← h0]
  exact integral_congr_ae (hA.mono fun z hz ↦ by simp only [hz])

/-- **The range of `L_x*` on `H¹` is the orthogonal complement of the kernel of `L_x`.** At a
`C¹` vortex `x` with `|α| → 1` at infinity and with `L∞` class `a`, the range of the realization
of `L_x*` is the `L²`-orthogonal complement of the values of the kernel of the realization of
`L_x`. -/
theorem range_sobolevGaugeFixedAdjoint (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedAdjoint a).range =
      ((sobolevGaugeFixedOperator a).ker.map sobolevFieldValues.toLinearMap)ᗮ := by
  set R := (sobolevGaugeFixedAdjoint a).range
  -- The range is closed, hence complete, so it is the orthogonal complement of its complement.
  have hR : IsClosed (R : Set (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)) :=
    (isClosedEmbedding_sobolevGaugeFixedAdjoint hx hsol hlim hax).isClosed_range
  have : CompleteSpace R := hR.completeSpace_coe
  refine le_antisymm ?_ ?_
  · -- By duality, the range is orthogonal to the kernel of `L_x`.
    rintro _ ⟨η, rfl⟩
    refine (Submodule.mem_orthogonal _ _).2 ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hy ⊢
    rw [← inner_sobolevGaugeFixedOperator_sobolevFieldValues hx.continuous hax, hy,
      inner_zero_left]
  · -- A class orthogonal to the range solves `L_x u = 0` weakly, so it is in the kernel.
    rw [← Submodule.orthogonal_orthogonal R]
    refine Submodule.orthogonal_le fun u hu ↦ ?_
    have hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ =
          ∫ z, ⟪(0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) z, η z⟫ := fun η hη hηc ↦ by
      rw [integral_inner_gaugeFixedAdjoint_eq_zero_of_mem_orthogonal hax hu hη hηc,
        integral_congr_ae (((Lp.coeFn_zero _ 2 μ⊤).filter_mono
          (ae_mono (Measure.restrict_coe_opens_top _).ge)).mono
          fun z hz ↦ by rw [hz, Pi.zero_apply, inner_zero_left])]
      exact (integral_zero _ _).symm
    obtain ⟨w, hw, hw0⟩ :=
      exists_sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq hx.continuous hax
        ((Lp.memLp u).mono_measure (Measure.restrict_coe_opens_top _).ge) hweak
    refine ⟨w, LinearMap.mem_ker.2 hw0, Lp.ext ?_⟩
    rw [ContinuousLinearMap.coe_coe]
    filter_upwards [sobolevFieldValues_ae_eq w,
      ae_all_iff.2 fun j ↦ ae_mono (Measure.restrict_coe_opens_top _).le (hw j)] with z h₁ h₂
    rw [h₁]
    ext j
    simp [h₂ j]

/-- **The cokernel of `L_x*` on `H¹` is the kernel of `L_x`.** At a `C¹` vortex `x` with
`|α| → 1` at infinity and with `L∞` class `a`, when the kernel of the realization of `L_x` is
finite dimensional, the cokernel `L² ⧸ range L_x*` is isomorphic to that kernel, through the
orthogonal complement of the range (`range_sobolevGaugeFixedAdjoint`). Its inverse sends `y` to the
class of its values (`sobolevGaugeFixedAdjointCokernelEquiv_symm_apply`). -/
def sobolevGaugeFixedAdjointCokernelEquiv (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) [FiniteDimensional ℝ (sobolevGaugeFixedOperator a).ker] :
    (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ ⧸ (sobolevGaugeFixedAdjoint a).range) ≃ₗ[ℝ]
      (sobolevGaugeFixedOperator a).ker :=
  let K := (sobolevGaugeFixedOperator a).ker.map sobolevFieldValues.toLinearMap
  let e : (sobolevGaugeFixedOperator a).ker ≃ₗ[ℝ] K :=
    Submodule.equivMapOfInjective _ sobolevFieldValues_injective _
  have : FiniteDimensional ℝ K := Module.Finite.equiv e
  (Submodule.quotEquivOfEq _ _ (range_sobolevGaugeFixedAdjoint hx hsol hlim hax)).trans
    ((Submodule.quotientEquivOfIsCompl _ _
      (Submodule.isCompl_orthogonal (K := K)).symm).trans e.symm)

/-- The inverse of `sobolevGaugeFixedAdjointCokernelEquiv` sends an element `y` of the kernel of
the realization of `L_x` to the class of its values modulo the range of `L_x*`. -/
theorem sobolevGaugeFixedAdjointCokernelEquiv_symm_apply (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) [FiniteDimensional ℝ (sobolevGaugeFixedOperator a).ker]
    (y : (sobolevGaugeFixedOperator a).ker) :
    (sobolevGaugeFixedAdjointCokernelEquiv hx hsol hlim hax).symm y =
      Submodule.Quotient.mk (sobolevFieldValues (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)) := by
  simp only [sobolevGaugeFixedAdjointCokernelEquiv, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, Submodule.quotientEquivOfIsCompl_symm_apply]
  rw [LinearEquiv.symm_apply_eq, Submodule.quotEquivOfEq_mk,
    Submodule.coe_equivMapOfInjective_apply, ContinuousLinearMap.coe_coe]

/-- **The realization of `L_x*` on `H¹` is Fredholm** at a `C¹` vortex `x` with `|α| → 1` at
infinity and with `L∞` class `a`, when the kernel of the realization of `L_x` is finite
dimensional. Its kernel is trivial (`isClosedEmbedding_sobolevGaugeFixedAdjoint`), and its
cokernel is finite dimensional because its range is the orthogonal complement of the values of
that kernel (`range_sobolevGaugeFixedAdjoint`). -/
theorem isFredholm_sobolevGaugeFixedAdjoint (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) [FiniteDimensional ℝ (sobolevGaugeFixedOperator a).ker] :
    (sobolevGaugeFixedAdjoint a).IsFredholm :=
  (isClosedEmbedding_sobolevGaugeFixedAdjoint hx hsol hlim hax).isFredholm
    (Module.Finite.equiv (sobolevGaugeFixedAdjointCokernelEquiv hx hsol hlim hax).symm)

/-- **The index of `L_x*` on `H¹` is minus the dimension of the kernel of `L_x`** at a `C¹`
vortex `x` with `|α| → 1` at infinity and with `L∞` class `a`, when that kernel is finite
dimensional. -/
theorem index_sobolevGaugeFixedAdjoint_eq_neg_finrank_ker_sobolevGaugeFixedOperator
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) [FiniteDimensional ℝ (sobolevGaugeFixedOperator a).ker] :
    (sobolevGaugeFixedAdjoint a).index = -(finrank ℝ (sobolevGaugeFixedOperator a).ker : ℤ) := by
  rw [ContinuousLinearMap.index_of_injective _
      (isClosedEmbedding_sobolevGaugeFixedAdjoint hx hsol hlim hax).injective,
    (sobolevGaugeFixedAdjointCokernelEquiv hx hsol hlim hax).finrank_eq]

/-- **The realization of `L_x*` at a plane vortex has index `-2m`.** Let `x` be a continuous plane
vortex lying in the affine field space `A_m^k` for every `k`, with `L∞` class `a`. Then the
realization `L_x* : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` has index `-2m`: minus the real dimension `2m` of the
kernel of `L_x`
(`index_sobolevGaugeFixedAdjoint_eq_neg_finrank_ker_sobolevGaugeFixedOperator`). -/
theorem index_sobolevGaugeFixedAdjoint_eq_neg_two_mul {f : ContDiffBump (0 : ℝ)} {m : ℕ}
    (hx : Continuous x) (hmem : ∀ k : ℕ, x ∈ framedFieldSpace f m k)
    (hsol : ∀ z, equation x z = 0) (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedAdjoint a).index = -(2 * m : ℤ) := by
  have hhol (w : ℂ) : equation x w 1 = 0 ∧ equation x w 2 = 0 := by simp [hsol w]
  have := finiteDimensional_ker_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace hx hmem
    hhol hax
  rw [index_sobolevGaugeFixedAdjoint_eq_neg_finrank_ker_sobolevGaugeFixedOperator
      ((contDiff_of_forall_mem_framedFieldSpace hx hmem).of_le (by simp)) hsol
      (tendsto_normSq_of_forall_mem_framedFieldSpace hx hmem) hax,
    finrank_ker_sobolevGaugeFixedOperator_eq_two_mul hx hmem hhol hax]
  omega

end TauCeti.Vortex
