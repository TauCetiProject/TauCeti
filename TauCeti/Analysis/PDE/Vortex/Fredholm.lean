/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.SobolevRealization
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import TauCeti.Analysis.PDE.Vortex.EllipticRegularity
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Calculus.ContDiff.WithLp

/-!
# The gauge-fixed vortex operator on `H¹` is Fredholm and surjective

At a field `x`, the realization `L_x : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` of the gauge-fixed vortex operator
(`TauCeti.Vortex.sobolevGaugeFixedOperator`) acts on variations whose coordinates lie in
`W^{1,2}(ℂ)`, through their weak gradients. At a vortex with `|α| → 1` and `∇₁ α → 0` at infinity it
has a finite-dimensional kernel and a closed range
(`TauCeti.Vortex.finiteDimensional_ker_sobolevGaugeFixedOperator`,
`TauCeti.Vortex.isClosed_range_sobolevGaugeFixedOperator`). This file shows that its cokernel
vanishes, so that it is a Fredholm operator in the sense of Mathlib's
`ContinuousLinearMap.IsFredholm`, whose index is the real dimension of its kernel
(`LinearMap.index_of_surjective`).

The realization is the weak operator of `TauCeti.Analysis.PDE.Vortex.RightInverse`: for every
`y ∈ H¹(ℂ)⁴` and every compactly supported `C¹` test field `η`,

`∫ ⟪L_x y, η⟫ = ∫ ⟪y, L_x* η⟫`

(`TauCeti.Vortex.integral_inner_sobolevGaugeFixedOperator`). Both sides are continuous in `y`, and
for fields of test functions this is the classical integration by parts
`TauCeti.Vortex.integral_inner_gaugeFixedOperator`; test functions are dense in `H¹(ℂ)`
(`TauCeti.W1p.denseRange_ofTestFunctionₗ_top`).

At a vortex, every `f ∈ L²` is weakly `L_x y` for some `y` in the Sobolev space `H¹` of the
framed field space, by the weak right inverse and elliptic regularity
(`TauCeti.Vortex.exists_mem_sobolevFields_one_integral_inner_gaugeFixedAdjoint_eq`). Each
coordinate of `y` is the value of an element of `W^{1,2}(ℂ)`
(`TemperedDistribution.exists_w1p_value_ae_eq_of_mem_realSobolevFunctions`), and by the weak form
above the realization maps the resulting element of `H¹(ℂ)⁴` to an `L²` field with the same
pairings against test fields as `f`. Smooth compactly supported test functions separate locally
integrable functions (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`), so it maps it to `f`.

## Main results

All in the namespace `TauCeti.Vortex`:

* `integral_inner_sobolevGaugeFixedOperator`: the realization is the weak operator `L_x`, tested
  against compactly supported `C¹` fields.
* `surjective_sobolevGaugeFixedOperator`: at a `C¹` vortex with `|α| → 1` at infinity, the
  realization `H¹ → L²` is surjective.
* `isFredholm_sobolevGaugeFixedOperator`: if moreover `∇₁ α → 0` at infinity, the realization is
  Fredholm.

The value `2m` of the index for a vortex framed in degree `m` needs, beyond this, the comparison of
the kernel of the realization with the classical kernel of `L_x`, which is not treated here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology InnerProductSpace Distributions

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-- The values of the four coordinates of an element of `H¹(ℂ)⁴`, as an `L²` field. -/
private def sobolevValues :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ :=
  ∑ j : Fin 4, ((ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single j (1 : ℝ))).compLpL 2 μ⊤).comp
      ((W1p.valueL).comp (ContinuousLinearMap.proj j))

private theorem sobolevValues_ae_eq (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevValues y =ᵐ[μ⊤] fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y j) z := by
  have hv : ∀ᵐ z ∂μ⊤, ∀ j : Fin 4,
      (ContinuousLinearMap.compLpL 2 μ⊤ (ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single j (1 : ℝ))) (W1p.value (y j))) z =
          W1p.value (y j) z • EuclideanSpace.single j (1 : ℝ) :=
    ae_all_iff.2 fun j ↦ (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.single j (1 : ℝ))).coeFn_compLpL (W1p.value (y j))
  filter_upwards [Lp.coeFn_finsetSum (μ := μ⊤) (p := 2) Finset.univ fun j : Fin 4 ↦
      ContinuousLinearMap.compLpL 2 μ⊤ (ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single j (1 : ℝ))) (W1p.value (y j)), hv] with z hs hv
  simp only [sobolevValues, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, W1p.valueL_apply]
  rw [hs, Finset.sum_apply]
  simp_rw [hv]
  ext i
  simp [Pi.single_apply]

/-- The weak form of the realization on a field of test functions: the classical integration by
parts `integral_inner_gaugeFixedOperator`. -/
private theorem integral_inner_sobolevGaugeFixedOperator_ofTestFunctionₗ
    {x : ℂ → EuclideanSpace ℝ (Fin 4)} (hx : Continuous x)
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} (hax : a =ᵐ[μ⊤] x) (φ : Fin 4 → 𝓓((⊤ : Opens ℂ), ℝ))
    {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 1 η) :
    ∫ z, ⟪sobolevGaugeFixedOperator a (fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) z,
      η z⟫_ℝ =
      ∫ z, ⟪(WithLp.toLp 2 fun j ↦ W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) z :
        EuclideanSpace ℝ (Fin 4)), gaugeFixedAdjoint x η z⟫_ℝ := by
  set Y : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ WithLp.toLp 2 fun j ↦ φ j z
  have hY : ContDiff ℝ 1 Y := ((contDiff_piLp 2).2 fun j ↦ (φ j).contDiff).of_le (by simp)
  have hYc : HasCompactSupport Y :=
    (hasCompactSupport_pi_iff.2 fun j ↦ (φ j).hasCompactSupport).comp_left (g := WithLp.toLp 2)
      (WithLp.toLp_zero 2)
  have hval : ∀ᵐ z ∂(volume : Measure ℂ), ∀ j : Fin 4,
      W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) z = φ j z :=
    ae_all_iff.2 fun j ↦ W1p.value_ofTestFunctionₗ_top_ae (φ j)
  have hop := sobolevGaugeFixedOperator_ae_eq_gaugeFixedOperator hax
    (y := fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) hY
    fun j ↦ W1p.value_ofTestFunctionₗ_ae (φ j)
  simp only [Opens.coe_top, Measure.restrict_univ] at hop
  calc ∫ z, ⟪sobolevGaugeFixedOperator a (fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) z,
        η z⟫_ℝ = ∫ z, ⟪gaugeFixedOperator x Y z, η z⟫_ℝ :=
        integral_congr_ae (hop.mono fun z hz ↦ by simp only [hz])
    _ = ∫ z, ⟪Y z, gaugeFixedAdjoint x η z⟫_ℝ := integral_inner_gaugeFixedOperator hx hY hYc hη
    _ = _ := integral_congr_ae (hval.mono fun z hz ↦ by simp only [Y, hz])

/-- **The realization is the weak operator `L_x`.** Let `x` be a continuous field with `L∞` class
`a`. For every `y ∈ H¹(ℂ)⁴` and every compactly supported `C¹` field `η`, the pairing of the
realization `L_x y` with `η` is the pairing of the values of `y` with `L_x* η`. -/
theorem integral_inner_sobolevGaugeFixedOperator {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Continuous x) {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} (hax : a =ᵐ[μ⊤] x)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪sobolevGaugeFixedOperator a y z, η z⟫_ℝ =
      ∫ z, ⟪(WithLp.toLp 2 fun j ↦ W1p.value (y j) z : EuclideanSpace ℝ (Fin 4)),
        gaugeFixedAdjoint x η z⟫_ℝ := by
  have hηL : MemLp η 2 μ⊤ := hη.continuous.memLp_of_hasCompactSupport hηc
  have hGL : MemLp (gaugeFixedAdjoint x η) 2 μ⊤ :=
    (continuous_gaugeFixedAdjoint hx hη).memLp_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint hηc)
  -- Both sides are `L²` inner products, continuous in `y`.
  have hL (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
      ∫ z, ⟪sobolevGaugeFixedOperator a y z, η z⟫_ℝ =
        ⟪sobolevGaugeFixedOperator a y, hηL.toLp η⟫_ℝ := by
    have h := hηL.coeFn_toLp
    rw [L2.inner_def]
    simp only [Opens.coe_top, Measure.restrict_univ] at h ⊢
    refine integral_congr_ae ?_
    filter_upwards [h] with z hz
    rw [hz]
  have hR (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
      ∫ z, ⟪(WithLp.toLp 2 fun j ↦ W1p.value (y j) z : EuclideanSpace ℝ (Fin 4)),
        gaugeFixedAdjoint x η z⟫_ℝ = ⟪sobolevValues y, hGL.toLp _⟫_ℝ := by
    have h := hGL.coeFn_toLp
    have hv := sobolevValues_ae_eq y
    rw [L2.inner_def]
    simp only [Opens.coe_top, Measure.restrict_univ] at h hv ⊢
    refine integral_congr_ae ?_
    filter_upwards [h, hv] with z hz hv
    rw [hz, hv]
  rw [hL, hR]
  refine (DenseRange.piMap fun _ : Fin 4 ↦
    W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 2) (by norm_num)).induction_on
      (p := fun y ↦ ⟪sobolevGaugeFixedOperator a y, hηL.toLp η⟫_ℝ =
        ⟪sobolevValues y, hGL.toLp _⟫_ℝ) y
      (isClosed_eq (((sobolevGaugeFixedOperator a).continuous).inner continuous_const)
        ((sobolevValues.continuous).inner continuous_const)) fun φ ↦ ?_
  rw [← hL, ← hR]
  exact integral_inner_sobolevGaugeFixedOperator_ofTestFunctionₗ hx hax φ hη

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}

/-- **The cokernel of `L_x : H¹ → L²` vanishes** at a `C¹` vortex `x` with `|α| → 1` at infinity
and with `L∞` class `a`: every `f ∈ L²(ℂ; ℝ⁴)` is `L_x y` for some `y ∈ H¹(ℂ)⁴`. -/
theorem surjective_sobolevGaugeFixedOperator (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    Function.Surjective (sobolevGaugeFixedOperator a) := by
  intro f
  have hf := Lp.memLp f
  have hLw (w) := Lp.memLp (sobolevGaugeFixedOperator a w)
  simp only [Opens.coe_top, Measure.restrict_univ] at hf hLw
  -- A weak solution `y ∈ H¹` of `L_x y = f`, and the element `w` of `H¹(ℂ)⁴` representing it.
  obtain ⟨y, hy, hweak⟩ := exists_mem_sobolevFields_one_integral_inner_gaugeFixedAdjoint_eq hx
    (fun z ↦ Lp.norm_le_norm_top_of_ae_eq_of_continuousAt hax hx.continuous.continuousAt) hsol
    hlim hf
  choose w hw using fun j ↦
    TemperedDistribution.exists_w1p_value_ae_eq_of_mem_realSobolevFunctions (p := 2)
      (by norm_num) (by norm_num) le_rfl (mem_sobolevFields.1 hy j)
  refine ⟨w, Lp.ext (ae_restrict_of_ae ?_)⟩
  set F : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ sobolevGaugeFixedOperator a w z - f z
  have hFL : MemLp F 2 volume := (hLw w).sub hf
  -- `F` is orthogonal to every compactly supported `C²` field.
  have horth (η : ℂ → EuclideanSpace ℝ (Fin 4)) (hη : ContDiff ℝ 2 η)
      (hηc : HasCompactSupport η) : ∫ z, ⟪F z, η z⟫_ℝ = 0 := by
    have hη₂ : MemLp η 2 volume := hη.continuous.memLp_of_hasCompactSupport hηc
    have hvals : (fun z ↦ (WithLp.toLp 2 fun j ↦ W1p.value (w j) z : EuclideanSpace ℝ (Fin 4)))
        =ᵐ[volume] y := by
      filter_upwards [ae_all_iff.2 hw] with z hz
      ext j
      simp [hz j]
    simp only [F, inner_sub_left]
    rw [integral_sub ((hLw w).integrable_inner hη₂)
        (hf.integrable_inner hη₂),
      integral_inner_sobolevGaugeFixedOperator hx.continuous hax w (hη.of_le one_le_two) hηc,
      ← hweak η hη hηc, sub_eq_zero]
    exact integral_congr_ae (hvals.mono fun z hz ↦ by simp only [hz])
  -- Smooth compactly supported functions separate locally integrable fields.
  have hF : ∀ᵐ z ∂(volume : Measure ℂ), F z = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero (hFL.locallyIntegrable (by norm_num))
      fun g hg hgc ↦ ?_
    by_cases hint : Integrable (fun z ↦ g z • F z)
    · refine integral_eq_zero_of_forall_integral_inner_eq_zero ℝ _ hint fun v ↦ ?_
      have h := horth (fun z ↦ g z • v) ((hg.of_le (by simp)).smul_const v)
        (hgc.smul_right (f' := fun _ ↦ v))
      refine (integral_congr_ae (ae_of_all _ fun z ↦ ?_)).trans h
      simp only [real_inner_smul_right, real_inner_comm v]
    · exact integral_undef hint
  filter_upwards [hF] with z hz
  exact sub_eq_zero.1 hz

/-- **`L_x : H¹ → L²` is Fredholm** at a `C¹` vortex `x` with `|α| → 1` and `∇₁ α → 0` at
infinity and with `L∞` class `a`. It is surjective (`surjective_sobolevGaugeFixedOperator`), so its
index is the real dimension of its kernel. -/
theorem isFredholm_sobolevGaugeFixedOperator (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).IsFredholm := by
  have hsurj := surjective_sobolevGaugeFixedOperator hx hsol hlim hax
  have := finiteDimensional_ker_sobolevGaugeFixedOperator hx hsol hlim hcov hax
  exact (Function.Surjective.isFredholm_iff _ hsurj).2
    ⟨(sobolevGaugeFixedOperator a).isQuotientMap hsurj,
      Submodule.ClosedComplemented.of_finiteDimensional _, this⟩

end TauCeti.Vortex
