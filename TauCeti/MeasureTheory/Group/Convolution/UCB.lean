/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import TauCeti.MeasureTheory.Function.Lp.One
public import TauCeti.Topology.Algebra.Group.UCB.Basic

import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import TauCeti.MeasureTheory.Group.ModularCharacter

/-!
# Convolution of `L¹` with `L∞` on a locally compact group

Let `μ` be a regular left Haar measure on a locally compact group `G`. For `h ∈ L¹(G, μ)` and
`φ ∈ L∞(G, μ)` the convolution

```text
(h ⋆ φ) x = ∫ y, h y * φ (y⁻¹ * x) ∂μ
```

is an actual function, defined at every point and not only almost everywhere, and it lies in
`TauCeti.UCB G`: it is bounded by `‖h‖₁ ‖φ‖∞`, and it is uniformly continuous under small left
multiplication. Indeed, by left invariance of `μ`,

```text
(h ⋆ φ) (u * x) = (h (u * ·) ⋆ φ) x,
```

so `|(h ⋆ φ) (u * x) - (h ⋆ φ) x| ≤ ‖h (u * ·) - h‖₁ ‖φ‖∞`, and left translation is continuous
on `L¹(G, μ)`. The resulting operator `MeasureTheory.Lp.convolutionUCB h : L∞(G, μ) →L[ℝ] UCB G`
has norm at most `‖h‖₁`, depends linearly on `h`, is positive when `h ≥ 0`, and sends the
constant one to the constant `∫ h dμ`.

The point evaluation needs no σ-finiteness of `μ`: for each `x`, the map `y ↦ y⁻¹ * x` is the
composite of inversion and right translation, which preserve the null sets of a regular Haar
measure. So `y ↦ φ (y⁻¹ * x)` is well defined almost everywhere, and the value of `h ⋆ φ` at `x`
does not depend on the representatives of `h` and `φ`.

These operators turn essentially bounded functions into functions in `UCB G`, the space on which
invariant means of a topological group are defined, so they are the tool for comparing invariant
means on `UCB G` with invariant means on `L∞(G, μ)`.

## Main definitions

* `MeasureTheory.Lp.convolutionUCB h`: the operator `φ ↦ h ⋆ φ` from `L∞(G, μ)` to `UCB G`.
* `MeasureTheory.Lp.convolutionUCBL`: the continuous bilinear map `h ↦ (φ ↦ h ⋆ φ)`.

## Main results

* `MeasureTheory.Lp.convolutionUCB_apply`: the formula `(h ⋆ φ) x = ∫ y, h y * φ (y⁻¹ * x) ∂μ`,
  and `MeasureTheory.Lp.convolutionUCB_apply_of_ae_eq` for arbitrary representatives.
* `MeasureTheory.Lp.convolutionUCB_apply_mul`: `(h ⋆ φ) (u * x) = (h (u * ·) ⋆ φ) x`.
* `MeasureTheory.Lp.norm_convolutionUCB_le`: the operator norm is at most `‖h‖₁`.
* `MeasureTheory.Lp.continuous_convolutionUCB`: `h ⋆ ·` depends continuously on `h ∈ L¹(G, μ)`.
* `MeasureTheory.Lp.convolutionUCB_nonneg`: `h ⋆ φ ≥ 0` when `h ≥ 0` and `φ ≥ 0`.
* `MeasureTheory.Lp.convolutionUCB_linftyOne`: `h ⋆ 1 = (∫ h dμ) • 1`.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, proof of Theorem G.3.1.
-/

public section

noncomputable section

open Filter Topology DomMulAct
open scoped BoundedContinuousFunction ENNReal

namespace MeasureTheory.Lp

open TauCeti Measure

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] [μ.Regular]

/-- The translated function `y ↦ φ (y⁻¹ * x)` is bounded by `‖φ‖` almost everywhere. -/
private theorem ae_norm_comp_inv_mul_le (φ : Lp ℝ ∞ μ) (x : G) :
    ∀ᵐ y ∂μ, ‖φ (y⁻¹ * x)‖ ≤ ‖φ‖ :=
  (quasiMeasurePreserving_inv_mul_of_regular μ x).ae (ae_le_lpNorm_exponent_top (Lp.memLp φ))

private theorem integrable_mul_comp_inv_mul (h : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) (x : G) :
    Integrable (fun y => h y * φ (y⁻¹ * x)) μ :=
  (L1.integrable_coeFn h).mul_bdd
    ((Lp.aestronglyMeasurable φ).comp_quasiMeasurePreserving
      (quasiMeasurePreserving_inv_mul_of_regular μ x))
    (ae_norm_comp_inv_mul_le φ x)

/-- The convolution `x ↦ ∫ y, h y * φ (y⁻¹ * x) ∂μ` as a function. -/
private def convFun (h : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) (x : G) : ℝ :=
  ∫ y, h y * φ (y⁻¹ * x) ∂μ

private theorem convFun_of_ae_eq {h : Lp ℝ 1 μ} {φ : Lp ℝ ∞ μ} {h' φ' : G → ℝ}
    (hh : h =ᵐ[μ] h') (hφ : φ =ᵐ[μ] φ') (x : G) :
    convFun h φ x = ∫ y, h' y * φ' (y⁻¹ * x) ∂μ := by
  refine integral_congr_ae ?_
  filter_upwards [hh, (quasiMeasurePreserving_inv_mul_of_regular μ x).ae_eq_comp hφ] with y hy hy'
  simp only [Function.comp_apply] at hy'
  rw [hy, hy']

private theorem abs_convFun_le (h : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) (x : G) :
    |convFun h φ x| ≤ ‖h‖ * ‖φ‖ := by
  rw [← Real.norm_eq_abs, L1.norm_eq_integral_norm, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((L1.integrable_coeFn h).norm.mul_const _) ?_
  filter_upwards [ae_norm_comp_inv_mul_le φ x] with y hy
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)

private theorem convFun_add_left (h k : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) (x : G) :
    convFun (h + k) φ x = convFun h φ x + convFun k φ x := by
  simp only [convFun]
  rw [← integral_add (integrable_mul_comp_inv_mul h φ x)
    (integrable_mul_comp_inv_mul k φ x)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add h k] with y hy
  rw [hy, Pi.add_apply, add_mul]

private theorem convFun_sub_left (h k : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) (x : G) :
    convFun (h - k) φ x = convFun h φ x - convFun k φ x := by
  simp only [convFun]
  rw [← integral_sub (integrable_mul_comp_inv_mul h φ x) (integrable_mul_comp_inv_mul k φ x)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub h k] with y hy
  rw [hy, Pi.sub_apply, sub_mul]

omit [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [BorelSpace G]
  [μ.IsHaarMeasure] [μ.Regular] in
private theorem convFun_smul_left (c : ℝ) (h : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) (x : G) :
    convFun (c • h) φ x = c * convFun h φ x := by
  rw [convFun, convFun, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul c h] with y hy
  rw [hy, Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem convFun_add_right (h : Lp ℝ 1 μ) (φ ψ : Lp ℝ ∞ μ) (x : G) :
    convFun h (φ + ψ) x = convFun h φ x + convFun h ψ x := by
  simp only [convFun]
  rw [← integral_add (integrable_mul_comp_inv_mul h φ x)
    (integrable_mul_comp_inv_mul h ψ x)]
  refine integral_congr_ae ?_
  filter_upwards [(quasiMeasurePreserving_inv_mul_of_regular μ x).ae (Lp.coeFn_add φ ψ)] with y hy
  rw [hy, Pi.add_apply, mul_add]

private theorem convFun_smul_right (c : ℝ) (h : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) (x : G) :
    convFun h (c • φ) x = c * convFun h φ x := by
  rw [convFun, convFun, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [(quasiMeasurePreserving_inv_mul_of_regular μ x).ae (Lp.coeFn_smul c φ)] with y hy
  rw [hy, Pi.smul_apply, smul_eq_mul, mul_left_comm]

/-- Left translation of the argument of `h ⋆ φ` moves to the kernel `h`. -/
private theorem convFun_mul (h : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) (u x : G) :
    convFun h φ (u * x) = convFun (mk u • h) φ x := by
  rw [convFun_of_ae_eq (smul_Lp_ae_eq (mk u) h) (ae_eq_refl _) x, convFun,
    ← integral_mul_left_eq_self _ u]
  simp [mul_assoc]

private theorem convFun_mem_ucb (h : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) :
    ∀ ε > 0, ∀ᶠ u in 𝓝 (1 : G), ∀ x, dist (convFun h φ (u * x)) (convFun h φ x) < ε := by
  intro ε hε
  have hδ : 0 < ε / (‖φ‖ + 1) := div_pos hε (by positivity)
  -- Left translation is continuous on `L¹` of a regular Haar measure.
  have : Fact ((1 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.one_ne_top⟩
  have hc : Tendsto (fun u : G => mk u • h) (𝓝 1) (𝓝 h) := by
    have hcont : Continuous fun u : G => mk u • h := continuous_mk.smul continuous_const
    simpa using hcont.tendsto 1
  filter_upwards [Metric.tendsto_nhds.1 hc _ hδ] with u hu x
  have hsub : convFun h φ (u * x) - convFun h φ x = convFun (mk u • h - h) φ x := by
    rw [convFun_sub_left, convFun_mul]
  rw [Real.dist_eq, hsub]
  calc |convFun (mk u • h - h) φ x| ≤ ‖mk u • h - h‖ * ‖φ‖ := abs_convFun_le _ _ _
    _ ≤ ε / (‖φ‖ + 1) * ‖φ‖ := by
        gcongr
        rw [← _root_.dist_eq_norm]
        exact hu.le
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-- The convolution `h ⋆ φ` as a bounded continuous function. -/
private def convBCF (h : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) : G →ᵇ ℝ :=
  .ofNormedAddCommGroup (convFun h φ)
    (continuous_of_forall_eventually_dist_mul_lt (convFun_mem_ucb h φ)) (‖h‖ * ‖φ‖)
    (abs_convFun_le h φ)

private theorem convBCF_mem_ucb (h : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) : convBCF h φ ∈ ucb G := by
  rw [mem_ucb_iff]
  simpa [convBCF, Real.dist_eq] using convFun_mem_ucb h φ

/-- The convolution `φ ↦ h ⋆ φ` as a linear map from `L∞` to `UCB G`. -/
private def convLinear (h : Lp ℝ 1 μ) : Lp ℝ ∞ μ →ₗ[ℝ] UCB G where
  toFun φ := ⟨convBCF h φ, convBCF_mem_ucb h φ⟩
  map_add' φ ψ := UCB.ext fun x => by simpa [convBCF] using convFun_add_right h φ ψ x
  map_smul' c φ := UCB.ext fun x => by simpa [convBCF] using convFun_smul_right c h φ x

/-- **Convolution of `L¹` with `L∞`.** For `h ∈ L¹(G, μ)`, the operator
`φ ↦ h ⋆ φ = (x ↦ ∫ y, h y * φ (y⁻¹ * x) ∂μ)` from `L∞(G, μ)` to `UCB G`. Its values are actual
functions, uniformly continuous under small left multiplication; the operator norm is at most
`‖h‖₁` (`MeasureTheory.Lp.norm_convolutionUCB_le`). -/
def convolutionUCB (h : Lp ℝ 1 μ) : Lp ℝ ∞ μ →L[ℝ] UCB G :=
  (convLinear h).mkContinuous ‖h‖ fun φ => by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x => ?_
    rw [Real.norm_eq_abs]
    exact abs_convFun_le h φ x

@[simp]
theorem convolutionUCB_apply (h : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) (x : G) :
    (convolutionUCB h φ : G →ᵇ ℝ) x = ∫ y, h y * φ (y⁻¹ * x) ∂μ :=
  (rfl)

/-- The value of `h ⋆ φ` at a point may be computed from any representatives of `h` and `φ`. -/
theorem convolutionUCB_apply_of_ae_eq {h : Lp ℝ 1 μ} {φ : Lp ℝ ∞ μ} {h' φ' : G → ℝ}
    (hh : h =ᵐ[μ] h') (hφ : φ =ᵐ[μ] φ') (x : G) :
    (convolutionUCB h φ : G →ᵇ ℝ) x = ∫ y, h' y * φ' (y⁻¹ * x) ∂μ :=
  convFun_of_ae_eq hh hφ x

/-- Left translation of the argument of `h ⋆ φ` moves to the kernel:
`(h ⋆ φ) (u * x) = (h (u * ·) ⋆ φ) x`. -/
theorem convolutionUCB_apply_mul (h : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) (u x : G) :
    (convolutionUCB h φ : G →ᵇ ℝ) (u * x) = (convolutionUCB (mk u • h) φ : G →ᵇ ℝ) x :=
  convFun_mul h φ u x

/-- The operator norm of `φ ↦ h ⋆ φ` is at most `‖h‖₁`. -/
theorem norm_convolutionUCB_le (h : Lp ℝ 1 μ) : ‖convolutionUCB h‖ ≤ ‖h‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg h) _

/-- `‖h ⋆ φ‖∞ ≤ ‖h‖₁ ‖φ‖∞`. -/
theorem norm_convolutionUCB_apply_le (h : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) :
    ‖convolutionUCB h φ‖ ≤ ‖h‖ * ‖φ‖ :=
  (convolutionUCB h).le_of_opNorm_le (norm_convolutionUCB_le h) φ

/-- Convolution is additive in the kernel. -/
@[simp]
theorem convolutionUCB_add (h k : Lp ℝ 1 μ) :
    convolutionUCB (h + k) = convolutionUCB h + convolutionUCB k := by
  ext φ x
  simpa [convFun] using convFun_add_left h k φ x

/-- Convolution is homogeneous in the kernel. -/
@[simp]
theorem convolutionUCB_smul (c : ℝ) (h : Lp ℝ 1 μ) :
    convolutionUCB (c • h) = c • convolutionUCB h := by
  ext φ x
  simpa [convFun] using convFun_smul_left c h φ x

/-- Convolution as a continuous bilinear map `h ↦ (φ ↦ h ⋆ φ)` from `L¹(G, μ)` and `L∞(G, μ)` to
`UCB G`, bounded by `‖h ⋆ φ‖∞ ≤ ‖h‖₁ ‖φ‖∞`. -/
def convolutionUCBL : Lp ℝ 1 μ →L[ℝ] Lp ℝ ∞ μ →L[ℝ] UCB G :=
  LinearMap.mkContinuous
    { toFun := convolutionUCB
      map_add' := convolutionUCB_add
      map_smul' := convolutionUCB_smul } 1
    fun h => by simpa using norm_convolutionUCB_le h

@[simp]
theorem convolutionUCBL_apply (h : Lp ℝ 1 μ) : convolutionUCBL h = convolutionUCB h :=
  (rfl)

/-- The operator `φ ↦ h ⋆ φ` depends continuously on the kernel `h ∈ L¹(G, μ)`. -/
theorem continuous_convolutionUCB :
    Continuous (convolutionUCB : Lp ℝ 1 μ → Lp ℝ ∞ μ →L[ℝ] UCB G) :=
  convolutionUCBL.continuous

@[simp]
theorem convolutionUCB_zero : convolutionUCB (0 : Lp ℝ 1 μ) = 0 :=
  map_zero (convolutionUCBL (G := G))

@[simp]
theorem convolutionUCB_neg (h : Lp ℝ 1 μ) : convolutionUCB (-h) = -convolutionUCB h :=
  map_neg convolutionUCBL h

@[simp]
theorem convolutionUCB_sub (h k : Lp ℝ 1 μ) :
    convolutionUCB (h - k) = convolutionUCB h - convolutionUCB k :=
  map_sub convolutionUCBL h k

/-- Convolution with a nonnegative kernel is positive. -/
theorem convolutionUCB_nonneg {h : Lp ℝ 1 μ} (hh : 0 ≤ h) {φ : Lp ℝ ∞ μ} (hφ : 0 ≤ φ) :
    0 ≤ convolutionUCB h φ := by
  refine UCB.le_def.2 fun x => ?_
  rw [convolutionUCB_apply]
  refine (integral_nonneg_of_ae ?_).trans_eq' (by simp)
  filter_upwards [(Lp.coeFn_nonneg h).2 hh,
    (quasiMeasurePreserving_inv_mul_of_regular μ x).ae ((Lp.coeFn_nonneg φ).2 hφ)] with y hy hy'
  exact mul_nonneg hy hy'

/-- Convolution with a nonnegative kernel is monotone. -/
theorem convolutionUCB_mono {h : Lp ℝ 1 μ} (hh : 0 ≤ h) {φ ψ : Lp ℝ ∞ μ} (hφψ : φ ≤ ψ) :
    convolutionUCB h φ ≤ convolutionUCB h ψ := by
  simpa using convolutionUCB_nonneg hh (sub_nonneg.2 hφψ)

/-- Convolution with the constant one is the constant `∫ h dμ`. -/
@[simp]
theorem convolutionUCB_linftyOne (h : Lp ℝ 1 μ) :
    convolutionUCB h linftyOne = (∫ y, h y ∂μ) • 1 := by
  refine UCB.ext fun x => ?_
  rw [convolutionUCB_apply_of_ae_eq (ae_eq_refl _) coeFn_linftyOne x]
  simp

end MeasureTheory.Lp
