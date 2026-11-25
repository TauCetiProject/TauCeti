/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Garding
public import TauCeti.Analysis.Sobolev.W1p.Basic
public import Mathlib.MeasureTheory.Function.Holder
import TauCeti.Analysis.Sobolev.W1p.Density
public import TauCeti.Analysis.Sobolev.W1p.Zero
import TauCeti.Analysis.Sobolev.W1p.LocalCompactness
import TauCeti.Analysis.Sobolev.W1p.Restriction
import TauCeti.Analysis.Normed.Operator.Compact.Estimate
import TauCeti.Analysis.Normed.Operator.Compact.Pi
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.Topology.Algebra.Support
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Normed.Group.Pi
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Fredholm.Criteria
public import TauCeti.Analysis.Fredholm.OrthogonalSplitting

/-!
# The gauge-fixed vortex operator on `H¹`: kernel, range and orthogonal splittings

At a field `x = (b₁, b₂, p, q)`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁`
(`TauCeti.Vortex.gaugeFixedOperator`) is a first-order operator with constant leading part and
zeroth-order coefficients linear in `x`:

`L_x y = F(∇y₀, ∇y₁, ∇y₂, ∇y₃) + Z(x, y)`

(`TauCeti.Vortex.gaugeFixedOperator_eq_gaugeFixedFirstOrder_add`), where `F`
(`TauCeti.Vortex.gaugeFixedFirstOrder`) reads off the four first-order rows
`∂₁y₀ + ∂₂y₁`, `∂₂y₀ - ∂₁y₁`, `∂₁y₂ - ∂₂y₃`, `∂₁y₃ + ∂₂y₂` from the gradients of the coordinates,
and `Z` (`TauCeti.Vortex.gaugeFixedZerothOrder`) is bilinear in the values of `x` and `y`.

This file realizes `L_x` as a bounded operator

`TauCeti.Vortex.sobolevGaugeFixedOperator a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)`

on variations whose four coordinates lie in `H¹(ℂ) = W^{1,2}(ℂ)` (`TauCeti.W1p`), with the weak
gradients in the leading part. The coefficient enters through its `L∞` class `a`, so the
operator depends only on the almost-everywhere class of the field, and for a bounded measurable
field `x` one takes `a` with `a = x` almost everywhere. The domain carries the product norm, the
largest of the `H¹` norms of the four coordinates; the inclusion
`TauCeti.Vortex.sobolevFieldValues : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` is injective
(`TauCeti.Vortex.sobolevFieldValues_injective`) and gives it the `L²` pairing. Its values are
given almost everywhere by the same formula with weak gradients
(`TauCeti.Vortex.sobolevGaugeFixedOperator_apply_ae`), and on variations with a `C¹`
representative it is the classical operator
(`TauCeti.Vortex.sobolevGaugeFixedOperator_ae_eq_gaugeFixedOperator`). Changing the coefficient
changes only the zeroth-order part (`TauCeti.Vortex.sobolevGaugeFixedOperator_sub_apply_ae`), so
the realization depends Lipschitz continuously on `a` in operator norm
(`TauCeti.Vortex.exists_lipschitzWith_sobolevGaugeFixedOperator`).

At a `C¹` vortex `x` with `|α| → 1` and `∇₁ α → 0` at infinity and with an `L∞` class `a`, so
that its coordinates are bounded by `‖a‖`, the Gårding inequality
`TauCeti.Vortex.exists_integral_gaugeFixedGradientDensity_add_mul_integral_norm_sq_le` bounds the
covariant gradient and the `L²` norm of a test field by `‖L_x y‖²` and the `L²` norm of `y` on a
disc. The covariant gradient controls the flat gradient up to the norm of the field, bounded by
`‖a‖` (`TauCeti.Vortex.sum_norm_gradient_sq_le`), and test fields are dense in `H¹(ℂ)`
(`TauCeti.W1p.denseRange_ofTestFunctionₗ_top`). This gives the coercive estimate
(`TauCeti.Vortex.exists_norm_sq_le_mul_norm_sobolevGaugeFixedOperator_sq_add`)

`‖y‖²_{H¹} ≤ C (‖L_x y‖²_{L²} + ‖y‖²_{L²(B_R)})`  for every `y ∈ H¹(ℂ)⁴`.

The restriction `H¹(ℂ) → L²(B_R)` is compact (`TauCeti.W1p.isCompactOperator_valueL_restrictL`),
so by Peetre's lemma (`ContinuousLinearMap.finiteDimensional_ker_of_compact_estimate`,
`ContinuousLinearMap.isClosed_range_of_compact_estimate`) the realization has a
finite-dimensional kernel and a closed range:

* `TauCeti.Vortex.finiteDimensional_ker_sobolevGaugeFixedOperator`;
* `TauCeti.Vortex.isClosed_range_sobolevGaugeFixedOperator`.

So `L_x : H¹ → L²` is upper semi-Fredholm at such a vortex. The vanishing of its cokernel is
proved in `TauCeti.Analysis.PDE.Vortex.Fredholm`. The value `2m` of its index at a continuous
plane vortex lying in `A_m^k` for every `k` is proved in `TauCeti.Analysis.PDE.Vortex.Index`.

Near a coefficient `a₀` at which the realization is onto with a finite-dimensional kernel, the
projections onto the kernels of `L_a` along their `L²`-orthogonal complements, and the right
inverses of `L_a` with values in those complements, depend continuously on `a`
(`TauCeti.Vortex.exists_continuousOn_orthogonal_rightInverse_sobolevGaugeFixedOperator`). This is
the general statement for Fredholm families,
`ContinuousLinearMap.IsFredholm.exists_continuousOn_orthogonal_rightInverse`, applied to the
Lipschitz family `a ↦ L_a` and the inclusion into `L²`.

Both are unique (`ContinuousLinearMap.IsOrthogonalKerProjection.unique`,
`ContinuousLinearMap.IsOrthogonalRightInverse.unique`): at every coefficient where `L_a` is onto
with a finite-dimensional kernel they are
`ContinuousLinearMap.orthogonalKerProjection sobolevFieldValues L_a` and
`ContinuousLinearMap.orthogonalRightInverse sobolevFieldValues L_a`, which are continuous in `L_a`
there (`ContinuousLinearMap.IsFredholm.continuousAt_orthogonalKerProjection`,
`ContinuousLinearMap.IsFredholm.continuousAt_orthogonalRightInverse`). Composed with a family of
vortex coefficients continuous in `L∞`, at which the realization is onto with a
finite-dimensional kernel (`TauCeti.Vortex.sobolevGaugeFixedOperator_surjective`,
`TauCeti.Vortex.finiteDimensional_ker_sobolevGaugeFixedOperator`), they give continuous kernel
projections and right inverses along that family
(`TauCeti.Vortex.continuous_orthogonalKerProjection_sobolevGaugeFixedOperator`,
`TauCeti.Vortex.continuous_orthogonalRightInverse_sobolevGaugeFixedOperator`). Since `a ↦ L_a`
is affine (`TauCeti.Vortex.sobolevGaugeFixedOperator_eq_add`), hence smooth
(`TauCeti.Vortex.contDiff_sobolevGaugeFixedOperator`), and over `ℝ` the projections and
right inverses are `C^n` in the operator
(`ContinuousLinearMap.IsFredholm.contDiffAt_orthogonalKerProjection`,
`ContinuousLinearMap.IsFredholm.contDiffAt_orthogonalRightInverse`), they are `C^n` along a family
of coefficients `C^n` in `L∞`
(`TauCeti.Vortex.contDiff_orthogonalKerProjection_sobolevGaugeFixedOperator`,
`TauCeti.Vortex.contDiff_orthogonalRightInverse_sobolevGaugeFixedOperator`). Along a family of
coefficients differentiable at a point, `L_a` is differentiable there
(`TauCeti.Vortex.differentiableAt_sobolevGaugeFixedOperator_comp`), and the derivative of `L_a`
in a direction `v` is the zeroth-order operator whose coefficient is the derivative of `a` in that
direction (`TauCeti.Vortex.fderiv_sobolevGaugeFixedOperator_comp_apply`).

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.1, for the Fredholm criterion with a compact error.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter Metric TopologicalSpace
open scoped ENNReal Topology InnerProductSpace Gradient Distributions

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-- The values of a variation `y ∈ H¹(ℂ)⁴`, as an element of `L²(ℂ; ℝ⁴)`: the inclusion
`H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)`, through which the `L²` pairing is taken on `H¹(ℂ)⁴`. -/
def sobolevFieldValues :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ :=
  ∑ j : Fin 4, ((ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single j (1 : ℝ))).compLpL 2 μ⊤).comp
      ((W1p.valueL).comp (ContinuousLinearMap.proj j))

/-- Almost everywhere, the `L²` values of a variation have the values of its four coordinates as
coordinates. -/
theorem sobolevFieldValues_ae_eq (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevFieldValues y =ᵐ[μ⊤] fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y j) z := by
  simp only [sobolevFieldValues, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, W1p.valueL_apply]
  have hv : ∀ᵐ z ∂μ⊤, ∀ j : Fin 4,
      (ContinuousLinearMap.compLpL 2 μ⊤ (ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single j (1 : ℝ))) (W1p.value (y j))) z =
          W1p.value (y j) z • EuclideanSpace.single j (1 : ℝ) :=
    ae_all_iff.2 fun j ↦ (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.single j (1 : ℝ))).coeFn_compLpL (W1p.value (y j))
  filter_upwards [Lp.coeFn_finsetSum (μ := μ⊤) (p := 2) Finset.univ fun j : Fin 4 ↦
      ContinuousLinearMap.compLpL 2 μ⊤ (ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single j (1 : ℝ))) (W1p.value (y j)), hv] with z h₁ h₂
  rw [h₁]
  simp only [Finset.sum_apply, h₂]
  ext i
  simp [WithLp.ofLp_sum, EuclideanSpace.single, Pi.single_apply]

/-- A variation is determined by its `L²` values. -/
theorem sobolevFieldValues_injective : Function.Injective sobolevFieldValues := by
  refine (injective_iff_map_eq_zero _).2 fun y hy ↦ funext fun j ↦ ?_
  refine W1p.ext_value ?_
  rw [Pi.zero_apply, W1p.value_zero]
  have h := sobolevFieldValues_ae_eq y
  rw [hy] at h
  refine Lp.ext_iff.2 ?_
  filter_upwards [h, Lp.coeFn_zero (EuclideanSpace ℝ (Fin 4)) 2 μ⊤, Lp.coeFn_zero ℝ 2 μ⊤]
    with z h₁ h₂ h₃
  rw [h₃]
  simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 4) ↦ v j) (h₁.symm.trans h₂)

/-- The realization `H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` of the gauge-fixed vortex operator `L_x`, whose
zeroth-order coefficients are given by the `L∞` class `a` of the field `x`. The leading part
acts on the weak gradients of the four coordinates. -/
def sobolevGaugeFixedOperator (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ :=
  ∑ j : Fin 4, ((gaugeFixedFirstOrder.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin 4 ↦ ℂ) j)).compLpL 2 μ⊤).comp
        ((W1p.gradientL).comp (ContinuousLinearMap.proj j)) +
    (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 a).comp sobolevFieldValues

/-- Almost everywhere, the realization is given by the formula of `L_x` with the weak gradients
and the values of the coordinates. -/
theorem sobolevGaugeFixedOperator_apply_ae (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevGaugeFixedOperator a y =ᵐ[μ⊤] fun z ↦
      gaugeFixedFirstOrder (fun j ↦ W1p.gradient (y j) z) +
        gaugeFixedZerothOrder (a z) (WithLp.toLp 2 fun j ↦ W1p.value (y j) z) := by
  simp only [sobolevGaugeFixedOperator, add_apply,
    FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.holderL_apply_apply, ContinuousLinearMap.proj_apply,
    W1p.gradientL_apply]
  have hg : ∀ᵐ z ∂μ⊤, ∀ j : Fin 4,
      (ContinuousLinearMap.compLpL 2 μ⊤
        (gaugeFixedFirstOrder.comp (ContinuousLinearMap.single ℝ (fun _ : Fin 4 ↦ ℂ) j))
          (W1p.gradient (y j))) z = gaugeFixedFirstOrder (Pi.single j (W1p.gradient (y j) z)) :=
    ae_all_iff.2 fun j ↦ (gaugeFixedFirstOrder.comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin 4 ↦ ℂ) j)).coeFn_compLpL (W1p.gradient (y j))
  set G := ∑ j : Fin 4, ContinuousLinearMap.compLpL 2 μ⊤
    (gaugeFixedFirstOrder.comp (ContinuousLinearMap.single ℝ (fun _ : Fin 4 ↦ ℂ) j))
      (W1p.gradient (y j))
  filter_upwards [Lp.coeFn_add G (gaugeFixedZerothOrder.holder 2 a (sobolevFieldValues y)),
    Lp.coeFn_finsetSum (μ := μ⊤) (p := 2) Finset.univ fun j : Fin 4 ↦
      ContinuousLinearMap.compLpL 2 μ⊤
        (gaugeFixedFirstOrder.comp (ContinuousLinearMap.single ℝ (fun _ : Fin 4 ↦ ℂ) j))
          (W1p.gradient (y j)),
    gaugeFixedZerothOrder.coeFn_holder (r := 2) a (sobolevFieldValues y), hg,
    sobolevFieldValues_ae_eq y] with z h₁ h₂ h₃ h₄ h₅
  rw [h₁, Pi.add_apply, h₂, h₃, h₅]
  simp only [Finset.sum_apply, h₄, ← map_sum, Finset.univ_sum_single]

/-- Changing the coefficient changes the realization only in its zeroth-order part: almost
everywhere, the difference of the realizations at `a` and `b` is the zeroth-order term with
coefficient `a - b`. -/
theorem sobolevGaugeFixedOperator_sub_apply_ae (a b : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    (sobolevGaugeFixedOperator a - sobolevGaugeFixedOperator b) y =ᵐ[μ⊤] fun z ↦
      gaugeFixedZerothOrder (a z - b z) (WithLp.toLp 2 fun j ↦ W1p.value (y j) z) := by
  filter_upwards [Lp.coeFn_sub (sobolevGaugeFixedOperator a y) (sobolevGaugeFixedOperator b y),
    sobolevGaugeFixedOperator_apply_ae a y, sobolevGaugeFixedOperator_apply_ae b y]
    with z h h₁ h₂
  rw [sub_apply, h, Pi.sub_apply, h₁, h₂, map_sub, sub_apply]
  abel

/-- The realization depends Lipschitz continuously, in operator norm, on the `L∞` class of the
coefficient. -/
theorem exists_lipschitzWith_sobolevGaugeFixedOperator :
    ∃ K, LipschitzWith K sobolevGaugeFixedOperator := by
  set V := sobolevFieldValues
  set H := gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2
  have hsub : ∀ a b, sobolevGaugeFixedOperator a - sobolevGaugeFixedOperator b =
      (H (a - b)).comp V := fun a b ↦ by
    simp only [sobolevGaugeFixedOperator, map_sub, ContinuousLinearMap.sub_comp]
    abel
  refine ⟨‖H‖₊ * ‖V‖₊, LipschitzWith.of_dist_le_mul fun a b ↦ ?_⟩
  rw [dist_eq_norm, dist_eq_norm, hsub]
  calc ‖(H (a - b)).comp V‖ ≤ ‖H (a - b)‖ * ‖V‖ := ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖H‖ * ‖a - b‖ * ‖V‖ := by gcongr; exact H.le_opNorm _
    _ = _ := by push_cast; ring

/-- The realization depends continuously, in operator norm, on the `L∞` class of the
coefficient. -/
theorem continuous_sobolevGaugeFixedOperator :
    Continuous sobolevGaugeFixedOperator :=
  exists_lipschitzWith_sobolevGaugeFixedOperator.elim fun _ h ↦ h.continuous

/-- The realization is affine in the `L∞` class of the coefficient: it is the realization at `0`
plus the zeroth-order part with coefficient `a`. -/
theorem sobolevGaugeFixedOperator_eq_add (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤) :
    sobolevGaugeFixedOperator a = sobolevGaugeFixedOperator 0 +
      (gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 a).comp sobolevFieldValues := by
  simp only [sobolevGaugeFixedOperator, map_zero, ContinuousLinearMap.zero_comp, add_zero]

/-- The realization is a smooth function of the `L∞` class of the coefficient: it is affine in
it, the realization at `0` plus the zeroth-order part with coefficient `a`. -/
theorem contDiff_sobolevGaugeFixedOperator {n : WithTop ℕ∞} :
    ContDiff ℝ n sobolevGaugeFixedOperator := by
  rw [funext sobolevGaugeFixedOperator_eq_add]
  exact contDiff_const.add
    ((gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2).contDiff.clm_comp contDiff_const)

/-- Along a family of coefficients differentiable at `p₀`, the realizations are differentiable
at `p₀`. -/
theorem differentiableAt_sobolevGaugeFixedOperator_comp {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}
    (ha : DifferentiableAt ℝ a p₀) :
    DifferentiableAt ℝ (fun p ↦ sobolevGaugeFixedOperator (a p)) p₀ :=
  ((contDiff_sobolevGaugeFixedOperator (n := 1)).differentiable one_ne_zero).differentiableAt.comp
    p₀ ha

/-- **The derivative of the realization along a family of coefficients.** The realization is
affine in the `L∞` class of the coefficient, so along a family `a` of coefficients differentiable
at `p₀` its derivative in the direction `v`, applied to `y`, is the zeroth-order part with
coefficient `a' = Da(p₀) v`: the `L²` class of `z ↦ Z(a'(z), y(z))`, with `Z` the bilinear map
`gaugeFixedZerothOrder`. -/
theorem fderiv_sobolevGaugeFixedOperator_comp_apply {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {p₀ : X}
    (ha : DifferentiableAt ℝ a p₀) (v : X) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    fderiv ℝ (fun p ↦ sobolevGaugeFixedOperator (a p)) p₀ v y =
      gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2 (fderiv ℝ a p₀ v) (sobolevFieldValues y) := by
  set H := gaugeFixedZerothOrder.holderL μ⊤ ∞ 2 2
  -- Evaluated at `y`, the family is the constant `L₀ y` plus the linear map `b ↦ Z(b, y)` of `a`.
  have hS (p : X) : sobolevGaugeFixedOperator (a p) y =
      sobolevGaugeFixedOperator 0 y + H.flip (sobolevFieldValues y) (a p) := by
    rw [sobolevGaugeFixedOperator_eq_add (a p), add_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  have h : HasFDerivAt (fun p ↦ sobolevGaugeFixedOperator (a p) y)
      ((H.flip (sobolevFieldValues y)).comp (fderiv ℝ a p₀)) p₀ := by
    simp only [hS]
    exact ((H.flip (sobolevFieldValues y)).hasFDerivAt.comp p₀ ha.hasFDerivAt).const_add _
  simpa using congrArg (fun L ↦ L v)
    (((differentiableAt_sobolevGaugeFixedOperator_comp ha).hasFDerivAt.clm_apply
      (hasFDerivAt_const y p₀)).unique h)

/-- On a variation `y` whose coordinates have the coordinates of a `C¹` field `Y` as
representatives, the realization at the `L∞` class of a field `x` is the classical gauge-fixed
operator `L_x Y`. -/
theorem sobolevGaugeFixedOperator_ae_eq_gaugeFixedOperator
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hax : a =ᵐ[μ⊤] x) {y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2}
    {Y : ℂ → EuclideanSpace ℝ (Fin 4)} (hY : ContDiff ℝ 1 Y)
    (hyY : ∀ j, W1p.value (y j) =ᵐ[μ⊤] fun z ↦ Y z j) :
    sobolevGaugeFixedOperator a y =ᵐ[μ⊤] gaugeFixedOperator x Y := by
  have hg : ∀ᵐ z ∂μ⊤, ∀ j : Fin 4, W1p.gradient (y j) z = ∇ (fun w ↦ Y w j) z :=
    ae_all_iff.2 fun j ↦
      W1p.gradient_ae_eq_of_contDiffOn (y j) ((contDiff_piLp 2).1 hY j).contDiffOn (hyY j)
  filter_upwards [sobolevGaugeFixedOperator_apply_ae a y, hax, hg, ae_all_iff.2 hyY]
    with z h₁ h₂ h₃ h₄
  rw [h₁, gaugeFixedOperator_eq_gaugeFixedFirstOrder_add, h₂]
  simp_rw [h₃, h₄]

/-- The values of the four coordinates on the disc of radius `R`, as `L²` classes there: the
compact error term of the coercive estimate. -/
private def discValues (R : ℝ) :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ]
      (Fin 4 → Lp ℝ 2 ((volume : Measure ℂ).restrict (ball (0 : ℂ) R))) :=
  ContinuousLinearMap.pi fun j ↦
    (W1p.valueL (mu := volume) (Omega := ⟨ball (0 : ℂ) R, isOpen_ball⟩) (p := 2)).comp
      ((W1p.restrictL le_top).comp (ContinuousLinearMap.proj j))

private theorem isCompactOperator_discValues (R : ℝ) : IsCompactOperator (discValues R) := by
  have hVc : IsCompact (closure (ball (0 : ℂ) R)) :=
    (isCompact_closedBall 0 R).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  refine IsCompactOperator.pi fun j ↦ ?_
  convert (W1p.isCompactOperator_valueL_restrictL (mu := volume) (Omega := ⊤) (p := 2)
      (V := ⟨ball (0 : ℂ) R, isOpen_ball⟩) hVc (Set.subset_univ _)).comp_clm
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin 4 ↦ W1p (volume : Measure ℂ) ⊤ 2) j) using 1
  -- Both sides are the `j`-th component of `discValues R`, by its definition.
  rfl

private theorem norm_discValues_apply_sq (R : ℝ) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)
    (j : Fin 4) :
    ‖discValues R y j‖ ^ 2 = ∫ z in ball (0 : ℂ) R, W1p.value (y j) z ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  refine integral_congr_ae ?_
  filter_upwards [W1p.value_restrictL_ae (mu := volume) (p := 2)
    (U := ⟨ball (0 : ℂ) R, isOpen_ball⟩) le_top (y j)] with z hz
  simp only [discValues, ContinuousLinearMap.pi_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, W1p.valueL_apply, Real.norm_eq_abs, sq_abs]
  exact congrArg (· ^ 2) hz

/-- The `H¹` norm of a field of test functions is controlled by the integrals of its squared
values and gradients. -/
private theorem norm_sq_le_integral_testField (φ : Fin 4 → 𝓓((⊤ : Opens ℂ), ℝ)) :
    ‖fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)‖ ^ 2 ≤
      ∫ z, (‖(WithLp.toLp 2 fun j ↦ φ j z : EuclideanSpace ℝ (Fin 4))‖ ^ 2 +
        ∑ j : Fin 4, ‖∇ (φ j : ℂ → ℝ) z‖ ^ 2) := by
  set y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2 := fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)
  have hφi (j : Fin 4) : Integrable (fun z ↦ φ j z ^ 2) := by
    simpa using (φ j).continuous.integrable_norm_sq_of_hasCompactSupport (μ := volume)
      (φ j).hasCompactSupport
  have hgi (j : Fin 4) : Integrable (fun z ↦ ‖∇ (φ j : ℂ → ℝ) z‖ ^ 2) :=
    (continuous_gradient_testFunction (φ j)).integrable_norm_sq_of_hasCompactSupport
      (φ j).hasCompactSupport.gradient
  have hnorm (j : Fin 4) :
      ‖y j‖ ^ 2 = (∫ z, φ j z ^ 2) + ∫ z, ‖∇ (φ j : ℂ → ℝ) z‖ ^ 2 := by
    simp only [y, W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq,
      W1p.norm_value_ofTestFunctionₗ_top_sq, W1p.norm_gradient_ofTestFunctionₗ_top_sq,
      norm_gradient_eq_norm_fderiv]
  refine (Pi.norm_pow_le_sum_norm_pow y two_ne_zero).trans (le_of_eq ?_)
  simp_rw [hnorm, Finset.sum_add_distrib]
  rw [← integral_finsetSum _ fun j _ ↦ hφi j, ← integral_finsetSum _ fun j _ ↦ hgi j,
    ← integral_add (integrable_finsetSum _ fun j _ ↦ hφi j)
      (integrable_finsetSum _ fun j _ ↦ hgi j)]
  congr 1
  ext z
  simp [EuclideanSpace.real_norm_sq_eq]

/-- On a field of test functions, the squared `L²` norm of the realization is the integral of the
squared classical operator. -/
private theorem norm_sobolevGaugeFixedOperator_ofTestFunctionₗ_sq
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hax : a =ᵐ[μ⊤] x) (φ : Fin 4 → 𝓓((⊤ : Opens ℂ), ℝ)) :
    ‖sobolevGaugeFixedOperator a (fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j))‖ ^ 2 =
      ∫ z, ‖gaugeFixedOperator x (fun z ↦ WithLp.toLp 2 fun j ↦ φ j z) z‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  have h := sobolevGaugeFixedOperator_ae_eq_gaugeFixedOperator hax
    (y := fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j))
    (Y := fun z ↦ WithLp.toLp 2 fun j ↦ φ j z)
    (((contDiff_piLp 2).2 fun j ↦ (φ j).contDiff).of_le (by simp))
    fun j ↦ W1p.value_ofTestFunctionₗ_ae (φ j)
  simp only [Opens.coe_top, Measure.restrict_univ] at h ⊢
  exact integral_congr_ae (h.mono fun z hz ↦ by simp only [hz])

/-- The integral of the squared norm of a field of test functions over a closed disc is at most
the sum of the integrals of the squared values of its coordinates over a larger open disc. -/
private theorem integral_closedBall_norm_sq_testField_le (φ : Fin 4 → 𝓓((⊤ : Opens ℂ), ℝ))
    (R : ℝ) :
    ∫ z in closedBall 0 R, ‖(WithLp.toLp 2 fun j ↦ φ j z : EuclideanSpace ℝ (Fin 4))‖ ^ 2 ≤
      ∑ j, ∫ z in ball (0 : ℂ) (R + 1),
        W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) z ^ 2 := by
  have hc : Continuous fun z ↦ ‖(WithLp.toLp 2 fun j ↦ φ j z : EuclideanSpace ℝ (Fin 4))‖ ^ 2 :=
    (((PiLp.continuous_toLp 2 _).comp (continuous_pi fun j ↦ (φ j).continuous)).norm.pow 2)
  have hφ (j : Fin 4) : IntegrableOn (fun z ↦ φ j z ^ 2) (ball (0 : ℂ) (R + 1)) :=
    (((φ j).continuous.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : ℂ) (R + 1))).mono_set ball_subset_closedBall
  calc _ ≤ ∫ z in ball (0 : ℂ) (R + 1),
          ‖(WithLp.toLp 2 fun j ↦ φ j z : EuclideanSpace ℝ (Fin 4))‖ ^ 2 :=
        setIntegral_mono_set ((hc.continuousOn.integrableOn_compact
            (isCompact_closedBall (0 : ℂ) (R + 1))).mono_set ball_subset_closedBall)
          (ae_of_all _ fun z ↦ sq_nonneg _)
          (closedBall_subset_ball (by linarith)).eventuallySubset
    _ = ∑ j, ∫ z in ball (0 : ℂ) (R + 1), φ j z ^ 2 := by
        rw [← integral_finsetSum _ fun j _ ↦ hφ j]
        congr 1
        ext z
        simp [EuclideanSpace.real_norm_sq_eq]
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ ↦ integral_congr_ae ?_
        filter_upwards [ae_restrict_of_ae (W1p.value_ofTestFunctionₗ_top_ae (mu := volume)
          (p := 2) (φ j))] with z hz
        rw [hz]

/-- The coercive estimate on fields of test functions, from the Gårding inequality. -/
private theorem norm_sq_le_of_testFunction {x : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hx : Continuous x) {M : ℝ} (hM : ∀ z, ‖x z‖ ≤ M)
    {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} (hax : a =ᵐ[μ⊤] x) {R K : ℝ}
    (hG : ∀ y : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 y → HasCompactSupport y →
      (∫ z, gaugeFixedGradientDensity x y z) + 1 / 8 * ∫ z, ‖y z‖ ^ 2 ≤
        (∫ z, ‖gaugeFixedOperator x y z‖ ^ 2) + K * ∫ z in closedBall 0 R, ‖y z‖ ^ 2)
    (φ : Fin 4 → 𝓓((⊤ : Opens ℂ), ℝ)) :
    ‖fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)‖ ^ 2 ≤
      8 * (1 + 2 * M ^ 2) *
        (‖sobolevGaugeFixedOperator a (fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j))‖ ^ 2 +
          max K 0 * ∑ j, ∫ z in ball (0 : ℂ) (R + 1),
            W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) z ^ 2) := by
  set y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2 := fun j ↦ W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)
  set Y : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ WithLp.toLp 2 fun j ↦ φ j z
  have hY : ContDiff ℝ 2 Y := ((contDiff_piLp 2).2 fun j ↦ (φ j).contDiff).of_le (by simp)
  have hYc : HasCompactSupport Y :=
    (hasCompactSupport_pi_iff.2 fun j ↦ (φ j).hasCompactSupport).comp_left (g := WithLp.toLp 2)
      (WithLp.toLp_zero 2)
  have hYi : Integrable (fun z ↦ ‖Y z‖ ^ 2) :=
    hY.continuous.integrable_norm_sq_of_hasCompactSupport hYc
  have hGi : Integrable (gaugeFixedGradientDensity x Y) :=
    integrable_gaugeFixedGradientDensity hx (hY.of_le one_le_two) hYc
  -- The flat gradient is controlled by the covariant gradient density.
  have hle : ‖y‖ ^ 2 ≤
      (1 + 2 * M ^ 2) * (∫ z, ‖Y z‖ ^ 2) + 2 * ∫ z, gaugeFixedGradientDensity x Y z := by
    refine (norm_sq_le_integral_testField φ).trans ?_
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hYi.const_mul _)
      (hGi.const_mul _)]
    refine integral_mono_of_nonneg (ae_of_all _ fun z ↦ by positivity)
      ((hYi.const_mul _).add (hGi.const_mul _)) (ae_of_all _ fun z ↦ ?_)
    have h₁ := sum_norm_gradient_sq_le x Y z
    have h₂ : x z 0 ^ 2 + x z 1 ^ 2 ≤ M ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) (hM z) 2
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four] at this
      nlinarith [sq_nonneg (x z 2), sq_nonneg (x z 3)]
    -- The coordinates of `Y` are the test functions themselves.
    have h₃ (j : Fin 4) : (fun w ↦ Y w j) = φ j := funext fun w ↦ by simp only [Y]
    simp only [h₃] at h₁
    nlinarith [mul_le_mul_of_nonneg_right h₂ (sq_nonneg ‖Y z‖)]
  have hGarding := hG Y (hY.of_le le_rfl) hYc
  rw [← norm_sobolevGaugeFixedOperator_ofTestFunctionₗ_sq hax φ] at hGarding
  have hG0 : 0 ≤ ∫ z, gaugeFixedGradientDensity x Y z :=
    integral_nonneg fun z ↦ gaugeFixedGradientDensity_nonneg x Y z
  have hB0 : 0 ≤ ∫ z in closedBall 0 R, ‖Y z‖ ^ 2 := integral_nonneg fun z ↦ sq_nonneg _
  have hK : K * ∫ z in closedBall 0 R, ‖Y z‖ ^ 2 ≤
      max K 0 * ∑ j, ∫ z in ball (0 : ℂ) (R + 1), W1p.value (y j) z ^ 2 :=
    (mul_le_mul_of_nonneg_right (le_max_left K 0) hB0).trans
      (mul_le_mul_of_nonneg_left (integral_closedBall_norm_sq_testField_le φ R) (le_max_right K 0))
  nlinarith [sq_nonneg M]

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}

/-- **The coercive estimate for `L_x` on `H¹`.** At a `C¹` vortex `x` with `|α| → 1` and
`∇₁ α → 0` at infinity and with `L∞` class `a`, there are a radius `R` and a constant `C` with
`‖y‖²_{H¹} ≤ C (‖L_x y‖²_{L²} + ‖y‖²_{L²(B_R)})` for every `y ∈ H¹(ℂ)⁴`. -/
theorem exists_norm_sq_le_mul_norm_sobolevGaugeFixedOperator_sq_add (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    (hax : a =ᵐ[μ⊤] x) :
    ∃ R > 0, ∃ C ≥ 0, ∀ y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2,
      ‖y‖ ^ 2 ≤ C * (‖sobolevGaugeFixedOperator a y‖ ^ 2 +
        ∑ j, ∫ z in ball (0 : ℂ) R, W1p.value (y j) z ^ 2) := by
  obtain ⟨R, hR, K, hG⟩ := exists_integral_gaugeFixedGradientDensity_add_mul_integral_norm_sq_le
    (μ := volume) hx hsol hlim hcov (a := 1 / 8) (by norm_num)
  have hM (z : ℂ) : ‖x z‖ ≤ ‖a‖ :=
    Lp.norm_le_norm_top_of_ae_eq_of_continuousAt hax hx.continuous.continuousAt
  set C := 8 * (1 + 2 * ‖a‖ ^ 2) * max 1 (max K 0) with hC
  have hC₀ : 0 ≤ 8 * (1 + 2 * ‖a‖ ^ 2) := by positivity
  refine ⟨R + 1, by linarith, C, mul_nonneg hC₀ (zero_le_one.trans (le_max_left _ _)), ?_⟩
  intro y
  have hdisc (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
      ∑ j, ∫ z in ball (0 : ℂ) (R + 1), W1p.value (y j) z ^ 2 =
        ∑ j, ‖discValues (R + 1) y j‖ ^ 2 :=
    Finset.sum_congr rfl fun j _ ↦ (norm_discValues_apply_sq _ y j).symm
  rw [hdisc]
  refine (DenseRange.piMap fun _ : Fin 4 ↦
    W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 2) (by norm_num)).induction_on
      (p := fun y ↦ ‖y‖ ^ 2 ≤ C * (‖sobolevGaugeFixedOperator a y‖ ^ 2 +
        ∑ j, ‖discValues (R + 1) y j‖ ^ 2)) y ?_ fun φ ↦ ?_
  · refine isClosed_le (continuous_norm.pow 2) (continuous_const.mul
      (((sobolevGaugeFixedOperator a).continuous.norm.pow 2).add
        (continuous_finsetSum _ fun j _ ↦ ?_)))
    exact (((continuous_apply j).comp (discValues (R + 1)).continuous).norm.pow 2)
  · have h := norm_sq_le_of_testFunction hx.continuous hM hax hG φ
    rw [hdisc] at h
    refine h.trans ?_
    have hN : 0 ≤ ∑ j, ‖discValues (R + 1) (Pi.map (fun _ ↦ ⇑(W1p.ofTestFunctionₗ volume ⊤ 2))
        φ) j‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    set X := ‖sobolevGaugeFixedOperator a (Pi.map (fun _ ↦ ⇑(W1p.ofTestFunctionₗ volume ⊤ 2))
      φ)‖ ^ 2
    have hX : 0 ≤ X := sq_nonneg _
    have key : X + max K 0 * ∑ j, ‖discValues (R + 1) (Pi.map
        (fun _ ↦ ⇑(W1p.ofTestFunctionₗ volume ⊤ 2)) φ) j‖ ^ 2 ≤
        max 1 (max K 0) * (X + ∑ j, ‖discValues (R + 1) (Pi.map
          (fun _ ↦ ⇑(W1p.ofTestFunctionₗ volume ⊤ 2)) φ) j‖ ^ 2) := by
      nlinarith [le_max_left 1 (max K 0), le_max_right 1 (max K 0)]
    calc _ ≤ 8 * (1 + 2 * ‖a‖ ^ 2) * (max 1 (max K 0) * (X + ∑ j, ‖discValues (R + 1) (Pi.map
          (fun _ ↦ ⇑(W1p.ofTestFunctionₗ volume ⊤ 2)) φ) j‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left key hC₀
      _ = _ := by rw [hC]; ring

/-- The coercive estimate in the form of Peetre's lemma, with a compact error term. -/
private theorem exists_compact_estimate (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    (hax : a =ᵐ[μ⊤] x) :
    ∃ R C : ℝ, ∀ y, ‖y‖ ≤ C * ‖sobolevGaugeFixedOperator a y‖ +
      ‖((2 * C) • discValues R) y‖ := by
  obtain ⟨R, -, C, hC, hest⟩ :=
    exists_norm_sq_le_mul_norm_sobolevGaugeFixedOperator_sq_add hx hsol hlim hcov hax
  refine ⟨R, √C, fun y ↦ ?_⟩
  have h := hest y
  simp_rw [← norm_discValues_apply_sq] at h
  have hsum : ∑ j, ‖discValues R y j‖ ^ 2 ≤ 4 * ‖discValues R y‖ ^ 2 := by
    calc ∑ j, ‖discValues R y j‖ ^ 2 ≤ ∑ _j : Fin 4, ‖discValues R y‖ ^ 2 :=
          Finset.sum_le_sum fun j _ ↦ pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm _ j) 2
      _ = 4 * ‖discValues R y‖ ^ 2 := by simp
  have hs := Real.sq_sqrt hC
  have hs₀ := Real.sqrt_nonneg C
  rw [smul_apply, norm_smul, Real.norm_of_nonneg (by positivity)]
  refine (pow_le_pow_iff_left₀ (norm_nonneg y) (by positivity) two_ne_zero).1 ?_
  nlinarith [mul_le_mul_of_nonneg_left hsum hC, norm_nonneg (sobolevGaugeFixedOperator a y),
    norm_nonneg (discValues R y), mul_nonneg (mul_nonneg hs₀ (norm_nonneg
      (sobolevGaugeFixedOperator a y))) (mul_nonneg hs₀ (norm_nonneg (discValues R y)))]

/-- **The kernel of `L_x` on `H¹` is finite dimensional** at a `C¹` vortex `x` with `|α| → 1`
and `∇₁ α → 0` at infinity and with `L∞` class `a`. -/
theorem finiteDimensional_ker_sobolevGaugeFixedOperator (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    (hax : a =ᵐ[μ⊤] x) :
    FiniteDimensional ℝ (sobolevGaugeFixedOperator a).ker := by
  obtain ⟨R, C, h⟩ := exists_compact_estimate hx hsol hlim hcov hax
  exact (sobolevGaugeFixedOperator a).finiteDimensional_ker_of_compact_estimate
    ((isCompactOperator_discValues R).smul (2 * C)) h

/-- **The range of `L_x : H¹ → L²` is closed** at a `C¹` vortex `x` with `|α| → 1` and
`∇₁ α → 0` at infinity and with `L∞` class `a`. -/
theorem isClosed_range_sobolevGaugeFixedOperator (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    (hax : a =ᵐ[μ⊤] x) :
    IsClosed ((sobolevGaugeFixedOperator a).range :
      Set (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)) := by
  obtain ⟨R, C, h⟩ := exists_compact_estimate hx hsol hlim hcov hax
  exact (sobolevGaugeFixedOperator a).isClosed_range_of_compact_estimate
    ((isCompactOperator_discValues R).smul (2 * C)) h

/-- **The `L²`-orthogonal kernel projections and right inverses of `L_x : H¹ → L²` move
continuously with the coefficient.** Let `a₀` be an `L∞` class at which the realization is onto
with a finite-dimensional kernel; at a plane vortex these hypotheses are supplied by
`TauCeti.Vortex.sobolevGaugeFixedOperator_surjective` and
`TauCeti.Vortex.finiteDimensional_ker_sobolevGaugeFixedOperator`. Near `a₀` in `L∞`, every
realization `L_a` is onto, and there are families of operators `π a` on `H¹(ℂ)⁴` and
`Q a : L² → H¹(ℂ)⁴`, continuous in `a` for the operator norms,
such that `π a` is the projection onto the kernel of `L_a` along its `L²`-orthogonal complement,
`Q a` is a right inverse of `L_a` whose values are `L²`-orthogonal to that kernel, and every `y`
splits as `y = π a y + Q a (L_a y)`. The `L²` pairing on `H¹(ℂ)⁴` is taken through the inclusion
`sobolevFieldValues`. -/
theorem exists_continuousOn_orthogonal_rightInverse_sobolevGaugeFixedOperator
    {a₀ : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}
    (hsurj : Function.Surjective (sobolevGaugeFixedOperator a₀))
    (hfin : FiniteDimensional ℝ (sobolevGaugeFixedOperator a₀).ker) :
    ∃ U : Set (Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤), IsOpen U ∧ a₀ ∈ U ∧
      ∃ π : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤ →
          (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2),
        ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤ →
          Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2),
        ContinuousOn π U ∧ ContinuousOn Q U ∧ ∀ a ∈ U,
          Function.Surjective (sobolevGaugeFixedOperator a) ∧
          (∀ y, π a y ∈ (sobolevGaugeFixedOperator a).ker) ∧
          (∀ k ∈ (sobolevGaugeFixedOperator a).ker, π a k = k) ∧
          (∀ y, ∀ k ∈ (sobolevGaugeFixedOperator a).ker,
            ⟪sobolevFieldValues (y - π a y), sobolevFieldValues k⟫_ℝ = 0) ∧
          (∀ f, sobolevGaugeFixedOperator a (Q a f) = f) ∧
          (∀ f, ∀ k ∈ (sobolevGaugeFixedOperator a).ker,
            ⟪sobolevFieldValues (Q a f), sobolevFieldValues k⟫_ℝ = 0) ∧
          ∀ y, π a y + Q a (sobolevGaugeFixedOperator a y) = y := by
  have hT₀ := ContinuousLinearMap.IsFredholm.of_surjective hsurj
  obtain ⟨U, -, hU⟩ := hT₀.exists_continuousOn_orthogonal_rightInverse sobolevFieldValues
    sobolevFieldValues_injective hsurj continuous_sobolevGaugeFixedOperator.continuousOn
      isOpen_univ (Set.mem_univ a₀)
  exact ⟨U, hU⟩

section Family

variable {X : Type*} [TopologicalSpace X] {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}
  (ha : Continuous a) (hsurj : ∀ x, Function.Surjective (sobolevGaugeFixedOperator (a x)))
  (hfin : ∀ x, FiniteDimensional ℝ (sobolevGaugeFixedOperator (a x)).ker)
include ha hsurj hfin

/-- **Continuity of the kernel projections along a family of coefficients.** Along a family of
`L∞` coefficients `a x`, continuous in `x`, at which the realization `L_a : H¹ → L²` is onto with
a finite-dimensional kernel, the projection of `H¹(ℂ)⁴` onto the kernel of `L_a` along its
`L²`-orthogonal complement depends continuously on `x`, in operator norm. -/
theorem continuous_orthogonalKerProjection_sobolevGaugeFixedOperator :
    Continuous fun x ↦ ContinuousLinearMap.orthogonalKerProjection sobolevFieldValues
      (sobolevGaugeFixedOperator (a x)) :=
  continuous_iff_continuousAt.2 fun x ↦
    have := hfin x
    ((ContinuousLinearMap.IsFredholm.of_surjective (hsurj x)).continuousAt_orthogonalKerProjection
      sobolevFieldValues_injective (hsurj x)).comp
      (f := fun x ↦ sobolevGaugeFixedOperator (a x))
      (continuous_sobolevGaugeFixedOperator.comp ha).continuousAt

/-- **Continuity of the right inverses along a family of coefficients.** Along a family of `L∞`
coefficients `a x`, continuous in `x`, at which the realization `L_a : H¹ → L²` is onto with a
finite-dimensional kernel, the right inverse of `L_a` with values `L²`-orthogonal to its kernel
depends continuously on `x`, in operator norm. -/
theorem continuous_orthogonalRightInverse_sobolevGaugeFixedOperator :
    Continuous fun x ↦ ContinuousLinearMap.orthogonalRightInverse sobolevFieldValues
      (sobolevGaugeFixedOperator (a x)) :=
  continuous_iff_continuousAt.2 fun x ↦
    have := hfin x
    ((ContinuousLinearMap.IsFredholm.of_surjective (hsurj x)).continuousAt_orthogonalRightInverse
      sobolevFieldValues_injective (hsurj x)).comp
      (f := fun x ↦ sobolevGaugeFixedOperator (a x))
      (continuous_sobolevGaugeFixedOperator.comp ha).continuousAt

end Family

section SmoothFamily

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞}
  {a : X → Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤} (ha : ContDiff ℝ n a)
  (hsurj : ∀ x, Function.Surjective (sobolevGaugeFixedOperator (a x)))
  (hfin : ∀ x, FiniteDimensional ℝ (sobolevGaugeFixedOperator (a x)).ker)
include ha hsurj hfin

/-- **Smoothness of the kernel projections along a family of coefficients.** Along a family of
`L∞` coefficients `a x`, `C^n` in `x`, at which the realization `L_a : H¹ → L²` is onto with a
finite-dimensional kernel, the projection of `H¹(ℂ)⁴` onto the kernel of `L_a` along its
`L²`-orthogonal complement is a `C^n` function of `x`, in operator norm. -/
theorem contDiff_orthogonalKerProjection_sobolevGaugeFixedOperator :
    ContDiff ℝ n fun x ↦ ContinuousLinearMap.orthogonalKerProjection sobolevFieldValues
      (sobolevGaugeFixedOperator (a x)) :=
  contDiff_iff_contDiffAt.2 fun x ↦
    have := hfin x
    ((ContinuousLinearMap.IsFredholm.of_surjective (hsurj x)).contDiffAt_orthogonalKerProjection
      sobolevFieldValues_injective (hsurj x)).comp (f := fun x ↦ sobolevGaugeFixedOperator (a x))
      x (contDiff_sobolevGaugeFixedOperator.comp ha).contDiffAt

/-- **Smoothness of the right inverses along a family of coefficients.** Along a family of `L∞`
coefficients `a x`, `C^n` in `x`, at which the realization `L_a : H¹ → L²` is onto with a
finite-dimensional kernel, the right inverse of `L_a` with values `L²`-orthogonal to its kernel is
a `C^n` function of `x`, in operator norm. -/
theorem contDiff_orthogonalRightInverse_sobolevGaugeFixedOperator :
    ContDiff ℝ n fun x ↦ ContinuousLinearMap.orthogonalRightInverse sobolevFieldValues
      (sobolevGaugeFixedOperator (a x)) :=
  contDiff_iff_contDiffAt.2 fun x ↦
    have := hfin x
    ((ContinuousLinearMap.IsFredholm.of_surjective (hsurj x)).contDiffAt_orthogonalRightInverse
      sobolevFieldValues_injective (hsurj x)).comp (f := fun x ↦ sobolevGaugeFixedOperator (a x))
      x (contDiff_sobolevGaugeFixedOperator.comp ha).contDiffAt

end SmoothFamily

end TauCeti.Vortex
