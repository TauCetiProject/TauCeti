/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.TestFunction.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Geometry.Lie.Basic
import TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral
import TauCeti.MeasureTheory.Group.Convolution.Support
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Convolution of test functions on a Lie group

Let `G` be a real Lie group without boundary and `μ` a measure on `G` that is finite on compact
sets, for instance a left Haar measure. The convolution of two test functions `a b` is

`(a * b) g = ∫ x, a x * b (x⁻¹ * g) ∂μ`.

It is again a test function: it is smooth by differentiation under the integral sign
(`ContinuousLinearMap.contMDiff_integral_inv_mul`) and supported in the product of the supports
(`TauCeti.hasCompactSupport_integral_of_inv_mul_mem`). We bundle it as a `ℂ`-bilinear map.

For a left-invariant measure the convolution is associative, it commutes with left translation of
the first factor, and the involution `a^* g = conj (a g⁻¹)` reverses convolution products,
`(a * b)^* = b^* * a^*`. The last identity uses only left invariance, so it holds on every Lie
group. On a unimodular group this is also the involution for which the integrated action of `a^*`
in a unitary representation is the adjoint of that of `a`.

## Main definitions

* `TauCeti.LieTestFunction.convolution μ`: the convolution of test functions, a `ℂ`-bilinear map.

## Main results

* `TauCeti.LieTestFunction.support_convolution_subset`,
  `TauCeti.LieTestFunction.tsupport_convolution_subset`: `supp (a * b) ⊆ supp a * supp b`.
* `TauCeti.LieTestFunction.conj_convolution`: `conj (a * b) = conj a * conj b`.
* `TauCeti.LieTestFunction.rightTranslate_convolution`: `R(y) (a * b) = a * R(y) b`.
* `TauCeti.LieTestFunction.leftTranslate_convolution`: `L(y) (a * b) = L(y) a * b`.
* `TauCeti.LieTestFunction.convolution_assoc`: convolution is associative.
* `TauCeti.LieTestFunction.integral_convolution`: `∫ a * b = (∫ a) * ∫ b`.
* `TauCeti.LieTestFunction.inversion_convolution`: `(a * b)^∨ = b^∨ * a^∨` for inversion.
* `TauCeti.LieTestFunction.involution_convolution`: `(a * b)^* = b^* * a^*`.

## References

* J. R. Getz, *An introduction to automorphic representations*, §3.3.
* J. Bernstein, B. Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §2.5.
-/

public section

noncomputable section

open Function MeasureTheory Set
open scoped ContDiff Manifold Pointwise

namespace TauCeti

namespace LieTestFunction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [MeasurableSpace G] [OpensMeasurableSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

/-! ### The convolution integrand -/

section Integrand

variable (a b : LieTestFunction I G)

omit [I.Boundaryless] [LieGroup I ∞ G] [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The convolution integrand `x ↦ a x * b (x⁻¹ * g)` vanishes unless `x ∈ support a` and
`x⁻¹ * g ∈ support b`. -/
private theorem mem_support_of_mul_ne_zero {x g : G} (h : a x * b (x⁻¹ * g) ≠ 0) :
    x ∈ support a ∧ x⁻¹ * g ∈ support b :=
  mem_support_and_inv_mul_mem_support h (fun h ↦ by simp [h]) (fun h ↦ by simp [h])

omit [I.Boundaryless] [LieGroup I ∞ G] [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The convolution integrand `x ↦ a x * b (x⁻¹ * g)` vanishes unless `x ∈ tsupport a` and
`x⁻¹ * g ∈ tsupport b`. -/
private theorem mem_tsupport_of_mul_ne_zero {x g : G} (h : a x * b (x⁻¹ * g) ≠ 0) :
    x ∈ tsupport a ∧ x⁻¹ * g ∈ tsupport b :=
  mem_tsupport_and_inv_mul_mem_tsupport h (fun h ↦ by simp [h]) (fun h ↦ by simp [h])

omit [I.Boundaryless] [MeasurableSpace G] [OpensMeasurableSpace G] in
/-- The convolution integrand is jointly continuous. -/
private theorem continuous_integrand :
    Continuous (uncurry fun (g x : G) ↦ a x * b (x⁻¹ * g)) := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  rw [uncurry_def]
  fun_prop

omit [I.Boundaryless] in
/-- The convolution integrand is integrable against any measure finite on compact sets. -/
theorem integrable_mul_inv_mul (g : G) : Integrable (fun x ↦ a x * b (x⁻¹ * g)) μ :=
  ((continuous_integrand a b).comp (.prodMk_right g)).integrable_of_hasCompactSupport
    a.hasCompactSupport.mul_right

end Integrand

/-! ### The convolution -/

/-- The convolution of two test functions, before bundling. -/
private def convolutionAux (a b : LieTestFunction I G) : LieTestFunction I G :=
  have := I.t2Space_of_lieGroup ∞ (G := G)
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  { toFun g := ∫ x, a x * b (x⁻¹ * g) ∂μ
    contMDiff' := by
      simpa using (ContinuousLinearMap.mul ℝ ℂ).contMDiff_integral_inv_mul (ν := μ) a.contMDiff
        a.hasCompactSupport a.hasCompactSupport.isCompact.measure_lt_top.ne b.contMDiff
    hasCompactSupport' := hasCompactSupport_integral_of_inv_mul_mem μ a.hasCompactSupport
      b.hasCompactSupport fun _ _ ↦ mem_tsupport_of_mul_ne_zero a b }

private theorem convolutionAux_apply (a b : LieTestFunction I G) (g : G) :
    convolutionAux μ a b g = ∫ x, a x * b (x⁻¹ * g) ∂μ :=
  rfl

/-- The convolution `(a * b) g = ∫ x, a x * b (x⁻¹ * g) ∂μ` of test functions on a Lie group, as a
`ℂ`-bilinear map. -/
def convolution : LieTestFunction I G →ₗ[ℂ] LieTestFunction I G →ₗ[ℂ] LieTestFunction I G :=
  LinearMap.mk₂ ℂ (convolutionAux μ)
    (fun a₁ a₂ b ↦ ext fun g ↦ by
      simp only [convolutionAux_apply, add_apply, add_mul]
      exact integral_add (integrable_mul_inv_mul μ a₁ b g) (integrable_mul_inv_mul μ a₂ b g))
    (fun c a b ↦ ext fun g ↦ by
      simp only [convolutionAux_apply, smul_apply, smul_eq_mul, mul_assoc]
      exact integral_const_mul c _)
    (fun a b₁ b₂ ↦ ext fun g ↦ by
      simp only [convolutionAux_apply, add_apply, mul_add]
      exact integral_add (integrable_mul_inv_mul μ a b₁ g) (integrable_mul_inv_mul μ a b₂ g))
    (fun c a b ↦ ext fun g ↦ by
      simp only [convolutionAux_apply, smul_apply, smul_eq_mul, mul_left_comm _ c]
      exact integral_const_mul c _)

theorem convolution_apply (a b : LieTestFunction I G) (g : G) :
    convolution μ a b g = ∫ x, a x * b (x⁻¹ * g) ∂μ :=
  (rfl)

/-- A convolution of test functions is supported in the product of the supports. -/
theorem support_convolution_subset (a b : LieTestFunction I G) :
    support (convolution μ a b) ⊆ support a * support b :=
  support_integral_subset_mul μ fun _ _ ↦ mem_support_of_mul_ne_zero a b

/-- The support closure of a convolution of test functions lies in the product of the support
closures. -/
theorem tsupport_convolution_subset (a b : LieTestFunction I G) :
    tsupport (convolution μ a b) ⊆ tsupport a * tsupport b := by
  have := I.t2Space_of_lieGroup ∞ (G := G)
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  exact closure_minimal ((support_convolution_subset μ a b).trans
    (mul_subset_mul (subset_tsupport a) (subset_tsupport b)))
    (a.hasCompactSupport.isCompact.mul b.hasCompactSupport.isCompact).isClosed

/-- Right translation acts on the second factor of a convolution: `R(y) (a * b) = a * R(y) b`. -/
theorem rightTranslate_convolution (y : G) (a b : LieTestFunction I G) :
    rightTranslate y (convolution μ a b) = convolution μ a (rightTranslate y b) :=
  ext fun g ↦ by simp [convolution_apply, mul_assoc]

/-- Complex conjugation distributes over convolution: `conj (a * b) = conj a * conj b`. -/
theorem conj_convolution (a b : LieTestFunction I G) :
    conj (convolution μ a b) = convolution μ (conj a) (conj b) := by
  ext g
  simp only [conj_apply, convolution_apply, ← integral_conj, map_mul]

/-! ### Left-invariant measures -/

section LeftInvariant

variable [MeasurableMul G] [μ.IsMulLeftInvariant]

/-- For a left-invariant measure, left translation acts on the first factor of a convolution:
`L(y) (a * b) = L(y) a * b`. -/
theorem leftTranslate_convolution (y : G) (a b : LieTestFunction I G) :
    leftTranslate y (convolution μ a b) = convolution μ (leftTranslate y a) b := by
  ext g
  simp only [leftTranslate_apply, convolution_apply]
  conv_rhs => rw [← integral_mul_left_eq_self _ y]
  simp [mul_assoc]

/-- Convolution of test functions with respect to a left-invariant measure is associative. -/
theorem convolution_assoc (a b c : LieTestFunction I G) :
    convolution μ (convolution μ a b) c = convolution μ a (convolution μ b c) := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  ext g
  simp only [convolution_apply]
  calc ∫ t, (∫ x, a x * b (x⁻¹ * t) ∂μ) * c (t⁻¹ * g) ∂μ
      = ∫ t, ∫ x, a x * b (x⁻¹ * t) * c (t⁻¹ * g) ∂μ ∂μ := by
        congr 1 with t
        exact (integral_mul_const_of_integrable (integrable_mul_inv_mul μ a b t)).symm
    _ = ∫ x, ∫ t, a x * b (x⁻¹ * t) * c (t⁻¹ * g) ∂μ ∂μ := by
        refine integral_integral_swap_of_hasCompactSupport ?_
          (hasCompactSupport_uncurry_of_inv_mul_mem a.hasCompactSupport b.hasCompactSupport
            fun t x h ↦ mem_tsupport_of_mul_ne_zero a b (left_ne_zero_of_mul h))
        rw [uncurry_def]
        fun_prop
    _ = ∫ x, a x * ∫ t, b t * c (t⁻¹ * (x⁻¹ * g)) ∂μ ∂μ := by
        congr 1 with x
        -- Substitute `t ↦ x * t` in the inner integral, then pull out `a x`.
        rw [← integral_const_mul,
          ← integral_mul_left_eq_self (fun t ↦ a x * b (x⁻¹ * t) * c (t⁻¹ * g)) x]
        simp [mul_assoc]

/-- The integral of a convolution with respect to a left-invariant measure is the product of the
integrals. -/
theorem integral_convolution (a b : LieTestFunction I G) :
    ∫ g, convolution μ a b g ∂μ = (∫ g, a g ∂μ) * ∫ g, b g ∂μ := by
  have := topologicalGroup_of_lieGroup I ∞ (G := G)
  simp only [convolution_apply]
  rw [integral_integral_swap_of_hasCompactSupport (continuous_integrand a b)
    (hasCompactSupport_uncurry_of_inv_mul_mem a.hasCompactSupport b.hasCompactSupport
      fun _ _ ↦ mem_tsupport_of_mul_ne_zero a b), ← integral_mul_const]
  congr 1 with x
  rw [integral_const_mul, integral_mul_left_eq_self (fun g ↦ b g) x⁻¹]

/-- Inversion `a g ↦ a g⁻¹` reverses convolution products with respect to a left-invariant measure:
`(a * b)^∨ = b^∨ * a^∨`. -/
theorem inversion_convolution (a b : LieTestFunction I G) :
    inversion (convolution μ a b) = convolution μ (inversion b) (inversion a) := by
  ext g
  simp only [inversion_apply, convolution_apply]
  conv_rhs => rw [← integral_mul_left_eq_self _ g]
  congr 1 with x
  simp [mul_comm]

/-- The involution `a^* g = conj (a g⁻¹)` reverses convolution products with respect to a
left-invariant measure: `(a * b)^* = b^* * a^*`. -/
theorem involution_convolution (a b : LieTestFunction I G) :
    involution (convolution μ a b) = convolution μ (involution b) (involution a) := by
  ext g
  simp only [involution_apply, convolution_apply, mul_inv_rev, inv_inv]
  rw [← integral_conj]
  conv_rhs => rw [← integral_mul_left_eq_self _ g]
  congr 1 with x
  simp [mul_comm]

end LeftInvariant

end LieTestFunction

end TauCeti
