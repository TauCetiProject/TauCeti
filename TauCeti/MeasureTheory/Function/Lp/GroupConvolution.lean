/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import TauCeti.MeasureTheory.Function.Lp.LeftTranslation
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import TauCeti.MeasureTheory.Function.Lp.Order
import TauCeti.MeasureTheory.Function.StronglyMeasurable.InnerRegular

/-!
# Convolution by `L¹` on `Lᵖ` of a locally compact group

Let `μ` be a left-invariant measure on a topological group `G` which is locally finite and inner
regular for compact sets, for instance a regular left Haar measure on a locally compact group. An
integrable kernel `h` acts on `Lᵖ(G, μ; E)`, for `1 ≤ p < ∞`, by left convolution

```text
h ⋆ f = ∫ y, h(y) • L_y f dμ(y),        (L_y f)(x) = f (y⁻¹ * x),
```

an `Lᵖ`-valued Bochner integral of left translates of `f`. This is the operator form of the
classical convolution `(h ⋆ f)(x) = ∫ y, h(y) • f(y⁻¹ * x) dμ(y)`; identifying the two almost
everywhere needs a Fubini argument and is not done here. The group need not be abelian,
and neither σ-finiteness of `μ` nor second countability of `G` is assumed. The integrand is
almost everywhere strongly measurable because `y ↦ L_y f` is continuous, by Mathlib's continuity
of the `DomMulAct` action on `Lᵖ`, and an integrable `h` lives on a σ-finite set
(`MeasureTheory.AEFinStronglyMeasurable.aestronglyMeasurable_smul`).

Since the definition never evaluates `h ⋆ f` at a point, its algebraic properties need no Fubini
theorem. Left translation passes through the integral, and a left translation of the variable
`y` turns `L_g (h ⋆ f)` into `(L_g h) ⋆ f`. Applied to the operator `u ↦ u ⋆ f`, which is
continuous and linear in `u`, the same identity gives associativity. The positive cone of real
`Lᵖ` is closed, so convolution of nonnegative functions is nonnegative. Integration over `G` is
a continuous linear functional on `L¹` invariant under left translation, so integrals multiply.
In particular, convolution preserves nonnegative `L¹` functions of integral one.

The integrated form `ContRepresentation.integratedOperatorL1` is the corresponding construction
for an arbitrary strongly continuous representation in place of left translation; it is stated
for an additive, not necessarily commutative, monoid and reaches multiplicative groups only
through `Additive G`, whereas this file works with the multiplicative group `G` directly. Similarly,
`TauCeti.convolutionLp` is the additive version of this construction on a finite-dimensional real
vector space with an additive Haar measure.

## Main definitions

* `MeasureTheory.Lp.convolutionL μ p hp`: the bilinear map `(h, f) ↦ h ⋆ f` from `L¹(G, μ)` and
  `Lᵖ(G, μ; E)` to `Lᵖ(G, μ; E)`, of norm at most one.

## Main results

* `MeasureTheory.Lp.convolutionL_apply`: the defining `Lᵖ`-valued Bochner integral.
* `MeasureTheory.Lp.integrable_smul_leftTranslation`: its integrand is integrable.
* `MeasureTheory.Lp.norm_convolutionL_apply_le`: Young's inequality `‖h ⋆ f‖_p ≤ ‖h‖₁ ‖f‖_p`.
* `MeasureTheory.Lp.leftTranslation_convolutionL`: `L_g (h ⋆ f) = (L_g h) ⋆ f`.
* `MeasureTheory.Lp.convolutionL_assoc`: associativity, `(h ⋆ k) ⋆ f = h ⋆ (k ⋆ f)`.
* `MeasureTheory.Lp.convolutionL_nonneg`: `h ⋆ f ≥ 0` when `h ≥ 0` and `f ≥ 0`.
* `MeasureTheory.Lp.integral_convolutionL`: `∫ (h ⋆ f) = (∫ h) • ∫ f`.

## References

* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §2.5
  and §3.2.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, proof of Theorem G.3.1.
-/

public section

noncomputable section

open Filter
open scoped ENNReal

namespace MeasureTheory.Lp

variable {G E : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] {μ : Measure G} [μ.IsMulLeftInvariant] [IsLocallyFiniteMeasure μ]
  [μ.InnerRegularCompactLTTop] [NormedAddCommGroup E] [NormedSpace ℝ E]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The integrand `y ↦ h(y) • L_y f` of a convolution is integrable. Together with
`convolutionL_apply`, this lets continuous linear maps pass through the integral defining
`h ⋆ f`. -/
theorem integrable_smul_leftTranslation (hp : p ≠ ∞) {h : G → ℝ} (hh : Integrable h μ)
    (f : Lp E p μ) : Integrable (fun y ↦ h y • leftTranslation μ p ℝ y f) μ := by
  have : Fact (p ≠ ∞) := ⟨hp⟩
  -- `y ↦ L_y f = DomMulAct.mk y⁻¹ • f` is continuous by Mathlib's `ContinuousSMul` instance.
  have hcont : Continuous fun y ↦ leftTranslation μ p ℝ y f := by
    simp_rw [leftTranslation_apply]
    exact (DomMulAct.continuous_mk.comp continuous_inv).smul continuous_const
  refine (hh.norm.mul_const ‖f‖).mono'
    (hh.aefinStronglyMeasurable.aestronglyMeasurable_smul hcont) (.of_forall fun y ↦ ?_)
  rw [norm_smul, LinearIsometryEquiv.norm_map]

omit [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop] in
/-- The integral defining a convolution is bounded by the product of the norms. -/
private theorem norm_integral_smul_leftTranslation_le (h : Lp ℝ 1 μ) (f : Lp E p μ) :
    ‖∫ y, h y • leftTranslation μ p ℝ y f ∂μ‖ ≤ ‖h‖ * ‖f‖ := by
  rw [L1.norm_eq_integral_norm, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((L1.integrable_coeFn h).norm.mul_const _)
    (.of_forall fun y ↦ ?_)
  rw [norm_smul, LinearIsometryEquiv.norm_map]

variable (μ p) in
/-- **Convolution** on a group `G` by an integrable kernel, as the bilinear map
`L¹(G, μ) →L Lᵖ(G, μ; E) →L Lᵖ(G, μ; E)` sending `(h, f)` to the `Lᵖ`-valued Bochner integral
`h ⋆ f = ∫ y, h(y) • L_y f dμ(y)` of the left translates `(L_y f)(x) = f (y⁻¹ * x)`. -/
def convolutionL (hp : p ≠ ∞) : Lp ℝ 1 μ →L[ℝ] Lp E p μ →L[ℝ] Lp E p μ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun (h : Lp ℝ 1 μ) (f : Lp E p μ) ↦
        ∫ y, h y • leftTranslation μ p ℝ y f ∂μ)
      (fun h₁ h₂ f ↦ by
        rw [← integral_add (integrable_smul_leftTranslation hp (L1.integrable_coeFn h₁) f)
          (integrable_smul_leftTranslation hp (L1.integrable_coeFn h₂) f)]
        refine integral_congr_ae ?_
        filter_upwards [coeFn_add h₁ h₂] with y hy
        rw [hy, Pi.add_apply, add_smul])
      (fun c h f ↦ by
        rw [← integral_smul]
        refine integral_congr_ae ?_
        filter_upwards [coeFn_smul c h] with y hy
        rw [hy, Pi.smul_apply, smul_eq_mul, mul_smul])
      (fun h f₁ f₂ ↦ by
        rw [← integral_add (integrable_smul_leftTranslation hp (L1.integrable_coeFn h) f₁)
          (integrable_smul_leftTranslation hp (L1.integrable_coeFn h) f₂)]
        simp_rw [map_add, smul_add])
      (fun c h f ↦ by
        rw [← integral_smul]
        simp_rw [map_smul, smul_comm c]))
    1 fun h f ↦ by simpa using norm_integral_smul_leftTranslation_le h f

variable {hp : p ≠ ∞}

/-- The convolution `h ⋆ f` is the `Lᵖ`-valued integral of the left translates of `f` weighted
by `h`. -/
theorem convolutionL_apply (h : Lp ℝ 1 μ) (f : Lp E p μ) :
    convolutionL μ p hp h f = ∫ y, h y • leftTranslation μ p ℝ y f ∂μ :=
  (rfl)

/-- The convolution of the `L¹` class of an integrable function `h` with `f`. -/
theorem convolutionL_toL1 {h : G → ℝ} (hh : Integrable h μ) (f : Lp E p μ) :
    convolutionL μ p hp (hh.toL1 h) f = ∫ y, h y • leftTranslation μ p ℝ y f ∂μ := by
  rw [convolutionL_apply]
  refine integral_congr_ae ?_
  filter_upwards [hh.coeFn_toL1] with y hy
  rw [hy]

/-- **Young's inequality** for an `L¹` kernel: `‖h ⋆ f‖_p ≤ ‖h‖₁ ‖f‖_p`. -/
theorem norm_convolutionL_apply_le (h : Lp ℝ 1 μ) (f : Lp E p μ) :
    ‖convolutionL μ p hp h f‖ ≤ ‖h‖ * ‖f‖ :=
  norm_integral_smul_leftTranslation_le h f

/-- Convolution has operator norm at most one as a bilinear map. -/
theorem norm_convolutionL_le : ‖convolutionL (E := E) μ p hp‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound₂ _ zero_le_one fun h f ↦ by
    simpa using norm_convolutionL_apply_le h f

/-- Convolution commutes with left translation: `L_g (h ⋆ f) = (L_g h) ⋆ f`. -/
theorem leftTranslation_convolutionL (g : G) (h : Lp ℝ 1 μ) (f : Lp E p μ) :
    leftTranslation μ p ℝ g (convolutionL μ p hp h f) =
      convolutionL μ p hp (leftTranslation μ 1 ℝ g h) f := by
  have hcomm := (leftTranslation μ p ℝ g).toContinuousLinearEquiv.integral_comp_comm
    (μ := μ) fun y ↦ h y • leftTranslation μ p ℝ y f
  rw [LinearIsometryEquiv.coe_toContinuousLinearEquiv] at hcomm
  -- Substitute `y ↦ g * y` on the right, using left invariance of `μ`.
  rw [convolutionL_apply, convolutionL_apply, ← hcomm, ← integral_mul_left_eq_self
    (fun y ↦ leftTranslation μ 1 ℝ g h y • leftTranslation μ p ℝ y f) g]
  refine integral_congr_ae ?_
  filter_upwards [(measurePreserving_mul_left μ g).quasiMeasurePreserving.ae
    (coeFn_leftTranslation (𝕜 := ℝ) g h)] with y hy
  simp only [hy, inv_mul_cancel_left, map_smul, map_mul, LinearIsometryEquiv.coe_mul,
    Function.comp_apply]

/-- **Associativity of convolution**: `(h ⋆ k) ⋆ f = h ⋆ (k ⋆ f)` for `L¹` kernels `h` and
`k`. -/
theorem convolutionL_assoc [CompleteSpace E] (h k : Lp ℝ 1 μ) (f : Lp E p μ) :
    convolutionL μ p hp (convolutionL μ 1 ENNReal.one_ne_top h k) f =
      convolutionL μ p hp h (convolutionL μ p hp k f) := by
  -- Push the continuous linear map `u ↦ u ⋆ f` inside the integral defining `h ⋆ k`.
  have hint := ((convolutionL μ p hp).flip f).integral_comp_comm
    (integrable_smul_leftTranslation ENNReal.one_ne_top (L1.integrable_coeFn h) k)
  simp only [ContinuousLinearMap.flip_apply, map_smul, ← leftTranslation_convolutionL] at hint
  rw [convolutionL_apply (hp := ENNReal.one_ne_top) h k, ← hint]
  exact (convolutionL_apply h _).symm

/-- The convolution of nonnegative functions is nonnegative. -/
theorem convolutionL_nonneg {h : Lp ℝ 1 μ} {f : Lp ℝ p μ} (hh : 0 ≤ h) (hf : 0 ≤ f) :
    0 ≤ convolutionL μ p hp h f := by
  rw [convolutionL_apply]
  refine integral_nonneg_of_ae ?_
  filter_upwards [(coeFn_nonneg h).2 hh] with y hy
  exact smul_nonneg hy (by simpa using leftTranslation_mono y hf)

/-- The integral of a convolution is the product of the integrals: `∫ (h ⋆ f) = (∫ h) • ∫ f`. -/
theorem integral_convolutionL [CompleteSpace E] (h : Lp ℝ 1 μ) (f : Lp E 1 μ) :
    ∫ x, convolutionL μ 1 ENNReal.one_ne_top h f x ∂μ = (∫ x, h x ∂μ) • ∫ x, f x ∂μ := by
  rw [← L1.integral_eq_integral, L1.integral_eq, convolutionL_apply,
    ← L1.integralCLM.integral_comp_comm
      (integrable_smul_leftTranslation ENNReal.one_ne_top (L1.integrable_coeFn h) f)]
  simp_rw [map_smul, ← L1.integral_eq, L1.integral_eq_integral, integral_leftTranslation,
    integral_smul_const]

end MeasureTheory.Lp
