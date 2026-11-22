/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.PDE.Vortex.EllipticRegularity
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.SobolevRealization
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Normed.Operator.Banach
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Fredholm.Criteria
import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.Analysis.PDE.Vortex.RightInverse
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.MeasureTheory.Function.Lp.CastMeasure
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Fredholm property of the gauge-fixed vortex operator on `H¹`

For a bounded measurable field `x = (b₁, b₂, p, q)` with `L∞` class `a`, the gauge-fixed
linearized vortex operator `L_x = d₀* ⊕ d₁` is realized as the bounded linear operator

`TauCeti.Vortex.sobolevGaugeFixedOperator a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)`

constructed in `TauCeti.Analysis.PDE.Vortex.SobolevRealization`. At a `C¹` vortex with `|α| → 1`
and `∇₁ α → 0` at infinity, its kernel is finite dimensional and its range is closed
(`TauCeti.Vortex.finiteDimensional_ker_sobolevGaugeFixedOperator`,
`TauCeti.Vortex.isClosed_range_sobolevGaugeFixedOperator`). This file establishes the weak
formulation, surjectivity, bounded `L²`-orthogonal right inverse, and Fredholm property of this
Sobolev realization.

* **Weak and strong solutions.** By density of compactly supported test fields in `H¹(ℂ)⁴` and
  classical integration by parts (`TauCeti.Vortex.integral_inner_gaugeFixedOperator`), for a
  continuous field `x` with `L∞` class `a` the pairing `∫ ⟪L_a y, η⟫` equals `∫ ⟪y, L_x* η⟫` for
  every `y ∈ H¹(ℂ)⁴` and compactly supported `C¹` field `η`
  (`TauCeti.Vortex.integral_inner_sobolevGaugeFixedOperator`). By the fundamental lemma of the
  calculus of variations, `L_a y = f` holds in `L²` precisely when `y` is a weak solution of
  `L_x y = f` (`TauCeti.Vortex.sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq`,
  `TauCeti.Vortex.sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq`,
  `TauCeti.Vortex.mem_ker_sobolevGaugeFixedOperator_iff`). Combining `H¹` elliptic regularity
  (`TauCeti.Vortex.mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq`) with Calderón's
  identification (`TemperedDistribution.exists_w1p_value_ae_eq_of_mem_realSobolevFunctions`), every
  weak `L²` solution is the value of a strong solution in `H¹(ℂ)⁴`
  (`TauCeti.Vortex.exists_sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq`).
* **Surjectivity and bounded right inverse.** At a `C¹` plane vortex with `|α| → 1` at infinity
  and `L∞` class `a`, the weak right inverse of `TauCeti.Analysis.PDE.Vortex.RightInverse` solves
  `L_x y = f` weakly for every `f ∈ L²`, so the realization is surjective
  (`TauCeti.Vortex.sobolevGaugeFixedOperator_surjective`) and its cokernel vanishes. Applying the
  closed graph theorem produces a bounded right inverse `Q : L²(ℂ; ℝ⁴) → H¹(ℂ)⁴` whose values are
  `L²`-orthogonal to the kernel
  (`TauCeti.Vortex.exists_continuousLinearMap_sobolevGaugeFixedOperator_comp_eq_id`); such a
  preimage is unique for any `a`
  (`TauCeti.Vortex.eq_of_sobolevGaugeFixedOperator_eq_of_inner_sobolevFieldValues_eq_zero`).
* **Fredholm property.** Combining vanishing cokernel with the finite-dimensional kernel from
  `TauCeti.Analysis.PDE.Vortex.SobolevRealization` via
  `ContinuousLinearMap.IsFredholm.of_surjective` yields
  `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator` (for `C¹` vortices with `∇₁ α → 0`),
  `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_of_contDiff` (for `C²` vortices, where
  `TauCeti.Vortex.tendsto_covariantDerivative_cocompact` discharges `∇₁ α → 0` automatically), and
  `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_of_mem_framedFieldSpace` (on `A_m^s` for
  `s > 3`).

The kernel identification with `weakGaugeFixedKernel x` and `gaugeFixedKernel x`, the exact kernel
dimension and real Fredholm index `2 |D|` and `2 m`, and degree-zero bijectivity are proved in
`TauCeti.Analysis.PDE.Vortex.Index`.

## Main declarations

* `TauCeti.Vortex.integral_inner_sobolevGaugeFixedOperator`,
  `TauCeti.Vortex.sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq`,
  `TauCeti.Vortex.sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq`,
  `TauCeti.Vortex.mem_ker_sobolevGaugeFixedOperator_iff`, and
  `TauCeti.Vortex.exists_sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq`:
  integration by parts, weak characterization, and weak-to-strong lifting for
  `sobolevGaugeFixedOperator a`.
* `TauCeti.Vortex.sobolevGaugeFixedOperator_surjective`,
  `TauCeti.Vortex.eq_of_sobolevGaugeFixedOperator_eq_of_inner_sobolevFieldValues_eq_zero`, and
  `TauCeti.Vortex.exists_continuousLinearMap_sobolevGaugeFixedOperator_comp_eq_id`: surjectivity
  (vanishing cokernel) and unique bounded `L²`-orthogonal right inverse `L² → H¹`.
* `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator`,
  `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_of_contDiff`, and
  `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_of_mem_framedFieldSpace`: the Fredholm
  property of `sobolevGaugeFixedOperator a`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter TopologicalSpace Module
open scoped ENNReal Topology RealInnerProductSpace ContDiff Distributions

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}

/-- The pairing of the values of `y ∈ H¹(ℂ)⁴` with a field `f` whose coordinates are square
integrable, as a sum of `L²` inner products of coordinates. -/
private theorem integral_inner_value_eq_sum {f : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hf : ∀ j, MemLp (fun z ↦ f z j) 2 volume) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    ∫ z, ⟪(WithLp.toLp 2 fun j ↦ W1p.value (y j) z : EuclideanSpace ℝ (Fin 4)), f z⟫ =
      ∑ j, ⟪W1p.valueL (y j),
        ((hf j).mono_measure (Measure.restrict_coe_opens_top _).le).toLp _⟫ := by
  have hint (j : Fin 4) : Integrable (fun z ↦ f z j * W1p.value (y j) z) :=
    (hf j).integrable_mul (W1p.memLp_value (y j))
  simp_rw [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [integral_finsetSum _ fun j _ ↦ hint j]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [L2.inner_toLp, Measure.restrict_coe_opens_top, W1p.valueL_apply,
    RCLike.inner_apply, conj_trivial]

/-! ### Weak and strong solutions -/

/-- **Integration by parts for the `H¹` realization of `L_x`.** Let `x` be a continuous field with
`L∞` class `a`. For every `y ∈ H¹(ℂ)⁴` and every compactly supported `C¹` field `η`,
`∫ ⟪L_x y, η⟫ = ∫ ⟪y, L_x* η⟫`. -/
theorem integral_inner_sobolevGaugeFixedOperator (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪sobolevGaugeFixedOperator a y z, η z⟫ =
      ∫ z, ⟪(WithLp.toLp 2 fun j ↦ W1p.value (y j) z : EuclideanSpace ℝ (Fin 4)),
        gaugeFixedAdjoint x η z⟫ := by
  have hL := continuous_gaugeFixedAdjoint hx hη
  have hLc := hasCompactSupport_gaugeFixedAdjoint (x := x) hηc
  have hLj (j : Fin 4) : MemLp (fun z ↦ gaugeFixedAdjoint x η z j) 2 volume :=
    ((continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp hL)).memLp_of_hasCompactSupport
      (hLc.comp_left (g := fun v : EuclideanSpace ℝ (Fin 4) ↦ v j) rfl)
  have hη2 : MemLp η 2 μ⊤ := (hη.continuous.memLp_of_hasCompactSupport hηc).mono_measure
    (Measure.restrict_coe_opens_top _).le
  have hpair (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) : ∫ z, ⟪g z, η z⟫ = ⟪g, hη2.toLp η⟫ := by
    simp only [L2.inner_toLp g hη2, Measure.restrict_coe_opens_top]
  rw [hpair, integral_inner_value_eq_sum hLj]
  -- Both sides are continuous in `y`, and agree on the dense subspace of test fields.
  refine (DenseRange.piMap fun _ : Fin 4 ↦
    W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 2) (by norm_num)).induction_on
      (p := fun y ↦ ⟪sobolevGaugeFixedOperator a y, hη2.toLp η⟫ =
        ∑ j, ⟪W1p.valueL (y j),
          ((hLj j).mono_measure (Measure.restrict_coe_opens_top _).le).toLp _⟫)
      y ?_ fun φ ↦ ?_
  · exact isClosed_eq ((sobolevGaugeFixedOperator a).continuous.inner continuous_const)
      (continuous_finsetSum _ fun j _ ↦
        ((W1p.valueL.continuous.comp (continuous_apply j)).inner continuous_const))
  · set Y : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ WithLp.toLp 2 fun j ↦ φ j z
    have hY : ContDiff ℝ 1 Y := ((contDiff_piLp 2).2 fun j ↦ (φ j).contDiff).of_le (by simp)
    have hYc : HasCompactSupport Y :=
      (hasCompactSupport_pi_iff.2 fun j ↦ (φ j).hasCompactSupport).comp_left
        (g := WithLp.toLp 2) (WithLp.toLp_zero 2)
    have hvalue (j : Fin 4) : W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) =ᵐ[μ⊤]
        fun z ↦ Y z j :=
      W1p.value_ofTestFunctionₗ_ae (φ j)
    have hT := (sobolevGaugeFixedOperator_ae_eq_gaugeFixedOperator hax
      (y := Pi.map (fun _ ↦ W1p.ofTestFunctionₗ volume ⊤ 2) φ) hY hvalue).filter_mono
        (ae_mono (Measure.restrict_coe_opens_top _).ge)
    rw [← hpair, ← integral_inner_value_eq_sum hLj,
      integral_congr_ae (hT.mono fun z hz ↦ by rw [hz]),
      integral_inner_gaugeFixedOperator hY hη (.inl hYc)]
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 fun j ↦ ae_mono (Measure.restrict_coe_opens_top _).ge (hvalue j)]
      with z hz
    simp only [Pi.map_apply, hz, Y]

/-- **Weak solutions in `H¹` are strong.** Let `x` be a continuous field with `L∞` class `a`, and
let `y ∈ H¹(ℂ)⁴` be such that its values solve `L_x y = f` weakly, for `f ∈ L²(ℂ; ℝ⁴)`:
`∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every smooth compactly supported test field `η`. Then the
realization maps `y` to `f`. -/
theorem sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq (hx : Continuous x)
    (hax : a =ᵐ[μ⊤] x) {y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2}
    {f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤}
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪(WithLp.toLp 2 fun j ↦ W1p.value (y j) z : EuclideanSpace ℝ (Fin 4)),
        gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    sobolevGaugeFixedOperator a y = f := by
  have hloc (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
      LocallyIntegrableOn (g : ℂ → EuclideanSpace ℝ (Fin 4)) (⊤ : Opens ℂ) volume :=
    (((Lp.memLp g).mono_measure (Measure.restrict_coe_opens_top _).ge).locallyIntegrable
      (by norm_num)).locallyIntegrableOn _
  refine Lp.ext (ae_eq_of_forall_integral_inner_eq (hloc _) (hloc f) fun φ ↦ ?_)
  have hcomm (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
      ∫ z, ⟪(φ : ℂ → EuclideanSpace ℝ (Fin 4)) z, g z⟫ = ∫ z, ⟪g z, φ z⟫ :=
    integral_congr_ae (ae_of_all _ fun z ↦ real_inner_comm _ _)
  rw [hcomm, hcomm, integral_inner_sobolevGaugeFixedOperator hx hax y
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport]
  exact hweak φ φ.contDiff φ.hasCompactSupport

/-- **Weak characterization of `sobolevGaugeFixedOperator a`.** At a continuous field `x` with
`L∞` class `a`, an element `y ∈ H¹(ℂ)⁴` satisfies `sobolevGaugeFixedOperator a y = f` in `L²` if
and only if `y` is a weak solution of `L_x y = f` against all smooth compactly supported test
fields. -/
theorem sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq
    (hx : Continuous x) (hax : a =ᵐ[μ⊤] x) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
    sobolevGaugeFixedOperator a y = f ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪(WithLp.toLp 2 fun j ↦ W1p.value (y j) z : EuclideanSpace ℝ (Fin 4)),
          gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫ :=
  ⟨by rintro rfl η hη hηc
      exact (integral_inner_sobolevGaugeFixedOperator hx hax y (hη.of_le (by simp)) hηc).symm,
    sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq hx hax⟩

/-- **The kernel of the `H¹` realization is the weak kernel.** At a continuous field `x` with
`L∞` class `a`, an element `y ∈ H¹(ℂ)⁴` lies in the kernel of the realization exactly when its
values solve `L_x y = 0` weakly: `∫ ⟪y, L_x* η⟫ = 0` for every smooth compactly supported test
field `η`. -/
theorem mem_ker_sobolevGaugeFixedOperator_iff (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    {y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2} :
    y ∈ (sobolevGaugeFixedOperator a).ker ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪(WithLp.toLp 2 fun j ↦ W1p.value (y j) z : EuclideanSpace ℝ (Fin 4)),
          gaugeFixedAdjoint x η z⟫ = 0 := by
  have h0 (η : ℂ → EuclideanSpace ℝ (Fin 4)) :
      ∫ z, ⟪(0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) z, η z⟫ = 0 := by
    rw [integral_congr_ae (((Lp.coeFn_zero _ 2 μ⊤).filter_mono
      (ae_mono (Measure.restrict_coe_opens_top _).ge)).mono
      fun z hz ↦ by rw [hz, Pi.zero_apply, inner_zero_left])]
    exact integral_zero _ _
  refine ⟨fun hy η hη hηc ↦ ?_, fun h ↦ ?_⟩
  · have hy' : sobolevGaugeFixedOperator a y = 0 := by simpa using hy
    rw [← integral_inner_sobolevGaugeFixedOperator hx hax y (hη.of_le (by simp)) hηc, hy', h0]
  · exact LinearMap.mem_ker.2 (sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq
      hx hax fun η hη hηc ↦ by rw [h η hη hηc, h0])

/-- **Weak `L²` solutions are values of strong `H¹` solutions.** Let `x` be a bounded continuous
field with `L∞` class `a`, and let `y` be a square-integrable weak solution of `L_x y = f` with
`f ∈ L²(ℂ; ℝ⁴)`: `∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every smooth compactly supported test field `η`.
Then `y` is almost everywhere the value of some `w ∈ H¹(ℂ)⁴` with `L_x w = f`. With `f = 0`, the
weak `L²` kernel of `L_x` consists of values of the kernel of the realization. -/
theorem exists_sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq
    (hx : Continuous x) (hax : a =ᵐ[μ⊤] x) {y : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hy : MemLp y 2 volume) {f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤}
    (hweak : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫) :
    ∃ w : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2,
      (∀ j, W1p.value (w j) =ᵐ[volume] fun z ↦ y z j) ∧ sobolevGaugeFixedOperator a w = f := by
  have hM (z : ℂ) : ‖x z‖ ≤ ‖a‖ :=
    Lp.norm_le_norm_top_of_ae_eq_of_continuousAt hax hx.continuousAt
  have hH := mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq
    hx.aestronglyMeasurable (ae_of_all _ hM) hy
    ((Lp.memLp f).mono_measure (Measure.restrict_coe_opens_top _).ge) hweak
  choose w hw using fun j ↦ TemperedDistribution.exists_w1p_value_ae_eq_of_mem_realSobolevFunctions
    (p := 2) (by norm_num) (by norm_num) le_rfl (mem_sobolevFields.1 hH j)
  refine ⟨w, hw, sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq hx hax
    fun η hη hηc ↦ ?_⟩
  rw [← hweak η hη hηc]
  refine integral_congr_ae ?_
  filter_upwards [ae_all_iff.2 hw] with z hz
  congr 1
  ext j
  exact hz j

/-! ### Bounded `L²`-orthogonal right inverse, surjectivity, and vanishing cokernel -/

/-- **Uniqueness of `L²`-orthogonal preimages.** For any `L∞` coefficient `a`, two elements of
`H¹(ℂ)⁴` with the same image under `sobolevGaugeFixedOperator a` that are both `L²`-orthogonal to
its kernel are equal. -/
theorem eq_of_sobolevGaugeFixedOperator_eq_of_inner_sobolevFieldValues_eq_zero
    (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤)
    {y₁ y₂ : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2}
    (heq : sobolevGaugeFixedOperator a y₁ = sobolevGaugeFixedOperator a y₂)
    (hy₁ : ∀ u ∈ (sobolevGaugeFixedOperator a).ker,
      ⟪sobolevFieldValues y₁, sobolevFieldValues u⟫ = 0)
    (hy₂ : ∀ u ∈ (sobolevGaugeFixedOperator a).ker,
      ⟪sobolevFieldValues y₂, sobolevFieldValues u⟫ = 0) :
    y₁ = y₂ := by
  have hker : y₁ - y₂ ∈ (sobolevGaugeFixedOperator a).ker := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, heq, sub_self]
  have hzero : ⟪sobolevFieldValues (y₁ - y₂), sobolevFieldValues (y₁ - y₂)⟫ = 0 := by
    have hsub : ⟪sobolevFieldValues (y₁ - y₂), sobolevFieldValues (y₁ - y₂)⟫ =
        ⟪sobolevFieldValues y₁, sobolevFieldValues (y₁ - y₂)⟫ -
          ⟪sobolevFieldValues y₂, sobolevFieldValues (y₁ - y₂)⟫ := by
      rw [← inner_sub_left, ← map_sub]
    rw [hsub, hy₁ _ hker, hy₂ _ hker, sub_self]
  exact sub_eq_zero.1 (sobolevFieldValues_injective (by simpa using inner_self_eq_zero.1 hzero))

/-- **Bounded `L²`-orthogonal right inverse `L² → H¹`.** At a `C¹` plane vortex `x` with
`|α| → 1` at infinity and `L∞` class `a`, there is a continuous linear right inverse
`Q : L²(ℂ; ℝ⁴) → H¹(ℂ)⁴` of `sobolevGaugeFixedOperator a` whose outputs are `L²`-orthogonal to
the kernel of `sobolevGaugeFixedOperator a`. By
`TauCeti.Vortex.eq_of_sobolevGaugeFixedOperator_eq_of_inner_sobolevFieldValues_eq_zero`, this
operator `Q` is unique. -/
theorem exists_continuousLinearMap_sobolevGaugeFixedOperator_comp_eq_id (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2),
      (sobolevGaugeFixedOperator a).comp Q = ContinuousLinearMap.id ℝ _ ∧
        ∀ f, ∀ u ∈ (sobolevGaugeFixedOperator a).ker,
          ⟪sobolevFieldValues (Q f), sobolevFieldValues u⟫ = 0 := by
  -- Transport the `L²` minimal weak right inverse from `volume` to `μ⊤`, then lift to `H¹(ℂ)⁴`.
  obtain ⟨Q₀, hQ₀⟩ := exists_continuousLinearMap_isMinimalGaugeFixedWeakSolution
    (μ := volume) hx hsol hlim
  set e := castLpₗᵢ (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (p := 2)
    (Measure.restrict_coe_opens_top (volume : Measure ℂ))
  set Q₁ : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ :=
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (Q₀.comp e.toContinuousLinearEquiv.toContinuousLinearMap)
  have hQ₁_apply (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (z : ℂ) : Q₁ f z = Q₀ (e f) z := by
    simp only [Q₁, e, ContinuousLinearMap.comp_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
      castLpₗᵢ_symm, coeFn_castLpₗᵢ]
  have hQ₁_mem (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
      ∃ w : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2,
        sobolevFieldValues w = Q₁ f ∧ sobolevGaugeFixedOperator a w = f := by
    obtain ⟨w, hw, hLw⟩ :=
      exists_sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq
        hx.continuous hax ((Lp.memLp (Q₁ f)).mono_measure (Measure.restrict_coe_opens_top _).ge)
        (f := f) fun η hη hηc ↦ by
        have hL : ∫ z, ⟪(Q₁ f) z, gaugeFixedAdjoint x η z⟫ =
            ∫ z, ⟪(Q₀ (e f)) z, gaugeFixedAdjoint x η z⟫ :=
          integral_congr_ae (.of_forall fun z ↦ by simp only [hQ₁_apply])
        rw [hL, isGaugeFixedWeakSolution_iff.1 (hQ₀ (e f)).isGaugeFixedWeakSolution
          η (hη.of_le (by simp)) hηc]
        exact integral_congr_ae (.of_forall fun z ↦ by simp only [e, coeFn_castLpₗᵢ])
    refine ⟨w, Lp.ext ?_, hLw⟩
    filter_upwards [sobolevFieldValues_ae_eq w, ae_restrict_of_ae (ae_all_iff.2 hw)] with z h₁ h₂
    rw [h₁]
    ext j
    exact h₂ j
  let qL : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →ₗ[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :=
    Q₁.toLinearMap.codRestrictOfInjective sobolevFieldValues.toLinearMap
      sobolevFieldValues_injective fun f ↦ let ⟨w, hw, _⟩ := hQ₁_mem f; ⟨w, hw⟩
  have hqL (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) : sobolevFieldValues (qL f) = Q₁ f :=
    Q₁.toLinearMap.codRestrictOfInjective_comp_apply sobolevFieldValues.toLinearMap
      sobolevFieldValues_injective _ f
  have hclosed : IsClosed (qL.graph : Set (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ ×
      (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2))) := by
    have hgraph : (qL.graph : Set (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ ×
        (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2))) = {p | sobolevFieldValues p.snd = Q₁ p.fst} := by
      ext ⟨f, y⟩
      simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_ofPred_eq]
      exact ⟨fun h ↦ by rw [h, hqL], fun h ↦ sobolevFieldValues_injective (by rw [h, hqL])⟩
    rw [hgraph]
    exact isClosed_eq (sobolevFieldValues.continuous.comp continuous_snd)
      (Q₁.continuous.comp continuous_fst)
  refine ⟨ContinuousLinearMap.ofIsClosedGraph hclosed, ?_, fun f u hu ↦ ?_⟩
  · ext1 f
    obtain ⟨w, hw, hLw⟩ := hQ₁_mem f
    have hQw : ContinuousLinearMap.ofIsClosedGraph hclosed f = w :=
      sobolevFieldValues_injective (by simpa [hqL] using hw.symm)
    simpa [hQw] using hLw
  · have hQ_apply : sobolevFieldValues (ContinuousLinearMap.ofIsClosedGraph hclosed f) = Q₁ f := by
      simpa using hqL f
    have hu_weak : IsGaugeFixedWeakSolution volume x 0 (e (sobolevFieldValues u)) := by
      refine isGaugeFixedWeakSolution_iff.2 fun η hη hηc ↦ ?_
      have hae : (e (sobolevFieldValues u) : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume]
          fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (u j) z := by
        filter_upwards [ae_mono (Measure.restrict_coe_opens_top volume).ge
          (sobolevFieldValues_ae_eq u)] with z hz
        simpa only [e, coeFn_castLpₗᵢ] using hz
      have hEq : ∫ z, ⟪(e (sobolevFieldValues u)) z, gaugeFixedAdjoint x η z⟫ =
          ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (u j) z), gaugeFixedAdjoint x η z⟫ :=
        integral_congr_ae (hae.mono fun z hz ↦ congrArg (⟪·, gaugeFixedAdjoint x η z⟫) hz)
      have h0 : sobolevGaugeFixedOperator a u = 0 := by simpa using LinearMap.mem_ker.1 hu
      rw [Lp.integral_inner_coeFn_zero_left, hEq,
        ← integral_inner_sobolevGaugeFixedOperator hx.continuous hax u (hη.of_le one_le_two) hηc,
        h0]
      have hz : ∀ᵐ z ∂volume, (0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) z = 0 :=
        ae_mono (Measure.restrict_coe_opens_top volume).ge (Lp.coeFn_zero _ 2 μ⊤)
      rw [integral_congr_ae (hz.mono fun z h ↦ by rw [h, inner_zero_left]), integral_zero]
    rw [hQ_apply, ← e.inner_map_map (Q₁ f) (sobolevFieldValues u),
      show e (Q₁ f) = Q₀ (e f) from by simp [Q₁], L2.inner_def]
    exact (hQ₀ (e f)).integral_inner_eq_zero hu_weak

/-- **The realization of `L_x` on `H¹` is onto** at a `C¹` vortex `x` with `|α| → 1` at infinity
and with `L∞` class `a`: its cokernel vanishes. -/
theorem sobolevGaugeFixedOperator_surjective (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    Function.Surjective (sobolevGaugeFixedOperator a) := by
  intro f
  have hM (z : ℂ) : ‖x z‖ ≤ ‖a‖ :=
    Lp.norm_le_norm_top_of_ae_eq_of_continuousAt hax hx.continuous.continuousAt
  obtain ⟨y, hy, hweak⟩ := exists_mem_sobolevFields_one_integral_inner_gaugeFixedAdjoint_eq hx hM
    hsol hlim ((Lp.memLp f).mono_measure (Measure.restrict_coe_opens_top _).ge)
  obtain ⟨w, -, hw⟩ := exists_sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq
    hx.continuous hax (memLp_of_mem_sobolevFields hy)
      fun η hη hηc ↦ hweak η (hη.of_le (by simp)) hηc
  exact ⟨w, hw⟩

/-! ### Fredholm property -/

/-- **The realization of `L_x` on `H¹` is Fredholm** at a `C¹` vortex `x` with `|α| → 1` and
`∇₁ α → 0` at infinity and with `L∞` class `a`. It is onto, so its index is the real dimension
of its kernel (`LinearMap.index_of_surjective`). -/
theorem isFredholm_sobolevGaugeFixedOperator (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).IsFredholm := by
  have := finiteDimensional_ker_sobolevGaugeFixedOperator hx hsol hlim hcov hax
  exact .of_surjective (sobolevGaugeFixedOperator_surjective hx hsol hlim hax)

/-- **Fredholm property of `L_x : H¹ → L²` at a `C²` vortex.** At a `C²` plane vortex `x` with
`|α| → 1` at infinity and with `L∞` class `a`, the exponential decay of `d_a α` gives `∇₁ α → 0`
at infinity automatically, so `sobolevGaugeFixedOperator a` is a Fredholm operator. -/
theorem isFredholm_sobolevGaugeFixedOperator_of_contDiff (hx : ContDiff ℝ 2 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    ContinuousLinearMap.IsFredholm (sobolevGaugeFixedOperator a) :=
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx i
  isFredholm_sobolevGaugeFixedOperator (hx.of_le one_le_two) hsol hlim
    (tendsto_covariantDerivative_cocompact (hxi 0).continuous (hxi 2) (hxi 3) hsol hlim 1) hax

/-! ### Specialization to the framed affine field space `A_m^s` -/

section FramedFieldSpace

variable {ρ : ContDiffBump (0 : ℝ)} {m : ℕ}

/-- **Fredholm property on the framed affine field space `A_m^s` (`s > 3`).** At a continuous
vortex `x ∈ framedFieldSpace ρ m s` with `3 < s` and `L∞` class `a`, the Sobolev embedding
`H^s(ℂ) ↪ C²(ℂ)` gives `ContDiff ℝ 2 x` and `|α|² → 1`, so `sobolevGaugeFixedOperator a` is
Fredholm. -/
theorem isFredholm_sobolevGaugeFixedOperator_of_mem_framedFieldSpace {s : ℝ} (hs : 3 < s)
    (hx : Continuous x) (hmem : x ∈ framedFieldSpace ρ m s) (hsol : ∀ z, equation x z = 0)
    (hax : a =ᵐ[μ⊤] x) :
    ContinuousLinearMap.IsFredholm (sobolevGaugeFixedOperator a) :=
  isFredholm_sobolevGaugeFixedOperator_of_contDiff
    (contDiff_of_mem_framedFieldSpace (n := 2) (by push_cast; linarith) hx hmem) hsol
    (tendsto_normSq_of_mem_framedFieldSpace (by linarith) hmem hx) hax

end FramedFieldSpace

end TauCeti.Vortex
