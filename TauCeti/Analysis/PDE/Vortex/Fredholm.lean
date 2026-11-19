/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EllipticRegularity
public import TauCeti.Analysis.PDE.Vortex.SobolevRealization
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Fredholm.Criteria
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# The gauge-fixed vortex operator on `H¹` is Fredholm

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` is realized as a bounded operator

`TauCeti.Vortex.sobolevGaugeFixedOperator a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)`,

with `a` the `L∞` class of `x`. At a `C¹` vortex with `|α| → 1` and `∇₁ α → 0` at infinity, its
kernel is finite dimensional and its range is closed
(`TauCeti.Vortex.finiteDimensional_ker_sobolevGaugeFixedOperator`,
`TauCeti.Vortex.isClosed_range_sobolevGaugeFixedOperator`). This file proves that it is onto,
hence a Fredholm operator whose index is the dimension of its kernel.

The weak theory of `L_x` lives on `L²`: a square-integrable field `y` solves `L_x y = f` weakly if
`∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫` for every smooth compactly supported test field `η`. Three steps
connect it with the realization on `H¹`.

* **Integration by parts.** For `y ∈ H¹(ℂ)⁴` and a compactly supported `C¹` field `η`,
  `∫ ⟪L_x y, η⟫ = ∫ ⟪y, L_x* η⟫` (`TauCeti.Vortex.integral_inner_sobolevGaugeFixedOperator`). Both
  sides are continuous in `y ∈ H¹(ℂ)⁴`, and on test fields this is the classical identity
  `TauCeti.Vortex.integral_inner_gaugeFixedOperator`; test fields are dense in `H¹(ℂ)`. By the
  fundamental lemma of the calculus of variations, an element of `H¹(ℂ)⁴` whose values solve
  `L_x y = f` weakly is mapped to `f`
  (`TauCeti.Vortex.sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq`).
* **Regularity.** At a bounded continuous field, a weak `L²` solution of `L_x y = f` with
  `f ∈ L²` lies in the Bessel-potential space `H¹`
  (`TauCeti.Vortex.mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq`), whose real
  functions are values of elements of the weak-derivative space `W^{1,2}`
  (`TemperedDistribution.exists_w1p_value_ae_eq_of_mem_realSobolevFunctions`). So every weak
  `L²` solution is the value of a strong solution in `H¹(ℂ)⁴`
  (`TauCeti.Vortex.exists_sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq`).
  With `f = 0`, the weak `L²` kernel of `L_x` consists of values of the kernel of the realization.
* **Cokernel vanishing.** At a bounded `C¹` vortex with `|α| → 1`, the weak right inverse of
  `TauCeti.Analysis.PDE.Vortex.RightInverse` solves `L_x y = f` weakly for every `f ∈ L²`, so the
  realization is onto (`TauCeti.Vortex.sobolevGaugeFixedOperator_surjective`).

A surjective bounded operator between Banach spaces with finite-dimensional kernel is Fredholm
(`ContinuousLinearMap.IsFredholm.of_surjective`), so the realization is Fredholm
(`TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator`). Its index is the real dimension of its
kernel (`LinearMap.index_of_surjective`). At a continuous plane vortex lying in `A_m^k` for every
`k` (see `TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`) this kernel has real
dimension `2m`, the dimension of the divisor space `Sym^m ℂ`, so the index is `2m`; this is
proved in `TauCeti.Analysis.PDE.Vortex.Index`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.1.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter TopologicalSpace
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

end TauCeti.Vortex
