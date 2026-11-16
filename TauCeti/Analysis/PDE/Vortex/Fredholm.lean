/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Basic
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.PrincipalPart
public import TauCeti.Analysis.PDE.Vortex.SobolevRealization
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Fredholm.ClosedRange
import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.Analysis.PDE.Vortex.EllipticRegularity
import TauCeti.Analysis.PDE.Vortex.KernelDimension
import TauCeti.Analysis.PDE.Vortex.RightInverse
import TauCeti.Analysis.Sobolev.BesselPotential.Basic
import TauCeti.Analysis.Sobolev.BesselPotential.Embedding
import TauCeti.Analysis.Sobolev.W1p.Density
import TauCeti.MeasureTheory.Function.Lp.CastMeasure
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Measure.Restrict

/-!
# Fredholm property and index of the gauge-fixed vortex operator on `H¹`

For a bounded measurable field `x = (b₁, b₂, p, q)` with `L∞` class `a`, the gauge-fixed
linearized vortex operator `L_x = d₀* ⊕ d₁` is realized as the bounded linear operator

`TauCeti.Vortex.sobolevGaugeFixedOperator a : H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)`

constructed in `TauCeti.Analysis.PDE.Vortex.SobolevRealization`. This file establishes the weak
formulation, surjectivity, bounded `L²`-orthogonal right inverse, Fredholm property, kernel
identification with the principal-part space `ℂ^|D|`, and exact real index `2 |D|` (and `2 m` in the
framed degree-`m` case) of this Sobolev realization.

* **Weak formulation.** By density of compactly supported test fields in `H¹(ℂ)⁴` and classical
  integration by parts (`TauCeti.Vortex.integral_inner_gaugeFixedOperator`), for a continuous
  field `x` with `L∞` class `a` the pairing `∫ ⟪L_a y, η⟫` equals `∫ ⟪y, L_x* η⟫` for every
  `y ∈ H¹(ℂ)⁴` and compactly supported `C¹` field `η`
  (`TauCeti.Vortex.integral_inner_sobolevGaugeFixedOperator`). Thus `L_a y = f` holds in `L²`
  precisely when `y` is a weak solution of `L_x y = f`
  (`TauCeti.Vortex.sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq`,
  `TauCeti.Vortex.mem_ker_sobolevGaugeFixedOperator_iff`).
* **Bounded right inverse and surjectivity.** At a `C¹` plane vortex with `|α| → 1` at infinity
  and `L∞` class `a`, combining the weak right inverse of `TauCeti.Analysis.PDE.Vortex.RightInverse`
  with `H¹` elliptic regularity (`TauCeti.Analysis.PDE.Vortex.EllipticRegularity`) and the closed
  graph theorem yields a bounded right inverse `Q : L²(ℂ; ℝ⁴) → H¹(ℂ)⁴` whose values are
  `L²`-orthogonal to the kernel
  (`TauCeti.Vortex.exists_continuousLinearMap_sobolevGaugeFixedOperator_comp_eq_id`); such a
  preimage is unique for any `a`
  (`TauCeti.Vortex.eq_of_sobolevGaugeFixedOperator_eq_of_sum_inner_value_eq_zero`). In particular,
  `sobolevGaugeFixedOperator a` is surjective
  (`TauCeti.Vortex.surjective_sobolevGaugeFixedOperator`) and its cokernel vanishes.
* **Fredholm property.** Combining vanishing cokernel with the finite-dimensional kernel from
  `TauCeti.Analysis.PDE.Vortex.SobolevRealization` yields
  `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator` (for `C¹` vortices with `∇₁ α → 0`) and
  `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_of_contDiff` (for `C²` vortices, where
  exponential decay of `d_a α` in `TauCeti.Analysis.PDE.Vortex.DerivativeDecay` discharges
  `∇₁ α → 0` automatically).
* **Kernel identification and index `2 |D|` / `2 m`.** At any smooth field `x` whose derivatives
  through order `3` are bounded, elliptic bootstrap to `H⁴` and Sobolev embedding `H⁴(ℂ) ↪ C²(ℂ)`
  give a canonical real-linear equivalence
  `TauCeti.Vortex.kerSobolevGaugeFixedOperatorEquiv` from `(sobolevGaugeFixedOperator a).ker` to
  `gaugeFixedKernel x`, sending an `H¹` kernel element to its unique `C²` representative. At a
  smooth field satisfying `∂bar_a α = 0` with `|α| → 1` and zero divisor `D`, composing this
  equivalence with the principal-part map `TauCeti.Vortex.principalPartMap` is a real-linear
  isomorphism onto `D → ℂ`
  (`TauCeti.Vortex.bijective_principalPartMap_comp_kerSobolevGaugeFixedOperatorEquiv`), identifying
  the `H¹` kernel with the real tangent space of the symmetric divisor space `Sym^|D| ℂ`.
  In particular, the kernel has real dimension `2 |D|` (and `2 m` under the degree-`m` end
  framing), and at a smooth plane vortex `sobolevGaugeFixedOperator a` has real Fredholm index
  `2 |D|` (and `2 m` in degree `m`), and is bijective when `α` has no zeros (in particular in
  degree `0`). Specialization to the framed affine field space `A_m^s` concludes the file.

## Main declarations

* `TauCeti.Vortex.integral_inner_sobolevGaugeFixedOperator` and
  `TauCeti.Vortex.sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq`:
  integration by parts and weak characterization of `sobolevGaugeFixedOperator a`.
* `TauCeti.Vortex.surjective_sobolevGaugeFixedOperator` and
  `TauCeti.Vortex.exists_continuousLinearMap_sobolevGaugeFixedOperator_comp_eq_id`: surjectivity
  (vanishing cokernel) and bounded `L²`-orthogonal right inverse `L² → H¹`.
* `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator` and
  `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_of_contDiff`: the Fredholm property of
  `sobolevGaugeFixedOperator a`.
* `TauCeti.Vortex.kerSobolevGaugeFixedOperatorEquiv`: canonical real-linear equivalence between
  the `H¹` kernel and the classical `C²` kernel `gaugeFixedKernel x`.
* `TauCeti.Vortex.bijective_principalPartMap_comp_kerSobolevGaugeFixedOperatorEquiv`: isomorphism
  between the `H¹` kernel and the principal-part space `D → ℂ`.
* `TauCeti.Vortex.finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_card`,
  `TauCeti.Vortex.finrank_ker_sobolevGaugeFixedOperator_eq_two_mul`,
  `TauCeti.Vortex.index_sobolevGaugeFixedOperator_eq_two_mul_card`,
  `TauCeti.Vortex.index_sobolevGaugeFixedOperator_eq_two_mul`: exact kernel dimension and real
  Fredholm index `2 |D|` and `2 m`.
* `TauCeti.Vortex.bijective_sobolevGaugeFixedOperator_of_forall_sectionValue_ne_zero` and
  `TauCeti.Vortex.bijective_sobolevGaugeFixedOperator`: bijectivity when the section has no zeros
  and in degree zero.
* `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_of_mem_framedFieldSpace`,
  `TauCeti.Vortex.finrank_ker_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace`, and
  `TauCeti.Vortex.index_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace`: Fredholm
  property, kernel dimension `2 m`, and index `2 m` on the framed affine field space `A_m^s`.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* T. M. Samols, *Vortex scattering*, Comm. Math. Phys. 145 (1992), 149–179.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed.,
  Appendix A.1.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex MeasureTheory Filter TopologicalSpace Module
open scoped ENNReal Topology RealInnerProductSpace ContDiff Distributions

local notation "μ⊤" => Measure.restrict (volume : Measure ℂ) ((⊤ : Opens ℂ) : Set ℂ)

/-! ### Internal helpers for `H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` value embedding -/

/-- The continuous linear map taking a Sobolev field `y ∈ H¹(ℂ)⁴` to its `L²(ℂ; ℝ⁴)` value class. -/
private def sobolevFieldValueL :
    (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ :=
  ∑ j : Fin 4, ((ContinuousLinearMap.toSpanSingleton ℝ
    (EuclideanSpace.single j (1 : ℝ))).compLpL 2 μ⊤).comp
      (W1p.valueL.comp (ContinuousLinearMap.proj j))

/-- Almost everywhere, `sobolevFieldValueL y` evaluates to the tuple of values of `y`. -/
private theorem sobolevFieldValueL_apply_ae (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevFieldValueL y =ᵐ[μ⊤] fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y j) z := by
  simp only [sobolevFieldValueL, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, W1p.valueL_apply]
  have hv : ∀ᵐ z ∂μ⊤, ∀ j : Fin 4,
      (ContinuousLinearMap.compLpL 2 μ⊤ (ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single j (1 : ℝ))) (W1p.value (y j))) z =
          W1p.value (y j) z • EuclideanSpace.single j (1 : ℝ) :=
    ae_all_iff.2 fun j ↦ (ContinuousLinearMap.toSpanSingleton ℝ
      (EuclideanSpace.single j (1 : ℝ))).coeFn_compLpL (W1p.value (y j))
  filter_upwards [Lp.coeFn_finsetSum (μ := μ⊤) (p := 2) Finset.univ fun j : Fin 4 ↦
      ContinuousLinearMap.compLpL 2 μ⊤ (ContinuousLinearMap.toSpanSingleton ℝ
        (EuclideanSpace.single j (1 : ℝ))) (W1p.value (y j)), hv] with z hsum hcomp
  rw [hsum]
  simp only [Finset.sum_apply, hcomp]
  ext i
  simp [WithLp.ofLp_sum, EuclideanSpace.single, Pi.single_apply]

/-- A Sobolev field is uniquely determined by its `L²` value class. -/
private theorem sobolevFieldValueL_injective : Function.Injective sobolevFieldValueL := by
  intro y₁ y₂ h
  have hae : (fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y₁ j) z) =ᵐ[μ⊤]
      fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y₂ j) z :=
    (sobolevFieldValueL_apply_ae y₁).symm.trans ((Lp.ext_iff.1 h).trans
      (sobolevFieldValueL_apply_ae y₂))
  ext j : 1
  refine W1p.ext_value (Lp.ext ?_)
  exact hae.mono fun z hz ↦ congrArg (fun v : EuclideanSpace ℝ (Fin 4) ↦ v j) hz

/-- The `L²` inner product of `sobolevFieldValueL y` and `sobolevFieldValueL u` is the sum of
coordinatewise `L²` inner products of their values. -/
private theorem inner_sobolevFieldValueL (y u : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    ⟪sobolevFieldValueL y, sobolevFieldValueL u⟫ =
      ∑ j : Fin 4, ⟪W1p.value (y j), W1p.value (u j)⟫ := by
  rw [L2.inner_def]
  have hcoord (j : Fin 4) : ⟪W1p.value (y j), W1p.value (u j)⟫ =
      ∫ z, W1p.value (y j) z * W1p.value (u j) z ∂μ⊤ := by
    rw [W1p.inner_value_eq_setIntegral]
  have hint (j : Fin 4) : Integrable (fun z ↦ W1p.value (y j) z * W1p.value (u j) z) μ⊤ :=
    (Lp.memLp (W1p.value (y j))).integrable_mul (Lp.memLp (W1p.value (u j)))
  simp_rw [hcoord]
  rw [← integral_finsetSum _ fun j _ ↦ hint j]
  refine integral_congr_ae ?_
  filter_upwards [sobolevFieldValueL_apply_ae y, sobolevFieldValueL_apply_ae u] with z hy hu
  rw [hy, hu, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

/-- Every field in `sobolevFields 1` is represented almost everywhere by the values of an element
of `H¹(ℂ)⁴`. -/
private theorem exists_sobolevField_value_ae_eq_of_mem_sobolevFields
    {Y : ℂ → EuclideanSpace ℝ (Fin 4)} (hY : Y ∈ sobolevFields 1) :
    ∃ y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2,
      ∀ j : Fin 4, W1p.value (y j) =ᵐ[μ⊤] fun z ↦ Y z j := by
  choose y hy using fun j : Fin 4 ↦
    TemperedDistribution.exists_w1p_value_ae_eq_of_mem_realSobolevFunctions
      (p := 2) (by norm_num) (by norm_num) le_rfl (mem_sobolevFields.1 hY j)
  exact ⟨y, fun j ↦ by simpa only [Opens.coe_top, Measure.restrict_univ] using hy j⟩

/-- Any continuous linear operator `Q₁ : L²(ℂ; ℝ⁴) → L²(ℂ; ℝ⁴)` whose outputs lie in
`sobolevFields 1` lifts to a continuous linear operator `Q : L²(ℂ; ℝ⁴) → H¹(ℂ)⁴` with
`sobolevFieldValueL ∘ Q = Q₁`, by the closed graph theorem. -/
private theorem exists_lift_sobolevFieldValueL
    (Q₁ : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)
    (hmem : ∀ f, (Q₁ f : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields 1) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2),
      sobolevFieldValueL.comp Q = Q₁ := by
  have hQ₁_mem (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
      ∃ y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2, sobolevFieldValueL y = Q₁ f := by
    obtain ⟨y, hy⟩ := exists_sobolevField_value_ae_eq_of_mem_sobolevFields (hmem f)
    refine ⟨y, Lp.ext ?_⟩
    filter_upwards [sobolevFieldValueL_apply_ae y, ae_all_iff.2 hy] with z h₁ h₂
    rw [h₁]
    ext j
    exact h₂ j
  choose q hq using hQ₁_mem
  let qL : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →ₗ[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :=
    { toFun := q
      map_add' f g := sobolevFieldValueL_injective (by simp [hq])
      map_smul' c f := sobolevFieldValueL_injective (by simp [hq]) }
  have hclosed : IsClosed (qL.graph : Set (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ ×
      (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2))) := by
    have hgraph : (qL.graph : Set (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ ×
        (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2))) = {p | sobolevFieldValueL p.2 = Q₁ p.1} := by
      ext ⟨f, y⟩
      simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_ofPred_eq, qL, LinearMap.coe_mk,
        AddHom.coe_mk]
      exact ⟨fun h ↦ by rw [h, hq], fun h ↦ sobolevFieldValueL_injective (by rw [h, hq])⟩
    rw [hgraph]
    exact isClosed_eq (sobolevFieldValueL.continuous.comp continuous_snd)
      (Q₁.continuous.comp continuous_fst)
  refine ⟨ContinuousLinearMap.ofIsClosedGraph hclosed, ?_⟩
  ext1 f
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coeFn_ofIsClosedGraph, qL,
    LinearMap.coe_mk, AddHom.coe_mk] using hq f

/-! ### Weak formulation of the Sobolev realization -/

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤}

/-- **Integration by parts for the Sobolev realization `sobolevGaugeFixedOperator a`.** At a
continuous field `x` with `L∞` class `a`, the pairing of `sobolevGaugeFixedOperator a y` with a
compactly supported `C¹` field `η` equals the pairing of the value of `y` with `L_x* η`. -/
theorem integral_inner_sobolevGaugeFixedOperator (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) :
    ∫ z, ⟪sobolevGaugeFixedOperator a y z, η z⟫ =
      ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint x η z⟫ := by
  have hηL : MemLp η 2 μ⊤ := hη.continuous.memLp_of_hasCompactSupport hηc
  have hAηL : MemLp (gaugeFixedAdjoint x η) 2 μ⊤ :=
    (continuous_gaugeFixedAdjoint hx hη).memLp_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint hηc)
  -- Express both integrals as continuous `L²` inner products on `H¹(ℂ)⁴`.
  have hLHS (v : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
      ∫ z, ⟪sobolevGaugeFixedOperator a v z, η z⟫ =
        ⟪sobolevGaugeFixedOperator a v, hηL.toLp η⟫ := by
    rw [L2.inner_toLp]
    exact congrArg (fun ν ↦ ∫ z, ⟪sobolevGaugeFixedOperator a v z, η z⟫ ∂ν)
      (Measure.restrict_coe_opens_top (volume : Measure ℂ)).symm
  have hRHS (v : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
      ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (v j) z), gaugeFixedAdjoint x η z⟫ =
        ⟪sobolevFieldValueL v, hAηL.toLp (gaugeFixedAdjoint x η)⟫ := by
    rw [L2.inner_toLp, congrArg (fun ν ↦ ∫ z, ⟪sobolevFieldValueL v z, gaugeFixedAdjoint x η z⟫ ∂ν)
      (Measure.restrict_coe_opens_top (volume : Measure ℂ))]
    refine integral_congr_ae ?_
    filter_upwards [ae_mono (Measure.restrict_coe_opens_top volume).ge
      (sobolevFieldValueL_apply_ae v)] with z hz
    rw [hz]
  rw [hLHS, hRHS]
  -- Both sides are continuous in `v` and agree on the dense set of test fields.
  refine (DenseRange.piMap fun _ : Fin 4 ↦
    W1p.denseRange_ofTestFunctionₗ_top (mu := volume) (p := 2) (by norm_num)).induction_on
      (p := fun v ↦ ⟪sobolevGaugeFixedOperator a v, hηL.toLp η⟫ =
        ⟪sobolevFieldValueL v, hAηL.toLp (gaugeFixedAdjoint x η)⟫) y
      (isClosed_eq ((sobolevGaugeFixedOperator a).continuous.inner continuous_const)
        (sobolevFieldValueL.continuous.inner continuous_const)) fun φ ↦ ?_
  rw [← hLHS, ← hRHS]
  set Y : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ WithLp.toLp 2 fun j ↦ φ j z
  have hY : ContDiff ℝ 1 Y := ((contDiff_piLp 2).2 fun j ↦ (φ j).contDiff).of_le (by simp)
  have hval (j : Fin 4) : W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) =ᵐ[μ⊤] fun z ↦ Y z j :=
    W1p.value_ofTestFunctionₗ_ae (φ j)
  have hop : (sobolevGaugeFixedOperator a fun j ↦
        W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) =ᵐ[volume] gaugeFixedOperator x Y :=
    ae_mono (Measure.restrict_coe_opens_top volume).ge
      (sobolevGaugeFixedOperator_ae_eq_gaugeFixedOperator hax hY hval)
  have hval' : ∀ᵐ z ∂volume, ∀ j : Fin 4,
      W1p.value (W1p.ofTestFunctionₗ volume ⊤ 2 (φ j)) z = φ j z :=
    ae_all_iff.2 fun j ↦ ae_mono (Measure.restrict_coe_opens_top volume).ge (hval j)
  calc ∫ z, ⟪sobolevGaugeFixedOperator a
          (Pi.map (fun _ ↦ ⇑(W1p.ofTestFunctionₗ volume ⊤ 2)) φ) z, η z⟫
      = ∫ z, ⟪gaugeFixedOperator x Y z, η z⟫ :=
        integral_congr_ae (hop.mono fun z hz ↦ congrArg (⟪·, η z⟫) hz)
    _ = ∫ z, ⟪Y z, gaugeFixedAdjoint x η z⟫ :=
        integral_inner_gaugeFixedOperator hx hY hη (.inr hηc)
    _ = ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value
          (Pi.map (fun _ ↦ ⇑(W1p.ofTestFunctionₗ volume ⊤ 2)) φ j) z),
          gaugeFixedAdjoint x η z⟫ :=
        integral_congr_ae (hval'.mono fun z hz ↦ by
          simp only [Y, Pi.map_apply]; congr 1; ext j; exact (hz j).symm)

/-- **Weak characterization of `sobolevGaugeFixedOperator a`.** At a continuous field `x` with
`L∞` class `a`, an element `y ∈ H¹(ℂ)⁴` satisfies `sobolevGaugeFixedOperator a y = f` in `L²` if
and only if `y` is a weak solution of `L_x y = f` against all smooth compactly supported test
fields. -/
theorem sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq
    (hx : Continuous x) (hax : a =ᵐ[μ⊤] x) (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2)
    (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
    sobolevGaugeFixedOperator a y = f ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint x η z⟫ =
          ∫ z, ⟪f z, η z⟫ := by
  constructor
  · rintro rfl η hη hηc
    exact (integral_inner_sobolevGaugeFixedOperator hx hax y (hη.of_le (by simp)) hηc).symm
  · intro hweak
    have hloc₁ : LocallyIntegrableOn (sobolevGaugeFixedOperator a y : ℂ → _)
        ((⊤ : Opens ℂ) : Set ℂ) volume :=
      locallyIntegrableOn_of_locallyIntegrable_restrict
        ((Lp.memLp (sobolevGaugeFixedOperator a y)).locallyIntegrable one_le_two)
    have hloc₂ : LocallyIntegrableOn (f : ℂ → _) ((⊤ : Opens ℂ) : Set ℂ) volume :=
      locallyIntegrableOn_of_locallyIntegrable_restrict
        ((Lp.memLp f).locallyIntegrable one_le_two)
    have hae : (sobolevGaugeFixedOperator a y : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume] f := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using
        ae_eq_of_forall_integral_inner_eq (Ω := (⊤ : Opens ℂ)) hloc₁ hloc₂ fun φ ↦ by
          have h := hweak φ φ.contDiff φ.hasCompactSupport
          rw [← integral_inner_sobolevGaugeFixedOperator hx hax y
            (φ.contDiff.of_le (by simp)) φ.hasCompactSupport] at h
          simpa only [real_inner_comm] using h
    exact Lp.ext (ae_mono (Measure.restrict_coe_opens_top volume).le hae)

/-- **Weak characterization of the kernel of `sobolevGaugeFixedOperator a`.** At a continuous field
`x` with `L∞` class `a`, an element `y ∈ H¹(ℂ)⁴` lies in the kernel of
`sobolevGaugeFixedOperator a` if and only if its value is orthogonal to `L_x* η` for every smooth
compactly supported test field `η`. -/
theorem mem_ker_sobolevGaugeFixedOperator_iff (hx : Continuous x) (hax : a =ᵐ[μ⊤] x)
    (y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    y ∈ (sobolevGaugeFixedOperator a).ker ↔
      ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ ∞ η → HasCompactSupport η →
        ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y j) z), gaugeFixedAdjoint x η z⟫ = 0 := by
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq hx hax y 0]
  refine forall₃_congr fun η _ _ ↦ ?_
  have hzero : ∫ z, ⟪(0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) z, η z⟫ = 0 := by
    have hz : ∀ᵐ z ∂volume, (0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) z = 0 :=
      ae_mono (Measure.restrict_coe_opens_top volume).ge (Lp.coeFn_zero _ 2 μ⊤)
    rw [integral_congr_ae (hz.mono fun z h ↦ by rw [h, inner_zero_left]), integral_zero]
  rw [hzero]

/-! ### Bounded `L²`-orthogonal right inverse, surjectivity, and vanishing cokernel -/

/-- **Uniqueness of `L²`-orthogonal preimages.** For any `L∞` coefficient `a`, two elements of
`H¹(ℂ)⁴` with the same image under `sobolevGaugeFixedOperator a` that are both `L²`-orthogonal to
its kernel are equal. -/
theorem eq_of_sobolevGaugeFixedOperator_eq_of_sum_inner_value_eq_zero
    (a : Lp (EuclideanSpace ℝ (Fin 4)) ∞ μ⊤)
    {y₁ y₂ : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2}
    (heq : sobolevGaugeFixedOperator a y₁ = sobolevGaugeFixedOperator a y₂)
    (hy₁ : ∀ u ∈ (sobolevGaugeFixedOperator a).ker,
      ∑ j : Fin 4, ⟪W1p.value (y₁ j), W1p.value (u j)⟫ = 0)
    (hy₂ : ∀ u ∈ (sobolevGaugeFixedOperator a).ker,
      ∑ j : Fin 4, ⟪W1p.value (y₂ j), W1p.value (u j)⟫ = 0) :
    y₁ = y₂ := by
  have hker : y₁ - y₂ ∈ (sobolevGaugeFixedOperator a).ker := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub, heq, sub_self]
  have hnorm : ∑ j : Fin 4, ‖W1p.value ((y₁ - y₂) j)‖ ^ 2 = 0 := by
    have h₁ := hy₁ (y₁ - y₂) hker
    have h₂ := hy₂ (y₁ - y₂) hker
    calc ∑ j : Fin 4, ‖W1p.value ((y₁ - y₂) j)‖ ^ 2
        = ∑ j : Fin 4, ⟪W1p.value ((y₁ - y₂) j), W1p.value ((y₁ - y₂) j)⟫ := by
          simp_rw [real_inner_self_eq_norm_sq]
      _ = (∑ j : Fin 4, ⟪W1p.value (y₁ j), W1p.value ((y₁ - y₂) j)⟫) -
            ∑ j : Fin 4, ⟪W1p.value (y₂ j), W1p.value ((y₁ - y₂) j)⟫ := by
          simp only [Pi.sub_apply, W1p.value_sub, inner_sub_left, Finset.sum_sub_distrib]
      _ = 0 := by rw [h₁, h₂, sub_self]
  have hzero (j : Fin 4) : ‖W1p.value ((y₁ - y₂) j)‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).1 hnorm j (Finset.mem_univ j)
  refine sub_eq_zero.1 (funext fun j ↦ W1p.ext_value ?_)
  simpa only [Pi.zero_apply, W1p.value_zero, sq_eq_zero_iff, norm_eq_zero] using hzero j

/-- **Bounded `L²`-orthogonal right inverse `L² → H¹`.** At a `C¹` plane vortex `x` with
`|α| → 1` at infinity and `L∞` class `a`, there is a continuous linear right inverse
`Q : L²(ℂ; ℝ⁴) → H¹(ℂ)⁴` of `sobolevGaugeFixedOperator a` whose outputs are `L²`-orthogonal to
the kernel of `sobolevGaugeFixedOperator a`. By
`TauCeti.Vortex.eq_of_sobolevGaugeFixedOperator_eq_of_sum_inner_value_eq_zero`, this operator `Q`
is unique. -/
theorem exists_continuousLinearMap_sobolevGaugeFixedOperator_comp_eq_id (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2),
      (sobolevGaugeFixedOperator a).comp Q = ContinuousLinearMap.id ℝ _ ∧
        ∀ f, ∀ u ∈ (sobolevGaugeFixedOperator a).ker,
          ∑ j : Fin 4, ⟪W1p.value (Q f j), W1p.value (u j)⟫ = 0 := by
  have hM (z : ℂ) : ‖x z‖ ≤ ‖a‖ :=
    Lp.norm_le_norm_top_of_ae_eq_of_continuousAt hax hx.continuous.continuousAt
  -- Transport the `L²` weak right inverse from `volume` to `μ⊤`, then lift to `H¹(ℂ)⁴`.
  obtain ⟨Q₀, hQ₀weak, hQ₀orth⟩ :=
    exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq (μ := volume) hx hsol hlim
  set e := castLpₗᵢ (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 4)) (p := 2)
    (Measure.restrict_coe_opens_top (volume : Measure ℂ))
  set Q₁ : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ :=
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (Q₀.comp e.toContinuousLinearEquiv.toContinuousLinearMap)
  have hQ₁_apply (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (z : ℂ) : Q₁ f z = Q₀ (e f) z := by
    simp only [Q₁, e, ContinuousLinearMap.comp_apply,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, ContinuousLinearEquiv.coe_coe,
      castLpₗᵢ_symm, coeFn_castLpₗᵢ]
  have hQ₁weak (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) (η : ℂ → EuclideanSpace ℝ (Fin 4))
      (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
      ∫ z, ⟪Q₁ f z, gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪f z, η z⟫ := by
    simp_rw [hQ₁_apply]
    rw [hQ₀weak (e f) η hη hηc]
    exact integral_congr_ae (.of_forall fun z ↦ by simp only [e, coeFn_castLpₗᵢ])
  obtain ⟨Q, hQ⟩ := exists_lift_sobolevFieldValueL Q₁ fun f ↦
    mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq
      hx.continuous.aestronglyMeasurable (.of_forall hM)
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (Q₁ f))
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp f)
      fun η hη hηc ↦ hQ₁weak f η (hη.of_le (by simp)) hηc
  have hQ_apply (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) : sobolevFieldValueL (Q f) = Q₁ f :=
    DFunLike.congr_fun hQ f
  refine ⟨Q, ?_, fun f u hu ↦ ?_⟩
  · -- Verify `L_a ∘ Q = id` via the weak formulation.
    ext1 f
    refine (sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq
      hx.continuous hax (Q f) f).2 fun η hη hηc ↦ ?_
    rw [← hQ₁weak f η (hη.of_le (by simp)) hηc]
    have hae : (fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (Q f j) z) =ᵐ[volume] Q₁ f :=
      ae_mono (Measure.restrict_coe_opens_top volume).ge
        ((sobolevFieldValueL_apply_ae (Q f)).symm.trans (Lp.ext_iff.1 (hQ_apply f)))
    exact integral_congr_ae (hae.mono fun z hz ↦ by simp only [hz])
  · -- Verify `L²`-orthogonality to `ker L_a` from `L²`-orthogonality of `Q₀`.
    rw [← inner_sobolevFieldValueL, hQ_apply, L2.inner_def,
      congrArg (fun ν ↦ ∫ z, ⟪Q₁ f z, sobolevFieldValueL u z⟫ ∂ν)
        (Measure.restrict_coe_opens_top (volume : Measure ℂ))]
    have hu_weak (η : ℂ → EuclideanSpace ℝ (Fin 4)) (hη : ContDiff ℝ 2 η)
        (hηc : HasCompactSupport η) :
        ∫ z, ⟪(e (sobolevFieldValueL u)) z, gaugeFixedAdjoint x η z⟫ = 0 := by
      have hae : (e (sobolevFieldValueL u) : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume]
          fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (u j) z := by
        filter_upwards [ae_mono (Measure.restrict_coe_opens_top volume).ge
          (sobolevFieldValueL_apply_ae u)] with z hz
        simpa only [e, coeFn_castLpₗᵢ] using hz
      have hEq : ∫ z, ⟪(e (sobolevFieldValueL u)) z, gaugeFixedAdjoint x η z⟫ =
          ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (u j) z), gaugeFixedAdjoint x η z⟫ :=
        integral_congr_ae (hae.mono fun z hz ↦ congrArg (⟪·, gaugeFixedAdjoint x η z⟫) hz)
      have h0 : sobolevGaugeFixedOperator a u = 0 := by simpa using LinearMap.mem_ker.1 hu
      rw [hEq, ← integral_inner_sobolevGaugeFixedOperator hx.continuous hax u
        (hη.of_le one_le_two) hηc, h0]
      have hz : ∀ᵐ z ∂volume, (0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) z = 0 :=
        ae_mono (Measure.restrict_coe_opens_top volume).ge (Lp.coeFn_zero _ 2 μ⊤)
      rw [integral_congr_ae (hz.mono fun z h ↦ by rw [h, inner_zero_left]), integral_zero]
    refine (integral_congr_ae (.of_forall fun z ↦ ?_)).trans
      (hQ₀orth (e f) (e (sobolevFieldValueL u)) hu_weak)
    rw [hQ₁_apply]
    simp only [e, coeFn_castLpₗᵢ]

/-- **Surjectivity of `L_x : H¹ → L²` at a plane vortex.** At a `C¹` plane vortex `x` with
`|α| → 1` at infinity and `L∞` class `a`, the Sobolev realization `sobolevGaugeFixedOperator a`
is surjective; in particular its cokernel vanishes. -/
theorem surjective_sobolevGaugeFixedOperator (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    Function.Surjective (sobolevGaugeFixedOperator a) := by
  obtain ⟨Q, hQ, -⟩ :=
    exists_continuousLinearMap_sobolevGaugeFixedOperator_comp_eq_id hx hsol hlim hax
  exact fun f ↦ ⟨Q f, by simpa using DFunLike.congr_fun hQ f⟩

/-- **The range of `L_x : H¹ → L²` is the whole space** at a `C¹` plane vortex with `|α| → 1` at
infinity and `L∞` class `a`. -/
theorem range_sobolevGaugeFixedOperator_eq_top (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).range = ⊤ :=
  LinearMap.range_eq_top.2 (surjective_sobolevGaugeFixedOperator hx hsol hlim hax)

/-! ### Fredholm property -/

/-- **Fredholm property of `L_x : H¹ → L²` at a `C¹` vortex.** At a `C¹` plane vortex `x` with
`|α| → 1` and `∇₁ α → 0` at infinity and with `L∞` class `a`, the Sobolev realization
`sobolevGaugeFixedOperator a` is a Fredholm operator. -/
theorem isFredholm_sobolevGaugeFixedOperator (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0))
    (hax : a =ᵐ[μ⊤] x) :
    ContinuousLinearMap.IsFredholm (sobolevGaugeFixedOperator a) := by
  have hker := finiteDimensional_ker_sobolevGaugeFixedOperator hx hsol hlim hcov hax
  have hsub : Subsingleton (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ ⧸
      (sobolevGaugeFixedOperator a).range) :=
    Submodule.Quotient.subsingleton_iff.2
      (range_sobolevGaugeFixedOperator_eq_top hx hsol hlim hax)
  exact .of_finite_ker_coker (sobolevGaugeFixedOperator a) hker inferInstance

/-- **Fredholm property of `L_x : H¹ → L²` at a `C²` vortex.** At a `C²` plane vortex `x` with
`|α| → 1` at infinity and with `L∞` class `a`, the exponential decay of `d_a α` gives `∇₁ α → 0`
at infinity automatically, so `sobolevGaugeFixedOperator a` is a Fredholm operator. -/
theorem isFredholm_sobolevGaugeFixedOperator_of_contDiff (hx : ContDiff ℝ 2 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    ContinuousLinearMap.IsFredholm (sobolevGaugeFixedOperator a) := by
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i := contDiff_euclidean.1 hx i
  obtain ⟨K, hK⟩ := exists_norm_covariantDerivative_le_mul_exp (hxi 0).continuous (hxi 2) (hxi 3)
    hsol hlim (c := 1 / 4) (by norm_num)
  have hcov : Tendsto (fun z ↦ covariantDerivative x z 1) (cocompact ℂ) (𝓝 0) := by
    have hexp : Tendsto (fun z : ℂ ↦ K * Real.exp (-(1 / 4 * ‖z‖))) (cocompact ℂ) (𝓝 0) := by
      simpa only [Function.comp_apply, mul_zero] using tendsto_const_nhds.mul
        (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
          ((tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 1 / 4)).2
            tendsto_norm_cocompact_atTop)))
    exact squeeze_zero_norm (fun z ↦ by simpa only [norm_one, mul_one] using hK z 1) hexp
  exact isFredholm_sobolevGaugeFixedOperator (hx.of_le one_le_two) hsol hlim hcov hax

/-! ### Identification of the `H¹` kernel with the classical kernel and principal parts -/

/-- Each `H¹` kernel element of `L_x` at a smooth field with bounded derivatives through order `3`
agrees almost everywhere with a unique `C²` classical kernel element. -/
private theorem exists_mem_gaugeFixedKernel_ae_eq (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) (y : (sobolevGaugeFixedOperator a).ker) :
    ∃ Y : gaugeFixedKernel x,
      ∀ j : Fin 4, W1p.value (y.1 j) =ᵐ[μ⊤] fun z ↦ Y.1 z j := by
  have hweak := (mem_ker_sobolevGaugeFixedOperator_iff hx.continuous hax y.1).1 y.2
  have hY₀L : MemLp (fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y.1 j) z) 2 volume := by
    have hmem : MemLp (sobolevFieldValueL y.1 : ℂ → EuclideanSpace ℝ (Fin 4)) 2 volume := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (sobolevFieldValueL y.1)
    exact hmem.ae_eq (ae_mono (Measure.restrict_coe_opens_top volume).ge
      (sobolevFieldValueL_apply_ae y.1))
  -- Bootstrap the weak kernel element to `H⁴`, then apply Sobolev embedding `H⁴(ℂ) ↪ C²(ℂ)`.
  have h4 : (fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y.1 j) z) ∈ sobolevFields 4 := by
    have h31 : ((3 : ℕ) : ℝ) + 1 = 4 := by norm_num
    rw [← h31]
    exact mem_sobolevFields_natCast_add_one_of_integral_inner_gaugeFixedAdjoint_eq 3 hx hbound
      hY₀L (zero_mem (sobolevFields 3)) fun η hη hηc ↦ by simpa using hweak η hη hηc
  have hs : (finrank ℝ ℂ : ℝ) + 2 * (2 : ℕ) < 2 * (4 : ℝ) := by
    rw [Complex.finrank_real_complex]
    norm_num
  choose g hg hgy using fun j : Fin 4 ↦
    TemperedDistribution.exists_contDiff_ae_eq_of_mem_realSobolevFunctions (k := 2) hs
      (mem_sobolevFields.1 h4 j)
  set Y : ℂ → EuclideanSpace ℝ (Fin 4) := fun z ↦ WithLp.toLp 2 fun j ↦ g j z
  have hYcd : ContDiff ℝ 2 Y := contDiff_euclidean.2 fun j ↦ by simpa [Y] using hg j
  have hae : (fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y.1 j) z) =ᵐ[volume] Y := by
    filter_upwards [ae_all_iff.2 hgy] with z hz
    ext j
    exact hz j
  have hYker : ∀ z, gaugeFixedOperator x Y z = 0 :=
    (forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) hx.continuous
      (hYcd.of_le one_le_two) continuous_const).1 fun η hη hηc ↦ by
        have hEq : ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y.1 j) z),
            gaugeFixedAdjoint x η z⟫ = ∫ z, ⟪Y z, gaugeFixedAdjoint x η z⟫ :=
          integral_congr_ae (hae.mono fun z hz ↦ congrArg (⟪·, gaugeFixedAdjoint x η z⟫) hz)
        rw [← hEq, hweak η hη hηc]
        simp only [inner_zero_left, integral_zero]
  refine ⟨⟨Y, mem_gaugeFixedKernel.2 ⟨hYcd, hY₀L.ae_eq hae, hYker⟩⟩, fun j ↦ ?_⟩
  exact ae_mono (Measure.restrict_coe_opens_top volume).le (hgy j)

/-- Each `C²` classical kernel element of `L_x` at a continuous field with `L∞` class `a` lifts to
an `H¹` kernel element of `sobolevGaugeFixedOperator a`. -/
private theorem exists_mem_ker_sobolevGaugeFixedOperator_ae_eq (hx : Continuous x)
    (hax : a =ᵐ[μ⊤] x) (Y : gaugeFixedKernel x) :
    ∃ y : (sobolevGaugeFixedOperator a).ker,
      ∀ j : Fin 4, W1p.value (y.1 j) =ᵐ[μ⊤] fun z ↦ Y.1 z j := by
  obtain ⟨hYcd, hYL, hYker⟩ := mem_gaugeFixedKernel.1 Y.2
  have hM (z : ℂ) : ‖x z‖ ≤ ‖a‖ :=
    Lp.norm_le_norm_top_of_ae_eq_of_continuousAt hax hx.continuousAt
  have hYweak := (forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) hx
    (hYcd.of_le one_le_two) continuous_const).2 hYker
  have hY1 : Y.1 ∈ sobolevFields 1 :=
    mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq hx.aestronglyMeasurable
      (.of_forall hM) hYL MemLp.zero hYweak
  obtain ⟨y, hy⟩ := exists_sobolevField_value_ae_eq_of_mem_sobolevFields hY1
  have hyker : y ∈ (sobolevGaugeFixedOperator a).ker := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    refine Lp.ext ((sobolevGaugeFixedOperator_ae_eq_gaugeFixedOperator hax
      (hYcd.of_le one_le_two) hy).trans ?_)
    filter_upwards [Lp.coeFn_zero (EuclideanSpace ℝ (Fin 4)) 2 μ⊤] with z hz
    rw [hz, hYker z, Pi.zero_apply]
  exact ⟨⟨y, hyker⟩, hy⟩

/-- Two elements of `gaugeFixedKernel x` agreeing almost everywhere coordinatewise are equal. -/
private theorem gaugeFixedKernel_eq_of_ae_eq {Y₁ Y₂ : gaugeFixedKernel x}
    (h : ∀ j : Fin 4, (fun z ↦ Y₁.1 z j) =ᵐ[μ⊤] fun z ↦ Y₂.1 z j) : Y₁ = Y₂ := by
  refine Subtype.ext (((mem_gaugeFixedKernel.1 Y₁.2).1.continuous.ae_eq_iff_eq volume
    (mem_gaugeFixedKernel.1 Y₂.2).1.continuous).1 ?_)
  filter_upwards [ae_all_iff.2 fun j ↦
    ae_mono (Measure.restrict_coe_opens_top volume).ge (h j)] with z hz
  ext j
  exact hz j

/-- **Canonical identification of the `H¹` and classical `C²` kernels of `L_x`.** At a smooth field
`x` whose coordinates have bounded derivatives through order `3` and with `L∞` class `a`, every
`H¹` kernel element of `sobolevGaugeFixedOperator a` agrees almost everywhere with a unique `C²`
classical kernel element in `gaugeFixedKernel x`, giving a real-linear equivalence
`(sobolevGaugeFixedOperator a).ker ≃ₗ[ℝ] gaugeFixedKernel x`. -/
def kerSobolevGaugeFixedOperatorEquiv (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).ker ≃ₗ[ℝ] gaugeFixedKernel x where
  toFun y := (exists_mem_gaugeFixedKernel_ae_eq hx hbound hax y).choose
  invFun Y := (exists_mem_ker_sobolevGaugeFixedOperator_ae_eq hx.continuous hax Y).choose
  map_add' y₁ y₂ := by
    have h₁ := (exists_mem_gaugeFixedKernel_ae_eq hx hbound hax y₁).choose_spec
    have h₂ := (exists_mem_gaugeFixedKernel_ae_eq hx hbound hax y₂).choose_spec
    have h₁₂ := (exists_mem_gaugeFixedKernel_ae_eq hx hbound hax (y₁ + y₂)).choose_spec
    refine gaugeFixedKernel_eq_of_ae_eq fun j ↦ ?_
    filter_upwards [h₁₂ j, h₁ j, h₂ j, W1p.value_add_ae (y₁.1 j) (y₂.1 j)] with z hz hz₁ hz₂ hadd
    rw [← hz, Submodule.coe_add, Pi.add_apply, hadd, Pi.add_apply, hz₁, hz₂]
    rfl
  map_smul' c y := by
    have hy := (exists_mem_gaugeFixedKernel_ae_eq hx hbound hax y).choose_spec
    have hcy := (exists_mem_gaugeFixedKernel_ae_eq hx hbound hax (c • y)).choose_spec
    refine gaugeFixedKernel_eq_of_ae_eq fun j ↦ ?_
    filter_upwards [hcy j, hy j, W1p.value_smul_ae c (y.1 j)] with z hzc hz hsmul
    rw [← hzc, Submodule.coe_smul, Pi.smul_apply, hsmul, Pi.smul_apply, hz]
    rfl
  left_inv y := by
    have hy := (exists_mem_gaugeFixedKernel_ae_eq hx hbound hax y).choose_spec
    have hinv := (exists_mem_ker_sobolevGaugeFixedOperator_ae_eq hx.continuous hax
      (exists_mem_gaugeFixedKernel_ae_eq hx hbound hax y).choose).choose_spec
    refine Subtype.ext (funext fun j ↦ W1p.ext_value (Lp.ext ?_))
    exact (hinv j).trans (hy j).symm
  right_inv Y := by
    have hinv := (exists_mem_ker_sobolevGaugeFixedOperator_ae_eq hx.continuous hax Y).choose_spec
    have hy := (exists_mem_gaugeFixedKernel_ae_eq hx hbound hax
      (exists_mem_ker_sobolevGaugeFixedOperator_ae_eq hx.continuous hax Y).choose).choose_spec
    exact gaugeFixedKernel_eq_of_ae_eq fun j ↦ (hy j).symm.trans (hinv j)

/-- The image of an `H¹` kernel element under `kerSobolevGaugeFixedOperatorEquiv` agrees almost
everywhere with its value coordinates. -/
theorem kerSobolevGaugeFixedOperatorEquiv_apply_ae (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) (y : (sobolevGaugeFixedOperator a).ker) (j : Fin 4) :
    W1p.value (y.1 j) =ᵐ[μ⊤] fun z ↦ (kerSobolevGaugeFixedOperatorEquiv hx hbound hax y).1 z j :=
  (exists_mem_gaugeFixedKernel_ae_eq hx hbound hax y).choose_spec j

/-- The preimage of a classical kernel element under `kerSobolevGaugeFixedOperatorEquiv` has value
coordinates agreeing almost everywhere with that classical element. -/
theorem kerSobolevGaugeFixedOperatorEquiv_symm_value_ae (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) (Y : gaugeFixedKernel x) (j : Fin 4) :
    W1p.value (((kerSobolevGaugeFixedOperatorEquiv hx hbound hax).symm Y).1 j) =ᵐ[μ⊤]
      fun z ↦ Y.1 z j :=
  (exists_mem_ker_sobolevGaugeFixedOperator_ae_eq hx.continuous hax Y).choose_spec j

/-- Characteristic property of `kerSobolevGaugeFixedOperatorEquiv`: an `H¹` kernel element `y` maps
to `Y ∈ gaugeFixedKernel x` if and only if each coordinate value of `y` agrees almost everywhere
with the corresponding coordinate of `Y`. -/
theorem kerSobolevGaugeFixedOperatorEquiv_eq_iff (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) (y : (sobolevGaugeFixedOperator a).ker) (Y : gaugeFixedKernel x) :
    kerSobolevGaugeFixedOperatorEquiv hx hbound hax y = Y ↔
      ∀ j : Fin 4, W1p.value (y.1 j) =ᵐ[μ⊤] fun z ↦ Y.1 z j :=
  ⟨fun h j ↦ h ▸ kerSobolevGaugeFixedOperatorEquiv_apply_ae hx hbound hax y j,
    fun h ↦ gaugeFixedKernel_eq_of_ae_eq fun j ↦
      (kerSobolevGaugeFixedOperatorEquiv_apply_ae hx hbound hax y j).symm.trans (h j)⟩

/-- **Exact real dimension `2 |D|` of the `H¹` kernel of `L_x`.** At a smooth field `x` with
bounded derivatives through order `3`, vanishing holomorphicity rows `∂bar_a α = 0`, `|α|² → 1`
at infinity, zero divisor `D`, and `L∞` class `a`, the kernel of `sobolevGaugeFixedOperator a`
has real dimension `2 |D|`. -/
theorem finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_card (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hax : a =ᵐ[μ⊤] x) :
    finrank ℝ (sobolevGaugeFixedOperator a).ker = 2 * Multiset.card D := by
  rw [(kerSobolevGaugeFixedOperatorEquiv hx hbound hax).finrank_eq,
    finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD]

/-- **Exact real dimension `2 m` of the `H¹` kernel of `L_x` at a framed field.** At a smooth field
`x` with bounded derivatives through order `3`, vanishing holomorphicity rows, the degree-`m` end
framing `α(z) (z / |z|)⁻ᵐ → 1`, and `L∞` class `a`, the kernel of `sobolevGaugeFixedOperator a`
has real dimension `2 m`. -/
theorem finrank_ker_sobolevGaugeFixedOperator_eq_two_mul {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    finrank ℝ (sobolevGaugeFixedOperator a).ker = 2 * m := by
  rw [(kerSobolevGaugeFixedOperatorEquiv hx hbound hax).finrank_eq,
    finrank_gaugeFixedKernel_eq_two_mul hx hhol hframe]

/-- **Identification of the `H¹` kernel with the principal-part space `D → ℂ`.** At a smooth field
`x` with bounded derivatives through order `3`, vanishing holomorphicity rows, `|α|² → 1` at
infinity, zero divisor `D`, and `L∞` class `a`, for any `C²` integrating factor `ν` solving
`∂bar ν = (b₂ - i b₁) / 2` and principal-part decomposition `hdec` on `gaugeFixedKernel x`,
composing the canonical kernel equivalence with `principalPartMap` yields a real-linear bijection
from `(sobolevGaugeFixedOperator a).ker` onto `Multiset.ToType D → ℂ`, the real tangent space of
the symmetric divisor space `Sym^|D| ℂ`. -/
theorem bijective_principalPartMap_comp_kerSobolevGaugeFixedOperatorEquiv (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    {ν : ℂ → ℂ} (hν : ContDiff ℝ 2 ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hdec : ∀ y ∈ gaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ,
      Differentiable ℂ H ∧ ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w)
    (hax : a =ᵐ[μ⊤] x) :
    Function.Bijective
      ((principalPartMap hD hν.continuous hdec).comp
        (kerSobolevGaugeFixedOperatorEquiv hx hbound hax).toLinearMap) := by
  have hxi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ x w i :=
    (contDiff_euclidean.1 hx i).of_le (by simp)
  have : FiniteDimensional ℝ (gaugeFixedKernel x) :=
    finiteDimensional_of_gaugeFixedOperator_eq_zero (μ := volume)
      (hx.of_le (by simp)) hhol hlim hD fun _ ↦ mem_gaugeFixedKernel.1
  have hinj_pp : Function.Injective (principalPartMap hD hν.continuous hdec) := by
    refine principalPartMap_injective (k := 2) one_le_two (hxi 0) (hxi 1)
      ((hxi 2).differentiable (by norm_num)) ((hxi 3).differentiable (by norm_num)) hhol hD hν
      hνeq (fun y hy ↦ ?_) hdec fun y hy η hη hyη ↦ ?_
    · obtain ⟨hyc, -, hker⟩ := mem_gaugeFixedKernel.1 hy
      have hyi (i : Fin 4) : ContDiff ℝ 2 fun w ↦ y w i := contDiff_euclidean.1 hyc i
      refine ⟨hyi 0, hyi 1, (hyi 2).differentiable (by norm_num),
        (hyi 3).differentiable (by norm_num), fun w ↦ ⟨?_, ?_⟩⟩
      · rw [← gaugeFixedOperator_apply_two, hker w, PiLp.zero_apply]
      · rw [← gaugeFixedOperator_apply_three, hker w, PiLp.zero_apply]
    · obtain ⟨hyc, hy₂, hker⟩ := mem_gaugeFixedKernel.1 hy
      exact eq_zero_of_gaugeFixedOperator_eq_zero_of_sectionValue_eq_mul_of_tendsto
        (hx.of_le (by simp)) hhol hlim hyc.continuous hy₂ hker hη hyη
  have hdim_pp : finrank ℝ (gaugeFixedKernel x) = finrank ℝ (Multiset.ToType D → ℂ) := by
    rw [finrank_gaugeFixedKernel_eq_two_mul_card hx hhol hlim hD,
      Module.finrank_pi_fintype, Finset.sum_const, Complex.finrank_real_complex, smul_eq_mul,
      Finset.card_univ, Multiset.card_coe, mul_comm]
  have hsurj_pp : Function.Surjective (principalPartMap hD hν.continuous hdec) := by
    have hrank := (principalPartMap hD hν.continuous hdec).finrank_range_add_finrank_ker
    rw [LinearMap.ker_eq_bot.2 hinj_pp, finrank_bot, add_zero, hdim_pp] at hrank
    exact LinearMap.range_eq_top.1 (Submodule.eq_top_of_finrank_eq hrank)
  have hbij_pp : Function.Bijective (principalPartMap hD hν.continuous hdec) := ⟨hinj_pp, hsurj_pp⟩
  exact hbij_pp.comp (kerSobolevGaugeFixedOperatorEquiv hx hbound hax).bijective

/-! ### Exact Fredholm index and degree-zero bijectivity -/

/-- **Real Fredholm index `2 |D|` of `L_x : H¹ → L²`.** At a smooth plane vortex `x` with bounded
derivatives through order `3`, `|α|² → 1` at infinity, zero divisor `D`, and `L∞` class `a`,
the Sobolev realization `sobolevGaugeFixedOperator a` has real Fredholm index `2 |D|`. -/
theorem index_sobolevGaugeFixedOperator_eq_two_mul_card (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).index = 2 * Multiset.card D := by
  rw [(sobolevGaugeFixedOperator a).index_of_surjective
      (surjective_sobolevGaugeFixedOperator (hx.of_le (by simp)) hsol hlim hax),
    finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_card hx hbound
      (fun w ↦ by simp [hsol w]) hlim hD hax]
  push_cast
  rfl

/-- **Real Fredholm index `2 m` of `L_x : H¹ → L²` at a framed vortex.** At a smooth plane vortex
`x` with bounded derivatives through order `3`, the degree-`m` end framing
`α(z) (z / |z|)⁻ᵐ → 1`, and `L∞` class `a`, the Sobolev realization `sobolevGaugeFixedOperator a`
has real Fredholm index `2 m`. -/
theorem index_sobolevGaugeFixedOperator_eq_two_mul {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).index = 2 * m := by
  rw [(sobolevGaugeFixedOperator a).index_of_surjective
      (surjective_sobolevGaugeFixedOperator (hx.of_le (by simp)) hsol
        (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hax),
    finrank_ker_sobolevGaugeFixedOperator_eq_two_mul hx hbound
      (fun w ↦ by simp [hsol w]) hframe hax]
  push_cast
  rfl

/-- Transport triviality of `gaugeFixedKernel x` back to `(sobolevGaugeFixedOperator a).ker` via
`kerSobolevGaugeFixedOperatorEquiv`. -/
private theorem ker_sobolevGaugeFixedOperator_eq_bot_of_gaugeFixedKernel_eq_bot
    (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) (hbot : gaugeFixedKernel x = ⊥) :
    (sobolevGaugeFixedOperator a).ker = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun y hy ↦ ?_
  have h0 : kerSobolevGaugeFixedOperatorEquiv hx hbound hax ⟨y, hy⟩ = 0 :=
    Subtype.ext ((Submodule.mem_bot ℝ).1 ((SetLike.ext_iff.1 hbot _).1
      (kerSobolevGaugeFixedOperatorEquiv hx hbound hax ⟨y, hy⟩).2))
  exact congrArg Subtype.val ((kerSobolevGaugeFixedOperatorEquiv hx hbound hax).injective
    (h0.trans (kerSobolevGaugeFixedOperatorEquiv hx hbound hax).map_zero.symm))

/-- **Trivial `H¹` kernel when the section has no zeros.** At a smooth field `x` with bounded
derivatives through order `3`, vanishing holomorphicity rows, `|α|² → 1` at infinity, no zeros of
`α`, and `L∞` class `a`, the kernel of `sobolevGaugeFixedOperator a` is trivial. -/
theorem ker_sobolevGaugeFixedOperator_eq_bot_of_forall_sectionValue_ne_zero (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hne : ∀ z, sectionValue x z ≠ 0) (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).ker = ⊥ :=
  ker_sobolevGaugeFixedOperator_eq_bot_of_gaugeFixedKernel_eq_bot hx hbound hax
    (gaugeFixedKernel_eq_bot_of_forall_sectionValue_ne_zero (hx.of_le (by simp)) hhol hlim hne)

/-- **Trivial `H¹` kernel in degree zero.** At a smooth field `x` with bounded derivatives through
order `3`, vanishing holomorphicity rows, `α(z) → 1` at infinity, and `L∞` class `a`, the kernel
of `sobolevGaugeFixedOperator a` is trivial. -/
theorem ker_sobolevGaugeFixedOperator_eq_bot (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (sectionValue x) (cocompact ℂ) (𝓝 1)) (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).ker = ⊥ :=
  ker_sobolevGaugeFixedOperator_eq_bot_of_gaugeFixedKernel_eq_bot hx hbound hax
    (gaugeFixedKernel_eq_bot (hx.of_le (by simp)) hhol hframe)

/-- **Bijectivity of `L_x : H¹ → L²` when the section has no zeros.** At a smooth plane vortex `x`
with bounded derivatives through order `3`, `|α|² → 1` at infinity, no zeros of `α`, and `L∞`
class `a`, `sobolevGaugeFixedOperator a` is bijective (hence a continuous linear equivalence by
`ContinuousLinearEquiv.ofBijective`). -/
theorem bijective_sobolevGaugeFixedOperator_of_forall_sectionValue_ne_zero (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hne : ∀ z, sectionValue x z ≠ 0) (hax : a =ᵐ[μ⊤] x) :
    Function.Bijective (sobolevGaugeFixedOperator a) :=
  ⟨LinearMap.ker_eq_bot.1 (ker_sobolevGaugeFixedOperator_eq_bot_of_forall_sectionValue_ne_zero
      hx hbound (fun w ↦ by simp [hsol w]) hlim hne hax),
    surjective_sobolevGaugeFixedOperator (hx.of_le (by simp)) hsol hlim hax⟩

/-- **Bijectivity of `L_x : H¹ → L²` in degree zero.** At a smooth plane vortex `x` with bounded
derivatives through order `3`, `α(z) → 1` at infinity, and `L∞` class `a`,
`sobolevGaugeFixedOperator a` is bijective. -/
theorem bijective_sobolevGaugeFixedOperator (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (sectionValue x) (cocompact ℂ) (𝓝 1)) (hax : a =ᵐ[μ⊤] x) :
    Function.Bijective (sobolevGaugeFixedOperator a) := by
  have hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1) :=
    tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow (m := 0) (by simpa using hframe)
  exact ⟨LinearMap.ker_eq_bot.1 (ker_sobolevGaugeFixedOperator_eq_bot hx hbound
      (fun w ↦ by simp [hsol w]) hframe hax),
    surjective_sobolevGaugeFixedOperator (hx.of_le (by simp)) hsol hlim hax⟩

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
    ContinuousLinearMap.IsFredholm (sobolevGaugeFixedOperator a) := by
  have hsub_s : (finrank ℝ ℂ : ℝ) + 2 * (2 : ℕ) < 2 * s := by
    rw [Complex.finrank_real_complex]
    norm_num
    linarith
  have hd : ContDiff ℝ 2 (x - referenceField ρ m) :=
    contDiff_euclidean.2 fun i ↦ TemperedDistribution.contDiff_of_mem_realSobolevFunctions hsub_s
      (mem_sobolevFields.1 (mem_framedFieldSpace.1 hmem) i)
      ((PiLp.continuous_apply 2 _ i).comp (hx.sub (contDiff_referenceField ρ m).continuous))
  have hx₂ : ContDiff ℝ 2 x := by
    simpa only [Pi.sub_apply, sub_add_cancel] using
      hd.add ((contDiff_referenceField ρ m).of_le (by simp))
  exact isFredholm_sobolevGaugeFixedOperator_of_contDiff hx₂ hsol
    (tendsto_normSq_of_mem_framedFieldSpace (by linarith) hmem hx) hax

/-- **Kernel dimension `2 m` for a field in every `A_m^k`.** At a continuous field lying in
`framedFieldSpace ρ m k` for every `k`, satisfying the holomorphicity rows `∂bar_a α = 0`, and
with `L∞` class `a`, the kernel of `sobolevGaugeFixedOperator a` has real dimension `2 m`. -/
theorem finrank_ker_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace
    (hx : Continuous x) (hmem : ∀ k : ℕ, x ∈ framedFieldSpace ρ m k)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0) (hax : a =ᵐ[μ⊤] x) :
    finrank ℝ (sobolevGaugeFixedOperator a).ker = 2 * m :=
  finrank_ker_sobolevGaugeFixedOperator_eq_two_mul
    (contDiff_of_forall_mem_framedFieldSpace hx hmem)
    (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2)))
    hhol (tendsto_sectionValue_mul_inv_pow one_lt_two (by exact_mod_cast hmem 2) hx) hax

/-- **Real Fredholm index `2 m` for a vortex in every `A_m^k`.** At a continuous plane vortex
lying in `framedFieldSpace ρ m k` for every `k` and with `L∞` class `a`,
`sobolevGaugeFixedOperator a` has real Fredholm index `2 m`. -/
theorem index_sobolevGaugeFixedOperator_of_forall_mem_framedFieldSpace
    (hx : Continuous x) (hmem : ∀ k : ℕ, x ∈ framedFieldSpace ρ m k)
    (hsol : ∀ z, equation x z = 0) (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).index = 2 * m :=
  index_sobolevGaugeFixedOperator_eq_two_mul
    (contDiff_of_forall_mem_framedFieldSpace hx hmem)
    (fun i n _ ↦ exists_norm_iteratedFDeriv_le_of_mem_framedFieldSpace hx i n (hmem (n + 2)))
    hsol (tendsto_sectionValue_mul_inv_pow one_lt_two (by exact_mod_cast hmem 2) hx) hax

end FramedFieldSpace

end TauCeti.Vortex
