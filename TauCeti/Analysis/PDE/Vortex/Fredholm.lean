/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.PDE.Vortex.EllipticRegularity
public import TauCeti.Analysis.PDE.Vortex.FieldSpace
public import TauCeti.Analysis.PDE.Vortex.PrincipalPart
public import TauCeti.Analysis.PDE.Vortex.SobolevRealization
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Fredholm.Criteria
import TauCeti.Analysis.PDE.Vortex.DerivativeDecay
import TauCeti.Analysis.PDE.Vortex.Kernel.PrincipalPart
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

constructed in `TauCeti.Analysis.PDE.Vortex.SobolevRealization`. At a `C¹` vortex with `|α| → 1`
and `∇₁ α → 0` at infinity, its kernel is finite dimensional and its range is closed
(`TauCeti.Vortex.finiteDimensional_ker_sobolevGaugeFixedOperator`,
`TauCeti.Vortex.isClosed_range_sobolevGaugeFixedOperator`). This file establishes the weak
formulation, surjectivity, bounded `L²`-orthogonal right inverse, Fredholm property, kernel
identification with the principal-part space `ℂ^|D|`, and exact real index `2 |D|` (and `2 m` in the
framed degree-`m` case) of this Sobolev realization.

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
  (`TauCeti.Vortex.sobolevGaugeFixedOperator_surjective`,
  `TauCeti.Vortex.range_sobolevGaugeFixedOperator_eq_top`) and its cokernel vanishes. Applying the
  closed graph theorem produces a bounded right inverse `Q : L²(ℂ; ℝ⁴) → H¹(ℂ)⁴` whose values are
  `L²`-orthogonal to the kernel
  (`TauCeti.Vortex.exists_continuousLinearMap_sobolevGaugeFixedOperator_comp_eq_id`); such a
  preimage is unique for any `a`
  (`TauCeti.Vortex.eq_of_sobolevGaugeFixedOperator_eq_of_sum_inner_value_eq_zero`).
* **Fredholm property.** Combining vanishing cokernel with the finite-dimensional kernel from
  `TauCeti.Analysis.PDE.Vortex.SobolevRealization` via
  `ContinuousLinearMap.IsFredholm.of_surjective` yields
  `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator` (for `C¹` vortices with `∇₁ α → 0`),
  `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_of_contDiff` (for `C²` vortices, where
  exponential decay of `d_a α` in `TauCeti.Analysis.PDE.Vortex.DerivativeDecay` discharges
  `∇₁ α → 0` automatically), and
  `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_of_mem_framedFieldSpace` (on `A_m^s` for
  `s > 3`).
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
  degree `0`). At a continuous plane vortex lying in `A_m^k` for every `k` (see
  `TauCeti.Vortex.exists_framedGaugeGroup_smul_mem_framedFieldSpace`), the index `2 m` without
  assuming boundedness separately is proved in `TauCeti.Analysis.PDE.Vortex.Index`.

## Main declarations

* `TauCeti.Vortex.integral_inner_sobolevGaugeFixedOperator`,
  `TauCeti.Vortex.sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq`,
  `TauCeti.Vortex.sobolevGaugeFixedOperator_eq_iff_forall_integral_inner_gaugeFixedAdjoint_eq`,
  `TauCeti.Vortex.mem_ker_sobolevGaugeFixedOperator_iff`, and
  `TauCeti.Vortex.exists_sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq`:
  integration by parts, weak characterization, and weak-to-strong lifting for
  `sobolevGaugeFixedOperator a`.
* `TauCeti.Vortex.sobolevGaugeFixedOperator_surjective`,
  `TauCeti.Vortex.range_sobolevGaugeFixedOperator_eq_top`, and
  `TauCeti.Vortex.exists_continuousLinearMap_sobolevGaugeFixedOperator_comp_eq_id`: surjectivity
  (vanishing cokernel) and bounded `L²`-orthogonal right inverse `L² → H¹`.
* `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator`,
  `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_of_contDiff`, and
  `TauCeti.Vortex.isFredholm_sobolevGaugeFixedOperator_of_mem_framedFieldSpace`: the Fredholm
  property of `sobolevGaugeFixedOperator a`.
* `TauCeti.Vortex.kerSobolevGaugeFixedOperatorEquiv`: canonical real-linear equivalence between
  the `H¹` kernel and the classical `C²` kernel `gaugeFixedKernel x`.
* `TauCeti.Vortex.bijective_principalPartMap_comp_kerSobolevGaugeFixedOperatorEquiv`: isomorphism
  between the `H¹` kernel and the principal-part space `D → ℂ`.
* `TauCeti.Vortex.finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_card`,
  `finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_of_tendsto_sectionValue_mul_inv_pow`,
  `TauCeti.Vortex.index_sobolevGaugeFixedOperator_eq_two_mul_card`, and
  `index_sobolevGaugeFixedOperator_eq_two_mul_of_tendsto_sectionValue_mul_inv_pow`:
  exact kernel dimension and real Fredholm index `2 |D|` and `2 m`.
* `TauCeti.Vortex.bijective_sobolevGaugeFixedOperator_of_forall_sectionValue_ne_zero` and
  `TauCeti.Vortex.bijective_sobolevGaugeFixedOperator`: bijectivity when the section has no zeros
  and in degree zero.

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

/-! ### Internal helpers for `H¹(ℂ)⁴ → L²(ℂ; ℝ⁴)` value embedding -/

/-- The `L²` inner product of `sobolevFieldValues y` and `sobolevFieldValues u` is the sum of
coordinatewise `L²` inner products of their values. -/
private theorem inner_sobolevFieldValues (y u : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :
    ⟪sobolevFieldValues y, sobolevFieldValues u⟫ =
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
  filter_upwards [sobolevFieldValues_ae_eq y, sobolevFieldValues_ae_eq u] with z hy hu
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
`sobolevFieldValues ∘ Q = Q₁`, by the closed graph theorem. -/
private theorem exists_lift_sobolevFieldValues
    (Q₁ : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤)
    (hmem : ∀ f, (Q₁ f : ℂ → EuclideanSpace ℝ (Fin 4)) ∈ sobolevFields 1) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →L[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2),
      sobolevFieldValues.comp Q = Q₁ := by
  have hQ₁_mem (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) :
      ∃ y : Fin 4 → W1p (volume : Measure ℂ) ⊤ 2, sobolevFieldValues y = Q₁ f := by
    obtain ⟨y, hy⟩ := exists_sobolevField_value_ae_eq_of_mem_sobolevFields (hmem f)
    refine ⟨y, Lp.ext ?_⟩
    filter_upwards [sobolevFieldValues_ae_eq y, ae_all_iff.2 hy] with z h₁ h₂
    rw [h₁]
    ext j
    exact h₂ j
  choose q hq using hQ₁_mem
  let qL : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ →ₗ[ℝ] (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2) :=
    { toFun := q
      map_add' f g := sobolevFieldValues_injective (by simp [hq])
      map_smul' c f := sobolevFieldValues_injective (by simp [hq]) }
  have hclosed : IsClosed (qL.graph : Set (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ ×
      (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2))) := by
    have hgraph : (qL.graph : Set (Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤ ×
        (Fin 4 → W1p (volume : Measure ℂ) ⊤ 2))) = {p | sobolevFieldValues p.snd = Q₁ p.fst} := by
      ext ⟨f, y⟩
      simp only [SetLike.mem_coe, LinearMap.mem_graph_iff, Set.mem_ofPred_eq, qL, LinearMap.coe_mk,
        AddHom.coe_mk]
      exact ⟨fun h ↦ by rw [h, hq], fun h ↦ sobolevFieldValues_injective (by rw [h, hq])⟩
    rw [hgraph]
    exact isClosed_eq (sobolevFieldValues.continuous.comp continuous_snd)
      (Q₁.continuous.comp continuous_fst)
  refine ⟨ContinuousLinearMap.ofIsClosedGraph hclosed, ?_⟩
  ext1 f
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coeFn_ofIsClosedGraph, qL,
    LinearMap.coe_mk, AddHom.coe_mk] using hq f

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
  obtain ⟨Q, hQ⟩ := exists_lift_sobolevFieldValues Q₁ fun f ↦
    mem_sobolevFields_one_of_integral_inner_gaugeFixedAdjoint_eq
      hx.continuous.aestronglyMeasurable (.of_forall hM)
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (Q₁ f))
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp f)
      fun η hη hηc ↦ hQ₁weak f η (hη.of_le (by simp)) hηc
  have hQ_apply (f : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) : sobolevFieldValues (Q f) = Q₁ f :=
    DFunLike.congr_fun hQ f
  refine ⟨Q, ?_, fun f u hu ↦ ?_⟩
  · -- Verify `L_a ∘ Q = id` via the weak formulation.
    ext1 f
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    refine sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq
      hx.continuous hax fun η hη hηc ↦ ?_
    rw [← hQ₁weak f η (hη.of_le (by simp)) hηc]
    have hae : (fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (Q f j) z) =ᵐ[volume] Q₁ f :=
      ae_mono (Measure.restrict_coe_opens_top volume).ge
        ((sobolevFieldValues_ae_eq (Q f)).symm.trans (Lp.ext_iff.1 (hQ_apply f)))
    exact integral_congr_ae (hae.mono fun z hz ↦ by simp only [hz])
  · -- Verify `L²`-orthogonality to `ker L_a` from `L²`-orthogonality of `Q₀`.
    rw [← inner_sobolevFieldValues, hQ_apply, L2.inner_def,
      congrArg (fun ν ↦ ∫ z, ⟪Q₁ f z, sobolevFieldValues u z⟫ ∂ν)
        (Measure.restrict_coe_opens_top (volume : Measure ℂ))]
    have hu_weak (η : ℂ → EuclideanSpace ℝ (Fin 4)) (hη : ContDiff ℝ 2 η)
        (hηc : HasCompactSupport η) :
        ∫ z, ⟪(e (sobolevFieldValues u)) z, gaugeFixedAdjoint x η z⟫ = 0 := by
      have hae : (e (sobolevFieldValues u) : ℂ → EuclideanSpace ℝ (Fin 4)) =ᵐ[volume]
          fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (u j) z := by
        filter_upwards [ae_mono (Measure.restrict_coe_opens_top volume).ge
          (sobolevFieldValues_ae_eq u)] with z hz
        simpa only [e, coeFn_castLpₗᵢ] using hz
      have hEq : ∫ z, ⟪(e (sobolevFieldValues u)) z, gaugeFixedAdjoint x η z⟫ =
          ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (u j) z), gaugeFixedAdjoint x η z⟫ :=
        integral_congr_ae (hae.mono fun z hz ↦ congrArg (⟪·, gaugeFixedAdjoint x η z⟫) hz)
      have h0 : sobolevGaugeFixedOperator a u = 0 := by simpa using LinearMap.mem_ker.1 hu
      rw [hEq, ← integral_inner_sobolevGaugeFixedOperator hx.continuous hax u
        (hη.of_le one_le_two) hηc, h0]
      have hz : ∀ᵐ z ∂volume, (0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) z = 0 :=
        ae_mono (Measure.restrict_coe_opens_top volume).ge (Lp.coeFn_zero _ 2 μ⊤)
      rw [integral_congr_ae (hz.mono fun z h ↦ by rw [h, inner_zero_left]), integral_zero]
    refine (integral_congr_ae (.of_forall fun z ↦ ?_)).trans
      (hQ₀orth (e f) (e (sobolevFieldValues u)) hu_weak)
    rw [hQ₁_apply]
    simp only [e, coeFn_castLpₗᵢ]

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

/-- **The range of `L_x : H¹ → L²` is the whole space** at a `C¹` plane vortex with `|α| → 1` at
infinity and `L∞` class `a`. -/
theorem range_sobolevGaugeFixedOperator_eq_top (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).range = ⊤ :=
  LinearMap.range_eq_top.2 (sobolevGaugeFixedOperator_surjective hx hsol hlim hax)

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
      ∀ j : Fin 4, W1p.value (y.val j) =ᵐ[μ⊤] fun z ↦ Y.val z j := by
  have hweak := (mem_ker_sobolevGaugeFixedOperator_iff hx.continuous hax).1 y.property
  have hY₀L : MemLp (fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y.val j) z) 2 volume := by
    have hmem : MemLp (sobolevFieldValues y.val : ℂ → EuclideanSpace ℝ (Fin 4)) 2 volume := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using Lp.memLp (sobolevFieldValues y.val)
    exact hmem.ae_eq (ae_mono (Measure.restrict_coe_opens_top volume).ge
      (sobolevFieldValues_ae_eq y.val))
  -- Bootstrap the weak kernel element to `H⁴`, then apply Sobolev embedding `H⁴(ℂ) ↪ C²(ℂ)`.
  have h4 : (fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y.val j) z) ∈ sobolevFields 4 := by
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
  have hae : (fun z ↦ WithLp.toLp 2 fun j ↦ W1p.value (y.val j) z) =ᵐ[volume] Y := by
    filter_upwards [ae_all_iff.2 hgy] with z hz
    ext j
    exact hz j
  have hYker : ∀ z, gaugeFixedOperator x Y z = 0 :=
    (forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) hx.continuous
      (hYcd.of_le one_le_two) continuous_const).1 fun η hη hηc ↦ by
        have hEq : ∫ z, ⟪WithLp.toLp 2 (fun j ↦ W1p.value (y.val j) z),
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
      ∀ j : Fin 4, W1p.value (y.val j) =ᵐ[μ⊤] fun z ↦ Y.val z j := by
  obtain ⟨hYcd, hYL, hYker⟩ := mem_gaugeFixedKernel.1 Y.property
  have hYweak := (forall_integral_inner_gaugeFixedAdjoint_eq_iff (μ := volume) hx
    (hYcd.of_le one_le_two) continuous_const).2 hYker
  obtain ⟨w, hw, hLw⟩ :=
    exists_sobolevGaugeFixedOperator_eq_of_integral_inner_gaugeFixedAdjoint_eq
      hx hax hYL (f := 0) fun η hη hηc ↦ by
        have h0 : ∫ z, ⟪(0 : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ⊤) z, η z⟫ = 0 := by
          rw [integral_congr_ae (((Lp.coeFn_zero _ 2 μ⊤).filter_mono
            (ae_mono (Measure.restrict_coe_opens_top _).ge)).mono
            fun z hz ↦ by rw [hz, Pi.zero_apply, inner_zero_left])]
          exact integral_zero _ _
        rw [hYweak η hη hηc, h0]
        simp only [inner_zero_left, integral_zero]
  exact ⟨⟨w, LinearMap.mem_ker.2 hLw⟩, fun j ↦
    ae_mono (Measure.restrict_coe_opens_top volume).le (hw j)⟩

/-- Two elements of `gaugeFixedKernel x` agreeing almost everywhere coordinatewise are equal. -/
private theorem gaugeFixedKernel_eq_of_ae_eq {Y₁ Y₂ : gaugeFixedKernel x}
    (h : ∀ j : Fin 4, (fun z ↦ Y₁.val z j) =ᵐ[μ⊤] fun z ↦ Y₂.val z j) : Y₁ = Y₂ := by
  refine Subtype.ext (((mem_gaugeFixedKernel.1 Y₁.property).1.continuous.ae_eq_iff_eq volume
    (mem_gaugeFixedKernel.1 Y₂.property).1.continuous).1 ?_)
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
    filter_upwards [h₁₂ j, h₁ j, h₂ j, W1p.value_add_ae (y₁.val j) (y₂.val j)]
      with z hz hz₁ hz₂ hadd
    rw [← hz, Submodule.coe_add, Pi.add_apply, hadd, Pi.add_apply, hz₁, hz₂]
    rfl
  map_smul' c y := by
    have hy := (exists_mem_gaugeFixedKernel_ae_eq hx hbound hax y).choose_spec
    have hcy := (exists_mem_gaugeFixedKernel_ae_eq hx hbound hax (c • y)).choose_spec
    refine gaugeFixedKernel_eq_of_ae_eq fun j ↦ ?_
    filter_upwards [hcy j, hy j, W1p.value_smul_ae c (y.val j)] with z hzc hz hsmul
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
    W1p.value (y.val j) =ᵐ[μ⊤]
      fun z ↦ (kerSobolevGaugeFixedOperatorEquiv hx hbound hax y).val z j :=
  (exists_mem_gaugeFixedKernel_ae_eq hx hbound hax y).choose_spec j

/-- The preimage of a classical kernel element under `kerSobolevGaugeFixedOperatorEquiv` has value
coordinates agreeing almost everywhere with that classical element. -/
theorem kerSobolevGaugeFixedOperatorEquiv_symm_value_ae (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) (Y : gaugeFixedKernel x) (j : Fin 4) :
    W1p.value (((kerSobolevGaugeFixedOperatorEquiv hx hbound hax).symm Y).val j) =ᵐ[μ⊤]
      fun z ↦ Y.val z j :=
  (exists_mem_ker_sobolevGaugeFixedOperator_ae_eq hx.continuous hax Y).choose_spec j

/-- Characteristic property of `kerSobolevGaugeFixedOperatorEquiv`: an `H¹` kernel element `y` maps
to `Y ∈ gaugeFixedKernel x` if and only if each coordinate value of `y` agrees almost everywhere
with the corresponding coordinate of `Y`. -/
theorem kerSobolevGaugeFixedOperatorEquiv_eq_iff (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hax : a =ᵐ[μ⊤] x) (y : (sobolevGaugeFixedOperator a).ker) (Y : gaugeFixedKernel x) :
    kerSobolevGaugeFixedOperatorEquiv hx hbound hax y = Y ↔
      ∀ j : Fin 4, W1p.value (y.val j) =ᵐ[μ⊤] fun z ↦ Y.val z j :=
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
theorem finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_of_tendsto_sectionValue_mul_inv_pow
    {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    finrank ℝ (sobolevGaugeFixedOperator a).ker = 2 * m := by
  rw [(kerSobolevGaugeFixedOperatorEquiv hx hbound hax).finrank_eq,
    finrank_gaugeFixedKernel_eq_two_mul hx hhol hframe]

/-- **Identification of the `H¹` kernel with the principal-part space `D → ℂ`.** At a smooth field
`x` with bounded derivatives through order `3`, vanishing holomorphicity rows, `|α|² → 1` at
infinity, zero divisor `D`, and `L∞` class `a`, for any differentiable integrating factor `ν`
solving `∂bar ν = (b₂ - i b₁) / 2` and principal-part decomposition `hdec` on
`gaugeFixedKernel x`, composing the canonical kernel equivalence with `principalPartMap` yields a
real-linear bijection from `(sobolevGaugeFixedOperator a).ker` onto `Multiset.ToType D → ℂ`, the
real tangent space of the symmetric divisor space `Sym^|D| ℂ`. -/
theorem bijective_principalPartMap_comp_kerSobolevGaugeFixedOperatorEquiv (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hhol : ∀ w, equation x w 1 = 0 ∧ equation x w 2 = 0)
    (hlim : Tendsto (fun w ↦ 4 * (x w 2 ^ 2 + x w 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {D : Multiset ℂ} (hD : IsZeroMultiplicity (sectionValue x) fun z ↦ D.count z)
    {ν : ℂ → ℂ} (hν : Differentiable ℝ ν)
    (hνeq : ∀ w, conjWirtingerDeriv ν w 1 = ((x w 1 : ℂ) - I * x w 0) / 2)
    (hdec : ∀ y ∈ gaugeFixedKernel x, ∃ G : ℂ → ℂ, Continuous G ∧ ∃ H : ℂ → ℂ,
      Differentiable ℂ H ∧ ∀ w, sectionValue y w = sectionValue x w * G w + exp (ν w) * H w)
    (hax : a =ᵐ[μ⊤] x) :
    Function.Bijective
      ((principalPartMap hD hν.continuous hdec).comp
        (kerSobolevGaugeFixedOperatorEquiv hx hbound hax).toLinearMap) :=
  (principalPartMap_bijective hx hhol hlim hD hν hνeq hdec).comp
    (kerSobolevGaugeFixedOperatorEquiv hx hbound hax).bijective

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
      (sobolevGaugeFixedOperator_surjective (hx.of_le (by simp)) hsol hlim hax),
    finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_card hx hbound
      (fun w ↦ by simp [hsol w]) hlim hD hax]
  push_cast
  rfl

/-- **Real Fredholm index `2 m` of `L_x : H¹ → L²` at a framed vortex.** At a smooth plane vortex
`x` with bounded derivatives through order `3`, the degree-`m` end framing
`α(z) (z / |z|)⁻ᵐ → 1`, and `L∞` class `a`, the Sobolev realization `sobolevGaugeFixedOperator a`
has real Fredholm index `2 m`. -/
theorem index_sobolevGaugeFixedOperator_eq_two_mul_of_tendsto_sectionValue_mul_inv_pow
    {m : ℕ} (hx : ContDiff ℝ ∞ x)
    (hbound : ∀ i, ∀ n ≤ 3, ∃ C, ∀ z, ‖iteratedFDeriv ℝ n (fun z ↦ x z i) z‖ ≤ C)
    (hsol : ∀ z, equation x z = 0)
    (hframe : Tendsto (fun z ↦ sectionValue x z * ((z / (‖z‖ : ℂ)) ^ m)⁻¹) (cocompact ℂ) (𝓝 1))
    (hax : a =ᵐ[μ⊤] x) :
    (sobolevGaugeFixedOperator a).index = 2 * m := by
  rw [(sobolevGaugeFixedOperator a).index_of_surjective
      (sobolevGaugeFixedOperator_surjective (hx.of_le (by simp)) hsol
        (tendsto_normSq_of_tendsto_sectionValue_mul_inv_pow hframe) hax),
    finrank_ker_sobolevGaugeFixedOperator_eq_two_mul_of_tendsto_sectionValue_mul_inv_pow hx hbound
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
      (kerSobolevGaugeFixedOperatorEquiv hx hbound hax ⟨y, hy⟩).property))
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
    sobolevGaugeFixedOperator_surjective (hx.of_le (by simp)) hsol hlim hax⟩

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
    sobolevGaugeFixedOperator_surjective (hx.of_le (by simp)) hsol hlim hax⟩

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

end FramedFieldSpace

end TauCeti.Vortex
