/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.TestFunction
public import TauCeti.Analysis.PDE.Vortex.SpectralGap
public import TauCeti.Analysis.InnerProductSpace.WeakSolution
public import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Distribution.TestFunction.Lp
import TauCeti.Analysis.Normed.Group.Basic
import TauCeti.Analysis.PDE.Vortex.WeightedEstimate
import TauCeti.MeasureTheory.Integral.MeanInequalities
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The weak right inverse of the gauge-fixed operator at a plane vortex

At a field `x`, the gauge-fixed vortex operator `L_x = d₀* ⊕ d₁` (`gaugeFixedOperator`) is a
first-order operator on fields `ℂ → ℝ⁴`, with formal adjoint `L_x*` (`gaugeFixedAdjoint`). A
square-integrable field `y` is a *weak solution* of `L_x y = f`, for `f ∈ L²(ℂ; ℝ⁴)`, if

`∫ ⟪y, L_x* η⟫ = ∫ ⟪f, η⟫`

for every compactly supported `C²` test field `η`. This extends the classical notion: by the
integration-by-parts identity `integral_inner_gaugeFixedOperator`, when `x` is continuous a
compactly supported `C¹` field `y` is a weak solution of `L_x y = f` for `f` its classical image
under `L_x`. The *weak kernel* of `L_x` consists of the weak solutions of `L_x y = 0`.

This file shows that the weak cokernel of `L_x` vanishes at a plane vortex, with a bounded right
inverse. If `L_x*` is bounded below on test fields, `c ∫ |η|² ≤ ∫ |L_x* η|²` with `c > 0`, there
is a bounded operator `Q` on `L²(ℂ; ℝ⁴)` of norm at most `c^(-1/2)` such that `Q f` is a weak
solution of `L_x y = f` for every `f`, and `Q f` is orthogonal to the weak kernel
(`TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_of_mul_le`). Thus
`Q f` is the weak solution of least norm, and `Q` is the right inverse `L_x* (L_x L_x*)⁻¹` on the
`L²`-orthogonal complement of the weak kernel. At an actual vortex with `|α| → 1`, the spectral
gap `exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint` supplies the lower
bound (`TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`).

At such a vortex `Q` also respects exponential decay. With `ρ = √(1 + |z|²)` and `|c| < 1/2`,
every weak solution `y` of `L_x y = f` orthogonal to the weak kernel, in particular `y = Q f`,
satisfies `‖exp(c ρ) y‖₂ ≤ K ‖exp(c ρ) f‖₂` with `K` depending only on the vortex and `c`
(`TauCeti.Vortex.exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq`). The
weighted coercivity of `L_x L_x*` in `TauCeti.Analysis.PDE.Vortex.WeightedEstimate` gives this for
test fields; here it is transferred to `y`, which is an `L²` limit of values `L_x* η` because it
is orthogonal to the weak kernel. The transfer uses the bounded weights `W / (1 + ε W)`, for which
every weighted quantity of `y` and `f` is finite, and lets `ε → 0` by Fatou's lemma.

These are statements about weak solutions in `L²`. At a bounded field, weak solutions lie in `H¹`
by the elliptic regularity of `TauCeti.Analysis.PDE.Vortex.EllipticRegularity`, so `Q f ∈ H¹`
there. The Fredholm property and the dimension of the kernel of the Sobolev realization of `L_x`
are not proved here.

## Main results

* `TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_of_mul_le`: a
  lower bound on `L_x*` gives a bounded weak right inverse of `L_x` orthogonal to its weak kernel.
* `TauCeti.Vortex.exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`: the weak
  right inverse at a plane vortex with `|α| → 1`.
* `TauCeti.Vortex.exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq`: the
  exponentially weighted `L²` estimate for the weak right inverse at such a vortex.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

namespace TauCeti.Vortex

open MeasureTheory Filter
open scoped RealInnerProductSpace Topology NNReal ENNReal

variable {μ : Measure ℂ} [μ.IsAddHaarMeasure] {x : ℂ → EuclideanSpace ℝ (Fin 4)}

/-- The compactly supported `C²` test fields. -/
private abbrev TestField := TestFunction (⊤ : TopologicalSpace.Opens ℂ) (EuclideanSpace ℝ (Fin 4)) 2

private theorem memLp_gaugeFixedAdjoint (hx : Continuous x) (η : TestField) :
    MemLp (gaugeFixedAdjoint x η) 2 μ :=
  (continuous_gaugeFixedAdjoint hx (η.contDiff.of_le (by norm_cast))).memLp_of_hasCompactSupport
    (hasCompactSupport_gaugeFixedAdjoint η.hasCompactSupport)

/-- The formal adjoint `L_x*` on test fields, with values in `L²`. -/
private noncomputable def gaugeFixedAdjointToLp (μ : Measure ℂ) [μ.IsAddHaarMeasure]
    (hx : Continuous x) : TestField →ₗ[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ where
  toFun η := (memLp_gaugeFixedAdjoint hx η).toLp (gaugeFixedAdjoint x η)
  map_add' η ν := by
    rw [← MemLp.toLp_add]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun z ↦ ?_)
    rw [FunLike.coe_add, Pi.add_apply]
    exact gaugeFixedAdjoint_add x (η.contDiff.differentiable (by norm_num) z)
      (ν.contDiff.differentiable (by norm_num) z)
  map_smul' t η := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    refine MemLp.toLp_congr _ _ (ae_of_all _ fun z ↦ ?_)
    rw [FunLike.coe_smul, Pi.smul_apply]
    exact gaugeFixedAdjoint_smul x η t z

private theorem gaugeFixedAdjointToLp_apply (hx : Continuous x) (η : TestField) :
    gaugeFixedAdjointToLp μ hx η = (memLp_gaugeFixedAdjoint hx η).toLp (gaugeFixedAdjoint x η) :=
  rfl

private theorem inner_gaugeFixedAdjointToLp (hx : Continuous x)
    (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) (η : TestField) :
    ⟪u, gaugeFixedAdjointToLp μ hx η⟫ = ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ := by
  rw [gaugeFixedAdjointToLp_apply]
  exact L2.inner_toLp u (memLp_gaugeFixedAdjoint hx η)

/-- **Weak right inverse from a lower bound on the formal adjoint.** Let `x` be a continuous
field and suppose that `c ∫ |η|² ≤ ∫ |L_x* η|²` for every compactly supported `C²` field `η`,
with `c > 0`. Then there is a bounded operator `Q` on `L²(ℂ; ℝ⁴)` with `‖Q‖ ≤ c^(-1/2)` such
that

* `Q f` is a weak solution of `L_x y = f`: `∫ ⟪Q f, L_x* η⟫ = ∫ ⟪f, η⟫` for every compactly
  supported `C²` field `η`;
* `Q f` is orthogonal to the weak kernel: `∫ ⟪Q f, u⟫ = 0` for every `u ∈ L²` with
  `∫ ⟪u, L_x* η⟫ = 0` for all such `η`. -/
theorem exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_of_mul_le
    (hx : Continuous x) {c : ℝ} (hc : 0 < c)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      ‖Q‖ ≤ (√c)⁻¹ ∧
      (∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) ∧
      ∀ f u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪Q f z, u z⟫ ∂μ = 0 := by
  set S := gaugeFixedAdjointToLp μ hx
  set ι := (TestFunction.ambientToLp 2 μ : TestField →L[ℝ] _).toLinearMap
  have hS := inner_gaugeFixedAdjointToLp (μ := μ) hx
  have hι (u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) (η : TestField) :
      ⟪u, ι η⟫ = ∫ z, ⟪u z, η z⟫ ∂μ :=
    TestFunction.inner_ambientToLp u η
  -- The gap is the lower bound `√c ‖η‖ ≤ ‖L_x* η‖` in `L²`.
  have hbound (η : TestField) : √c * ‖ι η‖ ≤ ‖S η‖ := by
    refine le_of_sq_le_sq ?_ (norm_nonneg _)
    rw [mul_pow, Real.sq_sqrt hc.le, ContinuousLinearMap.coe_coe, TestFunction.norm_ambientToLp_sq,
      gaugeFixedAdjointToLp_apply, MemLp.norm_toLp_sq]
    exact hgap η η.contDiff η.hasCompactSupport
  obtain ⟨Q, hQn, hQK, hQ⟩ := LinearMap.exists_continuousLinearMap_inner_apply_eq_of_mul_norm_le
    S ι (Real.sqrt_pos.2 hc) hbound
  refine ⟨Q, hQn, fun f η hη hηc ↦ ?_, fun f u hu ↦ ?_⟩
  · have h := hQ f ⟨η, hη, hηc, by simp⟩
    rwa [hS, hι] at h
  · -- `u` lies in the weak kernel `(range S)ᗮ`, and `Q f` in its orthogonal complement.
    have huK : u ∈ (LinearMap.range S)ᗮ := by
      rw [Submodule.mem_orthogonal]
      rintro _ ⟨η, rfl⟩
      rw [real_inner_comm, hS]
      exact hu η η.contDiff η.hasCompactSupport
    rw [← L2.inner_def]
    exact Submodule.inner_left_of_mem_orthogonal huK (hQK f)

/-- **Weak right inverse at a plane vortex.** Let `x` be a `C¹` solution of the plane vortex
equation with `|α| → 1` at infinity. Then there is a bounded operator `Q` on `L²(ℂ; ℝ⁴)` such
that `Q f` is a weak solution of `L_x y = f` for every `f ∈ L²`, orthogonal to the weak kernel of
`L_x`. In particular the weak cokernel of `L_x` vanishes. -/
theorem exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq (hx : ContDiff ℝ 1 x)
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) :
    ∃ Q : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ →L[ℝ] Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ f η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪Q f z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) ∧
      ∀ f u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪Q f z, u z⟫ ∂μ = 0 := by
  obtain ⟨c, hc, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) hx hsol hlim
  obtain ⟨Q, -, hQ⟩ :=
    exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq_of_mul_le hx.continuous hc hgap
  exact ⟨Q, hQ⟩

/-! ### The exponentially weighted estimate -/

/-- A square-integrable field orthogonal to the weak kernel of `L_x` is an `L²` limit of values
`L_x* η` on test fields. -/
private theorem exists_integral_norm_sub_gaugeFixedAdjoint_sq_lt (hx : Continuous x)
    {y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ}
    (hy : ∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
      ∫ z, ⟪y z, u z⟫ ∂μ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η ∧ HasCompactSupport η ∧
      ∫ z, ‖y z - gaugeFixedAdjoint x η z‖ ^ 2 ∂μ < ε := by
  set S := gaugeFixedAdjointToLp μ hx
  have hS := inner_gaugeFixedAdjointToLp (μ := μ) hx
  have hmem : y ∈ (LinearMap.range S)ᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    have hu' (η : ℂ → EuclideanSpace ℝ (Fin 4)) (hη : ContDiff ℝ 2 η)
        (hηc : HasCompactSupport η) : ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0 := by
      have h := hS u ⟨η, hη, hηc, by simp⟩
      rw [TestFunction.coe_mk] at h
      rw [← h]
      exact Submodule.inner_left_of_mem_orthogonal (LinearMap.mem_range_self S _) hu
    rw [L2.inner_def, ← hy u hu']
    exact integral_congr_ae (ae_of_all _ fun z ↦ real_inner_comm _ _)
  rw [Submodule.orthogonal_orthogonal_eq_closure, ← SetLike.mem_coe,
    Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
  obtain ⟨_, ⟨η, rfl⟩, hd⟩ := hmem (√ε) (Real.sqrt_pos.2 hε)
  refine ⟨η, η.contDiff, η.hasCompactSupport, ?_⟩
  have hn : ∫ z, ‖y z - gaugeFixedAdjoint x η z‖ ^ 2 ∂μ = ‖y - S η‖ ^ 2 := by
    rw [← Lp.integral_norm_sq_eq_norm_sq]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub y (S η),
      (memLp_gaugeFixedAdjoint (μ := μ) hx η).coeFn_toLp] with z h₁ h₂
    rw [h₁, Pi.sub_apply, gaugeFixedAdjointToLp_apply, h₂]
  rw [hn]
  rw [dist_eq_norm] at hd
  exact (Real.lt_sqrt (norm_nonneg _)).1 hd

/-- If `y` is a weak solution of `L_x y = f`, the weighted pairing `∫ V² ⟪L_x L_x* η, η⟫` is the
pairing of `L_x* η - y` with `L_x* (V² η)` plus the weighted pairing of `f` with `η`. -/
private theorem integral_sq_mul_inner_gaugeFixedOperator_eq_add
    (hx : ContDiff ℝ 1 x) {y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 μ)
    (hweak : ∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    {V : ℂ → ℝ} (hV : ContDiff ℝ 2 V) {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) :
    ∫ z, V z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ =
      ∫ z, ⟪gaugeFixedAdjoint x η z - y z,
        gaugeFixedAdjoint x (fun t ↦ V t ^ 2 • η t) z⟫ ∂μ +
      ∫ z, V z ^ 2 * ⟪f z, η z⟫ ∂μ := by
  set H := gaugeFixedAdjoint x (fun t ↦ V t ^ 2 • η t)
  have hVη : ContDiff ℝ 2 (fun t ↦ V t ^ 2 • η t) := (hV.pow 2).smul hη
  have hVηc : HasCompactSupport (fun t ↦ V t ^ 2 • η t) := hηc.smul_left (f := fun t ↦ V t ^ 2)
  have hA := contDiff_gaugeFixedAdjoint hx hη
  have hAc := hasCompactSupport_gaugeFixedAdjoint (x := x) hηc
  have hH : MemLp H 2 μ :=
    (continuous_gaugeFixedAdjoint hx.continuous
      (hVη.of_le (by norm_num))).memLp_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint hVηc)
  have hG : MemLp (gaugeFixedAdjoint x η) 2 μ := hA.continuous.memLp_of_hasCompactSupport hAc
  have hi₁ : Integrable (fun z ↦ ⟪gaugeFixedAdjoint x η z - y z, H z⟫) μ :=
    (hG.sub hy).integrable_inner hH
  have hi₂ : Integrable (fun z ↦ ⟪y z, H z⟫) μ := hy.integrable_inner hH
  -- Integration by parts: `∫ V² ⟪L_x L_x* η, η⟫ = ∫ ⟪L_x* η, L_x* (V² η)⟫`.
  have h₁ : ∫ z, V z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ =
      ∫ z, ⟪gaugeFixedAdjoint x η z, H z⟫ ∂μ := by
    rw [← integral_inner_gaugeFixedOperator hx.continuous hA (hVη.of_le (by norm_num)) (.inl hAc)]
    simp only [real_inner_smul_right]
  have h₂ := hweak _ hVη hVηc
  simp only [real_inner_smul_right] at h₂
  rw [h₁, ← h₂, ← integral_add hi₁ hi₂]
  simp only [inner_sub_left, sub_add_cancel]

/-- For a weight `V` bounded by `B` with logarithmic gradient at most `|c|`,
`∫ |L_x* (V² η)|² ≤ 2 B⁴ ∫ |L_x* η|² + 8 c² B⁴ ∫ |η|²`. -/
private theorem integral_norm_sq_gaugeFixedAdjoint_sq_smul_le
    (hx : ContDiff ℝ 1 x) {V : ℂ → ℝ} (hV : ContDiff ℝ 2 V) {B c : ℝ} (hVB : ∀ z, V z ^ 2 ≤ B ^ 2)
    (hdV : ∀ z, ‖fderiv ℝ V z‖ ^ 2 ≤ c ^ 2 * V z ^ 2) {η : ℂ → EuclideanSpace ℝ (Fin 4)}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) :
    ∫ z, ‖gaugeFixedAdjoint x (fun t ↦ V t ^ 2 • η t) z‖ ^ 2 ∂μ ≤
      2 * B ^ 4 * (∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ) +
        8 * c ^ 2 * B ^ 4 * ∫ z, ‖η z‖ ^ 2 ∂μ := by
  have hVη : ContDiff ℝ 2 (fun t ↦ V t ^ 2 • η t) := (hV.pow 2).smul hη
  have hVηc : HasCompactSupport (fun t ↦ V t ^ 2 • η t) := hηc.smul_left (f := fun t ↦ V t ^ 2)
  have hA := contDiff_gaugeFixedAdjoint hx hη
  have hAc := hasCompactSupport_gaugeFixedAdjoint (x := x) hηc
  have hi {g : ℂ → EuclideanSpace ℝ (Fin 4)} (hg : Continuous g) (hgc : HasCompactSupport g) :
      Integrable (fun z ↦ ‖g z‖ ^ 2) μ :=
    (hg.norm.pow 2).integrable_of_hasCompactSupport (hgc.mono fun z hz hzero ↦ hz (by simp [hzero]))
  have iH := hi (continuous_gaugeFixedAdjoint hx.continuous (hVη.of_le (by norm_num)))
    (hasCompactSupport_gaugeFixedAdjoint (x := x) hVηc)
  have iG := hi hA.continuous hAc
  have iη := hi hη.continuous hηc
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (iG.const_mul _) (iη.const_mul _)]
  refine integral_mono iH ((iG.const_mul _).add (iη.const_mul _)) fun z ↦ ?_
  have hVz : DifferentiableAt ℝ V z := hV.differentiable (by simp) z
  have hl := gaugeFixedAdjoint_fun_smul (w := fun t ↦ V t ^ 2) x (hVz.pow 2)
    (hη.differentiable (by simp) z)
  have hp : fderiv ℝ (fun t ↦ V t ^ 2) z = (2 * V z) • fderiv ℝ V z := by
    simpa using (hVz.hasFDerivAt.pow 2).fderiv
  have hs := norm_sq_gaugeFixedAdjointSymbol (fderiv ℝ (fun t ↦ V t ^ 2) z) (η z)
  rw [hp, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hs
  rw [hl, hp]
  set σ := gaugeFixedAdjointSymbol ((2 * V z) • fderiv ℝ V z) (η z)
  have ht := norm_add_le (V z ^ 2 • gaugeFixedAdjoint x η z) σ
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at ht
  have hB4 : V z ^ 4 ≤ B ^ 4 := by
    have := pow_le_pow_left₀ (sq_nonneg _) (hVB z) 2
    simpa only [← pow_mul] using this
  -- `‖L_x* (V² η)‖ ≤ V² ‖L_x* η‖ + ‖σ‖`, with `‖σ‖² = 4 V² ‖dV‖² ‖η‖² ≤ 4 c² B⁴ ‖η‖²`.
  have h₁ : (V z ^ 2 * ‖gaugeFixedAdjoint x η z‖) ^ 2 ≤ B ^ 4 * ‖gaugeFixedAdjoint x η z‖ ^ 2 := by
    rw [mul_pow, ← pow_mul]
    exact mul_le_mul_of_nonneg_right hB4 (sq_nonneg _)
  have h₂ : ‖σ‖ ^ 2 ≤ 4 * c ^ 2 * B ^ 4 * ‖η z‖ ^ 2 := by
    rw [hs]
    have := mul_le_mul_of_nonneg_right (hdV z) (by positivity : (0 : ℝ) ≤ 4 * V z ^ 2 * ‖η z‖ ^ 2)
    have h4 := mul_le_mul_of_nonneg_right hB4
      (by positivity : (0 : ℝ) ≤ 4 * c ^ 2 * ‖η z‖ ^ 2)
    nlinarith
  have h₃ := norm_sub_sq_le_two_mul (V z ^ 2 • gaugeFixedAdjoint x η z + σ) 0 σ
  rw [sub_zero, add_sub_cancel_right, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)] at h₃
  linarith

/-- The bookkeeping behind the bounded-weight estimate: real inequalities between the weighted
norms, the pairings and the approximation error `e` combine to the stated bound. -/
private theorem le_of_weighted_energy_inequalities {Y F e s a P Q R h g n Y₀ t δ c₀ B c : ℝ}
    (ht : 0 < t) (hδ : 0 < δ) (hc₀ : 0 < c₀) (hl : a = P + Q) (h₁ : P ≤ t / 2 * h + 1 / (2 * t) * e)
    (h₂ : Q ≤ δ / 2 * s + 1 / (2 * δ) * F) (h₃ : δ * s ≤ a) (h₄ : R ≤ 2 * a + 4 * c ^ 2 * s)
    (h₅ : h ≤ 2 * B ^ 4 * g + 8 * c ^ 2 * B ^ 4 * n) (h₆ : c₀ * n ≤ g)
    (h₇ : g ≤ 2 * e + 2 * Y₀) (h₈ : Y ≤ 2 * B ^ 2 * e + 2 * R) :
    Y ≤ (4 / δ + 8 * c ^ 2 / δ ^ 2) * F +
        (8 + 16 * c ^ 2 / δ) * t * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) * Y₀ +
      (2 * B ^ 2 + (8 + 16 * c ^ 2 / δ) * t * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) +
        (8 + 16 * c ^ 2 / δ) / (2 * t)) * e := by
  set D := 2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀
  set E := t / 2 * h + 1 / (2 * t) * e
  -- `E ≤ t D (e + Y₀) + e / (2 t)`, from `h ≤ D g` and `g ≤ 2 e + 2 Y₀`.
  have hn := mul_le_mul_of_nonneg_left h₆ (by positivity : (0 : ℝ) ≤ 8 * c ^ 2 * B ^ 4 / c₀)
  have hcn : 8 * c ^ 2 * B ^ 4 / c₀ * (c₀ * n) = 8 * c ^ 2 * B ^ 4 * n := by field_simp
  have hh := mul_le_mul_of_nonneg_left h₇ (by positivity : (0 : ℝ) ≤ t / 2 * D)
  have hh' := mul_le_mul_of_nonneg_left h₅ (by positivity : (0 : ℝ) ≤ t / 2)
  have hE : E ≤ t * D * e + t * D * Y₀ + 1 / (2 * t) * e := by
    linear_combination hh' + t / 2 * hn + hh - t / 2 * hcn
  -- `δ s ≤ 2 E + F / δ`, so `4 c² s ≤ 4 c² δ⁻¹ (2 E + F / δ)`.
  have hδs : δ * s ≤ 2 * E + F / δ := by linear_combination 2 * (h₃ + hl + h₁ + h₂)
  have hs := mul_le_mul_of_nonneg_left hδs (by positivity : (0 : ℝ) ≤ 4 * c ^ 2 / δ)
  have hκ := mul_le_mul_of_nonneg_left hE (by positivity : (0 : ℝ) ≤ 8 + 16 * c ^ 2 / δ)
  have hss : 4 * c ^ 2 / δ * (δ * s) = 4 * c ^ 2 * s := by field_simp
  linear_combination h₈ + 2 * h₄ + 4 * hl + 4 * h₁ + 4 * h₂ + 2 * hδs + 2 * hs + hκ - 2 * hss

/-- One approximation step of the bounded-weight estimate. Let `y` be a weak solution of
`L_x y = f` and `V` a weight bounded by `B` with logarithmic gradient at most `|c|`, for which
`L_x L_x*` is weighted-coercive with constant `δ`. Then for every test field `η` and `t > 0`,
`∫ V² |y|²` is at most `(4 / δ + 8 c² / δ²) ∫ V² |f|²` plus errors that are small when `t` is small
and `L_x* η` is close to `y` in `L²`. -/
private theorem integral_sq_mul_norm_sq_le_add_mul_integral_norm_sub_sq
    (hx : ContDiff ℝ 1 x) {y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 μ)
    (hf : MemLp f 2 μ)
    (hweak : ∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c₀ * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ)
    {V : ℂ → ℝ} (hV : ContDiff ℝ 2 V) {B : ℝ} (hVB : ∀ z, V z ^ 2 ≤ B ^ 2) {c : ℝ}
    (hdV : ∀ z, ‖fderiv ℝ V z‖ ^ 2 ≤ c ^ 2 * V z ^ 2) {δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      δ * (∫ z, V z ^ 2 * ‖η z‖ ^ 2 ∂μ) ≤
        ∫ z, V z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ)
    {t : ℝ} (ht : 0 < t) {η : ℂ → EuclideanSpace ℝ (Fin 4)} (hη : ContDiff ℝ 2 η)
    (hηc : HasCompactSupport η) :
    ∫ z, V z ^ 2 * ‖y z‖ ^ 2 ∂μ ≤
      (4 / δ + 8 * c ^ 2 / δ ^ 2) * (∫ z, V z ^ 2 * ‖f z‖ ^ 2 ∂μ) +
        (8 + 16 * c ^ 2 / δ) * t * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) *
          (∫ z, ‖y z‖ ^ 2 ∂μ) +
        (2 * B ^ 2 + (8 + 16 * c ^ 2 / δ) * t * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) +
          (8 + 16 * c ^ 2 / δ) / (2 * t)) *
          ∫ z, ‖y z - gaugeFixedAdjoint x η z‖ ^ 2 ∂μ := by
  set G := gaugeFixedAdjoint x η
  set H := gaugeFixedAdjoint x (fun t ↦ V t ^ 2 • η t)
  have hwt {g : ℂ → EuclideanSpace ℝ (Fin 4)} (hg : MemLp g 2 μ) :=
    hg.integrable_sq_mul_norm_sq hV.continuous.aestronglyMeasurable (ae_of_all _ hVB)
  have hG : MemLp G 2 μ := (contDiff_gaugeFixedAdjoint hx hη).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_gaugeFixedAdjoint hηc)
  have hH : MemLp H 2 μ :=
    (continuous_gaugeFixedAdjoint hx.continuous
      (((hV.pow 2).smul hη).of_le (by norm_num))).memLp_of_hasCompactSupport
      (hasCompactSupport_gaugeFixedAdjoint (hηc.smul_left (f := fun t ↦ V t ^ 2)))
  have hη₂ : MemLp η 2 μ := hη.continuous.memLp_of_hasCompactSupport hηc
  have iyG : Integrable (fun z ↦ ‖y z - G z‖ ^ 2) μ := (hy.sub hG).norm.integrable_sq
  have iy := hy.norm.integrable_sq
  have iG := hG.norm.integrable_sq
  have hl := integral_sq_mul_inner_gaugeFixedOperator_eq_add hx hy hweak hV hη hηc
  -- The two pairings, by the arithmetic-geometric mean inequality.
  have h₁ : ∫ z, ⟪G z - y z, H z⟫ ∂μ ≤
      t / 2 * (∫ z, ‖H z‖ ^ 2 ∂μ) + 1 / (2 * t) * ∫ z, ‖y z - G z‖ ^ 2 ∂μ := by
    have := integral_mul_inner_le (ν := μ) (w := fun _ ↦ (1 : ℝ)) (G := fun z ↦ G z - y z)
      (η := H) (fun _ ↦ zero_le_one) (by simpa using hH.norm.integrable_sq)
      (by simpa using (hG.sub hy).norm.integrable_sq) ht
    simpa only [one_mul, norm_sub_rev (G _)] using this
  have h₂ := integral_mul_inner_le (ν := μ) (w := fun z ↦ V z ^ 2) (G := f) (η := η)
    (fun z ↦ sq_nonneg _) (hwt hη₂) (hwt hf) hδ
  -- Coercivity, the weighted adjoint energy, and the size of `L_x* (V² η)`.
  have h₃ := hcoer η hη hηc
  have h₄ := integral_sq_mul_norm_sq_gaugeFixedAdjoint_le (μ := μ) hx hη hηc
    (hV.of_le (by norm_num)) hdV
  have h₅ := integral_norm_sq_gaugeFixedAdjoint_sq_smul_le (μ := μ) hx hV hVB hdV hη hηc
  have h₆ := hgap η hη hηc
  -- `|L_x* η|² ≤ 2 |y - L_x* η|² + 2 |y|²` and `V² |y|² ≤ 2 B² |y - L_x* η|² + 2 V² |L_x* η|²`.
  have h₇ : ∫ z, ‖G z‖ ^ 2 ∂μ ≤
      2 * (∫ z, ‖y z - G z‖ ^ 2 ∂μ) + 2 * ∫ z, ‖y z‖ ^ 2 ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (iyG.const_mul _) (iy.const_mul _)]
    refine integral_mono iG ((iyG.const_mul _).add (iy.const_mul _)) fun z ↦ ?_
    have := norm_sub_sq_le_two_mul (G z) 0 (y z)
    rw [sub_zero, zero_sub, norm_neg, norm_sub_rev] at this
    linarith
  have h₈ : ∫ z, V z ^ 2 * ‖y z‖ ^ 2 ∂μ ≤
      2 * B ^ 2 * (∫ z, ‖y z - G z‖ ^ 2 ∂μ) + 2 * ∫ z, V z ^ 2 * ‖G z‖ ^ 2 ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (iyG.const_mul _) ((hwt hG).const_mul _)]
    refine integral_mono (hwt hy) ((iyG.const_mul _).add ((hwt hG).const_mul _)) fun z ↦ ?_
    have h2 := norm_sub_sq_le_two_mul (y z) 0 (G z)
    rw [sub_zero, zero_sub, norm_neg] at h2
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg (V z))
    have := mul_le_mul_of_nonneg_right (hVB z) (sq_nonneg ‖y z - G z‖)
    linarith
  exact le_of_weighted_energy_inequalities ht hδ hc₀ hl h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈

/-- **The bounded-weight estimate.** Let `y` be a square-integrable weak solution of `L_x y = f`
that is an `L²` limit of values `L_x* η` on test fields, and let `V` be a weight bounded by `B`
with logarithmic gradient at most `|c|`, for which `L_x L_x*` is weighted-coercive with constant
`δ`. Then `∫ V² |y|² ≤ (4 / δ + 8 c² / δ²) ∫ V² |f|²`; the bound `B` does not enter. -/
private theorem integral_sq_mul_norm_sq_le_of_forall_exists_lt
    (hx : ContDiff ℝ 1 x) {y f : ℂ → EuclideanSpace ℝ (Fin 4)} (hy : MemLp y 2 μ)
    (hf : MemLp f 2 μ)
    (hweak : ∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
      ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ)
    (happrox : ∀ ε > 0, ∃ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η ∧
      HasCompactSupport η ∧ ∫ z, ‖y z - gaugeFixedAdjoint x η z‖ ^ 2 ∂μ < ε)
    {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hgap : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      c₀ * ∫ z, ‖η z‖ ^ 2 ∂μ ≤ ∫ z, ‖gaugeFixedAdjoint x η z‖ ^ 2 ∂μ)
    {V : ℂ → ℝ} (hV : ContDiff ℝ 2 V) {B : ℝ} (hVB : ∀ z, V z ^ 2 ≤ B ^ 2) {c : ℝ}
    (hdV : ∀ z, ‖fderiv ℝ V z‖ ^ 2 ≤ c ^ 2 * V z ^ 2) {δ : ℝ} (hδ : 0 < δ)
    (hcoer : ∀ η : ℂ → EuclideanSpace ℝ (Fin 4), ContDiff ℝ 2 η → HasCompactSupport η →
      δ * (∫ z, V z ^ 2 * ‖η z‖ ^ 2 ∂μ) ≤
        ∫ z, V z ^ 2 * ⟪gaugeFixedOperator x (gaugeFixedAdjoint x η) z, η z⟫ ∂μ) :
    ∫ z, V z ^ 2 * ‖y z‖ ^ 2 ∂μ ≤
      (4 / δ + 8 * c ^ 2 / δ ^ 2) * ∫ z, V z ^ 2 * ‖f z‖ ^ 2 ∂μ := by
  -- Nonnegativity facts used by `positivity` and `nlinarith` below.
  have : 0 ≤ 8 + 16 * c ^ 2 / δ := by positivity
  have : 0 ≤ 2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀ := by positivity
  have : 0 ≤ ∫ z, ‖y z‖ ^ 2 ∂μ := integral_nonneg fun z ↦ by positivity
  -- First let `L_x* η → y` in `L²` at fixed `t > 0`, then let `t → 0`.
  have step (t : ℝ) (ht : 0 < t) : ∫ z, V z ^ 2 * ‖y z‖ ^ 2 ∂μ ≤
      (4 / δ + 8 * c ^ 2 / δ ^ 2) * (∫ z, V z ^ 2 * ‖f z‖ ^ 2 ∂μ) +
        (8 + 16 * c ^ 2 / δ) * t * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) *
          ∫ z, ‖y z‖ ^ 2 ∂μ := by
    have : 0 ≤ 2 * B ^ 2 + (8 + 16 * c ^ 2 / δ) * t * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) +
        (8 + 16 * c ^ 2 / δ) / (2 * t) := by positivity
    refine le_of_forall_pos_le_add fun ε hε ↦ ?_
    obtain ⟨η, hη, hηc, he⟩ := happrox (ε / (2 * B ^ 2 + (8 + 16 * c ^ 2 / δ) * t *
      (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) + (8 + 16 * c ^ 2 / δ) / (2 * t) + 1)) (by positivity)
    have h := integral_sq_mul_norm_sq_le_add_mul_integral_norm_sub_sq hx hy hf hweak hc₀ hgap hV
      hVB hdV hδ hcoer ht hη hηc
    have he₀ : 0 ≤ ∫ z, ‖y z - gaugeFixedAdjoint x η z‖ ^ 2 ∂μ :=
      integral_nonneg fun z ↦ by positivity
    have hlt := (lt_div_iff₀ (by positivity)).1 he
    nlinarith
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  set M := (8 + 16 * c ^ 2 / δ) * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) * ∫ z, ‖y z‖ ^ 2 ∂μ
  have : 0 ≤ M := by positivity
  have h := step (ε / (M + 1)) (by positivity)
  have : (8 + 16 * c ^ 2 / δ) * (ε / (M + 1)) * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) *
      ∫ z, ‖y z‖ ^ 2 ∂μ ≤ ε := by
    rw [show (8 + 16 * c ^ 2 / δ) * (ε / (M + 1)) * (2 * B ^ 4 + 8 * c ^ 2 * B ^ 4 / c₀) *
      ∫ z, ‖y z‖ ^ 2 ∂μ = ε * (M / (M + 1)) by ring]
    exact mul_le_of_le_one_right hε.le ((div_le_one (by positivity)).2 (by linarith))
  linarith

omit [μ.IsAddHaarMeasure] in
/-- **Fatou's lemma for truncated weights.** A bound on `∫ V_n² u` for all the truncations
`V_n = W / (1 + W / (n + 1))` of a weight `W` holds for `W` itself, since `V_n → W` pointwise. -/
private theorem lintegral_ofReal_sq_mul_le_of_forall_lintegral_div_one_add_mul_le
    {W u : ℂ → ℝ} (hW : AEMeasurable W μ) (hu : AEMeasurable u μ) {C : ℝ≥0∞}
    (h : ∀ n : ℕ,
      ∫⁻ z, ENNReal.ofReal ((W z / (1 + 1 / ((n : ℝ) + 1) * W z)) ^ 2 * u z) ∂μ ≤ C) :
    ∫⁻ z, ENNReal.ofReal (W z ^ 2 * u z) ∂μ ≤ C := by
  have hlim (z : ℂ) : Tendsto (fun n : ℕ ↦
      ENNReal.ofReal ((W z / (1 + 1 / ((n : ℝ) + 1) * W z)) ^ 2 * u z)) atTop
      (𝓝 (ENNReal.ofReal (W z ^ 2 * u z))) := by
    have hc : ContinuousAt (fun ε : ℝ ↦ ENNReal.ofReal ((W z / (1 + ε * W z)) ^ 2 * u z)) 0 :=
      ENNReal.continuous_ofReal.continuousAt.comp
        (((continuousAt_const.div (continuousAt_const.add
          (continuousAt_id.mul continuousAt_const)) (by simp)).pow 2).mul continuousAt_const)
    have h := hc.tendsto
    simp only [zero_mul, add_zero, div_one] at h
    exact h.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  calc ∫⁻ z, ENNReal.ofReal (W z ^ 2 * u z) ∂μ
      = ∫⁻ z, liminf (fun n : ℕ ↦
          ENNReal.ofReal ((W z / (1 + 1 / ((n : ℝ) + 1) * W z)) ^ 2 * u z)) atTop ∂μ :=
        lintegral_congr fun z ↦ (hlim z).liminf_eq.symm
    _ ≤ liminf (fun n : ℕ ↦
          ∫⁻ z, ENNReal.ofReal ((W z / (1 + 1 / ((n : ℝ) + 1) * W z)) ^ 2 * u z) ∂μ) atTop :=
        lintegral_liminf_le' fun n ↦ (((hW.div (aemeasurable_const.add
          (aemeasurable_const.mul hW))).pow_const 2).mul hu).ennreal_ofReal
    _ ≤ C := liminf_le_of_frequently_le' (Frequently.of_forall h)

/-- **The exponentially weighted estimate for the weak right inverse.** Let `x` be a `C¹`
solution of the plane vortex equation with `|α| → 1` at infinity, let `ρ(z) = √(1 + |z|²)` and
`|c| < 1/2`. There is `K` such that every square-integrable weak solution `y` of `L_x y = f`
orthogonal to the weak kernel of `L_x` satisfies

`‖exp(c ρ) y‖₂ ≤ K ‖exp(c ρ) f‖₂`,

where either side may be infinite. Such a `y` is unique
(`LinearMap.eq_of_inner_apply_eq_of_mem_orthogonal`), so it is the value at `f` of the weak right
inverse `Q` of `exists_continuousLinearMap_integral_inner_gaugeFixedAdjoint_eq`, and this is the
weighted output estimate `‖exp(c ρ) Q f‖₂ ≤ K ‖exp(c ρ) f‖₂` for every `f ∈ L²`. For `c > 0` it
says that `Q` maps inputs decaying like `exp(-c ρ)` in `L²` to outputs decaying at the same rate.

The proof applies the weighted coercivity of `L_x L_x*`
(`exists_pos_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator`) to the
bounded weights `W / (1 + ε W)`, `W = exp(c √(b + |z|²))`, approximating `y` in `L²` by values
`L_x* η` on test fields, and then lets `ε → 0` by Fatou's lemma. -/
theorem exists_eLpNorm_exp_mul_smul_le_of_integral_inner_gaugeFixedAdjoint_eq
    (hx : ContDiff ℝ 1 x) (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1))
    {c : ℝ} (hc : |c| < 1 / 2) :
    ∃ K : ℝ≥0, ∀ f y : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
      (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
        ∫ z, ⟪y z, gaugeFixedAdjoint x η z⟫ ∂μ = ∫ z, ⟪f z, η z⟫ ∂μ) →
      (∀ u : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ,
        (∀ η, ContDiff ℝ 2 η → HasCompactSupport η →
          ∫ z, ⟪u z, gaugeFixedAdjoint x η z⟫ ∂μ = 0) →
        ∫ z, ⟪y z, u z⟫ ∂μ = 0) →
      eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • y z) 2 μ ≤
        K * eLpNorm (fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2)) • f z) 2 μ := by
  obtain ⟨c₀, hc₀, hgap⟩ :=
    exists_pos_mul_integral_norm_sq_le_integral_norm_sq_gaugeFixedAdjoint (μ := μ) hx hsol hlim
  obtain ⟨b, hb, δ, hδ, hcoer⟩ :=
    exists_pos_mul_integral_sq_mul_norm_sq_le_integral_sq_mul_inner_gaugeFixedOperator (μ := μ)
      hx hsol hlim hc
  have hb₀ : 0 < b := by linarith
  set K₀ : ℝ := 4 / δ + 8 * c ^ 2 / δ ^ 2
  set E : ℝ := Real.exp (|c| * √|b - 1|) ^ 2
  have hK₀ : 0 ≤ K₀ := by positivity
  have hE : 0 ≤ E := by positivity
  set K : ℝ≥0 := Real.toNNReal √(E * E * K₀) with hK_def
  refine ⟨K, fun f y hweak horth ↦ ?_⟩
  set w : ℂ → ℝ := fun z ↦ Real.exp (c * √(1 + ‖z‖ ^ 2))
  set W : ℂ → ℝ := fun z ↦ Real.exp (c * √(b + ‖z‖ ^ 2))
  have hy := Lp.memLp y
  have hf := Lp.memLp f
  -- The estimate for the bounded weights `V_n = W / (1 + W / (n + 1))`.
  set V : ℕ → ℂ → ℝ := fun n z ↦ W z / (1 + 1 / ((n : ℝ) + 1) * W z)
  have hVn (n : ℕ) : ∫⁻ z, ENNReal.ofReal (V n z ^ 2 * ‖y z‖ ^ 2) ∂μ ≤
      ENNReal.ofReal K₀ * ∫⁻ z, ENNReal.ofReal (W z ^ 2 * ‖f z‖ ^ 2) ∂μ := by
    have hε : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hV : ContDiff ℝ 2 (V n) := contDiff_exp_div_one_add_mul_exp c hb₀ hε.le
    have hV₀ (z : ℂ) : 0 ≤ V n z := exp_div_one_add_mul_exp_nonneg c hε.le z
    have hVB (z : ℂ) : V n z ^ 2 ≤ (1 / (1 / ((n : ℝ) + 1))) ^ 2 :=
      pow_le_pow_left₀ (hV₀ z) (exp_div_one_add_mul_exp_le_one_div c hε z) 2
    have h := integral_sq_mul_norm_sq_le_of_forall_exists_lt hx hy hf hweak
      (fun ε hε ↦ exists_integral_norm_sub_gaugeFixedAdjoint_sq_lt hx.continuous horth hε) hc₀
      hgap hV hVB (fun z ↦ norm_fderiv_sq_le_of_norm_fderiv_le c hb₀.le (hV₀ z)
        (norm_fderiv_exp_div_one_add_mul_exp_le c hb₀ hε.le z)) hδ
      (hcoer (V n) hV hV₀ (norm_fderiv_exp_div_one_add_mul_exp_le c hb₀ hε.le))
    have hwt {g : ℂ → EuclideanSpace ℝ (Fin 4)} (hg : MemLp g 2 μ) :=
      hg.integrable_sq_mul_norm_sq hV.continuous.aestronglyMeasurable (ae_of_all _ hVB)
    rw [← ofReal_integral_eq_lintegral_ofReal (hwt hy) (ae_of_all _ fun z ↦ by positivity)]
    refine (ENNReal.ofReal_le_ofReal h).trans ?_
    rw [ENNReal.ofReal_mul hK₀,
      ofReal_integral_eq_lintegral_ofReal (hwt hf) (ae_of_all _ fun z ↦ by positivity)]
    gcongr with z
    exact exp_div_one_add_mul_exp_le_exp c hε.le z
  -- Fatou's lemma as `n → ∞`, since `V_n → W` pointwise.
  have hWy := lintegral_ofReal_sq_mul_le_of_forall_lintegral_div_one_add_mul_le
    (contDiff_exp_mul_sqrt_add_norm_sq (n := 0) c hb₀).continuous.aemeasurable
    ((Lp.aestronglyMeasurable y).norm.pow 2).aemeasurable hVn
  -- The weights `w` and `W` are comparable.
  have hcmp {u v : ℂ → ℝ} (huv : ∀ z, u z ^ 2 ≤ E * v z ^ 2)
      (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
      ∫⁻ z, ENNReal.ofReal (u z ^ 2 * ‖g z‖ ^ 2) ∂μ ≤
        ENNReal.ofReal E * ∫⁻ z, ENNReal.ofReal (v z ^ 2 * ‖g z‖ ^ 2) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z ↦ ?_
    rw [← ENNReal.ofReal_mul hE, ← mul_assoc]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (huv z) (sq_nonneg _))
  have hwy := hcmp (u := w) (v := W)
    (fun z ↦ by simpa only [abs_sub_comm 1 b] using sq_exp_mul_sqrt_add_norm_sq_le c 1 b z) y
  have hWf := hcmp (u := W) (v := w) (sq_exp_mul_sqrt_add_norm_sq_le c b 1) f
  -- Convert to `L²` norms.
  have henorm (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) (z : ℂ) :
      ‖w z • g z‖ₑ ^ (2 : ℝ≥0∞).toReal = ENNReal.ofReal (w z ^ 2 * ‖g z‖ ^ 2) := by
    rw [← ofReal_norm, ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg
      (norm_nonneg _) zero_le_two, norm_smul, Real.norm_eq_abs, Real.rpow_two, mul_pow, sq_abs]
  have hsm (g : Lp (EuclideanSpace ℝ (Fin 4)) 2 μ) :
      AEStronglyMeasurable (fun z ↦ w z • g z) μ :=
    ((contDiff_exp_mul_sqrt_add_norm_sq (n := 0) c one_pos).continuous.aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable g)
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top (hsm y),
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top (hsm f)]
  simp_rw [henorm]
  have hK : (K : ℝ≥0∞) = ENNReal.ofReal (E * E * K₀) ^ (1 / (2 : ℝ≥0∞).toReal) := by
    rw [ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
      ← Real.sqrt_eq_rpow, ← ENNReal.ofReal_coe_nnreal, hK_def,
      Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  rw [hK, ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  gcongr
  calc ∫⁻ z, ENNReal.ofReal (w z ^ 2 * ‖y z‖ ^ 2) ∂μ
      ≤ ENNReal.ofReal E * (ENNReal.ofReal K₀ *
          (ENNReal.ofReal E * ∫⁻ z, ENNReal.ofReal (w z ^ 2 * ‖f z‖ ^ 2) ∂μ)) :=
        hwy.trans (by gcongr; exact hWy.trans (by gcongr))
    _ = ENNReal.ofReal (E * E * K₀) * ∫⁻ z, ENNReal.ofReal (w z ^ 2 * ‖f z‖ ^ 2) ∂μ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hE]
        ring

end TauCeti.Vortex
