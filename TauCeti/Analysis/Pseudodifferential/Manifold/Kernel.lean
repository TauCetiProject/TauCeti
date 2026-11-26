/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.Pseudodifferential.Kernel
public import TauCeti.Analysis.Pseudodifferential.Manifold.Smoothing
public import TauCeti.Geometry.Manifold.IsManifold.MaximalAtlas
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Geometry.Manifold.ContMDiff.ChartCutoff

/-!
# Operators of order `-∞` on a compact manifold have smooth kernels

Let `M` be a manifold modelled on `ℝⁿ` and `μ` a measure on `M` with a smooth nonvanishing
density in every chart `e` of the maximal atlas: there is a function `ρ`, smooth and nonzero on
the chart target, with `∫ f dμ = ∫_{e.target} ρ(y) f(e⁻¹ y) dy` for continuous compactly supported
functions `f` supported in the chart source; the Riemannian volume of a smooth metric is an
example.

This file shows that an operator `P` of order `-∞` on the complex-valued smooth functions on `M`
(`TauCeti.smoothingPseudodifferentialOperators`) is an integral operator with a smooth kernel:

* **In a chart** (`TauCeti.exists_contMDiff_forall_mul_apply_mul_eq_integral`): for cutoffs `φ` and
  `ψ` in the target of a chart `e`, read on `M` through the chart, there is a smooth compactly
  supported function `K` on `M × M` with `φ(x) P (ψ u) (x) = ∫ K(x, y) u(y) dμ(y)` for every
  smooth `u`. The chart compression of `P` by `φ` and `ψ` is the quantization `Op(r)` of a
  smoothing symbol `r`, which is the integral operator with the smooth kernel
  `TauCeti.quantizationKernel r.coefficient`
  (`TauCeti.Symbol.IsSmoothing.contDiff_quantizationKernel`,
  `TauCeti.quantizeSchwartzValue_eq_integral_quantizationKernel`). Read on `M`, and divided by the
  density of `μ` in the chart, this kernel is `K`.
* **On a compact manifold** of positive dimension
  (`TauCeti.exists_contMDiff_forall_apply_eq_integral_of_mem_smoothingPseudodifferentialOperators`),
  there is a smooth function `K` on `M × M` with `P u (x) = ∫ K(x, y) u(y) dμ(y)` for
  every smooth `u`. A partition of unity `ρᵢ` subordinate to charts splits `P` as
  `∑ᵢ ρᵢ P`, and a second partition of unity `σᵢⱼ` splits each `ρᵢ P` as `∑ⱼ ρᵢ P σᵢⱼ`, where both
  `ρᵢ` and `σᵢⱼ` are supported in the source of one chart `eᵢⱼ` of the maximal atlas
  (`IsCompact.exists_smoothPartition_mem_maximalAtlas_eqOn_symm`). When `σᵢⱼ` is supported far
  from `ρᵢ`, the chart `eᵢⱼ` has two components with disjoint images in `ℝⁿ`: the class of
  operators of order `-∞` is defined by chart compressions in every chart of the maximal atlas,
  and these are the charts that see how `P` connects two distant points. Each piece `ρᵢ P σᵢⱼ`
  has a smooth kernel by the chart statement, and `K` is their sum.

Conversely, an integral operator with a smooth compactly supported kernel has order `-∞`, so on a
compact manifold the operators of order `-∞` are exactly the integral operators with smooth
kernels. They are the remainders of the elliptic parametrices on a compact base.

## Main results

* `TauCeti.exists_contMDiff_forall_mul_apply_mul_eq_integral`: an operator of order `-∞`,
  localized by two cutoffs in one chart, is an integral operator with a smooth compactly supported
  kernel.
* `TauCeti.exists_contMDiff_forall_apply_eq_integral_of_mem_smoothingPseudodifferentialOperators`:
  on a compact manifold of positive dimension, an operator of order `-∞` is an integral operator
  with a smooth kernel.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1, Definition
  18.1.20 and the remark following it (operators of order `-∞` are those with smooth kernels).
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

open MeasureTheory Set Filter
open scoped ContDiff Manifold Distributions SchwartzMap Topology

namespace TauCeti

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M]
  [T2Space M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [MeasurableSpace M] {μ : Measure M}
  {P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
    C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯}

/-! ### In a chart -/

section Chart

variable {e : OpenPartialHomeomorph M (CoordinateSpace n)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)

omit [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] [MeasurableSpace M] in
/-- **The chart compression as an integral.** Let `Op(r)`, for a smoothing symbol `r`, be the
compression of `P` by cutoffs `φ` and `ψ` in the chart `e`, and let `φ₁ = 1` on the support of `φ`
and `ψ₁ = 1` on the support of `ψ`. At a point `x` of the chart source,
`φ(x) P (ψ u) (x) = ∫ φ₁(e x) ψ₁(w) k(e x, w) u(e⁻¹ w) dw` for the kernel `k` of `r`. -/
private theorem mul_apply_mul_eq_integral_quantizationKernel {φ ψ φ₁ ψ₁ :
    𝓓(⟨e.target, e.open_target⟩, ℝ)} {r : Symbol n ℂ ℂ 0} (hr : r.IsSmoothing)
    (hop : ∀ (u : 𝓢(CoordinateSpace n, ℂ)) (z : CoordinateSpace n),
      quantizeSchwartzValue r.coefficient u z =
        e.complexChartCompression he φ ψ P (ContMDiffMap.ofContDiff u (u.smooth ⊤)) z)
    (hφ₁ : EqOn φ₁ 1 (tsupport φ)) (hψ₁ : EqOn ψ₁ 1 (tsupport ψ))
    (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) {x : M} (hx : x ∈ e.source) :
    e.complexCutoffPullback he φ 1 x * P (e.complexCutoffPullback he ψ 1 * u) x =
      ∫ w, ((φ₁ (e x) * ψ₁ w : ℝ) : ℂ) * quantizationKernel r.coefficient (e x) w 1 *
        u (e.symm w) := by
  -- The Schwartz function `U = ψ₁ · (u ∘ e⁻¹)` satisfies `(ψ U) ∘ e = (ψ ∘ e) · u`.
  have hUc : HasCompactSupport (e.complexCutoffPushforward he ψ₁ u) := by
    rw [show ⇑(e.complexCutoffPushforward he ψ₁ u) = fun y ↦ ψ₁ y • u (e.symm y) from
      funext (e.complexCutoffPushforward_apply he ψ₁ u)]
    exact ψ₁.hasCompactSupport.smul_right
  set U : 𝓢(CoordinateSpace n, ℂ) := hUc.toSchwartzMap
    (contMDiff_iff_contDiff.1 (e.complexCutoffPushforward he ψ₁ u).contMDiff)
  have hU (w : CoordinateSpace n) : U w = ψ₁ w • u (e.symm w) :=
    (HasCompactSupport.toSchwartzMap_toFun _ _ w).trans (e.complexCutoffPushforward_apply he ψ₁ u w)
  have hpull : e.complexCutoffPullback he ψ (ContMDiffMap.ofContDiff U (U.smooth ⊤)) =
      e.complexCutoffPullback he ψ 1 * u := by
    ext p
    by_cases hp : p ∈ e.source
    · rw [ContMDiffMap.coe_mul, Pi.mul_apply, e.complexCutoffPullback_apply_of_mem he _ _ hp,
        e.complexCutoffPullback_apply_of_mem he _ _ hp, ContMDiffMap.coe_ofContDiff, hU,
        e.left_inv hp]
      by_cases hψp : ψ (e p) = 0
      · simp [hψp]
      · simp [hψ₁ (subset_tsupport _ hψp)]
    · simp [e.complexCutoffPullback_apply_of_notMem he _ _ hp]
  -- So `φ(x) P (ψ u) (x) = Op(r) U (e x)`, which is `φ(e x)` times a number, and `φ₁ = 1` where
  -- `φ ≠ 0`. The kernel representation of `Op(r) U` gives the integral.
  have h := hop U (e x)
  rw [e.complexChartCompression_apply he, hpull, e.left_inv hx,
    quantizeSchwartzValue_eq_integral_quantizationKernel (hr.integrable_coefficient (e x))] at h
  have hφx : e.complexCutoffPullback he φ 1 x * P (e.complexCutoffPullback he ψ 1 * u) x =
      (φ₁ (e x) : ℂ) * (φ (e x) • P (e.complexCutoffPullback he ψ 1 * u) x) := by
    rw [e.complexCutoffPullback_apply_of_mem he _ _ hx, ContMDiffMap.coe_one, Pi.one_apply]
    by_cases hφx : φ (e x) = 0
    · simp [hφx]
    · simp [hφ₁ (subset_tsupport _ hφx), Complex.real_smul]
  rw [hφx, ← h, ← integral_const_mul]
  refine integral_congr_ae (.of_forall fun w ↦ ?_)
  dsimp only
  rw [show quantizationKernel r.coefficient (e x) w (U w) =
      U w * quantizationKernel r.coefficient (e x) w 1 by
    simpa using (quantizationKernel r.coefficient (e x) w).map_smul (U w) 1, hU, Complex.real_smul]
  push_cast
  ring

omit [ChartedSpace (CoordinateSpace n) M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M] in
/-- **A kernel read in a chart.** Let `μ` have the density `ρ` in the chart `e`, and let `K` be a
continuous function on `M × M` equal to `F (e x, e y)` on the product of the chart sources and to
`0` elsewhere, where `F (z, w)` vanishes for `w` outside a compact subset of the chart target. Then
`∫ K(x, y) u(y) dμ(y) = ∫_{e.target} ρ(w) F(e x, w) u(e⁻¹ w) dw` at points `x` of the chart
source. -/
private theorem integral_mul_eq_setIntegral {ρ : CoordinateSpace n → ℝ}
    (hint : ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
      ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y))
    {K : M × M → ℂ} (hK : Continuous K) {F : CoordinateSpace n × CoordinateSpace n → ℂ}
    (hKF : ∀ p ∈ e.source ×ˢ e.source, K p = F (e p.1, e p.2))
    (hK0 : ∀ p ∉ e.source ×ˢ e.source, K p = 0) {B : Set (CoordinateSpace n)} (hB : IsCompact B)
    (hBt : B ⊆ e.target) (hFB : ∀ z, ∀ w ∉ B, F (z, w) = 0) {u : M → ℂ} (hu : Continuous u)
    {x : M} (hx : x ∈ e.source) :
    ∫ y, K (x, y) * u y ∂μ = ∫ w in e.target, (ρ w : ℂ) * F (e x, w) * u (e.symm w) := by
  -- The integrand vanishes off the compact set `e⁻¹(B)` inside the chart source.
  have hB' : IsCompact (e.symm '' B) := hB.image_of_continuousOn (e.continuousOn_symm.mono hBt)
  have hfB : ∀ y ∉ e.symm '' B, K (x, y) * u y = 0 := fun y hy ↦ by
    by_cases hys : y ∈ e.source
    · rw [hKF (x, y) ⟨hx, hys⟩, hFB _ _ fun h ↦ hy ⟨_, h, e.left_inv hys⟩, zero_mul]
    · rw [hK0 (x, y) fun h ↦ hys h.2, zero_mul]
  rw [hint (fun y ↦ K (x, y) * u y) ((hK.comp (continuous_const.prodMk continuous_id)).mul hu)
    (HasCompactSupport.intro hB' hfB) ((closure_minimal (Function.support_subset_iff'.2 hfB)
      hB'.isClosed).trans (image_subset_iff.2 fun w hw ↦ e.map_target (hBt hw)))]
  refine setIntegral_congr_fun e.open_target.measurableSet fun w hw ↦ ?_
  simp only [hKF (x, e.symm w) ⟨hx, e.map_target hw⟩, e.right_inv hw, mul_assoc]

omit [MeasurableSpace M] in
include he in
/-- A smooth function `F` on `ℝⁿ × ℝⁿ` with compact support in the product of the chart targets of
`e`, read on `M × M` through the chart in both variables and extended by `0`, is a smooth
compactly supported function on `M × M`. -/
private theorem exists_contMDiff_eq_comp_prodMap {F : CoordinateSpace n × CoordinateSpace n → ℂ}
    (hF : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F) (hFt : tsupport F ⊆ e.target ×ˢ e.target) :
    ∃ K : M × M → ℂ,
      ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞ K ∧
        HasCompactSupport K ∧ (∀ p ∈ e.source ×ˢ e.source, K p = F (e p.1, e p.2)) ∧
          ∀ p ∉ e.source ×ˢ e.source, K p = 0 := by
  -- `K` is `F` read through the product chart `e × e` of the maximal atlas of `M × M`.
  set I2 := 𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)
  have hEt : tsupport F ⊆ ((e.prod e).extend I2).target := fun p hp ↦ by
    simp [I2, (hFt hp).1, (hFt hp).2]
  refine ⟨(e.prod e).source.indicator (F ∘ (e.prod e).extend I2),
    OpenPartialHomeomorph.contMDiff_indicator_comp_extend
      (H := ModelProd (CoordinateSpace n) (CoordinateSpace n))
      (IsManifold.mem_maximalAtlas_prod he he) hF hFc hEt,
    (hFc.isCompact.image_of_continuousOn
      ((e.prod e).continuousOn_extend_symm.mono hEt)).of_isClosed_subset (isClosed_tsupport _)
      (OpenPartialHomeomorph.tsupport_indicator_comp_extend_subset
        (H := ModelProd (CoordinateSpace n) (CoordinateSpace n)) hFc hEt),
    fun p hp ↦ by simp [I2, hp], fun p hp ↦ indicator_of_notMem (by simpa using hp) _⟩

/-- **An operator of order `-∞` has a smooth kernel in a chart.** Let `μ` have a density `ρ` in a
chart `e` of the maximal atlas, smooth and nonzero on the chart target:
`∫ f dμ = ∫_{e.target} ρ(y) f(e⁻¹ y) dy` for continuous compactly supported functions `f`
supported in the chart source. If `P` has order `-∞` and `φ`, `ψ` are cutoffs in the chart
target, read on `M` through the chart, there is a smooth compactly supported function `K` on
`M × M` with `φ(x) P (ψ u) (x) = ∫ K(x, y) u(y) dμ(y)` for every smooth `u`. -/
theorem exists_contMDiff_forall_mul_apply_mul_eq_integral
    (hP : P ∈ smoothingPseudodifferentialOperators) {ρ : CoordinateSpace n → ℝ}
    (hρ : ContDiffOn ℝ ∞ ρ e.target) (hρ0 : ∀ y ∈ e.target, ρ y ≠ 0)
    (hint : ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
      ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y))
    (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) :
    ∃ K : M × M → ℂ,
      ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞ K ∧
        HasCompactSupport K ∧ ∀ (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M),
          e.complexCutoffPullback he φ 1 x * P (e.complexCutoffPullback he ψ 1 * u) x =
            ∫ y, K (x, y) * u y ∂μ := by
  -- The compression of `P` by `φ` and `ψ` is `Op(r)` for a smoothing symbol `r`, with smooth
  -- kernel `k`. Take cutoffs `φ₁ = 1` near the support of `φ` and `ψ₁ = 1` near that of `ψ`.
  obtain ⟨r, hr, hop⟩ := ((mem_smoothingPseudodifferentialOperators_iff_isSmoothing 0).1 hP).2
    e he φ ψ
  set k := quantizationKernel r.coefficient
  obtain ⟨φ₁, hφ₁, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤)
    φ.hasCompactSupport.isCompact φ.tsupport_subset
  obtain ⟨ψ₁, hψ₁, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤)
    ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  -- The kernel in the chart is `F(z, w) = φ₁(z) θ(w) k(z, w)`, with `θ = ψ₁ / ρ`. It vanishes
  -- off the compact set `supp φ₁ × supp θ` inside the product of the chart targets.
  set θ : CoordinateSpace n → ℝ := fun w ↦ ψ₁ w • (ρ w)⁻¹
  have hθt : tsupport θ ⊆ e.target :=
    (tsupport_smul_subset_left (f := ⇑ψ₁) _).trans ψ₁.tsupport_subset
  have hθc : HasCompactSupport θ := ψ₁.hasCompactSupport.smul_right
  set F : CoordinateSpace n × CoordinateSpace n → ℂ := fun p ↦
    ((φ₁ p.1 * θ p.2 : ℝ) : ℂ) * k p.1 p.2 1
  have hF : ContDiff ℝ ∞ F := (Complex.ofRealCLM.contDiff.comp ((φ₁.contDiff.comp contDiff_fst).mul
    ((ContDiffOn.contDiff_smul_of_tsupport_subset (hρ.inv hρ0) e.open_target
      ψ₁.contDiff.contDiffOn ψ₁.tsupport_subset).comp contDiff_snd))).mul
    (((ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).restrictScalars ℝ).contDiff.comp
      hr.contDiff_quantizationKernel)
  have hFt : tsupport F ⊆ tsupport φ₁ ×ˢ tsupport θ :=
    closure_minimal (fun p hp ↦ ⟨subset_tsupport _ fun h ↦ hp (by simp [F, h]),
      subset_tsupport _ fun h ↦ hp (by simp [F, h])⟩)
      ((isClosed_tsupport _).prod (isClosed_tsupport _))
  have hFc : HasCompactSupport F :=
    (φ₁.hasCompactSupport.isCompact.prod hθc.isCompact).of_isClosed_subset (isClosed_tsupport _) hFt
  -- Read on `M × M` through the chart in both variables, `F` is the kernel `K`.
  obtain ⟨K, hKs, hKc, hKF, hK0⟩ := exists_contMDiff_eq_comp_prodMap he hF hFc
    (hFt.trans (prod_mono φ₁.tsupport_subset hθt))
  refine ⟨K, hKs, hKc, fun u x ↦ ?_⟩
  by_cases hx : x ∉ e.source
  · -- Off the chart source both sides vanish.
    have hKx (y : M) : K (x, y) = 0 := hK0 (x, y) fun h ↦ hx h.1
    simp [e.complexCutoffPullback_apply_of_notMem he _ _ hx, hKx]
  -- On it, both sides are integrals over the chart target, and `θ ρ = ψ₁` there.
  push Not at hx
  rw [mul_apply_mul_eq_integral_quantizationKernel he hr hop
      (fun y hy ↦ hφ₁.self_of_nhdsSet y hy) (fun y hy ↦ hψ₁.self_of_nhdsSet y hy) u hx,
    integral_mul_eq_setIntegral hint hKs.continuous hKF hK0 hθc.isCompact hθt
      (fun z w hw ↦ by simp [F, image_eq_zero_of_notMem_tsupport hw]) u.contMDiff.continuous hx,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.target) fun w hw ↦ by
      simp [image_eq_zero_of_notMem_tsupport fun h ↦ hw (ψ₁.tsupport_subset h)]]
  refine setIntegral_congr_fun e.open_target.measurableSet fun w hw ↦ ?_
  have hρw : (ρ w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hρ0 w hw)
  simp only [F, θ, k, smul_eq_mul]
  push_cast
  field_simp

end Chart

/-! ### On a compact manifold -/

omit [MeasurableSpace M] in
/-- **Splitting operators into chart pieces.** On a nonempty compact manifold of positive dimension
there are finitely many charts `Eᵢⱼ` of the maximal atlas, with cutoffs `φᵢⱼ` and `ψᵢⱼ` in their
targets, such that every complex-linear operator `P` on the smooth functions is
`P = ∑ᵢⱼ φᵢⱼ P ψᵢⱼ`, the cutoffs being read on `M` through the charts. The `φᵢⱼ` come from a
partition of unity `ρᵢ` subordinate to charts, and for each `i` the `ψᵢⱼ` from a partition of unity
`σᵢⱼ` with `ρᵢ` and `σᵢⱼ` both supported in the source of `Eᵢⱼ`. -/
private theorem exists_forall_apply_eq_sum_mul_apply_mul [CompactSpace M] [NeZero n] [Nonempty M] :
    ∃ (ι : Type u) (_ : Fintype ι) (κ : ι → Type u) (_ : ∀ i, Fintype (κ i))
      (E : ∀ i, κ i → OpenPartialHomeomorph M (CoordinateSpace n))
      (hE : ∀ i j, E i j ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
      (φ ψ : ∀ i j, 𝓓(⟨(E i j).target, (E i j).open_target⟩, ℝ)),
      ∀ (P : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯ →ₗ[ℂ]
        C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (u) (x : M),
        P u x = ∑ i, ∑ j, (E i j).complexCutoffPullback (hE i j) (φ i j) 1 x *
          P ((E i j).complexCutoffPullback (hE i j) (ψ i j) 1 * u) x := by
  classical
  -- A partition of unity `ρᵢ` on `M`, each `ρᵢ` supported in the source of a chart `eᵢ`.
  obtain ⟨ι, _, ρ, e, hρ1, he⟩ :=
    (isCompact_univ : IsCompact (univ : Set M)).exists_smoothPartition_mem_maximalAtlas_eqOn_symm
      (IsManifold.chart_mem_maximalAtlas (Classical.arbitrary M))
      (isCompact_empty (X := CoordinateSpace n)) (empty_subset _)
  choose he hρc hρe _ _ using he
  -- For each `i`, a partition of unity `σᵢⱼ` on `M`, with `σᵢⱼ` supported in the source of a chart
  -- `Eᵢⱼ` that agrees with `eᵢ` on `eᵢ(supp ρᵢ)`. So `ρᵢ` is supported in that source too.
  choose κ _ σ E hσ1 hE using fun i ↦
    (isCompact_univ : IsCompact (univ : Set M)).exists_smoothPartition_mem_maximalAtlas_eqOn_symm
      (he i) ((hρc i).image_of_continuousOn ((e i).continuousOn.mono (hρe i)))
      (image_subset_iff.2 fun p hp ↦ (e i).map_source (hρe i hp))
  choose hE hσc hσE hCE hEe using hE
  have hρE (i : ι) (j : κ i) : tsupport (ρ i) ⊆ (E i j).source := fun p hp ↦ by
    rw [← (e i).left_inv (hρe i hp), ← hEe i j (mem_image_of_mem _ hp)]
    exact (E i j).map_target (hCE i j (mem_image_of_mem _ hp))
  -- The functions `ρᵢ` and `σᵢⱼ` are cutoffs `φᵢⱼ` and `ψᵢⱼ` in the chart `Eᵢⱼ`, read on `M`.
  choose φ hφ using fun i j ↦ (E i j).exists_cutoffPullback_one_eq (hE i j) (hρc i) (hρE i j)
  choose ψ hψ using fun i j ↦ (E i j).exists_cutoffPullback_one_eq (hE i j) (hσc i j) (hσE i j)
  refine ⟨ι, inferInstance, κ, inferInstance, E, hE, φ, ψ, fun P u x ↦ ?_⟩
  -- `P u = ∑ᵢ ρᵢ P u = ∑ᵢ ∑ⱼ ρᵢ P (σᵢⱼ u)`.
  calc P u x = ∑ i, (ρ i x : ℂ) * P u x := by
        rw [← Finset.sum_mul, ← Complex.ofReal_sum, hρ1 x (mem_univ x), Complex.ofReal_one,
          one_mul]
    _ = _ := Finset.sum_congr rfl fun i _ ↦ by
        have hu : u = ∑ j, (E i j).complexCutoffPullback (hE i j) (ψ i j) 1 * u := by
          ext p
          simp only [ContMDiffMap.coe_sum, ContMDiffMap.coe_mul, Finset.sum_apply, Pi.mul_apply,
            OpenPartialHomeomorph.complexCutoffPullback_one_apply, hψ, ← Finset.sum_mul,
            ← Complex.ofReal_sum, hσ1 i p (mem_univ p), Complex.ofReal_one, one_mul]
        conv_lhs => rw [hu]
        rw [map_sum, ContMDiffMap.coe_sum, Finset.sum_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [OpenPartialHomeomorph.complexCutoffPullback_one_apply, hφ]

/-- **On a compact manifold, an operator of order `-∞` is an integral operator with a smooth
kernel.** Let `M` be a compact manifold modelled on `ℝⁿ`, `n ≠ 0`, and `μ` a measure on `M`, finite
on compact sets, with a smooth nonvanishing density in every chart `e` of the maximal atlas: there
is `ρ`, smooth and nonzero on the chart target, with `∫ f dμ = ∫_{e.target} ρ(y) f(e⁻¹ y) dy` for
continuous compactly supported functions `f` supported in the chart source. Then for every operator
`P` of order `-∞` there is a smooth function `K` on `M × M` with
`P u (x) = ∫ K(x, y) u(y) dμ(y)` for every smooth `u` and every `x`. -/
theorem exists_contMDiff_forall_apply_eq_integral_of_mem_smoothingPseudodifferentialOperators
    [CompactSpace M] [NeZero n] [OpensMeasurableSpace M] [IsFiniteMeasureOnCompacts μ]
    (hμ : ∀ e : OpenPartialHomeomorph M (CoordinateSpace n),
      e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M →
        ∃ ρ : CoordinateSpace n → ℝ, ContDiffOn ℝ ∞ ρ e.target ∧ (∀ y ∈ e.target, ρ y ≠ 0) ∧
          ∀ f : M → ℂ, Continuous f → HasCompactSupport f → tsupport f ⊆ e.source →
            ∫ x, f x ∂μ = ∫ y in e.target, (ρ y : ℂ) * f (e.symm y))
    (hP : P ∈ smoothingPseudodifferentialOperators) :
    ∃ K : M × M → ℂ,
      ContMDiff (𝓘(ℝ, CoordinateSpace n).prod 𝓘(ℝ, CoordinateSpace n)) 𝓘(ℝ, ℂ) ∞ K ∧
        ∀ (u : C^∞⟮𝓘(ℝ, CoordinateSpace n), M; 𝓘(ℝ, ℂ), ℂ⟯) (x : M),
          P u x = ∫ y, K (x, y) * u y ∂μ := by
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨0, contMDiff_const, fun u x ↦ isEmptyElim x⟩
  -- Split `P` as `∑ᵢⱼ φᵢⱼ P ψᵢⱼ`; each piece has a smooth kernel `Kᵢⱼ`, and `K = ∑ᵢⱼ Kᵢⱼ`.
  obtain ⟨ι, _, κ, _, E, hE, φ, ψ, hsplit⟩ :=
    exists_forall_apply_eq_sum_mul_apply_mul (n := n) (M := M)
  choose ρ hρ hρ0 hint using fun i j ↦ hμ (E i j) (hE i j)
  choose K hK _ hKu using fun i j ↦ exists_contMDiff_forall_mul_apply_mul_eq_integral (hE i j) hP
    (hρ i j) (hρ0 i j) (hint i j) (φ i j) (ψ i j)
  refine ⟨∑ i, ∑ j, K i j, contMDiff_finsetSum' fun i _ ↦ contMDiff_finsetSum' fun j _ ↦ hK i j,
    fun u x ↦ ?_⟩
  have hK1 (i : ι) (j : κ i) : Integrable (fun y ↦ K i j (x, y) * u y) μ :=
    Continuous.integrable_of_hasCompactSupport
      (((hK i j).continuous.comp (continuous_const.prodMk continuous_id)).mul
        u.contMDiff.continuous) (HasCompactSupport.of_compactSpace _)
  simp only [hsplit P u x, hKu, Finset.sum_apply, Finset.sum_mul]
  rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hK1 i j]
  exact Finset.sum_congr rfl fun i _ ↦ (integral_finsetSum _ fun j _ ↦ hK1 i j).symm

end TauCeti
