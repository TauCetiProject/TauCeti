/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.Pseudodifferential.Kernel
public import TauCeti.Analysis.Pseudodifferential.Manifold.Smoothing
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Geometry.Manifold.ContMDiff.ChartCutoff
import TauCeti.Geometry.Manifold.Measure.Chart

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
  (`TauCeti.exists_forall_apply_eq_sum_complexCutoffPullback_mul_apply_mul`). When `σᵢⱼ` is
  supported far from `ρᵢ`, the chart `eᵢⱼ` has two components with disjoint images in `ℝⁿ`: the
  class of operators of order `-∞` is defined by chart compressions in every chart of the maximal
  atlas, and these are the charts that see how `P` connects two distant points. Each piece
  `ρᵢ P σᵢⱼ` has a smooth kernel by the chart statement, and `K` is their sum.

Classically the converse also holds, so that on a compact manifold the operators of order `-∞` are
exactly the integral operators with smooth kernels (Hörmander III, §18.1); that converse is not
formalized here. Operators of order `-∞` are the remainders of the elliptic parametrices on a
compact base.

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
  set U := e.cutoffPushforwardSchwartz he ψ₁ u
  have hU (w : CoordinateSpace n) : U w = ψ₁ w • u (e.symm w) :=
    e.cutoffPushforwardSchwartz_apply he ψ₁ u w
  -- So `φ(x) P (ψ u) (x) = Op(r) U (e x)`, which is `φ(e x)` times a number, and `φ₁ = 1` where
  -- `φ ≠ 0`. The kernel representation of `Op(r) U` gives the integral.
  have h := hop U (e x)
  rw [e.complexChartCompression_apply he,
    e.complexCutoffPullback_cutoffPushforwardSchwartz he hψ₁ u, e.left_inv hx,
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
  obtain ⟨K, hKs, hKc, hKF, hK0⟩ := e.exists_contMDiff_eq_comp_prodMap he he hF hFc
    (by simpa using hFt.trans (prod_mono φ₁.tsupport_subset hθt))
  refine ⟨K, hKs, hKc, fun u x ↦ ?_⟩
  by_cases hx : x ∉ e.source
  · -- Off the chart source both sides vanish.
    simp [e.complexCutoffPullback_apply_of_notMem he _ _ hx, fun y ↦ hK0 (x, y) fun h ↦ hx h.1]
  -- On it, both sides are integrals over the chart target, and `θ ρ = ψ₁` there.
  push Not at hx
  rw [mul_apply_mul_eq_integral_quantizationKernel he hr hop
      (fun y hy ↦ hφ₁.self_of_nhdsSet y hy) (fun y hy ↦ hψ₁.self_of_nhdsSet y hy) u hx,
    integral_mul_eq_setIntegral_target hint hKs.continuous (by simpa using hKF) hK0 hθc.isCompact
      hθt (fun z w hw ↦ by simp [F, image_eq_zero_of_notMem_tsupport hw]) u.contMDiff.continuous hx,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := e.target) fun w hw ↦ by
      simp [image_eq_zero_of_notMem_tsupport fun h ↦ hw (ψ₁.tsupport_subset h)]]
  refine setIntegral_congr_fun e.open_target.measurableSet fun w hw ↦ ?_
  have hρw : (ρ w : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hρ0 w hw)
  simp only [F, θ, k, smul_eq_mul]
  push_cast
  field_simp

end Chart

/-! ### On a compact manifold -/

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
    exists_forall_apply_eq_sum_complexCutoffPullback_mul_apply_mul (E := CoordinateSpace n) (M := M)
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
