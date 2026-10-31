/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Uniform approximation by simple functions

Mathlib's `MeasureTheory.SimpleFunc.approxOn f hf s y₀ h₀` is a sequence of simple functions with
values in `s` converging pointwise to a measurable function `f` whose values lie in the closure of
the separable set `s` (`MeasureTheory.SimpleFunc.tendsto_approxOn`). When `s` is totally bounded
the convergence is uniform: finitely many points of the dense sequence underlying `approxOn`
already form an `ε`-net of `closure s`, and from then on every approximant is within `ε` of `f`.

Thus a measurable function with totally bounded range, such as a bounded measurable function into
a finite-dimensional normed space, is a uniform limit of measurable finite-range functions whose
values stay in any prescribed totally bounded set containing its range. This is the
approximation behind integration of bounded measurable functions against projection-valued
measures, where uniform rather than pointwise control is needed. It also shows that simple
functions are dense in real `L∞` for any measure: an essentially bounded function has a bounded
measurable representative.

## Main statements

* `MeasureTheory.SimpleFunc.tendstoUniformlyOn_nearestPt` — nearest-point projections onto the
  initial segments of a sequence converge uniformly to the identity on every totally bounded set
  in the closure of the sequence.
* `MeasureTheory.SimpleFunc.tendstoUniformly_approxOn` — for totally bounded `s`, the simple
  approximants `approxOn f hf s y₀ h₀ n` converge to `f` uniformly.
* `MeasureTheory.SimpleFunc.toLpTop μ 𝕜`: the class in `L∞(μ)` of a simple function, as a linear
  map.
* `MeasureTheory.SimpleFunc.denseRange_toLpTop` — simple functions are dense in real `L∞`.
-/

public section

open Filter Set TopologicalSpace
open scoped ENNReal

namespace MeasureTheory.SimpleFunc

variable {α β : Type*} [MeasurableSpace α] [PseudoEMetricSpace α] [OpensMeasurableSpace α]

/-- The nearest-point projections `nearestPt e N` onto `{e 0, …, e N}` converge to the identity
uniformly on every totally bounded set contained in the closure of the range of `e`. -/
theorem tendstoUniformlyOn_nearestPt {e : ℕ → α} {S : Set α} (hS : TotallyBounded S)
    (hSe : S ⊆ closure (range e)) :
    TendstoUniformlyOn (fun N ↦ ⇑(nearestPt e N)) id atTop S := by
  refine EMetric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
  obtain ⟨t, htS, ht, hSt⟩ := EMetric.totallyBounded_iff'.1 hS (ε / 2) (ENNReal.half_pos hε.ne')
  -- each point `z` of the finite `ε / 2`-net is within `ε / 2` of some `e k`; once `N ≥ k`, the
  -- nearest point to any `y` within `ε / 2` of `z` is at least as close to `y` as `e k` is
  have hnet : ∀ z ∈ t, ∀ᶠ N in atTop, ∀ y ∈ Metric.eball z (ε / 2),
      edist y (nearestPt e N y) < ε := by
    intro z hz
    obtain ⟨-, ⟨k, rfl⟩, hk⟩ :=
      EMetric.mem_closure_iff.1 (hSe (htS hz)) (ε / 2) (ENNReal.half_pos hε.ne')
    filter_upwards [eventually_ge_atTop k] with N hN y hy
    calc edist y (nearestPt e N y) = edist (nearestPt e N y) y := edist_comm _ _
      _ ≤ edist (e k) y := edist_nearestPt_le e y hN
      _ ≤ edist (e k) z + edist z y := edist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by
        gcongr
        · rwa [edist_comm]
        · rwa [edist_comm, ← Metric.mem_eball]
      _ = ε := ENNReal.add_halves ε
  filter_upwards [(eventually_all_finite ht).2 hnet] with N hN y hy
  obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.1 (hSt hy)
  exact hN z hz y hyz

variable [MeasurableSpace β]

/-- If `s` is totally bounded, the simple approximants `approxOn f hf s y₀ h₀ n` of a measurable
function `f` with values in the closure of `s` converge to `f` uniformly. -/
theorem tendstoUniformly_approxOn {f : β → α} (hf : Measurable f) {s : Set α} {y₀ : α}
    (h₀ : y₀ ∈ s) [SeparableSpace s] (hs : TotallyBounded s) (hfs : ∀ x, f x ∈ closure s) :
    TendstoUniformly (fun n ↦ ⇑(approxOn f hf s y₀ h₀ n)) f atTop := by
  have : Nonempty s := ⟨⟨y₀, h₀⟩⟩
  -- the points used by `approxOn` are `y₀` followed by the dense sequence of `s`
  have hsub : closure s ⊆ closure (range fun k ↦ (Nat.casesOn k y₀ ((↑) ∘ denseSeq s) : α)) := by
    refine closure_minimal (fun y hy ↦ closure_mono (s := range ((↑) ∘ denseSeq s)) ?_ ?_)
      isClosed_closure
    · rintro _ ⟨k, rfl⟩
      exact ⟨k + 1, rfl⟩
    · rw [range_comp]
      exact image_closure_subset_closure_image continuous_subtype_val
        ⟨⟨y, hy⟩, (denseRange_denseSeq s).closure_range ▸ mem_univ _, rfl⟩
  rw [← tendstoUniformlyOn_univ]
  simpa only [approxOn, coe_comp, Function.id_comp] using
    ((tendstoUniformlyOn_nearestPt hs.closure hsub).comp f).mono fun x _ ↦ hfs x

end MeasureTheory.SimpleFunc

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace SimpleFunc

variable (μ) (𝕜 : Type*) {E : Type*} [NormedAddCommGroup E] [NormedRing 𝕜] [Module 𝕜 E]
  [IsBoundedSMul 𝕜 E] in
/-- The class in `L∞(μ)` of a simple function, as a linear map. This is Mathlib's
`MeasureTheory.SimpleFunc.toLp` at exponent `∞`, where every simple function is essentially
bounded whatever the measure. -/
noncomputable def toLpTop : SimpleFunc α E →ₗ[𝕜] Lp E ∞ μ where
  toFun f := (f.memLp_top μ).toLp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The class of a simple function in `L∞` is almost everywhere the function. -/
theorem coeFn_toLpTop {𝕜 E : Type*} [NormedAddCommGroup E] [NormedRing 𝕜] [Module 𝕜 E]
    [IsBoundedSMul 𝕜 E] (f : SimpleFunc α E) : toLpTop μ 𝕜 f =ᵐ[μ] f :=
  MemLp.coeFn_toLp (f.memLp_top μ)

/-- Simple functions are dense in real `L∞`, for any measure: an essentially bounded function
has a bounded measurable representative, which is a uniform limit of simple functions. -/
theorem denseRange_toLpTop : DenseRange (toLpTop μ ℝ : SimpleFunc α ℝ →ₗ[ℝ] Lp ℝ ∞ μ) := by
  intro φ
  set C := ‖φ‖
  -- A measurable representative of `φ`, truncated to `[-C, C]` where it exceeds the bound.
  have hφ := Lp.aestronglyMeasurable φ
  set f : α → ℝ := fun x => max (-C) (min (hφ.mk φ x) C) with hf_def
  have hf : Measurable f :=
    measurable_const.max (hφ.stronglyMeasurable_mk.measurable.min measurable_const)
  have hfC (x : α) : f x ∈ Metric.closedBall (0 : ℝ) C := by
    have : 0 ≤ C := norm_nonneg φ
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_le, hf_def]
    constructor <;> [exact le_max_left _ _; exact max_le (by linarith) (min_le_right _ _)]
  have hφf : φ =ᵐ[μ] f := by
    filter_upwards [hφ.ae_eq_mk, Lp.ae_norm_le_norm_top φ] with x h hx
    rw [Real.norm_eq_abs, abs_le] at hx
    simp only [hf_def]
    rw [← h, min_eq_left hx.2, max_eq_right hx.1]
  -- The simple approximants of `f` converge to it uniformly.
  have h₀ : (0 : ℝ) ∈ Metric.closedBall 0 C := Metric.mem_closedBall_self (norm_nonneg φ)
  have hunif := tendstoUniformly_approxOn hf h₀ (isCompact_closedBall (0 : ℝ) C).totallyBounded
    fun x => subset_closure (hfC x)
  refine mem_closure_of_tendsto (b := atTop) (f := fun n => toLpTop μ ℝ (approxOn f hf _ 0 h₀ n)) ?_
    (Eventually.of_forall fun n => Set.mem_range_self _)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformly_iff.1 hunif (ε / 2) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  refine (Lp.norm_top_le_of_ae_bound (by positivity) ?_).trans_lt (half_lt_self hε)
  filter_upwards [Lp.coeFn_sub (toLpTop μ ℝ (approxOn f hf _ 0 h₀ n)) φ,
    coeFn_toLpTop (μ := μ) (𝕜 := ℝ) (approxOn f hf _ 0 h₀ n), hφf] with x hsub hx hφx
  rw [hsub, Pi.sub_apply, hx, hφx, ← dist_eq_norm, dist_comm]
  exact (hN n hn x).le

end SimpleFunc

end MeasureTheory
