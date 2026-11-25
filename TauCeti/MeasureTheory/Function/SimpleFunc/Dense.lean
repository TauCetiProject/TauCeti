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
functions are dense in `L∞` with values in a proper normed group, such as a finite-dimensional
normed space, for any measure: an essentially bounded function has a bounded measurable
representative.

## Main statements

* `MeasureTheory.SimpleFunc.tendstoUniformlyOn_nearestPt` — nearest-point projections onto the
  initial segments of a sequence converge uniformly to the identity on every totally bounded set
  in the closure of the sequence.
* `MeasureTheory.SimpleFunc.tendstoUniformly_approxOn` — for totally bounded `s`, the simple
  approximants `approxOn f hf s y₀ h₀ n` converge to `f` uniformly.
* `MeasureTheory.SimpleFunc.toLpTop μ 𝕜`: the class in `L∞(μ)` of a simple function, as a linear
  map.
* `MeasureTheory.SimpleFunc.denseRange_toLpTop` — simple functions are dense in `L∞` with values
  in a proper normed group.
* `MeasureTheory.SimpleFunc.integrable_toLp` — the class in `Lᵖ`, `0 < p < ∞`, of a simple
  function is integrable.
* `MeasureTheory.SimpleFunc.eLpNorm_eq_top_of_not_memLp` — a simple function outside `Lᵖ` for one
  exponent `p` has infinite `L^q` norm for every `0 < q < ∞`.
* `MeasureTheory.Lp.simpleFunc.memLp_toSimpleFunc_of_ne_top` — a simple function of `Lᵖ`,
  `0 < p < ∞`, lies in every `Lʳ`.
* `MeasureTheory.Lp.simpleFunc.memLp_of_ne_top` — the same statement for the function itself.
* `MeasureTheory.Lp.dense_setOf_memLp` — for `1 ≤ p < ∞`, the functions of `Lᵖ` that also lie in
  `Lʳ` are dense in `Lᵖ`.
* `MeasureTheory.Lp.continuousLinearMap_ext_of_memLp` — two continuous semilinear maps out of
  `Lᵖ`, `1 ≤ p < ∞`, that agree on `Lᵖ ∩ Lʳ` are equal.
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
    rw [Nat.range_casesOn, range_comp]
    exact closure_minimal ((Subtype.dense_iff.1 (denseRange_denseSeq s)).trans
      (closure_mono subset_union_right)) isClosed_closure
  rw [← tendstoUniformlyOn_univ]
  simpa only [approxOn, coe_comp, Function.id_comp] using
    ((tendstoUniformlyOn_nearestPt hs.closure hsub).comp f).mono fun x _ ↦ hfs x

end MeasureTheory.SimpleFunc

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace SimpleFunc

variable {𝕜 E : Type*} [NormedAddCommGroup E] [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

variable (μ 𝕜) in
/-- The class in `L∞(μ)` of a simple function, as a linear map. This is Mathlib's
`MeasureTheory.SimpleFunc.toLp` at exponent `∞`, where every simple function is essentially
bounded whatever the measure. -/
noncomputable def toLpTop : SimpleFunc α E →ₗ[𝕜] Lp E ∞ μ where
  toFun f := (f.memLp_top μ).toLp f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The class of a simple function in `L∞` is almost everywhere the function. -/
theorem coeFn_toLpTop (f : SimpleFunc α E) : toLpTop μ 𝕜 f =ᵐ[μ] f :=
  MemLp.coeFn_toLp (f.memLp_top μ)

/-- Simple functions are dense in `L∞` with values in a proper normed group, such as a
finite-dimensional normed space, for any measure: an essentially bounded function has a bounded
measurable representative, which is a uniform limit of simple functions. -/
theorem denseRange_toLpTop [ProperSpace E] :
    DenseRange (toLpTop μ 𝕜 : SimpleFunc α E →ₗ[𝕜] Lp E ∞ μ) := by
  borelize E
  intro φ
  set C := ‖φ‖
  -- A measurable representative of `φ`, replaced by `0` where it exceeds the bound `C`.
  have hφ := Lp.aestronglyMeasurable φ
  have hg : Measurable (hφ.mk φ) := hφ.stronglyMeasurable_mk.measurable
  set f : α → E := fun x => if ‖hφ.mk φ x‖ ≤ C then hφ.mk φ x else 0
  have hf : Measurable f := hg.ite (measurableSet_le hg.norm measurable_const) measurable_const
  have hfC (x : α) : f x ∈ Metric.closedBall (0 : E) C := by
    simp only [f, mem_closedBall_zero_iff]
    split_ifs with h
    exacts [h, norm_zero.le.trans (norm_nonneg φ)]
  have hφf : φ =ᵐ[μ] f := by
    filter_upwards [hφ.ae_eq_mk, Lp.ae_norm_le_norm_top φ] with x h hx
    exact h.trans (ite_eq_left (h ▸ hx)).symm
  -- The simple approximants of `f` converge to it uniformly.
  have h₀ : (0 : E) ∈ Metric.closedBall 0 C := Metric.mem_closedBall_self (norm_nonneg φ)
  have hunif := tendstoUniformly_approxOn hf h₀ (isCompact_closedBall (0 : E) C).totallyBounded
    fun x => subset_closure (hfC x)
  refine mem_closure_of_tendsto (b := atTop) (f := fun n => toLpTop μ 𝕜 (approxOn f hf _ 0 h₀ n)) ?_
    (Eventually.of_forall fun n => Set.mem_range_self _)
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformly_iff.1 hunif (ε / 2) (by positivity))
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm]
  refine (Lp.norm_le_of_ae_bound_top (by positivity) ?_).trans_lt (half_lt_self hε)
  filter_upwards [Lp.coeFn_sub (toLpTop μ 𝕜 (approxOn f hf _ 0 h₀ n)) φ,
    coeFn_toLpTop (μ := μ) (𝕜 := 𝕜) (approxOn f hf _ 0 h₀ n), hφf] with x hsub hx hφx
  rw [hsub, Pi.sub_apply, hx, hφx, ← dist_eq_norm, dist_comm]
  exact (hN n hn x).le

/-- The class in `Lᵖ`, `0 < p < ∞`, of a simple function is integrable: a simple function in `Lᵖ`
has support of finite measure. -/
theorem integrable_toLp {p : ℝ≥0∞} {f : SimpleFunc α E} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hf : MemLp f p μ) : Integrable (hf.toLp f) μ :=
  ((memLp_iff_integrable hp0 hp).1 hf).congr hf.coeFn_toLp.symm

/-- A simple function outside `Lᵖ` for one exponent `p` has infinite `L^q` norm for every
`0 < q < ∞`. -/
theorem eLpNorm_eq_top_of_not_memLp {p q : ℝ≥0∞} {f : SimpleFunc α E} (hq0 : q ≠ 0)
    (hq : q ≠ ∞) (hf : ¬MemLp f p μ) : eLpNorm f q μ = ∞ := by
  by_contra h
  refine hf ?_
  rcases eq_or_ne p 0 with rfl | hp0
  · exact memLp_zero_iff_aestronglyMeasurable.2 f.aestronglyMeasurable
  rcases eq_or_ne p ∞ with rfl | hp
  · exact f.memLp_top μ
  exact (SimpleFunc.memLp_iff hp0 hp).2
    ((SimpleFunc.memLp_iff hq0 hq).1 (MeasureTheory.memLp_iff.2 (Ne.lt_top h)))

end SimpleFunc

/-- A simple function of `Lᵖ`, `0 < p < ∞`, has support of finite measure, so it lies in every
`Lʳ`. -/
theorem Lp.simpleFunc.memLp_toSimpleFunc_of_ne_top {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (r : ℝ≥0∞) (f : Lp.simpleFunc E p μ) :
    MemLp (Lp.simpleFunc.toSimpleFunc f) r μ :=
  SimpleFunc.memLp_of_finite_measure_preimage r <|
    SimpleFunc.measure_preimage_lt_top_of_memLp hp0 hp _ (Lp.simpleFunc.memLp f)

/-- A simple function of `Lᵖ`, `0 < p < ∞`, lies in every `Lʳ` as a function. -/
theorem Lp.simpleFunc.memLp_of_ne_top {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (r : ℝ≥0∞) (f : Lp.simpleFunc E p μ) :
    MemLp (f : α → E) r μ :=
  (memLp_toSimpleFunc_of_ne_top hp0 hp r f).ae_eq (toSimpleFunc_eq_toFun f)

/-- For `1 ≤ p < ∞`, the functions of `Lᵖ` that also lie in `Lʳ` are dense in `Lᵖ`: they contain
the simple functions. -/
theorem Lp.dense_setOf_memLp {E : Type*} [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (r : ℝ≥0∞) : Dense {f : Lp E p μ | MemLp f r μ} :=
  (Lp.simpleFunc.denseRange hp).mono <| range_subset_iff.2 <|
    Lp.simpleFunc.memLp_of_ne_top (zero_lt_one.trans_le Fact.out).ne' hp r

/-- Two continuous semilinear maps out of `Lᵖ`, `1 ≤ p < ∞`, that agree on `Lᵖ ∩ Lʳ` are
equal, because the simple functions of `Lᵖ` lie in `Lʳ` and are dense in `Lᵖ`. -/
theorem Lp.continuousLinearMap_ext_of_memLp {𝕜 R E G : Type*} [NormedRing 𝕜] [Semiring R]
    {σ : 𝕜 →+* R} [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [AddCommMonoid G]
    [Module R G] [TopologicalSpace G] [T2Space G] {p r : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞)
    {S S' : Lp E p μ →SL[σ] G} (h : ∀ f : Lp E p μ, MemLp f r μ → S f = S' f) : S = S' :=
  DFunLike.coe_injective <|
    S.continuous.ext_on (Lp.dense_setOf_memLp hp r) S'.continuous fun f hf => h f hf

end MeasureTheory
