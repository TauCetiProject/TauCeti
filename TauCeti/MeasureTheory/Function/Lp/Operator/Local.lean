/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import TauCeti.MeasureTheory.Function.Lp.DominatedConvergence
import TauCeti.MeasureTheory.Function.Lp.Indicator
import TauCeti.MeasureTheory.Function.Lp.Restriction
import TauCeti.MeasureTheory.Function.LpSeminorm.Multiplier
import TauCeti.MeasureTheory.Measure.Regular

/-!
# Local operators on `Lᵖ` are multiplication operators

Let `S` be a bounded linear operator from `Lᵖ(α, E)` to `Lᵖ(α, F)`. Call `S` **local** when it
does not enlarge supports: whenever `f` vanishes almost everywhere off a measurable set `s`, so
does `S f`. Multiplication by an essentially bounded operator-valued function, `f ↦ x ↦ m x (f x)`,
is local. This file proves the converse for `1 ≤ p < ∞` on a σ-finite measure space, when `E` is
finite-dimensional and separable: a local operator is a multiplication operator, with a symbol
`m : α → E →L[𝕜] F` of essential supremum at most `‖S‖`.

The argument has three steps. A local operator commutes with the restriction `f ↦ 1_s f` to every
measurable set (`ContinuousLinearMap.ae_eq_indicator_apply_of_forall_ae_eq_zero`), since `f` is
the sum of `1_s f`, which vanishes off `s`, and `1_{sᶜ} f`, which vanishes on `s`. Hence on each
piece `D` of a countable partition of `α` into sets of finite measure, `S (1_A v) = 1_A S (1_D v)`
for `A` of finite measure and `v ∈ E`, so the values `S (1_D bᵢ)` on a basis `bᵢ` of `E` define the
symbol on `D`. Testing `S` on `1_A v` bounds the symbol by `‖S‖`, and the identity
`S f = m f`, known for the indicator classes `1_A v`, extends to all of `Lᵖ` by density of simple
functions.

The finite-dimensionality of `E` is needed for the symbol to be strongly measurable: on `L²([0,1],
ℓ²(ℤ))` the local operator given at `x` by the diagonal unitary with entries `exp (2πinx)` is
multiplication only by a function that is not almost everywhere separably valued in operator
norm. The case `p = ∞` is excluded, since simple functions supported on sets of finite measure are
not dense in `L∞`.

The main application is to singular integral operators. A bounded operator on `Lᵖ` given off the
support of its argument by integration against a kernel `K` is determined by `K` only up to a
local operator: two operators with the same kernel differ by a bounded multiplication operator.
This is why the theory of Calderón–Zygmund operators treats the operator, and not its kernel, as
the primitive datum.

## Main declarations

* `ContinuousLinearMap.ae_eq_indicator_apply_of_forall_ae_eq_zero`: a local operator commutes with
  restriction to measurable sets.
* `ContinuousLinearMap.ae_norm_le_of_forall_apply_indicatorConstLp_ae_eq`: an operator agreeing on
  indicator classes with multiplication by `m` bounds `‖m x‖` almost everywhere by its norm.
* `ContinuousLinearMap.exists_forall_ae_eq_apply_of_forall_ae_eq_zero`: a local operator is the
  multiplication operator of an operator-valued symbol of essential supremum at most `‖S‖`.
* `ContinuousLinearMap.ae_apply_eq_zero_of_forall_isCompact`,
  `ContinuousLinearMap.exists_forall_ae_eq_apply_of_forall_isCompact`: for a measure inner regular
  with respect to compact sets, locality only has to be checked on compact sets.
* `ContinuousLinearMap.exists_forall_ae_eq_add_of_forall_isCompact`: two operators agreeing off
  the compact support of their argument differ by a bounded multiplication operator.
* `ContinuousLinearMap.exists_forall_ae_eq_add_of_ae_eq_integral`: in particular, two operators
  given off the support of their argument by the same kernel differ by a bounded multiplication
  operator.

## References

* E. M. Stein, *Harmonic Analysis*, Chapter VII, §3, and L. Grafakos, *Classical Fourier
  Analysis*, Section 5.3, for bounded operators given off the diagonal by a kernel.
-/

public section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace ContinuousLinearMap

variable {α 𝕜 E F : Type*} [MeasurableSpace α] {μ : Measure α}
  [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **A local operator commutes with restriction.** Let `S` be a bounded operator from
`Lᵖ(α, E)` to `Lᵖ(α, F)` that is local: whenever `f` vanishes almost everywhere off a measurable
set, so does `S f`. If `g` is the restriction `1_s f` of `f` to a measurable set `s`, up to
almost everywhere equality, then `S g` is the restriction `1_s (S f)` of `S f`. -/
theorem ae_eq_indicator_apply_of_forall_ae_eq_zero (S : Lp E p μ →L[𝕜] Lp F p μ)
    (hS : ∀ (f : Lp E p μ) (s : Set α), MeasurableSet s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → S f x = 0)
    {s : Set α} (hs : MeasurableSet s) {f g : Lp E p μ} (hg : g =ᵐ[μ] s.indicator f) :
    S g =ᵐ[μ] s.indicator (S f) := by
  have h₁ := hS g s hs (hg.mono fun x hx hxs ↦ by rw [hx, indicator_of_notMem hxs])
  have h₂ := hS (f - g) sᶜ hs.compl (by
    filter_upwards [hg, Lp.coeFn_sub f g] with x hx hfg hxs
    rw [hfg, Pi.sub_apply, hx, indicator_of_mem (not_not.1 hxs), sub_self])
  have h₃ := Lp.coeFn_sub (S f) (S g)
  rw [← map_sub] at h₃
  filter_upwards [h₁, h₂, h₃] with x hx₁ hx₂ hx₃
  by_cases hxs : x ∈ s
  · rw [indicator_of_mem hxs]
    exact (sub_eq_zero.1 (hx₃.symm.trans (hx₂ (not_not.2 hxs)))).symm
  · rw [indicator_of_notMem hxs, hx₁ hxs]

/-- On a set `t` of finite measure, a local operator acts on the indicator class `1_s v` of a set
`s` of finite measure as the restriction to `s` of its action on `1_t v`. -/
private theorem ae_restrict_apply_indicatorConstLp_eq (S : Lp E p μ →L[𝕜] Lp F p μ)
    (hS : ∀ (f : Lp E p μ) (s : Set α), MeasurableSet s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → S f x = 0)
    {s t : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (ht : MeasurableSet t) (hμt : μ t ≠ ∞)
    (v : E) :
    S (indicatorConstLp p hs hμs v) =ᵐ[μ.restrict t]
      s.indicator (S (indicatorConstLp p ht hμt v)) := by
  have hμst : μ (s ∩ t) ≠ ∞ := (measure_mono inter_subset_left).trans_lt hμs.lt_top |>.ne
  -- `S (1_{s ∩ t} v)` is the restriction of `S (1_w v)` to `r`, for `{w, r} = {s, t}`.
  have hk {w r : Set α} (hw : MeasurableSet w) (hμw : μ w ≠ ∞) (hr : MeasurableSet r)
      (hwr : s ∩ t = w ∩ r) :
      S (indicatorConstLp p (hs.inter ht) hμst v) =ᵐ[μ]
        r.indicator (S (indicatorConstLp p hw hμw v)) := by
    refine S.ae_eq_indicator_apply_of_forall_ae_eq_zero hS hr ?_
    filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hs.inter ht) (hμs := hμst) (c := v),
      indicatorConstLp_coeFn (p := p) (hs := hw) (hμs := hμw) (c := v)] with x hx hx'
    rw [hx, hwr]
    by_cases hxw : x ∈ w <;> by_cases hxr : x ∈ r <;> simp [hxw, hxr, hx']
  filter_upwards [ae_restrict_mem ht, ae_restrict_of_ae (hk hs hμs ht rfl),
    ae_restrict_of_ae (hk ht hμt hs (inter_comm s t))] with x hxt hx₁ hx₂
  rw [← hx₂, hx₁, indicator_of_mem hxt]

/-- **A multiplication operator bounds its symbol.** Let `1 ≤ p < ∞`, let `μ` be σ-finite and let
`E` be separable. If a bounded operator `S` from `Lᵖ(α, E)` to `Lᵖ(α, F)` acts on every indicator
class `1_s v` as multiplication by an a.e. strongly measurable operator-valued function `m`, then
`‖m x‖ ≤ ‖S‖` for almost every `x`. -/
theorem ae_norm_le_of_forall_apply_indicatorConstLp_ae_eq [SigmaFinite μ]
    [TopologicalSpace.SeparableSpace E] (hp : p ≠ ∞) (S : Lp E p μ →L[𝕜] Lp F p μ)
    {m : α → E →L[𝕜] F} (hm : AEStronglyMeasurable m μ)
    (hmS : ∀ (s : Set α) (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (v : E),
      S (indicatorConstLp p hs hμs v) =ᵐ[μ] fun x ↦ m x (s.indicator (fun _ ↦ v) x)) :
    ∀ᵐ x ∂μ, ‖m x‖ ≤ ‖S‖ := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hv (v : E) : ∀ᵐ x ∂μ, ‖m x v‖ₑ ≤ ‖S‖ₑ * ‖v‖ₑ := by
    have ha : AEStronglyMeasurable (fun x ↦ m x v) μ :=
      (apply 𝕜 F v).continuous.comp_aestronglyMeasurable hm
    have hind (s : Set α) (hs : MeasurableSet s) (hμs : μ s < ∞) :
        eLpNorm (s.indicator fun x ↦ m x v) p μ ≤ ‖S‖ₑ * ‖v‖ₑ * μ s ^ (1 / p.toReal) := by
      have hSs : eLpNorm (s.indicator fun x ↦ m x v) p μ =
          ‖S (indicatorConstLp p hs hμs.ne v)‖ₑ := by
        rw [Lp.eNorm_def]
        refine eLpNorm_congr_ae ?_
        filter_upwards [hmS s hs hμs.ne v] with x hx
        by_cases hxs : x ∈ s <;> simp [hx, hxs]
      rw [hSs, mul_assoc, ← eLpNorm_indicator_const hs.nullMeasurableSet hp₀ hp,
        ← eLpNorm_congr_ae indicatorConstLp_coeFn, ← Lp.eNorm_def]
      exact S.le_opENorm _
    have h := eLpNorm_top_le_of_forall_eLpNorm_indicator_le ha hp₀ hp hind
    rw [eLpNorm_exponent_top ha] at h
    filter_upwards [ae_le_eLpNormEssSup (f := fun x ↦ m x v) (μ := μ)] with x hx
    exact hx.trans h
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq E
  filter_upwards [ae_all_iff.2 fun k ↦ hv (u k)] with x hx
  refine opNorm_le_bound _ (norm_nonneg _) fun v ↦ ?_
  have hclosed : IsClosed {v | ‖m x v‖ ≤ ‖S‖ * ‖v‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  refine hclosed.closure_subset_iff.2 (range_subset_iff.2 fun k ↦ ?_) (hu.closure_eq ▸ mem_univ v)
  simpa [← ofReal_norm, ← ENNReal.ofReal_mul, ENNReal.ofReal_le_ofReal_iff, mul_nonneg] using hx k

section Symbol

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]

/-- In the coordinates of a basis `b` of `E`, the class `S (1_t v)` depends linearly on `v`: it is
`x ↦ m x v` for the operator `m x` sending `bᵢ` to `S (1_t bᵢ) x`. -/
private theorem coeFn_apply_indicatorConstLp_ae_eq {ι : Type*} [Fintype ι]
    (b : Module.Basis ι 𝕜 E) (S : Lp E p μ →L[𝕜] Lp F p μ) {t : Set α} (ht : MeasurableSet t)
    (hμt : μ t ≠ ∞) (v : E) :
    S (indicatorConstLp p ht hμt v) =ᵐ[μ] fun x ↦
      (∑ i, (b.coord i).toContinuousLinearMap.smulRight (S (indicatorConstLp p ht hμt (b i)) x))
        v := by
  have h : S (indicatorConstLp p ht hμt v) =
      ∑ i, b.repr v i • S (indicatorConstLp p ht hμt (b i)) := by
    conv_lhs => rw [← b.sum_repr v, ← TauCeti.indicatorConstLpₗ_apply 𝕜, map_sum, map_sum]
    simp
  rw [h]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      fun i ↦ b.repr v i • S (indicatorConstLp p ht hμt (b i)),
    ae_all_iff.2 fun i ↦ Lp.coeFn_smul (b.repr v i) (S (indicatorConstLp p ht hμt (b i)))]
    with x h₁ h₂
  rw [h₁]
  simp [h₂]

/-- A local operator acts on indicator classes `1_s v` as multiplication by a strongly measurable
operator-valued function. -/
private theorem exists_stronglyMeasurable_forall_apply_indicatorConstLp_ae_eq [SigmaFinite μ]
    (S : Lp E p μ →L[𝕜] Lp F p μ)
    (hS : ∀ (f : Lp E p μ) (s : Set α), MeasurableSet s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → S f x = 0) :
    ∃ m : α → E →L[𝕜] F, StronglyMeasurable m ∧ ∀ (s : Set α) (hs : MeasurableSet s)
      (hμs : μ s ≠ ∞) (v : E),
      S (indicatorConstLp p hs hμs v) =ᵐ[μ] fun x ↦ m x (s.indicator (fun _ ↦ v) x) := by
  classical
  set b := Module.finBasis 𝕜 E
  have hD : ∀ n, MeasurableSet (disjointed (spanningSets μ) n) :=
    MeasurableSet.disjointed (measurableSet_spanningSets μ)
  have hμD : ∀ n, μ (disjointed (spanningSets μ) n) ≠ ∞ := fun n ↦
    ((measure_mono (disjointed_subset _ n)).trans_lt (measure_spanningSets_lt_top μ n)).ne
  -- On the `n`-th piece of the partition, the symbol is read off from `S (1_{Dₙ} bᵢ)`.
  obtain ⟨M, hM⟩ : ∃ M : ℕ → α → E →L[𝕜] F, M = fun n x ↦
      ∑ i, (b.coord i).toContinuousLinearMap.smulRight
        (S (indicatorConstLp p (hD n) (hμD n) (b i)) x) := ⟨_, rfl⟩
  refine ⟨fun x ↦ M (spanningSetsIndex μ x) x, ?_, fun s hs hμs v ↦ ?_⟩
  · have hMm : StronglyMeasurable (Function.uncurry M) := hM ▸
      stronglyMeasurable_uncurry_of_countable fun n ↦ Finset.stronglyMeasurable_fun_sum _
        fun i _ ↦ ((smulRightL 𝕜 𝕜 𝕜 E F (b.coord i).toContinuousLinearMap).continuous
          |>.comp_stronglyMeasurable (Lp.stronglyMeasurable _))
    exact hMm.comp_measurable ((measurableSet_spanningSetsIndex μ).prodMk measurable_id)
  have h (n : ℕ) : S (indicatorConstLp p hs hμs v) =ᵐ[μ.restrict (disjointed (spanningSets μ) n)]
      fun x ↦ M (spanningSetsIndex μ x) x (s.indicator (fun _ ↦ v) x) := by
    filter_upwards [ae_restrict_mem (hD n),
      ae_restrict_apply_indicatorConstLp_eq S hS hs hμs (hD n) (hμD n) v,
      ae_restrict_of_ae (coeFn_apply_indicatorConstLp_ae_eq b S (hD n) (hμD n) v)]
      with x hxD hx₁ hx₂
    rw [(spanningSetsIndex_eq_iff μ).2 hxD, hx₁]
    by_cases hxs : x ∈ s
    · simp [hxs, hx₂, hM]
    · simp [hxs]
  have h' := (ae_eq_restrict_iUnion_iff (μ := μ) _ _ _).2 h
  rwa [iUnion_disjointed, iUnion_spanningSets, Measure.restrict_univ] at h'

/-- **Local operators are multiplication operators.** Let `1 ≤ p < ∞`, let `μ` be σ-finite and
let `E` be finite-dimensional and separable. If a bounded operator `S` from `Lᵖ(α, E)` to
`Lᵖ(α, F)` is local, that is, `S f` vanishes almost everywhere off every measurable set off which
`f` vanishes, then `S` is multiplication by a strongly measurable operator-valued function `m` of
essential supremum at most `‖S‖`: `S f = m f` almost everywhere for every `f`. -/
theorem exists_forall_ae_eq_apply_of_forall_ae_eq_zero [SigmaFinite μ]
    [TopologicalSpace.SeparableSpace E] (hp : p ≠ ∞) (S : Lp E p μ →L[𝕜] Lp F p μ)
    (hS : ∀ (f : Lp E p μ) (s : Set α), MeasurableSet s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → S f x = 0) :
    ∃ m : α → E →L[𝕜] F, StronglyMeasurable m ∧ (∀ᵐ x ∂μ, ‖m x‖ ≤ ‖S‖) ∧
      ∀ f : Lp E p μ, S f =ᵐ[μ] fun x ↦ m x (f x) := by
  obtain ⟨m, hm, hmS⟩ := exists_stronglyMeasurable_forall_apply_indicatorConstLp_ae_eq S hS
  have hbound := ae_norm_le_of_forall_apply_indicatorConstLp_ae_eq hp S hm.aestronglyMeasurable hmS
  refine ⟨m, hm, hbound, ?_⟩
  -- The multiplication operator `f ↦ m f` is bounded on `Lᵖ`, and agrees with `S` on the
  -- indicator classes, which span a dense subspace.
  have hmL : MemLp m ∞ μ := memLp_top_of_bound hm.aestronglyMeasurable ‖S‖ hbound
  set M := (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).holderL μ ∞ p p hmL.toLp
  have hM (f : Lp E p μ) : M f =ᵐ[μ] fun x ↦ m x (f x) := by
    filter_upwards [(ContinuousLinearMap.id 𝕜 (E →L[𝕜] F)).coeFn_holder (r := p) hmL.toLp f,
      hmL.coeFn_toLp] with x hx hx'
    simp [M, hx, hx']
  have key (f : Lp E p μ) : S f = M f := by
    refine Lp.induction hp (fun f ↦ S f = M f) (fun v s hs hμs ↦ ?_)
      (fun f g _ _ _ hf hg ↦ by rw [map_add, map_add, hf, hg])
      (isClosed_eq S.continuous M.continuous) f
    rw [Lp.simpleFunc.coe_indicatorConst]
    refine Lp.ext ((hmS s hs hμs.ne v).trans ?_)
    filter_upwards [hM (indicatorConstLp p hs hμs.ne v),
      indicatorConstLp_coeFn (p := p) (hs := hs) (hμs := hμs.ne) (c := v)] with x hx hx'
    rw [hx, hx']
  exact fun f ↦ (Lp.ext_iff.1 (key f)).trans (hM f)

end Symbol

section Compact

variable [TopologicalSpace α] [OpensMeasurableSpace α] [T2Space α] [μ.InnerRegularCompactLTTop]
  [SigmaFinite μ]

/-- **Locality can be tested on compact sets.** Let `μ` be σ-finite and inner regular with respect
to compact sets on sets of finite measure, and let `p < ∞`. If a bounded operator `S` from
`Lᵖ(α, E)` to `Lᵖ(α, F)` maps every `f` vanishing almost everywhere off a compact set `K` to a
class vanishing almost everywhere off `K`, then the same holds with any measurable set in place
of `K`. -/
theorem ae_apply_eq_zero_of_forall_isCompact (hp : p ≠ ∞) (S : Lp E p μ →L[𝕜] Lp F p μ)
    (hS : ∀ (f : Lp E p μ) (K : Set α), IsCompact K → (∀ᵐ x ∂μ, x ∉ K → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ K → S f x = 0)
    (f : Lp E p μ) {s : Set α} (hs : MeasurableSet s) (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0) :
    ∀ᵐ x ∂μ, x ∉ s → S f x = 0 := by
  -- Exhaust `s`, up to a null set, by the increasing compact sets `accumulate K n`.
  obtain ⟨t, hts, ⟨K, hK, rfl⟩, hst⟩ :=
    hs.nullMeasurableSet.exists_isSigmaCompact_subset_ae_eq (μ := μ)
  have hL (n : ℕ) : IsCompact (accumulate K n) := isCompact_accumulate hK n
  have hmem (n : ℕ) : MemLp ((accumulate K n).indicator f) p μ :=
    (Lp.memLp f).indicator (hL n).isClosed.measurableSet.nullMeasurableSet
  have htend : Tendsto (fun n ↦ (hmem n).toLp _) atTop (𝓝 f) := by
    refine TauCeti.tendsto_toLp_of_ae_tendsto_of_norm_le hp hmem (u := f) .rfl
      (fun n ↦ .of_forall fun x ↦ norm_indicator_le_norm_self _ _) ?_
    filter_upwards [hf, hst.mem_iff] with x hx hxt
    by_cases hxs : x ∈ s
    · obtain ⟨n, hn⟩ := mem_iUnion.1 (hxt.2 hxs)
      exact tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n, fun m hm ↦
        (indicator_of_mem (monotone_accumulate hm (subset_accumulate hn)) _).symm⟩)
    · rw [hx hxs]
      exact tendsto_const_nhds.congr fun n ↦ (indicator_apply_eq_zero.2 fun _ ↦ hx hxs).symm
  refine (Lp.isClosed_setOf_ae_notMem_imp_eq_zero s).mem_of_tendsto
    ((S.continuous.tendsto f).comp htend) (.of_forall fun n ↦ ?_)
  filter_upwards [hS _ _ (hL n) (by
    filter_upwards [(hmem n).coeFn_toLp] with x hx hxn
    rw [hx, indicator_of_notMem hxn])] with x hx hxs
  exact hx fun hxn ↦ hxs (hts (accumulate_subset_iUnion n hxn))

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] [TopologicalSpace.SeparableSpace E]

/-- **Operators local on compact sets are multiplication operators.** Let `μ` be σ-finite and
inner regular with respect to compact sets on sets of finite measure, let `1 ≤ p < ∞` and let `E`
be finite-dimensional and separable. If a bounded operator `S` from `Lᵖ(α, E)` to `Lᵖ(α, F)` maps
every `f` vanishing almost everywhere off a compact set `K` to a class vanishing almost
everywhere off `K`, then `S` is multiplication by a strongly measurable operator-valued function
`m` of essential supremum at most `‖S‖`. -/
theorem exists_forall_ae_eq_apply_of_forall_isCompact (hp : p ≠ ∞)
    (S : Lp E p μ →L[𝕜] Lp F p μ)
    (hS : ∀ (f : Lp E p μ) (K : Set α), IsCompact K → (∀ᵐ x ∂μ, x ∉ K → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ K → S f x = 0) :
    ∃ m : α → E →L[𝕜] F, StronglyMeasurable m ∧ (∀ᵐ x ∂μ, ‖m x‖ ≤ ‖S‖) ∧
      ∀ f : Lp E p μ, S f =ᵐ[μ] fun x ↦ m x (f x) :=
  S.exists_forall_ae_eq_apply_of_forall_ae_eq_zero hp fun f _ hs hf ↦
    S.ae_apply_eq_zero_of_forall_isCompact hp hS f hs hf

/-- **Operators agreeing off supports differ by a multiplication operator.** Let `μ` be σ-finite
and inner regular with respect to compact sets on sets of finite measure, let `1 ≤ p < ∞` and let
`E` be finite-dimensional and separable. Let `T` and `T'` be bounded operators from `Lᵖ(α, E)` to
`Lᵖ(α, F)` that agree off the support of their argument: whenever `f` vanishes almost everywhere
off a compact set `K`, `T f x = T' f x` for almost every `x ∉ K`. Then `T = T' + m` for a strongly
measurable operator-valued function `m` of essential supremum at most `‖T - T'‖`. -/
theorem exists_forall_ae_eq_add_of_forall_isCompact (hp : p ≠ ∞)
    (T T' : Lp E p μ →L[𝕜] Lp F p μ)
    (hTT' : ∀ (f : Lp E p μ) (K : Set α), IsCompact K → (∀ᵐ x ∂μ, x ∉ K → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ K → T f x = T' f x) :
    ∃ m : α → E →L[𝕜] F, StronglyMeasurable m ∧ (∀ᵐ x ∂μ, ‖m x‖ ≤ ‖T - T'‖) ∧
      ∀ f : Lp E p μ, T f =ᵐ[μ] fun x ↦ T' f x + m x (f x) := by
  obtain ⟨m, hm, hmT, hTm⟩ := (T - T').exists_forall_ae_eq_apply_of_forall_isCompact hp
    fun f K hK hf ↦ by
      filter_upwards [hTT' f K hK hf, Lp.coeFn_sub (T f) (T' f)] with x hx hsub hxK
      rw [sub_apply, hsub, Pi.sub_apply, hx hxK, sub_self]
  refine ⟨m, hm, hmT, fun f ↦ ?_⟩
  filter_upwards [hTm f, Lp.coeFn_sub (T f) (T' f)] with x hx hsub
  rw [← hx, sub_apply, hsub, Pi.sub_apply, add_sub_cancel]

/-- **Operators with the same kernel differ by a multiplication operator.** Let `μ` be σ-finite
and inner regular with respect to compact sets on sets of finite measure, let `1 ≤ p < ∞` and let
`E` be finite-dimensional and separable. Let `T` and `T'` be bounded operators from `Lᵖ(α, E)` to
`Lᵖ(α, F)` given off the support of their argument by the same kernel `k`: whenever `f` vanishes
almost everywhere off a compact set `K`, `T f x = ∫ k x y (f y) dy = T' f x` for almost every
`x ∉ K`. Then `T = T' + m` for a strongly measurable operator-valued function `m` of essential
supremum at most `‖T - T'‖`: the kernel determines the operator only up to a bounded
multiplication operator. -/
theorem exists_forall_ae_eq_add_of_ae_eq_integral [NormedSpace ℝ F] (hp : p ≠ ∞)
    (T T' : Lp E p μ →L[𝕜] Lp F p μ) (k : α → α → E →L[𝕜] F)
    (hT : ∀ (f : Lp E p μ) (K : Set α), IsCompact K → (∀ᵐ x ∂μ, x ∉ K → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ K → T f x = ∫ y, k x y (f y) ∂μ)
    (hT' : ∀ (f : Lp E p μ) (K : Set α), IsCompact K → (∀ᵐ x ∂μ, x ∉ K → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ K → T' f x = ∫ y, k x y (f y) ∂μ) :
    ∃ m : α → E →L[𝕜] F, StronglyMeasurable m ∧ (∀ᵐ x ∂μ, ‖m x‖ ≤ ‖T - T'‖) ∧
      ∀ f : Lp E p μ, T f =ᵐ[μ] fun x ↦ T' f x + m x (f x) :=
  T.exists_forall_ae_eq_add_of_forall_isCompact hp T' fun f K hK hf ↦ by
    filter_upwards [hT f K hK hf, hT' f K hK hf] with x hx hx' hxK
    rw [hx hxK, hx' hxK]

end Compact

end ContinuousLinearMap
