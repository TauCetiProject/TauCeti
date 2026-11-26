/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Module.PositiveLinearMap
public import Mathlib.MeasureTheory.Function.LpOrder
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.Lp.Exponent
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# Restriction and set integration on finite-measure sets

This file provides the continuous map from `Lᵖ` to `L¹` obtained by restricting to a
finite-measure set, together with the corresponding set-integral map.  These constructions are
useful whenever an `Lᵖ` identity is tested against integrals on finite-measure sets. It also
collects facts about restricting `Lᵖ` classes and their representatives to measurable or
finite-measure sets.

## Main declarations

* `TauCeti.tendsto_setLIntegral_enorm_sub_of_tendsto_Lp`: convergence of representatives on a
  finite-measure set.
* `MeasureTheory.MemLp.coeFn_toLp_indicator_restrict`: recover a function from its zero extension
  on a measurable subset.

* `Set.LpToL1RestrictCLM`: restriction from `Lᵖ` to `L¹` on a finite-measure set.
* `Set.LpToL1RestrictCLM_coeFn`: the restricted class has the original representative almost
  everywhere.
* `Set.setIntegralLp`: integration on a finite-measure set as a continuous linear map on
  `Lᵖ`.
* `Set.setIntegralLp_apply`: the pointwise formula for this map.
* `MeasureTheory.Lp.integralPositiveLinearMap`: integration against a finite measure as a
  positive linear functional on real `Lᵖ`.
* `TauCeti.totallyBounded_restrict_of_forall_eqOn`: restricting a totally bounded family of `Lᵖ`
  classes to a measurable set on which they agree with given functions.
* `TauCeti.tendsto_setLIntegral_enorm_sub_of_tendsto_Lp`: convergence of representatives on a
  finite-measure set.
* `TauCeti.setIntegral_norm_le_toReal_eLpNorm_restrict`: on a set of measure at most one, the
  integral of the norm is at most the `Lᵖ` norm.
* `MeasureTheory.MemLp.coeFn_toLp_indicator_restrict`: recover a function from its zero extension
  on a measurable subset.
* `MeasureTheory.Lp.toReal_eLpNorm_restrict_mono`: the `Lᵖ` seminorm of an element of `Lᵖ(Ω)` on
  subsets of `Ω` is monotone in the subset.
* `MeasureTheory.Lp.toReal_eLpNorm_restrict_le_norm`: the `Lᵖ` seminorm of an element of `Lᵖ(Ω)`
  on a subset of `Ω` is at most its norm.
* `MeasureTheory.Lp.isClosed_setOf_ae_notMem_imp_eq_zero`: the `Lᵖ` classes vanishing off a set
  form a closed set.
* `MeasureTheory.LpToLpRestrictCLM_eq_zero_iff`: the restriction of an `Lᵖ` class to a set vanishes
  exactly when the class vanishes almost everywhere on that set.
* `MeasureTheory.Lp.restrictOfSubsetL`: the restriction `Lᵖ(μ|t) → Lᵖ(μ|s)` for `s ⊆ t`, with
  `MeasureTheory.Lp.coeFn_restrictOfSubsetL`, the bound
  `MeasureTheory.Lp.norm_restrictOfSubsetL_le` and its compatibility
  `MeasureTheory.Lp.restrictOfSubsetL_LpToLpRestrictCLM` with `MeasureTheory.LpToLpRestrictCLM`.
* `MeasureTheory.MemLp.integrableOn_of_subset` and
  `MeasureTheory.MemLp.integrableOn_norm_sub_sq_of_subset`: a function in `Lᵖ(t)`, `1 ≤ p`, is
  integrable on every subset of `t` of finite measure, and for `p = 2` so is its squared distance
  to any constant.
* `MeasureTheory.MemLp.setIntegral_norm_sq_le_eLpNorm_sq_mul_measureReal_rpow`: Hölder's
  inequality bounding the integral of `‖g‖²` over a subset `s ⊆ t` of finite measure by
  `‖g‖²_{L^q(t)} μ(s)^{1 - 2/q}`, `2 ≤ q`.
-/

public section

noncomputable section

namespace Set

open ContinuousLinearMap Filter MeasureTheory Set
open scoped ENNReal

variable {E F 𝕜 : Type*} [MeasurableSpace E]
  [NormedAddCommGroup F] [NormedRing 𝕜] [Module 𝕜 F] [IsBoundedSMul 𝕜 F]
  {μ : Measure E} {p : ENNReal} [Fact (1 ≤ p)]

/-- Restrict an `Lᵖ` class to a finite-measure set and view it as an `L¹` class. -/
def LpToL1RestrictCLM (s : Set E) (hμs : μ s < ∞) :
    Lp F p μ →L[𝕜] Lp F 1 (μ.restrict s) := by
  letI : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
  exact (Lp.ofExponentLEL (ν := μ.restrict s) 𝕜 F (Fact.out : 1 ≤ p)).comp
    (LpToLpRestrictCLM E F 𝕜 μ p s)

/-- The restricted `L¹` class agrees almost everywhere with the original `Lᵖ` class. -/
theorem LpToL1RestrictCLM_coeFn (s : Set E) (hμs : μ s < ∞)
    (f : Lp F p μ) :
    LpToL1RestrictCLM (𝕜 := 𝕜) s hμs f =ᵐ[μ.restrict s] f := by
  let _ : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
  rw [LpToL1RestrictCLM, ContinuousLinearMap.comp_apply, Lp.coeFn_ofExponentLEL]
  exact LpToLpRestrictCLM_coeFn 𝕜 s f

variable [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F] [CompleteSpace F]

/-- Integrate an `Lᵖ` class over a finite-measure set as a continuous linear map. -/
def setIntegralLp (s : Set E) (hμs : μ s < ∞) :
    Lp F p μ →L[𝕜] F :=
  (L1.integralCLM' 𝕜 (α := E) (E := F) (μ := μ.restrict s)).comp
    (LpToL1RestrictCLM (𝕜 := 𝕜) s hμs)

/-- The set integral of an `Lᵖ` class agrees with the integral of its representative. -/
@[simp]
theorem setIntegralLp_apply (s : Set E) (hμs : μ s < ∞)
    (f : Lp F p μ) :
    setIntegralLp (𝕜 := 𝕜) s hμs f = ∫ x in s, f x ∂μ := by
  rw [setIntegralLp, ContinuousLinearMap.comp_apply, ← L1.integral_eq' 𝕜,
    L1.integral_eq_integral]
  exact integral_congr_ae (LpToL1RestrictCLM_coeFn s hμs f)

end Set

namespace MeasureTheory.Lp

open scoped ENNReal

variable {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ] (p : ℝ≥0∞)
  [Fact (1 ≤ p)]

/-- Integration against a finite measure, `φ ↦ ∫ x, φ x ∂μ`, as a positive linear functional on
real `Lᵖ`. This is the `Lᵖ` counterpart of
`CompactlySupportedContinuousMap.integralPositiveLinearMap`. -/
def integralPositiveLinearMap : Lp ℝ p μ →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (Set.setIntegralLp (𝕜 := ℝ) Set.univ (measure_lt_top μ _)).toLinearMap
    fun φ hφ => by
      simpa using integral_nonneg_of_ae ((Lp.coeFn_nonneg φ).2 hφ)

variable {μ p}

/-- The functional `integralPositiveLinearMap μ p` integrates a representative. -/
@[simp]
theorem integralPositiveLinearMap_apply (φ : Lp ℝ p μ) :
    integralPositiveLinearMap μ p φ = ∫ x, φ x ∂μ :=
  (Set.setIntegralLp_apply (𝕜 := ℝ) Set.univ (measure_lt_top μ _) φ).trans setIntegral_univ

end MeasureTheory.Lp

namespace TauCeti

open Filter _root_.MeasureTheory Set
open scoped ENNReal Topology

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
  {μ : Measure α} {p : ℝ≥0∞}

/-- Restricting a totally bounded family of `Lᵖ(μ)` classes `g u` to a measurable set `K` on which
`g u = u` gives a totally bounded family of `Lᵖ(μ|_K)` classes `u`. -/
theorem totallyBounded_restrict_of_forall_eqOn [Fact (1 ≤ p)] {K : Set α}
    (hK : MeasurableSet K) {S : Set (α → F)} {g : (α → F) → α → F}
    (hg : ∀ u ∈ S, MemLp (g u) p μ) (hgK : ∀ u ∈ S, ∀ x ∈ K, g u x = u x)
    (hT : TotallyBounded {f : Lp F p μ | ∃ u ∈ S, f =ᵐ[μ] g u}) :
    TotallyBounded {f : Lp F p (μ.restrict K) | ∃ u ∈ S, f =ᵐ[μ.restrict K] u} := by
  let res : Lp F p μ →+ Lp F p (μ.restrict K) :=
    AddMonoidHom.mk' (fun f => ((Lp.memLp f).restrict K).toLp f)
      fun f g => Lp_toLp_restrict_add f g K
  have hres_ae (f : Lp F p μ) : res f =ᵐ[μ.restrict K] f :=
    MemLp.coeFn_toLp ((Lp.memLp f).restrict K)
  have hres : UniformContinuous res :=
    AddMonoidHomClass.uniformContinuous_of_bound res 1 fun f => by
      rw [one_mul]
      exact norm_Lp_toLp_restrict_le K f
  refine (hT.image hres).subset ?_
  rintro f ⟨u, hu, hfu⟩
  refine ⟨(hg u hu).toLp _, ⟨u, hu, MemLp.coeFn_toLp _⟩, ?_⟩
  refine Lp.ext ?_
  filter_upwards [hres_ae ((hg u hu).toLp _), ae_restrict_of_ae (MemLp.coeFn_toLp (hg u hu)),
    ae_restrict_mem hK, hfu] with x h₁ h₂ hx h₃
  rw [h₁, h₂, h₃, hgK u hu x hx]

/-- `Lᵖ` convergence gives `L¹` convergence of representatives on every finite-measure set. -/
theorem tendsto_setLIntegral_enorm_sub_of_tendsto_Lp
    {E H ι : Type*} [MeasurableSpace E] [NormedAddCommGroup H]
    {μ : Measure E} {r : ℝ≥0∞} [Fact (1 ≤ r)] {W : Set E} (hW : μ W < ⊤)
    {l : Filter ι} {A : ι → Lp H r μ} {A₀ : Lp H r μ} (hA : Tendsto A l (𝓝 A₀))
    {a : ι → E → H} {a₀ : E → H} (ha : ∀ n, A n =ᵐ[μ] a n)
    (ha₀ : A₀ =ᵐ[μ.restrict W] a₀) :
    Tendsto (fun n => ∫⁻ x in W, ‖a n x - a₀ x‖ₑ ∂μ) l (𝓝 0) := by
  -- Hölder's inequality on the finite-measure set `W` bounds the `L¹(W)` distance by the `Lʳ` one.
  have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).1 hA
  have := isFiniteMeasure_restrict.2 hW.ne
  have hL1 : Tendsto (fun n => eLpNorm (⇑(A n) - ⇑A₀) 1 (μ.restrict W)) l (𝓝 0) :=
    TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm Fact.out
      (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le)
        fun n => eLpNorm_mono_measure _ Measure.restrict_le_self)
  refine hL1.congr fun n => ?_
  have hmeas : AEStronglyMeasurable (⇑(A n) - ⇑A₀) (μ.restrict W) :=
    ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)).mono_measure
      Measure.restrict_le_self
  rw [eLpNorm_one_eq_lintegral_eNorm hmeas]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae (ha n), ha₀] with x h₁ h₂
  rw [Pi.sub_apply, h₁, h₂]

/-- On a set of measure at most one, the integral of the norm is at most the `Lᵖ` norm, for
`1 ≤ p`. -/
theorem setIntegral_norm_le_toReal_eLpNorm_restrict (hp : 1 ≤ p) {s : Set α} (hs : μ s ≤ 1)
    {g : α → F} (hg : MemLp g p (μ.restrict s)) :
    ∫ x in s, ‖g x‖ ∂μ ≤ (eLpNorm g p (μ.restrict s)).toReal := by
  rw [integral_norm_eq_lintegral_eNorm hg.aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_eNorm hg.aestronglyMeasurable]
  refine ENNReal.toReal_mono hg.eLpNorm_ne_top <|
    (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hg.aestronglyMeasurable).trans ?_
  refine mul_le_of_le_one_right'
    (ENNReal.rpow_le_one ?_
      (ENNReal.one_div_toReal_sub_one_div_toReal_nonneg one_ne_zero hp))
  rwa [Measure.restrict_apply_univ]

end TauCeti

namespace MeasureTheory

/-- The class of a zero extension agrees with the original function on a measurable subset
of its original domain. -/
theorem MemLp.coeFn_toLp_indicator_restrict {E F : Type*} [MeasurableSpace E]
    [NormedAddCommGroup F] {μ : Measure E} {p : ENNReal} {s W : Set E} {f : E → F}
    (hf : MemLp (s.indicator f) p μ) (hW : MeasurableSet W) (hWs : W ⊆ s) :
    hf.toLp (s.indicator f) =ᵐ[μ.restrict W] f := by
  filter_upwards [ae_restrict_of_ae hf.coeFn_toLp, ae_restrict_mem hW] with x h₁ h₂
  rw [h₁, Set.indicator_of_mem (hWs h₂)]

/-- On nested sets `s ⊆ t ⊆ Ω`, the `Lᵖ` seminorm on `s` of an element of `Lᵖ(Ω)` is at most its
seminorm on `t`; both are finite, so the inequality holds for their real values. -/
theorem Lp.toReal_eLpNorm_restrict_mono {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
    {μ : Measure α} {p : ENNReal} {Ω : Set α} (g : Lp F p (μ.restrict Ω)) {s t : Set α}
    (hst : s ⊆ t) (htΩ : t ⊆ Ω) :
    (eLpNorm g p (μ.restrict s)).toReal ≤ (eLpNorm g p (μ.restrict t)).toReal :=
  ENNReal.toReal_mono ((eLpNorm_mono_measure _ (Measure.restrict_mono htΩ le_rfl)).trans_lt
    (Lp.eLpNorm_lt_top g)).ne (eLpNorm_mono_measure _ (Measure.restrict_mono hst le_rfl))

/-- On a subset `s ⊆ Ω`, the `Lᵖ` seminorm of an element of `Lᵖ(Ω)` is at most its norm. -/
theorem Lp.toReal_eLpNorm_restrict_le_norm {α F : Type*} [MeasurableSpace α]
    [NormedAddCommGroup F] {μ : Measure α} {p : ENNReal} {Ω : Set α} (g : Lp F p (μ.restrict Ω))
    {s : Set α} (hs : s ⊆ Ω) : (eLpNorm g p (μ.restrict s)).toReal ≤ ‖g‖ :=
  (Lp.toReal_eLpNorm_restrict_mono g hs subset_rfl).trans_eq (Lp.norm_def g).symm

/-- The `Lᵖ` classes vanishing almost everywhere off a set `s` form a closed set: convergence in
`Lᵖ` implies almost everywhere convergence of a subsequence. -/
theorem Lp.isClosed_setOf_ae_notMem_imp_eq_zero {α F : Type*} [MeasurableSpace α]
    {μ : Measure α} [NormedAddCommGroup F] {p : ENNReal} [Fact (1 ≤ p)] (s : Set α) :
    IsClosed {f : Lp F p μ | ∀ᵐ x ∂μ, x ∉ s → f x = 0} := by
  refine IsSeqClosed.isClosed fun g h hgs hg ↦ ?_
  obtain ⟨ns, -, hns⟩ := (tendstoInMeasure_of_tendsto_Lp hg).exists_seq_tendsto_ae
  filter_upwards [hns, ae_all_iff.2 hgs] with x hx hgx hxs
  exact tendsto_nhds_unique hx (tendsto_const_nhds.congr fun i ↦ (hgx (ns i) hxs).symm)

/-- The restriction of an `Lᵖ` class to a set `s` vanishes exactly when the class vanishes almost
everywhere on `s`. -/
theorem LpToLpRestrictCLM_eq_zero_iff {E F 𝕜 : Type*} [MeasurableSpace E] [NormedAddCommGroup F]
    [NormedRing 𝕜] [Module 𝕜 F] [IsBoundedSMul 𝕜 F] {μ : Measure E} {p : ENNReal} [Fact (1 ≤ p)]
    (s : Set E) (f : Lp F p μ) :
    LpToLpRestrictCLM E F 𝕜 μ p s f = 0 ↔ f =ᵐ[μ.restrict s] 0 :=
  Lp.eq_zero_iff_ae_eq_zero.trans
    ⟨(LpToLpRestrictCLM_coeFn 𝕜 s f).symm.trans, (LpToLpRestrictCLM_coeFn 𝕜 s f).trans⟩

section Subset

open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {s t : Set X}

/-- A function in `Lᵖ(t)`, `1 ≤ p`, is integrable on every subset `s ⊆ t` of finite measure. -/
theorem MemLp.integrableOn_of_subset {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
    {g : X → ε} {p : ℝ≥0∞} (hg : MemLp g p (μ.restrict t)) (hp : 1 ≤ p) (hst : s ⊆ t)
    (hs : μ s ≠ ⊤) :
    IntegrableOn g s μ := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  exact (hg.mono_measure (Measure.restrict_mono hst le_rfl)).integrable hp

/-- For a function `g` in `L²(t)`, the squared distance `‖g - c‖²` to a constant `c` is integrable
on every subset `s ⊆ t` of finite measure. -/
theorem MemLp.integrableOn_norm_sub_sq_of_subset {F : Type*} [SeminormedAddCommGroup F]
    {g : X → F} (hg : MemLp g 2 (μ.restrict t)) (hst : s ⊆ t) (hs : μ s ≠ ⊤) (c : F) :
    IntegrableOn (fun x ↦ ‖g x - c‖ ^ 2) s μ := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  have hgs : MemLp g 2 (μ.restrict s) := hg.mono_measure (Measure.restrict_mono hst le_rfl)
  -- Dominate `‖g - c‖²` by `(‖g‖ + ‖c‖)²`; the real-valued `‖g‖ + ‖c‖` lies in `L²(s)`.
  have hn : MemLp (fun x ↦ ‖g x‖ + ‖c‖) 2 (μ.restrict s) :=
    (hgs.congr_eNorm hgs.aestronglyMeasurable.norm
      (ae_of_all _ fun x ↦ (eNorm_norm (g x)).symm)).add (memLp_const ‖c‖)
  refine (hn.integrable_norm_pow two_ne_zero).mono
    ((hgs.aestronglyMeasurable.sub aestronglyMeasurable_const).norm.pow 2) (ae_of_all _ fun x ↦ ?_)
  simp only [norm_pow, Real.norm_eq_abs]
  gcongr
  exact (norm_sub_le _ _).trans (le_abs_self _)

/-- **Hölder's inequality for the `L²` mass on a subset.** For `2 ≤ q` and a function `g` in
`L^q(t)`, the integral of `‖g‖²` over a subset `s ⊆ t` of finite measure is at most
`‖g‖²_{L^q(t)} μ(s)^{1 - 2/q}`. -/
theorem MemLp.setIntegral_norm_sq_le_eLpNorm_sq_mul_measureReal_rpow {F : Type*}
    [SeminormedAddGroup F] {g : X → F} {q : ℝ≥0∞} (hg : MemLp g q (μ.restrict t)) (hq : 2 ≤ q)
    (hst : s ⊆ t) (hs : μ s ≠ ⊤) :
    ∫ x in s, ‖g x‖ ^ 2 ∂μ ≤
      (eLpNorm g q (μ.restrict t)).toReal ^ 2 * μ.real s ^ (1 - 2 / q.toReal) := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hs
  have hgs : MemLp g q (μ.restrict s) := hg.mono_measure (Measure.restrict_mono hst le_rfl)
  have hexp : 0 ≤ 1 / 2 - 1 / q.toReal := by
    simpa only [ENNReal.toReal_ofNat] using
      ENNReal.one_div_toReal_sub_one_div_toReal_nonneg two_ne_zero hq
  -- Hölder's inequality on `s`: `‖g‖_{L²(s)} ≤ ‖g‖_{L^q(t)} μ(s)^{1/2-1/q}`.
  have hH : (eLpNorm g 2 (μ.restrict s)).toReal ≤
      (eLpNorm g q (μ.restrict t)).toReal * μ.real s ^ (1 / 2 - 1 / q.toReal) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict s) (p := 2) (q := q) hq
      hgs.aestronglyMeasurable
    rw [Measure.restrict_apply_univ, ENNReal.toReal_ofNat] at h
    have hmono := eLpNorm_mono_measure g (p := q) (Measure.restrict_mono hst (le_refl μ))
    refine (ENNReal.toReal_mono (ENNReal.mul_ne_top hg.eLpNorm_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hexp hs)) (h.trans (mul_le_mul_left hmono _))).trans_eq ?_
    rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, measureReal_def]
  -- `∫_s ‖g‖² = ‖g‖²_{L²(s)}`.
  rw [integral_norm_sq_eq_toReal_eLpNorm_sq hgs.aestronglyMeasurable]
  calc _ ≤ ((eLpNorm g q (μ.restrict t)).toReal * μ.real s ^ (1 / 2 - 1 / q.toReal)) ^ 2 :=
        pow_le_pow_left₀ ENNReal.toReal_nonneg hH 2
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast measureReal_nonneg]
      congr 2
      push_cast
      ring

end Subset

section RestrictOfSubset

open scoped ENNReal

variable {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure X} {p : ℝ≥0∞} [Fact (1 ≤ p)] {s t : Set X}

/-- The restriction `Lᵖ(μ|t) → Lᵖ(μ|s)` for `s ⊆ t`, as a continuous linear map: it sends the
class of `f` on `t` to the class of `f` on `s`. -/
def Lp.restrictOfSubsetL (hst : s ⊆ t) : Lp F p (μ.restrict t) →L[ℝ] Lp F p (μ.restrict s) :=
  Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top
    ((Measure.restrict_mono_set μ hst).trans_eq (one_smul _ _).symm)

/-- The restriction to `s ⊆ t` of an `Lᵖ(μ|t)` class agrees with it almost everywhere on `s`. -/
theorem Lp.coeFn_restrictOfSubsetL (hst : s ⊆ t) (f : Lp F p (μ.restrict t)) :
    Lp.restrictOfSubsetL hst f =ᵐ[μ.restrict s] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f

/-- The restriction `Lᵖ(μ|t) → Lᵖ(μ|s)` has norm at most one. -/
theorem Lp.norm_restrictOfSubsetL_le (hst : s ⊆ t) :
    ‖(Lp.restrictOfSubsetL hst : Lp F p (μ.restrict t) →L[ℝ] Lp F p (μ.restrict s))‖ ≤ 1 :=
  (Lp.norm_LpToLpOfMeasureLeSMul_le _ _).trans (by simp)

/-- Restricting to `t` and then to `s ⊆ t` is restricting to `s`. -/
@[simp]
theorem Lp.restrictOfSubsetL_LpToLpRestrictCLM {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 F]
    [IsBoundedSMul 𝕜 F] (hst : s ⊆ t) (f : Lp F p μ) :
    Lp.restrictOfSubsetL hst (LpToLpRestrictCLM X F 𝕜 μ p t f) =
      LpToLpRestrictCLM X F 𝕜 μ p s f := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_restrictOfSubsetL hst (LpToLpRestrictCLM X F 𝕜 μ p t f),
    ae_restrict_of_ae_restrict_of_subset hst (LpToLpRestrictCLM_coeFn 𝕜 t f),
    LpToLpRestrictCLM_coeFn 𝕜 s f] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃]

end RestrictOfSubset

end MeasureTheory
