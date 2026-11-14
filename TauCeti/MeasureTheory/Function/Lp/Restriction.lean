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
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Function.Lp.Exponent

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

end MeasureTheory
