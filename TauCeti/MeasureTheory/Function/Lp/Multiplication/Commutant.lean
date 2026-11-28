/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Multiplication.Basic
public import TauCeti.MeasureTheory.Function.Lp.Operator.Local
import TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# Commutant and support-preserving operators on scalar `Lᵖ`

Let `μ` be a sigma-finite measure, let `1 ≤ p < ∞`, and let `S` be a bounded operator on the scalar
space `Lᵖ(μ)`. This file proves that `S` is multiplication by an essentially bounded function
`a ∈ L∞(μ)` (`MeasureTheory.Lp.multiplicationOperator`) exactly when it is local, that is, does not
enlarge supports: whenever `f` vanishes almost everywhere off a measurable set `s`, so does `S f`
(`MeasureTheory.Lp.exists_eq_multiplicationOperator_iff`). Equivalently, `S` commutes with every
multiplication operator (`MeasureTheory.Lp.forall_commute_multiplicationOperator_iff`):
the commutant of `L∞(μ)` acting on `Lᵖ(μ)` is `L∞(μ)` itself. On a topological space whose measure
is inner regular for compact sets, compact sets suffice
(`MeasureTheory.Lp.exists_eq_multiplicationOperator_of_isCompact`). Both the local and global
multiplier representations in this file are built from the scalar specialization of the
operator-valued locality theorem
`ContinuousLinearMap.exists_forall_ae_eq_apply_of_forall_ae_eq_zero` (applied via
`MeasureTheory.Lp.exists_eq_multiplicationOperator_of_forall_ae_eq_zero`, where the symbol `m x`
on `𝕜` is multiplication by `m x 1`).

Over a complete separable nontrivially normed field `𝕜` and for `1 ≤ p < ∞`, every bounded operator
commuting with measurable-set indicator multiplications on sets of finite measure is locally
multiplication by an `L∞` symbol on each finite-measure set
(`MeasureTheory.Lp.exists_norm_le_and_comp_indicatorMultiplication_eq`),
and globally multiplication by an `L∞` symbol when the measure is `σ`-finite
(`MeasureTheory.Lp.exists_multiplicationOperator_eq_of_forall_commute_indicatorMultiplication` and
`MeasureTheory.Lp.centralizer_range_multiplicationOperator`).

Without any `σ`-finiteness assumption on `μ`, any two bounded operators on `Lp 𝕜 p μ` (`1 ≤ p < ∞`)
commuting with all finite-measure indicator multiplications commute with each other
(`MeasureTheory.Lp.commute_of_forall_commute_indicatorMultiplication`).

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Section IX.6 (the multiplication
  algebra `L∞(μ)` on `L²(μ)` is maximal abelian).
* M. Takesaki, *Theory of Operator Algebras I*, Springer, 2002, Chapter III, §1.
* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  Academic Press, 1983, Example 5.1.6.
-/

public section

noncomputable section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory.Lp

section GeneralLp

open Set

variable {α 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α} [NontriviallyNormedField 𝕜]
  [CompleteSpace 𝕜] [TopologicalSpace.SeparableSpace 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {S : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ}

/-- **Local operators on scalar `Lᵖ` are multiplication operators.** On a sigma-finite measure
space and for `p < ∞`, a bounded operator `S` on the scalar space `Lᵖ(μ)` such that `S f` vanishes
almost everywhere off every measurable set off which `f` vanishes is multiplication by some
`a ∈ L∞(μ)`. -/
theorem exists_eq_multiplicationOperator_of_forall_ae_eq_zero [SigmaFinite μ] (hp : p ≠ ∞)
    (hS : ∀ (f : Lp 𝕜 p μ) (s : Set α), MeasurableSet s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → S f x = 0) :
    ∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a := by
  obtain ⟨m, hm, hbound, hSm⟩ := S.exists_forall_ae_eq_apply_of_forall_ae_eq_zero hp hS
  -- the operator `m x` on `𝕜` is multiplication by `m x 1`
  have ha : MemLp (fun x ↦ m x 1) ∞ μ :=
    memLp_top_of_bound ((ContinuousLinearMap.apply 𝕜 𝕜 (1 : 𝕜)).continuous.comp_stronglyMeasurable
      hm).aestronglyMeasurable ‖S‖ (hbound.mono fun x hx ↦ by
        simpa using ((m x).le_opNorm 1).trans (by simpa using hx))
  refine ⟨ha.toLp _, ContinuousLinearMap.ext fun f ↦ Lp.ext ?_⟩
  filter_upwards [hSm f, multiplicationOperator_ae (ha.toLp _) f, ha.coeFn_toLp] with x h₁ h₂ h₃
  rw [h₁, h₂, h₃, smul_eq_mul, mul_comm, ← smul_eq_mul, ← map_smul, smul_eq_mul, mul_one]

/-- **Multiplication operators are the local operators.** On a sigma-finite measure space and for
`p < ∞`, a bounded operator `S` on the scalar space `Lᵖ(μ)` is multiplication by some
`a ∈ L∞(μ)` if and only if `S f` vanishes almost everywhere off every measurable set off which `f`
vanishes. -/
theorem exists_eq_multiplicationOperator_iff [SigmaFinite μ] (hp : p ≠ ∞) :
    (∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a) ↔
      ∀ (f : Lp 𝕜 p μ) (s : Set α), MeasurableSet s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
        ∀ᵐ x ∂μ, x ∉ s → S f x = 0 := by
  refine ⟨?_, exists_eq_multiplicationOperator_of_forall_ae_eq_zero hp⟩
  rintro ⟨a, rfl⟩ f s - hf
  filter_upwards [multiplicationOperator_ae a f, hf] with x h₁ h₂ hx
  rw [h₁, h₂ hx, smul_zero]

/-- **The commutant of `L∞`.** On a sigma-finite measure space and for `p < ∞`, a bounded operator
on the scalar space `Lᵖ(μ)` commutes with every multiplication operator if and only if it is
itself a multiplication operator: the multiplication operators form a maximal commutative family
of operators on `Lᵖ(μ)`. -/
theorem forall_commute_multiplicationOperator_iff [SigmaFinite μ] (hp : p ≠ ∞) :
    (∀ b : Lp 𝕜 ∞ μ, Commute S (multiplicationOperator b)) ↔
      ∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a := by
  refine ⟨fun h ↦ (exists_eq_multiplicationOperator_iff hp).2 fun f s hs hf ↦ ?_,
    fun ⟨a, ha⟩ b ↦ ha ▸ commute_multiplicationOperator a b⟩
  -- `f` is fixed by multiplication by `1_s`, which commutes with `S`
  have hb : MemLp (s.indicator fun _ ↦ (1 : 𝕜)) ∞ μ :=
    (memLp_top_const 1).indicator hs.nullMeasurableSet
  have hfix : multiplicationOperator (hb.toLp _) f = f := by
    refine Lp.ext ?_
    filter_upwards [multiplicationOperator_ae (hb.toLp _) f, hb.coeFn_toLp, hf] with x h₁ h₂ h₃
    rw [h₁, h₂]
    by_cases hx : x ∈ s <;> simp [hx, h₃]
  have hcomm : S f = multiplicationOperator (hb.toLp _) (S f) := by
    conv_lhs => rw [← hfix]
    exact congrArg (· f) (h (hb.toLp _)).eq
  filter_upwards [multiplicationOperator_ae (hb.toLp _) (S f), hb.coeFn_toLp] with x h₁ h₂ hx
  rw [hcomm, h₁, h₂, indicator_of_notMem hx, zero_smul]

/-- **Operators that preserve compact supports are multiplication operators.** Let `μ` be a
sigma-finite measure on a Hausdorff space, inner regular for compact sets on sets of finite
measure, and let `p < ∞`. A bounded operator `S` on the scalar space `Lᵖ(μ)` such that `S f`
vanishes almost everywhere off every compact set off which `f` vanishes almost everywhere is
multiplication by some `a ∈ L∞(μ)`. -/
theorem exists_eq_multiplicationOperator_of_isCompact [TopologicalSpace α]
    [OpensMeasurableSpace α] [T2Space α] [SigmaFinite μ] [μ.InnerRegularCompactLTTop]
    (hp : p ≠ ∞)
    (hS : ∀ (f : Lp 𝕜 p μ) (K : Set α), IsCompact K → (∀ᵐ x ∂μ, x ∉ K → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ K → S f x = 0) :
    ∃ a : Lp 𝕜 ∞ μ, S = multiplicationOperator a :=
  exists_eq_multiplicationOperator_of_forall_ae_eq_zero hp fun f _ hs hf ↦
    S.ae_apply_eq_zero_of_forall_isCompact hp hS f hs hf

end GeneralLp

open ContinuousLinearMap

section CentralizerHelpers

variable {α 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Any operator in the centralizer of the range of `multiplicationOperator` commutes with every
`multiplicationOperator a`. -/
theorem commute_multiplicationOperator_of_mem_centralizer_range [NormedField 𝕜]
    {T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ}
    (hT : T ∈ (Set.range (multiplicationOperator (𝕜 := 𝕜) (E := 𝕜) (p := p) (μ := μ))).centralizer)
    (a : Lp 𝕜 ∞ μ) :
    Commute T (multiplicationOperator (𝕜 := 𝕜) (E := 𝕜) (p := p) a) :=
  (commute_iff_eq _ _).mpr (hT _ ⟨a, rfl⟩).symm

/-- Any operator in the centralizer of the range of `multiplicationOperator` commutes with every
`indicatorMultiplication`. -/
theorem commute_indicatorMultiplication_of_mem_centralizer_range [NontriviallyNormedField 𝕜]
    {T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ}
    (hT : T ∈ (Set.range (multiplicationOperator (𝕜 := 𝕜) (E := 𝕜) (p := p) (μ := μ))).centralizer)
    {s : Set α} (hs : MeasurableSet s) :
    Commute T (indicatorMultiplication 𝕜 p hs) := by
  rw [← multiplicationOperator_linftyIndicator hs]
  exact commute_multiplicationOperator_of_mem_centralizer_range hT _

end CentralizerHelpers

section IndicatorCommutantHelpers

variable {α 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α} [NontriviallyNormedField 𝕜]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Compressing an operator `T` that commutes with measurable-subset indicators on `s` yields a
local operator on `Lp 𝕜 p (μ.restrict s)`. -/
private theorem isLocal_comp_extendByZero {s : Set α} (hs : MeasurableSet s)
    (T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ)
    (hcomm : ∀ ⦃t : Set α⦄ (ht : MeasurableSet t), t ⊆ s →
      Commute T (indicatorMultiplication 𝕜 p ht))
    (g : Lp 𝕜 p (μ.restrict s)) (t : Set α) (ht : MeasurableSet t)
    (hg : ∀ᵐ x ∂μ.restrict s, x ∉ t → g x = 0) :
    ∀ᵐ x ∂μ.restrict s, x ∉ t →
      ((LpToLpRestrictCLM α 𝕜 𝕜 μ p s).comp
        (T.comp ((TauCeti.castLpₗᵢ (𝕜 := 𝕜) (E := 𝕜) (p := p)
          Measure.restrict_univ).toLinearIsometry.comp
          (TauCeti.extendByZeroLpₗᵢ 𝕜 μ hs.nullMeasurableSet
            (Set.subset_univ s))).toContinuousLinearMap)) g x = 0 := by
  set extp : Lp 𝕜 p (μ.restrict s) →ₗᵢ[𝕜] Lp 𝕜 p μ :=
    (TauCeti.castLpₗᵢ Measure.restrict_univ).toLinearIsometry.comp
      (TauCeti.extendByZeroLpₗᵢ 𝕜 μ hs.nullMeasurableSet (Set.subset_univ s)) with hext
  have hι : (extp g : α → 𝕜) =ᵐ[μ] s.indicator g := by
    rw [hext, LinearIsometry.coe_comp, LinearIsometryEquiv.coe_toLinearIsometry,
      Function.comp_apply]
    exact TauCeti.coeFn_castLpₗᵢ_extendByZeroLpₗᵢ 𝕜 hs.nullMeasurableSet g
  set r := t ∩ s
  have hr : MeasurableSet r := ht.inter hs
  have hι_fix : indicatorMultiplication 𝕜 p hr (extp g) = extp g := by
    refine indicatorMultiplication_eq_self_of_ae_notMem hr ?_
    filter_upwards [hι, (ae_restrict_iff' hs).mp hg] with x hιx hgx hxr
    rw [hιx]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs, hgx hxs fun hxt ↦ hxr ⟨hxt, hxs⟩]
    · rw [Set.indicator_of_notMem hxs]
  have hTι : T (extp g) = indicatorMultiplication 𝕜 p hr (T (extp g)) := by
    rw [← (hcomm hr Set.inter_subset_right).indicatorMultiplication_apply, hι_fix]
  filter_upwards [LpToLpRestrictCLM_coeFn 𝕜 s (T (extp g)),
    ae_restrict_of_ae ((Lp.ext_iff.mp hTι).trans
      (indicatorMultiplication_ae hr (T (extp g))))] with x hxR hxT hxt
  simp only [comp_apply, LinearIsometry.coe_toContinuousLinearMap]
  rw [hxR, hxT, Set.indicator_of_notMem fun (h : x ∈ r) ↦ hxt h.1]

/-- Gluing on-`s` multiplication representation of the compressed operator and off-`s` vanishing of
`T ∘L P` back into `T ∘L P = multiplicationOperator (ι ∞ b) ∘L P`. -/
private theorem comp_indicatorMultiplication_eq_of_restrict {s : Set α} (hs : MeasurableSet s)
    {T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ} (hcomm_s : Commute T (indicatorMultiplication 𝕜 p hs))
    {b : Lp 𝕜 ∞ (μ.restrict s)}
    (hb_eq : multiplicationOperator (E := 𝕜) (p := p) b =
      (LpToLpRestrictCLM α 𝕜 𝕜 μ p s).comp
        (T.comp ((TauCeti.castLpₗᵢ (𝕜 := 𝕜) (E := 𝕜) (p := p)
          Measure.restrict_univ).toLinearIsometry.comp
          (TauCeti.extendByZeroLpₗᵢ 𝕜 μ hs.nullMeasurableSet
            (Set.subset_univ s))).toContinuousLinearMap)) :
    T ∘L indicatorMultiplication 𝕜 p hs =
      multiplicationOperator (TauCeti.castLpₗᵢ (𝕜 := 𝕜) Measure.restrict_univ
        (TauCeti.extendByZeroLpₗᵢ 𝕜 μ hs.nullMeasurableSet (Set.subset_univ s) b)) ∘L
        indicatorMultiplication 𝕜 p hs := by
  refine ContinuousLinearMap.ext fun f ↦ Lp.ext ?_
  simp only [comp_apply]
  set P : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ := indicatorMultiplication 𝕜 p hs
  have hTP : T (P f) = P (T f) := hcomm_s.indicatorMultiplication_apply f
  have hTf_off : ∀ᵐ x ∂μ, x ∉ s → T (P f) x = 0 := by
    filter_upwards [(Lp.ext_iff.mp hTP).trans (indicatorMultiplication_ae hs (T f))]
      with x hx hxs
    rw [hx, Set.indicator_of_notMem hxs]
  have hTf_on : ⇑(T (P f)) =ᵐ[μ.restrict s] fun x ↦ b x * f x := by
    have hS_apply : multiplicationOperator (E := 𝕜) (p := p) b (LpToLpRestrictCLM α 𝕜 𝕜 μ p s f) =
        LpToLpRestrictCLM α 𝕜 𝕜 μ p s (T (P f)) := by
      have h := congrArg (fun A : Lp 𝕜 p (μ.restrict s) →L[𝕜] Lp 𝕜 p (μ.restrict s) ↦
        A (LpToLpRestrictCLM α 𝕜 𝕜 μ p s f)) hb_eq
      rwa [comp_apply, comp_apply, LinearIsometry.coe_toContinuousLinearMap,
        LinearIsometry.coe_comp, LinearIsometryEquiv.coe_toLinearIsometry,
        Function.comp_apply, TauCeti.castLpₗᵢ_extendByZeroLpₗᵢ_LpToLpRestrictCLM] at h
    filter_upwards [LpToLpRestrictCLM_coeFn 𝕜 s (T (P f)),
      multiplicationOperator_ae b (LpToLpRestrictCLM α 𝕜 𝕜 μ p s f),
      LpToLpRestrictCLM_coeFn 𝕜 s f] with x hx hmul hR
    rw [← hx, ← hS_apply, hmul, hR, smul_eq_mul]
  filter_upwards [hTf_off, (ae_restrict_iff' hs).mp hTf_on,
    multiplicationOperator_ae (TauCeti.castLpₗᵢ (𝕜 := 𝕜) Measure.restrict_univ
      (TauCeti.extendByZeroLpₗᵢ 𝕜 μ hs.nullMeasurableSet (Set.subset_univ s) b)) (P f),
    indicatorMultiplication_ae (𝕜 := 𝕜) hs f,
    TauCeti.coeFn_castLpₗᵢ_extendByZeroLpₗᵢ 𝕜 hs.nullMeasurableSet b]
    with x hxoff hxon hmul₁ hmul₂ hax
  by_cases hxs : x ∈ s
  · rw [hxon hxs, hmul₁, hmul₂, hax, Set.indicator_of_mem hxs, Set.indicator_of_mem hxs,
      smul_eq_mul]
  · rw [hxoff hxs, hmul₁, hmul₂, Set.indicator_of_notMem hxs, smul_zero]

end IndicatorCommutantHelpers

section IndicatorCommutant

variable {α 𝕜 : Type*} [MeasurableSpace α] {μ : Measure α} [NontriviallyNormedField 𝕜]
  [CompleteSpace 𝕜] [TopologicalSpace.SeparableSpace 𝕜] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Local multiplier representation on a finite-measure set.** On an arbitrary measure space and
for `1 ≤ p < ∞`, a bounded operator on `Lp 𝕜 p μ` that commutes with indicator multiplications on
measurable subsets of a finite-measure measurable set `s` agrees after cutoff to `s` with
multiplication by an `L∞` symbol of norm at most `‖T‖`. -/
theorem exists_norm_le_and_comp_indicatorMultiplication_eq (hp : p ≠ ∞) {s : Set α}
    (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ)
    (hcomm : ∀ ⦃t : Set α⦄ (ht : MeasurableSet t), t ⊆ s →
      Commute T (indicatorMultiplication 𝕜 p ht)) :
    ∃ a : Lp 𝕜 ∞ μ, ‖a‖ ≤ ‖T‖ ∧
      T ∘L indicatorMultiplication 𝕜 p hs =
        multiplicationOperator a ∘L indicatorMultiplication 𝕜 p hs := by
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs
  -- Phase 1: Compress `T` to `Lp 𝕜 p (μ.restrict s)` and verify locality.
  let extp : Lp 𝕜 p (μ.restrict s) →ₗᵢ[𝕜] Lp 𝕜 p μ :=
    (TauCeti.castLpₗᵢ Measure.restrict_univ).toLinearIsometry.comp
      (TauCeti.extendByZeroLpₗᵢ 𝕜 μ hs.nullMeasurableSet (Set.subset_univ s))
  let S : Lp 𝕜 p (μ.restrict s) →L[𝕜] Lp 𝕜 p (μ.restrict s) :=
    (LpToLpRestrictCLM α 𝕜 𝕜 μ p s).comp (T.comp extp.toContinuousLinearMap)
  have hS_norm : ‖S‖ ≤ ‖T‖ := opNorm_le_bound S (norm_nonneg T) fun g ↦
    calc ‖S g‖ ≤ ‖T (extp g)‖ := norm_Lp_toLp_restrict_le s _
      _ ≤ ‖T‖ * ‖extp g‖ := T.le_opNorm _
      _ = ‖T‖ * ‖g‖ := by rw [extp.norm_map]
  -- Phase 2: Represent the compressed operator as multiplication by `b : Lp 𝕜 ∞ (μ.restrict s)`.
  obtain ⟨b, hb_eq⟩ := exists_eq_multiplicationOperator_of_forall_ae_eq_zero hp
    (isLocal_comp_extendByZero hs T hcomm)
  have hb_norm : ‖b‖ ≤ ‖S‖ := by
    rw [← norm_multiplicationOperator (E := 𝕜) (p := p) b, ← hb_eq]
  -- Phase 3: Extend `b` by zero to `Lp 𝕜 ∞ μ` and glue on and off `s`.
  refine ⟨TauCeti.castLpₗᵢ Measure.restrict_univ
      (TauCeti.extendByZeroLpₗᵢ 𝕜 μ hs.nullMeasurableSet (Set.subset_univ s) b), ?_,
    comp_indicatorMultiplication_eq_of_restrict hs (hcomm hs Set.Subset.rfl) hb_eq.symm⟩
  rw [LinearIsometryEquiv.norm_map, LinearIsometry.norm_map]
  exact hb_norm.trans hS_norm

/-- **Unconditional commutativity of the multiplier commutant.** On an arbitrary measure space —
with no sigma-finiteness assumption — any two bounded operators on `Lp 𝕜 p μ` (`1 ≤ p < ∞`) that
commute with all finite-measure indicator multiplications commute with each other. -/
theorem commute_of_forall_commute_indicatorMultiplication (hp : p ≠ ∞)
    {S T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ}
    (hS : ∀ ⦃s : Set α⦄ (hs : MeasurableSet s), μ s ≠ ∞ →
      Commute S (indicatorMultiplication 𝕜 p hs))
    (hT : ∀ ⦃s : Set α⦄ (hs : MeasurableSet s), μ s ≠ ∞ →
      Commute T (indicatorMultiplication 𝕜 p hs)) :
    Commute S T := by
  refine (commute_iff_eq _ _).mpr
    (ContinuousLinearMap.ext_indicatorConstLp hp fun s hs hμs c ↦ ?_)
  set u := indicatorConstLp p hs hμs c
  set P : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ := indicatorMultiplication 𝕜 p hs
  have hPu : P u = u := indicatorMultiplication_indicatorConstLp_self hs hμs c
  obtain ⟨a, -, ha⟩ := exists_norm_le_and_comp_indicatorMultiplication_eq hp hs
    hμs S fun t ht hts ↦ hS ht (measure_ne_top_of_subset hts hμs)
  obtain ⟨b, -, hb⟩ := exists_norm_le_and_comp_indicatorMultiplication_eq hp hs
    hμs T fun t ht hts ↦ hT ht (measure_ne_top_of_subset hts hμs)
  have happly {A B : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ} {x y : Lp 𝕜 ∞ μ}
      (hA : A ∘L P = multiplicationOperator x ∘L P)
      (hB : B ∘L P = multiplicationOperator y ∘L P) :
      (A * B) u = multiplicationOperator (x * y) u := by
    have hBu : B u = multiplicationOperator y u := by
      simpa only [comp_apply, hPu] using congrArg (fun R ↦ R u) hB
    have hPBu : P (B u) = B u := by
      have hcomm :=
        (commute_multiplicationOperator_indicatorMultiplication (E := 𝕜) (p := p) y hs)
      rw [hBu, ← hcomm.indicatorMultiplication_apply, hPu]
    calc (A * B) u = (A ∘L P) (B u) := by rw [mul_apply_eq_comp, comp_apply, hPBu]
      _ = multiplicationOperator x (B u) := by rw [hA, comp_apply, hPBu]
      _ = multiplicationOperator (x * y) u := by
        rw [hBu, ← comp_apply, multiplicationOperator_comp_multiplicationOperator]
  rw [happly ha hb, happly hb ha, mul_comm a b]

/-- On an arbitrary measure space and for `1 ≤ p < ∞`, any two operators in the centralizer of
the range of `multiplicationOperator` commute with each other. -/
theorem commute_of_mem_centralizer_range_multiplicationOperator (hp : p ≠ ∞)
    {S T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ}
    (hS : S ∈
      (Set.range (multiplicationOperator (𝕜 := 𝕜) (E := 𝕜) (p := p) (μ := μ))).centralizer)
    (hT : T ∈
      (Set.range (multiplicationOperator (𝕜 := 𝕜) (E := 𝕜) (p := p) (μ := μ))).centralizer) :
    Commute S T :=
  commute_of_forall_commute_indicatorMultiplication hp
    (fun _ hs _ ↦ commute_indicatorMultiplication_of_mem_centralizer_range hS hs)
    (fun _ hs _ ↦ commute_indicatorMultiplication_of_mem_centralizer_range hT hs)

/-- **Multiplier commutant theorem on sigma-finite `Lᵖ`.** For `1 ≤ p < ∞`, every bounded operator
on `Lp 𝕜 p μ` that commutes with all finite-measure indicator multiplications is multiplication by
an essentially bounded symbol. -/
theorem exists_multiplicationOperator_eq_of_forall_commute_indicatorMultiplication
    [SigmaFinite μ] (hp : p ≠ ∞) (T : Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ)
    (hcomm : ∀ ⦃s : Set α⦄ (hs : MeasurableSet s), μ s ≠ ∞ →
      Commute T (indicatorMultiplication 𝕜 p hs)) :
    ∃ a : Lp 𝕜 ∞ μ, multiplicationOperator (E := 𝕜) (p := p) a = T := by
  have hloc : ∀ (f : Lp 𝕜 p μ) (s : Set α), MeasurableSet s → (∀ᵐ x ∂μ, x ∉ s → f x = 0) →
      ∀ᵐ x ∂μ, x ∉ s → T f x = 0 := by
    intro f s hs hf
    set sₙ : ℕ → Set α := fun n ↦ spanningSets μ n ∩ s
    have hsₙ (n : ℕ) : MeasurableSet (sₙ n) := (measurableSet_spanningSets μ n).inter hs
    have hμsₙ (n : ℕ) : μ (sₙ n) ≠ ∞ :=
      measure_ne_top_of_subset Set.inter_subset_left (measure_spanningSets_lt_top μ n).ne
    have hfs : indicatorMultiplication 𝕜 p hs f = f :=
      indicatorMultiplication_eq_self_of_ae_notMem hs hf
    let fₙ (n : ℕ) : Lp 𝕜 p μ := indicatorMultiplication 𝕜 p (hsₙ n) f
    have hfₙ (n : ℕ) : fₙ n = indicatorMultiplication 𝕜 p (measurableSet_spanningSets μ n) f := by
      dsimp only [fₙ]
      rw [← indicatorMultiplication_comp_indicatorMultiplication
        (measurableSet_spanningSets μ n) hs, comp_apply, hfs]
    have htend : Tendsto fₙ atTop (𝓝 f) := by
      simpa only [funext hfₙ] using tendsto_indicatorMultiplication_spanningSets hp f
    refine (Lp.isClosed_setOf_ae_notMem_imp_eq_zero s).mem_of_tendsto
      ((T.continuous.tendsto f).comp htend) (.of_forall fun n ↦ ?_)
    have hTfₙ : T (fₙ n) = indicatorMultiplication 𝕜 p (hsₙ n) (T f) :=
      (hcomm (hsₙ n) (hμsₙ n)).indicatorMultiplication_apply f
    filter_upwards [(Lp.ext_iff.mp hTfₙ).trans (indicatorMultiplication_ae (hsₙ n) (T f))]
      with x hx hxs
    rw [Function.comp_apply, hx, Set.indicator_of_notMem fun (h : x ∈ sₙ n) ↦ hxs h.2]
  exact (exists_eq_multiplicationOperator_of_forall_ae_eq_zero hp hloc).imp
    fun _ h ↦ h.symm

/-- On a sigma-finite measure space and for `1 ≤ p < ∞`, the centralizer in
`Lp 𝕜 p μ →L[𝕜] Lp 𝕜 p μ` of the range of `multiplicationOperator` is that range itself. -/
theorem centralizer_range_multiplicationOperator [SigmaFinite μ] (hp : p ≠ ∞) :
    (Set.range (multiplicationOperator (𝕜 := 𝕜) (E := 𝕜) (p := p) (μ := μ))).centralizer =
      Set.range (multiplicationOperator (𝕜 := 𝕜) (E := 𝕜) (p := p) (μ := μ)) := by
  ext T
  constructor
  · intro hT
    exact exists_multiplicationOperator_eq_of_forall_commute_indicatorMultiplication hp T
      fun _ hs _ ↦ commute_indicatorMultiplication_of_mem_centralizer_range hT hs
  · rintro ⟨a, rfl⟩ S ⟨b, rfl⟩
    exact (commute_iff_eq _ _).mp (commute_multiplicationOperator b a)

end IndicatorCommutant

end MeasureTheory.Lp

end
