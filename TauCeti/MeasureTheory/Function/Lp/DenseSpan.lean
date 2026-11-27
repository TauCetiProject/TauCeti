/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import TauCeti.MeasureTheory.Function.Lp.Indicator

/-!
# Dense spans of indicator classes in Bochner `Lᵖ` spaces

Let `1 ≤ p < ∞` and let `E` be a normed space. Simple functions are dense in the Bochner space
`Lᵖ(μ; E)`, so the indicator classes `𝟙_s c`, for measurable sets `s` of finite measure and
constants `c ∈ E`, span a dense subspace. This file shows that much smaller families of indicator
classes already have dense span, in the form needed to identify continuous linear maps out of
`Lᵖ(μ; E)` by their values on such classes and to approximate Bochner functions by finite sums.

* The constants may be restricted to any set `D ⊆ E` whose span is dense in `E`
  (`MeasureTheory.Lp.eq_top_of_forall_indicatorConstLp_mem`): a closed subspace of `Lᵖ(μ; E)`
  containing `𝟙_s c` for all such `s` and all `c ∈ D` is the whole space.
* The sets may be restricted to a measure-dense family `𝒜`, one whose members approximate every
  measurable set of finite measure in measure of the symmetric difference
  (`MeasureTheory.Measure.MeasureDense.topologicalClosure_span_indicatorConstLp_eq_top`). By
  Mathlib's `MeasureTheory.Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite` and
  `MeasureTheory.Measure.MeasureDense.of_generateFrom_isSetAlgebra_sigmaFinite`, every algebra of
  sets generating the σ-algebra is measure-dense when the measure is finite, or when the algebra
  contains a countable cover of the space by sets of finite measure.
* The sets may be restricted to a π-system `𝒞` generating the σ-algebra and containing a
  countable cover of the space by sets of finite measure
  (`IsPiSystem.topologicalClosure_span_indicatorConstLp_eq_top`); only the members of `𝒞` of
  finite measure are used.
* The elementary tensors `s ↦ φ(s) x`, for scalar `φ ∈ Lᵖ(μ)` and `x ∈ E`, span a dense subspace
  (`MeasureTheory.Lp.topologicalClosure_span_compLp_toSpanSingleton_eq_top`).

Restricting the constants to a set of dense span lets the results be iterated: for instance the
classes `𝟙_A (𝟙_B x)` of rectangle tensors span a dense subspace of `Lᵖ(μ; L^q(ν; E))`, taking for
`D` the indicator classes `𝟙_B x` in `L^q(ν; E)`.

## Implementation notes

The π-system statement is proved by a Dynkin system argument: inside a fixed member `B` of the
cover, the measurable sets `t` for which `𝟙_{t ∩ B} c` lies in the closed span are closed under
relative complements and countable disjoint unions, the latter because `Lᵖ` norms of indicators of
the tails of a disjoint union of finite measure tend to zero for `p < ∞`.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Springer, 2016, Lemma 1.2.19.
-/

public section

open Filter Function Set
open scoped ENNReal symmDiff Topology

namespace MeasureTheory

variable {α 𝕜 E : Type*} {m : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]
  [NormedAddCommGroup E]

section IndicatorMem

variable {V : Set (Lp E p μ)} {c : E}

omit [Fact (1 ≤ p)] in
/-- Membership of an indicator class in a set of `Lᵖ` classes depends only on the underlying set,
not on the proofs of its measurability and finiteness of measure. -/
private theorem indicatorConstLp_mem_of_eq {s t : Set α} (hst : s = t) {hs : MeasurableSet s}
    {ht : MeasurableSet t} {hμs : μ s ≠ ∞} {hμt : μ t ≠ ∞}
    (h : indicatorConstLp p hs hμs c ∈ V) : indicatorConstLp p ht hμt c ∈ V := by
  subst hst
  exact h

/-- If a closed additive subgroup of `Lᵖ`, `p < ∞`, contains the indicator classes of the members
of a pairwise disjoint sequence of measurable sets, it contains the indicator class of their union,
provided the union has finite measure. -/
private theorem indicatorConstLp_iUnion_mem {V : AddSubgroup (Lp E p μ)}
    (hV : IsClosed (V : Set (Lp E p μ))) (hp : p ≠ ∞) {f : ℕ → Set α}
    (hfm : ∀ i, MeasurableSet (f i)) (hfd : Pairwise (Disjoint on f)) (hμ : μ (⋃ i, f i) ≠ ∞)
    (hf : ∀ i (hμi : μ (f i) ≠ ∞), indicatorConstLp p (hfm i) hμi c ∈ V) :
    indicatorConstLp p (MeasurableSet.iUnion hfm) hμ c ∈ V := by
  have hAm : ∀ n, MeasurableSet (accumulate f n) := fun n ↦
    MeasurableSet.biUnion (to_countable _) fun i _ ↦ hfm i
  have hAμ : ∀ n, μ (accumulate f n) ≠ ∞ := fun n ↦
    measure_ne_top_of_subset (accumulate_subset_iUnion n) hμ
  -- the partial unions have indicator classes in `V`
  have hA : ∀ n, indicatorConstLp p (hAm n) (hAμ n) c ∈ V := by
    intro n
    induction n with
    | zero =>
      exact indicatorConstLp_mem_of_eq (accumulate_zero_nat f).symm
        (hf 0 (measure_ne_top_of_subset (subset_iUnion f 0) hμ))
    | succ n ih =>
      have hμ' : μ (f (n + 1)) ≠ ∞ := measure_ne_top_of_subset (subset_iUnion f _) hμ
      refine indicatorConstLp_mem_of_eq (accumulate_succ f n).symm
        (hs := (hAm n).union (hfm _)) (hμs := measure_union_ne_top (hAμ n) hμ') ?_
      rw [indicatorConstLp_disjoint_union (hAm n) (hfm _) (hAμ n) hμ'
        (disjoint_accumulate hfd n.lt_succ_self)]
      exact V.add_mem ih (hf _ hμ')
  -- and the measure of the remaining part of the union tends to zero
  have hlim : Tendsto (fun n ↦ μ (accumulate f n ∆ ⋃ i, f i)) atTop (𝓝 0) := by
    have hsub : ∀ n, accumulate f n ⊆ ⋃ i, f i := fun n ↦ accumulate_subset_iUnion n
    simp_rw [symmDiff_of_le (hsub _)]
    have h := tendsto_measure_iInter_atTop (μ := μ)
      (s := fun n ↦ (⋃ i, f i) \ accumulate f n)
      (fun n ↦ ((MeasurableSet.iUnion hfm).diff (hAm n)).nullMeasurableSet)
      (fun i j hij ↦ sdiff_subset_sdiff_right (monotone_accumulate hij))
      ⟨0, measure_ne_top_of_subset sdiff_subset hμ⟩
    rwa [← sdiff_iUnion, iUnion_accumulate, Set.sdiff_self, measure_empty] at h
  exact hV.mem_of_tendsto (tendsto_indicatorConstLp_set hp hlim) (Eventually.of_forall hA)

/-- **Dynkin step.** Let `𝒞` be a π-system generating the σ-algebra and let `B ∈ 𝒞` have finite
measure. If a closed additive subgroup of `Lᵖ`, `p < ∞`, contains the indicator classes of the
members of `𝒞` of finite measure, it contains the indicator class of `t ∩ B` for every measurable
set `t`. -/
private theorem indicatorConstLp_inter_mem {V : AddSubgroup (Lp E p μ)}
    (hV : IsClosed (V : Set (Lp E p μ))) (hp : p ≠ ∞) {𝒞 : Set (Set α)} (h𝒞 : IsPiSystem 𝒞)
    (hgen : m = MeasurableSpace.generateFrom 𝒞) {c : E}
    (hgenP : ∀ s ∈ 𝒞, ∀ (hs : MeasurableSet s) (hμs : μ s ≠ ∞), indicatorConstLp p hs hμs c ∈ V)
    {B : Set α} (hB : B ∈ 𝒞) (hBμ : μ B ≠ ∞) {t : Set α} (ht : MeasurableSet t)
    (htB : MeasurableSet (t ∩ B)) (hμ : μ (t ∩ B) ≠ ∞) : indicatorConstLp p htB hμ c ∈ V := by
  -- `P u` says that the indicator class of `u` lies in `V`
  let P : Set α → Prop := fun u ↦
    ∀ (hu : MeasurableSet u) (hμu : μ u ≠ ∞), indicatorConstLp p hu hμu c ∈ V
  have hemptyP : P ∅ := fun _ _ ↦ by simp
  have hBm : MeasurableSet B := hgen ▸ MeasurableSpace.measurableSet_generateFrom hB
  have hsub : ∀ u ⊆ B, μ u ≠ ∞ := fun u hu ↦ measure_ne_top_of_subset hu hBμ
  refine MeasurableSpace.induction_on_inter (C := fun u _ ↦ P (u ∩ B)) hgen h𝒞
    (by simpa using hemptyP) ?_ ?_ ?_ t ht htB hμ
  · intro u hu
    rcases (u ∩ B).eq_empty_or_nonempty with he | hne
    · exact he ▸ hemptyP
    · exact hgenP _ (h𝒞 _ hu _ hB hne)
  · -- `𝟙_{uᶜ ∩ B} = 𝟙_B - 𝟙_{u ∩ B}`
    intro u hum hu huc hμu
    have hunion : (uᶜ ∩ B) ∪ (u ∩ B) = B := by
      rw [← union_inter_distrib_right, compl_union_self, univ_inter]
    have hsum := indicatorConstLp_disjoint_union (p := p) huc (hum.inter hBm) hμu
      (hsub _ inter_subset_right) (disjoint_compl_left.mono inter_subset_left inter_subset_left) c
    have hB' : indicatorConstLp p (huc.union (hum.inter hBm))
        (hsub _ (union_subset inter_subset_right inter_subset_right)) c ∈ V :=
      indicatorConstLp_mem_of_eq hunion.symm (hgenP _ hB hBm hBμ)
    rw [hsum] at hB'
    simpa using V.sub_mem hB' (hu (hum.inter hBm) (hsub _ inter_subset_right))
  · intro f hfd hfm hf _ hμf
    simp_rw [iUnion_inter] at hμf ⊢
    exact indicatorConstLp_iUnion_mem hV hp (fun i ↦ (hfm i).inter hBm)
      (hfd.mono fun i j h ↦ h.mono inter_subset_left inter_subset_left) hμf
      fun i ↦ hf i ((hfm i).inter hBm)

end IndicatorMem

section Module

variable [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]

/-- Let `1 ≤ p < ∞` and let `D ⊆ E` have dense span. A closed submodule of `Lᵖ(μ; E)` containing
the indicator classes `𝟙_s c` of all measurable sets `s` of finite measure and all `c ∈ D` is the
whole space. -/
theorem Lp.eq_top_of_forall_indicatorConstLp_mem (hp : p ≠ ∞) {D : Set E}
    (hD : (Submodule.span 𝕜 D).topologicalClosure = ⊤) {V : Submodule 𝕜 (Lp E p μ)}
    (hV : IsClosed (V : Set (Lp E p μ)))
    (h : ∀ s (hs : MeasurableSet s) (hμs : μ s ≠ ∞), ∀ c ∈ D, indicatorConstLp p hs hμs c ∈ V) :
    V = ⊤ := by
  -- for a fixed set, the constants whose indicator classes lie in `V` form a closed submodule
  have hall : ∀ s (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (c : E),
      indicatorConstLp p hs hμs c ∈ V := by
    intro s hs hμs c
    let L := TauCeti.indicatorConstLpL 𝕜 p hs hμs (E := E)
    have hle : (Submodule.span 𝕜 D).topologicalClosure ≤ V.comap (L : E →ₗ[𝕜] Lp E p μ) :=
      Submodule.topologicalClosure_minimal _
        (Submodule.span_le.2 fun c hc ↦ by simpa [L] using h s hs hμs c hc)
        (by simpa only [Submodule.comap_coe, ContinuousLinearMap.coe_coe] using
          hV.preimage L.continuous)
    rw [hD] at hle
    simpa [L] using hle (Submodule.mem_top (x := c))
  refine Submodule.eq_top_iff'.2 fun f ↦ ?_
  induction f using Lp.induction hp with
  | indicatorConst c hs hμs =>
    rw [Lp.simpleFunc.coe_indicatorConst]
    exact hall _ hs hμs.ne c
  | add _ _ _ hf hg => exact V.add_mem hf hg
  | isClosed => exact hV

/-- Let `1 ≤ p < ∞`, let `𝒜` be a measure-dense family of sets and let `D ⊆ E` have dense span.
The indicator classes `𝟙_s c`, for `s ∈ 𝒜` of finite measure and `c ∈ D`, span a dense subspace
of `Lᵖ(μ; E)`. -/
theorem Measure.MeasureDense.topologicalClosure_span_indicatorConstLp_eq_top
    {𝒜 : Set (Set α)} (h𝒜 : μ.MeasureDense 𝒜) (hp : p ≠ ∞) {D : Set E}
    (hD : (Submodule.span 𝕜 D).topologicalClosure = ⊤) :
    (Submodule.span 𝕜 {f : Lp E p μ | ∃ s ∈ 𝒜, ∃ (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      ∃ c ∈ D, indicatorConstLp p hs hμs c = f}).topologicalClosure = ⊤ := by
  have : Fact (p ≠ ∞) := ⟨hp⟩
  refine Lp.eq_top_of_forall_indicatorConstLp_mem hp hD
    (Submodule.isClosed_topologicalClosure _) fun s hs hμs c hc ↦ ?_
  rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
  refine closure_mono ?_ (h𝒜.indicatorConstLp_subset_closure p c ⟨s, hs, hμs, rfl⟩)
  rintro _ ⟨t, ht, hμt, rfl⟩
  exact Submodule.subset_span ⟨t, ht, h𝒜.measurable t ht, hμt, c, hc, rfl⟩

/-- Let `1 ≤ p < ∞`, let `𝒞` be a π-system generating the σ-algebra and containing a countable
cover of the space by sets of finite measure, and let `D ⊆ E` have dense span. The indicator
classes `𝟙_s c`, for `s ∈ 𝒞` of finite measure and `c ∈ D`, span a dense subspace of
`Lᵖ(μ; E)`. -/
theorem _root_.IsPiSystem.topologicalClosure_span_indicatorConstLp_eq_top {𝒞 : Set (Set α)}
    (h𝒞 : IsPiSystem 𝒞) (hgen : m = MeasurableSpace.generateFrom 𝒞)
    (S : μ.FiniteSpanningSetsIn 𝒞) (hp : p ≠ ∞) {D : Set E}
    (hD : (Submodule.span 𝕜 D).topologicalClosure = ⊤) :
    (Submodule.span 𝕜 {f : Lp E p μ | ∃ s ∈ 𝒞, ∃ (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      ∃ c ∈ D, indicatorConstLp p hs hμs c = f}).topologicalClosure = ⊤ := by
  set V := (Submodule.span 𝕜 {f : Lp E p μ | ∃ s ∈ 𝒞, ∃ (hs : MeasurableSet s)
    (hμs : μ s ≠ ∞), ∃ c ∈ D, indicatorConstLp p hs hμs c = f}).topologicalClosure
  have hV : IsClosed (V : Set (Lp E p μ)) := Submodule.isClosed_topologicalClosure _
  have h𝒞m : ∀ s ∈ 𝒞, MeasurableSet s := fun s hs ↦
    hgen ▸ MeasurableSpace.measurableSet_generateFrom hs
  have hSm : ∀ n, MeasurableSet (S.set n) := fun n ↦ h𝒞m _ (S.set_mem n)
  refine Lp.eq_top_of_forall_indicatorConstLp_mem hp hD hV fun t ht hμt c hc ↦ ?_
  have hgenP : ∀ s ∈ 𝒞, ∀ (hs : MeasurableSet s) (hμs : μ s ≠ ∞),
      indicatorConstLp p hs hμs c ∈ V.toAddSubgroup := fun s hs hsm hμs ↦
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨s, hs, hsm, hμs, c, hc, rfl⟩)
  -- `t` is the disjoint union of its traces on the members of the cover with the earlier members
  -- removed, and each trace is handled by the Dynkin step
  have ht' : t = ⋃ n, (t ∩ disjointed S.set n) ∩ S.set n := by
    simp_rw [inter_assoc, inter_eq_left.2 (disjointed_subset S.set _), ← inter_iUnion,
      iUnion_disjointed, S.spanning, inter_univ]
  have hm : ∀ n, MeasurableSet (t ∩ disjointed S.set n) := fun n ↦
    ht.inter (MeasurableSet.disjointed hSm n)
  have key := indicatorConstLp_iUnion_mem hV hp (fun n ↦ (hm n).inter (hSm n))
    ((disjoint_disjointed S.set).mono fun i j h ↦ h.mono
      (inter_subset_left.trans inter_subset_right) (inter_subset_left.trans inter_subset_right))
    (ht' ▸ hμt) fun n ↦ indicatorConstLp_inter_mem hV hp h𝒞 hgen hgenP (S.set_mem n)
      (S.finite n).ne (hm n) _
  exact indicatorConstLp_mem_of_eq ht'.symm key

end Module

/-- Let `1 ≤ p < ∞`. The elementary tensors `s ↦ φ(s) x`, for scalar `φ ∈ Lᵖ(μ)` and `x ∈ E`,
span a dense subspace of the Bochner space `Lᵖ(μ; E)`. Here `s ↦ φ(s) x` is the composition of
`φ` with `c ↦ c • x`. -/
theorem Lp.topologicalClosure_span_compLp_toSpanSingleton_eq_top [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 E] (hp : p ≠ ∞) :
    (Submodule.span 𝕜 {f : Lp E p μ | ∃ (φ : Lp 𝕜 p μ) (x : E),
      (ContinuousLinearMap.toSpanSingleton 𝕜 x).compLp φ = f}).topologicalClosure = ⊤ := by
  refine Lp.eq_top_of_forall_indicatorConstLp_mem hp (D := univ)
    (by rw [Submodule.span_univ]; exact eq_top_iff.2 (Submodule.le_topologicalClosure _))
    (Submodule.isClosed_topologicalClosure _) fun s hs hμs c _ ↦ ?_
  refine Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨indicatorConstLp p hs hμs 1, c,
    ?_⟩)
  rw [ContinuousLinearMap.compLp_indicatorConstLp, ContinuousLinearMap.toSpanSingleton_apply,
    one_smul]

end MeasureTheory
