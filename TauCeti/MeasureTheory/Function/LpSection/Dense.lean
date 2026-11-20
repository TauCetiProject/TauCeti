/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support
public import TauCeti.MeasureTheory.Function.LpSection.Basic
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.Metrizable.Urysohn
import TauCeti.Geometry.Manifold.SmoothApprox.Lp
import TauCeti.Geometry.Manifold.VectorBundle.Trivialization

/-!
# Density and separability of `Lᵖ` sections

Let `E → B` be a smooth vector bundle over `𝕜 = ℝ` or `ℂ` with finite-dimensional model fibre
`F` and continuous fibre norms, over a finite-dimensional, Hausdorff, second-countable real
manifold `B`, and let `μ` be a measure on the Borel sets of `B` that is finite on compact sets. A
compactly supported smooth section has continuous, compactly supported fibre norm, so it defines a
class in `Lᵖ(E, μ)` (`TauCeti.LpSection.ofCompactlySupported`) for every `p`. This file proves
that for `p < ∞` these classes are dense (`TauCeti.LpSection.denseRange_ofCompactlySupported`),
and that the map is injective as soon as `μ` charges every nonempty open set
(`TauCeti.LpSection.injective_ofCompactlySupported`): two continuous sections that agree almost
everywhere then agree everywhere. Without that hypothesis the map has a kernel, the sections
vanishing almost everywhere (`TauCeti.LpSection.ofCompactlySupported_eq_zero_iff`); for the zero
measure every section is in it.

Since `Lᵖ(E, μ)` is complete in finite rank (`TauCeti.LpSection.instCompleteSpace`), it is the
completion of the compactly supported smooth sections for the `Lᵖ` norm. The restriction `p < ∞`
is needed: on `ℝ` with Lebesgue measure, the indicator function of `[0, 1]` has `L^∞` distance at
least `1 / 2` from every continuous function.

For `p < ∞` and fibre metrics, `Lᵖ(E, μ)` is moreover separable for every s-finite `μ`
(`TauCeti.LpSection.instSecondCountableTopology`), being isometric to `Lᵖ(μ; 𝕜ʳ)` through a
measurable isometric frame.

## The approximation

A section `s` in `Lᵖ(E, μ)` is first cut down to a compact set `K`: approximating the scalar
function `x ↦ ‖s x‖` by a continuous compactly supported one (Mathlib's
`MeasureTheory.MemLp.exists_hasCompactSupport_eLpNorm_sub_le`, for the regular measure `μ`) bounds
the `Lᵖ` norm of `s` off the support `K` of the approximation. Then `K` is covered by finitely
many compact sets, each inside the base set of an atlas chart `e`, and `s` on `K` is the sum of
its restrictions to measurable pieces of these sets. On a piece `A`, inside a compact `L` in the
base set of `e`, the coordinates `g = 1_A (e s)` of the piece lie in `Lᵖ(μ; F)`, as fibre norms
and the norm of `F` are uniformly comparable on compact subsets of the base set
(`Bundle.Trivialization.exists_norm_symm_le_and_norm_le_of_isCompact`). They are approximated in
`Lᵖ` by a smooth `g'` with topological support in an open `V ⊇ L` whose closure is compact and
contained in the base set (`MeasureTheory.MemLp.exists_contMDiff_tsupport_subset_eLpNorm_sub_le`).
The section `x ↦ e.symm x (g' x)`, extended by zero off the base set, is smooth
(`Bundle.Trivialization.contMDiff_section_symmL`) with compact support, and its distance to the
piece is at most a constant times the distance from `g` to `g'`.

## Main declarations

* `TauCeti.LpSection.ofCompactlySupported`: the classes of compactly supported smooth sections.
* `TauCeti.LpSection.denseRange_ofCompactlySupported`: they are dense in `Lᵖ(E, μ)` for `p < ∞`.
* `TauCeti.LpSection.injective_ofCompactlySupported`: the map is injective when `μ` is positive
  on nonempty open sets.
* `TauCeti.LpSection.instSecondCountableTopology`: `Lᵖ(E, μ)` is separable for `p < ∞`.

## References

* L. I. Nicolaescu, *Lectures on the Geometry of Manifolds*, 3rd ed., §10.2.3
  (Theorem 10.2.36).
-/

public section

noncomputable section

open Bundle MeasureTheory Set Filter
open scoped Topology ENNReal NNReal Manifold ContDiff

namespace TauCeti

section Separable

variable {𝕜 B F : Type*} [RCLike 𝕜] [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace 𝕜 (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  [ContinuousFiberNorm F E] {p : ℝ≥0∞} {μ : Measure B}

/-- **Separability.** For a finite-rank bundle with continuous fibre metric over a second-countable
base and finite `p`, `Lᵖ(E, μ)` is second countable for every s-finite measure `μ` on the Borel
sets of the base: a measurable isometric frame identifies it with `Lᵖ(μ; 𝕜ʳ)`. -/
instance LpSection.instSecondCountableTopology [FiniteDimensional 𝕜 F] [Fact (1 ≤ p)]
    [Fact (p ≠ ⊤)] [SFinite μ] : SecondCountableTopology (LpSection 𝕜 F E p μ) := by
  obtain ⟨Φ, hΦ⟩ := exists_isMeasurableIsometricFrame F E
    (EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 F))) finrank_euclideanSpace_fin
  exact ((hΦ μ).lpSectionEquiv p).toHomeomorph.secondCountableTopology

end Separable

variable {𝕜 B F EB HB : Type*} [RCLike 𝕜] [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {I : ModelWithCorners ℝ EB HB} [TopologicalSpace B]
  [ChartedSpace HB B] [MeasurableSpace B] [SecondCountableTopology B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace 𝕜 (E x)]
  [∀ x, Module ℝ (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E] [VectorBundle ℝ F E]
  [ContinuousFiberNorm F E] {p : ℝ≥0∞} {μ : Measure B} [IsFiniteMeasureOnCompacts μ]

section Opens

variable [OpensMeasurableSpace B]

omit [SecondCountableTopology B] in
/-- The fibre norm of a compactly supported smooth section is `p`-integrable for a measure that
is finite on compact sets. -/
theorem _root_.ContMDiffSection.memLp_norm_of_mem_compactlySupported {n : ℕ∞ω}
    {s : Cₛ^n⟮I; F, E⟯}
    (hs : s ∈ ContMDiffSection.compactlySupported I F n E) :
    MemLp (fun x ↦ ‖s x‖) p μ := by
  refine s.contMDiff.continuous.norm_bundle_of_continuousFiberNorm.memLp_of_hasCompactSupport ?_
  have h : tsupport (fun x ↦ ‖s x‖) = s.tsupport := by
    simp only [tsupport, Function.support, ne_eq, norm_eq_zero, ContMDiffSection.tsupport_def]
  rw [HasCompactSupport, h]
  exact ContMDiffSection.mem_compactlySupported.1 hs

namespace LpSection

variable (𝕜 I p μ) in
/-- The class in `Lᵖ(E, μ)` of a compactly supported smooth section. Its fibre norm is continuous
with compact support, hence `p`-integrable for a measure that is finite on compact sets. -/
def ofCompactlySupported :
    ContMDiffSection.compactlySupported I F ∞ E →+ LpSection 𝕜 F E p μ where
  toFun s := mk (s : ∀ x, E x) s.1.contMDiff.continuous.aestronglyMeasurableSection
    (ContMDiffSection.memLp_norm_of_mem_compactlySupported s.2)
  map_zero' := by
    rw [← mk_zero]
    exact (mk_eq_mk_iff (F := F)).2 (.of_forall fun x ↦ rfl)
  map_add' s t := by
    rw [mk_add]
    exact (mk_eq_mk_iff (F := F)).2 (.of_forall fun x ↦ rfl)

/-- The class of a compactly supported smooth section is represented by the section. -/
theorem coeFn_ofCompactlySupported (s : ContMDiffSection.compactlySupported I F ∞ E) :
    ∀ᵐ x ∂μ, ofCompactlySupported 𝕜 I p μ s x = s.1 x :=
  coeFn_mk _ _

/-- The kernel of `ofCompactlySupported` consists of the sections vanishing almost everywhere. -/
theorem ofCompactlySupported_eq_zero_iff {s : ContMDiffSection.compactlySupported I F ∞ E} :
    ofCompactlySupported 𝕜 I p μ s = 0 ↔ ∀ᵐ x ∂μ, s.1 x = 0 := by
  rw [ext_iff]
  constructor <;> intro h <;>
    filter_upwards [h, coeFn_ofCompactlySupported (𝕜 := 𝕜) (p := p) (μ := μ) s,
      coeFn_zero (𝕜 := 𝕜) (F := F) (E := E) (p := p) (μ := μ)] with x hx h1 h0
  · rwa [← h1, ← h0]
  · rw [h1, h0, hx]

/-- **Injectivity.** For a measure positive on nonempty open sets, a compactly supported smooth
section is determined by its class in `Lᵖ(E, μ)`. -/
theorem injective_ofCompactlySupported [μ.IsOpenPosMeasure] :
    Function.Injective (ofCompactlySupported 𝕜 I p μ (F := F) (E := E)) := by
  refine (injective_iff_map_eq_zero _).2 fun s hs ↦ ?_
  rw [ofCompactlySupported_eq_zero_iff] at hs
  -- The set where `s` does not vanish is open, since the fibre norm of `s` is continuous.
  have hopen : IsOpen {x | ‖(s : Cₛ^∞⟮I; F, E⟯) x‖ ≠ 0} :=
    isOpen_ne_fun ((s : Cₛ^∞⟮I; F, E⟯).contMDiff.continuous.norm_bundle_of_continuousFiberNorm
      (F := F)) continuous_const
  have hnull : μ {x | ‖(s : Cₛ^∞⟮I; F, E⟯) x‖ ≠ 0} = 0 :=
    measure_mono_null (fun x hx ↦ by simpa using hx) (ae_iff.1 hs)
  rw [hopen.measure_eq_zero_iff μ] at hnull
  ext x
  simpa using Set.eq_empty_iff_forall_notMem.1 hnull x

end LpSection

end Opens

/-! ### Approximation in a chart -/

section Approximation

variable [BorelSpace B] [FiniteDimensional ℝ EB] [IsManifold I ∞ B] [T2Space B]
  [ContMDiffVectorBundle ∞ F E I] [FiniteDimensional 𝕜 F] [Fact (1 ≤ p)]

omit [SecondCountableTopology B] [NormedSpace ℝ F] [∀ x, Module ℝ (E x)] [VectorBundle ℝ F E]
  [IsFiniteMeasureOnCompacts μ] [T2Space B] [Fact (1 ≤ p)] in
/-- On a compact subset `L` of the base set of an atlas chart `e`, the coordinates in `e` of a
measurable section with `p`-integrable fibre norm, restricted to a measurable `A ⊆ L`, are
`p`-integrable: the fibre norms and the norm of `F` are uniformly comparable on `L`. -/
private theorem memLp_indicator_coord (e : Trivialization F (π F E)) [MemTrivializationAtlas e]
    {L A : Set B} (hL : IsCompact L) (hLe : L ⊆ e.baseSet) (hA : MeasurableSet A) (hAL : A ⊆ L)
    {s : ∀ x, E x} (hs : AEStronglyMeasurableSection 𝕜 F μ s)
    (hsp : MemLp (fun x ↦ ‖s x‖) p μ) :
    MemLp (A.indicator fun x ↦ (e ⟨x, s x⟩).2) p μ := by
  obtain ⟨_, C', hC'⟩ := e.exists_norm_symm_le_and_norm_le_of_isCompact 𝕜 hL hLe
  refine hsp.of_le_mul (c := C') ((aestronglyMeasurable_indicator_iff hA).2 <|
    (hs.aestronglyMeasurable_coord e).mono_measure (Measure.restrict_mono (hAL.trans hLe) le_rfl))
    (.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ A
  · have := (hC' x (hAL hx) (e ⟨x, s x⟩).2).2
    rw [e.symm_apply_apply_mk (hLe (hAL hx))] at this
    rwa [indicator_of_mem hx, norm_norm]
  · rw [indicator_of_notMem hx, norm_zero, norm_norm]
    positivity

/-- **Approximation in a chart.** Let `A` be a measurable subset of a compact set `L` inside the
base set of an atlas chart `e`. The restriction to `A` of a measurable section `s` with
`p`-integrable fibre norm is approximated in `Lᵖ` by compactly supported smooth sections. -/
private theorem exists_eLpNorm_piecewise_sub_le (hp : p ≠ ⊤) (e : Trivialization F (π F E))
    [MemTrivializationAtlas e] {L A : Set B} (hL : IsCompact L) (hLe : L ⊆ e.baseSet)
    (hA : MeasurableSet A) [DecidablePred (· ∈ A)] (hAL : A ⊆ L) {s : ∀ x, E x}
    (hs : AEStronglyMeasurableSection 𝕜 F μ s) (hsp : MemLp (fun x ↦ ‖s x‖) p μ)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ t ∈ ContMDiffSection.compactlySupported I F ∞ E,
      eLpNorm (fun x ↦ ‖A.piecewise s 0 x - t x‖) p μ ≤ ε := by
  have := Manifold.locallyCompact_of_finiteDimensional (M := B) I
  -- An open `V ⊇ L` with compact closure inside the base set, on which `‖e.symm x v‖ ≤ C ‖v‖`.
  obtain ⟨V, hV, hLV, hVe, hVc⟩ := exists_open_between_and_isCompact_closure hL e.open_baseSet hLe
  obtain ⟨C, _, hC⟩ := e.exists_norm_symm_le_and_norm_le_of_isCompact 𝕜 hVc hVe
  -- The coordinates `g` of the piece of `s` over `A`, approximated by a smooth `g'` supported
  -- in `V`; then `x ↦ e.symm x (g' x)` approximates the piece.
  set g : B → F := A.indicator fun x ↦ (e ⟨x, s x⟩).2 with hgdef
  obtain ⟨η, hη, hηε⟩ := ENNReal.exists_nnreal_pos_mul_lt (a := C) ENNReal.coe_ne_top hε
  obtain ⟨g', -, hg'V, hg'⟩ := MemLp.exists_contMDiff_tsupport_subset_eLpNorm_sub_le I hp Fact.out
    (memLp_indicator_coord e hL hLe hA hAL hs hsp) hL.isClosed (hV.mem_nhdsSet.2 hLV)
    (.of_forall fun x hx ↦ indicator_of_notMem (fun h ↦ hx (hAL h)) _)
    (ENNReal.coe_ne_zero.2 hη.ne')
  have hg'K : tsupport g' ⊆ closure V := hg'V.trans subset_closure
  set t : Cₛ^∞⟮I; F, E⟯ := ⟨_, e.contMDiff_section_symmL g'.contMDiff (hg'K.trans hVe)⟩
  have ht_apply (x : B) : t x = e.symmL ℝ x (g' x) := rfl
  have htK : t.tsupport ⊆ closure V := by
    rw [ContMDiffSection.tsupport_def]
    have hsub : {x | t x ≠ 0} ⊆ Function.support g' := fun x hx ↦
      Function.mem_support.2 fun h0 ↦ hx (by rw [ht_apply, h0, map_zero])
    exact (closure_mono hsub).trans hg'K
  refine ⟨t, ContMDiffSection.mem_compactlySupported.2
    (hVc.of_isClosed_subset (ContMDiffSection.isClosed_tsupport t) htK), ?_⟩
  -- Pointwise, the piece minus `t` is `e.symm x (g x - g' x)`, of norm at most `C ‖g x - g' x‖`.
  have hbound (x : B) : ‖A.piecewise s 0 x - t x‖ ≤ C * ‖g x - g' x‖ := by
    have hpiece : A.piecewise s 0 x = e.symmL ℝ x (g x) := by
      by_cases hx : x ∈ A
      · rw [piecewise_eq_of_mem _ _ _ hx, hgdef, indicator_of_mem hx,
          e.symmL_apply (hLe (hAL hx)), e.symm_apply_apply_mk (hLe (hAL hx))]
      · rw [piecewise_eq_of_notMem _ _ _ hx, hgdef, indicator_of_notMem hx, map_zero,
          Pi.zero_apply]
    rw [hpiece, ht_apply, ← map_sub]
    by_cases hx : x ∈ closure V
    · rw [e.symmL_apply (hVe hx)]
      exact (hC x hx _).1
    · have hgx : g x = 0 :=
        indicator_of_notMem (fun h ↦ hx (subset_closure (hLV (hAL h)))) _
      have hg'x : g' x = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hx (hg'K h)
      simp [hgx, hg'x]
  calc eLpNorm (fun x ↦ ‖A.piecewise s 0 x - t x‖) p μ ≤ C • eLpNorm (g - ⇑g') p μ :=
        eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul ((hs.piecewise hA (.zero 𝕜 F E μ)).sub
          t.contMDiff.continuous.aestronglyMeasurableSection).aestronglyMeasurable_norm
          (.of_forall fun x ↦ by
            rw [← NNReal.coe_le_coe]
            simpa using hbound x) p
    _ ≤ C * η := by
        rw [ENNReal.smul_def, smul_eq_mul]
        gcongr
    _ ≤ ε := by rw [mul_comm]; exact hηε.le

/-- **Approximation over finitely many charts.** For compact sets `L x` inside the base sets of
the atlas charts at the points `x`, the restriction of `s` to a measurable set covered by finitely
many of the `L x` is approximated in `Lᵖ` by compactly supported smooth sections. -/
private theorem exists_eLpNorm_piecewise_sub_le_of_subset_biUnion (hp : p ≠ ⊤) {s : ∀ x, E x}
    (hs : AEStronglyMeasurableSection 𝕜 F μ s) (hsp : MemLp (fun x ↦ ‖s x‖) p μ)
    {L : B → Set B} (hL : ∀ x, IsCompact (L x))
    (hLe : ∀ x, L x ⊆ (trivializationAt F E x).baseSet) (T : Finset B) {A : Set B}
    (hA : MeasurableSet A) [DecidablePred (· ∈ A)] (hAT : A ⊆ ⋃ x ∈ T, L x) {ε : ℝ≥0∞}
    (hε : ε ≠ 0) :
    ∃ t ∈ ContMDiffSection.compactlySupported I F ∞ E,
      eLpNorm (fun x ↦ ‖A.piecewise s 0 x - t x‖) p μ ≤ ε := by
  classical
  induction T using Finset.induction_on generalizing A ε with
  | empty =>
    have hA0 : A = ∅ := by simpa using hAT
    refine ⟨0, zero_mem _, ?_⟩
    simp [hA0]
  | insert a T haT ih =>
    have hLa : MeasurableSet (L a) := (hL a).isClosed.measurableSet
    have hε2 : ε / 2 ≠ 0 := (ENNReal.half_pos hε).ne'
    obtain ⟨t₁, ht₁, h₁⟩ := exists_eLpNorm_piecewise_sub_le (I := I) hp (trivializationAt F E a)
      (hL a) (hLe a) (hA.inter hLa) inter_subset_right hs hsp hε2
    obtain ⟨t₂, ht₂, h₂⟩ := ih (hA.diff hLa) (fun x hx ↦ by
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (hAT hx.1)
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact absurd hxy hx.2
      · exact mem_iUnion₂.2 ⟨y, hy, hxy⟩) hε2
    refine ⟨t₁ + t₂, add_mem ht₁ ht₂, ?_⟩
    have hm (A : Set B) [DecidablePred (· ∈ A)] (hA : MeasurableSet A) (t : Cₛ^∞⟮I; F, E⟯) :
        AEStronglyMeasurable (fun x ↦ ‖A.piecewise s 0 x - t x‖) μ :=
      ((hs.piecewise hA (.zero 𝕜 F E μ)).sub
        t.contMDiff.continuous.aestronglyMeasurableSection).aestronglyMeasurable_norm
    calc eLpNorm (fun x ↦ ‖A.piecewise s 0 x - (t₁ + t₂) x‖) p μ
        ≤ eLpNorm ((fun x ↦ ‖(A ∩ L a).piecewise s 0 x - t₁ x‖) +
            fun x ↦ ‖(A \ L a).piecewise s 0 x - t₂ x‖) p μ := by
          refine eLpNorm_mono (hm A hA _) fun x ↦ ?_
          have hsplit : A.piecewise s 0 x - (t₁ + t₂) x =
              ((A ∩ L a).piecewise s 0 x - t₁ x) + ((A \ L a).piecewise s 0 x - t₂ x) := by
            rw [ContMDiffSection.coe_add, Pi.add_apply]
            by_cases hxA : x ∈ A <;> by_cases hxL : x ∈ L a <;> simp [hxA, hxL] <;> abel
          rw [hsplit, norm_norm, Pi.add_apply, Real.norm_of_nonneg (by positivity)]
          exact norm_add_le _ _
      _ ≤ ε / 2 + ε / 2 := (eLpNorm_add_le Fact.out).trans (add_le_add h₁ h₂)
      _ = ε := ENNReal.add_halves ε

namespace LpSection

/-- **Density of compactly supported smooth sections.** Over a finite-dimensional, Hausdorff,
second-countable manifold, with a measure on its Borel sets that is finite on compact sets, the
classes of compactly supported smooth sections are dense in `Lᵖ(E, μ)` for `p < ∞`, when the model
fibre is finite-dimensional and the fibre norms are continuous. -/
theorem denseRange_ofCompactlySupported (hp : p ≠ ⊤) :
    DenseRange (ofCompactlySupported 𝕜 I p μ (F := F) (E := E)) := by
  classical
  have := Manifold.locallyCompact_of_finiteDimensional (M := B) I
  refine Metric.denseRange_iff.2 fun f r hr ↦ ?_
  have hε : ENNReal.ofReal (r / 2) ≠ 0 := by simpa using half_pos hr
  have hε2 := (ENNReal.half_pos hε).ne'
  -- Off the compact support `K` of a continuous `h` close to `x ↦ ‖f x‖`, `f` is small.
  obtain ⟨h, hhc, hh, hhcont, -⟩ := f.memLp_norm.exists_hasCompactSupport_eLpNorm_sub_le hp hε2
  -- `K` is covered by finitely many compact sets inside base sets of atlas charts.
  choose L hL hxL hLe using fun x : B ↦ exists_compact_subset
    (trivializationAt F E x).open_baseSet (FiberBundle.mem_baseSet_trivializationAt' x)
  obtain ⟨T, -, hKT⟩ := hhc.elim_nhds_subcover L fun x _ ↦ mem_interior_iff_mem_nhds.1 (hxL x)
  obtain ⟨t, ht, htK⟩ := exists_eLpNorm_piecewise_sub_le_of_subset_biUnion (I := I) hp
    f.aestronglyMeasurableSection f.memLp_norm hL hLe T hhc.isClosed.measurableSet hKT hε2
  refine ⟨⟨t, ht⟩, ?_⟩
  have hbound (x : B) :
      ‖f x - t x‖ ≤ ‖((fun y ↦ ‖f y‖) - h) x‖ + ‖(tsupport h).piecewise f 0 x - t x‖ := by
    by_cases hx : x ∈ tsupport h
    · rw [piecewise_eq_of_mem _ _ _ hx]
      exact le_add_of_nonneg_left (norm_nonneg _)
    · rw [piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply, zero_sub, norm_neg, Pi.sub_apply,
        image_eq_zero_of_notMem_tsupport hx, sub_zero, norm_norm]
      exact norm_sub_le _ _
  have hle : eLpNorm (fun x ↦ ‖f x - t x‖) p μ ≤ ENNReal.ofReal (r / 2) :=
    calc _ ≤ eLpNorm ((fun x ↦ ‖((fun y ↦ ‖f y‖) - h) x‖) +
            fun x ↦ ‖(tsupport h).piecewise f 0 x - t x‖) p μ :=
          eLpNorm_mono ((f.aestronglyMeasurableSection.sub
            t.contMDiff.continuous.aestronglyMeasurableSection).aestronglyMeasurable_norm)
            fun x ↦ by
              rw [norm_norm, Pi.add_apply, Real.norm_of_nonneg (by positivity)]
              exact hbound x
      _ ≤ eLpNorm ((fun y ↦ ‖f y‖) - h) p μ +
            eLpNorm (fun x ↦ ‖(tsupport h).piecewise f 0 x - t x‖) p μ := by
          rw [← eLpNorm_norm ((fun y ↦ ‖f y‖) - h)
            (f.aestronglyMeasurable_norm.sub hhcont.aestronglyMeasurable)]
          exact eLpNorm_add_le Fact.out
      _ ≤ ENNReal.ofReal (r / 2) / 2 + ENNReal.ofReal (r / 2) / 2 := add_le_add hh htK
      _ = ENNReal.ofReal (r / 2) := ENNReal.add_halves _
  have hrep : ‖f - ofCompactlySupported 𝕜 I p μ ⟨t, ht⟩‖ =
      (eLpNorm (fun x ↦ ‖f x - t x‖) p μ).toReal := by
    rw [norm_def]
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [coeFn_sub f (ofCompactlySupported 𝕜 I p μ ⟨t, ht⟩),
      coeFn_ofCompactlySupported (𝕜 := 𝕜) (p := p) (μ := μ) ⟨t, ht⟩] with x h1 h2
    rw [h1, h2]
  rw [dist_eq_norm, hrep]
  calc _ ≤ (ENNReal.ofReal (r / 2)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = r / 2 := ENNReal.toReal_ofReal (half_pos hr).le
    _ < r := half_lt_self hr

end LpSection

end Approximation

end TauCeti
