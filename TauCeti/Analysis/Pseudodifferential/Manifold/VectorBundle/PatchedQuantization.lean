/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.ChartQuantization
public import TauCeti.Analysis.Pseudodifferential.Manifold.VectorBundle.Smoothing

/-!
# Patching pseudodifferential operators between bundles from chart quantizations

Let `M` be a manifold modelled on `ℝⁿ` and `E`, `F` smooth complex vector bundles over `M` with
finite-dimensional model fibres `V` and `W`. A pseudodifferential operator `Γ(E) → Γ(F)` is
assembled from local data by **patching**: for finitely many charts `eᵢ`, trivializations `tᵢ` of
`E` and `t'ᵢ` of `F` over their sources, cutoffs and classical symbols `aᵢ` with values in
`V →L[ℂ] W`, the patched operator is the sum `∑ᵢ Op_{eᵢ}(aᵢ)` of the chart quantizations
`s ↦ t'ᵢ⁻¹ (φᵢ · Op(aᵢ) (ψᵢ · tᵢ(s ∘ eᵢ⁻¹))) ∘ eᵢ`
(`OpenPartialHomeomorph.sectionChartQuantization`). Each chart quantization of a classical symbol
of order `m` is a classical pseudodifferential operator of order `m` between the bundles
(`OpenPartialHomeomorph.sectionChartQuantization_mem_sectionClassicalPseudodifferentialOperators`),
and so is every patched operator.

This file proves the converse, modulo operators of order `-∞`
(`TauCeti.sectionSmoothingPseudodifferentialOperators`), following Hörmander (III, §18.1) and
Melrose (§5.3). Let `P : Γ(E) → Γ(F)` be a classical pseudodifferential operator of order `m`, let
`ρᵢ` be cutoffs in the charts `eᵢ`, `χᵢ` cutoffs equal to `1` near the supports of the `ρᵢ`, and
`aᵢ` the symbol of the chart compression of `P` by `ρᵢ` and `χᵢ`
(`TauCeti.exists_quantizeSchwartzValue_eq_apply_chartCutoffSection`). Then

`(∑ᵢ ρᵢ) P - ∑ᵢ Op_{eᵢ}(aᵢ)` has order `-∞`

(`sum_smul_sub_sum_sectionChartQuantization_mem_sectionSmoothingPseudodifferentialOperators`),
where the chart quantizations are localized by cutoffs equal to `1` on the supports of `ρᵢ` and
`χᵢ`. Each `Op_{eᵢ}(aᵢ)` is `ρᵢ P χᵢ`
(`OpenPartialHomeomorph.sectionChartQuantization_eq_smul_comp_comp_smul`), so the difference is
`∑ᵢ ρᵢ P (1 - χᵢ)`, which has order `-∞` by pseudolocality
(`TauCeti.smul_comp_smul_mem_sectionSmoothingPseudodifferentialOperators`). When the `ρᵢ` add up
to `1`, this says that `P` is its own patched quantization modulo order `-∞`
(`TauCeti.sub_sum_sectionChartQuantization_mem_sectionSmoothingPseudodifferentialOperators`). In
particular two patchings of `P` from its chart symbols, over different atlases, partitions of unity
and cutoffs, differ by an operator of order `-∞`.

On a compact manifold such data exist once and for all: finitely many charts, each with its source
inside the base sets of the preferred trivializations of `E` and `F` at a point, and cutoffs in
them, such that every classical pseudodifferential operator `P` of every order `m` is a sum of chart
quantizations of classical symbols of order `m` modulo order `-∞`
(`TauCeti.exists_sub_sum_sectionChartQuantization_mem_sectionSmoothingPseudodifferentialOperators`).
Consequently the classical pseudodifferential operators of order `m` between the bundles are
exactly the operators spanned by chart quantizations of classical symbols of order `m`, up to
operators of order `-∞`
(`TauCeti.sectionClassicalPseudodifferentialOperators_eq_span_sectionChartQuantization_sup`): the
class defined by its matrix entries in cut-off frames (`TauCeti.sectionEntry`) agrees with the class
of patched quantizations.

These are the bundle versions of the scalar
`TauCeti.mulLeft_sum_comp_sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators` and
`TauCeti.sub_sum_chartQuantization_mem_smoothingPseudodifferentialOperators`
(`Manifold/Smoothing.lean`), and the proofs follow theirs. The compact theorem works in charts
restricted to the base sets of the trivializations, with the cutoffs summing to `1` supplied by
`TauCeti.exists_sum_complexCutoffPullback_eq_one`.

## Main results

* `sum_smul_sub_sum_sectionChartQuantization_mem_sectionSmoothingPseudodifferentialOperators`:
  `(∑ᵢ ρᵢ) P` differs from the patched quantization of its chart symbols by an operator of order
  `-∞`.
* `TauCeti.sub_sum_sectionChartQuantization_mem_sectionSmoothingPseudodifferentialOperators`: when
  the `ρᵢ` add up to `1`, `P` itself does.
* `TauCeti.exists_sub_sum_sectionChartQuantization_mem_sectionSmoothingPseudodifferentialOperators`:
  on a compact manifold, fixed charts and cutoffs exhibit every classical pseudodifferential
  operator between the bundles as a sum of chart quantizations modulo order `-∞`.
* `TauCeti.sectionClassicalPseudodifferentialOperators_eq_span_sectionChartQuantization_sup`: on a
  compact manifold, the classical pseudodifferential operators of order `m` between the bundles are
  the span of the chart quantizations plus the operators of order `-∞`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1
  (pseudodifferential operators between sections of vector bundles).
* R. Melrose, *Introduction to Microlocal Analysis*, §5.3.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, §8.
-/

public section

noncomputable section

open Bundle Filter Set
open scoped ContDiff Distributions Manifold SchwartzMap Topology

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (CoordinateSpace n) M] [T2Space M]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {E : M → Type*} [TopologicalSpace (TotalSpace V E)] [∀ x, AddCommGroup (E x)]
  [∀ x, Module ℝ (E x)] [∀ x, Module ℂ (E x)] [∀ x, TopologicalSpace (E x)] [FiberBundle V E]
  [VectorBundle ℝ V E] [VectorBundle ℂ V E] [ContMDiffVectorBundle ∞ V E 𝓘(ℝ, CoordinateSpace n)]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
  {F : M → Type*} [TopologicalSpace (TotalSpace W F)] [∀ x, AddCommGroup (F x)]
  [∀ x, Module ℝ (F x)] [∀ x, Module ℂ (F x)] [∀ x, TopologicalSpace (F x)] [FiberBundle W F]
  [VectorBundle ℝ W F] [VectorBundle ℂ W F] [ContMDiffVectorBundle ∞ W F 𝓘(ℝ, CoordinateSpace n)]
  {m : ℝ}
  {P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ] Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯}

/-! ### Patching modulo operators of order `-∞` -/

section Patching

variable {ι : Type*} {s : Finset ι} {e : ι → OpenPartialHomeomorph M (CoordinateSpace n)}
  {he : ∀ i, e i ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M}
  {t : ι → Trivialization V (π V E)} [∀ i, MemTrivializationAtlas (t i)]
  {t' : ι → Trivialization W (π W F)} [∀ i, MemTrivializationAtlas (t' i)]
  (hE : ∀ i, (e i).source ⊆ (t i).baseSet) (hF : ∀ i, (e i).source ⊆ (t' i).baseSet)
  {ρ χ φ ψ : ∀ i, 𝓓(⟨(e i).target, (e i).open_target⟩, ℝ)} {a : ι → ClassicalSymbol n V W m}

/-- **Operators between bundles are patched from their chart symbols, modulo order `-∞`.** Let `P`
be a classical pseudodifferential operator of order `m` from the sections of `E` to those of `F`.
For finitely many charts `eᵢ` whose sources lie in the base sets of trivializations `tᵢ` of `E` and
`t'ᵢ` of `F`, let `ρᵢ` be cutoffs, `χᵢ` cutoffs equal to `1` near the supports of the `ρᵢ`, and
`aᵢ` the symbol of the chart compression `u ↦ ρᵢ · t'ᵢ (P (tᵢ⁻¹ ((χᵢ u) ∘ eᵢ))) ∘ eᵢ⁻¹` of `P`.
If `φᵢ` and `ψᵢ` are cutoffs equal to `1` on the supports of `ρᵢ` and `χᵢ`, then `(∑ᵢ ρᵢ) P` and the
patched operator `∑ᵢ Op_{eᵢ}(aᵢ)`, localized by the `φᵢ` and `ψᵢ`, differ by an operator of order
`-∞`. -/
theorem sum_smul_sub_sum_sectionChartQuantization_mem_sectionSmoothingPseudodifferentialOperators
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hχ : ∀ i ∈ s, ∀ᶠ y in 𝓝ˢ (tsupport (ρ i)), χ i y = 1)
    (ha : ∀ i ∈ s, ∀ (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n),
      quantizeSchwartzValue (a i).toSymbol.coefficient u y =
        ρ i y • (t' i).continuousLinearMapAt ℂ ((e i).symm y)
          (P ((t i).chartCutoffSection (he i) (hE i) (χ i) u) ((e i).symm y)))
    (hφ : ∀ i ∈ s, ∀ y ∈ tsupport (ρ i), φ i y = 1)
    (hψ : ∀ i ∈ s, ∀ y ∈ tsupport (χ i), ψ i y = 1) :
    (∑ i ∈ s, (e i).complexCutoffPullback (he i) (ρ i) 1) • P -
        ∑ i ∈ s, (e i).sectionChartQuantization (he i) (t i) (t' i) (φ i) (ψ i)
          (((e i).symm_image_tsupport_subset_source (φ i)).trans (hF i))
          (((e i).symm_image_tsupport_subset_source (ψ i)).trans (hE i)) (a i) ∈
      sectionSmoothingPseudodifferentialOperators := by
  -- Each chart quantization is `ρᵢ P χᵢ`, so the difference is `∑ᵢ ρᵢ P (1 - χᵢ)`.
  have key : (∑ i ∈ s, (e i).complexCutoffPullback (he i) (ρ i) 1) • P -
      ∑ i ∈ s, (e i).sectionChartQuantization (he i) (t i) (t' i) (φ i) (ψ i)
        (((e i).symm_image_tsupport_subset_source (φ i)).trans (hF i))
        (((e i).symm_image_tsupport_subset_source (ψ i)).trans (hE i)) (a i) =
      ∑ i ∈ s, (e i).complexCutoffPullback (he i) (ρ i) 1 •
        (P ∘ₗ ((1 - (e i).complexCutoffPullback (he i) (χ i) 1) • LinearMap.id)) := by
    rw [Finset.sum_congr rfl fun i hi ↦
      (e i).sectionChartQuantization_eq_smul_comp_comp_smul (he i) (t i) (t' i) (hE i) (hF i)
        (ha i hi) (hφ i hi) (hψ i hi), Finset.sum_smul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun _ _ ↦ ?_
    ext u x
    simp [sub_smul, smul_sub]
  rw [key]
  exact Submodule.sum_mem _ fun i hi ↦
    smul_comp_smul_mem_sectionSmoothingPseudodifferentialOperators hP
      (OpenPartialHomeomorph.disjoint_tsupport_complexCutoffPullback_one_sub (he i) (hχ i hi))

/-- **An operator between bundles is the patched quantization of its chart symbols, modulo order
`-∞`.** In the setting of
`sum_smul_sub_sum_sectionChartQuantization_mem_sectionSmoothingPseudodifferentialOperators`,
if the cutoffs `ρᵢ`, read on `M`, add up to `1`, then `P - ∑ᵢ Op_{eᵢ}(aᵢ)` has order `-∞`. -/
theorem sub_sum_sectionChartQuantization_mem_sectionSmoothingPseudodifferentialOperators
    (hP : P ∈ sectionClassicalPseudodifferentialOperators m)
    (hρ : ∑ i ∈ s, (e i).complexCutoffPullback (he i) (ρ i) 1 = 1)
    (hχ : ∀ i ∈ s, ∀ᶠ y in 𝓝ˢ (tsupport (ρ i)), χ i y = 1)
    (ha : ∀ i ∈ s, ∀ (u : 𝓢(CoordinateSpace n, V)) (y : CoordinateSpace n),
      quantizeSchwartzValue (a i).toSymbol.coefficient u y =
        ρ i y • (t' i).continuousLinearMapAt ℂ ((e i).symm y)
          (P ((t i).chartCutoffSection (he i) (hE i) (χ i) u) ((e i).symm y)))
    (hφ : ∀ i ∈ s, ∀ y ∈ tsupport (ρ i), φ i y = 1)
    (hψ : ∀ i ∈ s, ∀ y ∈ tsupport (χ i), ψ i y = 1) :
    P - ∑ i ∈ s, (e i).sectionChartQuantization (he i) (t i) (t' i) (φ i) (ψ i)
        (((e i).symm_image_tsupport_subset_source (φ i)).trans (hF i))
        (((e i).symm_image_tsupport_subset_source (ψ i)).trans (hE i)) (a i) ∈
      sectionSmoothingPseudodifferentialOperators := by
  simpa only [hρ, one_smul] using
    sum_smul_sub_sum_sectionChartQuantization_mem_sectionSmoothingPseudodifferentialOperators
      hE hF hP hχ ha hφ hψ

end Patching

/-! ### Operators on a compact manifold -/

section Compact

variable [CompactSpace M] [IsManifold 𝓘(ℝ, CoordinateSpace n) ∞ M]

/-- **On a compact manifold, operators between bundles are finite sums of chart quantizations
modulo order `-∞`.** If `M` is compact, there are finitely many points `x`, charts `eₓ` of the
maximal atlas whose sources lie in the base sets of the trivializations of `E` and `F` at `x`, and
cutoffs `φₓ`, `ψₓ` in their targets, such that every classical pseudodifferential operator `P` of
any order `m` from the sections of `E` to those of `F` differs from a sum `∑ₓ Op_{eₓ}(aₓ)` of chart
quantizations of classical symbols `aₓ` of order `m` by an operator of order `-∞`. The charts and
cutoffs do not depend on `P`. -/
theorem exists_sub_sum_sectionChartQuantization_mem_sectionSmoothingPseudodifferentialOperators :
    ∃ (s : Finset M) (e : M → OpenPartialHomeomorph M (CoordinateSpace n))
      (he : ∀ x, e x ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
      (hE : ∀ x, (e x).source ⊆ (trivializationAt V E x).baseSet)
      (hF : ∀ x, (e x).source ⊆ (trivializationAt W F x).baseSet)
      (φ ψ : ∀ x, 𝓓(⟨(e x).target, (e x).open_target⟩, ℝ)),
      ∀ (m : ℝ) (P : Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); V, E⟯ →ₗ[ℂ]
        Cₛ^∞⟮𝓘(ℝ, CoordinateSpace n); W, F⟯),
        P ∈ sectionClassicalPseudodifferentialOperators m → ∃ a : ∀ _ : M, ClassicalSymbol n V W m,
          P - ∑ x ∈ s, (e x).sectionChartQuantization (he x) (trivializationAt V E x)
              (trivializationAt W F x) (φ x) (ψ x)
              (((e x).symm_image_tsupport_subset_source (φ x)).trans (hF x))
              (((e x).symm_image_tsupport_subset_source (ψ x)).trans (hE x)) (a x) ∈
            sectionSmoothingPseudodifferentialOperators := by
  -- The chart at `x`, restricted to the base sets of the trivializations of `E` and `F` at `x`.
  set U : M → Set M := fun x ↦ (trivializationAt V E x).baseSet ∩ (trivializationAt W F x).baseSet
  have hU (x : M) : IsOpen (U x) :=
    (trivializationAt V E x).open_baseSet.inter (trivializationAt W F x).open_baseSet
  set e : M → OpenPartialHomeomorph M (CoordinateSpace n) := fun x ↦ (chartAt _ x).restr (U x)
  have he (x : M) : e x ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M :=
    restr_mem_maximalAtlas _ (IsManifold.chart_mem_maximalAtlas x) (hU x)
  have hsource (x : M) : (e x).source = (chartAt _ x).source ∩ U x :=
    (chartAt _ x).restr_source' _ (hU x)
  have hE (x : M) : (e x).source ⊆ (trivializationAt V E x).baseSet :=
    (hsource x).subset.trans (inter_subset_right.trans inter_subset_left)
  have hF (x : M) : (e x).source ⊆ (trivializationAt W F x).baseSet :=
    (hsource x).subset.trans (inter_subset_right.trans inter_subset_right)
  -- Cutoffs `ρ x` in the charts `e x` at the finitely many `x ∈ s` whose pullbacks add up to `1`;
  -- `χ x` and `ψ x` are cutoffs equal to `1` near the supports of `ρ x` and `χ x`, and `a x` is
  -- the chart symbol of `P`.
  obtain ⟨s, ρ, hρ⟩ := exists_sum_complexCutoffPullback_eq_one e he fun x ↦ by
    rw [hsource x]
    exact ⟨mem_chart_source _ x, mem_baseSet_trivializationAt V E x,
      mem_baseSet_trivializationAt W F x⟩
  choose χ hχ using fun x ↦ TestFunction.exists_eventually_eq_one (n := ⊤)
    (ρ x).hasCompactSupport.isCompact (ρ x).tsupport_subset
  choose ψ hψ using fun x ↦ TestFunction.exists_eventually_eq_one (n := ⊤)
    (χ x).hasCompactSupport.isCompact (χ x).tsupport_subset
  refine ⟨s, e, he, hE, hF, χ, ψ, fun m P hP ↦ ?_⟩
  choose a ha using fun x ↦ exists_quantizeSchwartzValue_eq_apply_chartCutoffSection (he x)
    (trivializationAt V E x) (hE x) hP (trivializationAt W F x) (hF x) (ρ x) (χ x)
  exact ⟨a, sub_sum_sectionChartQuantization_mem_sectionSmoothingPseudodifferentialOperators
    hE hF hP hρ (fun x _ ↦ (hχ x).1) (fun x _ ↦ ha x)
    (fun x _ y hy ↦ (hχ x).1.self_of_nhdsSet y hy) (fun x _ y hy ↦ (hψ x).1.self_of_nhdsSet y hy)⟩

variable (n M V E W F m) in
/-- **On a compact manifold, the classical pseudodifferential operators between bundles are the
patched quantizations, modulo order `-∞`.** If `M` is compact, the classical pseudodifferential
operators of order `m` from the sections of `E` to those of `F` are the operators of order `-∞`
plus the complex span of the chart quantizations `Op_e(a)` of classical symbols `a` of order `m`
with values in `V →L[ℂ] W`, over all charts `e` of the maximal atlas, trivializations `t` of `E`
and `t'` of `F` in their atlases, and cutoffs `φ`, `ψ` in the chart target such that `e⁻¹(supp φ)`
lies in the base set of `t'` and `e⁻¹(supp ψ)` in that of `t`. -/
theorem sectionClassicalPseudodifferentialOperators_eq_span_sectionChartQuantization_sup :
    sectionClassicalPseudodifferentialOperators (V := V) (E := E) (W := W) (F := F) m =
      Submodule.span ℂ
          {Q | ∃ (e : OpenPartialHomeomorph M (CoordinateSpace n))
            (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, CoordinateSpace n) ∞ M)
            (t : Trivialization V (π V E)) (_ : MemTrivializationAtlas t)
            (t' : Trivialization W (π W F)) (_ : MemTrivializationAtlas t')
            (φ ψ : 𝓓(⟨e.target, e.open_target⟩, ℝ)) (hφ : e.symm '' tsupport φ ⊆ t'.baseSet)
            (hψ : e.symm '' tsupport ψ ⊆ t.baseSet) (a : ClassicalSymbol n V W m),
            e.sectionChartQuantization he t t' φ ψ hφ hψ a = Q} ⊔
        sectionSmoothingPseudodifferentialOperators := by
  refine le_antisymm (fun P hP ↦ ?_) (sup_le (Submodule.span_le.2 ?_)
    (sectionSmoothingPseudodifferentialOperators_le_sectionClassicalPseudodifferentialOperators m))
  · obtain ⟨s, e, he, hE, hF, φ, ψ, h⟩ :=
      exists_sub_sum_sectionChartQuantization_mem_sectionSmoothingPseudodifferentialOperators
        (n := n) (M := M) (V := V) (E := E) (W := W) (F := F)
    obtain ⟨a, ha⟩ := h m P hP
    -- `P` is the sum of the chart quantizations plus an operator of order `-∞`.
    refine Submodule.mem_sup.2 ⟨_, ?_, _, ha, add_sub_cancel _ _⟩
    exact Submodule.sum_mem _ fun x _ ↦ Submodule.subset_span ⟨e x, he x, _, inferInstance, _,
      inferInstance, φ x, ψ x, _, _, a x, rfl⟩
  · rintro _ ⟨e, he, t, _, t', _, φ, ψ, hφ, hψ, a, rfl⟩
    exact e.sectionChartQuantization_mem_sectionClassicalPseudodifferentialOperators he t t' φ ψ hφ
      hψ a

end Compact

end TauCeti
