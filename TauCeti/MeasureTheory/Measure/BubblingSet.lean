/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Data.ENNReal.NatCastDiv
import TauCeti.MeasureTheory.Integral.EnergyConcentration
import TauCeti.Order.Filter.AtTopBot
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Bubbling sets on countable unions of windows

Compactness theorems for pseudoholomorphic curves and Floer solutions are first proved on a
single window: a sequence of solutions with uniformly bounded energy has a subsequence that
converges locally uniformly off a finite set `Z` of *bubbling points*, at each of which a fixed
quantum `δ > 0` of energy concentrates. This file assembles such statements over a countable
family of open windows `Uᵢ` into one statement on their union, which is how compactness on a
noncompact domain, such as a surface with cylindrical ends, follows from compactness on compact
pieces of it.

Let `Fₙ : X → α` be a sequence of maps and `μₙ` a sequence of measures on `X` (the energy
measures of the maps) with `μₙ (⋃ᵢ Uᵢ) ≤ E < ∞`. Suppose that for every window `Uᵢ`, every
subsequence of `Fₙ` has a further subsequence and a set `Zᵢ` such that

* at every point `z ∈ Zᵢ` the energy `δ` concentrates: every neighbourhood `N` of `z` eventually
  has `μ N ≥ δ` along the subsequence;
* the subsequence converges locally uniformly on `Uᵢ \ Zᵢ`.

Then a single subsequence of `Fₙ` converges locally uniformly on `(⋃ᵢ Uᵢ) \ Z` for a finite set
`Z` with `#Z * δ ≤ E`, and the energy `δ` concentrates at every point of `Z`
(`TauCeti.exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion`). If moreover functions
`Gₙ`, such as the energy densities of the maps, are eventually bounded above near every point of
`Uᵢ \ Zᵢ` along the subsequences of the windows, then they are eventually bounded above near
every point of `(⋃ᵢ Uᵢ) \ Z` along the single subsequence
(`TauCeti.exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion_of_le`).

The subsequence is the diagonal of the subsequences chosen successively on the windows. Energy
concentration and locally uniform convergence along a filter pass to finer filters, so the diagonal
has the properties of every window (`TauCeti.extraction_forall_of_antitone`). The bubbling
set `Z` is the union of the bubbling sets of the windows. Distinct bubbling points have disjoint
neighbourhoods, each of which eventually carries energy at least `δ`, so every finite subset of
`Z` has at most `E / δ` points (`TauCeti.card_mul_le_of_forall_eventually_le_measure`). Hence `Z`
is finite with `#Z * δ ≤ E` (`Set.finite_of_forall_finset_card_mul_le`), even though the sets
`Zᵢ` are not assumed to be finite. The limits on the windows glue to a limit on `(⋃ᵢ Uᵢ) \ Z`
(`TauCeti.exists_tendstoLocallyUniformlyOn_iUnion_sdiff`). The uniform quantum `δ` is essential:
the thresholds of infinitely many windows need not be bounded below otherwise.

Without a uniform quantum, on open windows `Oⱼ` exhausting a set `Ω`, with finite bubbling sets
`Zⱼ` and thresholds `δⱼ > 0` depending on the window, the points of `Ω` lying in no regular part
`Oⱼ \ Zⱼ` still form a set meeting every compact subset of `Ω` in finitely many points, each
carrying a positive amount of energy, and bounds on the compact subsets of the regular parts give
bounds on the compact subsets of their union
(`TauCeti.exists_bubblingSet_of_forall_window`).

## Main results

* `TauCeti.exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion`: convergence off finitely
  many bubbling points on a countable union of windows.
* `TauCeti.exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion_of_le`: the same, with local
  bounds off the bubbling points.
* `TauCeti.exists_bubblingSet_of_forall_window`: the bubbling set of an exhaustion by windows with
  thresholds depending on the window.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6,
  on bubbling off finitely many points and the exhaustion of a noncompact domain by compact sets.
-/

public section

open Filter Set Topology MeasureTheory
open scoped ENNReal

namespace TauCeti

/-- **The bubbling set of an exhaustion by windows.** Let open windows `Oⱼ`, directed under
inclusion, cover `Ω`, and let `Zⱼ` be finite sets. Let the densities `fᵢ` be nonnegative and
integrable on measurable sets `Uᵢ`, each window eventually lying in `Uᵢ` along `l`. Suppose that
along `l`, every ball about a point of `Zⱼ` eventually carries `∫ fᵢ ≥ δⱼ > 0` within `Oⱼ`, and the
functions `gᵢ` are eventually bounded above on every compact subset of `Oⱼ \ Zⱼ`. Then the set
`Z ⊆ Ω` of points lying in no regular part `Oⱼ \ Zⱼ` meets every compact subset of `Ω` in a finite
set, every ball about a point of `Z` eventually carries `∫ fᵢ ≥ δ` within `Uᵢ` for some `δ > 0`, and
the `gᵢ` are eventually bounded above on every compact subset of `Ω \ Z = ⋃ⱼ (Oⱼ \ Zⱼ)`. -/
theorem exists_bubblingSet_of_forall_window {X κ ι β : Type*} [MetricSpace X]
    [LocallyCompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X}
    [Preorder β] [IsDirected β (· ≤ ·)] [Nonempty β] {Ω : Set X} {O : κ → Set X}
    (hO : ∀ j, IsOpen (O j)) (hOd : Directed (· ⊆ ·) O) (hOΩ : ⋃ j, O j = Ω)
    {Zw : κ → Finset X} {l : Filter ι} {U : ι → Set X} {f : ι → X → ℝ} {g : ι → X → β}
    {δ : κ → ℝ} (hU : ∀ i, MeasurableSet (U i)) (hint : ∀ i, IntegrableOn (f i) (U i) μ)
    (hf0 : ∀ i, ∀ y ∈ U i, 0 ≤ f i y) (hOU : ∀ j, ∀ᶠ i in l, O j ⊆ U i) (hδ : ∀ j, 0 < δ j)
    (hconc : ∀ j, ∀ z ∈ Zw j, ∀ ε > 0, ∀ᶠ i in l, δ j ≤ ∫ y in Metric.ball z ε ∩ O j, f i y ∂μ)
    (hbd : ∀ j C, IsCompact C → C ⊆ O j \ ↑(Zw j) → ∃ A, ∀ᶠ i in l, ∀ y ∈ C, g i y ≤ A) :
    ∃ Z ⊆ Ω, Ω \ Z = ⋃ j, O j \ ↑(Zw j) ∧ (∀ C, IsCompact C → C ⊆ Ω → (Z ∩ C).Finite) ∧
      (∀ z ∈ Z, ∃ δ > 0, ∀ ε > 0, ∀ᶠ i in l, δ ≤ ∫ y in Metric.ball z ε ∩ U i, f i y ∂μ) ∧
      ∀ C, IsCompact C → C ⊆ Ω \ Z → ∃ A, ∀ᶠ i in l, ∀ y ∈ C, g i y ≤ A := by
  have hΩZ : Ω \ (Ω \ ⋃ j, O j \ ↑(Zw j)) = ⋃ j, O j \ ↑(Zw j) :=
    sdiff_sdiff_cancel_left (iUnion_subset fun j ↦ sdiff_subset.trans (hOΩ ▸ subset_iUnion O j))
  refine ⟨_, sdiff_subset, hΩZ, fun C hC hCΩ ↦ ?_, fun z hz ↦ ?_, fun C hC hCZ ↦ ?_⟩
  · -- A compact set lies in some window `O m`, so it only meets the bubbling points of `O m`.
    cases isEmpty_or_nonempty κ
    · exact finite_empty.subset fun y hy ↦ by simpa [← hOΩ] using hCΩ hy.2
    obtain ⟨m, hm⟩ := hC.elim_directed_cover O hO (hOΩ ▸ hCΩ) hOd
    exact (Zw m).finite_toSet.subset fun y hy ↦
      by_contra fun hyZ ↦ hy.1.2 (mem_iUnion.2 ⟨m, hm hy.2, hyZ⟩)
  · -- Energy concentrates at `z` on a window containing it, which eventually lies in `U i`.
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hOΩ.symm ▸ hz.1 : z ∈ ⋃ j, O j)
    have hzZ : z ∈ Zw j := by_contra fun h ↦ hz.2 (mem_iUnion.2 ⟨j, hj, h⟩)
    refine ⟨δ j, hδ j, fun ε hε ↦ ?_⟩
    filter_upwards [hconc j z hzZ ε hε, hOU j] with i hi hOU
    exact hi.trans (setIntegral_mono_set ((hint i).mono_set inter_subset_right)
      (ae_restrict_of_forall_mem (measurableSet_ball.inter (hU i)) fun y hy ↦
        hf0 i y hy.2)
      (inter_subset_inter_right _ hOU).eventuallySubset)
  · -- Bounds on compact neighbourhoods of the points of `C`, from their windows, cover `C`.
    refine hC.exists_eventually_forall_le_of_forall fun y hy ↦ ?_
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hΩZ ▸ hCZ hy)
    obtain ⟨s, hs, hsG, hsc⟩ :=
      local_compact_nhds (((hO j).sdiff (Zw j).finite_toSet.isClosed).mem_nhds hj)
    exact ⟨s, mem_nhdsWithin_of_mem_nhds hs, hbd j s hsc hsG⟩

variable {X α : Type*} [TopologicalSpace X] [UniformSpace α] [MeasurableSpace X]

/-- **Convergence off finitely many bubbling points on a countable union of windows, with local
bounds.** Let `Uᵢ` be countably many open sets, `Fₙ : X → α` maps, `Gₙ : X → ℝ` functions (the
energy densities of the maps) and `μₙ` measures on `X` with `μₙ (⋃ᵢ Uᵢ) ≤ E < ∞`, and let `δ > 0`.
Suppose that for every window `Uᵢ` and every subsequence `ψ`, there are a further subsequence
`ψ ∘ φ`, a set `Zᵢ` and a map `vᵢ` such that every neighbourhood of a point of `Zᵢ` eventually
carries `μ`-energy at least `δ` along `ψ ∘ φ`, the functions `G ∘ ψ ∘ φ` are eventually bounded
above near every point of `Uᵢ \ Zᵢ`, and `F ∘ ψ ∘ φ → vᵢ` locally uniformly on `Uᵢ \ Zᵢ`. Then
there are a subsequence `φ`, a finite set `Z ⊆ ⋃ᵢ Uᵢ` with `#Z * δ ≤ E` and a map `v` such that
every neighbourhood of a point of `Z` eventually carries energy at least `δ` along `φ`, the
functions `G ∘ φ` are eventually bounded above near every point of `(⋃ᵢ Uᵢ) \ Z`, and
`F ∘ φ → v` locally uniformly on `(⋃ᵢ Uᵢ) \ Z`. -/
theorem exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion_of_le [T2Space X]
    [OpensMeasurableSpace X] [T2Space α] {ι : Type*} [Countable ι] {U : ι → Set X}
    (hU : ∀ i, IsOpen (U i)) {F : ℕ → X → α} {G : ℕ → X → ℝ} {μ : ℕ → Measure X}
    {δ E : ℝ≥0∞} (hδ : δ ≠ 0) (hE : E ≠ ∞) (hμ : ∀ n, μ n (⋃ i, U i) ≤ E)
    (h : ∀ i ⦃ψ : ℕ → ℕ⦄, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Set X,
      (∀ z ∈ Z, ∀ N ∈ 𝓝 z, ∀ᶠ n in atTop, δ ≤ μ (ψ (φ n)) N) ∧
      (∀ y ∈ U i \ Z, ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in atTop, ∀ x ∈ N, G (ψ (φ n)) x ≤ A) ∧
      ∃ v : X → α, TendstoLocallyUniformlyOn (fun n ↦ F (ψ (φ n))) v atTop (U i \ Z)) :
    ∃ (φ : ℕ → ℕ) (Z : Finset X) (v : X → α), StrictMono φ ∧ ↑Z ⊆ ⋃ i, U i ∧
      Z.card * δ ≤ E ∧ (∀ z ∈ Z, ∀ N ∈ 𝓝 z, ∀ᶠ n in atTop, δ ≤ μ (φ n) N) ∧
      (∀ y ∈ (⋃ i, U i) \ ↑Z, ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in atTop, ∀ x ∈ N, G (φ n) x ≤ A) ∧
      TendstoLocallyUniformlyOn (fun n ↦ F (φ n)) v atTop ((⋃ i, U i) \ ↑Z) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨id, ∅, F 0, strictMono_id, by simp, by simp, by simp, fun _ hy ↦ by simp at hy,
      fun _ _ _ hx ↦ by simp at hx⟩
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  -- The property of the filter of a subsequence on the window `U (e m)`; it passes to finer
  -- filters.
  let P : ℕ → Filter ℕ → Prop := fun m l ↦ ∃ Z : Set X,
    (∀ z ∈ Z, ∀ N ∈ 𝓝 z, ∀ᶠ n in l, δ ≤ μ n N) ∧
    (∀ y ∈ U (e m) \ Z, ∃ N ∈ 𝓝 y, ∃ A, ∀ᶠ n in l, ∀ x ∈ N, G n x ≤ A) ∧
    ∃ v : X → α, TendstoLocallyUniformlyOn F v l (U (e m) \ Z)
  obtain ⟨D, hD, hDP⟩ := extraction_forall_of_antitone (P := P)
    (fun _ _ _ hl hP ↦ by
      obtain ⟨Z, hconc, hbd, v, hv⟩ := hP
      exact ⟨Z, fun z hz N hN ↦ (hconc z hz N hN).filter_mono hl,
        fun y hy ↦ (hbd y hy).imp fun _ ⟨hN, A, hA⟩ ↦ ⟨hN, A, hA.filter_mono hl⟩, v,
        hv.comp_tendsto (tendsto_id'.2 hl)⟩) fun m ψ hψ ↦ by
    obtain ⟨φ, hφ, Z, hconc, hbd, v, hv⟩ := h (e m) hψ
    exact ⟨φ, hφ, Z, fun z hz N hN ↦ eventually_map.2 (hconc z hz N hN),
      fun y hy ↦ (hbd y hy).imp fun _ ⟨hN, A, hA⟩ ↦ ⟨hN, A, eventually_map.2 hA⟩, v,
      tendstoLocallyUniformlyOn_map_iff.2 hv⟩
  -- Along the diagonal, energy concentrates at the bubbling points of every window, the
  -- functions `G` are bounded near the other points of every window, and the diagonal converges
  -- on every window off its bubbling points.
  choose Zw hconcD hbdD vw hvD using hDP
  -- The bubbling set is the union of the bubbling sets of the windows, inside the windows.
  set Z : Set X := ⋃ m, Zw m ∩ U (e m)
  have hZW : Z ⊆ ⋃ i, U i :=
    iUnion_subset fun m ↦ inter_subset_right.trans (subset_iUnion U (e m))
  have hZconc (z : X) (hz : z ∈ Z) (N : Set X) (hN : N ∈ 𝓝 z) : ∀ᶠ n in atTop, δ ≤ μ (D n) N := by
    obtain ⟨m, hm⟩ := mem_iUnion.1 hz
    exact eventually_map.1 (hconcD m z hm.1 N hN)
  -- Every finite subset of `Z` has at most `E / δ` points, so `Z` is finite.
  have hcard (T : Finset X) (hT : ↑T ⊆ Z) : T.card * δ ≤ E :=
    card_mul_le_of_forall_eventually_le_measure (l := atTop) (isOpen_iUnion hU)
      (fun n ↦ hμ (D n)) (hT.trans hZW) fun z hz ↦ hZconc z (hT hz)
  have hZf : Z.Finite := Set.finite_of_forall_finset_card_mul_le hδ hE hcard
  obtain ⟨v, hv⟩ := exists_tendstoLocallyUniformlyOn_iUnion_sdiff (fun m ↦ hU (e m))
    hZf.toFinset.finite_toSet.isClosed
    (fun m x hx ↦ by rw [hZf.coe_toFinset]; exact mem_iUnion_of_mem m hx)
    fun m ↦ tendstoLocallyUniformlyOn_map_iff.1 (hvD m)
  rw [he.iUnion_comp U] at hv
  refine ⟨D, hZf.toFinset, v, hD, by simpa using hZW, hcard _ (by simp),
    fun z hz N hN ↦ hZconc z (by simpa using hz) N hN, fun y hy ↦ ?_, hv⟩
  -- A point off `Z` lies in a window off its bubbling set, where the bound holds.
  rw [hZf.coe_toFinset] at hy
  obtain ⟨i, hi⟩ := mem_iUnion.1 hy.1
  obtain ⟨m, rfl⟩ := he i
  obtain ⟨N, hN, A, hA⟩ := hbdD m y ⟨hi, fun hyZ ↦ hy.2 (mem_iUnion.2 ⟨m, hyZ, hi⟩)⟩
  exact ⟨N, hN, A, eventually_map.1 hA⟩

/-- **Convergence off finitely many bubbling points on a countable union of windows.** Let
`Uᵢ` be countably many open sets, `Fₙ : X → α` maps and `μₙ` measures on `X` with
`μₙ (⋃ᵢ Uᵢ) ≤ E < ∞`, and let `δ > 0`. Suppose that for every window `Uᵢ` and every subsequence
`ψ`, there are a further subsequence `ψ ∘ φ`, a set `Zᵢ` and a map `vᵢ` such that every
neighbourhood of a point of `Zᵢ` eventually carries `μ`-energy at least `δ` along `ψ ∘ φ`, and
`F ∘ ψ ∘ φ → vᵢ` locally uniformly on `Uᵢ \ Zᵢ`. Then there are a subsequence `φ`, a finite set
`Z ⊆ ⋃ᵢ Uᵢ` with `#Z * δ ≤ E` and a map `v` such that every neighbourhood of a point of `Z`
eventually carries energy at least `δ` along `φ`, and `F ∘ φ → v` locally uniformly on
`(⋃ᵢ Uᵢ) \ Z`. This is the case `G = 0` of
`TauCeti.exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion_of_le`. -/
theorem exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion [T2Space X]
    [OpensMeasurableSpace X] [T2Space α] {ι : Type*} [Countable ι] {U : ι → Set X}
    (hU : ∀ i, IsOpen (U i)) {F : ℕ → X → α} {μ : ℕ → Measure X} {δ E : ℝ≥0∞} (hδ : δ ≠ 0)
    (hE : E ≠ ∞) (hμ : ∀ n, μ n (⋃ i, U i) ≤ E)
    (h : ∀ i ⦃ψ : ℕ → ℕ⦄, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Set X,
      (∀ z ∈ Z, ∀ N ∈ 𝓝 z, ∀ᶠ n in atTop, δ ≤ μ (ψ (φ n)) N) ∧
      ∃ v : X → α, TendstoLocallyUniformlyOn (fun n ↦ F (ψ (φ n))) v atTop (U i \ Z)) :
    ∃ (φ : ℕ → ℕ) (Z : Finset X) (v : X → α), StrictMono φ ∧ ↑Z ⊆ ⋃ i, U i ∧
      Z.card * δ ≤ E ∧ (∀ z ∈ Z, ∀ N ∈ 𝓝 z, ∀ᶠ n in atTop, δ ≤ μ (φ n) N) ∧
      TendstoLocallyUniformlyOn (fun n ↦ F (φ n)) v atTop ((⋃ i, U i) \ ↑Z) := by
  obtain ⟨φ, Z, v, hφ, hZ, hcard, hconc, -, hv⟩ :=
    exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion_of_le (G := 0) hU hδ hE hμ
      fun i ψ hψ ↦ (h i hψ).imp fun _ ⟨hφ, Z, hconc, hv⟩ ↦
        ⟨hφ, Z, hconc, fun _ _ ↦ ⟨univ, univ_mem, 0, .of_forall fun _ _ _ ↦ le_rfl⟩, hv⟩
  exact ⟨φ, Z, v, hφ, hZ, hcard, hconc, hv⟩

end TauCeti
