/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Data.ENNReal.NatCastDiv
import TauCeti.MeasureTheory.Integral.Bochner.PeriodicStrip
import TauCeti.MeasureTheory.Integral.EnergyConcentration
import TauCeti.Order.Filter.AtTopBot
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.MetricSpace.Pseudo.Prod
import TauCeti.Topology.Order.Compact
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
(`TauCeti.exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion`).

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

On the cylinder `ℝ × ℝ / ℤ (0, 1)`, written as maps on `ℝ × ℝ` of period one in the second
variable, the energy over the whole plane is infinite, but the energy over the strip
`ℝ × [0, 1)` is finite. Take as windows the open unit discs about the integer points `(m, n)`,
which cover the plane. If on each window every subsequence has a further subsequence converging
off a finite set at whose points the energy `δ` concentrates, with some functions `gₖ` bounded on
the compact subsets of the regular part, then a single subsequence converges off the translates
`Z + (0, n)` of a finite set `Z` in the strip, with `#Z * δ ≤ 2E`, and the `gₖ` are bounded on
every compact set disjoint from these translates
(`TauCeti.exists_tendstoLocallyUniformlyOn_subseq_off_finset_of_periodic`). Here concentration is
periodic in the second variable, so the bubbling points are determined by those in the strip.
The factor `2` comes from counting the concentration points in the strip against the energy of
the two adjacent periods about them
(`TauCeti.card_mul_le_two_mul_of_forall_eventually_le_setIntegral_ball_of_periodic`).

## Main results

* `TauCeti.exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion`: convergence off finitely
  many bubbling points on a countable union of windows.
* `TauCeti.exists_bubblingSet_of_forall_window`: the bubbling set of an exhaustion by windows with
  thresholds depending on the window.
* `TauCeti.exists_tendstoLocallyUniformlyOn_subseq_off_finset_of_periodic`: convergence off
  finitely many bubbling points on the cylinder, from windows about the integer points.

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

/-- **Convergence off finitely many bubbling points on a countable union of windows.** Let
`Uᵢ` be countably many open sets, `Fₙ : X → α` maps and `μₙ` measures on `X` with
`μₙ (⋃ᵢ Uᵢ) ≤ E < ∞`, and let `δ > 0`. Suppose that for every window `Uᵢ` and every subsequence
`ψ`, there are a further subsequence `ψ ∘ φ`, a set `Zᵢ` and a map `vᵢ` such that every
neighbourhood of a point of `Zᵢ` eventually carries `μ`-energy at least `δ` along `ψ ∘ φ`, and
`F ∘ ψ ∘ φ → vᵢ` locally uniformly on `Uᵢ \ Zᵢ`. Then there are a subsequence `φ`, a finite set
`Z ⊆ ⋃ᵢ Uᵢ` with `#Z * δ ≤ E` and a map `v` such that every neighbourhood of a point of `Z`
eventually carries energy at least `δ` along `φ`, and `F ∘ φ → v` locally uniformly on
`(⋃ᵢ Uᵢ) \ Z`. -/
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
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨id, ∅, F 0, strictMono_id, by simp, by simp, by simp,
      fun _ _ _ hx ↦ by simp at hx⟩
  obtain ⟨e, he⟩ := exists_surjective_nat ι
  -- The property of the filter of a subsequence on the window `U (e m)`; it passes to finer
  -- filters.
  let P : ℕ → Filter ℕ → Prop := fun m l ↦ ∃ Z : Set X,
    (∀ z ∈ Z, ∀ N ∈ 𝓝 z, ∀ᶠ n in l, δ ≤ μ n N) ∧
    ∃ v : X → α, TendstoLocallyUniformlyOn F v l (U (e m) \ Z)
  obtain ⟨D, hD, hDP⟩ := extraction_forall_of_antitone (P := P)
    (fun _ _ _ hl hP ↦ by
      obtain ⟨Z, hconc, v, hv⟩ := hP
      exact ⟨Z, fun z hz N hN ↦ (hconc z hz N hN).filter_mono hl, v,
        hv.comp_tendsto (tendsto_id'.2 hl)⟩) fun m ψ hψ ↦ by
    obtain ⟨φ, hφ, Z, hconc, v, hv⟩ := h (e m) hψ
    exact ⟨φ, hφ, Z, fun z hz N hN ↦ eventually_map.2 (hconc z hz N hN), v,
      tendstoLocallyUniformlyOn_map_iff.2 hv⟩
  -- Along the diagonal, energy concentrates at the bubbling points of every window, and the
  -- diagonal converges on every window off its bubbling points.
  choose Zw hconcD vw hvD using hDP
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
  exact ⟨D, hZf.toFinset, v, hD, by simpa using hZW, hcard _ (by simp),
    fun z hz N hN ↦ hZconc z (by simpa using hz) N hN, hv⟩

section Periodic

open Metric

/-- The diagonal step of `exists_tendstoLocallyUniformlyOn_subseq_off_finset_of_periodic`: if on
the unit disc about every integer point `c = (m, n)` every subsequence has a further subsequence
with the conclusions of a window, then one subsequence `φ` has these conclusions eventually along
`φ` on every such disc. -/
private theorem exists_subseq_forall_ball_add_int {F : ℕ → ℝ × ℝ → α} {f g : ℕ → ℝ × ℝ → ℝ}
    {δ : ℝ}
    (hwin : ∀ (m : ℤ × ℤ) ⦃ψ : ℕ → ℕ⦄, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → α),
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball (z + ((m.1 : ℝ), (m.2 : ℝ))) ε, f (ψ (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ (· - ((m.1 : ℝ), (m.2 : ℝ))) ⁻¹' (ball 0 1 \ ↑Z) →
          ∃ M, ∀ n, ∀ y ∈ C, g (ψ (φ n)) y ≤ M) ∧
        TendstoLocallyUniformlyOn (fun n ↦ F (ψ (φ n))) v atTop
          ((· - ((m.1 : ℝ), (m.2 : ℝ))) ⁻¹' (ball 0 1 \ ↑Z))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ m : ℤ × ℤ, ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → α),
      (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ k in map φ atTop,
        δ ≤ ∫ y in ball (z + ((m.1 : ℝ), (m.2 : ℝ))) ε, f k y) ∧
      (∀ C, IsCompact C → C ⊆ (· - ((m.1 : ℝ), (m.2 : ℝ))) ⁻¹' (ball 0 1 \ ↑Z) →
        ∃ M, ∀ᶠ k in map φ atTop, ∀ y ∈ C, g k y ≤ M) ∧
      TendstoLocallyUniformlyOn F v (map φ atTop)
        ((· - ((m.1 : ℝ), (m.2 : ℝ))) ⁻¹' (ball 0 1 \ ↑Z)) := by
  -- These properties pass to finer filters. Enumerate the windows.
  set e : ℕ ≃ ℤ × ℤ := (Denumerable.eqv (ℤ × ℤ)).symm
  let P : ℕ → Filter ℕ → Prop := fun j l ↦ ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → α),
      (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ k in l,
        δ ≤ ∫ y in ball (z + (((e j).1 : ℝ), ((e j).2 : ℝ))) ε, f k y) ∧
      (∀ C, IsCompact C → C ⊆ (· - (((e j).1 : ℝ), ((e j).2 : ℝ))) ⁻¹' (ball 0 1 \ ↑Z) →
        ∃ M, ∀ᶠ k in l, ∀ y ∈ C, g k y ≤ M) ∧
      TendstoLocallyUniformlyOn F v l ((· - (((e j).1 : ℝ), ((e j).2 : ℝ))) ⁻¹' (ball 0 1 \ ↑Z))
  obtain ⟨φ, hφ, hP⟩ := extraction_forall_of_antitone (P := P)
    (fun j _ _ hl ⟨Z, v, hconc, hbd, hlim⟩ ↦ ⟨Z, v,
      fun z hz ε hε ↦ (hconc z hz ε hε).filter_mono hl,
      fun C hC hCZ ↦ (hbd C hC hCZ).imp fun _ hM ↦ hM.filter_mono hl,
      hlim.comp_tendsto (tendsto_id'.2 hl)⟩) fun j ψ hψ ↦ by
      obtain ⟨φ, hφ, Z, v, hconc, hbd, hlim⟩ := hwin (e j) hψ
      exact ⟨φ, hφ, Z, v, fun z hz ε hε ↦ eventually_map.2 (hconc z hz ε hε),
        fun C hC hCZ ↦ (hbd C hC hCZ).imp fun _ hM ↦ eventually_map.2 (Eventually.of_forall hM),
        tendstoLocallyUniformlyOn_map_iff.2 hlim⟩
  refine ⟨φ, hφ, fun m ↦ ?_⟩
  simpa only [P, Equiv.apply_symm_apply] using hP (e.symm m)

/-- **Convergence off finitely many bubbling points on the cylinder.** Let `Fₖ : ℝ × ℝ → α` and
nonnegative densities `fₖ` be of period one in the second variable, with `fₖ` integrable over the
strip `ℝ × [0, 1)` and `∫_{ℝ × [0, 1)} fₖ ≤ E`, and let `gₖ` be continuous. Let `δ > 0`, and
suppose that for the unit disc about every integer point `c = (m, n)` and every subsequence `ψ`
there are a further subsequence `ψ ∘ φ`, a finite set `Zc` in the unit disc and a map `vc` such
that, along `ψ ∘ φ`, every disc about a point of `Zc + c` eventually carries `∫ f ≥ δ`, the
`gₖ` are bounded on every compact subset of the disc off `Zc + c`, and `Fₖ → vc` locally
uniformly on the disc off `Zc + c`.

Then there are a subsequence `φ`, a finite set `Z` in the strip with `#Z * δ ≤ 2E`, and a map `v`
of period one in the second variable such that, along `φ`, every disc about a point of `Z`
eventually carries `∫ f ≥ δ`, the `gₖ` are bounded on every compact set disjoint from the
translates `Z + (0, n)`, and `Fₖ → v` locally uniformly off these translates. -/
theorem exists_tendstoLocallyUniformlyOn_subseq_off_finset_of_periodic [T2Space α] [Nonempty α]
    {F : ℕ → ℝ × ℝ → α} {f g : ℕ → ℝ × ℝ → ℝ} {δ E : ℝ} (hδ : 0 < δ)
    (hf0 : ∀ k y, 0 ≤ f k y) (hf : ∀ k s t, f k (s, t + 1) = f k (s, t))
    (hint : ∀ k, IntegrableOn (f k) (univ ×ˢ Ico 0 1))
    (hE : ∀ k, ∫ y in univ ×ˢ Ico 0 1, f k y ≤ E) (hF : ∀ k s t, F k (s, t + 1) = F k (s, t))
    (hg : ∀ k, Continuous (g k))
    (hwin : ∀ (m : ℤ × ℤ) ⦃ψ : ℕ → ℕ⦄, StrictMono ψ → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → α),
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball (z + ((m.1 : ℝ), (m.2 : ℝ))) ε, f (ψ (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ (· - ((m.1 : ℝ), (m.2 : ℝ))) ⁻¹' (ball 0 1 \ ↑Z) →
          ∃ M, ∀ n, ∀ y ∈ C, g (ψ (φ n)) y ≤ M) ∧
        TendstoLocallyUniformlyOn (fun n ↦ F (ψ (φ n))) v atTop
          ((· - ((m.1 : ℝ), (m.2 : ℝ))) ⁻¹' (ball 0 1 \ ↑Z))) :
    ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → α), StrictMono φ ∧
      (Z : Set (ℝ × ℝ)) ⊆ univ ×ˢ Ico 0 1 ∧ Z.card * δ ≤ 2 * E ∧
      (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε, f (φ n) y) ∧
      (∀ C, IsCompact C → C ⊆ {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} →
        ∃ M, ∀ n, ∀ y ∈ C, g (φ n) y ≤ M) ∧
      (∀ s t, v (s, t + 1) = v (s, t)) ∧
      TendstoLocallyUniformlyOn (fun n ↦ F (φ n)) v atTop
        {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ Z} := by
  obtain ⟨φ, hφ, hP⟩ := exists_subseq_forall_ball_add_int hwin
  choose Z v hconc hbd hlim using hP
  set l : Filter ℕ := map φ atTop
  set c : ℤ × ℤ → ℝ × ℝ := fun m ↦ ((m.1 : ℝ), (m.2 : ℝ))
  have hk (k : ℕ) : IntegrableOn (f k) (univ ×ˢ Ico 0 (0 + 1)) := by simpa using hint k
  have hEk (k : ℕ) : ∫ z in univ ×ˢ Ico 0 (0 + 1), f k z ≤ E := by simpa using hE k
  have hS : (univ ×ˢ Ico 0 1 : Set (ℝ × ℝ)) ⊆ univ ×ˢ Ico 0 (0 + 1) := by rw [zero_add]
  -- The bubbling points of all windows, and the good parts of the windows, in the plane.
  set Zall : Set (ℝ × ℝ) := ⋃ m, (· + c m) '' (Z m : Set (ℝ × ℝ))
  set G : ℤ × ℤ → Set (ℝ × ℝ) := fun m ↦ (· - c m) ⁻¹' (ball 0 1 \ ↑(Z m))
  -- The points at which energy at least `δ` concentrates; finitely many lie in the strip.
  set Zc : Set (ℝ × ℝ) := {y | ∀ ε > 0, ∀ᶠ k in l, δ ≤ ∫ y' in ball y ε, f k y'}
  have hfin : (Zc ∩ univ ×ˢ Ico 0 1).Finite :=
    finite_of_forall_eventually_le_setIntegral_ball_of_periodic (μ := volume) (l := l) hδ hf0
      hf hk hEk (inter_subset_right.trans hS) fun z hz ↦ hz.1
  -- Each bubbling point is a translate of one of them, since concentration is periodic in `t`.
  have hgood : {y : ℝ × ℝ | (y.1, Int.fract y.2) ∉ hfin.toFinset} ⊆ Zallᶜ := by
    intro y hy hyZ
    obtain ⟨m, z, hz, rfl⟩ := mem_iUnion.1 hyZ
    have h := forall_eventually_le_setIntegral_ball_toIcoMod_of_periodic (μ := volume) (a := 0)
      zero_lt_one hf (hconc m z hz)
    rw [toIcoMod_zero_one] at h
    exact hy (hfin.mem_toFinset.2 ⟨h, mem_univ _, Int.fract_nonneg _, Int.fract_lt_one _⟩)
  -- The good parts of the windows are open and cover the complement of `Zall`: the integer point
  -- nearest to `y` is at distance at most `1 / 2`.
  have hGopen (m : ℤ × ℤ) : IsOpen (G m) :=
    (isOpen_ball.sdiff (Z m).finite_toSet.isClosed).preimage (continuous_sub_right _)
  have hcover (y : ℝ × ℝ) (hy : y ∉ Zall) : ∃ m, y ∈ G m := by
    have hm : y - c (round y.1, round y.2) ∈ ball 0 1 := by
      rw [mem_ball_zero_iff, ← dist_eq_norm]
      exact (Prod.dist_round_le y).trans_lt (by norm_num)
    exact ⟨_, hm, fun hZ ↦ hy (mem_iUnion.2 ⟨_, _, hZ, sub_add_cancel _ _⟩)⟩
  refine ⟨φ, hfin.toFinset, fun y ↦ limUnder l fun k ↦ F k y, hφ,
    fun z hz ↦ (hfin.mem_toFinset.1 hz).2, ?_,
    fun z hz ε hε ↦ eventually_map.1 ((hfin.mem_toFinset.1 hz).1 ε hε), fun C hC hCZ ↦ ?_,
    fun s t ↦ by simp only [hF], ?_⟩
  · exact card_mul_le_two_mul_of_forall_eventually_le_setIntegral_ball_of_periodic
      (μ := volume) (l := l) hf0 hf hk hEk (fun z hz ↦ hS (hfin.mem_toFinset.1 hz).2)
      fun z hz ↦ (hfin.mem_toFinset.1 hz).1
  · -- Each point of `C` has a closed disc in the good part of some window, on which the
    -- functions `g` are eventually bounded.
    refine hC.exists_forall_le_of_eventually_nhds (fun n ↦ (hg (φ n)).continuousOn)
      fun x hx ↦ ?_
    obtain ⟨m, hm⟩ := hcover x (hgood (hCZ hx))
    obtain ⟨r, hr, hsub⟩ := nhds_basis_closedBall.mem_iff.1 ((hGopen m).mem_nhds hm)
    obtain ⟨M, hM⟩ := hbd m _ (isCompact_closedBall _ _) hsub
    exact ⟨closedBall x r, closedBall_mem_nhds x hr, M, eventually_map.1 hM⟩
  · -- The limits of the windows glue to the pointwise limit, off the translates of `Z`.
    exact ((tendstoLocallyUniformlyOn_iUnion_limUnder hGopen hlim).mono fun y hy ↦
      mem_iUnion.2 (hcover y (hgood hy))).comp_tendsto tendsto_map

end Periodic

end TauCeti
