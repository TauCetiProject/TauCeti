/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import TauCeti.Data.ENNReal.NatCastDiv
import TauCeti.MeasureTheory.Integral.EnergyConcentration
import TauCeti.Order.Filter.AtTopBot
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

## Main results

* `TauCeti.exists_tendstoLocallyUniformlyOn_subseq_off_finset_iUnion`: convergence off finitely
  many bubbling points on a countable union of windows.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6,
  on bubbling off finitely many points and the exhaustion of a noncompact domain by compact sets.
-/

public section

open Filter Set Topology MeasureTheory
open scoped ENNReal

namespace TauCeti

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

end TauCeti
