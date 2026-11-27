/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.Number.Segment.Jump
public import TauCeti.Analysis.Normed.Module.FilledHull
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Calculus.ContDiff.Approximation
import TauCeti.Analysis.Calculus.ContDiff.PiecewiseC1On.AbsolutelyContinuous
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.LocallyConstant
import TauCeti.Order.Interval.Set.Piecewise
import TauCeti.Topology.ConnectedComponents

/-!
# A segment crossing a set once has its ends on different sides

A closed set `K ⊆ ℂ` with `K \ {p}` preconnected, crossed once by a straight segment at `p` with
`K` adherent from both sides, separates the two ends into different connected components of `Kᶜ`.
The proof uses winding numbers and needs no Jordan curve theorem.

## Main results

* `TauCeti.Contour.notMem_connectedComponentIn_compl_of_isPreconnected_sdiff_singleton` — **the
  two ends of the segment lie in different components of `Kᶜ`.**
* `TauCeti.Contour.mem_filledHull_or_mem_filledHull_of_isPreconnected_sdiff_singleton` — **for
  bounded `K`, one end lies in the filled hull.**

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4, §2.1.
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Section 2.2.
-/

public section

open Bornology Complex Filter Metric Set

open scoped Topology

namespace TauCeti.Contour

variable {K : Set ℂ} {v z₀ : ℂ} {a b s : ℝ}

/-- A segment `t ↦ v t + z₀` on `[a, b]` whose ends lie in one connected component of the
complement of a closed set `K` closes up, through that component, to a piecewise-`C¹` closed curve
on `[a, b + 1]` that follows the segment on `[a, b]` and avoids `K` on `[b, b + 1]`. -/
private theorem exists_isPiecewiseC1On_eqOn_segment_mapsTo_compl (hK : IsClosed K) (hab : a ≤ b)
    (hmem : v * b + z₀ ∈ connectedComponentIn Kᶜ (v * a + z₀)) :
    ∃ Γ : ℝ → ℂ, IsPiecewiseC1On Γ a (b + 1) ∧ Γ a = Γ (b + 1) ∧
      EqOn Γ (fun t : ℝ ↦ v * t + z₀) (Icc a b) ∧ MapsTo Γ (Icc b (b + 1)) Kᶜ := by
  obtain ⟨g, hg, hg0, hg1, hgK⟩ :=
    ((hK.isOpen_compl.joinedIn_of_mem_connectedComponentIn hmem).symm.mono
      (connectedComponentIn_subset _ _)).exists_contDiff_mapsTo hK.isOpen_compl
  let Γ : ℝ → ℂ := fun t ↦ if t ≤ b then v * t + z₀ else g (t - b)
  have hΓg : EqOn Γ (fun t ↦ g (t - b)) (Ici b) := eqOn_ite_le_Ici (by simp [hg0])
  refine ⟨Γ, (IsPiecewiseC1On.of_contDiffOn
    ((contDiff_const.mul Complex.ofRealCLM.contDiff).add contDiff_const).contDiffOn).if_le
    (.of_contDiffOn ((hg.of_le le_top).comp (contDiff_id.sub contDiff_const)).contDiffOn) hab
    (by linarith) (by simp [hg0]), ?_, fun t ht ↦ ite_eq_left ht.2, fun t ht ↦ ?_⟩
  · simp only [hΓg (show b ≤ b + 1 by linarith), add_sub_cancel_left, hg1]
    exact ite_eq_left hab
  · rw [hΓg ht.1]
    exact hgK ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-- **A segment crossing a set once has its ends in different components of the complement.**
Let `K` be closed with `K \ {p}` preconnected, crossed by a straight segment at an interior point
`p = v · s + z₀` with `K` adherent from both sides of the segment. Then the two endpoints
`v · a + z₀` and `v · b + z₀` lie in different connected components of `Kᶜ`. -/
theorem notMem_connectedComponentIn_compl_of_isPreconnected_sdiff_singleton (hK : IsClosed K)
    (hs : s ∈ Ioo a b)
    (hseg : ∀ t ∈ Icc a b, v * t + z₀ ∈ K → t = s)
    (hKp : IsPreconnected (K \ {v * s + z₀}))
    (hleft : v * s + z₀ ∈ closure (K ∩ {q | 0 < ((q - (v * s + z₀)) / v).im}))
    (hright : v * s + z₀ ∈ closure (K ∩ {q | ((q - (v * s + z₀)) / v).im < 0})) :
    v * b + z₀ ∉ connectedComponentIn Kᶜ (v * a + z₀) := by
  intro hmem
  have hv : v ≠ 0 := by rintro rfl; simp at hleft
  set p : ℂ := v * s + z₀
  have hp : p ∈ K := hK.closure_subset (closure_mono inter_subset_left hleft)
  have hab : a < b := hs.1.trans hs.2
  -- Stage 1: the closed curve Γ = segment ∪ smooth return through `Kᶜ`
  obtain ⟨Γ, hΓpw, hΓclosed, hΓseg, hΓK⟩ :=
    exists_isPiecewiseC1On_eqOn_segment_mapsTo_compl hK hab.le hmem
  -- Stage 2: the return avoids p, so the jump formula applies
  have hpg : p ∉ Γ '' Icc b (b + 1) := fun ⟨_, ht, hpt⟩ ↦ hΓK ht (hpt ▸ hp)
  obtain ⟨r, hr, hjump⟩ := exists_forall_windingNumber_eq_add_one_of_eqOn_segment hΓpw hΓclosed
    (by linarith : b ≤ b + 1) hΓseg hv hs hpg
  -- Stage 3: winding number is constant on K \ {p} yet jumps — contradiction
  obtain ⟨q₁, ⟨hq₁K, hq₁im⟩, hq₁r⟩ := Metric.mem_closure_iff.mp hleft r hr
  obtain ⟨q₂, ⟨hq₂K, hq₂im⟩, hq₂r⟩ := Metric.mem_closure_iff.mp hright r hr
  simp only [mem_ofPred_eq] at hq₁im hq₂im
  have hq₁p : q₁ ≠ p := by rintro rfl; simp at hq₁im
  have hq₂p : q₂ ≠ p := by rintro rfl; simp at hq₂im
  have hKΓ : K \ {p} ⊆ (Γ '' uIcc a (b + 1))ᶜ := by
    rintro q ⟨hqK, hqp⟩ ⟨t, ht, hqt⟩
    rw [uIcc_of_le (by linarith : a ≤ b + 1)] at ht
    rcases le_or_gt t b with htb | htb
    · have hΓt : Γ t = v * t + z₀ := hΓseg ⟨ht.1, htb⟩
      have hts : t = s := hseg t ⟨ht.1, htb⟩ (by rw [← hΓt, hqt]; exact hqK)
      apply hqp
      rw [mem_singleton_iff, ← hqt, hΓt, hts]
    · exact hΓK ⟨htb.le, ht.2⟩ (hqt ▸ hqK)
  have hW : windingNumber Γ a (b + 1) q₁ = windingNumber Γ a (b + 1) q₂ :=
    hΓpw.absolutelyContinuousOnInterval.windingNumber_eq_of_mem_connectedComponentIn hΓclosed
      (hKp.subset_connectedComponentIn ⟨hq₂K, hq₂p⟩ hKΓ ⟨hq₁K, hq₁p⟩)
  have hJ := hjump q₁ (by rw [mem_ball, dist_comm]; exact hq₁r) q₂
    (by rw [mem_ball, dist_comm]; exact hq₂r) hq₁im hq₂im
  rw [hW] at hJ
  simp at hJ

/-- **One end of a segment crossing a bounded set once lies in its filled hull.**
Under the same hypotheses as
`notMem_connectedComponentIn_compl_of_isPreconnected_sdiff_singleton`, plus boundedness of `K`,
at least one of `v · a + z₀` and `v · b + z₀` lies in `filledHull K`. -/
theorem mem_filledHull_or_mem_filledHull_of_isPreconnected_sdiff_singleton (hK : IsClosed K)
    (hKb : IsBounded K) (hs : s ∈ Ioo a b)
    (hseg : ∀ t ∈ Icc a b, v * t + z₀ ∈ K → t = s)
    (hKp : IsPreconnected (K \ {v * s + z₀}))
    (hleft : v * s + z₀ ∈ closure (K ∩ {q | 0 < ((q - (v * s + z₀)) / v).im}))
    (hright : v * s + z₀ ∈ closure (K ∩ {q | ((q - (v * s + z₀)) / v).im < 0})) :
    v * a + z₀ ∈ filledHull K ∨ v * b + z₀ ∈ filledHull K := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    exact Cardinal.one_lt_two
  exact mem_filledHull_or_mem_filledHull_of_notMem_connectedComponentIn hrank hKb
    (notMem_connectedComponentIn_compl_of_isPreconnected_sdiff_singleton hK hs hseg
      hKp hleft hright)

end TauCeti.Contour
