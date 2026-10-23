/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Basic
import TauCeti.Topology.Continuum
import TauCeti.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Impressions of prime ends

The impression of a null chain is the intersection of the closures of the domains it cuts off.
Equivalent chains have the same impression, so this defines `PrimeEnd.impression` without
choosing a representative. For a bounded domain the impression is a nonempty compact connected
subset of the frontier. These sets relate the boundary seen from inside a domain to its ordinary
topological boundary; a single prime end may have more than one point in its impression.

The frontier assertion uses the fact that the crosscuts of a bounded null chain eventually
avoid every compact subset of the domain. A compact connected set inside the domain then
joins any proposed interior impression point to the first crosscut, contradicting nesting.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Section 2.4.
* C. Carathéodory, *Über die Begrenzung einfach zusammenhängender Gebiete*, Math. Ann. 73
  (1913).
-/

public section

noncomputable section

open Bornology Complex Filter Metric Set Topology

namespace TauCeti

variable {U : Set ℂ} {C C' : ℕ → Set ℂ}

/-- The impression of a sequence of crosscuts: the common limit set of its cut-off domains. -/
def nullChainImpression (U : Set ℂ) (C : ℕ → Set ℂ) : Set ℂ :=
  ⋂ n, closure (nullChainDomain U C n)

/-- The impression is the intersection of the closed cut-off domains. -/
theorem nullChainImpression_def :
    nullChainImpression U C = ⋂ n, closure (nullChainDomain U C n) := (rfl)

/-- Membership in the impression means membership in every closed cut-off domain. -/
theorem mem_nullChainImpression_iff {z : ℂ} :
    z ∈ nullChainImpression U C ↔ ∀ n, z ∈ closure (nullChainDomain U C n) := by
  simp [nullChainImpression]

/-- Equivalent chains have the same impression. No boundedness is needed for this invariance. -/
theorem NullChainEquivalent.nullChainImpression_eq (h : NullChainEquivalent U C C') :
    nullChainImpression U C = nullChainImpression U C' := by
  have hmono {A B : ℕ → Set ℂ}
      (hAB : ∀ m, ∃ n, nullChainDomain U B n ⊆ nullChainDomain U A m) :
      nullChainImpression U B ⊆ nullChainImpression U A := by
    intro z hz
    rw [mem_nullChainImpression_iff] at hz ⊢
    intro m
    obtain ⟨n, hn⟩ := hAB m
    exact closure_mono hn (hz n)
  obtain ⟨h₁, h₂⟩ := nullChainEquivalent_def.mp h
  exact Subset.antisymm (hmono h₂) (hmono h₁)

namespace IsNullChain

/-- Each domain cut off by a null chain is connected. -/
theorem isConnected_nullChainDomain (hC : IsNullChain U C) (n : ℕ) :
    IsConnected (nullChainDomain U C n) := by
  obtain ⟨z, hz⟩ := (hC.isConnected_inter (n + 1)).nonempty
  rw [hC.nullChainDomain_eq_connectedComponentIn hz]
  exact isConnected_connectedComponentIn_iff.mpr
    ⟨hz.2, disjoint_right.mp (hC.disjoint_succ n) hz.1⟩

/-- On a bounded domain, chordally shrinking crosscuts also shrink in Euclidean diameter. -/
theorem eventually_norm_sub_lt (hC : IsNullChain U C) (hU : IsBounded U) {ε : ℝ}
    (hε : 0 < ε) : ∀ᶠ n in atTop, ∀ z ∈ C n, ∀ w ∈ C n, ‖z - w‖ < ε := by
  obtain ⟨R, hR, hbound⟩ := hU.closure.exists_pos_norm_le
  filter_upwards [hC.eventually_chordal_lt (ε / (1 + R ^ 2)) (by positivity)]
    with n hn z hz w hw
  obtain ⟨x, y, γ, hγ, hrange⟩ := hC.exists_isCrosscut n
  have hsub : C n ⊆ closure U := hrange ▸ hγ.range_subset_closure
  have hzR := hbound z (hsub hz)
  have hwR := hbound w (hsub hw)
  have hz2 : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzR 2
  have hw2 : ‖w‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hwR 2
  have hs : √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) ≤ 1 + R ^ 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg ‖z‖, sq_nonneg ‖w‖]
  have hpos : 0 < √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) :=
    Real.sqrt_pos.mpr (by positivity)
  have h := (div_lt_iff₀ hpos).mp (hn z hz w hw)
  calc
    ‖z - w‖ < ε / (1 + R ^ 2) * √((1 + ‖z‖ ^ 2) * (1 + ‖w‖ ^ 2)) := h
    _ ≤ ε / (1 + R ^ 2) * (1 + R ^ 2) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = ε := div_mul_cancel₀ _ (by positivity)

/-- Crosscuts of a bounded null chain eventually avoid each compact subset of the open domain. -/
theorem eventually_disjoint_isCompact (hC : IsNullChain U C) (hU : IsOpen U)
    (hUb : IsBounded U) {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∀ᶠ n in atTop, Disjoint (C n) K := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hKU
  filter_upwards [hC.eventually_norm_sub_lt hUb hδ] with n hn
  refine disjoint_left.mpr fun z hzC hzK => ?_
  obtain ⟨x, y, γ, hγ, hrange⟩ := hC.exists_isCrosscut n
  have hxC : x ∈ C n := hrange ▸ ⟨0, γ.source⟩
  have hxU : x ∈ U := hδU (mem_thickening_iff.mpr ⟨z, hzK, by
    simpa only [dist_eq_norm] using hn x hxC z hzC⟩)
  exact (hU.frontier_eq.subset hγ.source_mem_frontier).2 hxU

/-- The impression of a bounded null chain is nonempty and connected. -/
theorem isConnected_nullChainImpression (hC : IsNullChain U C) (hU : IsBounded U) :
    IsConnected (nullChainImpression U C) := by
  rw [nullChainImpression_def]
  exact isConnected_iInter_of_directed
    (fun i j => ⟨max i j, closure_mono (hC.antitone_nullChainDomain (le_max_left _ _)),
      closure_mono (hC.antitone_nullChainDomain (le_max_right _ _))⟩)
    (fun n => (hC.nonempty_nullChainDomain n).closure)
    (fun _ => (hU.subset (nullChainDomain_subset.trans sdiff_subset)).isCompact_closure)
    (fun n => (hC.isConnected_nullChainDomain n).isPreconnected.closure)

/-- The impression of a bounded null chain in a connected open domain lies in its frontier. -/
theorem nullChainImpression_subset_frontier (hC : IsNullChain U C) (hU : IsOpen U)
    (hUc : IsPreconnected U) (hUb : IsBounded U) :
    nullChainImpression U C ⊆ frontier U := by
  intro x hx
  have hxD := mem_nullChainImpression_iff.mp hx
  rw [hU.frontier_eq]
  refine ⟨closure_mono (nullChainDomain_subset.trans sdiff_subset) (hxD 0), ?_⟩
  intro hxU
  obtain ⟨p, hpC, hpU⟩ := (hC.isConnected_inter 0).nonempty
  obtain ⟨L, hL, hLc, hpair, hLU⟩ :=
    exists_isCompact_isPreconnected_between ((isCompact_singleton (x := x)).insert p)
      hU hUc (by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨hpU, hxU⟩)
  have hxL : x ∈ interior L := hpair (by simp)
  have hpL : p ∈ L := interior_subset (hpair (by simp))
  obtain ⟨n, hn⟩ := (hC.eventually_disjoint_isCompact hU hUb hL hLU).exists
  obtain ⟨z, hzL, hzD⟩ := _root_.mem_closure_iff.mp (hxD n) _ isOpen_interior hxL
  have hLD : L ⊆ nullChainDomain U C n :=
    hLc.subset_nullChainDomain (fun w hw => ⟨hLU hw, disjoint_right.mp hn hw⟩)
      ⟨z, interior_subset hzL, hzD⟩
  exact (nullChainDomain_subset
    (hC.antitone_nullChainDomain (Nat.zero_le n) (hLD hpL))).2 hpC

end IsNullChain

namespace PrimeEnd

/-- The impression of a prime end, independent of its representing null chain. -/
def impression : PrimeEnd U → Set ℂ :=
  lift (fun C _ => nullChainImpression U C)
    (fun _ _ _ _ h => h.nullChainImpression_eq)

/-- The impression of a represented prime end is the impression of its chain. -/
@[simp]
theorem impression_mk (hC : IsNullChain U C) :
    (mk C hC).impression = nullChainImpression U C := by
  simp [impression]

/-- Every impression is contained in the closure of the domain. -/
theorem impression_subset_closure (p : PrimeEnd U) : p.impression ⊆ closure U := by
  induction p using PrimeEnd.ind with
  | h C hC =>
    rw [impression_mk]
    exact fun z hz => closure_mono (nullChainDomain_subset.trans sdiff_subset)
      (mem_nullChainImpression_iff.mp hz 0)

/-- Every impression is closed. -/
theorem isClosed_impression (p : PrimeEnd U) : IsClosed p.impression := by
  induction p using PrimeEnd.ind with
  | h C hC =>
    rw [impression_mk, nullChainImpression_def]
    exact isClosed_iInter fun _ => isClosed_closure

/-- Impressions in a bounded domain are compact. -/
theorem isCompact_impression (p : PrimeEnd U) (hU : IsBounded U) : IsCompact p.impression :=
  hU.isCompact_closure.of_isClosed_subset p.isClosed_impression p.impression_subset_closure

/-- Impressions in a bounded domain are nonempty and connected. -/
theorem isConnected_impression (p : PrimeEnd U) (hU : IsBounded U) :
    IsConnected p.impression := by
  induction p using PrimeEnd.ind with
  | h C hC =>
    rw [impression_mk]
    exact hC.isConnected_nullChainImpression hU

/-- The impression of a prime end of a bounded connected open domain is a boundary set. -/
theorem impression_subset_frontier (p : PrimeEnd U) (hU : IsOpen U)
    (hUc : IsPreconnected U) (hUb : IsBounded U) : p.impression ⊆ frontier U := by
  induction p using PrimeEnd.ind with
  | h C hC =>
    rw [impression_mk]
    exact hC.nullChainImpression_subset_frontier hU hUc hUb

end PrimeEnd

end TauCeti

end
