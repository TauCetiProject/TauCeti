/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Basic
import TauCeti.Topology.Continuum
import TauCeti.Topology.Connected.LocallyPathConnected

/-!
# Impressions of prime ends

The impression of a null chain is the intersection of the closures of the domains it cuts off.
Equivalent chains have the same impression, so this defines `PrimeEnd.impression` without
choosing a representative. In a connected open domain the impression is a subset of the
frontier, and for a bounded domain it is moreover nonempty, compact and connected. These sets
relate the boundary seen from inside a domain to its ordinary topological boundary; a single
prime end may have more than one point in its impression.

The frontier assertion uses the fact that the crosscuts of a null chain eventually avoid every
compact subset of the domain, which needs no boundedness. A compact connected set inside the
domain then joins any proposed interior impression point to the first crosscut, contradicting
nesting.

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
@[simp]
theorem mem_nullChainImpression_iff {z : ℂ} :
    z ∈ nullChainImpression U C ↔ ∀ n, z ∈ closure (nullChainDomain U C n) := by
  simp [nullChainImpression]

/-- Every chain impression is closed. -/
theorem isClosed_nullChainImpression : IsClosed (nullChainImpression U C) := by
  rw [nullChainImpression_def]
  exact isClosed_iInter fun _ => isClosed_closure

/-- Every chain impression is contained in the closure of the domain. -/
theorem nullChainImpression_subset_closure : nullChainImpression U C ⊆ closure U :=
  fun _ hz => closure_mono nullChainDomain_subset_self (mem_nullChainImpression_iff.mp hz 0)

/-- Chain impressions in a bounded domain are compact. -/
theorem isCompact_nullChainImpression (hU : IsBounded U) :
    IsCompact (nullChainImpression U C) :=
  hU.isCompact_closure.of_isClosed_subset isClosed_nullChainImpression
    nullChainImpression_subset_closure

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

/-- The impression of a bounded null chain is nonempty and connected. -/
theorem isConnected_nullChainImpression (hC : IsNullChain U C) (hU : IsBounded U) :
    IsConnected (nullChainImpression U C) := by
  rw [nullChainImpression_def]
  exact isConnected_iInter_of_directed
    (fun i j => ⟨max i j, closure_mono (hC.antitone_nullChainDomain (le_max_left _ _)),
      closure_mono (hC.antitone_nullChainDomain (le_max_right _ _))⟩)
    (fun n => (hC.nonempty_nullChainDomain n).closure)
    (fun _ => (hU.subset nullChainDomain_subset_self).isCompact_closure)
    (fun n => (hC.isConnected_nullChainDomain n).isPreconnected.closure)

/-- The impression of a null chain in a connected open domain lies in its frontier. -/
theorem nullChainImpression_subset_frontier (hC : IsNullChain U C) (hU : IsOpen U)
    (hUc : IsPreconnected U) :
    nullChainImpression U C ⊆ frontier U := by
  intro x hx
  have hxD := mem_nullChainImpression_iff.mp hx
  rw [hU.frontier_eq]
  refine ⟨nullChainImpression_subset_closure hx, ?_⟩
  intro hxU
  obtain ⟨p, hpC, hpU⟩ := (hC.isConnected_inter 0).nonempty
  obtain ⟨L, hL, hLc, hpair, hLU⟩ :=
    exists_isCompact_isPreconnected_between ((isCompact_singleton (x := x)).insert p)
      hU hUc (by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨hpU, hxU⟩)
  have hxL : x ∈ interior L := hpair (by simp)
  have hpL : p ∈ L := interior_subset (hpair (by simp))
  obtain ⟨n, hn⟩ := (hC.eventually_disjoint_of_isCompact hU hL hLU).exists
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
    exact nullChainImpression_subset_closure

/-- Every impression is closed. -/
theorem isClosed_impression (p : PrimeEnd U) : IsClosed p.impression := by
  induction p using PrimeEnd.ind with
  | h C hC =>
    rw [impression_mk]
    exact isClosed_nullChainImpression

/-- Impressions in a bounded domain are compact. -/
theorem isCompact_impression (p : PrimeEnd U) (hU : IsBounded U) : IsCompact p.impression := by
  induction p using PrimeEnd.ind with
  | h C hC =>
    rw [impression_mk]
    exact isCompact_nullChainImpression hU

/-- Impressions in a bounded domain are nonempty and connected. -/
theorem isConnected_impression (p : PrimeEnd U) (hU : IsBounded U) :
    IsConnected p.impression := by
  induction p using PrimeEnd.ind with
  | h C hC =>
    rw [impression_mk]
    exact hC.isConnected_nullChainImpression hU

/-- The impression of a prime end of a connected open domain is a boundary set. -/
theorem impression_subset_frontier (p : PrimeEnd U) (hU : IsOpen U) (hUc : IsPreconnected U) :
    p.impression ⊆ frontier U := by
  induction p using PrimeEnd.ind with
  | h C hC =>
    rw [impression_mk]
    exact hC.nullChainImpression_subset_frontier hU hUc

end PrimeEnd

end TauCeti

end
