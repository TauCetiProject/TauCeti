/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Graded.Basic

/-!
# Continuity of the graded commutator

The commutator on a topological group descends to a jointly continuous bracket on the graded
pieces of its lower `p`-series. In the closed lower central series (`p = 0`), this permits
closed-subgroup arguments with brackets even when the graded pieces are not discrete.
-/

public section

open scoped commutatorElement

namespace TauCeti

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The quotient map from a lower-series term to its graded piece is continuous. -/
theorem continuous_gradedMk (k : ℕ) : Continuous (gradedMk p G k) := by
  -- `gradedMk` is sealed; its defining equation identifies it with Mathlib's quotient map.
  rw [show gradedMk p G k =
    (fun x => Additive.ofMul (QuotientGroup.mk x)) from funext (gradedMk_def k)]
  exact continuous_quotient_mk'

/-- The quotient map from a lower-series term to its graded piece is open. -/
theorem isOpenQuotientMap_gradedMk (k : ℕ) :
    IsOpenQuotientMap (gradedMk p G k) := by
  -- Use the same equation to transfer the open quotient property across the additive wrapper.
  rw [show gradedMk p G k =
    (fun x => Additive.ofMul (QuotientGroup.mk x)) from funext (gradedMk_def k)]
  exact QuotientGroup.isOpenQuotientMap_mk

/-- The graded commutator is jointly continuous in its two arguments. -/
theorem continuous_gradedBracket (j k : ℕ) :
    Continuous (fun xy : gradedPiece p G j × gradedPiece p G k ↦
      gradedBracket p G j k xy.1 xy.2) := by
  rw [← ((isOpenQuotientMap_gradedMk (p := p) (G := G) j).prodMap
    (isOpenQuotientMap_gradedMk (p := p) (G := G) k)).continuous_comp_iff]
  have hcomm : Continuous (fun xy : pLowerCentralSeries p G j × pLowerCentralSeries p G k ↦
      ⁅(xy.1 : G), (xy.2 : G)⁆) := by
    simp only [commutatorElement_def]
    fun_prop
  have hraw : Continuous (fun xy : pLowerCentralSeries p G j × pLowerCentralSeries p G k ↦
      gradedMk p G (j + k + 1) ⟨⁅(xy.1 : G), (xy.2 : G)⁆,
        commutator_mem_pLowerCentralSeries xy.1.2 xy.2.2⟩) :=
    (continuous_gradedMk (p := p) (G := G) (j + k + 1)).comp (hcomm.subtype_mk _)
  convert hraw using 1
  ext xy
  exact gradedBracket_gradedMk xy.1 xy.2

end TauCeti
