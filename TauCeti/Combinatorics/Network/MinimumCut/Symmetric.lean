/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.MinimumCut.Basic

/-!
# Symmetric terminal cuts

For a symmetric set function, complementing a cut exchanges its source and sink terminal sets
without changing its value. Consequently the two terminal orders have the same minimum value,
and complementation exchanges their smallest and largest minimum source sides.

This interface makes terminal exchange explicit for later uncrossing arguments. Those arguments
can choose either side of an undirected cut while the underlying minimum-cut lattice remains
oriented by inclusion of the source side.
-/

public section

namespace TauCeti

open Finset

variable {V K : Type*}

namespace TerminalCut

/-- Complementing a minimum cut exchanges its source and sink terminal sets. -/
theorem IsMinimum.compl [Fintype V] [DecidableEq V] [Preorder K]
    {f : Finset V → K} (hf : ∀ S, f Sᶜ = f S) {A B S : Finset V}
    (hS : IsMinimum f A B S) : IsMinimum f B A Sᶜ := by
  refine isMinimum_iff.mpr ⟨hS.admissible.compl, fun T hT ↦ ?_⟩
  simpa only [hf] using hS.le hT.compl

/-- Complementing a minimum cut exchanges its source and sink terminal sets. -/
@[simp]
theorem isMinimum_compl_iff [Fintype V] [DecidableEq V] [Preorder K]
    {f : Finset V → K} (hf : ∀ S, f Sᶜ = f S) {A B S : Finset V} :
    IsMinimum f B A Sᶜ ↔ IsMinimum f A B S := by
  constructor
  · intro hS
    simpa only [compl_compl] using hS.compl hf
  · exact fun hS ↦ hS.compl hf

/-- For a symmetric set function, exchanging the terminal sets does not change the minimum cut
value. -/
theorem minimumValue_comm [Fintype V] [DecidableEq V] [LinearOrder K]
    {f : Finset V → K} (hf : ∀ S, f Sᶜ = f S) {A B : Finset V} (hAB : Disjoint A B) :
    minimumValue f hAB = minimumValue f hAB.symm := by
  obtain ⟨S, hS⟩ := exists_minimum f hAB
  have hSc : IsMinimum f B A Sᶜ := hS.compl hf
  calc
    minimumValue f hAB = f S := ((isMinimum_iff_value_eq f hAB).mp hS).2.symm
    _ = f Sᶜ := (hf S).symm
    _ = minimumValue f hAB.symm := ((isMinimum_iff_value_eq f hAB.symm).mp hSc).2

end TerminalCut

namespace IsSymmSubmodular

variable [Fintype V] [DecidableEq V] [AddCommMonoid K] [LinearOrder K]
variable {f : Finset V → K}

/-- Exchanging terminal sets sends the smallest minimum source side to the complement of the
largest one. -/
theorem smallest_symm_eq_compl_largest [IsOrderedCancelAddMonoid K] (hf : IsSymmSubmodular f)
    {A B : Finset V} (hAB : Disjoint A B) :
    TerminalCut.smallest hf.submodular hAB.symm =
      (TerminalCut.largest hf.submodular hAB)ᶜ := by
  apply (TerminalCut.smallest_eq_iff hf.submodular hAB.symm).mpr
  constructor
  · exact (TerminalCut.isGreatest_largest hf.submodular hAB).1.compl hf.symm
  · intro T hT v hv
    have hTc : TerminalCut.IsMinimum f A B Tᶜ := hT.compl hf.symm
    have hsub := (TerminalCut.isGreatest_largest hf.submodular hAB).2 hTc
    simp only [mem_compl] at hv
    by_contra hvT
    exact hv (hsub (mem_compl.mpr hvT))

/-- Exchanging terminal sets sends the largest minimum source side to the complement of the
smallest one. -/
theorem largest_symm_eq_compl_smallest [IsOrderedCancelAddMonoid K] (hf : IsSymmSubmodular f)
    {A B : Finset V} (hAB : Disjoint A B) :
    TerminalCut.largest hf.submodular hAB.symm =
      (TerminalCut.smallest hf.submodular hAB)ᶜ := by
  apply (TerminalCut.largest_eq_iff hf.submodular hAB.symm).mpr
  constructor
  · exact (TerminalCut.isLeast_smallest hf.submodular hAB).1.compl hf.symm
  · intro T hT v hv
    have hTc : TerminalCut.IsMinimum f A B Tᶜ := hT.compl hf.symm
    have hsub := (TerminalCut.isLeast_smallest hf.submodular hAB).2 hTc
    simp only [mem_compl]
    intro hvSmallest
    exact (mem_compl.mp (hsub hvSmallest)) hv

end IsSymmSubmodular

end TauCeti
