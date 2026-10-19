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

/-- Complementing a source side exchanges the source and sink terminal sets. -/
@[simp]
theorem isAdmissible_compl_iff [Fintype V] [DecidableEq V] {A B S : Finset V} :
    IsAdmissible B A Sᶜ ↔ IsAdmissible A B S := by
  constructor
  · intro hS
    apply isAdmissible_iff.mpr
    refine ⟨fun v hvA ↦ ?_, Finset.disjoint_left.mpr fun v hvS hvB ↦ ?_⟩
    · by_contra hvS
      exact Finset.disjoint_left.mp hS.disjoint (mem_compl.mpr hvS) hvA
    · exact (mem_compl.mp (hS.subset hvB)) hvS
  · intro hS
    apply isAdmissible_iff.mpr
    refine ⟨fun v hvB ↦ mem_compl.mpr fun hvS ↦
      Finset.disjoint_left.mp hS.disjoint hvS hvB, Finset.disjoint_left.mpr fun v hvSc hvA ↦ ?_⟩
    exact (mem_compl.mp hvSc) (hS.subset hvA)

end TerminalCut

namespace IsSymmSubmodular

variable [Fintype V] [DecidableEq V]

section Preorder

variable [AddCommMonoid K] [Preorder K]
variable {f : Finset V → K}

/-- Complementing a minimum cut exchanges its source and sink terminal sets. -/
@[simp]
theorem isMinimum_compl_iff (hf : IsSymmSubmodular f) {A B S : Finset V} :
    TerminalCut.IsMinimum f B A Sᶜ ↔ TerminalCut.IsMinimum f A B S := by
  constructor
  · intro hS
    refine TerminalCut.isMinimum_iff.mpr ⟨TerminalCut.isAdmissible_compl_iff.mp hS.admissible,
      fun T hT ↦ ?_⟩
    have hTc : TerminalCut.IsAdmissible B A Tᶜ :=
      TerminalCut.isAdmissible_compl_iff.mpr hT
    simpa only [IsSymmSubmodular.symm hf] using hS.le hTc
  · intro hS
    refine TerminalCut.isMinimum_iff.mpr ⟨TerminalCut.isAdmissible_compl_iff.mpr hS.admissible,
      fun T hT ↦ ?_⟩
    have hTc : TerminalCut.IsAdmissible A B Tᶜ := by
      simpa only [compl_compl] using
        (TerminalCut.isAdmissible_compl_iff (A := B) (B := A) (S := T)).mpr hT
    simpa only [IsSymmSubmodular.symm hf] using hS.le hTc

/-- Complementing a minimum singleton-terminal cut reverses its terminals. -/
theorem isMinimum_singleton_compl_iff (hf : IsSymmSubmodular f) {s t : V}
    {S : Finset V} :
    TerminalCut.IsMinimum f {t} {s} Sᶜ ↔ TerminalCut.IsMinimum f {s} {t} S :=
  isMinimum_compl_iff hf

end Preorder

section LinearOrder

variable [AddCommMonoid K] [LinearOrder K]
variable {f : Finset V → K}

/-- For a symmetric set function, exchanging the terminal sets does not change the minimum cut
value. -/
theorem minimumValue_comm (hf : IsSymmSubmodular f) {A B : Finset V}
    (hAB : Disjoint A B) :
    TerminalCut.minimumValue f hAB = TerminalCut.minimumValue f hAB.symm := by
  obtain ⟨S, hS⟩ := TerminalCut.exists_minimum f hAB
  have hSc : TerminalCut.IsMinimum f B A Sᶜ := (isMinimum_compl_iff hf).mpr hS
  calc
    TerminalCut.minimumValue f hAB = f S :=
      ((TerminalCut.isMinimum_iff_value_eq f hAB).mp hS).2.symm
    _ = f Sᶜ := (IsSymmSubmodular.symm hf S).symm
    _ = TerminalCut.minimumValue f hAB.symm :=
      ((TerminalCut.isMinimum_iff_value_eq f hAB.symm).mp hSc).2

/-- Exchanging terminal sets sends the smallest minimum source side to the complement of the
largest one. -/
theorem smallest_comm [IsOrderedCancelAddMonoid K] (hf : IsSymmSubmodular f)
    {A B : Finset V} (hAB : Disjoint A B) :
    TerminalCut.smallest hf.submodular hAB.symm =
      (TerminalCut.largest hf.submodular hAB)ᶜ := by
  apply (TerminalCut.smallest_eq_iff hf.submodular hAB.symm).mpr
  constructor
  · exact (isMinimum_compl_iff hf).mpr
      (TerminalCut.isGreatest_largest hf.submodular hAB).1
  · intro T hT v hv
    have hTc : TerminalCut.IsMinimum f A B Tᶜ := by
      simpa only [compl_compl] using
        (isMinimum_compl_iff hf (A := B) (B := A) (S := T)).mpr hT
    have hsub := (TerminalCut.isGreatest_largest hf.submodular hAB).2 hTc
    simp only [mem_compl] at hv
    by_contra hvT
    exact hv (hsub (mem_compl.mpr hvT))

/-- Exchanging terminal sets sends the largest minimum source side to the complement of the
smallest one. -/
theorem largest_comm [IsOrderedCancelAddMonoid K] (hf : IsSymmSubmodular f)
    {A B : Finset V} (hAB : Disjoint A B) :
    TerminalCut.largest hf.submodular hAB.symm =
      (TerminalCut.smallest hf.submodular hAB)ᶜ := by
  apply (TerminalCut.largest_eq_iff hf.submodular hAB.symm).mpr
  constructor
  · exact (isMinimum_compl_iff hf).mpr
      (TerminalCut.isLeast_smallest hf.submodular hAB).1
  · intro T hT v hv
    have hTc : TerminalCut.IsMinimum f A B Tᶜ := by
      simpa only [compl_compl] using
        (isMinimum_compl_iff hf (A := B) (B := A) (S := T)).mpr hT
    have hsub := (TerminalCut.isLeast_smallest hf.submodular hAB).2 hTc
    simp only [mem_compl]
    intro hvSmallest
    exact (mem_compl.mp (hsub hvSmallest)) hv

/-- Reversing distinct singleton terminals does not change the minimum cut value. -/
theorem minimumValue_singleton_comm (hf : IsSymmSubmodular f) {s t : V} (hst : s ≠ t) :
    TerminalCut.minimumValue f (A := {s}) (B := {t}) (by simpa using hst) =
      TerminalCut.minimumValue f (A := {t}) (B := {s}) (by simpa using hst.symm) :=
  minimumValue_comm hf (by simpa using hst)

end LinearOrder

end IsSymmSubmodular

end TauCeti
