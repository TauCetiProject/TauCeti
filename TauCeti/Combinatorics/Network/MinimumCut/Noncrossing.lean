/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.MinimumCut.Symmetric

/-!
# Non-crossing minimum cuts

Minimum cuts of a submodular set function can be uncrossed by intersection and union without
changing their values. For a symmetric submodular set function, complementing one of the cuts
also lets them be uncrossed by the two set differences.

The main result is the non-crossing lemma. If two vertices lie on the same side of a minimum
`s`–`t` cut, they have a minimum cut with one side contained in that `s`–`t` side. This is a basic
ingredient in constructions of Gomory–Hu cut trees.

## References

* B. Korte and J. Vygen, *Combinatorial Optimization: Theory and Algorithms*, Section 8.6.
* D. Gusfield, *Very Simple Methods for All Pairs Network Flow Analysis*, SIAM J. Comput. 19
  (1990), 143–155.
-/

public section

namespace TauCeti

open Finset

variable {V K : Type*}

namespace TerminalCut

section Preorder

variable [DecidableEq V] [AddCommMonoid K] [Preorder K]
  [IsOrderedCancelAddMonoid K]
variable {f : Finset V → K}

/-- Uncross two minimum cuts by union and intersection when the resulting sides have the
required terminal orientations. -/
theorem IsMinimum.uncross_union_inter (hf : IsSubmodular f)
    {A B C D S T : Finset V} (hS : IsMinimum f A B S) (hT : IsMinimum f C D T)
    (hunion : IsAdmissible C D (S ∪ T)) (hinter : IsAdmissible A B (S ∩ T)) :
    IsMinimum f C D (S ∪ T) ∧ IsMinimum f A B (S ∩ T) := by
  have h := hf.isMinOn_sup_inf (s := {U | IsAdmissible A B U}) (t := {U | IsAdmissible C D U})
    (isMinOn_iff.mpr fun _ ↦ hS.le) (isMinOn_iff.mpr fun _ ↦ hT.le) hunion hinter
  exact ⟨isMinimum_iff.mpr ⟨hunion, isMinOn_iff.mp h.1⟩,
    isMinimum_iff.mpr ⟨hinter, isMinOn_iff.mp h.2⟩⟩

/-- Uncross two minimum cuts by set difference when the resulting sides have the required
terminal orientations. -/
theorem IsMinimum.uncross_sdiff [Fintype V] (hf : IsSymmSubmodular f)
    {A B C D S T : Finset V} (hS : IsMinimum f A B S)
    (hT : IsMinimum f C D T)
    (hST : IsAdmissible A B (S \ T)) (hTS : IsAdmissible C D (T \ S)) :
    IsMinimum f A B (S \ T) ∧ IsMinimum f C D (T \ S) := by
  have hST_eq : S \ T = S ∩ Tᶜ := sdiff_eq_inter_compl S T
  have hTS_eq : (S ∪ Tᶜ)ᶜ = T \ S := by
    rw [compl_union, compl_compl, sdiff_eq_inter_compl, inter_comm]
  have h := hS.uncross_union_inter hf.submodular (hT.compl hf.symm)
    (isAdmissible_compl_iff.mp (by rwa [hTS_eq])) (by rwa [← hST_eq])
  exact ⟨hST_eq ▸ h.2, hTS_eq ▸ h.1.compl hf.symm⟩

end Preorder

section LinearOrder

variable [Fintype V] [DecidableEq V] [AddCommMonoid K] [LinearOrder K]
  [IsOrderedCancelAddMonoid K]
variable {f : Finset V → K}

/-- **Non-crossing lemma.** If `u` and `v` lie on the same side `S` of a minimum `s`–`t` cut,
then some minimum cut between `u` and `v` has a side contained in `S`. The contained side may be
oriented from either of its two terminals. -/
theorem IsMinimum.exists_isMinimum_subset (hf : IsSymmSubmodular f)
    {s t u v : V} {S : Finset V} (hS : IsMinimum f {s} {t} S)
    (hu : u ∈ S) (hv : v ∈ S) (huv : u ≠ v) :
    ∃ T ⊆ S, IsMinimum f {u} {v} T ∨ IsMinimum f {v} {u} T := by
  have huvDisjoint : Disjoint ({u} : Finset V) {v} := by
    simp [huv]
  obtain ⟨X, hX⟩ := exists_minimum f huvDisjoint
  have huX : u ∈ X := by
    exact (isAdmissible_singleton.mp hX.admissible).1
  have hvX : v ∉ X := by
    exact (isAdmissible_singleton.mp hX.admissible).2
  have hsS : s ∈ S := by
    exact (isAdmissible_singleton.mp hS.admissible).1
  have htS : t ∉ S := by
    exact (isAdmissible_singleton.mp hS.admissible).2
  by_cases htX : t ∈ X
  · have hXc : IsMinimum f {v} {u} Xᶜ := hX.compl hf.symm
    have hSc : IsMinimum f {t} {s} Sᶜ := hS.compl hf.symm
    have hSX : IsAdmissible {v} {u} (Xᶜ \ Sᶜ) := by
      simp [isAdmissible_singleton, huX, hvX, hu, hv]
    have hXS : IsAdmissible {t} {s} (Sᶜ \ Xᶜ) := by
      simp [isAdmissible_singleton, hsS, htS, htX]
    have hmin := hXc.uncross_sdiff hf hSc hSX hXS
    refine ⟨S \ X, sdiff_subset, Or.inr ?_⟩
    simpa only [compl_sdiff_compl] using hmin.1
  · have hunion : IsAdmissible {s} {t} (X ∪ S) := by
      simp only [isAdmissible_singleton, mem_union]
      exact ⟨Or.inr hsS, not_or.mpr ⟨htX, htS⟩⟩
    have hinter : IsAdmissible {u} {v} (X ∩ S) := by
      simp only [isAdmissible_singleton, mem_inter]
      exact ⟨⟨huX, hu⟩, fun h ↦ hvX h.1⟩
    have hmin := hX.uncross_union_inter hf.submodular hS hunion hinter
    exact ⟨X ∩ S, inter_subset_right, Or.inl hmin.2⟩

end LinearOrder

end TerminalCut

end TauCeti
