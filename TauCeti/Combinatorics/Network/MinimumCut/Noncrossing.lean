/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.MinimumCut.Symmetric
public import TauCeti.Data.Finset.Laminar
import Mathlib.Data.Set.Card

/-!
# Non-crossing minimum cuts

Minimum cuts of a submodular set function can be uncrossed by intersection and union without
changing their values. For a symmetric submodular set function, complementing one of the cuts
also lets them be uncrossed by the two set differences.

The main result is the non-crossing lemma. If two vertices lie on the same side of a minimum
`s`–`t` cut, they have a minimum cut with one side contained in that `s`–`t` side. This is a basic
ingredient in constructions of Gomory–Hu cut trees.

Those constructions maintain a whole family of pairwise non-crossing minimum cuts. Two cuts
cross when each side of one meets each side of the other; representing every cut by its side
avoiding a fixed root vertex turns a non-crossing family into a laminar one, whose members are
pairwise nested or disjoint. Uncrossing by union preserves non-crossing, which gives the
multi-cut non-crossing lemma: if no member of such a family separates `s` from `t`, some minimum
`s`–`t` cut crosses none of its members.

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


section MultiCut

variable [Fintype V] [DecidableEq V] [AddCommMonoid K] [LinearOrder K]
  [IsOrderedCancelAddMonoid K]
variable {f : Finset V → K}

/-- One uncrossing step: a minimum `s`–`t` cut crossing a minimum `a`–`b` cut `Z` that avoids
both `s` and `t` can be replaced by a minimum `s`–`t` cut that does not cross `Z` and crosses
no cut that neither original cut crosses. -/
private theorem IsMinimum.exists_uncross (hf : IsSymmSubmodular f) {s t a b : V}
    {X Z : Finset V} (hX : IsMinimum f {s} {t} X) (hZ : IsMinimum f {a} {b} Z)
    (hsZ : s ∉ Z) (htZ : t ∉ Z) (hXZ : Crosses X Z) :
    ∃ X', IsMinimum f {s} {t} X' ∧ ¬Crosses X' Z ∧
      ∀ Y, ¬Crosses X Y → ¬Crosses Z Y → ¬Crosses X' Y := by
  obtain ⟨hsX, htX⟩ := isAdmissible_singleton.mp hX.admissible
  obtain ⟨haZ, hbZ⟩ := isAdmissible_singleton.mp hZ.admissible
  obtain ⟨hmeet, -, ⟨w, hwZ, hwX⟩, -⟩ := crosses_def.mp hXZ
  by_cases haX : a ∈ X
  · -- Enlarge `X` by `Z`, which meets it.
    have hmin := hZ.uncross_union_inter hf.submodular hX
      (isAdmissible_singleton.mpr ⟨mem_union_right _ hsX, by simp [htX, htZ]⟩)
      (isAdmissible_singleton.mpr ⟨mem_inter.mpr ⟨haZ, haX⟩, fun h ↦ hbZ (mem_inter.mp h).1⟩)
    refine ⟨Z ∪ X, hmin.1, ?_, fun Y hXY hZY ↦ ?_⟩
    · exact (NestedOrDisjoint.of_superset subset_union_left).not_crosses
    · obtain ⟨v, hvX, hvZ⟩ := hmeet
      exact not_crosses_union ⟨v, mem_inter.mpr ⟨hvZ, hvX⟩⟩ hZY hXY
  · -- Shrink `X` away from `Z`; the complement `Xᶜ ∪ Z` is a union of two meeting sets.
    have hmin := hX.uncross_sdiff hf hZ
      (isAdmissible_singleton.mpr ⟨mem_sdiff.mpr ⟨hsX, hsZ⟩, fun h ↦ htX (mem_sdiff.mp h).1⟩)
      (isAdmissible_singleton.mpr ⟨mem_sdiff.mpr ⟨haZ, haX⟩, fun h ↦ hbZ (mem_sdiff.mp h).1⟩)
    refine ⟨X \ Z, hmin.1, ?_, fun Y hXY hZY ↦ ?_⟩
    · exact (NestedOrDisjoint.of_disjoint sdiff_disjoint).not_crosses
    · have h := not_crosses_union ⟨w, mem_inter.mpr ⟨mem_compl.mpr hwX, hwZ⟩⟩
        (crosses_compl_left.not.mpr hXY) hZY
      have hcompl : Xᶜ ∪ Z = (X \ Z)ᶜ := by
        simp [Finset.sdiff_eq_inter_compl, Finset.compl_inter]
      rwa [hcompl, crosses_compl_left] at h

/-- **Multi-cut non-crossing lemma.** Let `𝒞` be a pairwise non-crossing family of cuts, each a
minimum cut of a symmetric submodular `f` between some pair of vertices. If none of them
separates the distinct vertices `s` and `t`, then some minimum `s`–`t` cut crosses none of
them. -/
theorem exists_isMinimum_forall_not_crosses (hf : IsSymmSubmodular f)
    {𝒞 : Set (Finset V)} (h𝒞 : 𝒞.Pairwise fun Y Z ↦ ¬Crosses Y Z)
    (hmin : ∀ Y ∈ 𝒞, ∃ a b, IsMinimum f {a} {b} Y) {s t : V} (hst : s ≠ t)
    (hsep : ∀ Y ∈ 𝒞, s ∈ Y ↔ t ∈ Y) :
    ∃ X, IsMinimum f {s} {t} X ∧ ∀ Y ∈ 𝒞, ¬Crosses X Y := by
  -- Choose a minimum `s`–`t` cut crossing as few members of `𝒞` as possible.
  let crossed : Finset V → Set (Finset V) := fun X ↦ {Y ∈ 𝒞 | Crosses X Y}
  obtain ⟨X, hX, hXmin⟩ := Set.exists_min_image {X | IsMinimum f {s} {t} X}
    (fun X ↦ (crossed X).ncard) (Set.toFinite _)
    (exists_minimum f (disjoint_singleton.mpr hst))
  refine ⟨X, hX, fun Z hZ hXZ ↦ ?_⟩
  -- Represent `Z` by its side avoiding both `s` and `t`.
  obtain ⟨a, b, hab⟩ := hmin Z hZ
  obtain ⟨Z', a', b', hZ', hsZ', htZ', hZZ'⟩ : ∃ Z' a' b', IsMinimum f {a'} {b'} Z' ∧
      s ∉ Z' ∧ t ∉ Z' ∧ ∀ Y, Crosses Z' Y ↔ Crosses Z Y := by
    by_cases hs : s ∈ Z
    · exact ⟨Zᶜ, b, a, hab.compl hf.symm, by simpa using hs,
        by simpa [← hsep Z hZ] using hs, fun _ ↦ crosses_compl_left⟩
    · exact ⟨Z, a, b, hab, hs, by rwa [← hsep Z hZ], fun _ ↦ Iff.rfl⟩
  obtain ⟨X', hX', hX'Z, hX'Y⟩ :=
    hX.exists_uncross hf hZ' hsZ' htZ' (crosses_comm.mp ((hZZ' X).mpr hXZ.symm))
  -- The new cut crosses only members that `X` crosses, and not `Z`.
  have hsub : crossed X' ⊂ crossed X := by
    refine ⟨fun Y ⟨hY, hX'Y'⟩ ↦ ⟨hY, by_contra fun hXY ↦ ?_⟩, fun h ↦ ?_⟩
    · obtain rfl | hYZ := eq_or_ne Y Z
      · exact hX'Z (crosses_comm.mp ((hZZ' X').mpr hX'Y'.symm))
      · exact hX'Y Y hXY ((hZZ' Y).not.mpr (h𝒞 hZ hY hYZ.symm)) hX'Y'
    · exact hX'Z (crosses_comm.mp ((hZZ' X').mpr (h ⟨hZ, hXZ⟩).2.symm))
  exact (Set.ncard_lt_ncard hsub (Set.toFinite _)).not_ge (hXmin X' hX')

end MultiCut

end TerminalCut

end TauCeti
