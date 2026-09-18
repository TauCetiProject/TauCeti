/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.MinimumDistance.Basic
public import TauCeti.InformationTheory.Coding.Puncture
public import TauCeti.InformationTheory.Coding.DirectSum

/-!
# Minimum distance under coordinate operations

Puncturing can reduce minimum distance by at most the number of deleted coordinates.
Shortening cannot reduce it unless the shortened code is zero. The minimum distance of a
direct sum of two nonzero codes is the minimum of their distances; a zero summand leaves
the distance unchanged. The zero-code cases matter because minimum distance is defined as
zero for the zero code.

These formulas connect the coordinate operations on linear codes to their distance parameters.
They follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*, §§1.5–1.6.
-/

public section

namespace TauCeti

open Set

section CoordinateSets

variable {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]
  (C : LinearCode F ι) (s : Set ι) [DecidablePred (· ∈ s)]

/-- Puncturing loses at most one unit of minimum distance per deleted coordinate, including
when the punctured code collapses to zero. The set `s` consists of the retained coordinates. -/
theorem hammingMinDist_le_hammingMinDist_puncture_add :
    hammingMinDist (C : Set (ι → F)) ≤
      hammingMinDist (puncture C s : Set (s → F)) + Fintype.card ↥sᶜ := by
  by_cases hC : C = ⊥
  · simp [hC]
  have hC' : C.toAddSubgroup ≠ ⊥ := by
    intro h
    exact hC (Submodule.toAddSubgroup_injective h)
  by_cases hP : puncture C s = ⊥
  · obtain ⟨x, hx, -, hxd⟩ := exists_hammingNorm_eq_hammingMinDist hC'
    rw [Submodule.coe_toAddSubgroup] at hxd
    have hxs : s.domRestrict x = 0 := by
      have hm : s.domRestrict x ∈ puncture C s := mem_puncture.mpr ⟨x, hx, fun _ ↦ rfl⟩
      simpa [hP] using hm
    rw [← hxd, hammingNorm_eq_domRestrict_add_domRestrict_compl s, hxs, hammingNorm_zero]
    simpa [hP] using (hammingNorm_le_card_fintype (x := sᶜ.domRestrict x))
  · have hP' : (puncture C s).toAddSubgroup ≠ ⊥ := by
      intro h
      exact hP (Submodule.toAddSubgroup_injective h)
    obtain ⟨y, hy, hy0, hyd⟩ := exists_hammingNorm_eq_hammingMinDist hP'
    rw [Submodule.coe_toAddSubgroup] at hyd
    obtain ⟨x, hx, hxy⟩ := mem_puncture.mp hy
    have hxs : s.domRestrict x = y := funext hxy
    have hx0 : x ≠ 0 := by
      intro h
      apply hy0
      exact funext fun i ↦ (hxy i).symm.trans (congrFun h i)
    calc
      hammingMinDist (C : Set (ι → F)) ≤ hammingNorm x :=
        hammingMinDist_le_hammingNorm (E := C.toAddSubgroup) hx hx0
      _ = hammingNorm y + hammingNorm (sᶜ.domRestrict x) := by
        rw [hammingNorm_eq_domRestrict_add_domRestrict_compl s, hxs]
      _ ≤ hammingMinDist (puncture C s : Set (s → F)) + Fintype.card ↥sᶜ := by
        rw [hyd]
        exact Nat.add_le_add_left hammingNorm_le_card_fintype _

/-- Shortening cannot decrease minimum distance if the resulting code is nonzero. -/
theorem hammingMinDist_le_hammingMinDist_shorten (hS : shorten C s ≠ ⊥) :
    hammingMinDist (C : Set (ι → F)) ≤
      hammingMinDist (shorten C s : Set (s → F)) := by
  have hS' : (shorten C s).toAddSubgroup ≠ ⊥ := by
    intro h
    exact hS (Submodule.toAddSubgroup_injective h)
  obtain ⟨y, hy, hy0, hyd⟩ := exists_hammingNorm_eq_hammingMinDist hS'
  rw [Submodule.coe_toAddSubgroup] at hyd
  obtain ⟨x, hx, hxoff, hxy⟩ := mem_shorten.mp hy
  have hxs : s.domRestrict x = y := funext hxy
  have hxsc : sᶜ.domRestrict x = 0 := funext fun i ↦ hxoff i i.2
  have hx0 : x ≠ 0 := by
    intro h
    apply hy0
    exact funext fun i ↦ (hxy i).symm.trans (congrFun h i)
  calc
    hammingMinDist (C : Set (ι → F)) ≤ hammingNorm x :=
      hammingMinDist_le_hammingNorm (E := C.toAddSubgroup) hx hx0
    _ = hammingMinDist (shorten C s : Set (s → F)) := by
      rw [hammingNorm_eq_domRestrict_add_domRestrict_compl s, hxs, hxsc, hammingNorm_zero,
        add_zero, hyd]

end CoordinateSets

section DirectSum

variable {R ι κ : Type*} [Ring R] [DecidableEq R] [Fintype ι] [Fintype κ]
  (C : Submodule R (ι → R)) (D : Submodule R (κ → R))

/-- The minimum distance of a direct sum of two nonzero codes is the minimum of their
minimum distances. -/
theorem hammingMinDist_directSum (hC : C ≠ ⊥) (hD : D ≠ ⊥) :
    hammingMinDist (C.directSum D : Set (ι ⊕ κ → R)) =
      min (hammingMinDist (C : Set (ι → R))) (hammingMinDist (D : Set (κ → R))) := by
  have hC' : C.toAddSubgroup ≠ ⊥ := fun h ↦ hC (Submodule.toAddSubgroup_injective h)
  have hD' : D.toAddSubgroup ≠ ⊥ := fun h ↦ hD (Submodule.toAddSubgroup_injective h)
  obtain ⟨x, hx, hx0, hxd⟩ := exists_hammingNorm_eq_hammingMinDist hC'
  obtain ⟨y, hy, hy0, hyd⟩ := exists_hammingNorm_eq_hammingMinDist hD'
  rw [Submodule.coe_toAddSubgroup] at hxd hyd
  have hxmem : Sum.elim x 0 ∈ C.directSum D :=
    Submodule.mem_directSum_iff.mpr ⟨hx, D.zero_mem⟩
  have hxne : Sum.elim x (0 : κ → R) ≠ 0 := by
    intro h
    exact hx0 (funext fun i ↦ congrFun h (.inl i))
  have hE : (C.directSum D).toAddSubgroup ≠ ⊥ := by
    intro h
    have hxmem' : Sum.elim x (0 : κ → R) ∈ (C.directSum D).toAddSubgroup := hxmem
    rw [h] at hxmem'
    exact hxne (by simpa only [AddSubgroup.mem_bot] using hxmem')
  -- Embed a minimum-weight word of either summand to obtain both upper bounds.
  apply le_antisymm
  · apply le_min
    · have h := hammingMinDist_le_hammingNorm
        (E := (C.directSum D).toAddSubgroup) hxmem hxne
      simpa only [Submodule.coe_toAddSubgroup, hammingNorm_sumElim, hammingNorm_zero,
        add_zero, hxd] using h
    · have hymem : Sum.elim (0 : ι → R) y ∈ C.directSum D :=
        Submodule.mem_directSum_iff.mpr ⟨C.zero_mem, hy⟩
      have hyne : Sum.elim (0 : ι → R) y ≠ 0 := by
        intro h
        exact hy0 (funext fun i ↦ congrFun h (.inr i))
      have h := hammingMinDist_le_hammingNorm
        (E := (C.directSum D).toAddSubgroup) hymem hyne
      simpa only [Submodule.coe_toAddSubgroup, hammingNorm_sumElim, hammingNorm_zero,
        zero_add, hyd] using h
  -- A nonzero word has a nonzero component, which supplies the lower bound.
  · rw [← Submodule.coe_toAddSubgroup]
    apply (le_hammingMinDist_iff_hammingNorm hE).mpr
    intro z hz hz0
    obtain ⟨hzC, hzD⟩ := Submodule.mem_directSum_iff.mp hz
    have hzsplit : z = Sum.elim (fun i ↦ z (.inl i)) (fun j ↦ z (.inr j)) := by
      funext i
      cases i <;> rfl
    rw [hzsplit, hammingNorm_sumElim]
    by_cases hleft : (fun i ↦ z (.inl i)) = 0
    · have hright : (fun j ↦ z (.inr j)) ≠ 0 := by
        intro hright
        apply hz0
        rw [hzsplit, hleft, hright]
        funext i
        cases i <;> rfl
      exact (min_le_right _ _).trans ((hammingMinDist_le_hammingNorm
        (E := D.toAddSubgroup) hzD hright).trans (Nat.le_add_left _ _))
    · exact (min_le_left _ _).trans ((hammingMinDist_le_hammingNorm
        (E := C.toAddSubgroup) hzC hleft).trans (Nat.le_add_right _ _))

end DirectSum

section ZeroSummand

variable {R ι κ : Type*} [Semiring R] [DecidableEq R] [Fintype ι] [Fintype κ]
  (C : Submodule R (ι → R)) (D : Submodule R (κ → R))

/-- Adding a zero code on the right leaves minimum distance unchanged, including for the
zero code on the left. -/
@[simp]
theorem hammingMinDist_directSum_bot :
    hammingMinDist (C.directSum (⊥ : Submodule R (κ → R)) : Set (ι ⊕ κ → R)) =
      hammingMinDist (C : Set (ι → R)) := by
  have hset : (C.directSum (⊥ : Submodule R (κ → R)) : Set (ι ⊕ κ → R)) =
      (fun x : ι → R ↦ Sum.elim x (0 : κ → R)) '' (C : Set (ι → R)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hx, hy⟩ := Submodule.mem_directSum_iff.mp hz
      refine ⟨fun i ↦ z (.inl i), hx, ?_⟩
      have hy0 : (fun j ↦ z (.inr j)) = 0 := by simpa only [Submodule.mem_bot] using hy
      funext i
      cases i with
      | inl i => rfl
      | inr i => exact (congrFun hy0 i).symm
    · rintro ⟨x, hx, rfl⟩
      exact Submodule.mem_directSum_iff.mpr ⟨hx, Submodule.zero_mem _⟩
  rw [hset]
  apply hammingMinDist_image
  intro x _ y _ _
  simp only [hammingDist_sumElim, hammingDist_self, add_zero]

/-- Adding a zero code on the left leaves minimum distance unchanged. -/
@[simp]
theorem hammingMinDist_bot_directSum :
    hammingMinDist ((⊥ : Submodule R (ι → R)).directSum D : Set (ι ⊕ κ → R)) =
      hammingMinDist (D : Set (κ → R)) := by
  have hmap := congrArg (fun E : Submodule R (κ ⊕ ι → R) ↦ (E : Set (κ ⊕ ι → R)))
    (Submodule.map_directSum_sumComm (⊥ : Submodule R (ι → R)) D)
  rw [Submodule.map_coe] at hmap
  -- The linear equivalence reindexes words by swapping the two coordinate blocks.
  have hdist := hammingMinDist_image
    (C := ((⊥ : Submodule R (ι → R)).directSum D : Set (ι ⊕ κ → R)))
    (LinearEquiv.funCongrLeft R R (Equiv.sumComm κ ι)).toLinearMap
    (fun x _ y _ _ ↦ (Equiv.sumComm κ ι).hammingDist_comp x y)
  rw [hmap, hammingMinDist_directSum_bot] at hdist
  exact hdist.symm

end ZeroSummand

end TauCeti
