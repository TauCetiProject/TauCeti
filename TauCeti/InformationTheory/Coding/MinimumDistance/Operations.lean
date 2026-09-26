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

Puncturing can reduce minimum distance by at most the number of deleted coordinates, and
preserves dimension as long as the minimum distance is at least two.
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
theorem hammingMinDist_le_hammingMinDist_puncture_add_card_compl :
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

/-- Deleting one coordinate reduces minimum distance by at most one. -/
theorem hammingMinDist_le_hammingMinDist_punctureAt_add_one [DecidableEq ι] (i : ι) :
    hammingMinDist (C : Set (ι → F)) ≤
      hammingMinDist (punctureAt C i : Set (({i}ᶜ : Set ι) → F)) + 1 := by
  simpa only [punctureAt_def, compl_compl, Fintype.card_unique] using
    hammingMinDist_le_hammingMinDist_puncture_add_card_compl C {i}ᶜ

/-- Deleting a nonzero coordinate of a minimum-weight word lowers minimum distance by exactly
one, provided the original minimum distance is at least two. -/
theorem hammingMinDist_punctureAt_add_one_eq [DecidableEq ι] (i : ι) {x : ι → F}
    (hd : 2 ≤ hammingMinDist (C : Set (ι → F))) (hx : x ∈ C)
    (hxw : hammingNorm x = hammingMinDist (C : Set (ι → F))) (hxi : x i ≠ 0) :
    hammingMinDist (punctureAt C i : Set (({i}ᶜ : Set ι) → F)) + 1 =
      hammingMinDist (C : Set (ι → F)) := by
  set y := ({i}ᶜ : Set ι).domRestrict x with hy
  set z := (({i}ᶜ : Set ι)ᶜ).domRestrict x with hz
  have hyC : y ∈ punctureAt C i := by
    rw [punctureAt_def]
    exact mem_puncture.mpr ⟨x, hx, fun _ ↦ rfl⟩
  have hzw : hammingNorm z = 1 := by
    have hle : hammingNorm z ≤ 1 := by
      simpa only [hz, compl_compl, Fintype.card_unique] using
        hammingNorm_le_card_fintype (x := z)
    have hne : z ≠ 0 := fun h ↦ hxi (congrFun h ⟨i, by simp⟩)
    have := (hammingNorm_eq_zero (x := z)).not.mpr hne
    omega
  have hyw : hammingNorm y + 1 = hammingMinDist (C : Set (ι → F)) := by
    have hsplit := hammingNorm_eq_domRestrict_add_domRestrict_compl ({i}ᶜ : Set ι) x
    rw [hxw, ← hy, ← hz, hzw] at hsplit
    exact hsplit.symm
  have hy0 : y ≠ 0 := by
    intro h
    simp [h] at hyw
    omega
  have hupper := hammingMinDist_le_hammingNorm (E := (punctureAt C i).toAddSubgroup) hyC hy0
  rw [Submodule.coe_toAddSubgroup] at hupper
  have hlower := hammingMinDist_le_hammingMinDist_punctureAt_add_one C i
  omega

/-- Deleting one coordinate preserves dimension as soon as the minimum distance is at least
two, since then no nonzero codeword is supported at the deleted coordinate alone. -/
theorem finrank_punctureAt_eq (i : ι)
    (hd : 2 ≤ hammingMinDist (C : Set (ι → F))) :
    Module.finrank F (punctureAt C i) = Module.finrank F C := by
  classical
  rw [punctureAt_def]
  refine finrank_puncture_eq C _ fun x hx hx0 ↦ ?_
  by_contra hne
  have hle := hammingMinDist_le_hammingNorm (E := C.toAddSubgroup) hx hne
  rw [Submodule.coe_toAddSubgroup] at hle
  have hzero : ({i}ᶜ : Set ι).domRestrict x = 0 := funext hx0
  have hone : hammingNorm x ≤ 1 := by
    rw [hammingNorm_eq_domRestrict_add_domRestrict_compl ({i}ᶜ : Set ι) x, hzero,
      hammingNorm_zero, zero_add]
    simpa only [compl_compl, Fintype.card_unique] using
      hammingNorm_le_card_fintype (x := ({i}ᶜᶜ : Set ι).domRestrict x)
  omega

/-- Shortening at one coordinate cannot decrease minimum distance if the result is nonzero. -/
theorem hammingMinDist_le_hammingMinDist_shortenAt [DecidableEq ι] (i : ι)
    (hS : shortenAt C i ≠ ⊥) :
    hammingMinDist (C : Set (ι → F)) ≤
      hammingMinDist (shortenAt C i : Set (({i}ᶜ : Set ι) → F)) := by
  rw [shortenAt_def] at hS ⊢
  exact hammingMinDist_le_hammingMinDist_shorten C {i}ᶜ hS

end CoordinateSets

section DirectSum

variable {R ι κ : Type*} [Semiring R] [DecidableEq R] [Fintype ι] [Fintype κ]
  (C : Submodule R (ι → R)) (D : Submodule R (κ → R))

/-- The minimum distance of a direct sum of two nonzero codes is the minimum of their
minimum distances. -/
@[simp]
theorem hammingMinDist_directSum (hC : C ≠ ⊥) (hD : D ≠ ⊥) :
    hammingMinDist (C.directSum D : Set (ι ⊕ κ → R)) =
      min (hammingMinDist (C : Set (ι → R))) (hammingMinDist (D : Set (κ → R))) := by
  have hC' : (C : Set (ι → R)).Nontrivial :=
    Set.nontrivial_coe_sort.mp (Submodule.nontrivial_iff_ne_bot.mpr hC)
  have hD' : (D : Set (κ → R)).Nontrivial :=
    Set.nontrivial_coe_sort.mp (Submodule.nontrivial_iff_ne_bot.mpr hD)
  obtain ⟨x, hx, x', hx', hxx', hxd⟩ := exists_hammingDist_eq_hammingMinDist hC'
  obtain ⟨y, hy, y', hy', hyy', hyd⟩ := exists_hammingDist_eq_hammingMinDist hD'
  have hxmem : Sum.elim x 0 ∈ C.directSum D :=
    Submodule.sumElim_zero_right_mem_directSum D hx
  have hxmem' : Sum.elim x' 0 ∈ C.directSum D :=
    Submodule.sumElim_zero_right_mem_directSum D hx'
  have hxne : Sum.elim x (0 : κ → R) ≠ Sum.elim x' 0 := by
    intro h
    exact hxx' (funext fun i ↦ congrFun h (.inl i))
  -- Embed a pair attaining minimum distance in either summand for both upper bounds.
  apply le_antisymm
  · apply le_min
    · simpa only [hammingDist_sumElim, hammingDist_self, add_zero, hxd] using
        hammingMinDist_le hxmem hxmem' hxne
    · have hymem : Sum.elim (0 : ι → R) y ∈ C.directSum D :=
        Submodule.sumElim_zero_left_mem_directSum C hy
      have hymem' : Sum.elim (0 : ι → R) y' ∈ C.directSum D :=
        Submodule.sumElim_zero_left_mem_directSum C hy'
      have hyne : Sum.elim (0 : ι → R) y ≠ Sum.elim (0 : ι → R) y' := by
        intro h
        exact hyy' (funext fun i ↦ congrFun h (.inr i))
      simpa only [hammingDist_sumElim, hammingDist_self, zero_add, hyd] using
        hammingMinDist_le hymem hymem' hyne
  -- Distinct words differ in a component, which supplies the lower bound.
  · apply (le_hammingMinDist_iff ⟨_, hxmem, _, hxmem', hxne⟩).mpr
    intro z hz w hw hzw
    obtain ⟨hzC, hzD⟩ := Submodule.mem_directSum_iff.mp hz
    obtain ⟨hwC, hwD⟩ := Submodule.mem_directSum_iff.mp hw
    have hsplit : hammingDist z w =
        hammingDist (z ∘ Sum.inl) (w ∘ Sum.inl) +
          hammingDist (z ∘ Sum.inr) (w ∘ Sum.inr) := by
      simpa only [Sum.elim_comp_inl_inr] using
        hammingDist_sumElim (z ∘ Sum.inl) (w ∘ Sum.inl) (z ∘ Sum.inr) (w ∘ Sum.inr)
    rw [hsplit]
    by_cases hleft : z ∘ Sum.inl = w ∘ Sum.inl
    · have hright : z ∘ Sum.inr ≠ w ∘ Sum.inr := by
        intro hright
        apply hzw
        funext i
        cases i with
        | inl i => exact congrFun hleft i
        | inr i => exact congrFun hright i
      exact (min_le_right _ _).trans
        ((hammingMinDist_le hzD hwD hright).trans (Nat.le_add_left _ _))
    · exact (min_le_left _ _).trans
        ((hammingMinDist_le hzC hwC hleft).trans (Nat.le_add_right _ _))

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
      exact Submodule.sumElim_zero_right_mem_directSum _ hx
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
