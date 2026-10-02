/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.InformationTheory.Coding.MinimumDistance.Basic
public import TauCeti.InformationTheory.Coding.Additive.SingleCoordinate
public import TauCeti.InformationTheory.Coding.Additive.DirectSum

/-!
# Minimum distance under coordinate operations

Puncturing can reduce minimum distance by at most the number of deleted coordinates, and
preserves dimension as long as the minimum distance is at least two.
Shortening cannot reduce it unless the shortened code is zero. The minimum distance of a
direct sum of two nonzero codes is the minimum of their distances; a zero summand leaves
the distance unchanged. The zero-code cases matter because minimum distance is defined as
zero for the zero code.

The direct-sum formulas apply both to submodules with a module alphabet and to additive subgroups
with an additive group alphabet. Neither alphabet needs to be finite.
The puncturing and shortening bounds hold for additive codes over arbitrary abelian alphabets.
Deleting a nonzero coordinate of a minimum-weight word lowers the distance by exactly one
when the original distance is at least two. The linear results are their specializations.
These formulas connect coordinate operations
to the distance parameters of codes.
They follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*, §§1.5–1.6.
-/

public section

namespace TauCeti

open Set

namespace AdditiveCode

variable {A ι : Type*} [AddCommGroup A]

section CoordinateSets

variable [DecidableEq A] [Fintype ι] (C : AdditiveCode A ι) (s : Set ι)
  [DecidablePred (· ∈ s)]

/-- Puncturing reduces minimum distance by at most the number of deleted coordinates,
including when the punctured code collapses to zero. The set `s` is retained. -/
theorem hammingMinDist_le_hammingMinDist_puncture_add_card_compl :
    hammingMinDist (C : Set (ι → A)) ≤
      hammingMinDist (puncture C s : Set (s → A)) + Fintype.card ↥sᶜ := by
  by_cases hC : C = ⊥
  · simp [hC]
  by_cases hP : puncture C s = ⊥
  · obtain ⟨x, hx, _, hxd⟩ := exists_hammingNorm_eq_hammingMinDist hC
    have hxs : s.domRestrict x = 0 := by
      have hm : s.domRestrict x ∈ puncture C s := mem_puncture.mpr ⟨x, hx, fun _ ↦ rfl⟩
      simpa [hP] using hm
    rw [← hxd, hammingNorm_eq_domRestrict_add_domRestrict_compl s, hxs, hammingNorm_zero]
    simpa [hP] using (hammingNorm_le_card_fintype (x := sᶜ.domRestrict x))
  · obtain ⟨y, hy, hy0, hyd⟩ := exists_hammingNorm_eq_hammingMinDist hP
    obtain ⟨x, hx, hxy⟩ := mem_puncture.mp hy
    have hxs : s.domRestrict x = y := funext hxy
    have hx0 : x ≠ 0 := fun h ↦ hy0 (by rw [← hxs, h]; rfl)
    calc
      hammingMinDist (C : Set (ι → A)) ≤ hammingNorm x :=
        hammingMinDist_le_hammingNorm hx hx0
      _ = hammingNorm y + hammingNorm (sᶜ.domRestrict x) := by
        rw [hammingNorm_eq_domRestrict_add_domRestrict_compl s, hxs]
      _ ≤ hammingMinDist (puncture C s : Set (s → A)) + Fintype.card ↥sᶜ := by
        rw [hyd]
        exact Nat.add_le_add_left hammingNorm_le_card_fintype _

/-- Shortening cannot decrease minimum distance when the shortened additive code is nonzero. -/
theorem hammingMinDist_le_hammingMinDist_shorten (hS : shorten C s ≠ ⊥) :
    hammingMinDist (C : Set (ι → A)) ≤
      hammingMinDist (shorten C s : Set (s → A)) := by
  obtain ⟨y, hy, hy0, hyd⟩ := exists_hammingNorm_eq_hammingMinDist hS
  obtain ⟨x, hx, hxoff, hxy⟩ := mem_shorten.mp hy
  have hxs : s.domRestrict x = y := funext hxy
  have hxsc : sᶜ.domRestrict x = 0 := funext fun i ↦ hxoff i i.2
  have hx0 : x ≠ 0 := fun h ↦ hy0 (by rw [← hxs, h]; rfl)
  calc
    hammingMinDist (C : Set (ι → A)) ≤ hammingNorm x := hammingMinDist_le_hammingNorm hx hx0
    _ = hammingMinDist (shorten C s : Set (s → A)) := by
      rw [hammingNorm_eq_domRestrict_add_domRestrict_compl s, hxs, hxsc, hammingNorm_zero,
        add_zero, hyd]

end CoordinateSets

section SingleCoordinate

variable [DecidableEq A] [Fintype ι] (C : AdditiveCode A ι)

/-- Deleting one coordinate reduces minimum distance by at most one. -/
theorem hammingMinDist_le_hammingMinDist_punctureAt_add_one [DecidableEq ι] (i : ι) :
    hammingMinDist (C : Set (ι → A)) ≤
      hammingMinDist (punctureAt C i : Set (({i}ᶜ : Set ι) → A)) + 1 := by
  simpa only [punctureAt_def, compl_compl, Fintype.card_unique] using
    hammingMinDist_le_hammingMinDist_puncture_add_card_compl C {i}ᶜ

/-- Deleting a nonzero coordinate of a minimum-weight word lowers minimum distance by exactly
one, provided the original minimum distance is at least two. -/
theorem hammingMinDist_punctureAt_add_one_eq [DecidableEq ι] (i : ι) {x : ι → A}
    (hd : 2 ≤ hammingMinDist (C : Set (ι → A))) (hx : x ∈ C)
    (hxw : hammingNorm x = hammingMinDist (C : Set (ι → A))) (hxi : x i ≠ 0) :
    hammingMinDist (punctureAt C i : Set (({i}ᶜ : Set ι) → A)) + 1 =
      hammingMinDist (C : Set (ι → A)) := by
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
  have hyw : hammingNorm y + 1 = hammingMinDist (C : Set (ι → A)) := by
    have hsplit := hammingNorm_eq_domRestrict_add_domRestrict_compl ({i}ᶜ : Set ι) x
    rw [hxw, ← hy, ← hz, hzw] at hsplit
    exact hsplit.symm
  have hy0 : y ≠ 0 := by
    intro h
    simp [h] at hyw
    omega
  have hupper := hammingMinDist_le_hammingNorm (E := punctureAt C i) hyC hy0
  have hlower := hammingMinDist_le_hammingMinDist_punctureAt_add_one C i
  omega

end SingleCoordinate

end AdditiveCode

section CoordinateSets

variable {F ι : Type*} [Field F] [DecidableEq F] [Fintype ι]
  (C : LinearCode F ι) (s : Set ι) [DecidablePred (· ∈ s)]

/-- Puncturing loses at most one unit of minimum distance per deleted coordinate, including
when the punctured code collapses to zero. The set `s` consists of the retained coordinates. -/
theorem hammingMinDist_le_hammingMinDist_puncture_add_card_compl :
    hammingMinDist (C : Set (ι → F)) ≤
      hammingMinDist (puncture C s : Set (s → F)) + Fintype.card ↥sᶜ := by
  simpa only [← LinearCode.puncture_toAddSubgroup, Submodule.coe_toAddSubgroup] using
    AdditiveCode.hammingMinDist_le_hammingMinDist_puncture_add_card_compl C.toAddSubgroup s

/-- Shortening cannot decrease minimum distance if the resulting code is nonzero. -/
theorem hammingMinDist_le_hammingMinDist_shorten (hS : shorten C s ≠ ⊥) :
    hammingMinDist (C : Set (ι → F)) ≤
      hammingMinDist (shorten C s : Set (s → F)) := by
  have hS' : AdditiveCode.shorten C.toAddSubgroup s ≠ ⊥ := by
    rw [← LinearCode.shorten_toAddSubgroup]
    exact fun h ↦ hS (Submodule.toAddSubgroup_injective h)
  simpa only [← LinearCode.shorten_toAddSubgroup, Submodule.coe_toAddSubgroup] using
    AdditiveCode.hammingMinDist_le_hammingMinDist_shorten C.toAddSubgroup s hS'

/-- Deleting one coordinate reduces minimum distance by at most one. -/
theorem hammingMinDist_le_hammingMinDist_punctureAt_add_one [DecidableEq ι] (i : ι) :
    hammingMinDist (C : Set (ι → F)) ≤
      hammingMinDist (punctureAt C i : Set (({i}ᶜ : Set ι) → F)) + 1 := by
  simpa only [← LinearCode.punctureAt_toAddSubgroup, Submodule.coe_toAddSubgroup] using
    AdditiveCode.hammingMinDist_le_hammingMinDist_punctureAt_add_one C.toAddSubgroup i

/-- Deleting a nonzero coordinate of a minimum-weight word lowers minimum distance by exactly
one, provided the original minimum distance is at least two. -/
theorem hammingMinDist_punctureAt_add_one_eq [DecidableEq ι] (i : ι) {x : ι → F}
    (hd : 2 ≤ hammingMinDist (C : Set (ι → F))) (hx : x ∈ C)
    (hxw : hammingNorm x = hammingMinDist (C : Set (ι → F))) (hxi : x i ≠ 0) :
    hammingMinDist (punctureAt C i : Set (({i}ᶜ : Set ι) → F)) + 1 =
      hammingMinDist (C : Set (ι → F)) := by
  simpa only [← LinearCode.punctureAt_toAddSubgroup, Submodule.coe_toAddSubgroup] using
    AdditiveCode.hammingMinDist_punctureAt_add_one_eq C.toAddSubgroup i hd hx hxw hxi

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

variable {R A ι κ : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
  [DecidableEq A] [Fintype ι] [Fintype κ]
  (C : Submodule R (ι → A)) (D : Submodule R (κ → A))

/-- The minimum distance of a direct sum of two nonzero codes is the minimum of their
minimum distances. -/
@[simp]
theorem hammingMinDist_directSum (hC : C ≠ ⊥) (hD : D ≠ ⊥) :
    hammingMinDist (C.directSum D : Set (ι ⊕ κ → A)) =
      min (hammingMinDist (C : Set (ι → A))) (hammingMinDist (D : Set (κ → A))) := by
  have hC' : (C : Set (ι → A)).Nontrivial :=
    Set.nontrivial_coe_sort.mp (Submodule.nontrivial_iff_ne_bot.mpr hC)
  have hD' : (D : Set (κ → A)).Nontrivial :=
    Set.nontrivial_coe_sort.mp (Submodule.nontrivial_iff_ne_bot.mpr hD)
  obtain ⟨x, hx, x', hx', hxx', hxd⟩ := exists_hammingDist_eq_hammingMinDist hC'
  obtain ⟨y, hy, y', hy', hyy', hyd⟩ := exists_hammingDist_eq_hammingMinDist hD'
  have hxmem : Sum.elim x 0 ∈ C.directSum D :=
    Submodule.sumElim_zero_right_mem_directSum D hx
  have hxmem' : Sum.elim x' 0 ∈ C.directSum D :=
    Submodule.sumElim_zero_right_mem_directSum D hx'
  have hxne : Sum.elim x (0 : κ → A) ≠ Sum.elim x' 0 := by
    intro h
    exact hxx' (funext fun i ↦ congrFun h (.inl i))
  -- Embed a pair attaining minimum distance in either summand for both upper bounds.
  apply le_antisymm
  · apply le_min
    · simpa only [hammingDist_sumElim, hammingDist_self, add_zero, hxd] using
        hammingMinDist_le hxmem hxmem' hxne
    · have hymem : Sum.elim (0 : ι → A) y ∈ C.directSum D :=
        Submodule.sumElim_zero_left_mem_directSum C hy
      have hymem' : Sum.elim (0 : ι → A) y' ∈ C.directSum D :=
        Submodule.sumElim_zero_left_mem_directSum C hy'
      have hyne : Sum.elim (0 : ι → A) y ≠ Sum.elim (0 : ι → A) y' := by
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

variable {R A ι κ : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
  [DecidableEq A] [Fintype ι] [Fintype κ]
  (C : Submodule R (ι → A)) (D : Submodule R (κ → A))

/-- Adding a zero code on the right leaves minimum distance unchanged, including for the
zero code on the left. -/
@[simp]
theorem hammingMinDist_directSum_bot :
    hammingMinDist (C.directSum (⊥ : Submodule R (κ → A)) : Set (ι ⊕ κ → A)) =
      hammingMinDist (C : Set (ι → A)) := by
  have hset : (C.directSum (⊥ : Submodule R (κ → A)) : Set (ι ⊕ κ → A)) =
      (fun x : ι → A ↦ Sum.elim x (0 : κ → A)) '' (C : Set (ι → A)) := by
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
    hammingMinDist ((⊥ : Submodule R (ι → A)).directSum D : Set (ι ⊕ κ → A)) =
      hammingMinDist (D : Set (κ → A)) := by
  have hmap := congrArg (fun E : Submodule R (κ ⊕ ι → A) ↦ (E : Set (κ ⊕ ι → A)))
    (Submodule.map_directSum_sumComm (⊥ : Submodule R (ι → A)) D)
  rw [Submodule.map_coe] at hmap
  -- The linear equivalence reindexes words by swapping the two coordinate blocks.
  have hdist := hammingMinDist_image
    (C := ((⊥ : Submodule R (ι → A)).directSum D : Set (ι ⊕ κ → A)))
    (LinearEquiv.funCongrLeft R A (Equiv.sumComm κ ι)).toLinearMap
    (fun x _ y _ _ ↦ (Equiv.sumComm κ ι).hammingDist_comp x y)
  rw [hmap, hammingMinDist_directSum_bot] at hdist
  exact hdist.symm

end ZeroSummand

section AdditiveDirectSum

open AddSubgroup

variable {A ι κ : Type*} [AddGroup A] [DecidableEq A] [Fintype ι] [Fintype κ]

/-- The minimum distance of an additive direct sum of two nonzero codes is the smaller of their
minimum distances. -/
@[simp]
theorem _root_.AddSubgroup.hammingMinDist_directSum (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) (hC : C ≠ ⊥) (hD : D ≠ ⊥) :
    Set.hammingMinDist (C.directSum D : Set (ι ⊕ κ → A)) =
      min (Set.hammingMinDist (C : Set (ι → A))) (Set.hammingMinDist (D : Set (κ → A))) := by
  obtain ⟨x, hx, hx0, hxd⟩ := exists_hammingNorm_eq_hammingMinDist hC
  obtain ⟨y, hy, hy0, hyd⟩ := exists_hammingNorm_eq_hammingMinDist hD
  have hxmem := sumElim_zero_right_mem_directSum D hx
  have hxne : Sum.elim x (0 : κ → A) ≠ 0 := fun h ↦
    hx0 (funext fun i ↦ congrFun h (.inl i))
  have hsum : C.directSum D ≠ ⊥ := by
    intro h
    exact hxne (by simpa only [h, AddSubgroup.mem_bot] using hxmem)
  apply le_antisymm
  · apply le_min
    · simpa only [hammingNorm_sumElim, hammingNorm_zero, add_zero, hxd] using
        hammingMinDist_le_hammingNorm hxmem hxne
    · have hyne : Sum.elim (0 : ι → A) y ≠ 0 := fun h ↦
        hy0 (funext fun j ↦ congrFun h (.inr j))
      simpa only [hammingNorm_sumElim, hammingNorm_zero, zero_add, hyd] using
        hammingMinDist_le_hammingNorm (sumElim_zero_left_mem_directSum C hy) hyne
  · apply (le_hammingMinDist_iff_hammingNorm hsum).mpr
    intro z hz hz0
    obtain ⟨hzC, hzD⟩ := mem_directSum_iff.mp hz
    have hsplit : hammingNorm z =
        hammingNorm (z ∘ Sum.inl) + hammingNorm (z ∘ Sum.inr) := by
      simpa only [Sum.elim_comp_inl_inr] using
        hammingNorm_sumElim (z ∘ Sum.inl) (z ∘ Sum.inr)
    rw [hsplit]
    by_cases hleft : z ∘ Sum.inl = 0
    · have hright : z ∘ Sum.inr ≠ 0 := by
        intro hright
        apply hz0
        funext i
        cases i with
        | inl i => exact congrFun hleft i
        | inr j => exact congrFun hright j
      exact (min_le_right _ _).trans
        ((hammingMinDist_le_hammingNorm hzD hright).trans (Nat.le_add_left _ _))
    · exact (min_le_left _ _).trans
        ((hammingMinDist_le_hammingNorm hzC hleft).trans (Nat.le_add_right _ _))

/-- Adding a zero code on the right preserves minimum distance, including for a zero left code. -/
@[simp]
theorem _root_.AddSubgroup.hammingMinDist_directSum_bot (C : AddSubgroup (ι → A)) :
    Set.hammingMinDist (C.directSum (⊥ : AddSubgroup (κ → A)) : Set (ι ⊕ κ → A)) =
      Set.hammingMinDist (C : Set (ι → A)) := by
  rw [hammingMinDist_eq_sInf_hammingNorm, hammingMinDist_eq_sInf_hammingNorm]
  congr 1
  ext d
  constructor
  · rintro ⟨z, hz, hz0, hzd⟩
    obtain ⟨hzC, hzD⟩ := mem_directSum_iff.mp hz
    have hzD0 : z ∘ Sum.inr = 0 := AddSubgroup.mem_bot.mp hzD
    have hzsplit : Sum.elim (z ∘ Sum.inl) 0 = z := by
      rw [← hzD0, Sum.elim_comp_inl_inr]
    refine ⟨z ∘ Sum.inl, hzC, fun h ↦ hz0 ?_, ?_⟩
    · rw [← hzsplit, h]
      funext i
      cases i <;> rfl
    · rw [← hzsplit, hammingNorm_sumElim, hammingNorm_zero, add_zero] at hzd
      exact hzd
  · rintro ⟨x, hx, hx0, hxd⟩
    refine ⟨Sum.elim x 0, sumElim_zero_right_mem_directSum _ hx, ?_, ?_⟩
    · exact fun h ↦ hx0 (funext fun i ↦ congrFun h (.inl i))
    · simpa only [hammingNorm_sumElim, hammingNorm_zero, add_zero] using hxd

/-- Adding a zero code on the left preserves minimum distance. -/
@[simp]
theorem _root_.AddSubgroup.hammingMinDist_bot_directSum (D : AddSubgroup (κ → A)) :
    Set.hammingMinDist ((⊥ : AddSubgroup (ι → A)).directSum D : Set (ι ⊕ κ → A)) =
      Set.hammingMinDist (D : Set (κ → A)) := by
  have hset : (fun z : ι ⊕ κ → A ↦ z ∘ Equiv.sumComm κ ι) ''
      ((⊥ : AddSubgroup (ι → A)).directSum D : Set (ι ⊕ κ → A)) =
      (D.directSum (⊥ : AddSubgroup (ι → A)) : Set (κ ⊕ ι → A)) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa only [SetLike.mem_coe, mem_directSum_iff, Function.comp_def, Equiv.sumComm_apply,
        Sum.swap_inl, Sum.swap_inr, and_comm] using hw
    · intro hz
      refine ⟨z ∘ Equiv.sumComm ι κ, ?_, ?_⟩
      · simpa only [SetLike.mem_coe, mem_directSum_iff, Function.comp_def, Equiv.sumComm_apply,
          Sum.swap_inl, Sum.swap_inr, and_comm] using hz
      · funext i
        cases i <;> rfl
  have hdist := hammingMinDist_image
    (C := ((⊥ : AddSubgroup (ι → A)).directSum D : Set (ι ⊕ κ → A)))
    (fun z ↦ z ∘ Equiv.sumComm κ ι)
    (fun x _ y _ _ ↦ (Equiv.sumComm κ ι).hammingDist_comp x y)
  rw [hset, AddSubgroup.hammingMinDist_directSum_bot] at hdist
  exact hdist.symm

end AdditiveDirectSum

end TauCeti
