/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.Parabolic.Classification

/-!
# Conjugating parabolic subgroups of a Tits system

For a Tits system `(B, N)` in a group `G`, an element `g` that conjugates `B` into a subgroup
`P ⊇ B` already lies in `P`. Consequently, for subgroups `P, Q ⊇ B`, the conjugate `g P g⁻¹` lies
in `Q` exactly when `P ≤ Q` and `g ∈ Q`, and `g P g⁻¹ = Q` exactly when `P = Q` and `g ∈ P`.
Since every subgroup containing `B` is a standard parabolic
(`TauCeti.TitsSystem.standardParabolic_eq_of_subgroupB_le`), this says for standard parabolics
that `g P_J g⁻¹ ≤ P_{J'}` exactly when `J ⊆ J'` and `g ∈ P_{J'}`. In particular two standard
parabolics are conjugate only when they are equal, and a standard parabolic determines its set of
simple reflections up to conjugacy.

Conjugates are written in Mathlib's convention `MulAut.conj g • H` for `g H g⁻¹`.

The argument uses the Bruhat decomposition alone. Write `g ∈ B n B` with `n ∈ N` and choose a
reduced word `s w'` for the class `w` of `n`. The product `(B s B)(B w' B)` is the cell `B w B`,
so every `y ∈ B s B` satisfies `y r⁻¹ ∈ B (n B n⁻¹) ⊆ P` for a representative `r` of `s`; since
`(B s B)(B s B) ⊇ B s B`, the whole cell `B s B` lies in `P`. Conjugating by `r⁻¹ ∈ P` passes to
the shorter element `r⁻¹ n`, and induction on the word finishes. No finiteness, field or topology
is assumed, so the statements apply to the Tits system of any group with a BN-pair.

## Main statements

* `TauCeti.TitsSystem.conj_smul_subgroupB_le_iff`: for `P ⊇ B`, `g B g⁻¹ ≤ P` iff `g ∈ P`.
* `TauCeti.TitsSystem.conj_smul_le_iff_of_subgroupB_le`: for `P, Q ⊇ B`, `g P g⁻¹ ≤ Q` iff
  `P ≤ Q` and `g ∈ Q`.
* `TauCeti.TitsSystem.conj_smul_eq_iff_of_subgroupB_le`: for `P, Q ⊇ B`, `g P g⁻¹ = Q` iff
  `P = Q` and `g ∈ P`.
* `TauCeti.TitsSystem.conj_smul_standardParabolic_le_iff` and
  `TauCeti.TitsSystem.conj_smul_standardParabolic_eq_iff`: the same statements for standard
  parabolics, in terms of their sets of simple reflections, with simp-normal companions such as
  `TauCeti.TitsSystem.conj_smul_subgroupB_le_standardParabolic_iff` for the cases where `B`
  itself (that is, `P_∅`) appears.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §2, nos. 5--6.
* A. Borel and J. Tits, *Groupes réductifs*, Publ. Math. IHÉS 27 (1965), Corollaire 5.18.
-/

public section

open scoped Pointwise

namespace TauCeti.TitsSystem

universe u

variable {G : Type u} [Group G] (T : TitsSystem G)

local prefix:100 "ℓ " => T.simpleGenerators.wordLength

/-- If `n B n⁻¹ ⊆ P`, `r` represents a simple reflection `s`, and the Bruhat cell of `n` is the
product of the cells of `s` and of `r⁻¹ n`, then the simple cell `B s B` lies in `P`. -/
private theorem bruhatCell_subset_of_conj_mem {P : Subgroup G} (hB : T.subgroupB ≤ P)
    {n r : T.subgroupN} (hn : ∀ b ∈ T.subgroupB, (n : G) * b * (n : G)⁻¹ ∈ P)
    {s : T.WeylGroup} (hs : s ∈ T.simple)
    (hcell : T.bruhatCell s * T.bruhatCell (QuotientGroup.mk (r⁻¹ * n)) =
      T.bruhatCell (QuotientGroup.mk n)) :
    T.bruhatCell s ⊆ P := by
  -- Every `y ∈ B s B` has `y r⁻¹ ∈ P`, because `y (r⁻¹ n) ∈ B n B`.
  have key : ∀ y ∈ T.bruhatCell s, y * (r : G)⁻¹ ∈ P := by
    intro y hy
    have hmem : y * ((r⁻¹ * n : T.subgroupN) : G) ∈ T.bruhatCell (QuotientGroup.mk n) := by
      rw [← hcell, T.bruhatCell_mk (r⁻¹ * n)]
      exact Set.mul_mem_mul hy (DoubleCoset.mem_doubleCoset_self _ _ _)
    rw [T.bruhatCell_mk] at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := DoubleCoset.mem_doubleCoset.mp hmem
    rw [Subgroup.coe_mul, InvMemClass.coe_inv, ← mul_assoc] at hab
    rw [eq_mul_inv_of_mul_eq hab]
    simpa only [mul_assoc] using P.mul_mem (hB ha) (hn b hb)
  -- Every element of `B s B` is a product `y z` of two elements of `B s B`.
  intro x hx
  have hxx : x ∈ T.bruhatCell s * T.bruhatCell s := by
    rw [T.bruhatCell_mul_self_eq_union_of_mem_simple hs]
    exact Or.inr hx
  obtain ⟨y, hy, z, hz, rfl⟩ := hxx
  have hz' : z⁻¹ ∈ T.bruhatCell s := by
    simpa only [T.inv_bruhatCell, T.inv_simple hs] using Set.inv_mem_inv.mpr hz
  simpa only [SetLike.mem_coe, mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel_left] using
    P.mul_mem (key y hy) (P.inv_mem (key z⁻¹ hz'))

/-- An element `n ∈ N` whose Weyl class has a reduced word `l` and which conjugates `B` into a
subgroup `P ⊇ B` lies in `P`. -/
private theorem coe_mem_of_conj_mem {P : Subgroup G} (hB : T.subgroupB ≤ P)
    {l : List T.WeylGroup} (hl : ∀ s ∈ l, s ∈ T.simple) (hlen : l.length = ℓ l.prod)
    {n : T.subgroupN} (hnl : (QuotientGroup.mk n : T.WeylGroup) = l.prod)
    (hn : ∀ b ∈ T.subgroupB, (n : G) * b * (n : G)⁻¹ ∈ P) :
    (n : G) ∈ P := by
  induction l generalizing n with
  | nil =>
    rw [List.prod_nil, QuotientGroup.eq_one_iff] at hnl
    exact hB ((T.mem_intersection n).mp hnl)
  | cons s l ih =>
    have hs := hl s List.mem_cons_self
    have htl : ∀ t ∈ l, t ∈ T.simple := fun t ht ↦ hl t (List.mem_cons_of_mem s ht)
    have htail := T.wordLength_prod_le htl
    have hbound := T.wordLength_simple_mul_le hs l.prod
    simp only [List.length_cons, List.prod_cons] at hlen hnl
    obtain ⟨r, hr, hrs⟩ := T.exists_mem_bruhatCell s
    have hrn : (QuotientGroup.mk (r⁻¹ * n) : T.WeylGroup) = l.prod := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hr, hnl,
        inv_mul_cancel_left]
    have hcell : T.bruhatCell s * T.bruhatCell (QuotientGroup.mk (r⁻¹ * n)) =
        T.bruhatCell (QuotientGroup.mk n) := by
      rw [hrn, hnl]
      exact T.bruhatCell_mul_eq_of_wordLength_le hs (by omega)
    have hrP : (r : G) ∈ P := T.bruhatCell_subset_of_conj_mem hB hn hs hcell hrs
    -- The shorter element `r⁻¹ n` conjugates `B` into `r⁻¹ P r = P`.
    have hrnP : ((r⁻¹ * n : T.subgroupN) : G) ∈ P := by
      refine ih htl (by omega) hrn fun b hb ↦ ?_
      simpa only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_rev, inv_inv, mul_assoc] using
        P.mul_mem (P.mul_mem (P.inv_mem hrP) (hn b hb)) hrP
    simpa only [Subgroup.coe_mul, InvMemClass.coe_inv, mul_inv_cancel_left] using
      P.mul_mem hrP hrnP

/-- **Conjugating `B` into an overgroup.** For a subgroup `P` containing `B`, the conjugate
`g B g⁻¹` lies in `P` exactly when `g` does. -/
theorem conj_smul_subgroupB_le_iff {P : Subgroup G} (hB : T.subgroupB ≤ P) {g : G} :
    MulAut.conj g • T.subgroupB ≤ P ↔ g ∈ P := by
  refine ⟨fun h ↦ ?_, fun hg ↦
    (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hB).trans
      (Subgroup.conj_smul_eq_self_of_mem hg).le⟩
  obtain ⟨w, hw, -⟩ := T.existsUnique_mem_bruhatCell g
  obtain ⟨n, rfl, hgn⟩ := T.mem_bruhatCell_iff.mp hw
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hgn
  -- `n B n⁻¹ = a⁻¹ (g B g⁻¹) a` lies in `P`.
  have hn : ∀ c ∈ T.subgroupB, (n : G) * c * (n : G)⁻¹ ∈ P := by
    intro c hc
    have hgc := h (Subgroup.smul_mem_pointwise_smul _ (MulAut.conj (a * n * b)) _
      (T.subgroupB.mul_mem (T.subgroupB.mul_mem (T.subgroupB.inv_mem hb) hc) hb))
    rw [MulAut.smul_def, MulAut.conj_apply] at hgc
    simpa only [mul_inv_rev, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left,
      mul_inv_cancel, inv_mul_cancel, mul_one] using
      P.mul_mem (P.mul_mem (P.inv_mem (hB ha)) hgc) (hB ha)
  obtain ⟨l, hl, hlen, hprod⟩ := T.exists_prod_eq_of_wordLength (QuotientGroup.mk n)
  have hnP := T.coe_mem_of_conj_mem hB hl (hprod ▸ hlen) hprod.symm hn
  exact P.mul_mem (P.mul_mem (hB ha) hnP) (hB hb)

/-- For subgroups `P` and `Q` containing `B`, the conjugate `g P g⁻¹` lies in `Q` exactly when
`P ≤ Q` and `g ∈ Q`. -/
theorem conj_smul_le_iff_of_subgroupB_le {P Q : Subgroup G} (hP : T.subgroupB ≤ P)
    (hQ : T.subgroupB ≤ Q) {g : G} :
    MulAut.conj g • P ≤ Q ↔ P ≤ Q ∧ g ∈ Q := by
  refine ⟨fun h ↦ ?_, fun ⟨hPQ, hg⟩ ↦
    (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hPQ).trans
      (Subgroup.conj_smul_eq_self_of_mem hg).le⟩
  have hg : g ∈ Q := (T.conj_smul_subgroupB_le_iff hQ).mp
    ((Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hP).trans h)
  rw [← Subgroup.conj_smul_eq_self_of_mem hg, Subgroup.pointwise_smul_le_pointwise_smul_iff] at h
  exact ⟨h, hg⟩

/-- For subgroups `P` and `Q` containing `B`, the conjugate `g P g⁻¹` equals `Q` exactly when
`P = Q` and `g ∈ P`: distinct overgroups of `B` are never conjugate, and each is
self-normalizing. -/
theorem conj_smul_eq_iff_of_subgroupB_le {P Q : Subgroup G} (hP : T.subgroupB ≤ P)
    (hQ : T.subgroupB ≤ Q) {g : G} :
    MulAut.conj g • P = Q ↔ P = Q ∧ g ∈ P := by
  refine ⟨fun h ↦ ?_, fun ⟨hPQ, hg⟩ ↦ hPQ ▸ Subgroup.conj_smul_eq_self_of_mem hg⟩
  have hg : g ∈ Q := ((T.conj_smul_le_iff_of_subgroupB_le hP hQ).mp h.le).2
  rw [← Subgroup.conj_smul_eq_self_of_mem hg, smul_left_cancel_iff] at h
  exact ⟨h, h ▸ hg⟩

/-- **Conjugate standard parabolics.** A conjugate `g P_J g⁻¹` lies in `P_{J'}` exactly when
`J ⊆ J'` and `g ∈ P_{J'}`. For `J = ∅` this says that `g B g⁻¹ ≤ P_{J'}` forces `g ∈ P_{J'}`. -/
@[simp]
theorem conj_smul_standardParabolic_le_iff (J J' : Set T.simple) (g : G) :
    MulAut.conj g • T.standardParabolic J ≤ T.standardParabolic J' ↔
      J ⊆ J' ∧ g ∈ T.standardParabolic J' := by
  rw [T.conj_smul_le_iff_of_subgroupB_le (T.subgroupB_le_standardParabolic J)
    (T.subgroupB_le_standardParabolic J'), T.standardParabolic_le_standardParabolic_iff]

/-- **Conjugate standard parabolics are equal.** `g P_J g⁻¹ = P_{J'}` exactly when `J = J'` and
`g ∈ P_J`. -/
@[simp]
theorem conj_smul_standardParabolic_eq_iff (J J' : Set T.simple) (g : G) :
    MulAut.conj g • T.standardParabolic J = T.standardParabolic J' ↔
      J = J' ∧ g ∈ T.standardParabolic J := by
  rw [T.conj_smul_eq_iff_of_subgroupB_le (T.subgroupB_le_standardParabolic J)
    (T.subgroupB_le_standardParabolic J'), le_antisymm_iff,
    T.standardParabolic_le_standardParabolic_iff, T.standardParabolic_le_standardParabolic_iff,
    ← Set.Subset.antisymm_iff]

/-- `g B g⁻¹ ≤ P_J` exactly when `g ∈ P_J`; the simp-normal form of
`conj_smul_standardParabolic_le_iff` for `J = ∅`. -/
@[simp]
theorem conj_smul_subgroupB_le_standardParabolic_iff (J : Set T.simple) (g : G) :
    MulAut.conj g • T.subgroupB ≤ T.standardParabolic J ↔ g ∈ T.standardParabolic J :=
  T.conj_smul_subgroupB_le_iff (T.subgroupB_le_standardParabolic J)

/-- `g P_J g⁻¹ ≤ B` exactly when `J = ∅` and `g ∈ B`; the simp-normal form of
`conj_smul_standardParabolic_le_iff` for `J' = ∅`. -/
@[simp]
theorem conj_smul_standardParabolic_le_subgroupB_iff (J : Set T.simple) (g : G) :
    MulAut.conj g • T.standardParabolic J ≤ T.subgroupB ↔ J = ∅ ∧ g ∈ T.subgroupB := by
  simpa only [standardParabolic_empty, Set.subset_empty_iff] using
    T.conj_smul_standardParabolic_le_iff J ∅ g

/-- `g B g⁻¹ ≤ B` exactly when `g ∈ B`. -/
@[simp]
theorem conj_smul_subgroupB_le_self_iff (g : G) :
    MulAut.conj g • T.subgroupB ≤ T.subgroupB ↔ g ∈ T.subgroupB :=
  T.conj_smul_subgroupB_le_iff le_rfl

/-- `g B g⁻¹ = P_J` exactly when `J = ∅` and `g ∈ B`; the simp-normal form of
`conj_smul_standardParabolic_eq_iff` for `J = ∅`. -/
@[simp]
theorem conj_smul_subgroupB_eq_standardParabolic_iff (J : Set T.simple) (g : G) :
    MulAut.conj g • T.subgroupB = T.standardParabolic J ↔ J = ∅ ∧ g ∈ T.subgroupB := by
  simpa only [standardParabolic_empty, eq_comm (a := (∅ : Set T.simple))] using
    T.conj_smul_standardParabolic_eq_iff ∅ J g

/-- `g P_J g⁻¹ = B` exactly when `J = ∅` and `g ∈ B`; the simp-normal form of
`conj_smul_standardParabolic_eq_iff` for `J' = ∅`. -/
@[simp]
theorem conj_smul_standardParabolic_eq_subgroupB_iff (J : Set T.simple) (g : G) :
    MulAut.conj g • T.standardParabolic J = T.subgroupB ↔ J = ∅ ∧ g ∈ T.subgroupB := by
  have h := T.conj_smul_standardParabolic_eq_iff J ∅ g
  rw [T.standardParabolic_empty] at h
  exact h.trans (and_congr_right fun hJ ↦ by rw [hJ, T.standardParabolic_empty])

/-- `g B g⁻¹ = B` exactly when `g ∈ B`. -/
@[simp]
theorem conj_smul_subgroupB_eq_self_iff (g : G) :
    MulAut.conj g • T.subgroupB = T.subgroupB ↔ g ∈ T.subgroupB := by
  rw [T.conj_smul_eq_iff_of_subgroupB_le le_rfl le_rfl, and_iff_right rfl]

end TauCeti.TitsSystem
