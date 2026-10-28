/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.Parabolic.Classification
public import Mathlib.GroupTheory.IsPerfect
import Mathlib.Algebra.Group.Subgroup.Pointwise
import TauCeti.GroupTheory.Solvable

/-!
# Normal subgroups of a group with a Tits system, and Tits's simplicity theorem

Let `G` carry a Tits system `(B, N)` with simple reflections `S` in the Weyl group `W`. For a
normal subgroup `H` of `G`, the subgroup `H ⊔ B = H B` contains `B`, so it is a standard
parabolic `P_J`. **Tits's theorem on normal subgroups** says that `J` and its complement in `S`
commute elementwise. Consequently, if the Coxeter system `(W, S)` is irreducible, either `H` lies
in `B`, hence in the normal core `Z = ⋂ g B g⁻¹` of `B`, or `H B = G`.

Combined with a solvable subgroup `U` normalized by `B` whose conjugates generate a perfect group
`G`, this gives **Tits's simplicity theorem**: every normal subgroup of `G` lies in `Z` or is all
of `G`, so `G / Z` is simple as soon as `S` is nonempty. This is the abstract simplicity
criterion behind the simplicity of the finite groups of Lie type.

Irreducibility, `TauCeti.TitsSystem.IsIrreducible`, is a condition on the simple reflections:
every subset `J` of `S` that commutes elementwise with its complement is empty or all of `S`. For
nonempty `S` this says exactly that the Coxeter graph of `(W, S)` is connected, that is, that
`(W, S)` is irreducible.

## Main definitions

* `TauCeti.TitsSystem.IsIrreducible`: every set of simple reflections commuting elementwise with
  its complement is empty or everything.

## Main results

* `TauCeti.TitsSystem.simple_mul_comm_of_bruhatCell_subset_sup`: if `H` is normal, a simple
  reflection whose cell lies in `H B` commutes with one whose cell does not.
* `TauCeti.TitsSystem.exists_standardParabolic_eq_sup_of_normal`: Tits's theorem on normal
  subgroups.
* `TauCeti.TitsSystem.le_normalCore_or_sup_eq_top_of_normal`: the irreducible dichotomy
  `H ≤ Z` or `H B = G`.
* `TauCeti.TitsSystem.le_normalCore_or_eq_top_of_normal`: Tits's simplicity theorem for normal
  subgroups.
* `TauCeti.TitsSystem.isSimpleGroup_quotient_normalCore`: the quotient `G / Z` is simple.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §2, no. 7.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Section 29.5.
-/

public section

open scoped Pointwise

namespace TauCeti.TitsSystem

universe u

variable {G : Type u} [Group G] (T : TitsSystem G)

/-- The Weyl group of a Tits system is **irreducible** if every set `J` of simple reflections that
commutes elementwise with its complement is empty or all of `S`. For nonempty `S` this says exactly
that the Coxeter graph of `(W, S)` is connected. -/
def IsIrreducible : Prop :=
  ∀ J : Set T.simple, (∀ s ∈ J, ∀ t ∉ J, (s : T.WeylGroup) * t = t * s) → J = ∅ ∨ J = Set.univ

/-- Unfolds `TauCeti.TitsSystem.IsIrreducible`. -/
theorem isIrreducible_iff : T.IsIrreducible ↔
    ∀ J : Set T.simple, (∀ s ∈ J, ∀ t ∉ J, (s : T.WeylGroup) * t = t * s) →
      J = ∅ ∨ J = Set.univ :=
  Iff.rfl

/-- If `H` is normal, every Bruhat cell contained in `H ⊔ B` meets `H`. -/
private theorem exists_mem_bruhatCell_of_subset_sup {H : Subgroup G} [H.Normal]
    {w : T.WeylGroup} (hw : T.bruhatCell w ⊆ (H ⊔ T.subgroupB : Subgroup G)) :
    ∃ h ∈ H, h ∈ T.bruhatCell w := by
  obtain ⟨n, -, hn⟩ := T.exists_mem_bruhatCell w
  obtain ⟨h, hh, b, hb, hhb⟩ := (Subgroup.normal_mul H T.subgroupB ▸ hw hn :
    (n : G) ∈ (H : Set G) * T.subgroupB)
  refine ⟨h, hh, ?_⟩
  rw [← T.bruhatCell_mul_subgroupB w]
  exact ⟨n, hn, b⁻¹, inv_mem hb, by simp only [← hhb, mul_inv_cancel_right]⟩

/-- **The key step of Tits's theorem on normal subgroups.** If `H` is normal, a simple reflection
whose Bruhat cell lies in `H ⊔ B` commutes with every simple reflection whose cell does not. -/
theorem simple_mul_comm_of_bruhatCell_subset_sup {H : Subgroup G} [H.Normal]
    {s t : T.WeylGroup} (hs : s ∈ T.simple) (ht : t ∈ T.simple)
    (hsH : T.bruhatCell s ⊆ (H ⊔ T.subgroupB : Subgroup G))
    (htH : ¬ T.bruhatCell t ⊆ (H ⊔ T.subgroupB : Subgroup G)) :
    s * t = t * s := by
  -- Otherwise `B t B · B s B · B t B` is the single cell of the reduced word `t s t`. Conjugating
  -- an element of `H ∩ B s B` by an element of `B t B` puts that cell, and hence `B t B`, in `H B`.
  by_contra hst
  have h2 := T.wordLength_simple_mul_simple_of_ne ht hs fun h ↦ hst (by rw [h])
  have h3 := T.wordLength_simple_mul_simple_mul_simple_of_mul_ne ht hs (Ne.symm hst)
  obtain ⟨h, hh, hhs⟩ := T.exists_mem_bruhatCell_of_subset_sup hsH
  obtain ⟨m, -, hm⟩ := T.exists_mem_bruhatCell t
  have hconj : (m : G) * h * (m : G)⁻¹ ∈ T.bruhatCell (t * s * t) := by
    rw [← T.bruhatCell_mul_eq_of_wordLength_le_right (t * s) ht (by omega),
      ← T.bruhatCell_mul_eq_of_wordLength_le ht (w := s) (by rw [T.wordLength_simple hs]; omega)]
    refine Set.mul_mem_mul (Set.mul_mem_mul hm hhs) ?_
    rw [← T.inv_simple ht, ← T.inv_bruhatCell]
    exact Set.inv_mem_inv.mpr hm
  have hcell := T.bruhatCell_subset_of_mem le_sup_right hconj
    (le_sup_left (b := T.subgroupB) ((inferInstance : H.Normal).conj_mem h hh m))
  have hword : [t, s, t].prod = t * s * t := by
    simp only [List.prod_cons, List.prod_nil, mul_one, mul_assoc]
  exact htH (T.bruhatCell_subset_of_mem_reduced_word le_sup_right (by simp [hs, ht])
    (by rw [hword, h3]; rfl) (hword ▸ hcell) t (by simp))

/-- **Tits's theorem on normal subgroups.** For a normal subgroup `H`, the subgroup `H ⊔ B` is a
standard parabolic `P_J` for a set `J` of simple reflections that commutes elementwise with its
complement. -/
theorem exists_standardParabolic_eq_sup_of_normal (H : Subgroup G) [H.Normal] :
    ∃ J : Set T.simple, T.standardParabolic J = H ⊔ T.subgroupB ∧
      ∀ s ∈ J, ∀ t ∉ J, (s : T.WeylGroup) * t = t * s :=
  ⟨_, T.standardParabolic_eq_of_subgroupB_le le_sup_right,
    fun s hs t ht ↦ T.simple_mul_comm_of_bruhatCell_subset_sup s.property t.property hs ht⟩

/-- **Normal subgroups for an irreducible Weyl group.** If every set of simple reflections
commuting elementwise with its complement is empty or everything, then a normal subgroup `H`
either lies in the normal core `⋂ g B g⁻¹` of `B` or satisfies `H ⊔ B = G`. -/
theorem le_normalCore_or_sup_eq_top_of_normal (hirr : T.IsIrreducible)
    (H : Subgroup G) [H.Normal] : H ≤ T.subgroupB.normalCore ∨ H ⊔ T.subgroupB = ⊤ := by
  obtain ⟨J, hJ, hcomm⟩ := T.exists_standardParabolic_eq_sup_of_normal H
  rcases T.isIrreducible_iff.mp hirr J hcomm with rfl | rfl
  · exact Or.inl (Subgroup.normal_le_normalCore.mpr
      (sup_eq_right.mp (hJ.symm.trans T.standardParabolic_empty)))
  · exact Or.inr (hJ.symm.trans T.standardParabolic_univ)

/-- **Tits's simplicity theorem, for normal subgroups.** Suppose the Weyl group is irreducible,
`G` is perfect, and `U` is a solvable subgroup normalized by `B` whose conjugates generate `G`.
Then every normal subgroup of `G` either lies in the normal core `⋂ g B g⁻¹` of `B` or is `G`. -/
theorem le_normalCore_or_eq_top_of_normal (hirr : T.IsIrreducible)
    [Group.IsPerfect G] {U : Subgroup G} [Group.IsSolvable U]
    (hBU : T.subgroupB ≤ Subgroup.normalizer (U : Set G))
    (hU : Subgroup.normalClosure (U : Set G) = ⊤)
    (H : Subgroup G) [H.Normal] : H ≤ T.subgroupB.normalCore ∨ H = ⊤ :=
  (T.le_normalCore_or_sup_eq_top_of_normal hirr H).imp_right
    (Subgroup.Normal.eq_top_of_self_sup_eq_top_of_le_normalizer hBU hU)

/-- **Tits's simplicity theorem.** Suppose there is at least one simple reflection, the Weyl group
is irreducible, `G` is perfect, and `U` is a solvable subgroup normalized by `B` whose conjugates
generate `G`. Then the quotient of `G` by the normal core `⋂ g B g⁻¹` of `B` is simple. -/
theorem isSimpleGroup_quotient_normalCore (hS : T.simple.Nonempty) (hirr : T.IsIrreducible)
    [Group.IsPerfect G] {U : Subgroup G} [Group.IsSolvable U]
    (hBU : T.subgroupB ≤ Subgroup.normalizer (U : Set G))
    (hU : Subgroup.normalClosure (U : Set G) = ⊤) :
    IsSimpleGroup (G ⧸ T.subgroupB.normalCore) := by
  have hπ := QuotientGroup.mk'_surjective T.subgroupB.normalCore
  have : Nontrivial (G ⧸ T.subgroupB.normalCore) := QuotientGroup.nontrivial_iff.mpr
    fun h ↦ (T.subgroupB_eq_top_iff.not.mpr hS.ne_empty)
      (top_le_iff.mp (h ▸ T.subgroupB.normalCore_le))
  refine { eq_bot_or_eq_top_of_normal := fun K hK ↦ ?_ }
  have := hK.comap (QuotientGroup.mk' T.subgroupB.normalCore)
  rcases T.le_normalCore_or_eq_top_of_normal hirr hBU hU
    (K.comap (QuotientGroup.mk' T.subgroupB.normalCore)) with h | h
  · refine Or.inl (eq_bot_iff.mpr fun x hx ↦ ?_)
    obtain ⟨g, rfl⟩ := hπ x
    exact (QuotientGroup.eq_one_iff g).mpr (h hx)
  · rw [← Subgroup.map_comap_eq_self_of_surjective hπ K, h, Subgroup.map_top_of_surjective _ hπ]
    exact Or.inr rfl

end TauCeti.TitsSystem
