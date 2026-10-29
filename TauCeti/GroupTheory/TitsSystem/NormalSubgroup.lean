/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.TitsSystem.Parabolic.Classification
public import TauCeti.GroupTheory.TitsSystem.Coxeter
public import Mathlib.GroupTheory.IsPerfect
public import TauCeti.GroupTheory.DerivedCentralQuotient
import Mathlib.Algebra.Group.Subgroup.Pointwise
import TauCeti.Algebra.Group.Subgroup.Normalizer
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

Irreducibility is `TauCeti.TitsSystem.IsIrreducible`, defined with the Coxeter system of a Tits
system.

In the finite groups of Lie type the whole group is usually not perfect, and the simple group is
cut out inside it. For a *split* BN-pair, with a solvable subgroup `U` normalized by `B` and
`B ≤ U ⊔ (B ∩ N)`, let `H⁺` be the normal closure of `U`. Unless `H⁺ ≤ Z`, Tits's theorem gives
`H⁺ B = G`, hence `G = H⁺ (B ∩ N)`, so the Tits system pulls back to `H⁺`
(`TauCeti.TitsSystem.comap`) and the theorems above apply to it. If `H⁺` is perfect, every normal
subgroup of `H⁺` lies in `Z` or is `H⁺`. If moreover `Z ∩ U = 1`, then `Z` centralizes `H⁺`, so
`Z ∩ H⁺` is the centre of `H⁺`, and `H⁺` modulo its centre is simple once `U ≠ 1`. When `H⁺` is
the derived subgroup, this is the simplicity of `TauCeti.DerivedCentralQuotient G`.

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
* `TauCeti.TitsSystem.le_subgroupOf_normalCore_or_eq_top_of_normal`: for a split BN-pair, every
  normal subgroup of the normal closure `H⁺` of `U` lies in `Z` or is `H⁺`.
* `TauCeti.TitsSystem.center_normalClosure_eq_subgroupOf_normalCore`: the centre of `H⁺` is
  `Z ∩ H⁺`.
* `TauCeti.TitsSystem.isSimpleGroup_normalClosure_quotient_center`: `H⁺` modulo its centre is
  simple.
* `TauCeti.TitsSystem.isSimpleGroup_derivedCentralQuotient`: if `H⁺ = [G, G]`, then
  `[G, G] / Z([G, G])` is simple.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §2, no. 7.
* J. E. Humphreys, *Linear Algebraic Groups* (1975), Section 29.5.
* B. Conrad, *Tits systems and simplicity*, handout for Math 249B (Stanford, 2016), Theorem 2.4,
  https://math.stanford.edu/~conrad/249BW16Page/handouts/titssystem.pdf
-/

public section

open scoped Pointwise

namespace TauCeti.TitsSystem

universe u

variable {G : Type u} [Group G] (T : TitsSystem G)

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

/-! ### The normal closure of `U` in a split BN-pair -/

variable {U : Subgroup G}

/-- If `H⁺ ⊔ B = G` for the normal closure `H⁺` of `U` and `B ≤ U ⊔ (B ∩ N)`, then every element of
`G` is `x t` with `x ∈ H⁺` and `t ∈ B ∩ N`, so the Tits system pulls back to `H⁺`. -/
private theorem exists_mul_eq_of_sup_eq_top
    (hsplit : T.subgroupB ≤ U ⊔ T.subgroupB ⊓ T.subgroupN)
    (htop : Subgroup.normalClosure (U : Set G) ⊔ T.subgroupB = ⊤) (g : G) :
    ∃ x : Subgroup.normalClosure (U : Set G), ∃ t ∈ T.subgroupB ⊓ T.subgroupN,
      (Subgroup.normalClosure (U : Set G)).subtype x * t = g := by
  have hle : Subgroup.normalClosure (U : Set G) ⊔ T.subgroupB ≤
      Subgroup.normalClosure (U : Set G) ⊔ T.subgroupB ⊓ T.subgroupN :=
    sup_le le_sup_left (hsplit.trans (sup_le_sup_right Subgroup.le_normalClosure _))
  obtain ⟨x, hx, t, ht, rfl⟩ : g ∈ (Subgroup.normalClosure (U : Set G) : Set G) *
      (T.subgroupB ⊓ T.subgroupN : Subgroup G) := by
    rw [← Subgroup.normal_mul]
    exact hle (htop ▸ Subgroup.mem_top g)
  exact ⟨⟨x, hx⟩, t, ht, rfl⟩

/-- The pulled-back `B` normalizes `U`, read inside its normal closure. -/
private theorem comap_subgroupB_le_normalizer (hBU : T.subgroupB ≤ Subgroup.normalizer (U : Set G))
    (hf : ∀ g : G, ∃ x : Subgroup.normalClosure (U : Set G), ∃ t ∈ T.subgroupB ⊓ T.subgroupN,
      (Subgroup.normalClosure (U : Set G)).subtype x * t = g) :
    (T.comap _ hf).subgroupB ≤
      Subgroup.normalizer (U.subgroupOf (Subgroup.normalClosure (U : Set G)) : Set _) := by
  rw [← Subgroup.subgroupOf_normalizer_eq Subgroup.le_normalClosure, comap_subgroupB]
  exact Subgroup.comap_mono hBU

/-- **Tits's theorem for the normal closure of `U`.** Suppose the Weyl group is irreducible, `U` is
a solvable subgroup normalized by `B` with `B ≤ U ⊔ (B ∩ N)` (as for a split BN-pair
`B = U ⋊ (B ∩ N)`), and the normal closure `H⁺` of `U` is perfect. Then every normal subgroup of
`H⁺` lies in the normal core `Z = ⋂ g B g⁻¹` of `B`, or is `H⁺`. -/
theorem le_subgroupOf_normalCore_or_eq_top_of_normal (hirr : T.IsIrreducible)
    (hBU : T.subgroupB ≤ Subgroup.normalizer (U : Set G))
    (hsplit : T.subgroupB ≤ U ⊔ T.subgroupB ⊓ T.subgroupN) [Group.IsSolvable U]
    [Group.IsPerfect (Subgroup.normalClosure (U : Set G))]
    (K : Subgroup (Subgroup.normalClosure (U : Set G))) [K.Normal] :
    K ≤ T.subgroupB.normalCore.subgroupOf (Subgroup.normalClosure (U : Set G)) ∨ K = ⊤ := by
  -- Either `H⁺ ≤ Z`, or `H⁺ B = G`; then `G = H⁺ (B ∩ N)`, and the theorem for normal subgroups
  -- applies to the Tits system pulled back to `H⁺`, whose normal core of `B` is `Z ∩ H⁺`.
  rcases T.le_normalCore_or_sup_eq_top_of_normal hirr (Subgroup.normalClosure (U : Set G))
    with h | htop
  · exact Or.inl fun x _ ↦ h x.2
  have hf := T.exists_mul_eq_of_sup_eq_top hsplit htop
  have : Group.IsSolvable (U.subgroupOf (Subgroup.normalClosure (U : Set G))) :=
    (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalClosure).isSolvable_congr.mpr ‹_›
  exact ((T.comap _ hf).le_normalCore_or_eq_top_of_normal
    ((T.isIrreducible_comap_iff _ hf).mpr hirr) (T.comap_subgroupB_le_normalizer hBU hf)
    (Subgroup.normalClosure_subgroupOf_normalClosure_eq_top
      (eq_top_iff.mpr (htop.ge.trans (sup_le_sup_left hBU _)))) K).imp_left
    fun h ↦ h.trans (T.normalCore_comap_subgroupB _ hf).le

/-- **The centre of the normal closure of `U`.** Under the hypotheses of
`TauCeti.TitsSystem.le_subgroupOf_normalCore_or_eq_top_of_normal`, if moreover the normal core
`Z = ⋂ g B g⁻¹` of `B` meets `U` trivially, then the centre of the normal closure `H⁺` of `U` is
`Z ∩ H⁺`. -/
theorem center_normalClosure_eq_subgroupOf_normalCore (hirr : T.IsIrreducible)
    (hBU : T.subgroupB ≤ Subgroup.normalizer (U : Set G))
    (hsplit : T.subgroupB ≤ U ⊔ T.subgroupB ⊓ T.subgroupN)
    (hZU : Disjoint T.subgroupB.normalCore U) [Group.IsSolvable U]
    [Group.IsPerfect (Subgroup.normalClosure (U : Set G))] :
    Subgroup.center (Subgroup.normalClosure (U : Set G)) =
      T.subgroupB.normalCore.subgroupOf (Subgroup.normalClosure (U : Set G)) := by
  -- The centre is normal, so it lies in `Z` unless `H⁺` is commutative, hence trivial. Conversely
  -- `Z` normalizes `U` and meets it trivially, so it centralizes `H⁺`.
  refine le_antisymm ?_ fun x hx ↦ Subgroup.mem_center_iff.mpr fun y ↦ Subtype.ext ?_
  · refine (T.le_subgroupOf_normalCore_or_eq_top_of_normal hirr hBU hsplit _).elim id fun h ↦ ?_
    have := Subgroup.center_eq_top_iff.mp h
    exact fun x _ ↦ Subsingleton.elim (1 : Subgroup.normalClosure (U : Set G)) x ▸ one_mem _
  · exact (Subgroup.mem_centralizer_iff.mp (Subgroup.normalClosure_le_centralizer_of_le_normalizer
      ((Subgroup.normalCore_le _).trans hBU) hZU y.2) x hx).symm

/-- **Tits's simplicity theorem for the normal closure of `U`.** Suppose the Weyl group is
irreducible, `U ≠ 1` is a solvable subgroup normalized by `B` with `B ≤ U ⊔ (B ∩ N)`, the normal
core `⋂ g B g⁻¹` of `B` meets `U` trivially, and the normal closure `H⁺` of `U` is perfect. Then
`H⁺` modulo its centre is simple. -/
theorem isSimpleGroup_normalClosure_quotient_center (hirr : T.IsIrreducible)
    (hBU : T.subgroupB ≤ Subgroup.normalizer (U : Set G))
    (hsplit : T.subgroupB ≤ U ⊔ T.subgroupB ⊓ T.subgroupN)
    (hZU : Disjoint T.subgroupB.normalCore U) (hU : U ≠ ⊥) [Group.IsSolvable U]
    [Group.IsPerfect (Subgroup.normalClosure (U : Set G))] :
    IsSimpleGroup (Subgroup.normalClosure (U : Set G) ⧸
      Subgroup.center (Subgroup.normalClosure (U : Set G))) := by
  -- Apply Tits's simplicity theorem to the Tits system pulled back to `H⁺`; its normal core of `B`
  -- is `Z ∩ H⁺`, the centre of `H⁺`.
  have hUZ : ¬ Subgroup.normalClosure (U : Set G) ≤ T.subgroupB.normalCore :=
    fun h ↦ hU (hZU.symm.eq_bot_of_le (Subgroup.le_normalClosure.trans h))
  have htop := (T.le_normalCore_or_sup_eq_top_of_normal hirr _).resolve_left hUZ
  have hf := T.exists_mul_eq_of_sup_eq_top hsplit htop
  have hS : (T.comap _ hf).simple.Nonempty := by
    obtain ⟨s, hs⟩ := Set.nonempty_iff_ne_empty.mpr fun h ↦ hUZ (by
      rw [T.subgroupB_eq_top_iff.mpr h, Subgroup.normalCore_eq_self]
      exact le_top)
    exact ⟨(T.comapWeylGroupMulEquiv _ hf).symm s, by simpa using hs⟩
  have : Group.IsSolvable (U.subgroupOf (Subgroup.normalClosure (U : Set G))) :=
    (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalClosure).isSolvable_congr.mpr ‹_›
  have := (T.comap _ hf).isSimpleGroup_quotient_normalCore hS
    ((T.isIrreducible_comap_iff _ hf).mpr hirr) (T.comap_subgroupB_le_normalizer hBU hf)
    (Subgroup.normalClosure_subgroupOf_normalClosure_eq_top
      (eq_top_iff.mpr (htop.ge.trans (sup_le_sup_left hBU _))))
  exact (QuotientGroup.quotientMulEquivOfEq
    ((T.center_normalClosure_eq_subgroupOf_normalCore hirr hBU hsplit hZU).trans
      (T.normalCore_comap_subgroupB _ hf).symm)).isSimpleGroup

/-- **Simplicity of the derived central quotient.** If, under the hypotheses of
`TauCeti.TitsSystem.isSimpleGroup_normalClosure_quotient_center`, the normal closure of `U` is the
derived subgroup `[G, G]`, then `[G, G] / Z([G, G])` is simple. -/
theorem isSimpleGroup_derivedCentralQuotient (hirr : T.IsIrreducible)
    (hBU : T.subgroupB ≤ Subgroup.normalizer (U : Set G))
    (hsplit : T.subgroupB ≤ U ⊔ T.subgroupB ⊓ T.subgroupN)
    (hZU : Disjoint T.subgroupB.normalCore U) (hU : U ≠ ⊥) [Group.IsSolvable U]
    (hcomm : Subgroup.normalClosure (U : Set G) = commutator G)
    [Group.IsPerfect (commutator G)] :
    IsSimpleGroup (DerivedCentralQuotient G) := by
  have : Group.IsPerfect (Subgroup.normalClosure (U : Set G)) := hcomm ▸ ‹_›
  have := T.isSimpleGroup_normalClosure_quotient_center hirr hBU hsplit hZU hU
  rwa [hcomm] at this

end TauCeti.TitsSystem
