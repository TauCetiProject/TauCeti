/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Acyclic.Forest
public import TauCeti.RepresentationTheory.Quiver.Reflection.Admissible

/-!
# Any two orientations of a forest are related by reflections at sinks

Reflecting a quiver at a sink reverses the arrows meeting that vertex and keeps its underlying
multigraph (`Quiver.nonempty_reflectList_sum_hom_equiv`). This file proves the converse
for a forest: if a quiver `q` on a finite vertex type has at most one arrow between any two
vertices and an acyclic underlying graph, then every quiver `q'` with the same underlying
multigraph is reached from `q` by reflecting along a sink-admissible list of vertices
(`Quiver.exists_isSinkAdmissible_reflectList_equiv`).

The arrows are turned around one at a time. Removing an arrow `u ⟶ w` from a forest disconnects
`w` from `u`; let `B` be the set of vertices still connected to `w`. The arrow `u ⟶ w` is the only
one joining `B` to its complement, and it points into `B`, so no arrow leaves `B`. Reflecting at
the vertices of `B`, listed so that no arrow runs from an earlier entry to a later one, is then
sink-admissible, and it reverses exactly the arrows joining `B` to its complement: the single
arrow `u ⟶ w`. The orientation of a forest is acyclic
(`TauCeti.Quiver.isAcyclic_of_isAcyclic_underlyingGraph`), which provides such a listing.

## Main results

* `Quiver.exists_isSinkAdmissible_reflectList_equiv`: two orientations of the same finite
  forest are related by a sequence of reflections at sinks.

## References

* I. N. Bernstein, I. M. Gelfand, V. A. Ponomarev, *Coxeter functors and Gabriel's theorem*,
  Russian Math. Surveys **28** (1973), 17--32.
* H. Derksen, J. Weyman, *An Introduction to Quiver Representations*, Chapter 4.
-/

public section

namespace TauCeti

open _root_.Quiver

universe u v

variable {V : Type u}

namespace Quiver

/-- **Turning around a single arrow of a forest by reflections at sinks.** For an arrow `u ⟶ w`
of an acyclic quiver on finitely many vertices whose underlying graph is a forest, reflecting
along a suitable sink-admissible list turns that arrow around and leaves the arrows between every
other pair of vertices in place. -/
private theorem exists_isSinkAdmissible_flip [Finite V] [q : _root_.Quiver.{v} V]
    (hacyc : IsAcyclic V) (hG : (underlyingGraph V).IsAcyclic) {u w : V} (e : u ⟶ w) :
    ∃ l : List V, IsSinkAdmissible q l ∧ IsEmpty (@_root_.Quiver.Hom V (reflectList q l) u w) ∧
      ∀ a b : V, s(a, b) ≠ s(u, w) →
        (Nonempty (@_root_.Quiver.Hom V (reflectList q l) a b) ↔ Nonempty (a ⟶ b)) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  have huw : u ≠ w := fun h ↦ (hacyc.isEmpty_hom_self u).elim (h ▸ e)
  -- the vertices still connected to `w` once the edge of `e` is removed
  let H := (underlyingGraph V).deleteEdges {s(u, w)}
  let B : Finset V := Finset.univ.filter fun x ↦ H.Reachable w x
  have hmemB (x : V) : x ∈ B ↔ H.Reachable w x := by simp [B]
  have huB : u ∉ B := fun hu ↦ (SimpleGraph.isBridge_iff.mp
    (SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp hG (underlyingGraph_adj_of_hom e huw)))
      ((hmemB u).mp hu).symm
  -- an arrow joining `B` to its complement lies over the removed edge
  have hcross (a b : V) (ha : a ∈ B) (hb : b ∉ B) (hab : Nonempty (a ⟶ b) ∨ Nonempty (b ⟶ a)) :
      s(a, b) = s(u, w) := by
    by_contra hne
    have hadj : H.Adj a b := SimpleGraph.deleteEdges_adj.mpr
      ⟨underlyingGraph_adj.mpr ⟨fun h ↦ hb (h ▸ ha), hab⟩, by simpa using hne⟩
    exact hb ((hmemB b).mpr (((hmemB a).mp ha).trans hadj.reachable))
  -- no arrow leaves `B`
  have hout (x : V) (hx : x ∈ B) (b : V) (hb : b ∉ B) : IsEmpty (x ⟶ b) := ⟨fun f ↦ by
    rcases Sym2.eq_iff.mp (hcross x b hx hb (.inl ⟨f⟩)) with ⟨rfl, -⟩ | ⟨rfl, rfl⟩
    · exact huB hx
    · exact (hacyc.isEmpty_hom_of_hom e).elim f⟩
  -- an arrow joining two vertices on different sides of `B` lies over the removed edge
  have hsplit (a b : V) (hab : ¬(a ∈ B ↔ b ∈ B)) (hne : s(a, b) ≠ s(u, w)) :
      IsEmpty (a ⟶ b) ∧ IsEmpty (b ⟶ a) := by
    by_cases ha : a ∈ B
    · have hb : b ∉ B := fun hb ↦ hab (iff_of_true ha hb)
      exact ⟨⟨fun f ↦ hne (hcross a b ha hb (.inl ⟨f⟩))⟩,
        ⟨fun f ↦ hne (hcross a b ha hb (.inr ⟨f⟩))⟩⟩
    · have hb : b ∈ B := by tauto
      exact ⟨⟨fun f ↦ hne (Sym2.eq_swap.trans (hcross b a hb ha (.inr ⟨f⟩)))⟩,
        ⟨fun f ↦ hne (Sym2.eq_swap.trans (hcross b a hb ha (.inl ⟨f⟩)))⟩⟩
  obtain ⟨l, hnd, hmem, hp⟩ := hacyc.exists_pairwise_isEmpty_hom B
  have hwu : ¬(w ∈ l ↔ u ∈ l) := by
    rw [hmem, hmem]
    exact fun h ↦ huB (h.mp ((hmemB w).mpr .rfl))
  refine ⟨l, isSinkAdmissible_of_pairwise q hnd (fun x _ ↦ hacyc.isEmpty_hom_self x) hp
      fun x hx b hb ↦ hout x ((hmem x).mp hx) b fun h ↦ hb ((hmem b).mpr h), ?_, ?_⟩
  · rw [hom_reflectList_of_not_iff q hnd fun h ↦ hwu h.symm]
    exact hacyc.isEmpty_hom_of_hom e
  · intro a b hne
    by_cases hab : a ∈ l ↔ b ∈ l
    · rw [hom_reflectList q hnd hab]
    · rw [hom_reflectList_of_not_iff q hnd hab]
      obtain ⟨h₁, h₂⟩ := hsplit a b (by rwa [hmem, hmem] at hab) hne
      exact iff_of_false (not_nonempty_iff.mpr h₂) (not_nonempty_iff.mpr h₁)

/-- The arrows of `q` which `q'` turns around: the ordered pairs of vertices joined by an arrow of
`q` but not by an arrow of `q'`. -/
private noncomputable def _root_.Quiver.flipSet [Fintype V] (q q' : _root_.Quiver.{v} V) :
    Finset (V × V) := by
  classical
  exact Finset.univ.filter fun p ↦
    Nonempty (@_root_.Quiver.Hom V q p.1 p.2) ∧ IsEmpty (@_root_.Quiver.Hom V q' p.1 p.2)

private theorem _root_.Quiver.mem_flipSet [Fintype V] {q q' : _root_.Quiver.{v} V} {a b : V} :
    (a, b) ∈ flipSet q q' ↔
      Nonempty (@_root_.Quiver.Hom V q a b) ∧ IsEmpty (@_root_.Quiver.Hom V q' a b) := by
  classical
  simp [flipSet]

/-- When `q'` turns no arrow of `q` around, and the two quivers have the same underlying
multigraph with at most one arrow between any two vertices, their arrows agree. -/
private theorem nonempty_hom_equiv_of_flipSet_eq_empty [Fintype V] {q q' : _root_.Quiver.{v} V}
    (hsub : ∀ a b : V,
      Subsingleton (@_root_.Quiver.Hom V q a b ⊕ @_root_.Quiver.Hom V q b a))
    (h : ∀ a b : V, Nonempty ((@_root_.Quiver.Hom V q a b ⊕ @_root_.Quiver.Hom V q b a) ≃
      (@_root_.Quiver.Hom V q' a b ⊕ @_root_.Quiver.Hom V q' b a)))
    (hempty : flipSet q q' = ∅) (a b : V) :
    Nonempty (@_root_.Quiver.Hom V q a b ≃ @_root_.Quiver.Hom V q' a b) := by
  have hsub' (a b : V) :
      Subsingleton (@_root_.Quiver.Hom V q' a b ⊕ @_root_.Quiver.Hom V q' b a) :=
    have := hsub a b
    (h a b).some.symm.subsingleton
  have hnot (a b : V) (ha : Nonempty (@_root_.Quiver.Hom V q a b)) :
      Nonempty (@_root_.Quiver.Hom V q' a b) := by
    by_contra hb
    have : (a, b) ∈ flipSet q q' := mem_flipSet.mpr ⟨ha, not_nonempty_iff.mp hb⟩
    simp [hempty] at this
  -- an arrow `a ⟶ b` of `q'` is not an arrow `b ⟶ a` of `q`, since `q'` would then have both
  have hiff :
      Nonempty (@_root_.Quiver.Hom V q a b) ↔ Nonempty (@_root_.Quiver.Hom V q' a b) := by
    refine ⟨hnot a b, fun ⟨y⟩ ↦ ?_⟩
    by_contra ha
    obtain ⟨x⟩ | ⟨x⟩ := (h a b).some.symm (Sum.inl y)
    · exact ha ⟨x⟩
    · obtain ⟨y'⟩ := hnot b a ⟨x⟩
      exact Sum.inl_ne_inr ((hsub' a b).elim (Sum.inl y) (Sum.inr y'))
  have : Subsingleton (@_root_.Quiver.Hom V q' a b) :=
    ⟨fun x y ↦ Sum.inl_injective ((hsub' a b).elim (Sum.inl x) (Sum.inl y))⟩
  have : Subsingleton (@_root_.Quiver.Hom V q a b) :=
    ⟨fun x y ↦ Sum.inl_injective ((hsub a b).elim (Sum.inl x) (Sum.inl y))⟩
  exact ⟨equivOfSubsingletonOfSubsingleton (fun x ↦ (hiff.mp ⟨x⟩).some)
    fun y ↦ (hiff.mpr ⟨y⟩).some⟩

/-- **Any two orientations of a finite forest are related by reflections at sinks.** Let `q` be a
quiver on a finite vertex type with at most one arrow between any two vertices, counted in both
directions, whose underlying graph is acyclic. If a second quiver `q'` has the same arrows joining
any two vertices, in either direction, then reflecting `q` along some sink-admissible list of
vertices produces a quiver whose arrows are those of `q'`. -/
theorem _root_.Quiver.exists_isSinkAdmissible_reflectList_equiv [Finite V]
    (q q' : _root_.Quiver.{v} V)
    (hsub : ∀ a b : V,
      Subsingleton (@_root_.Quiver.Hom V q a b ⊕ @_root_.Quiver.Hom V q b a))
    (hG : (@underlyingGraph V q).IsAcyclic)
    (h : ∀ a b : V, Nonempty ((@_root_.Quiver.Hom V q a b ⊕ @_root_.Quiver.Hom V q b a) ≃
      (@_root_.Quiver.Hom V q' a b ⊕ @_root_.Quiver.Hom V q' b a))) :
    ∃ l : List V, IsSinkAdmissible q l ∧
      ∀ a b : V, Nonempty (@_root_.Quiver.Hom V (reflectList q l) a b ≃
        @_root_.Quiver.Hom V q' a b) := by
  classical
  have : Fintype V := Fintype.ofFinite V
  -- induction on the number of arrows still to be turned around
  induction hn : (flipSet q q').card using Nat.strong_induction_on generalizing q with
  | _ n ih =>
  rcases (flipSet q q').eq_empty_or_nonempty with hempty | ⟨⟨u, w⟩, huw⟩
  · -- nothing to turn around: the arrows of `q` and `q'` agree
    refine ⟨[], isSinkAdmissible_nil q, fun a b ↦ ?_⟩
    rw [reflectList_nil]
    exact nonempty_hom_equiv_of_flipSet_eq_empty hsub h hempty a b
  · -- turn the arrow `u ⟶ w` around, then recurse
    obtain ⟨⟨e⟩, hw⟩ := mem_flipSet.mp huw
    have hacyc : @IsAcyclic V q := @isAcyclic_of_isAcyclic_underlyingGraph V q
      (fun a b f ↦ ⟨fun g ↦ Sum.inl_ne_inr ((hsub a b).elim (Sum.inl f) (Sum.inr g))⟩) hG
    obtain ⟨l₁, hl₁, hempty₁, hsame⟩ := @exists_isSinkAdmissible_flip V _ q hacyc hG u w e
    let q₁ := reflectList q l₁
    have hmulti (a b : V) := nonempty_reflectList_sum_hom_equiv q l₁ a b
    have hsub₁ (a b : V) :
        Subsingleton (@_root_.Quiver.Hom V q₁ a b ⊕ @_root_.Quiver.Hom V q₁ b a) :=
      have := hsub a b
      (hmulti a b).some.subsingleton
    have hG₁ : (@underlyingGraph V q₁).IsAcyclic := by
      rwa [underlyingGraph_congr fun a b ↦ (hmulti a b).some.nonempty_congr]
    have h₁ (a b : V) : Nonempty ((@_root_.Quiver.Hom V q₁ a b ⊕ @_root_.Quiver.Hom V q₁ b a) ≃
        (@_root_.Quiver.Hom V q' a b ⊕ @_root_.Quiver.Hom V q' b a)) :=
      ⟨(hmulti a b).some.trans (h a b).some⟩
    -- `q'` has the arrow `w ⟶ u`, which `q₁` now has too
    have hw' : Nonempty (@_root_.Quiver.Hom V q' w u) := by
      obtain ⟨x⟩ | ⟨x⟩ := (h u w).some (Sum.inl e)
      · exact (hw.false x).elim
      · exact ⟨x⟩
    have hlt : (flipSet q₁ q').card < n := by
      rw [← hn]
      refine (Finset.card_le_card fun p hp ↦ ?_).trans_lt (Finset.card_erase_lt_of_mem huw)
      obtain ⟨a, b⟩ := p
      obtain ⟨ha, hb⟩ := mem_flipSet.mp hp
      by_cases hab : s(a, b) = s(u, w)
      · rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact (not_nonempty_iff.mpr hempty₁ ha).elim
        · exact (not_nonempty_iff.mpr hb hw').elim
      · refine Finset.mem_erase.mpr ⟨fun hp' ↦ hab ?_, mem_flipSet.mpr ⟨(hsame a b hab).mp ha, hb⟩⟩
        simp only [Prod.mk.injEq] at hp'
        rw [hp'.1, hp'.2]
    obtain ⟨l₂, hl₂, hequiv⟩ := ih _ hlt q₁ hsub₁ hG₁ h₁ rfl
    exact ⟨l₁ ++ l₂, isSinkAdmissible_append.mpr ⟨hl₁, hl₂⟩, by rwa [reflectList_append]⟩

end Quiver

end TauCeti
