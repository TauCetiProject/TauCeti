/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import TauCeti.GroupTheory.Sylow.Basic
import Mathlib.Data.Finite.Perm
import Mathlib.Tactic.IntervalCases
import TauCeti.Algebra.Group.Conj
import TauCeti.GroupTheory.SpecificGroups.Dihedral.Basic

/-!
# Nonsplitting conjugacy classes

A conjugacy class `c` of a group `G` is *nonsplitting* if it generates `G` and, for every subgroup
`H`, any two members of `c` lying in `H` are already conjugate in `H`. Since `c` is a whole class of
`G`, the second condition says that `c ∩ H` is either empty or a single conjugacy class of `H`.

This is the hypothesis of the homological stability theorem of Ellenberg, Venkatesh and Westerland
for Hurwitz spaces of branched covers with monodromy in `c`: it is what makes the braid orbits of
`c`-valued tuples generating a fixed subgroup stabilize under concatenation with a member of `c`.
For the transpositions of `S₄`, which are not nonsplitting, the number of these orbits grows with
the length of the tuples.

## Main definitions

* `ConjClasses.IsNonsplitting`: the nonsplitting property of a conjugacy class.

## Main results

* `ConjClasses.IsNonsplitting.carrier_mk_eq_preimage`: for a nonsplitting class `c` and a member
  `g` of `c` lying in `H`, the class of `g` in `H` is `c ∩ H`.
* `ConjClasses.isNonsplitting_iff`: the formulation in which `c ∩ H` is empty or one class of `H`.
* `ConjClasses.IsNonsplitting.isNonsplitting_mk_subgroup`: if `c ∩ H` is nonempty and generates
  `H`, it is a nonsplitting class of `H`.
* `ConjClasses.IsNonsplitting.map_of_surjective`: surjective group homomorphisms preserve the
  property.
* `ConjClasses.isNonsplitting_map_mulEquiv_iff`: group isomorphisms preserve and reflect the
  property.
* `ConjClasses.IsNonsplitting.eq_of_commute`: two commuting members of a nonsplitting class are
  equal.
* `TauCeti.isNonsplitting_mk_iff_of_orderOf_eq_two`: in a group of order not divisible by `4`, in
  particular of order twice an odd number, the class of involutions is nonsplitting exactly when it
  generates the group.
* `TauCeti.isNonsplitting_mk_dihedralSr`: the reflections of a dihedral group of order `2n`, `n`
  odd, form a nonsplitting class.
* `Equiv.Perm.isNonsplitting_mk_swap_iff`: the transpositions of a finite symmetric group form a
  nonsplitting class exactly when there are at most three points.

## References

* J. S. Ellenberg, A. Venkatesh, C. Westerland, *Homological stability for Hurwitz spaces and the
  Cohen–Lenstra conjecture over function fields*, Ann. of Math. 183 (2016), 729–786,
  Definition 3.1 and Lemma 3.2.
-/

public section

namespace ConjClasses

variable {G G' : Type*} [Group G] [Group G'] {c : ConjClasses G}

/-- A conjugacy class `c` of `G` is *nonsplitting* (Ellenberg–Venkatesh–Westerland,
Definition 3.1) if it generates `G` and, for every subgroup `H`, any two members of `c` lying in `H`
are conjugate by an element of `H`. Since `c` is a whole class of `G`, the second condition says
that `c ∩ H` is empty or a single conjugacy class of `H` (`ConjClasses.isNonsplitting_iff`). -/
structure IsNonsplitting (c : ConjClasses G) : Prop where
  /-- A nonsplitting class generates the group. -/
  closure_carrier_eq_top : Subgroup.closure c.carrier = ⊤
  /-- Two members of a nonsplitting class lying in a subgroup `H` are conjugate by an element
  of `H`. -/
  exists_mem_conj_eq {H : Subgroup G} {g h : G} :
    g ∈ c.carrier → h ∈ c.carrier → g ∈ H → h ∈ H → ∃ x ∈ H, x * g * x⁻¹ = h

/-- Two members of a nonsplitting class lying in a subgroup `H` are conjugate in `H`. -/
theorem IsNonsplitting.isConj (hc : c.IsNonsplitting) {H : Subgroup G} {g h : G}
    (hgc : g ∈ c.carrier) (hhc : h ∈ c.carrier) (hgH : g ∈ H) (hhH : h ∈ H) :
    IsConj (⟨g, hgH⟩ : H) ⟨h, hhH⟩ := by
  obtain ⟨x, hxH, hx⟩ := hc.exists_mem_conj_eq hgc hhc hgH hhH
  exact isConj_iff.mpr ⟨⟨x, hxH⟩, Subtype.ext hx⟩

/-- For a member `g` of a nonsplitting class `c` lying in a subgroup `H`, the conjugacy class of
`g` in `H` consists of exactly the members of `c` lying in `H`. -/
theorem IsNonsplitting.carrier_mk_eq_preimage (hc : c.IsNonsplitting) {H : Subgroup G} {g : G}
    (hgc : g ∈ c.carrier) (hgH : g ∈ H) :
    (ConjClasses.mk (⟨g, hgH⟩ : H)).carrier = ((↑) : H → G) ⁻¹' c.carrier := by
  ext x
  rw [mem_carrier_iff_mk_eq, mk_eq_mk_iff_isConj, Set.mem_preimage]
  refine ⟨fun hx => ?_, fun hx => hc.isConj hx hgc x.property hgH⟩
  rw [mem_carrier_iff_mk_eq] at hgc ⊢
  rw [← hgc, mk_eq_mk_iff_isConj]
  simpa using H.subtype.map_isConj hx

/-- **The nonsplitting property as in Ellenberg–Venkatesh–Westerland**: `c` generates `G`, and for
every subgroup `H` the members of `c` lying in `H` form either the empty set or a single conjugacy
class of `H`. -/
theorem isNonsplitting_iff :
    c.IsNonsplitting ↔ Subgroup.closure c.carrier = ⊤ ∧
      ∀ H : Subgroup G, ((↑) : H → G) ⁻¹' c.carrier = ∅ ∨
        ∃ d : ConjClasses H, d.carrier = ((↑) : H → G) ⁻¹' c.carrier := by
  refine ⟨fun hc => ⟨hc.closure_carrier_eq_top, fun H => ?_⟩,
    fun ⟨hgen, hH⟩ => ⟨hgen, fun {H g h} hgc hhc hgH hhH => ?_⟩⟩
  · rcases (((↑) : H → G) ⁻¹' c.carrier).eq_empty_or_nonempty with hempty | ⟨g, hg⟩
    · exact .inl hempty
    · exact .inr ⟨_, hc.carrier_mk_eq_preimage hg g.property⟩
  · rcases hH H with hempty | ⟨d, hd⟩
    · exact absurd hgc (Set.eq_empty_iff_forall_notMem.mp hempty ⟨g, hgH⟩)
    · have hg : (⟨g, hgH⟩ : H) ∈ d.carrier := hd ▸ hgc
      have hh : (⟨h, hhH⟩ : H) ∈ d.carrier := hd ▸ hhc
      rw [mem_carrier_iff_mk_eq] at hg hh
      obtain ⟨x, hx⟩ := isConj_iff.mp (mk_eq_mk_iff_isConj.mp (hg.trans hh.symm))
      exact ⟨x, x.property, congrArg Subtype.val hx⟩

/-- If a nonsplitting class `c` meets a subgroup `H` in a set generating `H`, then the members of
`c` lying in `H` form a nonsplitting class of `H`, the class in `H` of any one of them. -/
theorem IsNonsplitting.isNonsplitting_mk_subgroup (hc : c.IsNonsplitting) {H : Subgroup G}
    {g : G} (hgc : g ∈ c.carrier) (hgH : g ∈ H) (hgen : Subgroup.closure (c.carrier ∩ H) = H) :
    (ConjClasses.mk (⟨g, hgH⟩ : H)).IsNonsplitting := by
  refine ⟨?_, fun {K x y} hx hy hxK hyK => ?_⟩
  · apply Subgroup.map_injective H.subtype_injective
    simp [hc.carrier_mk_eq_preimage hgc hgH, MonoidHom.map_closure,
      Set.image_preimage_eq_inter_range, hgen, ← MonoidHom.range_eq_map]
  · rw [hc.carrier_mk_eq_preimage hgc hgH] at hx hy
    obtain ⟨z, hz, hzxy⟩ := hc.exists_mem_conj_eq hx hy (Subgroup.mem_map_of_mem H.subtype hxK)
      (Subgroup.mem_map_of_mem H.subtype hyK)
    obtain ⟨w, hwK, rfl⟩ := Subgroup.mem_map.mp hz
    exact ⟨w, hwK, Subtype.ext hzxy⟩

/-- A surjective group homomorphism carries a nonsplitting class to a nonsplitting class. In
particular the image of a nonsplitting class in a quotient group is nonsplitting. -/
theorem IsNonsplitting.map_of_surjective (hc : c.IsNonsplitting) {f : G →* G'}
    (hf : Function.Surjective f) : (c.map f).IsNonsplitting := by
  have hcar := carrier_map_of_surjective hf c
  refine ⟨?_, fun {H g h} hg hh hgH hhH => ?_⟩
  · rw [hcar, ← MonoidHom.map_closure, hc.closure_carrier_eq_top,
      Subgroup.map_top_of_surjective _ hf]
  · rw [hcar] at hg hh
    obtain ⟨g₀, hg₀, rfl⟩ := hg
    obtain ⟨h₀, hh₀, rfl⟩ := hh
    obtain ⟨x, hx, rfl⟩ := hc.exists_mem_conj_eq (H := H.comap f) hg₀ hh₀ hgH hhH
    exact ⟨f x, hx, by simp⟩

/-- A class is nonsplitting exactly when its image under a group isomorphism is. -/
@[simp]
theorem isNonsplitting_map_mulEquiv_iff (e : G ≃* G') :
    (c.map (e : G →* G')).IsNonsplitting ↔ c.IsNonsplitting := by
  refine ⟨fun hc => ?_, fun hc => hc.map_of_surjective e.surjective⟩
  convert hc.map_of_surjective (f := (e.symm : G' →* G)) e.symm.surjective
  obtain ⟨g, rfl⟩ := mk_surjective c
  simp

/-- Two commuting members of a nonsplitting class are equal. In particular a nonsplitting class
meets every commutative subgroup in at most one element. -/
theorem IsNonsplitting.eq_of_commute (hc : c.IsNonsplitting) {g h : G} (hg : g ∈ c.carrier)
    (hh : h ∈ c.carrier) (hgh : Commute g h) : g = h := by
  obtain ⟨x, hx, rfl⟩ := hc.exists_mem_conj_eq (H := Subgroup.centralizer {g}) hg hh
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    (Subgroup.mem_centralizer_singleton_iff.mpr hgh.symm.eq)
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  rw [hx, mul_inv_cancel_right]

/-- Every conjugacy class of a trivial group is nonsplitting. -/
theorem isNonsplitting_of_subsingleton [Subsingleton G] (c : ConjClasses G) : c.IsNonsplitting :=
  ⟨Subsingleton.elim _ _, fun {H _ _} _ _ _ _ => ⟨1, one_mem H, Subsingleton.elim _ _⟩⟩

end ConjClasses

namespace TauCeti

variable {G : Type*} [Group G]

/-- **Ellenberg–Venkatesh–Westerland, Lemma 3.2.** In a group whose order is not divisible by `4`,
for instance a finite group of order `2s` with `s` odd, the elements of order `2` form a single
conjugacy class, and this class is nonsplitting exactly when it generates the group. -/
theorem isNonsplitting_mk_iff_of_orderOf_eq_two (h4 : ¬ 4 ∣ Nat.card G) {g : G}
    (hg : orderOf g = 2) :
    (ConjClasses.mk g).IsNonsplitting ↔ Subgroup.closure {x : G | orderOf x = 2} = ⊤ := by
  rw [← carrier_mk_eq_setOf_orderOf_eq_two h4 hg]
  refine ⟨fun hc => hc.closure_carrier_eq_top, fun hgen => ⟨hgen, fun {H x y} hx hy hxH hyH => ?_⟩⟩
  rw [carrier_mk_eq_setOf_orderOf_eq_two h4 hg] at hx hy
  have h4H : ¬ 4 ∣ Nat.card H := fun h => h4 (h.trans (Subgroup.card_subgroup_dvd_card H))
  obtain ⟨z, hz⟩ := isConj_iff.mp <| isConj_of_orderOf_eq_two_of_not_four_dvd h4H
    (g := ⟨x, hxH⟩) (h := ⟨y, hyH⟩) (by rwa [Subgroup.orderOf_mk]) (by rwa [Subgroup.orderOf_mk])
  exact ⟨z, z.property, congrArg Subtype.val hz⟩

/-- The reflections of a dihedral group of order `2n` with `n` odd form a nonsplitting conjugacy
class. For `n = 3` this is the class of transpositions of `S₃`. -/
theorem isNonsplitting_mk_dihedralSr {n : ℕ} (hn : Odd n) (i : ZMod n) :
    (ConjClasses.mk (DihedralGroup.sr i)).IsNonsplitting := by
  have h4 : ¬ 4 ∣ Nat.card (DihedralGroup n) := by
    rw [DihedralGroup.nat_card]
    obtain ⟨k, rfl⟩ := hn
    omega
  refine (isNonsplitting_mk_iff_of_orderOf_eq_two h4 (DihedralGroup.orderOf_sr i)).mpr ?_
  refine eq_top_mono (Subgroup.closure_mono ?_) (closure_range_dihedralSr n)
  rintro _ ⟨j, rfl⟩
  exact DihedralGroup.orderOf_sr j

end TauCeti

namespace Equiv.Perm

variable {α : Type*} [DecidableEq α]

/-- **Transposition classes.** The transpositions of the symmetric group on a finite set `α` form
a nonsplitting conjugacy class exactly when `α` has at most three points. With three points this
is `S₃`, whose order `6` is twice an odd number; with four or more, two disjoint transpositions
commute, which a nonsplitting class forbids. -/
theorem isNonsplitting_mk_swap_iff [Finite α] {a b : α} (hab : a ≠ b) :
    (ConjClasses.mk (swap a b)).IsNonsplitting ↔ Nat.card α ≤ 3 := by
  refine ⟨fun hc => ?_, fun hα => ?_⟩
  · by_contra! hα
    have := Fintype.ofFinite α
    obtain ⟨f⟩ : Nonempty (Fin 4 ↪ α) :=
      Function.Embedding.nonempty_of_card_le <| by
        rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
        omega
    have hmem {x y : α} (hxy : x ≠ y) : swap x y ∈ (ConjClasses.mk (swap a b)).carrier :=
      ConjClasses.mem_carrier_iff_mk_eq.mpr
        (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_swap hxy hab))
    have hne {i j : Fin 4} (hij : i ≠ j) : f i ≠ f j := f.injective.ne hij
    have heq := hc.eq_of_commute (hmem (hne (by decide : (0 : Fin 4) ≠ 1)))
      (hmem (hne (by decide : (2 : Fin 4) ≠ 3)))
      (disjoint_swap_swap (by simp)).commute
    have := congrArg (· (f 0)) heq
    simp only [swap_apply_left] at this
    rw [swap_apply_of_ne_of_ne (hne (by decide)) (hne (by decide))] at this
    exact hne (by decide) this.symm
  · have h4 : ¬ 4 ∣ Nat.card (Perm α) := by
      rw [Nat.card_perm]
      interval_cases Nat.card α <;> decide
    refine (TauCeti.isNonsplitting_mk_iff_of_orderOf_eq_two h4
      (swap_isSwap_iff.mpr hab).orderOf).mpr ?_
    refine eq_top_mono (Subgroup.closure_mono ?_) closure_isSwap
    intro σ hσ
    exact IsSwap.orderOf hσ

end Equiv.Perm
