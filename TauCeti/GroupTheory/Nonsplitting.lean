/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finite.Perm
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import TauCeti.GroupTheory.Sylow.Basic

/-!
# Nonsplitting conjugacy classes

A conjugacy class `c` of a group `G` is *nonsplitting* if it generates `G` and, for every
subgroup `H`, any two elements of `c` lying in `H` are conjugate in `H`. Since `c` is a single
class of `G`, the intersection `c ∩ H` is stable under conjugation by `H`, so the second condition
says that `c ∩ H` is either empty or a single conjugacy class of `H`.

This is the hypothesis of the homological stability theorem of Ellenberg, Venkatesh and
Westerland for Hurwitz spaces of branched covers with monodromy in `c`. For a nonsplitting class,
a tuple of elements of `c` generating a subgroup `H` can be moved by braids so that any prescribed
element of `c ∩ H` appears first, which makes the stabilization by constant blocks eventually
bijective on connected components.

## Main definitions and results

* `ConjClasses.IsNonsplitting`: the nonsplitting property of a conjugacy class.
* `ConjClasses.isNonsplitting_iff`: the equivalent formulation in which every `c ∩ H` is empty or
  a single conjugacy class of `H`.
* `ConjClasses.IsNonsplitting.restrict`: a nonsplitting class restricts to a nonsplitting class of
  every subgroup that its intersection with the subgroup generates.
* `ConjClasses.isNonsplitting_map_iff`: the property is invariant under group isomorphisms.
* `ConjClasses.isNonsplitting_mk_of_orderOf_eq_two`: if `4` does not divide `|G|` and the
  elements of order two generate `G`, they form a nonsplitting class.
* `Equiv.Perm.isNonsplitting_mk_swap` and `Equiv.Perm.not_isNonsplitting_mk_swap`: the
  transpositions of a set with at most three elements form a nonsplitting class, while those of a
  set with at least four elements do not.

## References

* [J. S. Ellenberg, A. Venkatesh and C. Westerland, *Homological stability for Hurwitz spaces
  and the Cohen–Lenstra conjecture over function fields*, Ann. of Math. 183 (2016)],
  Definition 3.1 and Lemma 3.2.
-/

public section

namespace ConjClasses

variable {G G' : Type*} [Group G] [Group G'] {c : ConjClasses G}

/-- A conjugacy class `c` of `G` is *nonsplitting* if it generates `G` and, for every subgroup
`H` of `G`, any two elements of `c` lying in `H` are conjugate in `H`
(Ellenberg–Venkatesh–Westerland, Definition 3.1). -/
structure IsNonsplitting (c : ConjClasses G) : Prop where
  /-- A nonsplitting class generates the group. -/
  closure_carrier_eq_top : Subgroup.closure c.carrier = ⊤
  /-- Two elements of a nonsplitting class lying in a subgroup are conjugate in that subgroup. -/
  isConj (H : Subgroup G) {g h : H} : (g : G) ∈ c.carrier → (h : G) ∈ c.carrier → IsConj g h

/-- The conjugacy class in a subgroup `H` of an element of `c` is contained in `c ∩ H`. -/
theorem carrier_mk_subset_preimage_carrier {H : Subgroup G} {g : H} (hg : (g : G) ∈ c.carrier) :
    (ConjClasses.mk g).carrier ⊆ H.subtype ⁻¹' c.carrier := by
  intro x hx
  have hxg : IsConj (x : G) g :=
    H.subtype.map_isConj (mk_eq_mk_iff_isConj.mp (mem_carrier_iff_mk_eq.mp hx))
  exact mem_carrier_iff_mk_eq.mpr
    ((mk_eq_mk_iff_isConj.mpr hxg).trans (mem_carrier_iff_mk_eq.mp hg))

/-- For a nonsplitting class `c`, the intersection of `c` with a subgroup `H` is the conjugacy
class in `H` of any of its elements. -/
theorem IsNonsplitting.carrier_mk_eq_preimage_carrier (hc : c.IsNonsplitting) {H : Subgroup G}
    {g : H} (hg : (g : G) ∈ c.carrier) :
    (ConjClasses.mk g).carrier = H.subtype ⁻¹' c.carrier :=
  (carrier_mk_subset_preimage_carrier hg).antisymm fun _ hx =>
    mem_carrier_iff_mk_eq.mpr (mk_eq_mk_iff_isConj.mpr (hc.isConj H hx hg))

/-- For a subgroup `H`, two elements of `c` lying in `H` are always conjugate in `H` exactly when
`c ∩ H` is empty or a single conjugacy class of `H`. -/
private theorem forall_isConj_iff (c : ConjClasses G) (H : Subgroup G) :
    (∀ {g h : H}, (g : G) ∈ c.carrier → (h : G) ∈ c.carrier → IsConj g h) ↔
      H.subtype ⁻¹' c.carrier = ∅ ∨ ∃ d : ConjClasses H, d.carrier = H.subtype ⁻¹' c.carrier := by
  constructor
  · intro hc
    refine (Set.eq_empty_or_nonempty _).imp_right fun ⟨g, hg⟩ => ⟨ConjClasses.mk g, ?_⟩
    exact (carrier_mk_subset_preimage_carrier hg).antisymm fun _ hx =>
      mem_carrier_iff_mk_eq.mpr (mk_eq_mk_iff_isConj.mpr (hc hx hg))
  · rintro (hempty | ⟨d, hd⟩) g h hg hh
    · exact absurd (hempty ▸ hg : g ∈ (∅ : Set H)) (Set.notMem_empty g)
    · rw [← mk_eq_mk_iff_isConj, mem_carrier_iff_mk_eq.mp (hd ▸ hg : g ∈ d.carrier),
        mem_carrier_iff_mk_eq.mp (hd ▸ hh : h ∈ d.carrier)]

/-- A conjugacy class is nonsplitting exactly when it generates the group and its intersection
with every subgroup `H` is empty or a single conjugacy class of `H`. -/
theorem isNonsplitting_iff :
    c.IsNonsplitting ↔ Subgroup.closure c.carrier = ⊤ ∧ ∀ H : Subgroup G,
      H.subtype ⁻¹' c.carrier = ∅ ∨ ∃ d : ConjClasses H, d.carrier = H.subtype ⁻¹' c.carrier :=
  ⟨fun hc => ⟨hc.closure_carrier_eq_top, fun H => (forall_isConj_iff c H).mp (hc.isConj H)⟩,
    fun h => ⟨h.1, fun H => (forall_isConj_iff c H).mpr (h.2 H)⟩⟩

/-- If any two elements of `c` lying in a subgroup of `G` are conjugate in it, then the same holds
in `K` for the elements that an injective homomorphism `f : K →* G` sends into `c`. -/
private theorem isConj_of_injective {K : Type*} [Group K]
    (hc : ∀ (H : Subgroup G) {g h : H}, (g : G) ∈ c.carrier → (h : G) ∈ c.carrier → IsConj g h)
    (f : K →* G) (hf : Function.Injective f) (L : Subgroup K) {x y : L}
    (hx : f x ∈ c.carrier) (hy : f y ∈ c.carrier) : IsConj x y := by
  let e := L.equivMapOfInjective f hf
  simpa using (e.symm : L.map f →* L).map_isConj (hc (L.map f) (g := e x) (h := e y) hx hy)

/-- A nonsplitting class restricts to every subgroup `H` that it meets and that its intersection
with `H` generates: there, `c ∩ H` is a nonsplitting class of `H`. -/
theorem IsNonsplitting.restrict (hc : c.IsNonsplitting) {H : Subgroup G} {g : H}
    (hg : (g : G) ∈ c.carrier) (hgen : Subgroup.closure (c.carrier ∩ H) = H) :
    (ConjClasses.mk g).IsNonsplitting := by
  refine ⟨?_, fun L x y hx hy => ?_⟩
  · rw [hc.carrier_mk_eq_preimage_carrier hg, ← Subgroup.map_subtype_inj,
      MonoidHom.map_closure, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, Set.image_preimage_eq_inter_range, Subgroup.coe_subtype,
      Subtype.range_coe_subtype, SetLike.setOfPred_mem_eq, hgen]
  · exact isConj_of_injective hc.isConj H.subtype H.subtype_injective L
      (carrier_mk_subset_preimage_carrier hg hx) (carrier_mk_subset_preimage_carrier hg hy)

/-- A group isomorphism carries a nonsplitting class to a nonsplitting class. -/
theorem IsNonsplitting.map (hc : c.IsNonsplitting) (e : G ≃* G') :
    (c.map (e : G →* G')).IsNonsplitting := by
  obtain ⟨a, rfl⟩ := mk_surjective c
  -- The image of the class of `a` is the class of `e a`, whose members are the images of the
  -- members of the class of `a`.
  have hmem {x : G'} : x ∈ ((ConjClasses.mk a).map (e : G →* G')).carrier ↔
      e.symm x ∈ (ConjClasses.mk a).carrier := by
    -- `ConjClasses.map` computes on a representative by definition.
    change x ∈ (ConjClasses.mk (e a)).carrier ↔ _
    rw [mem_carrier_iff_mk_eq, mem_carrier_iff_mk_eq, mk_eq_mk_iff_isConj, mk_eq_mk_iff_isConj]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · simpa using e.symm.toMonoidHom.map_isConj h
    · simpa using e.toMonoidHom.map_isConj h
  refine ⟨?_, fun H x y hx hy => ?_⟩
  · rw [eq_top_iff, ← Subgroup.map_top_of_surjective e.toMonoidHom e.surjective,
      ← hc.closure_carrier_eq_top, MonoidHom.map_closure]
    exact Subgroup.closure_mono fun _ ⟨z, hz, hzx⟩ => hmem.mpr (by simpa [← hzx] using hz)
  · exact isConj_of_injective hc.isConj e.symm.toMonoidHom e.symm.injective H
      (hmem.mp hx) (hmem.mp hy)

/-- Being nonsplitting is invariant under group isomorphisms. -/
@[simp]
theorem isNonsplitting_map_iff (e : G ≃* G') :
    (c.map (e : G →* G')).IsNonsplitting ↔ c.IsNonsplitting := by
  refine ⟨fun hc => ?_, fun hc => hc.map e⟩
  obtain ⟨a, rfl⟩ := mk_surjective c
  -- `ConjClasses.map` computes on a representative by definition.
  have h : ((ConjClasses.mk a).map (e : G →* G')).map (e.symm : G' →* G) = ConjClasses.mk a :=
    congrArg ConjClasses.mk (e.symm_apply_apply a)
  exact h ▸ hc.map e.symm

/-- If `4` does not divide `|G|`, the conjugacy class of an element of order two consists of all
the elements of order two. -/
theorem carrier_mk_of_orderOf_eq_two (h4 : ¬ 4 ∣ Nat.card G) {g : G} (hg : orderOf g = 2) :
    (ConjClasses.mk g).carrier = {x | orderOf x = 2} := by
  ext x
  rw [mem_carrier_iff_mk_eq, mk_eq_mk_iff_isConj, Set.mem_ofPred_eq]
  refine ⟨fun ⟨u, hu⟩ => (SemiconjBy.orderOf_eq _ hu).trans hg, fun hx => ?_⟩
  exact TauCeti.isConj_of_orderOf_eq_two h4 hx hg

/-- If `|G| = 2s` with `s` odd, the elements of order two form a single conjugacy class. -/
theorem exists_carrier_eq_setOf_orderOf_eq_two (h2 : 2 ∣ Nat.card G) (h4 : ¬ 4 ∣ Nat.card G) :
    ∃ c : ConjClasses G, c.carrier = {x | orderOf x = 2} := by
  have : Finite G := Nat.finite_of_card_ne_zero fun h0 => h4 (h0 ▸ dvd_zero 4)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  exact ⟨ConjClasses.mk g, carrier_mk_of_orderOf_eq_two h4 hg⟩

/-- If `4` does not divide `|G|` and the elements of order two generate `G`, then they form a
nonsplitting conjugacy class (Ellenberg–Venkatesh–Westerland, Lemma 3.2). -/
theorem isNonsplitting_mk_of_orderOf_eq_two (h4 : ¬ 4 ∣ Nat.card G) {g : G} (hg : orderOf g = 2)
    (hgen : Subgroup.closure {x : G | orderOf x = 2} = ⊤) :
    (ConjClasses.mk g).IsNonsplitting := by
  rw [← carrier_mk_of_orderOf_eq_two h4 hg] at hgen
  refine ⟨hgen, fun H x y hx hy => ?_⟩
  rw [carrier_mk_of_orderOf_eq_two h4 hg, Set.mem_ofPred_eq, Subgroup.orderOf_coe] at hx hy
  exact TauCeti.isConj_of_orderOf_eq_two (fun h => h4 (h.trans H.card_subgroup_dvd_card)) hx hy

end ConjClasses

namespace Equiv.Perm

variable {α : Type*} [DecidableEq α]

/-- The transpositions of a finite set with at most three elements form a nonsplitting
conjugacy class; for three elements this is the class of transpositions of `S₃`. -/
theorem isNonsplitting_mk_swap [Finite α] (hα : Nat.card α ≤ 3) {a b : α} (hab : a ≠ b) :
    (ConjClasses.mk (swap a b)).IsNonsplitting := by
  refine ConjClasses.isNonsplitting_mk_of_orderOf_eq_two ?_ (IsSwap.orderOf ⟨a, b, hab, rfl⟩) ?_
  · rw [Nat.card_perm]
    interval_cases Nat.card α <;> decide
  · exact eq_top_iff.mpr (closure_isSwap (α := α) ▸ Subgroup.closure_mono fun σ hσ => hσ.orderOf)

/-- The transpositions of a set with at least four elements do not form a nonsplitting class:
two disjoint transpositions `swap a b` and `swap c d` generate an abelian subgroup in which they are
not conjugate. -/
theorem not_isNonsplitting_mk_swap {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) : ¬ (ConjClasses.mk (swap a b)).IsNonsplitting := by
  intro hc
  have hcomm : Commute (swap a b) (swap c d) := (disjoint_swap_swap (by simp [*])).commute
  let H := Subgroup.closure {swap a b, swap c d}
  have : IsMulCommutative H := Subgroup.isMulCommutative_closure <| by
    simp [Set.pairwise_insert, hcomm, hcomm.symm]
  obtain ⟨u, hu⟩ := hc.isConj H (g := ⟨swap a b, Subgroup.subset_closure (by simp)⟩)
    (h := ⟨swap c d, Subgroup.subset_closure (by simp)⟩) ConjClasses.mem_carrier_mk
    (ConjClasses.mem_carrier_iff_mk_eq.mpr
      (ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_swap hcd hab)))
  -- In the abelian group `H`, conjugate elements are equal.
  have hEq := congrArg Subtype.val (mul_right_cancel ((Std.Commutative.comm _ _).trans hu.eq))
  have hba : b = a := by simpa [swap_apply_of_ne_of_ne hac had] using congrArg (· a) hEq
  exact hab hba.symm

end Equiv.Perm
