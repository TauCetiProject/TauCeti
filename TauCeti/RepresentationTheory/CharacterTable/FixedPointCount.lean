/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.AlmostConjugate
public import TauCeti.RepresentationTheory.CharacterTable.Determined
public import TauCeti.RepresentationTheory.Induction.Permutation

/-!
# Permutation representations in characteristic zero are classified by fixed-point counts

Let `G` be a group acting on finite types `X` and `Y`, and let `k` be a field of
characteristic zero. The character of the permutation representation `k[X]` at `g` is the number
of points of `X` fixed by `g`, cast into `k` (`TauCeti.char_ofMulAction`), and over a field of
characteristic zero a finite-dimensional representation of a finite group is determined by its
character (`Representation.nonempty_equiv_of_character_eq`). The two actions factor through a
finite group, namely the image of `G` in `Perm X × Perm Y`, and the characteristic-zero hypothesis
makes the cast injective, so the two statements combine into an exact criterion:

`k[X] ≃ k[Y]` as representations of `G` **if and only if** `#X^g = #Y^g` for every `g : G`.

Both directions need the characteristic-zero hypothesis, for different reasons. Without it the
fixed-point counts are only visible modulo the characteristic, so an isomorphism says less; and
without it a representation of a finite group is not determined by its character at all.

The criterion is strictly weaker than an equivalence of `G`-sets: an equivariant equivalence
`X ≃ Y` gives an equivalence of permutation representations
(`TauCeti.ofMulActionEquivCongr`), but the converse fails, and the subgroup form below is exactly
where it fails. Taking `X = G ⧸ H` and `Y = G ⧸ K` for subgroups `H` and `K`, the criterion says
that the trivial representations of `H` and of `K` induce to equivalent representations of `G`
precisely when every element of `G` fixes as many cosets of `H` as of `K` — the classical condition
of Gassmann, satisfied by non-conjugate subgroups, so that `G ⧸ H` and `G ⧸ K` need not be
isomorphic `G`-sets. By the fixed-coset identity `Subgroup.natCard_fixedBy_mul_natCard` the
condition says that `H` and `K` are almost conjugate, meeting every conjugacy class of `G` in the
same number of elements (`Subgroup.almostConjugate_iff_forall_natCard_fixedBy_eq`). Nothing about
Gassmann's examples is proved here; what is proved is the criterion they are examples for.

## Main statements

* `TauCeti.natCard_fixedBy_eq_of_nonempty_equiv_ofMulAction`: equivalent permutation representations
  have equal fixed-point counts.
* `TauCeti.nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq`: **the classification** —
  over a field of characteristic zero, two permutation representations of a group on finite sets are
  equivalent exactly when the fixed-point counts of the underlying `G`-sets agree.
* `TauCeti.nonempty_iso_repOfMulAction_iff_forall_natCard_fixedBy_eq`: the same classification,
  read on the objects of `Rep k G`.
* `TauCeti.nonempty_equiv_ind_trivial_iff_forall_natCard_fixedBy_eq`: the subgroup form, for the
  representations induced from the trivial representations of two subgroups.
* `TauCeti.almostConjugate_iff_nonempty_equiv_ofMulAction`: two subgroups are almost conjugate
  exactly when the permutation representations on their coset spaces are equivalent.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Part I, §2.3
  (characters determine representations) and §3.3 (permutation representations).
* F. Gassmann, *Bemerkungen zur vorstehenden Arbeit von Hurwitz*, Math. Z. **25** (1926), 665–675,
  for the subgroup condition the last statement characterizes.
-/

public section

open MulAction Representation

namespace TauCeti

universe u v w

variable (k : Type u) [Field k] {G : Type v} [Group G] [Finite G]

section Classification

variable {X Y : Type w} [MulAction G X] [MulAction G Y] [Finite X] [Finite Y]

omit [Finite G] in
/-- **Equivalent permutation representations have equal fixed-point counts.** Equivalent
representations have equal characters, the character of `k[X]` at `g` is `#X^g` cast into `k`, and
in characteristic zero that cast is injective. -/
theorem natCard_fixedBy_eq_of_nonempty_equiv_ofMulAction [CharZero k]
    (h : Nonempty ((ofMulAction k G X).Equiv (ofMulAction k G Y))) (g : G) :
    Nat.card (fixedBy X g) = Nat.card (fixedBy Y g) := by
  obtain ⟨φ⟩ := h
  have hchar := congrFun (Representation.char_iso φ) g
  rw [char_ofMulAction, char_ofMulAction] at hchar
  exact Nat.cast_injective hchar

omit [Finite G] in
/-- **Permutation representations in characteristic zero are classified by fixed-point counts.**
For a group `G` acting on finite types `X` and `Y` and a field `k` of characteristic zero,
the permutation representations `k[X]` and `k[Y]` are equivalent exactly when `g` fixes as many
points of `X` as of `Y`, for every `g : G`. -/
theorem nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq [CharZero k] :
    Nonempty ((ofMulAction k G X).Equiv (ofMulAction k G Y)) ↔
      ∀ g : G, Nat.card (fixedBy X g) = Nat.card (fixedBy Y g) := by
  refine ⟨fun h g ↦ natCard_fixedBy_eq_of_nonempty_equiv_ofMulAction k h g, fun h ↦ ?_⟩
  -- Backward direction: factor both actions through the finite group `Perm X × Perm Y`, read the
  -- fixed-point counts as permutation characters of the image of `G`, and compare characters there.
  let f : G →* Equiv.Perm X × Equiv.Perm Y :=
    (MulAction.toPermHom G X).prod (MulAction.toPermHom G Y)
  let ρX : Representation k f.range (MonoidAlgebra k X) :=
    (ofMulAction k (Equiv.Perm X) X).comp ((MonoidHom.fst _ _).comp f.range.subtype)
  let ρY : Representation k f.range (MonoidAlgebra k Y) :=
    (ofMulAction k (Equiv.Perm Y) Y).comp ((MonoidHom.snd _ _).comp f.range.subtype)
  have hX : ∀ g, ofMulAction k G X g = ρX (f.rangeRestrict g) := fun g ↦
    MonoidAlgebra.lhom_ext' fun x ↦ LinearMap.ext_ring (by simp [ρX, f])
  have hY : ∀ g, ofMulAction k G Y g = ρY (f.rangeRestrict g) := fun g ↦
    MonoidAlgebra.lhom_ext' fun x ↦ LinearMap.ext_ring (by simp [ρY, f])
  obtain ⟨φ⟩ := Representation.nonempty_equiv_of_character_eq ρX ρY (funext fun q ↦ by
    obtain ⟨g, rfl⟩ := f.rangeRestrict_surjective q
    have hc : (ofMulAction k G X).character g = (ofMulAction k G Y).character g := by
      rw [char_ofMulAction, char_ofMulAction]
      exact congrArg Nat.cast (h g)
    simpa [Representation.character, hX, hY] using hc)
  refine ⟨.mk φ.toLinearEquiv fun g ↦ ?_⟩
  rw [hX, hY]
  exact φ.isIntertwining' _

omit [Finite G] in
/-- **The classification in `Rep k G`.** The permutation representations of two finite `G`-sets are
isomorphic as objects of `Rep k G`, over a field of characteristic zero, exactly when the
fixed-point counts agree. This is
`TauCeti.nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq` read through `Rep.mkIso` and
`Representation.equivOfIso`, which identify the two notions of sameness on the objects
`Rep.of ρ`. -/
theorem nonempty_iso_repOfMulAction_iff_forall_natCard_fixedBy_eq [CharZero k] :
    Nonempty (Rep.ofMulAction k G X ≅ Rep.ofMulAction k G Y) ↔
      ∀ g : G, Nat.card (fixedBy X g) = Nat.card (fixedBy Y g) := by
  rw [← nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq k]
  refine ⟨fun ⟨i⟩ ↦ ⟨?_⟩, fun ⟨e⟩ ↦ ⟨Rep.mkIso e⟩⟩
  have e := Representation.equivOfIso i
  rwa [Rep.of_ρ, Rep.of_ρ] at e

end Classification

section Subgroup

variable (H K : Subgroup G)

omit [Finite G] in
/-- **The subgroup form of the classification.** The trivial representations of two subgroups `H`
and `K` of finite index in a group `G` induce to equivalent representations of `G`, over a field of
characteristic zero, exactly when every `g : G` fixes as many cosets of `H` as of `K`.

The induced representations are the permutation representations on the coset spaces
(`TauCeti.indTrivialEquiv`), so this is
`TauCeti.nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq` at `X = G ⧸ H` and
`Y = G ⧸ K`. -/
theorem nonempty_equiv_ind_trivial_iff_forall_natCard_fixedBy_eq [CharZero k]
    [Finite (G ⧸ H)] [Finite (G ⧸ K)] :
    Nonempty (((Representation.trivial k H k).ind H.subtype).Equiv
        ((Representation.trivial k K k).ind K.subtype)) ↔
      ∀ g : G, Nat.card (fixedBy (G ⧸ H) g) = Nat.card (fixedBy (G ⧸ K) g) := by
  refine Iff.trans ?_
    (nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq (X := G ⧸ H) (Y := G ⧸ K) k)
  exact ⟨fun ⟨φ⟩ ↦ ⟨((indTrivialEquiv k H).symm.trans φ).trans (indTrivialEquiv k K)⟩,
    fun ⟨φ⟩ ↦ ⟨((indTrivialEquiv k H).trans φ).trans (indTrivialEquiv k K).symm⟩⟩

/-- **Almost-conjugate subgroups are those with equivalent permutation representations.** Two
subgroups `H` and `K` of a finite group `G` meet every conjugacy class of `G` in the same number of
elements exactly when, over a field of characteristic zero, the permutation representations
`k[G ⧸ H]` and `k[G ⧸ K]` are equivalent. -/
theorem almostConjugate_iff_nonempty_equiv_ofMulAction [CharZero k] :
    H.AlmostConjugate K ↔
      Nonempty ((ofMulAction k G (G ⧸ H)).Equiv (ofMulAction k G (G ⧸ K))) :=
  -- Almost-conjugacy is equality of the fixed-coset counts, and those counts classify the
  -- permutation representations.
  H.almostConjugate_iff_forall_natCard_fixedBy_eq.trans
    (nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq k).symm

end Subgroup

end TauCeti
