/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Regular permutation triples

A connected permutation triple is *regular* when its automorphism group — the simultaneous
centralizer of its components — acts transitively on the sheets. These are the triples of the
regular (Galois, normal) three-point covers: those whose deck group acts transitively on a fiber.

For a connected triple the automorphism group always acts freely on the sheets
(`TauCeti.PermutationTriple.eq_one_of_mem_automorphismGroup_of_apply_eq`), so a regular triple is
one whose automorphism group acts simply transitively. Dually, a triple is regular exactly when
its *monodromy* group acts freely: an element of the monodromy group fixing one sheet fixes every
translate of it by an automorphism, and conversely a free transitive monodromy action on `Fin n`
identifies the sheets with the monodromy group, on which right multiplications are automorphisms.
Counting then turns both characterisations into equalities of orders with the degree.

## Main definitions

* `TauCeti.PermutationTriple.IsRegular`: the triple is connected and its automorphism group is
  transitive on the sheets.

## Main results

* `TauCeti.PermutationTriple.isRegular_iff_isCancelSMul`: a triple is regular exactly when it is
  connected and its monodromy group acts freely on the sheets.
* `TauCeti.PermutationTriple.isRegular_iff_card_monodromyGroup`: a triple is regular exactly when
  it is connected and its monodromy group has order the degree.
* `TauCeti.PermutationTriple.isRegular_iff_card_automorphismGroup`: a triple is regular exactly
  when it is connected and its automorphism group has order the degree.
* `TauCeti.PermutationTriple.isRegular_smul_iff`: regularity is invariant under relabeling.

## References

* E. Girondo, G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins d'Enfants*,
  LMS Student Texts 79, Cambridge University Press, 2012, Definition 2.64 and Proposition 2.66.
-/

public section

namespace TauCeti

open Equiv

namespace PermutationTriple

variable {n : ℕ} {t : PermutationTriple n}

/-- A permutation triple is *regular* when it is connected and its automorphism group acts
transitively on the sheets. The connectedness clause is not redundant: the automorphism group of
the trivial triple is the whole symmetric group, which is transitive in every degree. -/
def IsRegular (t : PermutationTriple n) : Prop :=
  t.IsConnected ∧ MulAction.IsPretransitive t.automorphismGroup (Fin n)

theorem isRegular_iff :
    t.IsRegular ↔ t.IsConnected ∧ MulAction.IsPretransitive t.automorphismGroup (Fin n) :=
  Iff.rfl

theorem IsRegular.isConnected (ht : t.IsRegular) : t.IsConnected := ht.1

theorem IsRegular.isPretransitive (ht : t.IsRegular) :
    MulAction.IsPretransitive t.automorphismGroup (Fin n) := ht.2

/-- Automorphisms of a triple commute with its monodromy. -/
private theorem commute_of_mem {τ g : Perm (Fin n)} (hτ : τ ∈ t.automorphismGroup)
    (hg : g ∈ t.monodromyGroup) : g * τ = τ * g :=
  Subgroup.mem_centralizer_iff.mp (automorphismGroup_eq_centralizer_monodromyGroup (t := t) ▸ hτ)
    g hg

/-- The monodromy group of a regular triple acts freely on the sheets. -/
theorem IsRegular.isCancelSMul (ht : t.IsRegular) : IsCancelSMul t.monodromyGroup (Fin n) := by
  refine isCancelSMul_iff_stabilizer_eq_bot.mpr fun i => ?_
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => Subtype.ext <| Equiv.ext fun j => ?_
  have hgi : (g : Perm (Fin n)) i = i := hg
  obtain ⟨τ, hτ⟩ := ht.isPretransitive.exists_smul_eq i j
  have hτi : (τ : Perm (Fin n)) i = j := hτ
  rw [← hτi, ← Perm.mul_apply, commute_of_mem τ.2 g.2, Perm.mul_apply, hgi]
  rfl

/-- A connected triple whose monodromy group acts freely on the sheets is regular: the
monodromy group is then in bijection with the sheets, and right multiplications are
automorphisms. -/
theorem IsConnected.isRegular [IsCancelSMul t.monodromyGroup (Fin n)] (ht : t.IsConnected) :
    t.IsRegular := by
  refine ⟨ht, ⟨fun i j => ?_⟩⟩
  have := ht.isPretransitive
  -- The orbit map `g ↦ g • k` of a free transitive action is a bijection.
  have hbij : ∀ k : Fin n, Function.Bijective fun g : t.monodromyGroup => g • k := fun k =>
    ⟨fun g h hgh => IsCancelSMul.right_cancel g h k hgh,
      fun l => MulAction.exists_smul_eq t.monodromyGroup k l⟩
  set τ : Perm (Fin n) := (Equiv.ofBijective _ (hbij i)).symm.trans (Equiv.ofBijective _ (hbij j))
  have hτ : ∀ g : t.monodromyGroup, τ (g • i) = g • j := fun g => by
    have hg := (Equiv.ofBijective _ (hbij i)).symm_apply_apply g
    rw [Equiv.ofBijective_apply] at hg
    rw [Equiv.trans_apply, hg, Equiv.ofBijective_apply]
  have hmem : τ ∈ t.automorphismGroup := by
    rw [automorphismGroup_eq_centralizer_monodromyGroup, Subgroup.mem_centralizer_iff]
    intro g hg
    refine Equiv.ext fun k => ?_
    obtain ⟨h, rfl⟩ := (hbij i).2 k
    have hmul : ∀ l : Fin n, g (h • l) = (⟨g, hg⟩ * h : t.monodromyGroup) • l := fun l =>
      (mul_smul (⟨g, hg⟩ : t.monodromyGroup) h l).symm
    simp only [Perm.mul_apply, hτ, hmul]
  refine ⟨⟨τ, hmem⟩, ?_⟩
  simpa using hτ 1

/-- A triple is regular exactly when it is connected and its monodromy group acts freely on the
sheets. -/
theorem isRegular_iff_isCancelSMul :
    t.IsRegular ↔ t.IsConnected ∧ IsCancelSMul t.monodromyGroup (Fin n) :=
  ⟨fun ht => ⟨ht.isConnected, ht.isCancelSMul⟩, fun ⟨ht, _⟩ => ht.isRegular⟩

/-- For a connected triple, the order of the monodromy group is the degree times the order of
any sheet stabilizer. -/
private theorem card_stabilizer_mul (ht : t.IsConnected) (i : Fin n) :
    Nat.card (MulAction.stabilizer t.monodromyGroup i) * n = Nat.card t.monodromyGroup := by
  have := ht.isPretransitive
  rw [← (MulAction.stabilizer t.monodromyGroup i).card_mul_index,
    MulAction.index_stabilizer_of_transitive, Nat.card_eq_fintype_card (α := Fin n),
    Fintype.card_fin]

/-- A triple is regular exactly when it is connected and its monodromy group has order equal to
the degree. -/
theorem isRegular_iff_card_monodromyGroup :
    t.IsRegular ↔ t.IsConnected ∧ Nat.card t.monodromyGroup = n := by
  rw [isRegular_iff_isCancelSMul, isCancelSMul_iff_stabilizer_eq_bot]
  refine and_congr_right fun ht => ?_
  have hn := Nat.pos_of_ne_zero ht.ne_zero
  obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simp_rw [← Subgroup.card_eq_one]
  refine ⟨fun h => by rw [← card_stabilizer_mul ht i, h i, one_mul], fun h j => ?_⟩
  have hj := card_stabilizer_mul ht j
  rw [h] at hj
  exact (Nat.mul_eq_right hn.ne').mp hj

/-- The automorphism group of a connected triple acts freely on the sheets, so its order is the
size of any of its orbits. -/
private theorem card_automorphismGroup_eq_ncard_orbit (ht : t.IsConnected) (i : Fin n) :
    Nat.card t.automorphismGroup = (MulAction.orbit t.automorphismGroup i).ncard := by
  have hbot : MulAction.stabilizer t.automorphismGroup i = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).mpr fun τ hτ => Subtype.ext <|
      eq_one_of_mem_automorphismGroup_of_apply_eq ht.isPretransitive τ.2 hτ
  rw [← (MulAction.stabilizer t.automorphismGroup i).card_mul_index,
    MulAction.index_stabilizer, Subgroup.card_eq_one.mpr hbot, one_mul]

/-- A triple is regular exactly when it is connected and its automorphism group has order equal
to the degree. -/
theorem isRegular_iff_card_automorphismGroup :
    t.IsRegular ↔ t.IsConnected ∧ Nat.card t.automorphismGroup = n := by
  refine and_congr_right fun ht => ⟨fun _ => ?_, fun hcard => ⟨fun i j => ?_⟩⟩
  · obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero ht.ne_zero⟩⟩
    rw [card_automorphismGroup_eq_ncard_orbit ht i, MulAction.orbit_eq_univ, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  · have horbit : MulAction.orbit t.automorphismGroup i = Set.univ := by
      refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_
      rw [Set.ncard_univ, ← card_automorphismGroup_eq_ncard_orbit ht i, hcard,
        Nat.card_eq_fintype_card, Fintype.card_fin]
    exact MulAction.mem_orbit_iff.mp (horbit ▸ Set.mem_univ j)

/-- Regularity only depends on the isomorphism class of a triple. -/
@[simp] theorem isRegular_smul_iff (τ : Perm (Fin n)) (t : PermutationTriple n) :
    (τ • t).IsRegular ↔ t.IsRegular := by
  rw [isRegular_iff_card_monodromyGroup, isRegular_iff_card_monodromyGroup, isConnected_smul_iff,
    monodromyGroup_smul, Subgroup.card_map_of_injective (MulAut.conj τ).injective]

/-- Isomorphic triples are regular together. -/
theorem isRegular_iff_of_equivalent {t t' : PermutationTriple n} (h : Equivalent t t') :
    t.IsRegular ↔ t'.IsRegular := by
  obtain ⟨τ, rfl⟩ := equivalent_iff_exists_smul_eq.mp h
  exact (isRegular_smul_iff τ t).symm

end PermutationTriple

end TauCeti
