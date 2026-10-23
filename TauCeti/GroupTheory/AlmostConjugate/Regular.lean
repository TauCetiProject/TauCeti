/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Finite
public import Mathlib.Data.ZMod.Defs
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import TauCeti.GroupTheory.AlmostConjugate
public import TauCeti.GroupTheory.GroupAction.Orbit.CycleType
import Mathlib.NumberTheory.Divisors

/-!
# Almost-conjugate regular permutation groups

By Cayley's theorem a finite group `G` is a permutation group through its left-regular action
`MulAction.toPermHom G G`. Numbering the elements of `G` by a finite set `α`, along `e : G ≃ α`,
makes it the subgroup `(e.permCongrHom.toMonoidHom.comp (toPermHom G G)).range` of
`Equiv.Perm α`. Left multiplication by an element of order `d` is a product of `|G| / d` disjoint
`d`-cycles (`MulAction.fullCycleType_toPerm_of_isCancelSMul`), so the cycle types occurring in this
subgroup, with their multiplicities, are determined by how many elements of each order `G` has.
Since two permutations are conjugate exactly when they have the same cycle type, two groups with
equally many elements of each order have almost-conjugate regular permutation groups, by
`Subgroup.almostConjugate_iff_forall_natCard_cycleType_eq`. If one group is abelian and the other
is not, the two permutation groups are not isomorphic, so not conjugate either.

An instance in degree `16`: `C₄ × C₄` and `Q₈ × C₂` (here
`Multiplicative (ZMod 4) × Multiplicative (ZMod 4)` and
`QuaternionGroup 2 × Multiplicative (ZMod 2)`) both have one element of order `1`, three of
order `2` and twelve of order `4`. Their regular permutation groups in `Equiv.Perm (Fin 16)` are a
pair of almost-conjugate subgroups that are not conjugate, the group-theoretic input from which
Gassmann's method builds arithmetically equivalent, non-isomorphic number fields.

The full cycle types in both groups are `1^16`, `2^8` and `4^4`, with multiplicities `1`, `3` and
`12`. The raw `Equiv.Perm.cycleType` omits fixed points, so for the identity it is the empty
multiset rather than `1^16`, and for the other elements it is `2^8` and `4^4`.

## Main statements

* `Subgroup.almostConjugate_range_permCongrHom_comp_toPermHom`: two finite groups with equally many
  elements of each order have almost-conjugate regular permutation groups.
* `TauCeti.Gassmann.almostConjugate_regular_pair`: the regular permutation groups of
  `C₄ × C₄` and `Q₈ × C₂` are almost conjugate.
* `TauCeti.Gassmann.not_conj_regular_pair`: they are not conjugate.
* `TauCeti.Gassmann.exists_S16_gassmann_pair`: there are two almost-conjugate subgroups of order
  `16` of `Equiv.Perm (Fin 16)` that are not conjugate.

## References

* F. Gassmann, *Bemerkungen zur vorstehenden Arbeit von Hurwitz*, Math. Z. **25** (1926), 665–675.
* R. Perlis, *On the equation `ζ_K(s) = ζ_K'(s)`*, J. Number Theory **9** (1977), 342–360.
-/

public section

open Equiv MulAction

namespace Subgroup

variable {G H α : Type*} [Group G] [Group H]

section Fintype

variable [Fintype α] [DecidableEq α]

/-- The cycle type of left multiplication by `g`, with `G` numbered by `e`, is determined by the
order of `g`. -/
private theorem cycleType_permCongr_toPerm (e : G ≃ α) (g : G) :
    (e.permCongr (toPerm g)).cycleType =
      (Multiset.replicate (Fintype.card α / orderOf g) (orderOf g)).filter (2 ≤ ·) := by
  classical
  have := Fintype.ofEquiv α e.symm
  rw [Perm.cycleType_permCongr, ← Perm.filter_fullCycleType_eq_cycleType,
    fullCycleType_toPerm_of_isCancelSMul, Fintype.card_congr e]

/-- The permutations of cycle type `m` in the regular permutation group of `G` correspond to the
elements of `G` whose order gives that cycle type. -/
private theorem natCard_cycleType_eq_and_mem_range (e : G ≃ α) (m : Multiset ℕ) :
    Nat.card {σ : Perm α // σ.cycleType = m ∧
        σ ∈ (e.permCongrHom.toMonoidHom.comp (toPermHom G G)).range} =
      Nat.card {g : G //
        (Multiset.replicate (Fintype.card α / orderOf g) (orderOf g)).filter (2 ≤ ·) = m} := by
  have hinj : Function.Injective (e.permCongrHom.toMonoidHom.comp (toPermHom G G)) :=
    e.permCongrHom.injective.comp toPerm_injective
  let f : {g : G // (Multiset.replicate (Fintype.card α / orderOf g) (orderOf g)).filter
      (2 ≤ ·) = m} → {σ : Perm α // σ.cycleType = m ∧
        σ ∈ (e.permCongrHom.toMonoidHom.comp (toPermHom G G)).range} :=
    fun g ↦ ⟨e.permCongr (toPerm g.1), by rw [cycleType_permCongr_toPerm, g.2], g.1, rfl⟩
  refine (Nat.card_congr (Equiv.ofBijective f ⟨fun g h hgh ↦ ?_, ?_⟩)).symm
  · exact Subtype.ext (hinj (congrArg Subtype.val hgh))
  · rintro ⟨σ, hσ, g, rfl⟩
    exact ⟨⟨g, (cycleType_permCongr_toPerm e g).symm.trans hσ⟩, rfl⟩

end Fintype

/-- **Groups with the same order statistics have almost-conjugate regular permutation groups.** If
two groups `G` and `H`, both numbered by the same finite set `α`, have equally many elements of
each order, then their left-regular permutation groups in `Equiv.Perm α` are almost conjugate. -/
theorem almostConjugate_range_permCongrHom_comp_toPermHom [Finite α] (eG : G ≃ α) (eH : H ≃ α)
    (h : ∀ d : ℕ, Nat.card {g : G // orderOf g = d} = Nat.card {x : H // orderOf x = d}) :
    (eG.permCongrHom.toMonoidHom.comp (toPermHom G G)).range.AlmostConjugate
      (eH.permCongrHom.toMonoidHom.comp (toPermHom H H)).range := by
  classical
  have := Fintype.ofFinite α
  have := Finite.of_equiv α eG.symm
  have := Finite.of_equiv α eH.symm
  -- An order-preserving bijection `G ≃ H`, glued from bijections between the fibres of `orderOf`.
  let φ : G ≃ H := Equiv.ofFiberEquiv fun d ↦ (Finite.card_eq.mp (h d)).some
  have hφ (g : G) : orderOf (φ g) = orderOf g := Equiv.ofFiberEquiv_map _ g
  rw [almostConjugate_iff_forall_natCard_cycleType_eq]
  intro m
  rw [natCard_cycleType_eq_and_mem_range, natCard_cycleType_eq_and_mem_range]
  exact Nat.card_congr (φ.subtypeEquiv fun g ↦ by rw [hφ])

end Subgroup

namespace TauCeti.Gassmann

/-- In a group of exponent dividing four, every element has order `1`, `2` or `4`. -/
private theorem orderOf_mem_of_forall_pow_four_eq_one {G : Type*} [Group G]
    (h4 : ∀ x : G, x ^ 4 = 1) (x : G) : orderOf x ∈ ({1, 2, 4} : Finset ℕ) := by
  have hdiv : orderOf x ∈ Nat.divisors 4 :=
    Nat.mem_divisors.mpr ⟨orderOf_dvd_of_pow_eq_one (h4 x), by norm_num⟩
  rwa [show Nat.divisors 4 = {1, 2, 4} from rfl] at hdiv

/-- `C₄ × C₄` and `Q₈ × C₂` have equally many elements of each order: one of order `1`, three of
order `2` and twelve of order `4`. -/
private theorem natCard_orderOf_eq (d : ℕ) :
    Nat.card {x : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // orderOf x = d} =
      Nat.card {x : QuaternionGroup 2 × Multiplicative (ZMod 2) // orderOf x = d} := by
  have hA := orderOf_mem_of_forall_pow_four_eq_one
    (G := Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) (by decide)
  have hB := orderOf_mem_of_forall_pow_four_eq_one
    (G := QuaternionGroup 2 × Multiplicative (ZMod 2)) (by decide)
  by_cases hd : d ∈ ({1, 2, 4} : Finset ℕ)
  · -- For the three possible orders, `orderOf_eq_iff` makes both counts decidable.
    have hd0 : 0 < d := by simp at hd; omega
    simp only [orderOf_eq_iff hd0, Nat.card_eq_fintype_card]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl <;> decide
  · have (G : Type) [Group G] (hG : ∀ x : G, orderOf x ∈ ({1, 2, 4} : Finset ℕ)) :
        IsEmpty {x : G // orderOf x = d} := ⟨fun x ↦ hd (x.2 ▸ hG x.1)⟩
    rw [@Nat.card_of_isEmpty _ (this _ hA), @Nat.card_of_isEmpty _ (this _ hB)]

/-- **The regular permutation groups of `C₄ × C₄` and `Q₈ × C₂` are almost conjugate.** Here the
two groups of order `16` are numbered by the same finite set `α`, along `eA` and `eB`. -/
theorem almostConjugate_regular_pair {α : Type*} [Finite α]
    (eA : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃ α)
    (eB : QuaternionGroup 2 × Multiplicative (ZMod 2) ≃ α) :
    (eA.permCongrHom.toMonoidHom.comp
        (toPermHom (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) _)).range.AlmostConjugate
      (eB.permCongrHom.toMonoidHom.comp
        (toPermHom (QuaternionGroup 2 × Multiplicative (ZMod 2)) _)).range :=
  Subgroup.almostConjugate_range_permCongrHom_comp_toPermHom eA eB natCard_orderOf_eq

/-- **The regular permutation groups of `C₄ × C₄` and `Q₈ × C₂` are not conjugate**, however the
two groups are numbered: the first is abelian and the second is not. -/
theorem not_conj_regular_pair {α : Type*}
    (eA : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃ α)
    (eB : QuaternionGroup 2 × Multiplicative (ZMod 2) ≃ α) :
    ¬ ∃ σ : Perm α, (eA.permCongrHom.toMonoidHom.comp
        (toPermHom (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) _)).range.map
          (MulAut.conj σ : Perm α →* Perm α) =
      (eB.permCongrHom.toMonoidHom.comp
        (toPermHom (QuaternionGroup 2 × Multiplicative (ZMod 2)) _)).range := by
  rintro ⟨σ, hσ⟩
  set f := eB.permCongrHom.toMonoidHom.comp
    (toPermHom (QuaternionGroup 2 × Multiplicative (ZMod 2)) _)
  have hf : Function.Injective f := eB.permCongrHom.injective.comp toPerm_injective
  -- A conjugate of the abelian regular image of `C₄ × C₄` is abelian, which forces `Q₈ × C₂` to be.
  have : IsMulCommutative f.range := hσ ▸ inferInstance
  have hcomm (x y : QuaternionGroup 2 × Multiplicative (ZMod 2)) : x * y = y * x :=
    hf (by simpa using congrArg Subtype.val (mul_comm' (⟨f x, x, rfl⟩ : f.range) ⟨f y, y, rfl⟩))
  exact absurd hcomm (by decide)

/-- **A Gassmann pair in `S₁₆`.** The symmetric group on sixteen letters has two subgroups of
order `16` that are almost conjugate but not conjugate: the regular permutation groups of
`C₄ × C₄` and of `Q₈ × C₂`. -/
theorem exists_S16_gassmann_pair :
    ∃ H K : Subgroup (Perm (Fin 16)),
      Nat.card H = 16 ∧ Nat.card K = 16 ∧ H.AlmostConjugate K ∧
        ¬ ∃ σ : Perm (Fin 16), H.map (MulAut.conj σ : Perm (Fin 16) →* Perm (Fin 16)) = K := by
  let eA : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃ Fin 16 :=
    Fintype.equivFinOfCardEq (by simp)
  let eB : QuaternionGroup 2 × Multiplicative (ZMod 2) ≃ Fin 16 :=
    Fintype.equivFinOfCardEq (by simp [QuaternionGroup.card])
  refine ⟨_, _, ?_, ?_, almostConjugate_regular_pair eA eB,
    not_conj_regular_pair eA eB⟩
  · rw [← Nat.card_congr (MonoidHom.ofInjective (eA.permCongrHom.injective.comp
      toPerm_injective)).toEquiv]
    simp
  · rw [← Nat.card_congr (MonoidHom.ofInjective (eB.permCongrHom.injective.comp
      toPerm_injective)).toEquiv]
    simp [QuaternionGroup.card]

end TauCeti.Gassmann
