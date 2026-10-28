/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import TauCeti.GroupTheory.AlmostConjugate
import TauCeti.GroupTheory.GroupAction.Orbit.CycleType

/-!
# Almost-conjugate regular permutation groups

A finite group `G` embeds in the symmetric group on its own elements through its left-regular
action, and numbering the elements by a finite type `α` (through `e : G ≃ α`) places the image in
`Equiv.Perm α`. Left multiplication by an element of order `d` has `|G| / d` cycles, all of
length `d` (`MulAction.fullCycleType_toPerm_self`). Since two permutations are conjugate exactly
when they have the same cycle lengths, the regular images of two groups of the same order are
almost conjugate exactly when the groups have equally many elements of each order.

This is a source of almost-conjugate subgroups that are not conjugate. Conjugate subgroups are
isomorphic, and the regular image of a group is isomorphic to the group, so two non-isomorphic
groups of the same order with the same order statistics have almost-conjugate but non-conjugate
regular images. The example here uses `C₄ × C₄` and `Q₈ × C₂`, both of order sixteen: each has
one element of order one, three of order two and twelve of order four, so every numbering of
their elements gives almost-conjugate subgroups of the symmetric group on sixteen points. The
first group is commutative and the second is not, so the subgroups are not conjugate.

The left-regular images have full cycle types `1¹⁶`, `2⁸` and `4⁴`, with multiplicities one,
three and twelve. The raw `Equiv.Perm.cycleType` drops fixed points, so it is empty at the
identity; the comparison here uses `Equiv.Perm.fullCycleType`, which keeps them.

## Main statements

* `Subgroup.almostConjugate_map_range_toPermHom_iff`: the left-regular images of two finite groups
  numbered by the same finite type are almost conjugate exactly when the groups have equally many
  elements of each order.
* `TauCeti.almostConjugate_regular_zmodFour_prod_quaternion`: the left-regular images of
  `C₄ × C₄` and `Q₈ × C₂` are almost conjugate.
* `TauCeti.not_exists_map_conj_regular_zmodFour_prod_quaternion`: they are not conjugate.
* `TauCeti.exists_gassmann_pair_perm_fin_sixteen`: the symmetric group on sixteen points has two
  almost-conjugate subgroups that are not conjugate.

## References

* F. Gassmann, *Bemerkungen zur vorstehenden Arbeit von Hurwitz*, Math. Z. **25** (1926), 665–675.
* R. Perlis, *On the equation `ζ_K(s) = ζ_K'(s)`*, J. Number Theory **9** (1977), 342–360.
-/

public section

open Equiv MulAction

namespace Subgroup

variable {G G' α : Type*} [Group G] [Group G']

/-- For a divisor `d` of a nonzero `n`, the cycle pattern `d^(n / d)` determines `d`. -/
private theorem replicate_div_self_eq_iff {n d d' : ℕ} (hn : n ≠ 0) (hd : d ∣ n) :
    Multiset.replicate (n / d) d = Multiset.replicate (n / d') d' ↔ d = d' := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
  have hd0 : n / d ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd)
      (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hn))).ne'
  have hmem : d ∈ Multiset.replicate (n / d') d' := h ▸ Multiset.mem_replicate.mpr ⟨hd0, rfl⟩
  exact (Multiset.mem_replicate.mp hmem).2

/-- The full cycle type of a numbered left translation is determined by the order of the
translating element. -/
private theorem fullCycleType_permCongr_toPerm [Fintype α] [DecidableEq α] (e : G ≃ α) (g : G) :
    (e.permCongr (toPerm g : Perm G)).fullCycleType =
      Multiset.replicate (Fintype.card α / orderOf g) (orderOf g) := by
  classical
  let := Fintype.ofEquiv α e.symm
  rw [Perm.fullCycleType_permCongr, fullCycleType_toPerm_self, Fintype.card_congr e]

/-- The elements of the numbered left-regular image of `G` that are conjugate to `τ` correspond to
the elements of `G` whose cycle pattern `d^(|G| / d)`, for `d` the order, is the full cycle type
of `τ`. -/
private theorem natCard_isConj_mem_map_range_toPermHom [Fintype α] [DecidableEq α] (e : G ≃ α)
    (τ : Perm α) :
    Nat.card {σ : Perm α // IsConj τ σ ∧
        σ ∈ (toPermHom G G).range.map e.permCongrHom.toMonoidHom} =
      Nat.card {g : G // τ.fullCycleType =
        Multiset.replicate (Fintype.card α / orderOf g) (orderOf g)} := by
  have hconj (σ : Perm α) : IsConj τ σ ↔ τ.fullCycleType = σ.fullCycleType := by
    rw [Perm.partition_eq_of_isConj, Perm.fullCycleType_def, Perm.fullCycleType_def,
      Nat.Partition.ext_iff]
  have hinj : Function.Injective fun g : G ↦ e.permCongr (toPerm g : Perm G) :=
    e.permCongr.injective.comp toPerm_injective
  refine Nat.card_congr (Equiv.ofBijective (fun g ↦ ⟨e.permCongr (toPerm g.1 : Perm G),
      (hconj _).mpr (g.2.trans (fullCycleType_permCongr_toPerm e g.1).symm),
      ⟨toPerm g.1, ⟨g.1, rfl⟩, rfl⟩⟩) ⟨fun g h hgh ↦ Subtype.ext (hinj ?_), ?_⟩).symm
  · exact congrArg Subtype.val hgh
  · rintro ⟨σ, hσ, _, ⟨g, rfl⟩, rfl⟩
    refine ⟨⟨g, ?_⟩, rfl⟩
    rw [(hconj _).mp hσ]
    exact fullCycleType_permCongr_toPerm e g

/-- The order of an element of a group numbered by `α` divides the number of points. -/
private theorem orderOf_dvd_card_of_equiv [Fintype α] (e : G ≃ α) (g : G) :
    orderOf g ∣ Fintype.card α := by
  have : Finite G := .of_equiv α e.symm
  simpa [Nat.card_congr e, Nat.card_eq_fintype_card] using _root_.orderOf_dvd_natCard g

/-- If `τ` has the cycle pattern `d^(n / d)` of an element of order `d`, then the elements of
`G` whose cycle pattern is that of `τ` are exactly the elements of order `d`. -/
private theorem natCard_fullCycleType_eq_replicate_eq [Fintype α] [DecidableEq α] (e : G ≃ α)
    {τ : Perm α} {d : ℕ} (hτ : τ.fullCycleType = Multiset.replicate (Fintype.card α / d) d)
    (hd : d ∣ Fintype.card α) :
    Nat.card {g : G // τ.fullCycleType =
        Multiset.replicate (Fintype.card α / orderOf g) (orderOf g)} =
      Nat.card {g : G // orderOf g = d} :=
  Nat.card_congr <| Equiv.subtypeEquivRight fun g ↦ by
    have : Nonempty α := ⟨e g⟩
    rw [hτ, replicate_div_self_eq_iff Fintype.card_ne_zero hd, eq_comm]

/-- **Almost-conjugacy of regular permutation groups.** Number the elements of two finite groups
`G` and `G'` by the same finite type `α`. The images of their left-regular actions in
`Equiv.Perm α` are almost conjugate exactly when `G` and `G'` have equally many elements of each
order. -/
theorem almostConjugate_map_range_toPermHom_iff [Finite α] (e : G ≃ α) (e' : G' ≃ α) :
    ((toPermHom G G).range.map e.permCongrHom.toMonoidHom).AlmostConjugate
        ((toPermHom G' G').range.map e'.permCongrHom.toMonoidHom) ↔
      ∀ d : ℕ, Nat.card {g : G // orderOf g = d} = Nat.card {g : G' // orderOf g = d} := by
  classical
  have : Fintype α := .ofFinite α
  have : Finite G := .of_equiv α e.symm
  have : Finite G' := .of_equiv α e'.symm
  rw [almostConjugate_iff_forall_natCard_isConj]
  simp only [natCard_isConj_mem_map_range_toPermHom]
  constructor
  · intro h d
    by_cases hd : (∃ g : G, orderOf g = d) ∨ ∃ g : G', orderOf g = d
    · -- Some permutation has the cycle pattern `d^(n / d)`, and it detects the elements of
      -- order `d` in each group.
      obtain ⟨τ, hτ, hdn⟩ : ∃ τ : Perm α, τ.fullCycleType =
          Multiset.replicate (Fintype.card α / d) d ∧ d ∣ Fintype.card α := by
        rcases hd with ⟨g, rfl⟩ | ⟨g, rfl⟩
        · exact ⟨_, fullCycleType_permCongr_toPerm e g, orderOf_dvd_card_of_equiv e g⟩
        · exact ⟨_, fullCycleType_permCongr_toPerm e' g, orderOf_dvd_card_of_equiv e' g⟩
      rw [← natCard_fullCycleType_eq_replicate_eq e hτ hdn,
        ← natCard_fullCycleType_eq_replicate_eq e' hτ hdn]
      exact h τ
    · rw [not_or, not_exists, not_exists] at hd
      have : IsEmpty {g : G // orderOf g = d} := ⟨fun g ↦ hd.1 g g.2⟩
      have : IsEmpty {g : G' // orderOf g = d} := ⟨fun g ↦ hd.2 g g.2⟩
      rw [Nat.card_of_isEmpty, Nat.card_of_isEmpty]
  · intro h τ
    -- Match the elements of `G` and `G'` order by order.
    let φ : G ≃ G' := Equiv.ofFiberEquiv fun d ↦ (Finite.card_eq.mp (h d)).some
    exact Nat.card_congr <| φ.subtypeEquiv fun g ↦ by
      rw [Equiv.ofFiberEquiv_map (f := orderOf) (g := orderOf)]

end Subgroup

namespace TauCeti

open Subgroup

/-- In a monoid of exponent dividing four, the order of an element is determined by whether it is
trivial and whether its square is. -/
private theorem orderOf_eq_of_pow_four_eq_one {M : Type*} [Monoid M] [DecidableEq M] {g : M}
    (hg : g ^ 4 = 1) : orderOf g = if g = 1 then 1 else if g ^ 2 = 1 then 2 else 4 := by
  split_ifs with h1 h2
  · simp [h1]
  · exact orderOf_eq_prime_pow (p := 2) (n := 0) (by simpa using h1) (by simpa using h2)
  · exact orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using h2) (by simpa using hg)

/-- In a finite monoid of exponent dividing four, the number of elements of order `d` is the
multiplicity of `d` among the values of the order computed from squares. -/
private theorem natCard_orderOf_eq {M : Type*} [Monoid M] [Fintype M] [DecidableEq M]
    (hM : ∀ g : M, g ^ 4 = 1) (d : ℕ) :
    Nat.card {g : M // orderOf g = d} =
      ((Finset.univ : Finset M).val.map
        fun g ↦ if g = 1 then 1 else if g ^ 2 = 1 then 2 else 4).count d := by
  rw [Multiset.count_map, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp_rw [orderOf_eq_of_pow_four_eq_one (hM _), eq_comm (a := d)]
  rw [Finset.card_def, Finset.filter_val]

/-- `C₄ × C₄` and `Q₈ × C₂` have equally many elements of each order: one of order one, three of
order two and twelve of order four. -/
private theorem natCard_orderOf_zmodFour_prod_eq_quaternion (d : ℕ) :
    Nat.card {g : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) // orderOf g = d} =
      Nat.card {g : QuaternionGroup 2 × Multiplicative (ZMod 2) // orderOf g = d} := by
  rw [natCard_orderOf_eq (by decide), natCard_orderOf_eq (by decide)]
  congr 1
  decide

variable {α : Type*}

/-- **The regular images of `C₄ × C₄` and `Q₈ × C₂` are almost conjugate.** However the elements
of the two groups of order sixteen are numbered by a common type `α`, the images of their
left-regular actions in `Equiv.Perm α` meet every conjugacy class in equally many elements. -/
theorem almostConjugate_regular_zmodFour_prod_quaternion
    (e : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃ α)
    (e' : QuaternionGroup 2 × Multiplicative (ZMod 2) ≃ α) :
    ((toPermHom (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) _).range.map
      e.permCongrHom.toMonoidHom).AlmostConjugate
      ((toPermHom (QuaternionGroup 2 × Multiplicative (ZMod 2)) _).range.map
      e'.permCongrHom.toMonoidHom) :=
  have : Finite α := .of_equiv _ e
  (almostConjugate_map_range_toPermHom_iff e e').mpr natCard_orderOf_zmodFour_prod_eq_quaternion

/-- **The regular images of `C₄ × C₄` and `Q₈ × C₂` are not conjugate.** Conjugation preserves
commutativity of a subgroup; the regular image of `C₄ × C₄` is commutative, while that of
`Q₈ × C₂` is not, because the regular action is faithful and `Q₈ × C₂` is not commutative. -/
theorem not_exists_map_conj_regular_zmodFour_prod_quaternion
    (e : Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃ α)
    (e' : QuaternionGroup 2 × Multiplicative (ZMod 2) ≃ α) :
    ¬ ∃ σ : Perm α,
      ((toPermHom (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)) _).range.map
          e.permCongrHom.toMonoidHom).map (MulAut.conj σ : Perm α →* Perm α) =
        (toPermHom (QuaternionGroup 2 × Multiplicative (ZMod 2)) _).range.map
          e'.permCongrHom.toMonoidHom := by
  rintro ⟨σ, hσ⟩
  simp only [MonoidHom.map_range] at hσ
  set f := e'.permCongrHom.toMonoidHom.comp
    (toPermHom (QuaternionGroup 2 × Multiplicative (ZMod 2)) _)
  have hf : Function.Injective f := e'.permCongr.injective.comp toPerm_injective
  -- The conjugate of a commutative subgroup is commutative.
  have : IsMulCommutative f.range := hσ ▸ inferInstance
  apply (show ¬ ∀ a b : QuaternionGroup 2 × Multiplicative (ZMod 2), a * b = b * a by decide)
  intro a b
  apply hf
  rw [map_mul, map_mul]
  exact setLike_mul_comm (MonoidHom.mem_range.mpr ⟨a, rfl⟩) (MonoidHom.mem_range.mpr ⟨b, rfl⟩)

/-- **A Gassmann pair in the symmetric group on sixteen points.** There are two subgroups of
`Equiv.Perm (Fin 16)` that are almost conjugate but not conjugate: the left-regular images of
`C₄ × C₄` and `Q₈ × C₂`. -/
theorem exists_gassmann_pair_perm_fin_sixteen :
    ∃ H K : Subgroup (Perm (Fin 16)),
      H.AlmostConjugate K ∧
        ¬ ∃ σ : Perm (Fin 16), H.map (MulAut.conj σ : Perm (Fin 16) →* Perm (Fin 16)) = K := by
  obtain ⟨e⟩ : Nonempty (Multiplicative (ZMod 4) × Multiplicative (ZMod 4) ≃ Fin 16) :=
    Fintype.card_eq.mp (by simp)
  obtain ⟨e'⟩ : Nonempty (QuaternionGroup 2 × Multiplicative (ZMod 2) ≃ Fin 16) :=
    Fintype.card_eq.mp (by simp [QuaternionGroup.card])
  exact ⟨_, _, almostConjugate_regular_zmodFour_prod_quaternion e e',
    not_exists_map_conj_regular_zmodFour_prod_quaternion e e'⟩

end TauCeti
