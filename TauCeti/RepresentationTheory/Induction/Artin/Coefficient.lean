/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import TauCeti.GroupTheory.SpecificGroups.Cyclic.Moebius
import Mathlib.Data.SetLike.Fintype

/-!
# The Artin coefficient and Artin's identity for fixed points

Artin's induction theorem rests on one identity of integers. For a finite group `G` let

`m_C = ∑_{D cyclic, C ≤ D} μ ([D : C])`

be the **Artin coefficient** of a subgroup `C`, the Möbius sum over the cyclic subgroups above `C`;
it vanishes unless `C` is itself cyclic, since a subgroup of a cyclic group is cyclic. The identity
is then

`∑_C m_C · |C| · #(G/C)^g = |G|` for every `g : G`,

with `#(G/C)^g` the number of cosets fixed by `g` acting on `G ⧸ C`.

Two steps prove it. First, `|C| · #(G/C)^g` counts the elements `x : G` with `x⁻¹ g x ∈ C`: those
are exactly the elements whose coset is fixed, and the quotient map is `|C|`-to-one
(`QuotientGroup.preimageMkEquivSubgroupProdSet`). Second, exchanging the two sums leaves
`∑_x ∑_{C ∋ x⁻¹ g x} m_C`, and the inner sum is `1` for every element: expanding `m_C` and
exchanging once more turns it into a sum over the cyclic subgroups `D` of a Möbius sum over the
subgroups between `⟨y⟩` and `D`, which is `1` exactly for `D = ⟨y⟩`
(`TauCeti.sum_moebius_relIndex_of_le`).

The identity is stated in `ℤ`, not in a field: its consumer is Artin's theorem in the Grothendieck
group `G₀(k[G])` of modular representations, where the coefficients are genuine integers and the
fixed-point counts are the permutation classes, so reducing them into a field of coefficients
would lose the statement.

`TauCeti.sum_artinCoeff_mem_eq_one`, the pointwise identity, is also what the
characteristic-zero Artin theorem of
`TauCeti/RepresentationTheory/Induction/Artin/Basic.lean` runs on, read in the coefficient field
of the class functions.

## Main definitions

* `TauCeti.artinCoeff`: the Artin coefficient `m_C` of a subgroup.

## Main statements

* `TauCeti.artinCoeff_eq_zero_of_not_isCyclic`: the coefficient vanishes off the cyclic subgroups.
* `TauCeti.sum_artinCoeff_mem_eq_one`: **the pointwise identity**, `∑_{C ∋ y} m_C = 1`.
* `TauCeti.natCard_mul_natCard_fixedBy_quotient`: `|C| · #(G/C)^g` is the number of `x` with
  `x⁻¹ g x ∈ C`.
* `TauCeti.sum_artinCoeff_mul_card_fixedBy`: **Artin's identity for fixed points**,
  `∑_C m_C · |C| · #(G/C)^g = |G|`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Section 9.2,
  Theorem 17.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (7.3.4).
-/

public section

namespace TauCeti

open ArithmeticFunction MulAction

variable {G : Type*} [Group G] [Finite G]

/-- **The Artin coefficient** of a subgroup `C` of a finite group: the Möbius sum
`∑_{D cyclic, C ≤ D} μ ([D : C])` over the cyclic subgroups above `C`, with `[D : C]` the relative
index `Subgroup.relIndex C D`.

It is `0` unless `C` is cyclic (`TauCeti.artinCoeff_eq_zero_of_not_isCyclic`), and it is the
coefficient with which `C` enters Artin's identity
(`TauCeti.sum_artinCoeff_mul_card_fixedBy`). -/
noncomputable def artinCoeff (C : Subgroup G) : ℤ :=
  ∑ᶠ (D : Subgroup G) (_ : IsCyclic D ∧ C ≤ D), moebius (C.relIndex D)

omit [Finite G] in
/-- **The Artin coefficient is supported on the cyclic subgroups.** A subgroup of a cyclic group is
cyclic, so a non-cyclic `C` lies below no cyclic subgroup and its Möbius sum is empty. -/
theorem artinCoeff_eq_zero_of_not_isCyclic {C : Subgroup G} (hC : ¬ IsCyclic C) :
    artinCoeff C = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun D => ?_
  have hempty : IsEmpty (IsCyclic D ∧ C ≤ D) :=
    ⟨fun h => hC (have _ : IsCyclic D := h.1; Subgroup.isCyclic_of_le h.2)⟩
  exact finsum_of_isEmpty _

open scoped Classical in
/-- **The pointwise Artin identity.** For every element `y` of a finite group the Artin
coefficients of the subgroups containing `y` sum to `1`.

Expanding the coefficient and exchanging the two sums leaves, for each cyclic subgroup `D`, the
Möbius sum over the subgroups between `⟨y⟩` and `D`, which is `1` exactly when `D = ⟨y⟩`; and
`⟨y⟩` is cyclic, so exactly one term survives. -/
theorem sum_artinCoeff_mem_eq_one (y : G) :
    ∑ᶠ (C : Subgroup G) (_ : y ∈ C), artinCoeff C = 1 := by
  have _ : Fintype G := Fintype.ofFinite G
  rw [finsum_cond_eq_sum_of_cond_iff (t := Finset.univ.filter fun C : Subgroup G => y ∈ C) _
    fun _ => by simp]
  have hexp : ∀ C ∈ Finset.univ.filter (fun C : Subgroup G => y ∈ C), artinCoeff C =
      ∑ D ∈ Finset.univ.filter (fun D : Subgroup G => IsCyclic D ∧ C ≤ D),
        moebius (C.relIndex D) := fun C _ => by
    rw [artinCoeff, finsum_cond_eq_sum_of_cond_iff
      (t := Finset.univ.filter fun D : Subgroup G => IsCyclic D ∧ C ≤ D) _ fun _ => by simp]
  rw [Finset.sum_congr rfl hexp,
    Finset.sum_comm' (t' := Finset.univ.filter (fun D : Subgroup G => IsCyclic D))
      (s' := fun D => Finset.univ.filter (fun C : Subgroup G => y ∈ C ∧ C ≤ D))
      (by intro C D; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto)]
  have hinner : ∀ D ∈ Finset.univ.filter (fun D : Subgroup G => IsCyclic D),
      ∑ C ∈ Finset.univ.filter (fun C : Subgroup G => y ∈ C ∧ C ≤ D), moebius (C.relIndex D) =
        if Subgroup.zpowers y = D then 1 else 0 := by
    intro D hD
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD
    have _ : IsCyclic D := hD
    have hfil : Finset.univ.filter (fun C : Subgroup G => y ∈ C ∧ C ≤ D) =
        Finset.univ.filter (fun C : Subgroup G => Subgroup.zpowers y ≤ C ∧ C ≤ D) := by
      ext C
      simp [Subgroup.zpowers_le]
    by_cases hyD : y ∈ D
    · have key := sum_moebius_relIndex_of_le (D := D) (H := Subgroup.zpowers y)
        (Subgroup.zpowers_le.mpr hyD)
      rw [finsum_cond_eq_sum_of_cond_iff
        (t := Finset.univ.filter fun C : Subgroup G => Subgroup.zpowers y ≤ C ∧ C ≤ D) _
        fun _ => by simp] at key
      rw [hfil, key]
    · have hne : Subgroup.zpowers y ≠ D := fun h => hyD (h ▸ Subgroup.mem_zpowers y)
      rw [ite_eq_right hne]
      refine Finset.sum_eq_zero fun C hC => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
      exact absurd (hC.2 hC.1) hyD
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq]
  simp [Subgroup.isCyclic_zpowers]

omit [Finite G] in
/-- **The fixed cosets, counted in the group.** For a subgroup `C` of a finite group, the number of
cosets in `G ⧸ C` fixed by `g`, times `|C|`, is the number of elements `x` with `x⁻¹ g x ∈ C`: the
coset of `x` is fixed exactly under that condition, and the quotient map is `|C|`-to-one. -/
theorem natCard_mul_natCard_fixedBy_quotient (C : Subgroup G) (g : G) :
    Nat.card C * Nat.card (fixedBy (G ⧸ C) g) = Nat.card {x : G // x⁻¹ * g * x ∈ C} := by
  have hset : (QuotientGroup.mk ⁻¹' fixedBy (G ⧸ C) g) = {x : G | x⁻¹ * g * x ∈ C} := by
    ext x
    simp only [Set.mem_preimage, mem_fixedBy, Set.mem_ofPred_eq]
    rw [show g • (x : G ⧸ C) = ((g * x : G) : G ⧸ C) from rfl, QuotientGroup.eq,
      ← Subgroup.inv_mem_iff]
    constructor
    · intro h; simpa [mul_assoc] using h
    · intro h; simpa [mul_assoc] using h
  rw [← Nat.card_prod, ← Nat.card_congr
    (QuotientGroup.preimageMkEquivSubgroupProdSet C (fixedBy (G ⧸ C) g)), hset]
  rfl

open scoped Classical in
/-- **Artin's identity for fixed points.** For every element `g` of a finite group,
`∑_C m_C · |C| · #(G/C)^g = |G|`, the sum over all subgroups of the Artin coefficient times the
order of the subgroup times the number of cosets fixed by `g`.

This is the arithmetic core of Artin's induction theorem, stated in `ℤ` and with no coefficient
field in sight: the weight `|C| · #(G/C)^g` counts the conjugates of `g` landing in `C`
(`TauCeti.natCard_mul_natCard_fixedBy_quotient`), so exchanging the sums reduces the identity to
the pointwise one, `TauCeti.sum_artinCoeff_mem_eq_one`. -/
theorem sum_artinCoeff_mul_card_fixedBy (g : G) :
    ∑ᶠ C : Subgroup G, artinCoeff C * Nat.card C * Nat.card (fixedBy (G ⧸ C) g) =
      (Nat.card G : ℤ) := by
  have _ : Fintype G := Fintype.ofFinite G
  rw [finsum_eq_sum_of_fintype]
  have hterm : ∀ C : Subgroup G,
      artinCoeff C * Nat.card C * Nat.card (fixedBy (G ⧸ C) g) =
        ∑ x : G, if x⁻¹ * g * x ∈ C then artinCoeff C else 0 := by
    intro C
    rw [mul_assoc, ← Nat.cast_mul, natCard_mul_natCard_fixedBy_quotient C g,
      Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.sum_boole,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by split <;> simp
  rw [Finset.sum_congr rfl fun C _ => hterm C, Finset.sum_comm]
  have hx : ∀ x : G, (∑ C : Subgroup G, if x⁻¹ * g * x ∈ C then artinCoeff C else 0) = 1 := by
    intro x
    rw [← Finset.sum_filter]
    have key := sum_artinCoeff_mem_eq_one (x⁻¹ * g * x)
    rwa [finsum_cond_eq_sum_of_cond_iff
      (t := Finset.univ.filter fun C : Subgroup G => x⁻¹ * g * x ∈ C) _ fun _ => by simp] at key
  rw [Finset.sum_congr rfl fun x _ => hx x]
  simp [Nat.card_eq_fintype_card]

end TauCeti
