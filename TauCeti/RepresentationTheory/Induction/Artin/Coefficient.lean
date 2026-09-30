/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.QuotientGroup.Basic
public import TauCeti.GroupTheory.SpecificGroups.Cyclic.Moebius

/-!
# The Artin coefficient and Artin's identity for fixed points

Artin's induction theorem for a finite group `G` rests on one identity among permutation
characters: weighting the coset space `G ⧸ C` by `m_C · |C|`, where

`m_C = ∑_{C ≤ D, D cyclic} μ([D : C])`

is the **Artin coefficient** of `C`, the number of fixed points of any `g : G` adds up to `|G|`.
This file defines `m_C` and proves that identity in `ℤ`, where it says

`∑_C m_C · |C| · #(G ⧸ C)^g = |G|`.

Only cyclic subgroups carry a nonzero coefficient, because a subgroup of a cyclic group is cyclic.

The identity is a statement about `G`-sets rather than about representations: the coefficients are
integers and the fixed-point counts are natural numbers, so it can be transported to any
coefficient ring. Read in a field it gives Artin's induction theorem for class functions, in
`TauCeti.RepresentationTheory.Induction.Artin.Basic`.

## Main definitions

* `Subgroup.artinCoeff`: the Artin coefficient `m_C` of a subgroup.

## Main results

* `Subgroup.artinCoeff_eq_zero_of_not_isCyclic`: a non-cyclic subgroup has coefficient `0`.
* `TauCeti.sum_artinCoeff_of_mem_eq_one`: the Artin coefficients of the subgroups containing a
  fixed element sum to `1`.
* `TauCeti.sum_artinCoeff_mul_card_fixedBy`: **Artin's identity for fixed points**,
  `∑_C m_C · |C| · #(G ⧸ C)^g = |G|`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Section 9.2,
  Theorem 17.
-/

public section

open ArithmeticFunction MulAction

namespace Subgroup

variable {G : Type*} [Group G]

/-- **The Artin coefficient** of a subgroup `C`, the sum of `μ([D : C])` over the cyclic subgroups
`D` containing `C`. It vanishes unless `C` is cyclic. -/
noncomputable def artinCoeff (C : Subgroup G) : ℤ :=
  ∑ᶠ (D : Subgroup G) (_ : IsCyclic D ∧ C ≤ D), moebius (C.relIndex D)

/-- The defining formula for the Artin coefficient. -/
theorem artinCoeff_def (C : Subgroup G) :
    C.artinCoeff = ∑ᶠ (D : Subgroup G) (_ : IsCyclic D ∧ C ≤ D), moebius (C.relIndex D) := (rfl)

/-- A subgroup that is not cyclic has Artin coefficient `0`: no cyclic subgroup contains it. -/
@[simp]
theorem artinCoeff_eq_zero_of_not_isCyclic {C : Subgroup G} (h : ¬ IsCyclic C) :
    C.artinCoeff = 0 := by
  refine finsum_eq_zero_of_forall_eq_zero fun D => ?_
  by_cases hD : IsCyclic D ∧ C ≤ D
  · have := hD.1
    exact absurd (Subgroup.isCyclic_of_le hD.2) h
  · simp [finsum_eq_if, hD]

end Subgroup

namespace TauCeti

variable {G : Type*} [Group G]

/-- **The Artin coefficients of the subgroups containing a fixed element sum to `1`.** This is the
pointwise content of Artin's identity: it is the fibrewise statement that
`TauCeti.sum_artinCoeff_mul_card_fixedBy` integrates over `G`. -/
theorem sum_artinCoeff_of_mem_eq_one [Finite G] (y : G) :
    ∑ᶠ (C : Subgroup G) (_ : y ∈ C), C.artinCoeff = 1 := by
  classical
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  -- Exchanging the two sums leaves, for each cyclic `D` containing `y`, the Möbius sum over the
  -- interval between `⟨y⟩` and `D`, which vanishes unless `D = ⟨y⟩`.
  have h1 : ∑ᶠ (C : Subgroup G) (_ : y ∈ C), C.artinCoeff
      = ∑ C ∈ Finset.univ.filter (fun C : Subgroup G => y ∈ C), C.artinCoeff :=
    finsum_cond_eq_sum_of_cond_iff _ (by simp)
  have h2 : ∀ C : Subgroup G, C.artinCoeff
      = ∑ D ∈ Finset.univ.filter (fun D : Subgroup G => IsCyclic D ∧ C ≤ D),
          moebius (C.relIndex D) := fun C => finsum_cond_eq_sum_of_cond_iff _ (by simp)
  rw [h1]
  simp_rw [h2]
  rw [Finset.sum_comm' (t' := Finset.univ.filter (fun D : Subgroup G => IsCyclic D ∧ y ∈ D))
      (s' := fun D => Finset.univ.filter (fun C : Subgroup G => y ∈ C ∧ C ≤ D))
      (by intro C D; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto)]
  have hinner : ∀ D ∈ Finset.univ.filter (fun D : Subgroup G => IsCyclic D ∧ y ∈ D),
      ∑ C ∈ Finset.univ.filter (fun C : Subgroup G => y ∈ C ∧ C ≤ D), moebius (C.relIndex D)
        = if Subgroup.zpowers y = D then 1 else 0 := by
    intro D hD
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD
    have := hD.1
    have hle : Subgroup.zpowers y ≤ D := Subgroup.zpowers_le.mpr hD.2
    have hconv : ∑ C ∈ Finset.univ.filter (fun C : Subgroup G => y ∈ C ∧ C ≤ D),
          moebius (C.relIndex D)
        = ∑ᶠ (C : Subgroup G) (_ : Subgroup.zpowers y ≤ C ∧ C ≤ D), moebius (C.relIndex D) := by
      refine (finsum_cond_eq_sum_of_cond_iff _ ?_).symm
      intro C _
      simp [Subgroup.zpowers_le]
    rw [hconv, IsCyclic.sum_moebius_relIndex hle]
  have hmem : Subgroup.zpowers y ∈
      Finset.univ.filter (fun D : Subgroup G => IsCyclic D ∧ y ∈ D) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Subgroup.isCyclic_zpowers y, Subgroup.mem_zpowers y⟩
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq]
  simp [hmem]

/-- **Artin's identity for fixed points.** For every `g : G`, the fixed-point counts of the coset
spaces `G ⧸ C`, weighted by `m_C · |C|`, add up to `|G|`.

The identity holds in `ℤ`, before any choice of coefficient ring: both the Artin coefficients and
the fixed-point counts are integers. -/
theorem sum_artinCoeff_mul_card_fixedBy [Finite G] (g : G) :
    ∑ᶠ C : Subgroup G, C.artinCoeff * Nat.card C * Nat.card (fixedBy (G ⧸ C) g) =
      (Nat.card G : ℤ) := by
  classical
  have : Fintype G := Fintype.ofFinite _
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  -- `|C| · #(G ⧸ C)^g` counts the `x : G` with `x⁻¹gx ∈ C`, so the weighted sum becomes a sum
  -- over `G` of the coefficients of the subgroups containing `x⁻¹gx`.
  have step : ∀ C : Subgroup G,
      C.artinCoeff * Nat.card C * Nat.card (fixedBy (G ⧸ C) g)
        = ∑ x : G, if x⁻¹ * g * x ∈ C then C.artinCoeff else 0 := by
    intro C
    have hc : (Nat.card {x : G | x⁻¹ * g * x ∈ C} : ℤ)
        = ∑ x : G, if x⁻¹ * g * x ∈ C then (1 : ℤ) else 0 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
      push_cast
      rfl
    rw [mul_assoc, ← Nat.cast_mul, ← C.card_conj_mem_eq_card_mul_card_fixedBy g, hc,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by split <;> simp
  rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl (fun C _ => step C), Finset.sum_comm]
  have hinner : ∀ x : G, ∑ C : Subgroup G, (if x⁻¹ * g * x ∈ C then C.artinCoeff else 0) = 1 := by
    intro x
    have hcv : ∑ᶠ (C : Subgroup G) (_ : x⁻¹ * g * x ∈ C), C.artinCoeff
        = ∑ C ∈ Finset.univ.filter (fun C : Subgroup G => x⁻¹ * g * x ∈ C), C.artinCoeff :=
      finsum_cond_eq_sum_of_cond_iff _ (by simp)
    rw [← Finset.sum_filter, ← hcv]
    exact sum_artinCoeff_of_mem_eq_one _
  rw [Finset.sum_congr rfl (fun x _ => hinner x)]
  simp [Nat.card_eq_fintype_card]

end TauCeti
