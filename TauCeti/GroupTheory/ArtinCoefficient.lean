/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.SetLike.Fintype

/-!
# The Artin coefficients of a finite group, and Artin's identity for fixed points

Attach to every subgroup `C` of a finite group `G` the integer

`artinCoeff C = ∑_{D cyclic, C ≤ D} μ [D : C]`,

the Möbius function of arithmetic summed over the relative indices of the cyclic subgroups above
`C`. It vanishes unless `C` is cyclic, because a subgroup of a cyclic group is cyclic. These are
the coefficients of **Artin's identity**: for every `g : G`,

`∑_C artinCoeff C * |C| * |(G ⧸ C)^g| = |G|`.

Two inputs carry the proof. The first is combinatorial: for a cyclic subgroup `D` the map
`C ↦ [D : C]` is a bijection from the subgroups between `E` and `D` onto the divisors of `[D : E]`,
so `∑_{E ≤ C ≤ D} μ [D : C]` is `∑_{d ∣ [D : E]} μ d`, which is `1` when `E = D` and `0` otherwise.
Summing that over the cyclic `D` leaves the single term `D = ⟨y⟩`, so the Artin coefficients of the
subgroups containing a fixed element add up to `1` (`TauCeti.sum_artinCoeff_of_mem`). The second is
a count: the preimage in `G` of the `g`-fixed points of `G ⧸ C` is the set of `x` with
`x⁻¹ g x ∈ C`, and it is a union of cosets of `C`, so it has `|C| * |(G ⧸ C)^g|` elements
(`TauCeti.natCard_subgroup_mul_natCard_fixedBy`). Exchanging the two summations then replaces the
inner sum by `1` for each of the `|G|` elements `x`.

The identity is stated over `ℤ` rather than in a coefficient field, so that it can be transferred
to Grothendieck groups of modular representations, where the order of the group need not be
invertible.

`TauCeti.ClassFunction.natCard_nsmul_one_mem_indVirtualCharacters_isCyclic`
(`TauCeti.RepresentationTheory.Induction.Artin.Basic`) proves the same combinatorial input in a
different presentation, with the Möbius function of the incidence algebra of the poset of cyclic
subgroups in place of the arithmetic one, and only in the image of `ℤ` in a field; those private
coefficients are what this file makes public and arithmetic.

## Main declarations

* `TauCeti.artinCoeff`: the Artin coefficient of a subgroup.
* `TauCeti.sum_moebius_relIndex`: the Möbius sum over an interval below a cyclic subgroup.
* `TauCeti.sum_artinCoeff_of_mem`: the Artin coefficients of the subgroups containing an element
  add up to one.
* `TauCeti.natCard_subgroup_mul_natCard_fixedBy`: the coset count behind Artin's identity.
* `TauCeti.sum_artinCoeff_mul_card_fixedBy`: **Artin's identity for fixed points**.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Section 9.2.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Section VII.3.
-/

public section

open scoped ArithmeticFunction.Moebius

namespace TauCeti

/-! ### Möbius sums over the subgroups of a cyclic group -/

open scoped Classical in
/-- In a finite cyclic group the Möbius function of the index, summed over the subgroups above a
fixed subgroup `F₀`, is `1` if `F₀` is everything and `0` otherwise: the subgroups above `F₀` are
indexed by their indices, which run over the divisors of `[K : F₀]`. -/
theorem sum_moebius_index {K : Type*} [Group K] [Finite K] [IsCyclic K] (F₀ : Subgroup K) :
    ∑ᶠ (F : Subgroup K) (_ : F₀ ≤ F), μ F.index = if F₀ = ⊤ then 1 else 0 := by
  classical
  let _ := Fintype.ofFinite (Subgroup K)
  have hstep : ∑ᶠ (F : Subgroup K) (_ : F₀ ≤ F), μ F.index =
      ∑ F ∈ Finset.univ.filter (fun F : Subgroup K => F₀ ≤ F), μ F.index :=
    finsum_cond_eq_sum_of_cond_iff _ (by simp)
  have hexists : ∀ d : ℕ, d ∣ Nat.card K → ∃ F : Subgroup K, F.index = d := by
    intro d hd
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_zpowers_eq_top.mp ‹_›
    refine ⟨Subgroup.zpowers (g ^ (d : ℤ)), ?_⟩
    have horder : orderOf g = Nat.card K := by rw [← Nat.card_zpowers, hg]; simp
    rw [Subgroup.index_zpowers_zpow hg, horder]
    simp [Int.gcd_natCast_natCast, Nat.gcd_eq_left hd]
  have hne : F₀.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmain : ∑ F ∈ Finset.univ.filter (fun F : Subgroup K => F₀ ≤ F), μ F.index =
      ∑ d ∈ (F₀.index).divisors, μ d := by
    refine Finset.sum_bij (fun F _ => F.index) ?_ ?_ ?_ ?_
    · intro F hF
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
      exact Nat.mem_divisors.mpr ⟨IsCyclic.subgroup_le_iff_index_dvd.mp hF, hne⟩
    · intro F₁ _ F₂ _ h
      exact IsCyclic.subgroup_eq_iff_index_eq.mpr h
    · intro d hd
      rw [Nat.mem_divisors] at hd
      obtain ⟨F, hF⟩ := hexists d (hd.1.trans F₀.index_dvd_card)
      refine ⟨F, ?_, hF⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact IsCyclic.subgroup_le_iff_index_dvd.mpr (hF ▸ hd.1)
    · intro F _
      rfl
  rw [hstep, hmain, ← ArithmeticFunction.coe_mul_zeta_apply,
    ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  simp [Subgroup.index_eq_one]

open scoped Classical in
/-- The Möbius function of the relative index in a cyclic subgroup `D`, summed over the subgroups
between `E` and `D`, is `1` if `E = D` and `0` otherwise. This is `TauCeti.sum_moebius_index` read
through the correspondence between the subgroups of `G` lying between `E` and `D` and the
subgroups of `D` above `E ∩ D`. -/
theorem sum_moebius_relIndex {G : Type*} [Group G] [Finite G] {E D : Subgroup G}
    (hD : IsCyclic D) :
    ∑ᶠ (C : Subgroup G) (_ : E ≤ C ∧ C ≤ D), μ (C.relIndex D) = if E = D then 1 else 0 := by
  classical
  let _ := Fintype.ofFinite (Subgroup G)
  let _ := Fintype.ofFinite (Subgroup D)
  by_cases hED : E ≤ D
  · have hstep : ∑ᶠ (C : Subgroup G) (_ : E ≤ C ∧ C ≤ D), μ (C.relIndex D) =
        ∑ C ∈ Finset.univ.filter (fun C : Subgroup G => E ≤ C ∧ C ≤ D), μ (C.relIndex D) :=
      finsum_cond_eq_sum_of_cond_iff _ (by simp)
    have hstep' : ∑ᶠ (F : Subgroup D) (_ : E.subgroupOf D ≤ F), μ F.index =
        ∑ F ∈ Finset.univ.filter (fun F : Subgroup D => E.subgroupOf D ≤ F), μ F.index :=
      finsum_cond_eq_sum_of_cond_iff _ (by simp)
    have hbij : ∑ C ∈ Finset.univ.filter (fun C : Subgroup G => E ≤ C ∧ C ≤ D),
          μ (C.relIndex D) =
        ∑ F ∈ Finset.univ.filter (fun F : Subgroup D => E.subgroupOf D ≤ F), μ F.index := by
      refine Finset.sum_nbij' (fun C => C.subgroupOf D) (fun F => F.map D.subtype) ?_ ?_ ?_ ?_ ?_
      · intro C hC
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
        exact Subgroup.comap_mono hC.1
      · intro F hF
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF ⊢
        refine ⟨?_, Subgroup.map_subtype_le F⟩
        calc E = (E.subgroupOf D).map D.subtype := (Subgroup.map_subgroupOf_eq_of_le hED).symm
          _ ≤ F.map D.subtype := Subgroup.map_mono hF
      · intro C hC
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
        exact Subgroup.map_subgroupOf_eq_of_le hC.2
      · intro F _
        exact Subgroup.comap_map_eq_self_of_injective D.subtype_injective F
      · intro C _
        rfl
    rw [hstep, hbij, ← hstep', sum_moebius_index]
    congr 1
    simp only [eq_iff_iff, Subgroup.subgroupOf_eq_top]
    exact ⟨fun h => le_antisymm hED h, fun h => h.ge⟩
  · have hzero : ∀ C : Subgroup G, ¬ (E ≤ C ∧ C ≤ D) := fun C hC => hED (hC.1.trans hC.2)
    have hne : E ≠ D := fun h => hED h.le
    simp [hzero, hne]

/-! ### The Artin coefficients -/

/-- **The Artin coefficient** of a subgroup `C`, the sum of `μ [D : C]` over the cyclic subgroups
`D` containing `C`. It vanishes unless `C` is cyclic. -/
noncomputable def artinCoeff {G : Type*} [Group G] (C : Subgroup G) : ℤ :=
  ∑ᶠ (D : Subgroup G) (_ : IsCyclic D ∧ C ≤ D), μ (C.relIndex D)

variable {G : Type*} [Group G]

open scoped Classical in
/-- A subgroup of a cyclic group is cyclic, so a noncyclic subgroup lies below no cyclic subgroup
and its Artin coefficient vanishes. -/
theorem artinCoeff_eq_zero_of_not_isCyclic {C : Subgroup G} (hC : ¬ IsCyclic C) :
    artinCoeff C = 0 :=
  finsum_eq_zero_of_forall_eq_zero fun D ↦ by
    rw [finsum_eq_if, ite_eq_right]
    rintro ⟨_, hle⟩
    exact hC (Subgroup.isCyclic_of_le hle)

variable [Finite G]

open scoped Classical in
/-- **The Artin coefficients of the subgroups containing an element add up to one.** Exchanging the
two sums groups the pairs `C ≤ D` by their cyclic upper member `D`; the inner sum is
`TauCeti.sum_moebius_relIndex` for the interval between `⟨y⟩` and `D`, which leaves only the term
`D = ⟨y⟩`. -/
theorem sum_artinCoeff_of_mem (y : G) :
    ∑ᶠ (C : Subgroup G) (_ : y ∈ C), artinCoeff C = 1 := by
  classical
  let _ := Fintype.ofFinite (Subgroup G)
  have houter : ∑ᶠ (C : Subgroup G) (_ : y ∈ C), artinCoeff C =
      ∑ C ∈ Finset.univ.filter (fun C : Subgroup G => y ∈ C), artinCoeff C :=
    finsum_cond_eq_sum_of_cond_iff _ (by simp)
  have hinner : ∀ C : Subgroup G, artinCoeff C =
      ∑ D ∈ Finset.univ.filter (fun D : Subgroup G => IsCyclic D ∧ C ≤ D), μ (C.relIndex D) :=
    fun C ↦ finsum_cond_eq_sum_of_cond_iff _ (by simp)
  rw [houter]
  simp_rw [hinner]
  rw [Finset.sum_comm' (t' := Finset.univ.filter (fun D : Subgroup G => IsCyclic D))
    (s' := fun D => Finset.univ.filter (fun C : Subgroup G => y ∈ C ∧ C ≤ D))]
  · have hslice : ∀ D : Subgroup G, IsCyclic D →
        ∑ C ∈ Finset.univ.filter (fun C : Subgroup G => y ∈ C ∧ C ≤ D), μ (C.relIndex D) =
          if Subgroup.zpowers y = D then 1 else 0 := by
      intro D hD
      rw [← sum_moebius_relIndex (E := Subgroup.zpowers y) hD]
      refine (finsum_cond_eq_sum_of_cond_iff _ ?_).symm
      intro C _
      simp [Subgroup.zpowers_le]
    rw [Finset.sum_congr rfl fun D hD => hslice D (by simpa using hD)]
    simp only [Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and, ite_eq_left_iff,
      zero_ne_one, imp_false, Decidable.not_not]
    exact Subgroup.isCyclic_zpowers y
  · intro C D
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto

/-! ### Artin's identity for fixed points -/

omit [Finite G] in
/-- The elements `x` of `G` with `x⁻¹ g x ∈ C` are the preimage of the `g`-fixed points of `G ⧸ C`,
a union of `|(G ⧸ C)^g|` cosets of `C`. -/
theorem natCard_subgroup_mul_natCard_fixedBy (C : Subgroup G) (g : G) :
    Nat.card C * Nat.card (MulAction.fixedBy (G ⧸ C) g) =
      Nat.card {x : G // x⁻¹ * g * x ∈ C} := by
  have hset : {x : G | x⁻¹ * g * x ∈ C} =
      QuotientGroup.mk ⁻¹' (MulAction.fixedBy (G ⧸ C) g) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, MulAction.mem_fixedBy]
    rw [show g • (QuotientGroup.mk x : G ⧸ C) = QuotientGroup.mk (g * x) from rfl,
      QuotientGroup.eq]
    exact ⟨fun h => by simpa [mul_assoc] using C.inv_mem h,
      fun h => by simpa [mul_assoc] using C.inv_mem h⟩
  rw [show {x : G // x⁻¹ * g * x ∈ C} = ({x : G | x⁻¹ * g * x ∈ C} : Set G) from rfl, hset,
    Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet C _), Nat.card_prod]

open scoped Classical in
/-- **Artin's identity for fixed points**: weighting the permutation character of `G ⧸ C` by
`artinCoeff C * |C|` and summing over all subgroups gives `|G|`, at every `g : G`.

Each summand counts, with the weight `artinCoeff C`, the elements `x` of `G` whose conjugate
`x⁻¹ g x` lies in `C`; exchanging the two sums replaces the inner sum by
`TauCeti.sum_artinCoeff_of_mem` at `x⁻¹ g x`, which is `1`. -/
theorem sum_artinCoeff_mul_card_fixedBy (g : G) :
    ∑ᶠ C : Subgroup G, artinCoeff C * Nat.card C * Nat.card (MulAction.fixedBy (G ⧸ C) g) =
      (Nat.card G : ℤ) := by
  classical
  let _ := Fintype.ofFinite G
  let _ := Fintype.ofFinite (Subgroup G)
  have hcount : ∀ C : Subgroup G,
      (Nat.card C : ℤ) * Nat.card (MulAction.fixedBy (G ⧸ C) g) =
        ∑ x : G, if x⁻¹ * g * x ∈ C then (1 : ℤ) else 0 := by
    intro C
    rw [← Nat.cast_mul, natCard_subgroup_mul_natCard_fixedBy C g]
    rw [Finset.sum_boole]
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [finsum_eq_sum_of_fintype]
  have hrw : ∀ C : Subgroup G,
      artinCoeff C * Nat.card C * Nat.card (MulAction.fixedBy (G ⧸ C) g) =
        ∑ x : G, if x⁻¹ * g * x ∈ C then artinCoeff C else 0 := by
    intro C
    rw [mul_assoc, hcount C, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by split <;> simp
  simp_rw [hrw]
  rw [Finset.sum_comm]
  have hone : ∀ x : G, ∑ C : Subgroup G,
      (if x⁻¹ * g * x ∈ C then artinCoeff C else 0) = 1 := by
    intro x
    rw [← finsum_eq_sum_of_fintype]
    rw [← sum_artinCoeff_of_mem (x⁻¹ * g * x)]
    exact finsum_congr fun C => (finsum_eq_if).symm
  simp_rw [hone]
  simp [Nat.card_eq_fintype_card]

end TauCeti
