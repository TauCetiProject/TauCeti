/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Möbius sums over the subgroup lattice of a cyclic group

The subgroups of a finite cyclic group `A` containing a fixed subgroup `H` are in bijection with
the divisors of `H.index`, the bijection sending a subgroup to its index. Summing the Möbius
function of the index over those subgroups therefore computes `∑_{d ∣ [A : H]} μ(d)`, which is `1`
when `H = ⊤` and `0` otherwise.

Both the version with `A` itself cyclic and the version for an interval `H ≤ C ≤ D` below a cyclic
subgroup `D` of an ambient group are recorded; the latter is the form in which the coefficients of
Artin's induction theorem are summed, where the ambient group is arbitrary and only the subgroups
carrying a nonzero coefficient are cyclic.

## Main results

* `IsCyclic.sum_moebius_index`: in a finite cyclic group, `∑_{H ≤ C} μ([A : C])` is `1` if `H = ⊤`
  and `0` otherwise.
* `IsCyclic.sum_moebius_relIndex`: the same sum over the interval `H ≤ C ≤ D` below a cyclic
  subgroup `D`, with the relative index `[D : C]`.
-/

public section

open ArithmeticFunction

namespace IsCyclic

variable {A : Type*} [Group A] [Finite A] [IsCyclic A]

open scoped Classical in
/-- **Möbius sum over the subgroups of a cyclic group above a fixed subgroup.** In a finite cyclic
group, the Möbius function of the index, summed over the subgroups containing `H`, is `1` when
`H = ⊤` and `0` otherwise. -/
theorem sum_moebius_index (H : Subgroup A) :
    ∑ᶠ (C : Subgroup A) (_ : H ≤ C), moebius C.index = if H = ⊤ then 1 else 0 := by
  classical
  have : Fintype (Subgroup A) := Fintype.ofFinite _
  -- The subgroups above `H` have indices exactly the divisors of `H.index`, each occurring once.
  have key : ∑ C ∈ Finset.univ.filter (fun C : Subgroup A => H ≤ C), moebius C.index
      = ∑ e ∈ H.index.divisors, moebius e := by
    refine Finset.sum_bij (fun C _ => C.index) ?_ ?_ ?_ (fun _ _ => rfl)
    · intro C hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
      exact Nat.mem_divisors.mpr ⟨IsCyclic.subgroup_le_iff_index_dvd.mp hC,
        Subgroup.index_ne_zero_of_finite⟩
    · exact fun C₁ _ C₂ _ h => IsCyclic.subgroup_eq_iff_index_eq.mpr h
    · intro e he
      obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp he
      obtain ⟨C, hC, -⟩ := Group.IsNilpotent.exists_normal_index_eq_of_dvd_card
        (G := A) (hdvd.trans H.index_dvd_card)
      refine ⟨C, ?_, hC⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact IsCyclic.subgroup_le_iff_index_dvd.mpr (hC ▸ hdvd)
  rw [finsum_cond_eq_sum_of_cond_iff _
      (t := Finset.univ.filter (fun C : Subgroup A => H ≤ C)) (by simp), key,
    ← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]
  simp [Subgroup.index_eq_one]

open scoped Classical in
/-- **Möbius sum over an interval below a cyclic subgroup.** For `H ≤ D` with `D` cyclic, the
Möbius function of the relative index `[D : C]`, summed over the subgroups `C` of the ambient group
between `H` and `D`, is `1` when `H = D` and `0` otherwise. -/
theorem sum_moebius_relIndex {G : Type*} [Group G] [Finite G] {H D : Subgroup G} [IsCyclic D]
    (hHD : H ≤ D) :
    ∑ᶠ (C : Subgroup G) (_ : H ≤ C ∧ C ≤ D), moebius (C.relIndex D) =
      if H = D then 1 else 0 := by
  classical
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  have : Fintype (Subgroup D) := Fintype.ofFinite _
  -- The subgroups of `G` between `H` and `D` are the subgroups of `↥D` above `H.subgroupOf D`,
  -- and the relative index `[D : C]` is the index of `C.subgroupOf D` in `↥D` by definition.
  have key : ∑ C ∈ Finset.univ.filter (fun C : Subgroup G => H ≤ C ∧ C ≤ D),
        moebius (C.relIndex D)
      = ∑ C' ∈ Finset.univ.filter (fun C' : Subgroup D => H.subgroupOf D ≤ C'),
        moebius C'.index := by
    refine Finset.sum_nbij' (fun C => C.subgroupOf D) (fun C' => C'.map D.subtype)
      ?_ ?_ ?_ ?_ (fun _ _ => rfl)
    · intro C hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
      exact Subgroup.subgroupOf_mono D hC.1
    · intro C' hC'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC' ⊢
      refine ⟨?_, Subgroup.map_subtype_le C'⟩
      calc H = (H.subgroupOf D).map D.subtype := (Subgroup.map_subgroupOf_eq_of_le hHD).symm
        _ ≤ C'.map D.subtype := Subgroup.map_mono hC'
    · intro C hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC
      exact Subgroup.map_subgroupOf_eq_of_le hC.2
    · intro C' _
      rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective D.subtype_injective]
  have key' : ∑ᶠ (C' : Subgroup D) (_ : H.subgroupOf D ≤ C'), moebius C'.index
      = ∑ C' ∈ Finset.univ.filter (fun C' : Subgroup D => H.subgroupOf D ≤ C'),
        moebius C'.index :=
    finsum_cond_eq_sum_of_cond_iff _ (by simp)
  rw [finsum_cond_eq_sum_of_cond_iff _
      (t := Finset.univ.filter (fun C : Subgroup G => H ≤ C ∧ C ≤ D)) (by simp), key, ← key',
    sum_moebius_index]
  have hiff : (H.subgroupOf D = ⊤) ↔ (H = D) := by
    rw [Subgroup.subgroupOf_eq_top]
    exact ⟨fun h => le_antisymm hHD h, fun h => h ▸ le_rfl⟩
  simp only [hiff]

end IsCyclic
