/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Set.Basic
import Mathlib.Data.Finsupp.Order
import Mathlib.Order.Lattice.Nat

/-!
# Multiplicities of lowest-exponent theta couplings

A family selects one coupling per source, each uniquely of lowest exponent at its partner.
`TauCeti.IsCouplingFamily.eq_mapDomain_iff` characterizes the only multiplicities with the
prescribed partner degrees and at most the selected total source degree. This is the
degree comparison for the extremal coefficient in `New.IsCouplingFamily.norm_coeff_pairExponent`
in `grh/src/New/Derivatives/Sharpness/Couplings.lean` of
[grh-lean](https://github.com/lsernau/grh-lean) at revision `72fead1).
The proof uses `Finsupp.sum_mapDomain_index` to sum the degrees by their partners.
-/

public section

open Finsupp Function Set

namespace TauCeti

/-- Each selected exponent is admissible and its coupling is the unique one of lowest
exponent among the admissible couplings with the same partner. To restrict the source
places, take `ι` to be the subtype of those places. -/
structure IsCouplingFamily {ι κ : Type*} (S : Set ℕ) (pr : ℕ → ι → κ) (e : ι → ℕ) : Prop where
  /-- Each selected exponent belongs to the admissible set. -/
  mem (i : ι) : e i ∈ S
  /-- No other coupling to the selected partner has as small an exponent. -/
  eq_of_exponent_le {i j : ι} {k : ℕ} (hk : k ∈ S) (hle : k ≤ e i)
    (hpr : pr k j = pr (e i) i) : (j, k) = (i, e i)

variable {ι κ : Type*} {S : Set ℕ} {pr : ℕ → ι → κ} {e : ι → ℕ}

namespace IsCouplingFamily

/-- Distinct selected couplings have distinct partners. -/
theorem injective_partner (h : IsCouplingFamily S pr e) :
    Injective (fun i ↦ pr (e i) i) := by
  intro i j hij
  rcases le_total (e i) (e j) with hle | hle
  · exact congrArg Prod.fst (h.eq_of_exponent_le (h.mem i) hle hij)
  · exact (congrArg Prod.fst (h.eq_of_exponent_le (h.mem j) hle hij.symm)).symm

/-- At each selected partner, the selected exponent is the least admissible exponent of a
coupling to that partner. -/
theorem isLeast_partner_exponents (h : IsCouplingFamily S pr e) (i : ι) :
    IsLeast {k | k ∈ S ∧ ∃ j, pr k j = pr (e i) i} (e i) := by
  refine ⟨⟨h.mem i, i, rfl⟩, ?_⟩
  rintro k ⟨hk, j, hj⟩
  by_contra! hlt
  exact hlt.ne (congrArg Prod.snd (h.eq_of_exponent_le hk hlt.le hj))

/-- At fixed partner degrees, a source-degree bound by the selected couplings rules out
every unselected coupling from the support of the multiplicities. -/
theorem support_subset_range_of_sum_pow_mul_le (h : IsCouplingFamily S pr e)
    {p : ℕ} (hp : 1 < p) {m : (ι × ℕ) →₀ ℕ} {j : ι →₀ ℕ}
    (hm : ∀ a ∈ m.support, a.2 ∈ S)
    (hpartner : m.mapDomain (fun a ↦ pr a.2 a.1) = j.mapDomain (fun i ↦ pr (e i) i))
    (hdegree : m.sum (fun a n ↦ p ^ a.2 * n) ≤ j.sum (fun i n ↦ p ^ e i * n)) :
    (m.support : Set (ι × ℕ)) ⊆ range (fun i ↦ (i, e i)) := by
  classical
  let f (a : ι × ℕ) := pr a.2 a.1
  let g (i : ι) := pr (e i) i
  let u (b : κ) := sInf {k | k ∈ S ∧ ∃ i, pr k i = b}
  have hu (i : ι) : u (g i) = e i := (h.isLeast_partner_exponents i).csInf_eq
  have hle (a : ι × ℕ) (ha : a ∈ m.support) : u (f a) ≤ a.2 :=
    csInf_le' ⟨hm a ha, a.1, rfl⟩
  have hfg : m.mapDomain f = j.mapDomain g := hpartner
  have hsum : m.sum (fun a n ↦ p ^ u (f a) * n) = j.sum (fun i n ↦ p ^ e i * n) := by
    have he := congrArg (fun v : κ →₀ ℕ ↦ v.sum fun b n ↦ p ^ u b * n) hfg
    simpa only [sum_mapDomain_index (fun b ↦ mul_zero (p ^ u b))
      (fun b x y ↦ mul_add (p ^ u b) x y), hu] using he
  -- An unselected active coupling would strictly increase the total source degree.
  intro a ha
  have ham : a ∈ m.support := Finset.mem_coe.mp ha
  have hnonneg : 0 ≤ m := Finsupp.le_def.mpr fun _ ↦ Nat.zero_le _
  have hb : f a ∈ (m.mapDomain f).support := by
    rw [support_mapDomain_of_nonneg hnonneg]
    exact Finset.mem_image_of_mem f ham
  rw [hfg, mapDomain_support_of_injective h.injective_partner] at hb
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hb
  have ha' : a.2 ≤ e i := by
    by_contra! hlt
    have hltsum := Finset.sum_lt_sum
      (fun b hb ↦ Nat.mul_le_mul_right (m b)
        (Nat.pow_le_pow_right (zero_lt_one.trans hp) (hle b hb)))
      ⟨a, ham, Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right hp (by rwa [← hi, hu]))
        (Nat.pos_of_ne_zero (mem_support_iff.mp ham))⟩
    exact (ne_of_gt (lt_of_lt_of_le hltsum hdegree)) hsum.symm
  exact ⟨i, (h.eq_of_exponent_le (hm a ham) ha' hi.symm).symm⟩

/-- An assignment of multiplicities using admissible exponents with the prescribed partner
degrees and with total source degree at most the selected one must use the selected couplings.
A coupling with exponent `k` contributes `p ^ k` per copy to the source degree. -/
theorem eq_mapDomain_of_sum_pow_mul_le (h : IsCouplingFamily S pr e) {p : ℕ} (hp : 1 < p)
    {m : (ι × ℕ) →₀ ℕ} {j : ι →₀ ℕ} (hm : ∀ a ∈ m.support, a.2 ∈ S)
    (hpartner : m.mapDomain (fun a ↦ pr a.2 a.1) = j.mapDomain (fun i ↦ pr (e i) i))
    (hdegree : m.sum (fun a n ↦ p ^ a.2 * n) ≤ j.sum (fun i n ↦ p ^ e i * n)) :
    m = j.mapDomain (fun i ↦ (i, e i)) := by
  classical
  let f (a : ι × ℕ) := pr a.2 a.1
  let r (i : ι) := (i, e i)
  have hsupport := h.support_subset_range_of_sum_pow_mul_le hp hm hpartner hdegree
  have hf : InjOn f (range r) := by
    rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩ hij
    exact congrArg r (h.injective_partner hij)
  refine mapDomain_injOn (range r) hf hsupport ?_ ?_
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp (mapDomain_support ha)
    exact mem_range_self i
  · rw [← mapDomain_fun_comp]
    exact hpartner

/-- The selected couplings realize the partner degrees at their minimum total source degree,
and these constraints characterize their multiplicities. -/
theorem eq_mapDomain_iff (h : IsCouplingFamily S pr e) {p : ℕ} (hp : 1 < p)
    {m : (ι × ℕ) →₀ ℕ} {j : ι →₀ ℕ} :
    m = j.mapDomain (fun i ↦ (i, e i)) ↔
      (∀ a ∈ m.support, a.2 ∈ S) ∧
        m.mapDomain (fun a ↦ pr a.2 a.1) = j.mapDomain (fun i ↦ pr (e i) i) ∧
        m.sum (fun a n ↦ p ^ a.2 * n) ≤ j.sum (fun i n ↦ p ^ e i * n) := by
  classical
  refine ⟨?_, fun ⟨hm, ht, hd⟩ ↦ h.eq_mapDomain_of_sum_pow_mul_le hp hm ht hd⟩
  rintro rfl
  have hr : Injective (fun i ↦ (i, e i)) := fun _ _ h ↦ congrArg Prod.fst h
  rw [mapDomain_support_of_injective hr, ← mapDomain_fun_comp]
  rw [sum_mapDomain_index (fun _ ↦ mul_zero _) (fun _ _ _ ↦ mul_add _ _ _)]
  refine ⟨fun a ha ↦ ?_, rfl, le_rfl⟩
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  exact h.mem i

end IsCouplingFamily

end TauCeti
