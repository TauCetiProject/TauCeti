/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.Catalan
public import TauCeti.Combinatorics.Enumerative.IncidenceAlgebra
public import TauCeti.Combinatorics.NoncrossingPartition.Interval
public import TauCeti.Combinatorics.NoncrossingPartition.Kreweras
import Mathlib.Algebra.BigOperators.Fin
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.Data.Finset.Basic

/-!
# The Möbius function of the lattice of noncrossing partitions

The free cumulants of a word are obtained from its block moments by Möbius inversion on the
lattice `NC(s)` of noncrossing partitions, so the values of its Möbius function `μ` are the
coefficients expressing cumulants through moments. This file computes the values `μ(0̂, π)`,
identifies `μ(π, 1̂)` with `μ(0̂, Kπ)` using the Kreweras complement, and, factoring every interval
`[σ, π]` over the parts of `π`, computes `μ(σ, π)` on all intervals of `NC(s)` for every finite
set `s` of positions.

First, `μ(0̂, π)` is multiplicative: the lower interval `[0̂, π]` is the product of the lattices
`NC(B)` over the parts `B` of `π`, and accordingly `μ(0̂, π) = ∏_{B ∈ π} μ_{NC(B)}(0̂, 1̂)`.

Second, on the noncrossing partitions of `n` positions, `μ(0̂, 1̂) = (-1)^(n-1) C_(n-1)`, with
`C_k` the Catalan numbers. The proof applies Weisner's theorem to the atom joining the two first
positions `m₁ < m₂`: the noncrossing partitions other than `1̂` whose join with this atom is `1̂`
are exactly the partitions into the positions after `m₁` up to some position `y` and the remaining
positions. Together with multiplicativity this gives the recurrence
`μ_n = -∑_{0 < i < n} μ_i μ_(n-i)`, which is the recurrence of the signed Catalan numbers.

Third, the Kreweras complement `K` reverses the order and maps the upper interval `[π, 1̂]` onto
the lower interval `[0̂, K(π)]`, so `μ(π, 1̂) = μ(0̂, K(π))`. These are the coefficients of the
formula expressing free cumulants through moments.

Finally, every interval `[σ, π]` is the product over the parts `B` of `π` of the upper intervals
`[σ|_B, 1_B]` of `NC(B)`, so `μ(σ, π) = ∏_{B ∈ π} μ_{NC(B)}(σ|_B, 1̂)`, and with the Kreweras
complement on each `NC(B)` this gives a blockwise formula for all values of `μ`. The two directions
of Möbius inversion on `NC(s)` are the general `IncidenceAlgebra.moebius_inversion_bot` and
`IncidenceAlgebra.sum_Iic_sum_Iic_mu_mul`.

## Main results

* `TauCeti.NoncrossingPartition.mu_bot_eq_prod_mu` — `μ(0̂, π) = ∏_{B ∈ π} μ_{NC(B)}(0̂, 1̂)`.
* `TauCeti.NoncrossingPartition.mu_bot_top` — `μ(0̂, 1̂) = (-1)^(|s|-1) C_(|s|-1)` on `NC(s)`, and
  `TauCeti.NoncrossingPartition.mu_bot_top_fin` — `μ(0_n, 1_n) = (-1)^(n-1) C_(n-1)` on `NC(n)`.
* `TauCeti.NoncrossingPartition.mu_top_eq_mu_bot_kreweras` — Kreweras duality of upper and
  lower Möbius intervals.
* `TauCeti.NoncrossingPartition.mu_bot_eq_prod` — the blockwise formula
  `μ(0̂, π) = ∏_{B ∈ π} (-1)^(|B|-1) C_(|B|-1)`.
* `TauCeti.NoncrossingPartition.mu_top_eq_prod_kreweras` —
  `μ(π, 1̂) = ∏_{B ∈ K(π)} (-1)^(|B|-1) C_(|B|-1)`, with `K` the Kreweras complement.
* `TauCeti.NoncrossingPartition.mu_eq_prod_mu_restrict` — for `σ ≤ π`,
  `μ(σ, π) = ∏_{B ∈ π} μ_{NC(B)}(σ|_B, 1̂)`.
* `TauCeti.NoncrossingPartition.mu_eq_prod_prod_kreweras` — for `σ ≤ π`,
  `μ(σ, π) = ∏_{B ∈ π} ∏_{C ∈ K_B(σ|_B)} (-1)^(|C|-1) C_(|C|-1)`.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lectures 9 and 10
  (Proposition 10.15).
* G. Kreweras, *Sur les partitions non croisées d'un cycle*, Discrete Math. 1 (1972), 333–350.
* L. Weisner, *Abstract theory of inversion of finite series*, Trans. Amer. Math. Soc. 38 (1935),
  474–484.
-/

public section

open Finset Finpartition IncidenceAlgebra

namespace TauCeti.NoncrossingPartition

variable {α 𝕜 : Type*} [LinearOrder α] {s : Finset α}

section CommRing

variable [CommRing 𝕜]

/-- *Multiplicativity of the Möbius function* of `NC(s)`: for `σ ≤ π`, `μ(σ, π)` is the product
over the parts `B` of `π` of the values `μ(σ|_B, 1̂)` on the lattices `NC(B)`. This reflects the
factorisation `[σ, π] ≅ ∏_{B ∈ π} [σ|_B, 1_B]` (`TauCeti.NoncrossingPartition.iccOrderIso`). -/
theorem mu_eq_prod_mu_restrict {σ π : NoncrossingPartition s} (h : σ ≤ π) :
    mu 𝕜 σ π = ∏ B : π.val.parts, mu 𝕜 (σ.restrict (π.val.le B.property)) ⊤ := by
  induction σ using WellFoundedGT.induction with
  | _ σ ih =>
  rcases h.eq_or_lt with rfl | hlt
  · rw [mu_self, eq_comm]
    exact prod_eq_one fun B _ => by rw [restrict_of_mem_parts _ B.property, mu_self]
  -- Some part `B` of `π` has `σ|_B ≠ 1_B`, since the restrictions determine `σ ≤ π`.
  obtain ⟨B, hB⟩ : ∃ B : π.val.parts, σ.restrict (π.val.le B.property) ≠ ⊤ := by
    by_contra! H
    refine hlt.ne (congrArg Subtype.val (π.iicOrderIso.injective (a₁ := ⟨σ, h⟩)
      (a₂ := ⟨π, Set.self_mem_Iic⟩) (funext fun B => ?_)))
    rw [iicOrderIso_apply, iicOrderIso_apply, H B, restrict_of_mem_parts _ B.property]
  -- Summing the right-hand side over `[σ, π]` gives `∏_B ∑_{ρ ≥ σ|_B} μ(ρ, 1̂) = 0`.
  have hsum :=
    sum_Icc_prod_restrict_eq_prod_sum h fun B ρ => mu 𝕜 ρ (⊤ : NoncrossingPartition B.val)
  rw [prod_eq_zero (mem_univ B) (by rw [Ici_eq_Icc, sum_Icc_mu_left, ite_eq_right hB]),
    Icc_eq_cons_Ioc h, sum_cons, add_eq_zero_iff_eq_neg] at hsum
  rw [hsum, mu_eq_neg_sum_Ioc_of_ne hlt.ne]
  exact congrArg _ (sum_congr rfl fun τ hτ => ih τ (mem_Ioc.1 hτ).1 (mem_Ioc.1 hτ).2)

/-- *Multiplicativity of the Möbius function* of `NC(s)` on lower intervals: `μ(0̂, π)` is the
product over the parts `B` of `π` of the values `μ(0̂, 1̂)` on the lattices `NC(B)`. -/
theorem mu_bot_eq_prod_mu (π : NoncrossingPartition s) :
    mu 𝕜 ⊥ π = ∏ B ∈ π.val.parts, mu 𝕜 (⊥ : NoncrossingPartition B) ⊤ := by
  rw [mu_eq_prod_mu_restrict bot_le]
  simp only [restrict_bot]
  exact prod_coe_sort _ fun B => mu 𝕜 (⊥ : NoncrossingPartition B) ⊤

section Recurrence

/-! ### The noncrossing partitions joining the two smallest positions with everything -/

variable {m₁ m₂ : α}

variable (hm₁ : m₁ ∈ s) (hm₂ : m₂ ∈ s.erase m₁) {x : NoncrossingPartition s}
  (hx : x.val.part m₁ ∪ x.val.part m₂ = s) (hne : x.val.part m₁ ≠ x.val.part m₂)
include hm₁ hm₂ hx hne

variable (hmin₁ : ∀ z ∈ s, m₁ ≤ z) (hmin₂ : ∀ z ∈ s.erase m₁, m₂ ≤ z)
include hmin₁ hmin₂

/-- Let `m₁ < m₂` be the two first positions of `s`. If the parts of a noncrossing partition
through `m₁` and `m₂` are different and cover `s`, then the part through `m₂` consists of the
positions of `s` other than `m₁` up to its last element. -/
private theorem filter_le_max'_eq_part :
    {z ∈ s.erase m₁ | z ≤ (x.val.part m₂).max' ⟨m₂, x.val.mem_part_self.2 (mem_of_mem_erase hm₂)⟩} =
      x.val.part m₂ := by
  have hm₂s := mem_of_mem_erase hm₂
  have hm₁C : m₁ ∉ x.val.part m₂ := fun h => hne ((x.val.mem_part_iff_part_eq_part hm₁ hm₂s).1 h)
  set y := (x.val.part m₂).max' ⟨m₂, x.val.mem_part_self.2 hm₂s⟩
  have hyC : y ∈ x.val.part m₂ := max'_mem _ _
  have hys : y ∈ s := x.val.part_subset m₂ hyC
  ext z
  simp only [mem_filter, mem_erase]
  refine ⟨fun ⟨⟨hz₁, hzs⟩, hzy⟩ => by_contra fun hzC => ?_,
    fun hz => ⟨⟨fun h => hm₁C (h ▸ hz), x.val.part_subset m₂ hz⟩, le_max' _ _ hz⟩⟩
  -- Otherwise `m₁ < m₂ < z < y` with `m₁, z` in one part and `m₂, y` in another.
  have hzB : z ∈ x.val.part m₁ := (mem_union.1 (hx.symm ▸ hzs)).resolve_right hzC
  have h₁₂ : m₁ < m₂ := (hmin₁ m₂ hm₂s).lt_of_ne (ne_of_mem_erase hm₂).symm
  have h₂z : m₂ < z := (hmin₂ z (mem_erase.2 ⟨hz₁, hzs⟩)).lt_of_ne
    fun h => hzC (h ▸ x.val.mem_part_self.2 hm₂s)
  have hzy' : z < y := hzy.lt_of_ne fun h => hzC (h ▸ hyC)
  exact hne (x.property.part_eq_part hm₁ hm₂s ((x.val.mem_part_iff_part_eq_part hzs hm₁).1 hzB).symm
    ((x.val.mem_part_iff_part_eq_part hys hm₂s).1 hyC).symm h₁₂ h₂z hzy')

omit hm₁ hm₂ hx hne hmin₁ hmin₂ in
/-- The Möbius function at the partition of `s` into the nonempty part `T` and the nonempty rest
`s \ T` is the product of the values on the two lattices of noncrossing partitions. -/
private theorem mu_bot_splitPartition {T : Finset α} (hT : T.Nonempty) (hTs : T ⊆ s)
    (hconv : ∀ a ∈ T, ∀ c ∈ T, ∀ b ∈ s, a < b → b < c → b ∈ T) (hsT : (s \ T).Nonempty) :
    mu 𝕜 ⊥ (⟨splitPartition s T hT hTs, isNoncrossing_splitPartition hconv⟩ :
        NoncrossingPartition s) =
      mu 𝕜 (⊥ : NoncrossingPartition T) ⊤ * mu 𝕜 (⊥ : NoncrossingPartition (s \ T)) ⊤ := by
  rw [mu_bot_eq_prod_mu, parts_splitPartition hsT,
    prod_pair fun h : T = s \ T => ?_]
  obtain ⟨t, ht⟩ := hT
  exact (mem_sdiff.1 (h ▸ ht : t ∈ s \ T)).2 ht

omit hm₁ hm₂ hx hne hmin₁ hmin₂ in
/-- Let `m₁ < m₂` be the two first positions of `s`. Removing the partition into one part, the
noncrossing partitions whose join with the part `{m₁, m₂}` is the partition into one part are the
partitions into the positions of `s` other than `m₁` up to some `y` and the remaining positions;
summing `μ(⊥, x)` over them gives a sum over `y` of products of Möbius functions of smaller
lattices. -/
private theorem sum_erase_top_mu_bot (hpair : {m₁, m₂} ⊆ s) (hmin₁ : ∀ z ∈ s, m₁ ≤ z)
    (hm₂ : m₂ ∈ s.erase m₁) (hmin₂ : ∀ z ∈ s.erase m₁, m₂ ≤ z) :
    ∑ x ∈ ({x | x ⊔ ⟨pairPartition s m₁ m₂ hpair, isNoncrossing_pairPartition hpair⟩ = ⊤} :
        Finset (NoncrossingPartition s)).erase ⊤,
      mu 𝕜 ⊥ x =
    ∑ y ∈ s.erase m₁, mu 𝕜 (⊥ : NoncrossingPartition {z ∈ s.erase m₁ | z ≤ y}) ⊤ *
      mu 𝕜 (⊥ : NoncrossingPartition (s \ {z ∈ s.erase m₁ | z ≤ y})) ⊤ := by
  have hm₁ : m₁ ∈ s := hpair (mem_insert_self _ _)
  have hm₂s := mem_of_mem_erase hm₂
  have hle : m₁ ≤ m₂ := hmin₁ m₂ hm₂s
  have hadj (z : α) (hz : z ∈ s) : z ≤ m₁ ∨ m₂ ≤ z :=
    if h : z = m₁ then Or.inl h.le else Or.inr (hmin₂ z (mem_erase.2 ⟨h, hz⟩))
  have hC {y : α} (hy : y ∈ s.erase m₁) : y ∈ {z ∈ s.erase m₁ | z ≤ y} := mem_filter.2 ⟨hy, le_rfl⟩
  have hm₂C {y : α} (hy : y ∈ s.erase m₁) : m₂ ∈ {z ∈ s.erase m₁ | z ≤ y} :=
    mem_filter.2 ⟨hm₂, hmin₂ y hy⟩
  have hCs (y : α) : {z ∈ s.erase m₁ | z ≤ y} ⊆ s := (filter_subset _ _).trans (erase_subset _ _)
  have hm₁C (y : α) : m₁ ∉ {z ∈ s.erase m₁ | z ≤ y} :=
    fun h => ne_of_mem_erase (mem_filter.1 h).1 rfl
  have hX (x : NoncrossingPartition s) (hx : x ∈ ({x | x ⊔ ⟨pairPartition s m₁ m₂ hpair,
      isNoncrossing_pairPartition hpair⟩ = ⊤} : Finset (NoncrossingPartition s)).erase ⊤) :
      x.val.part m₁ ∪ x.val.part m₂ = s ∧ x.val.part m₁ ≠ x.val.part m₂ :=
    part_union_eq_of_sup_pairPartition_eq_top hpair hle hadj (mem_erase.1 hx).1
      (mem_filter.1 (mem_erase.1 hx).2).2
  -- Biject `y` with the partition splitting off the positions after `m₁` up to `y`; the inverse
  -- sends `x` to the last position of its part through `m₂`.
  symm
  refine sum_bij'
    (fun y hy => ⟨splitPartition s _ (nonempty_of_ne_empty (ne_empty_of_mem (hC hy))) (hCs y),
      isNoncrossing_splitPartition (Finset.convex_filter_erase_le hmin₁ y)⟩)
    (fun x _ => (x.val.part m₂).max' ⟨m₂, x.val.mem_part_self.2 hm₂s⟩)
    (fun y hy => ?_) (fun x hx => ?_) (fun y hy => ?_) (fun x hx => ?_) (fun y hy => ?_)
  · -- The split partition joins with the atom to the top, and is not the top itself.
    exact splitPartition_mem_erase_top_sup_pairPartition hpair _ (hCs y)
      (Finset.convex_filter_erase_le hmin₁ y) (hm₂C hy) (hm₁C y)
  · -- The last position of the part through `m₂` is not `m₁`.
    obtain ⟨_, hne⟩ := hX x hx
    have hmax := max'_mem (x.val.part m₂) ⟨m₂, x.val.mem_part_self.2 hm₂s⟩
    refine mem_erase.2 ⟨fun h => hne ?_, x.val.part_subset m₂ hmax⟩
    exact (x.val.mem_part_iff_part_eq_part hm₁ hm₂s).1 (h ▸ hmax)
  · -- The last position of the split-off part is `y`.
    dsimp only
    simp only [part_splitPartition_of_mem (hm₂C hy)]
    exact le_antisymm (max'_le _ _ _ fun z hz => (mem_filter.1 hz).2) (le_max' _ _ (hC hy))
  · -- A partition `x` is the split at the last position of its part through `m₂`.
    obtain ⟨hu, hne⟩ := hX x hx
    have hCx := filter_le_max'_eq_part hm₁ hm₂ hu hne hmin₁ hmin₂
    refine Subtype.ext (Finpartition.ext_of_part fun z hz => ?_)
    dsimp only
    by_cases hzC : z ∈ x.val.part m₂
    · rw [part_splitPartition_of_mem (hCx.symm ▸ hzC), hCx,
        (x.val.mem_part_iff_part_eq_part hz hm₂s).1 hzC]
    · rw [part_splitPartition_of_notMem hz (hCx.symm ▸ hzC), hCx,
        ← x.val.part_eq_sdiff_part hu hne,
        (x.val.mem_part_iff_part_eq_part hz hm₁).1
          ((mem_union.1 (hu.symm ▸ hz)).resolve_right hzC)]
  · -- The Möbius function at the split partition is a product over its two parts.
    exact (mu_bot_splitPartition _ (hCs y) (Finset.convex_filter_erase_le hmin₁ y)
      (nonempty_of_ne_empty (ne_empty_of_mem (mem_sdiff.2 ⟨hm₁, hm₁C y⟩)))).symm

end Recurrence

end CommRing

/-- `mu_bot_top` with integer coefficients, from which it is transported to any ring. -/
private theorem mu_bot_top_int (s : Finset α) :
    mu ℤ (⊥ : NoncrossingPartition s) ⊤ = (-1) ^ (#s - 1) * catalan (#s - 1) := by
  induction hn : #s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  subst hn
  by_cases hs1 : #s ≤ 1
  · rw [bot_eq_top_iff_card_le_one.2 hs1, mu_self, Nat.sub_eq_zero_of_le hs1, pow_zero,
      catalan_zero, Nat.cast_one, one_mul]
  obtain ⟨k, hk⟩ : ∃ k, #s = k + 2 := ⟨#s - 2, by omega⟩
  -- The two first positions `m₁ < m₂` of `s`.
  obtain ⟨m₁, hm₁, hmin₁⟩ : ∃ m ∈ s, ∀ z ∈ s, m ≤ z :=
    have hs : s.Nonempty := card_pos.1 (by omega)
    ⟨s.min' hs, min'_mem s hs, fun z hz => min'_le s z hz⟩
  have hcard : #(s.erase m₁) = k + 1 := by rw [card_erase_of_mem hm₁, hk]; rfl
  obtain ⟨m₂, hm₂, hmin₂⟩ : ∃ m ∈ s.erase m₁, ∀ z ∈ s.erase m₁, m ≤ z :=
    have ht : (s.erase m₁).Nonempty := card_pos.1 (by omega)
    ⟨_, min'_mem _ ht, fun z hz => min'_le _ z hz⟩
  have hpair : {m₁, m₂} ⊆ s :=
    insert_subset hm₁ (singleton_subset_iff.2 (mem_of_mem_erase hm₂))
  -- Weisner's theorem at the atom joining `m₁` and `m₂`.
  have hW := sum_filter_sup_eq_mu_eq_zero (𝕜 := ℤ)
    (a := (⟨_, isNoncrossing_pairPartition hpair⟩ : NoncrossingPartition s)) (d := ⊤)
    fun h => pairPartition_ne_bot (hij := hpair) (ne_of_mem_erase hm₂).symm <| by
      simpa only [coe_bot] using congrArg Subtype.val (le_bot_iff.1 h)
  have htop : (⊤ : NoncrossingPartition s) ∈ ({x | x ⊔ ⟨pairPartition s _ _ hpair,
      isNoncrossing_pairPartition hpair⟩ = ⊤} : Finset (NoncrossingPartition s)) := by simp
  rw [Icc_bot_top, ← add_sum_erase _ _ htop, sum_erase_top_mu_bot hpair hmin₁ hm₂ hmin₂] at hW
  -- By induction, each summand is a product of signed Catalan numbers.
  have hterm (y : α) (hy : y ∈ s.erase m₁) :
      mu ℤ (⊥ : NoncrossingPartition {z ∈ s.erase m₁ | z ≤ y}) ⊤ *
        mu ℤ (⊥ : NoncrossingPartition (s \ {z ∈ s.erase m₁ | z ≤ y})) ⊤ =
      (-1) ^ #{z ∈ s.erase m₁ | z < y} * catalan #{z ∈ s.erase m₁ | z < y} *
        ((-1) ^ #{z ∈ s.erase m₁ | y < z} * catalan #{z ∈ s.erase m₁ | y < z}) := by
    have hle : #{z ∈ s.erase m₁ | z ≤ y} = #{z ∈ s.erase m₁ | z < y} + 1 := by
      rw [← card_insert_of_notMem (by simp : y ∉ {z ∈ s.erase m₁ | z < y})]
      congr 1
      ext z
      simp only [mem_filter, mem_insert]
      grind
    have hsplit : #{z ∈ s.erase m₁ | z ≤ y} + #{z ∈ s.erase m₁ | y < z} = k + 1 := by
      rw [← hcard, ← card_filter_add_card_filter_not (s := s.erase m₁) (p := fun z => z ≤ y)]
      simp only [not_le]
    have hsdiff : #(s \ {z ∈ s.erase m₁ | z ≤ y}) = #{z ∈ s.erase m₁ | y < z} + 1 := by
      rw [card_sdiff_of_subset ((filter_subset _ _).trans (erase_subset _ _))]
      omega
    rw [ih _ (by omega) _ rfl, ih _ (by omega) _ rfl, hle, hsdiff, Nat.add_sub_cancel,
      Nat.add_sub_cancel]
  rw [sum_congr rfl hterm, sum_card_filter_lt_card_filter_gt (s.erase m₁)
    (fun i j => (-1 : ℤ) ^ i * catalan i * ((-1) ^ j * catalan j)), hcard,
    Nat.add_sub_cancel, sum_range_neg_one_pow_mul_catalan] at hW
  rw [eq_neg_of_add_eq_zero_left hW, hk, show k + 2 - 1 = k + 1 by omega, pow_succ]
  ring

/-- **The Möbius function of the lattice of noncrossing partitions**: on the noncrossing
partitions of a set `s` of `n` positions, `μ(0̂, 1̂) = (-1)^(n-1) C_(n-1)`, where `C_k` is the
`k`-th Catalan number. For `n = 0` both sides are `1`. -/
@[simp]
theorem mu_bot_top [Ring 𝕜] (s : Finset α) :
    mu 𝕜 (⊥ : NoncrossingPartition s) ⊤ = (-1) ^ (#s - 1) * catalan (#s - 1) := by
  rw [← map_mu (Int.castRingHom 𝕜) (map_one _), mu_bot_top_int]
  simp

/-- The Möbius function of `NC(n)`: `μ(0_n, 1_n) = (-1)^(n-1) C_(n-1)` on the noncrossing
partitions of the `n` ordered positions of `Fin n`. -/
theorem mu_bot_top_fin [Ring 𝕜] (n : ℕ) :
    mu 𝕜 (⊥ : NoncrossingPartition (univ : Finset (Fin n))) ⊤ =
      (-1) ^ (n - 1) * catalan (n - 1) := by
  rw [mu_bot_top, card_univ, Fintype.card_fin]

/-- The blockwise formula for the Möbius function of `NC(s)`: `μ(0̂, π)` is the product over the
parts `B` of `π` of `(-1)^(|B|-1) C_(|B|-1)`. -/
theorem mu_bot_eq_prod [CommRing 𝕜] (π : NoncrossingPartition s) :
    mu 𝕜 ⊥ π = ∏ B ∈ π.val.parts, (-1) ^ (#B - 1) * (catalan (#B - 1) : 𝕜) := by
  rw [mu_bot_eq_prod_mu]
  exact prod_congr rfl fun B _ => mu_bot_top B

/-! ### Upper intervals -/

/-- The Kreweras complement identifies an upper Möbius interval with a lower one:
`μ(π, 1̂) = μ(0̂, K(π))` on `NC(s)`. -/
theorem mu_top_eq_mu_bot_kreweras [AddCommGroup 𝕜] [One 𝕜] (π : NoncrossingPartition s) :
    mu 𝕜 π ⊤ = mu 𝕜 ⊥ (kreweras π) := by
  -- `mu_toDual` needs a ring, so compare over `ℤ` and transport along `k ↦ k • 1`.
  have h := OrderIso.mu_map (𝕜 := ℤ) (krewerasOrderIso s) π ⊤
  simp only [krewerasOrderIso_apply, kreweras_top, mu_toDual] at h
  simpa using congrArg (zmultiplesHom 𝕜 1) h.symm

/-- The blockwise formula for the Möbius function of `NC(s)` on upper intervals: `μ(π, 1̂)` is the
product over the parts `B` of the Kreweras complement `K(π)` of `(-1)^(|B|-1) C_(|B|-1)`. -/
theorem mu_top_eq_prod_kreweras [CommRing 𝕜] (π : NoncrossingPartition s) :
    mu 𝕜 π ⊤ = ∏ B ∈ (kreweras π).val.parts, (-1) ^ (#B - 1) * (catalan (#B - 1) : 𝕜) := by
  rw [mu_top_eq_mu_bot_kreweras, mu_bot_eq_prod]

/-! ### General intervals -/

/-- The blockwise formula for the Möbius function of `NC(s)` on all intervals: for `σ ≤ π`,
`μ(σ, π) = ∏_{B ∈ π} ∏_{C ∈ K_B(σ|_B)} (-1)^(|C|-1) C_(|C|-1)`, where `K_B` is the Kreweras
complement on `NC(B)`. In the lattice of all partitions, `μ(σ, π)` only depends on the number of
parts of `σ` inside each part of `π`; in `NC(s)` it also depends on how they are arranged, for
instance `μ({1,2}{3}{4}, 1_4) = 2` while `μ({1,3}{2}{4}, 1_4) = 1`. -/
theorem mu_eq_prod_prod_kreweras [CommRing 𝕜] {σ π : NoncrossingPartition s} (h : σ ≤ π) :
    mu 𝕜 σ π = ∏ B : π.val.parts, ∏ C ∈ (kreweras (σ.restrict (π.val.le B.property))).val.parts,
      (-1) ^ (#C - 1) * (catalan (#C - 1) : 𝕜) := by
  rw [mu_eq_prod_mu_restrict h]
  exact prod_congr rfl fun B _ => mu_top_eq_prod_kreweras _

end TauCeti.NoncrossingPartition
