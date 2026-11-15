/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Recoloring
public import TauCeti.Order.Partition.Finpartition
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Enumerative.CoupledColoring

/-!
# Coupled low-edit recolorings of pair-color systems

When regularizing a pair-color system by editing few pairs, recoloring a disjoint pair `(s, t)`
from scratch (`TauCeti.PairColorSystem.exists_recoloring_isRegularPair`) edits a constant fraction
of `s ×ˢ t` even when `S` already has densities on `(s, t)` close to the target distribution `p`.
When `(s, t)` is already `δ`-regular for `S`, coupling `S`'s colors on `s ×ˢ t` to `p` via
`TauCeti.exists_recoloring_card_filter_ne_lt` keeps the edit count on `s ×ˢ t` within `ε ^ 3 #s #t`
of the total variation count `(1 / 2) (∑ c, |d_c(s, t) - p c|) #s #t`, while every subrectangle
`s' ×ˢ t'` (`s' ⊆ s`, `t' ⊆ t`) has color-count discrepancy at most `(ε ^ 3 + card κ * δ) #s #t`
around `p` (`TauCeti.PairColorSystem.exists_coupled_recoloring_abs_card_filter_sub_le`).

Working directly with subrectangle *count* discrepancy (holding on all `s' ⊆ s`, `t' ⊆ t` without
any minimum-size threshold) allows fine-block recolorings along a refinement `Q ≤ P` to be summed
additively onto coarse off-diagonal cell pairs `(A, B)` of `P`
(`TauCeti.PairColorSystem.abs_card_filter_colorOfPair_sub_le_of_refines`) and glued into a single
coherent `PairColorSystem` (`TauCeti.PairColorSystem.exists_offDiag_recoloring_of_refines`).

## Main results

* `TauCeti.PairColorSystem.exists_coupled_recoloring_abs_card_filter_sub_le`: coupled recoloring of
  a `δ`-regular disjoint pair `(s, t)` toward target densities `p`, controlling both edit count and
  all subrectangle color counts.
* `TauCeti.PairColorSystem.exists_recoloring_abs_card_filter_sub_le`: uncoupled rectangle-count
  counterpart for arbitrary disjoint pairs `(s, t)`.
* `TauCeti.PairColorSystem.abs_card_filter_colorOfPair_sub_le_of_refines`: summing fine-block
  rectangle count discrepancy along `Q ≤ P` onto coarse cell pairs.
* `TauCeti.PairColorSystem.isRegularPair_of_abs_card_filter_colorOfPair_sub_le`: small rectangle
  count discrepancy on `(s, t)` implies `IsRegularPair`.
* `TauCeti.PairColorSystem.exists_offDiag_recoloring_of_refines`: gluing local fine-block
  recolorings across all off-diagonal coarse pairs of `Q ≤ P` into one global `PairColorSystem`.

## References

* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), Lemma 4.3.
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Lemma 4.2.
-/

public section

open Finset Real

namespace TauCeti.PairColorSystem

variable {κ V : Type*}

open Classical in
/-- Recolor the pairs from `s` to `t` by `x`, the pairs from `t` to `s` by the reversed colors,
and keep all other colors of `S`. -/
private noncomputable def recolorProduct (S : PairColorSystem κ V) {s t : Finset V}
    (hst : Disjoint s t) (x : V × V → κ) : PairColorSystem κ V where
  color q :=
    if q.1 ∈ s ×ˢ t then x q.1 else if q.1.swap ∈ s ×ˢ t then S.rev (x q.1.swap) else S.color q
  rev := S.rev
  rev_involutive := S.rev_involutive
  color_rev q := by
    obtain ⟨⟨u, v⟩, huv⟩ := q
    have hboth : ¬((u, v) ∈ s ×ˢ t ∧ (v, u) ∈ s ×ˢ t) := fun ⟨h₁, h₂⟩ ↦
      disjoint_left.1 hst (mem_product.1 h₂).1 (mem_product.1 h₁).2
    simp only [Prod.swap_prod_mk]
    by_cases h₁ : (u, v) ∈ s ×ˢ t <;> by_cases h₂ : (v, u) ∈ s ×ˢ t
    · exact absurd ⟨h₁, h₂⟩ hboth
    · simp [h₁, h₂]
    · simp [h₁, h₂]
    · simpa [h₁, h₂] using S.color_rev ⟨(u, v), huv⟩

private theorem colorOfPair_recolorProduct_of_mem {S : PairColorSystem κ V} {s t : Finset V}
    (hst : Disjoint s t) (x : V × V → κ) {u v : V} (h : (u, v) ∈ s ×ˢ t) :
    (S.recolorProduct hst x).colorOfPair u v = some (x (u, v)) := by
  have huv : u ≠ v := hst.forall_ne_finset (mem_product.1 h).1 (mem_product.1 h).2
  rw [colorOfPair_of_ne _ huv]
  simp [recolorProduct, h]

private theorem colorOfPair_recolorProduct_of_not_mem {S : PairColorSystem κ V} {s t : Finset V}
    (hst : Disjoint s t) (x : V × V → κ) {u v : V} (hs : u ∈ s → v ∉ t) (ht : u ∈ t → v ∉ s) :
    (S.recolorProduct hst x).colorOfPair u v = S.colorOfPair u v := by
  by_cases huv : u = v
  · simp [huv]
  have h₁ : (u, v) ∉ s ×ˢ t := fun h ↦ hs (mem_product.1 h).1 (mem_product.1 h).2
  have h₂ : (v, u) ∉ s ×ˢ t := fun h ↦ ht (mem_product.1 h).2 (mem_product.1 h).1
  rw [colorOfPair_of_ne _ huv, colorOfPair_of_ne _ huv]
  simp [recolorProduct, h₁, h₂]

/-- The size bound `card κ ^ 2 * (card κ + 2) ≤ ε ^ 6 * #u` on a nonempty palette forces
`#u ≥ 1`. -/
private theorem one_le_cast_card_of_sq_mul_le [Fintype κ] [Nonempty κ] {ε : ℝ} {u : Finset V}
    (h : (Fintype.card κ : ℝ) ^ 2 * (Fintype.card κ + 2) ≤ ε ^ 6 * #u) : (1 : ℝ) ≤ #u := by
  have hK : (1 : ℝ) ≤ Fintype.card κ := Nat.one_le_cast.2 Fintype.card_pos
  have hu : (0 : ℝ) < #u := by
    by_contra! h'
    have : ε ^ 6 * #u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h'
    nlinarith
  exact Nat.one_le_cast.2 (Nat.cast_pos.1 hu)

/-- Exponential union bound for coupled rectangle recoloring across the `2 ^ #s * 2 ^ #t`
subrectangles and `card κ` source/target colors. -/
private theorem two_mul_two_pow_add_one_mul_exp_lt [Fintype κ] [Nonempty κ] {ε : ℝ}
    {s t : Finset V}
    (hs : (Fintype.card κ : ℝ) ^ 2 * (Fintype.card κ + 2) ≤ ε ^ 6 * #s)
    (ht : (Fintype.card κ : ℝ) ^ 2 * (Fintype.card κ + 2) ≤ ε ^ 6 * #t) :
    2 * ((2 ^ #s * 2 ^ #t : ℕ) + 1 : ℝ) * Fintype.card κ *
      exp (-2 * (ε ^ 3 * #s * #t / Fintype.card κ) ^ 2 / (#s * #t : ℕ)) < 1 := by
  set K : ℝ := (Fintype.card κ : ℝ)
  have hK : 1 ≤ K := Nat.one_le_cast.2 Fintype.card_pos
  have hm := one_le_cast_card_of_sq_mul_le hs
  have hn := one_le_cast_card_of_sq_mul_le ht
  have h2 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have hpow (k : ℕ) : (2 : ℝ) ^ k ≤ exp k :=
    (pow_le_pow_left₀ (by norm_num) h2 k).trans_eq (by rw [← exp_nat_mul, mul_one])
  have hrect : 2 * (((2 ^ #s * 2 ^ #t : ℕ) : ℝ) + 1) ≤ exp 2 * (exp #s * exp #t) := by
    have h1 : (1 : ℝ) ≤ ((2 ^ #s * 2 ^ #t : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (Nat.pow_pos two_pos) (Nat.pow_pos two_pos)
    have h4 : (4 : ℝ) ≤ exp 2 := by
      have := mul_le_mul h2 h2 (by norm_num) (exp_pos 1).le
      rw [← exp_add] at this
      norm_num at this ⊢
      exact this
    calc 2 * (((2 ^ #s * 2 ^ #t : ℕ) : ℝ) + 1)
        ≤ 4 * ((2 ^ #s : ℝ) * 2 ^ #t) := by push_cast at h1 ⊢; linarith
      _ ≤ exp 2 * (exp #s * exp #t) := by gcongr; exacts [hpow _, hpow _]
  have hKexp : K ≤ exp (K - 1) := by linarith [add_one_le_exp (K - 1)]
  have hexp : -2 * (ε ^ 3 * #s * #t / K) ^ 2 / ((#s * #t : ℕ) : ℝ) =
      -2 * (ε ^ 6 * #s / K ^ 2) * #t := by
    push_cast
    field_simp
  calc 2 * (((2 ^ #s * 2 ^ #t : ℕ) : ℝ) + 1) * K *
        exp (-2 * (ε ^ 3 * #s * #t / K) ^ 2 / (#s * #t : ℕ))
      ≤ exp 2 * (exp #s * exp #t) * exp (K - 1) * exp (-2 * (ε ^ 6 * #s / K ^ 2) * #t) := by
        rw [hexp]
        gcongr
    _ = exp (#s + #t + K + 1 - 2 * (ε ^ 6 * #s / K ^ 2) * #t) := by
        simp only [← exp_add]
        ring_nf
    _ < 1 := by
        rw [exp_lt_one_iff, sub_neg]
        have hs' : K + 2 ≤ ε ^ 6 * #s / K ^ 2 := (le_div_iff₀' (by positivity)).2 hs
        have ht' : K + 2 ≤ ε ^ 6 * #t / K ^ 2 := (le_div_iff₀' (by positivity)).2 ht
        have heq : 2 * (ε ^ 6 * #s / K ^ 2) * #t =
            (ε ^ 6 * #s / K ^ 2) * #t + #s * (ε ^ 6 * #t / K ^ 2) := by ring
        rw [heq]
        nlinarith [mul_le_mul_of_nonneg_right hs' (by linarith : (0 : ℝ) ≤ #t),
          mul_le_mul_of_nonneg_left ht' (by linarith : (0 : ℝ) ≤ #s)]

/-- **Coupled low-edit recoloring of a regular pair.** Let `(s, t)` be a `δ`-regular disjoint pair
for `S`, and let `p` be a target probability distribution on `κ`. If
`card κ ^ 2 * (card κ + 2) ≤ ε ^ 6 * #s` and `card κ ^ 2 * (card κ + 2) ≤ ε ^ 6 * #t` for `ε > 0`,
then the pairs between `s` and `t` can be recolored into `S'` (preserving `S.rev` and all pairs not
joining `s` and `t`) so that:

* the edited pairs in `s ×ˢ t` number at most
  `((∑ c, |pairColorDensity S c s t - p c|) / 2 + ε ^ 3) * (#s * #t)`, and
* on every subrectangle `s' ×ˢ t'` (`s' ⊆ s`, `t' ⊆ t`) and color `c`, the color count differs from
  `p c * (#s' * #t')` by at most `(ε ^ 3 + card κ * δ) * (#s * #t)`. -/
theorem exists_coupled_recoloring_abs_card_filter_sub_le [Fintype κ] [DecidableEq κ]
    (S : PairColorSystem κ V) {s t : Finset V} (hst : Disjoint s t) {δ : ℝ}
    (hreg : S.IsRegularPair δ s t) {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    {ε : ℝ} (hε : 0 < ε)
    (hs : (Fintype.card κ : ℝ) ^ 2 * (Fintype.card κ + 2) ≤ ε ^ 6 * #s)
    (ht : (Fintype.card κ : ℝ) ^ 2 * (Fintype.card κ + 2) ≤ ε ^ 6 * #t) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) → S'.colorOfPair u v = S.colorOfPair u v) ∧
      (#{q ∈ s ×ˢ t | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        ((∑ c, |(pairColorDensity S c s t : ℝ) - p c|) / 2 + ε ^ 3) * (#s * #t) ∧
      ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t,
        |(#{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#s' * #t')| ≤
          (ε ^ 3 + Fintype.card κ * δ) * (#s * #t) := by
  classical
  have : Nonempty κ :=
    Classical.byContradiction fun hκ ↦ by have := not_nonempty_iff.1 hκ; simp at hp1
  have hs0 : (0 : ℝ) < #s := lt_of_lt_of_le zero_lt_one (one_le_cast_card_of_sq_mul_le hs)
  have ht0 : (0 : ℝ) < #t := lt_of_lt_of_le zero_lt_one (one_le_cast_card_of_sq_mul_le ht)
  let y : V × V → κ := fun q ↦ if h : q.1 ≠ q.2 then S.color ⟨q, h⟩ else Classical.arbitrary κ
  have hy_iff {q : V × V} (hq : q ∈ s ×ˢ t) (c : κ) :
      y q = c ↔ S.colorOfPair q.1 q.2 = some c := by
    simp [y, hst.forall_ne_finset (mem_product.1 hq).1 (mem_product.1 hq).2]
  have hy_card {s' t' : Finset V} (hs' : s' ⊆ s) (ht' : t' ⊆ t) (c : κ) :
      #{q ∈ s' ×ˢ t' | y q = c} = #{q ∈ s' ×ˢ t' | S.colorOfPair q.1 q.2 = some c} :=
    congrArg card (filter_congr fun q hq ↦ hy_iff (product_subset_product hs' ht' hq) c)
  have hy_st (c : κ) : (#{q ∈ s ×ˢ t | y q = c} : ℝ) = pairColorDensity S c s t * (#s * #t) := by
    rw [hy_card subset_rfl subset_rfl]
    exact mod_cast (pairColorDensity_mul_card_of_disjoint S c hst).symm
  obtain ⟨x, -, hne_lt, hrect⟩ := exists_recoloring_card_filter_ne_lt hp hp1 y (s ×ˢ t)
    (I := ↥(s.powerset ×ˢ t.powerset)) (fun i ↦ i.1.1 ×ˢ i.1.2)
    (fun i ↦ product_subset_product (mem_powerset.1 (mem_product.1 i.2).1)
      (mem_powerset.1 (mem_product.1 i.2).2))
    (N := #s * #t) (by rw [card_product]) (a := ε ^ 3 * #s * #t) (by positivity)
    (by simpa [card_product, card_powerset] using two_mul_two_pow_add_one_mul_exp_lt hs ht)
  refine ⟨S.recolorProduct hst x, rfl, fun u v ↦ colorOfPair_recolorProduct_of_not_mem hst x,
    ?_, fun c s' hs' t' ht' ↦ ?_⟩
  · have hne_eq : #{q ∈ s ×ˢ t | (S.recolorProduct hst x).colorOfPair q.1 q.2 ≠
        S.colorOfPair q.1 q.2} = #{q ∈ s ×ˢ t | x q ≠ y q} :=
      congrArg card (filter_congr fun ⟨u, v⟩ hq ↦ by
        rw [colorOfPair_recolorProduct_of_mem hst x hq, ne_eq, eq_comm, ← hy_iff hq, eq_comm])
    have htv : ∑ c, |(#{q ∈ s ×ˢ t | y q = c} : ℝ) - p c * #(s ×ˢ t)| =
        (∑ c, |(pairColorDensity S c s t : ℝ) - p c|) * (#s * #t) := by
      rw [sum_mul]
      exact sum_congr rfl fun c _ ↦ by
        rw [hy_st, card_product, Nat.cast_mul, ← sub_mul, abs_mul, abs_of_pos (mul_pos hs0 ht0)]
    rw [hne_eq]
    linarith [hne_lt]
  · have hdev := hrect ⟨(s', t'), mem_product.2 ⟨mem_powerset.2 hs', mem_powerset.2 ht'⟩⟩ c
    have hx_eq : #{q ∈ s' ×ˢ t' | (S.recolorProduct hst x).colorOfPair q.1 q.2 = some c} =
        #{q ∈ s' ×ˢ t' | x q = c} :=
      congrArg card (filter_congr fun q hq ↦ by
        rw [colorOfPair_recolorProduct_of_mem hst x (product_subset_product hs' ht' hq),
          Option.some_inj])
    have hy_sum : ∑ c₀, |(#{q ∈ s' ×ˢ t' | y q = c₀} : ℝ) -
        (#{q ∈ s ×ˢ t | y q = c₀} : ℝ) / #(s ×ˢ t) * #(s' ×ˢ t')| ≤
        Fintype.card κ * (δ * #s * #t) :=
      (sum_le_sum (g := fun _ ↦ δ * #s * #t) fun c₀ _ ↦ by
        rw [hy_st c₀, hy_card hs' ht', card_product s t, Nat.cast_mul,
          mul_div_cancel_right₀ _ (mul_pos hs0 ht0).ne', card_product, Nat.cast_mul, ← mul_assoc]
        exact hreg.abs_card_filter_colorOfPair_sub_le hst hs' ht').trans_eq
        (by rw [sum_const, card_univ, nsmul_eq_mul])
    rw [hx_eq, ← Nat.cast_mul, ← card_product]
    linarith

/-- **Uncoupled rectangle-count recoloring.** Under `card κ + 1 ≤ ε ^ 6 * #s` and
`card κ + 1 ≤ ε ^ 6 * #t`, recoloring `s ×ˢ t` toward `p` achieves rectangle count discrepancy at
most `3 * ε * (#s * #t)` on *every* subrectangle `s' ×ˢ t'` (`s' ⊆ s`, `t' ⊆ t`). -/
theorem exists_recoloring_abs_card_filter_sub_le [Fintype κ] [DecidableEq κ]
    (S : PairColorSystem κ V) {s t : Finset V} (hst : Disjoint s t) {p : κ → ℝ}
    (hp : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) {ε : ℝ} (hε : 0 < ε)
    (hs : Fintype.card κ + 1 ≤ ε ^ 6 * #s) (ht : Fintype.card κ + 1 ≤ ε ^ 6 * #t) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) → S'.colorOfPair u v = S.colorOfPair u v) ∧
      ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t,
        |(#{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#s' * #t')| ≤
          3 * ε * (#s * #t) := by
  obtain ⟨S', hrev, hagree, hreg, hdens⟩ :=
    S.exists_recoloring_isRegularPair hst hp hp1 hε hs ht
  refine ⟨S', hrev, hagree, fun c s' hs' t' ht' ↦ ?_⟩
  have h₁ := hreg.abs_card_filter_colorOfPair_sub_le (c := c) hst hs' ht'
  have hst' : (#s' : ℝ) * #t' ≤ #s * #t :=
    mul_le_mul (Nat.cast_le.2 (card_le_card hs')) (Nat.cast_le.2 (card_le_card ht'))
      (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have h₂ : |(pairColorDensity S' c s t : ℝ) * #s' * #t' - p c * (#s' * #t')| ≤ ε * (#s * #t) := by
    rw [mul_assoc (pairColorDensity S' c s t : ℝ), ← sub_mul, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ #s' * #t')]
    exact (mul_le_mul_of_nonneg_right (hdens c) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hst' hε.le)
  linarith [abs_sub_le (#{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some c} : ℝ)
    (pairColorDensity S' c s t * #s' * #t') (p c * (#s' * #t'))]

/-- Rectangle count discrepancy on `(s, t)` around `p` transfers to `(t, s)` around `p ∘ S.rev`
whenever `S'.rev = S.rev`. -/
private theorem abs_card_filter_colorOfPair_sub_le_swap [DecidableEq κ]
    {S S' : PairColorSystem κ V} (hrev : S'.rev = S.rev) {s t : Finset V} {p : κ → ℝ} {η : ℝ}
    (h : ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t,
      |(#{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#s' * #t')| ≤
        η * (#s * #t)) :
    ∀ c, ∀ t' ⊆ t, ∀ s' ⊆ s,
      |(#{q ∈ t' ×ˢ s' | S'.colorOfPair q.1 q.2 = some c} : ℝ) - p (S.rev c) * (#t' * #s')| ≤
        η * (#t * #s) := by
  classical
  intro c t' ht' s' hs'
  have hcard : #{q ∈ t' ×ˢ s' | S'.colorOfPair q.1 q.2 = some c} =
      #{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some (S.rev c)} := by
    apply card_equiv (Equiv.prodComm V V)
    rintro ⟨v, u⟩
    rw [mem_filter, mem_filter, mem_product, mem_product, Equiv.prodComm_apply,
      Prod.swap_prod_mk, and_comm (a := v ∈ t'), ← hrev, S'.colorOfPair_swap_eq_some_iff v u c]
  rw [hcard, mul_comm (#t' : ℝ) #s', mul_comm (#t : ℝ) #s]
  exact h (S.rev c) s' hs' t' ht'

/-- **Coarse rectangle discrepancy from fine blocks.** Let `Q ≤ P` be finite partitions of `u`, and
let `A, B ∈ P.parts` be distinct coarse parts. If every pair `(A', B')` of fine parts in `A` and `B`
has rectangle count discrepancy at most `η * (#A' * #B')` around `p`, then `(A, B)` has rectangle
count discrepancy at most `η * (#A * #B)` around `p` on all `X ⊆ A` and `Y ⊆ B`. -/
theorem abs_card_filter_colorOfPair_sub_le_of_refines [DecidableEq V] [DecidableEq κ]
    (T : PairColorSystem κ V) {u : Finset V} {P Q : Finpartition u} (hQP : Q ≤ P)
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) {p : κ → ℝ} {η : ℝ}
    (hfine : ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B → ∀ c, ∀ s' ⊆ A', ∀ t' ⊆ B',
      |(#{q ∈ s' ×ˢ t' | T.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#s' * #t')| ≤
        η * (#A' * #B'))
    (c : κ) {X Y : Finset V} (hX : X ⊆ A) (hY : Y ⊆ B) :
    |(#{q ∈ X ×ˢ Y | T.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#X * #Y)| ≤
      η * (#A * #B) := by
  set QA := {A' ∈ Q.parts | A' ⊆ A}
  set QB := {B' ∈ Q.parts | B' ⊆ B}
  have hdisjQ : ∀ {Z : Finset (Finset V)}, Z ⊆ Q.parts → ∀ W : Finset V,
      (Z : Set (Finset V)).PairwiseDisjoint fun C ↦ W ∩ C := fun hZ W C hC D hD hne ↦
    (Q.disjoint (hZ hC) (hZ hD) hne).mono inter_subset_right inter_subset_right
  have hdecomp {C W : Finset V} (hC : C ∈ P.parts) (hW : W ⊆ C) :
      {C' ∈ Q.parts | C' ⊆ C}.biUnion (fun C' ↦ W ∩ C') = W := by
    simpa only [id_eq, inter_biUnion] using
      (congrArg (W ∩ ·) (Finpartition.biUnion_filter_subset_eq_of_le hQP hC)).trans
        (inter_eq_left.2 hW)
  have hXcard : (#X : ℝ) = ∑ A' ∈ QA, (#(X ∩ A') : ℝ) := by
    exact_mod_cast (congrArg card (hdecomp hA hX).symm).trans
      (card_biUnion (hdisjQ (filter_subset _ _) X))
  have hYcard : (#Y : ℝ) = ∑ B' ∈ QB, (#(Y ∩ B') : ℝ) := by
    exact_mod_cast (congrArg card (hdecomp hB hY).symm).trans
      (card_biUnion (hdisjQ (filter_subset _ _) Y))
  have hAcard : (#A : ℝ) = ∑ A' ∈ QA, (#A' : ℝ) := by
    exact_mod_cast (congrArg card (Finpartition.biUnion_filter_subset_eq_of_le hQP hA).symm).trans
      (card_biUnion (Q.supIndep.pairwiseDisjoint.subset (filter_subset _ _)))
  have hBcard : (#B : ℝ) = ∑ B' ∈ QB, (#B' : ℝ) := by
    exact_mod_cast (congrArg card (Finpartition.biUnion_filter_subset_eq_of_le hQP hB).symm).trans
      (card_biUnion (Q.supIndep.pairwiseDisjoint.subset (filter_subset _ _)))
  have hprod : X ×ˢ Y = (QA ×ˢ QB).biUnion fun P' ↦ (X ∩ P'.1) ×ˢ (Y ∩ P'.2) := by
    conv_lhs => rw [← hdecomp hA hX, ← hdecomp hB hY]
    ext ⟨x, y⟩
    simp only [mem_product, mem_biUnion, Prod.exists]
    tauto
  have hdisjP : ((QA ×ˢ QB : Finset _) : Set _).PairwiseDisjoint
      fun P' : Finset V × Finset V ↦
        {q ∈ (X ∩ P'.1) ×ˢ (Y ∩ P'.2) | T.colorOfPair q.1 q.2 = some c} := by
    intro P₁ hP₁ P₂ hP₂ hne
    refine disjoint_filter_filter (disjoint_product.2 ?_)
    by_cases h₁ : P₁.1 = P₂.1
    · exact Or.inr (hdisjQ (filter_subset _ _) Y (mem_product.1 hP₁).2 (mem_product.1 hP₂).2
        fun h₂ ↦ hne (Prod.ext h₁ h₂))
    · exact Or.inl (hdisjQ (filter_subset _ _) X (mem_product.1 hP₁).1 (mem_product.1 hP₂).1 h₁)
  have hcount : (#{q ∈ X ×ˢ Y | T.colorOfPair q.1 q.2 = some c} : ℝ) =
      ∑ P' ∈ QA ×ˢ QB, (#{q ∈ (X ∩ P'.1) ×ˢ (Y ∩ P'.2) | T.colorOfPair q.1 q.2 = some c} : ℝ) := by
    exact_mod_cast (congrArg card (by rw [hprod, filter_biUnion])).trans (card_biUnion hdisjP)
  have hmean : p c * (#X * #Y) = ∑ P' ∈ QA ×ˢ QB, p c * (#(X ∩ P'.1) * #(Y ∩ P'.2)) := by
    rw [hXcard, hYcard, sum_mul_sum, ← sum_product', mul_sum]
  rw [hcount, hmean, ← sum_sub_distrib, hAcard, hBcard, sum_mul_sum, ← sum_product', mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun P' hP' ↦ ?_)
  obtain ⟨hA', hB'⟩ := mem_product.1 hP'
  exact hfine P'.1 (mem_filter.1 hA').1 (mem_filter.1 hA').2 P'.2 (mem_filter.1 hB').1
    (mem_filter.1 hB').2 c _ inter_subset_right _ inter_subset_right

/-- Small rectangle count discrepancy on disjoint nonempty `(s, t)` around `p` implies both
`|(pairColorDensity T c s t : ℝ) - p c| ≤ η` and `T.IsRegularPair θ s t` whenever
`2 * η ≤ min 1 θ ^ 3` and `0 < θ`. -/
theorem isRegularPair_of_abs_card_filter_colorOfPair_sub_le [DecidableEq κ]
    (T : PairColorSystem κ V) {s t : Finset V} (hst : Disjoint s t) (hs : s.Nonempty)
    (ht : t.Nonempty) {p : κ → ℝ} {η θ : ℝ} (hθ : 0 < θ) (hη : 2 * η ≤ min 1 θ ^ 3)
    (hrect : ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t,
      |(#{q ∈ s' ×ˢ t' | T.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#s' * #t')| ≤
        η * (#s * #t)) :
    T.IsRegularPair θ s t ∧ ∀ c, |(pairColorDensity T c s t : ℝ) - p c| ≤ η := by
  have hs0 : (0 : ℝ) < #s := Nat.cast_pos.2 hs.card_pos
  have ht0 : (0 : ℝ) < #t := Nat.cast_pos.2 ht.card_pos
  have hd_le {s' t' : Finset V} (hs' : s' ⊆ s) (ht' : t' ⊆ t) (c : κ) :
      |(pairColorDensity T c s' t' : ℝ) - p c| * (#s' * #t') ≤ η * (#s * #t) := by
    have hc : (#{q ∈ s' ×ˢ t' | T.colorOfPair q.1 q.2 = some c} : ℝ) =
        pairColorDensity T c s' t' * (#s' * #t') :=
      mod_cast (pairColorDensity_mul_card_of_disjoint T c (hst.mono hs' ht')).symm
    have hr := hrect c s' hs' t' ht'
    rwa [hc, ← sub_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ #s' * #t')] at hr
  have hfull (c : κ) : |(pairColorDensity T c s t : ℝ) - p c| ≤ η :=
    le_of_mul_le_mul_right (hd_le subset_rfl subset_rfl c) (mul_pos hs0 ht0)
  refine ⟨?_, hfull⟩
  obtain h1θ | hθ1 := le_or_gt 1 θ
  · exact isRegularPair_of_one_le h1θ
  rw [min_eq_right hθ1.le] at hη
  rw [isRegularPair_iff]
  intro c s' hs' t' ht' hs's ht't
  have hpos : (0 : ℝ) < #s' * #t' := mul_pos ((mul_pos hθ hs0).trans_le hs's)
    ((mul_pos hθ ht0).trans_le ht't)
  have hsub : |(pairColorDensity T c s' t' : ℝ) - p c| ≤ θ / 2 := by
    refine le_of_mul_le_mul_right ?_ hpos
    calc |(pairColorDensity T c s' t' : ℝ) - p c| * (#s' * #t')
        ≤ η * (#s * #t) := hd_le hs' ht' c
      _ ≤ (θ ^ 3 / 2) * (#s * #t) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (θ / 2) * ((θ * #s) * (θ * #t)) := by ring
      _ ≤ (θ / 2) * (#s' * #t') := by gcongr
  have hη_le : η ≤ θ / 2 := by
    have : θ ^ 3 ≤ θ := by nlinarith [sq_nonneg θ]
    linarith
  calc |(pairColorDensity T c s' t' : ℝ) - pairColorDensity T c s t|
      ≤ |(pairColorDensity T c s' t' : ℝ) - p c| + |p c - pairColorDensity T c s t| :=
        abs_sub_le _ _ _
    _ ≤ θ := by rw [abs_sub_comm (p c)]; linarith [hfull c]

/-- Two pair-color systems sharing `S.rev` have the same number of disagreements with `S` on
`s ×ˢ t` and on `t ×ˢ s`. -/
private theorem card_colorOfPair_ne_swap [DecidableEq κ] {S S' : PairColorSystem κ V}
    (hrev : S'.rev = S.rev) (s t : Finset V) :
    #{q ∈ s ×ˢ t | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
      #{q ∈ t ×ˢ s | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} := by
  classical
  apply card_equiv (Equiv.prodComm V V)
  rintro ⟨u, v⟩
  have hinj := Option.map_injective S.rev_involutive.injective
  have heq : S'.colorOfPair v u = S.colorOfPair v u ↔ S'.colorOfPair u v = S.colorOfPair u v := by
    rw [← hinj.eq_iff, ← S.colorOfPair_swap v u, ← hrev, ← S'.colorOfPair_swap v u]
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, mem_filter, mem_product,
    and_comm (a := u ∈ s), ne_eq, heq]

section GlueOffDiag

variable [Fintype V] [DecidableEq V]

open Classical in
/-- Assemble local pair-color systems `L A' B'` (`(L A' B').rev = S.rev`) on fine blocks of `Q ≤ P`
lying in distinct coarse cells of `P`, orienting unordered fine pairs via `e` and preserving `S`
inside each coarse cell of `P`. -/
private noncomputable def glueOffDiag (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (e : Q.parts ≃ Fin #Q.parts)
    (L : Q.parts → Q.parts → PairColorSystem κ V) (hLrev : ∀ A' B', (L A' B').rev = S.rev) :
    PairColorSystem κ V where
  color q :=
    let A' : Q.parts := ⟨Q.part q.1.1, Q.part_mem.2 (mem_univ _)⟩
    let B' : Q.parts := ⟨Q.part q.1.2, Q.part_mem.2 (mem_univ _)⟩
    if P.part q.1.1 = P.part q.1.2 then S.color q
    else if e A' < e B' then (L A' B').color q else (L B' A').color q
  rev := S.rev
  rev_involutive := S.rev_involutive
  color_rev q := by
    obtain ⟨⟨u, v⟩, huv⟩ := q
    let A' : Q.parts := ⟨Q.part u, Q.part_mem.2 (mem_univ _)⟩
    let B' : Q.parts := ⟨Q.part v, Q.part_mem.2 (mem_univ _)⟩
    change (if P.part v = P.part u then S.color ⟨(v, u), huv.symm⟩
        else if e B' < e A' then (L B' A').color ⟨(v, u), huv.symm⟩
        else (L A' B').color ⟨(v, u), huv.symm⟩) =
      S.rev (if P.part u = P.part v then S.color ⟨(u, v), huv⟩
        else if e A' < e B' then (L A' B').color ⟨(u, v), huv⟩
        else (L B' A').color ⟨(u, v), huv⟩)
    by_cases hP : P.part u = P.part v
    · simp only [ite_eq_left hP, ite_eq_left hP.symm]
      exact S.color_rev ⟨(u, v), huv⟩
    have hAB' : e A' ≠ e B' := fun he ↦ hP <|
      Finpartition.part_eq_part_of_le hQP (congrArg Subtype.val (e.injective he))
    simp only [ite_eq_right hP, ite_eq_right (Ne.symm hP)]
    rcases lt_or_gt_of_ne hAB' with hlt | hgt
    · rw [ite_eq_left hlt, ite_eq_right (lt_asymm hlt), ← hLrev A' B']
      exact (L A' B').color_rev ⟨(u, v), huv⟩
    · rw [ite_eq_right (lt_asymm hgt), ite_eq_left hgt, ← hLrev B' A']
      exact (L B' A').color_rev ⟨(u, v), huv⟩

private theorem glueOffDiag_colorOfPair_of_lt {S : PairColorSystem κ V}
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (e : Q.parts ≃ Fin #Q.parts)
    (L : Q.parts → Q.parts → PairColorSystem κ V) (hLrev : ∀ A' B', (L A' B').rev = S.rev)
    {A' B' : Q.parts} (hP : Finpartition.refinementParent hQP A' ≠
      Finpartition.refinementParent hQP B')
    (hlt : e A' < e B') {u v : V} (hu : u ∈ A'.1) (hv : v ∈ B'.1) :
    (S.glueOffDiag hQP e L hLrev).colorOfPair u v = (L A' B').colorOfPair u v := by
  have hPu : P.part u = (Finpartition.refinementParent hQP A').1 :=
    Finpartition.part_eq_refinementParent hQP A' hu
  have hPv : P.part v = (Finpartition.refinementParent hQP B').1 :=
    Finpartition.part_eq_refinementParent hQP B' hv
  have hPne : P.part u ≠ P.part v := by rw [hPu, hPv]; exact Subtype.coe_injective.ne hP
  have huv : u ≠ v := fun h ↦ hPne (h ▸ rfl)
  have hQu : (⟨Q.part u, Q.part_mem.2 (mem_univ _)⟩ : Q.parts) = A' :=
    Subtype.ext (Q.part_eq_of_mem A'.2 hu)
  have hQv : (⟨Q.part v, Q.part_mem.2 (mem_univ _)⟩ : Q.parts) = B' :=
    Subtype.ext (Q.part_eq_of_mem B'.2 hv)
  rw [colorOfPair_of_ne _ huv, colorOfPair_of_ne _ huv]
  dsimp only [glueOffDiag]
  rw [ite_eq_right hPne, hQu, hQv, ite_eq_left hlt]

private theorem glueOffDiag_colorOfPair_of_gt {S : PairColorSystem κ V}
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (e : Q.parts ≃ Fin #Q.parts)
    (L : Q.parts → Q.parts → PairColorSystem κ V) (hLrev : ∀ A' B', (L A' B').rev = S.rev)
    {A' B' : Q.parts} (hP : Finpartition.refinementParent hQP A' ≠
      Finpartition.refinementParent hQP B')
    (hgt : e B' < e A') {u v : V} (hu : u ∈ A'.1) (hv : v ∈ B'.1) :
    (S.glueOffDiag hQP e L hLrev).colorOfPair u v = (L B' A').colorOfPair u v := by
  have hswap := glueOffDiag_colorOfPair_of_lt (S := S) hQP e L hLrev hP.symm hgt hv hu
  have h₁ := (S.glueOffDiag hQP e L hLrev).colorOfPair_swap u v
  have h₂ := (L B' A').colorOfPair_swap u v
  dsimp only [glueOffDiag] at h₁
  rw [hLrev B' A'] at h₂
  exact Option.map_injective S.rev_involutive.injective (h₁.symm.trans (hswap.trans h₂))

/-- Bound global ordered-pair edits of `glueOffDiag` by summing symmetric fine-block edit bounds
over all ordered fine pairs lying in distinct coarse parts. -/
private theorem card_glueOffDiag_colorOfPair_ne_le [DecidableEq κ] {S : PairColorSystem κ V}
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (e : Q.parts ≃ Fin #Q.parts)
    (L : Q.parts → Q.parts → PairColorSystem κ V) (hLrev : ∀ A' B', (L A' B').rev = S.rev)
    {b : Q.parts → Q.parts → ℝ} (hb_symm : ∀ A' B', b A' B' = b B' A')
    (hb : ∀ A' B', Finpartition.refinementParent hQP A' ≠ Finpartition.refinementParent hQP B' →
      (#{q ∈ A'.1 ×ˢ B'.1 | (L A' B').colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        b A' B') :
    (#{q : V × V | (S.glueOffDiag hQP e L hLrev).colorOfPair q.1 q.2 ≠
        S.colorOfPair q.1 q.2} : ℝ) ≤
      ∑ A' : Q.parts, ∑ B' : Q.parts with
        Finpartition.refinementParent hQP A' ≠ Finpartition.refinementParent hQP B', b A' B' := by
  set T := S.glueOffDiag hQP e L hLrev
  set Ω := (univ ×ˢ univ : Finset (Q.parts × Q.parts)).filter fun AB ↦
    Finpartition.refinementParent hQP AB.1 ≠ Finpartition.refinementParent hQP AB.2
  have hsub : (univ.filter fun q : V × V ↦ T.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2) ⊆
      Ω.biUnion fun AB ↦
        {q ∈ AB.1.1 ×ˢ AB.2.1 | T.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} := by
    intro ⟨u, v⟩ hq
    have hne := (mem_filter.1 hq).2
    have huv : u ≠ v := fun h ↦ by simp [h] at hne
    have hPne : P.part u ≠ P.part v := fun hP ↦ hne <| by
      rw [colorOfPair_of_ne _ huv, colorOfPair_of_ne _ huv]; simp [T, glueOffDiag, hP]
    let A' : Q.parts := ⟨Q.part u, Q.part_mem.2 (mem_univ _)⟩
    let B' : Q.parts := ⟨Q.part v, Q.part_mem.2 (mem_univ _)⟩
    have hpar : Finpartition.refinementParent hQP A' ≠ Finpartition.refinementParent hQP B' :=
      fun heq ↦ hPne <| by
        rw [Finpartition.part_eq_refinementParent hQP A' (Q.mem_part (mem_univ u)), heq,
          Finpartition.part_eq_refinementParent hQP B' (Q.mem_part (mem_univ v))]
    exact mem_biUnion.2 ⟨(A', B'), mem_filter.2 ⟨mem_product.2 ⟨mem_univ _, mem_univ _⟩, hpar⟩,
      mem_filter.2 ⟨mem_product.2 ⟨Q.mem_part (mem_univ u), Q.mem_part (mem_univ v)⟩, hne⟩⟩
  have hblock {A' B' : Q.parts}
      (hP : Finpartition.refinementParent hQP A' ≠ Finpartition.refinementParent hQP B') :
      (#{q ∈ A'.1 ×ˢ B'.1 | T.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤ b A' B' := by
    rcases lt_or_gt_of_ne (fun he ↦ hP (congrArg _ (e.injective he))) with hlt | hgt
    · have heq : {q ∈ A'.1 ×ˢ B'.1 | T.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
          {q ∈ A'.1 ×ˢ B'.1 | (L A' B').colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} :=
        filter_congr fun q hq ↦ by
          rw [glueOffDiag_colorOfPair_of_lt hQP e L hLrev hP hlt (mem_product.1 hq).1
            (mem_product.1 hq).2]
      exact heq ▸ hb A' B' hP
    · have heq : {q ∈ A'.1 ×ˢ B'.1 | T.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
          {q ∈ A'.1 ×ˢ B'.1 | (L B' A').colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} :=
        filter_congr fun q hq ↦ by
          rw [glueOffDiag_colorOfPair_of_gt hQP e L hLrev hP hgt (mem_product.1 hq).1
            (mem_product.1 hq).2]
      rw [heq, card_colorOfPair_ne_swap (hLrev B' A'), hb_symm A' B']
      exact hb B' A' hP.symm
  calc (#{q : V × V | T.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ)
      ≤ ∑ AB ∈ Ω, (#{q ∈ AB.1.1 ×ˢ AB.2.1 | T.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) :=
        mod_cast (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ AB ∈ Ω, b AB.1 AB.2 := sum_le_sum fun AB hAB ↦ hblock (mem_filter.1 hAB).2
    _ = _ := by simp only [Ω, sum_filter, sum_product]

/-- **Gluing local fine-block recolorings across `Q ≤ P`.** Suppose for every ordered pair of fine
parts `(A', B')` of `Q ≤ P` lying in distinct coarse parts `(A, B)` of `P` there is a local
pair-color system with reversal `S.rev`, edit count on `A' ×ˢ B'` at most `b A' B'` (`b` symmetric),
and rectangle count discrepancy at most `η * (#A' * #B')` around `p A B`
(`p B A c = p A B (S.rev c)`). Then there is a single `T : PairColorSystem κ V` with `T.rev = S.rev`
that preserves all colors within parts of `P`, edits at most
`∑ A', ∑ B' (in different P-part), b A' B'` ordered pairs of `V × V`, and has rectangle count
discrepancy at most `η * (#A * #B)` around `p A B` on every pair `A ≠ B` of parts of `P`. -/
theorem exists_offDiag_recoloring_of_refines [DecidableEq κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P)
    {p : Finset V → Finset V → κ → ℝ} (hp_swap : ∀ A B c, p B A c = p A B (S.rev c))
    {b : Q.parts → Q.parts → ℝ} (hb_symm : ∀ A' B', b A' B' = b B' A') {η : ℝ}
    (hloc : ∀ A' B' : Q.parts,
      Finpartition.refinementParent hQP A' ≠ Finpartition.refinementParent hQP B' →
      ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
        (#{q ∈ A'.1 ×ˢ B'.1 | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤ b A' B' ∧
        ∀ c, ∀ s' ⊆ A'.1, ∀ t' ⊆ B'.1,
          |(#{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some c} : ℝ) -
            p (Finpartition.refinementParent hQP A').1
              (Finpartition.refinementParent hQP B').1 c * (#s' * #t')| ≤
            η * (#A'.1 * #B'.1)) :
    ∃ T : PairColorSystem κ V, T.rev = S.rev ∧
      (∀ u v, P.part u = P.part v → T.colorOfPair u v = S.colorOfPair u v) ∧
      (#{q : V × V | T.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        (∑ A' : Q.parts, ∑ B' : Q.parts with
          Finpartition.refinementParent hQP A' ≠ Finpartition.refinementParent hQP B', b A' B') ∧
      ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c, ∀ X ⊆ A, ∀ Y ⊆ B,
        |(#{q ∈ X ×ˢ Y | T.colorOfPair q.1 q.2 = some c} : ℝ) - p A B c * (#X * #Y)| ≤
          η * (#A * #B) := by
  classical
  let e : Q.parts ≃ Fin #Q.parts :=
    (Fintype.equivFin Q.parts).trans (finCongr (Fintype.card_coe Q.parts))
  let L (A' B' : Q.parts) : PairColorSystem κ V :=
    if h : Finpartition.refinementParent hQP A' ≠ Finpartition.refinementParent hQP B'
    then (hloc A' B' h).choose else S
  have hL {A' B' : Q.parts}
      (h : Finpartition.refinementParent hQP A' ≠ Finpartition.refinementParent hQP B') :
      L A' B' = (hloc A' B' h).choose := dite_eq_left h
  have hLrev (A' B' : Q.parts) : (L A' B').rev = S.rev := by
    by_cases h : Finpartition.refinementParent hQP A' ≠ Finpartition.refinementParent hQP B'
    · rw [hL h]; exact (hloc A' B' h).choose_spec.1
    · simp only [L, dite_eq_right h]
  let T := S.glueOffDiag hQP e L hLrev
  refine ⟨T, rfl, fun u v hP ↦ ?_, card_glueOffDiag_colorOfPair_ne_le hQP e L hLrev hb_symm
    fun A' B' h ↦ hL h ▸ (hloc A' B' h).choose_spec.2.1, fun A hA B hB hAB c X hX Y hY ↦ ?_⟩
  · by_cases huv : u = v
    · simp [huv]
    rw [colorOfPair_of_ne _ huv, colorOfPair_of_ne _ huv]
    simp [T, glueOffDiag, hP]
  · refine T.abs_card_filter_colorOfPair_sub_le_of_refines hQP hA hB
      (fun A' hA' hA'A B' hB' hB'B c' s' hs' t' ht' ↦ ?_) c hX hY
    let qA : Q.parts := ⟨A', hA'⟩
    let qB : Q.parts := ⟨B', hB'⟩
    have hpA : (Finpartition.refinementParent hQP qA).1 = A :=
      congrArg Subtype.val ((Finpartition.refinementParent_eq_iff hQP (B := qA) (A := ⟨A, hA⟩)).2
        hA'A)
    have hpB : (Finpartition.refinementParent hQP qB).1 = B :=
      congrArg Subtype.val ((Finpartition.refinementParent_eq_iff hQP (B := qB) (A := ⟨B, hB⟩)).2
        hB'B)
    have hpar : Finpartition.refinementParent hQP qA ≠ Finpartition.refinementParent hQP qB :=
      fun heq ↦ hAB (hpA.symm.trans ((congrArg Subtype.val heq).trans hpB))
    rcases lt_or_gt_of_ne (fun he ↦ hpar (congrArg _ (e.injective he))) with hlt | hgt
    · have hfilter : {q ∈ s' ×ˢ t' | T.colorOfPair q.1 q.2 = some c'} =
          {q ∈ s' ×ˢ t' | (L qA qB).colorOfPair q.1 q.2 = some c'} :=
        filter_congr fun q hq ↦ by
          rw [glueOffDiag_colorOfPair_of_lt hQP e L hLrev hpar hlt
            (hs' (mem_product.1 hq).1) (ht' (mem_product.1 hq).2)]
      have hspec := (hloc qA qB hpar).choose_spec.2.2 c' s' hs' t' ht'
      rwa [hfilter, hL hpar, ← hpA, ← hpB]
    · have hfilter : {q ∈ s' ×ˢ t' | T.colorOfPair q.1 q.2 = some c'} =
          {q ∈ s' ×ˢ t' | (L qB qA).colorOfPair q.1 q.2 = some c'} :=
        filter_congr fun q hq ↦ by
          rw [glueOffDiag_colorOfPair_of_gt hQP e L hLrev hpar hgt
            (hs' (mem_product.1 hq).1) (ht' (mem_product.1 hq).2)]
      have hswap := abs_card_filter_colorOfPair_sub_le_swap (S := S) (p := p B A) (η := η)
        (hLrev qB qA)
        (fun c'' u' hu' v' hv' ↦ by
          have hspec := (hloc qB qA hpar.symm).choose_spec.2.2 c'' u' hu' v' hv'
          rwa [hL hpar.symm, ← hpB, ← hpA])
        c' s' hs' t' ht'
      rwa [hp_swap A B (S.rev c'), S.rev_rev, ← hfilter] at hswap

end GlueOffDiag

end TauCeti.PairColorSystem
