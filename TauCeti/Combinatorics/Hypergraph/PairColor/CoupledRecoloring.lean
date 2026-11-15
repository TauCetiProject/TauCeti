/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Recoloring
public import TauCeti.Order.Partition.Finpartition
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Combinatorics.Enumerative.CoupledColoring
import TauCeti.Combinatorics.Enumerative.RandomColoring
import TauCeti.Combinatorics.SimpleGraph.Density

/-!
# Coupled low-edit recolorings of pair-color systems

When regularizing a pair-color system by editing few pairs, recoloring a disjoint pair `(s, t)`
from scratch (`TauCeti.PairColorSystem.exists_recoloring_isRegularPair`) edits a constant fraction
of `s ×ˢ t` even when `S` already has densities on `(s, t)` close to the target distribution `p`.
When `(s, t)` is already `δ`-regular for `S`, coupling `S`'s colors on `s ×ˢ t` to `p` via
`TauCeti.exists_recoloring_card_filter_ne_lt` keeps the edit count on `s ×ˢ t` at most the total
variation count `(1 / 2) (∑ c, |d_c(s, t) - p c|) #s #t` plus `ε ^ 3 #s #t`, while every
subrectangle `s' ×ˢ t'` (`s' ⊆ s`, `t' ⊆ t`) has color-count discrepancy at most
`(ε ^ 3 + card κ * δ) #s #t` around `p`
(`TauCeti.PairColorSystem.exists_coupled_recoloring_abs_card_filter_sub_le`).

Working directly with subrectangle *count* discrepancy (holding on all `s' ⊆ s`, `t' ⊆ t` without
any minimum-size threshold) allows fine-block recolorings along a refinement `Q ≤ P` to be summed
additively onto coarse cell pairs `(A, B)` of `P`
(`TauCeti.PairColorSystem.abs_card_filter_colorOfPair_sub_le_of_refines`) and glued into a single
coherent `PairColorSystem` (`TauCeti.PairColorSystem.exists_offDiag_recoloring_of_refines`).

## Main results

* `TauCeti.PairColorSystem.exists_coupled_recoloring_abs_card_filter_sub_le`: coupled recoloring of
  a `δ`-regular disjoint pair `(s, t)` toward target densities `p`, controlling both edit count and
  all subrectangle color counts.
* `TauCeti.PairColorSystem.abs_card_filter_colorOfPair_sub_le_of_refines`: summing fine-block
  rectangle count discrepancy along `Q ≤ P` onto coarse cell pairs.
* `TauCeti.PairColorSystem.exists_offDiag_recoloring_of_refines`: gluing local fine-block
  recolorings across all off-diagonal coarse pairs of `Q ≤ P` into one global `PairColorSystem`.

## References

* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), Lemma 4.3.
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Lemma 4.2.
-/

public section

open Finset

namespace TauCeti.PairColorSystem

variable {κ V : Type*}

/-- Specialize `two_mul_two_pow_mul_two_pow_add_mul_exp_lt` to `r = 1` and `δ = ε ^ 3 / card κ` on
the rectangle family `s.powerset ×ˢ t.powerset`. -/
private theorem coupled_powerset_exp_lt [Fintype κ] [Nonempty κ] {s t : Finset V} {ε : ℝ}
    (hs : (Fintype.card κ : ℝ) ^ 2 * (Fintype.card κ + 2) ≤ ε ^ 6 * #s)
    (ht : (Fintype.card κ : ℝ) ^ 2 * (Fintype.card κ + 2) ≤ ε ^ 6 * #t) :
    2 * (Fintype.card ↥(s.powerset ×ˢ t.powerset) + 1) * Fintype.card κ *
      Real.exp (-2 * ((ε ^ 3 * #s * #t) / Fintype.card κ) ^ 2 / (#s * #t : ℕ)) < 1 := by
  have hK2 : (0 : ℝ) < (Fintype.card κ : ℝ) ^ 2 := by
    have : 0 < Fintype.card κ := Fintype.card_pos
    positivity
  have hdiv {u : Finset V}
      (hu : (Fintype.card κ : ℝ) ^ 2 * (Fintype.card κ + 2) ≤ ε ^ 6 * #u) :
      (Fintype.card κ : ℝ) + 1 + 1 ≤ (ε ^ 3 / Fintype.card κ) ^ 2 * #u := by
    have h1 := (le_div_iff₀' hK2).2 hu
    have h2 : ε ^ 6 * #u / (Fintype.card κ : ℝ) ^ 2 = (ε ^ 3 / Fintype.card κ) ^ 2 * #u := by ring
    linarith
  have hub := two_mul_two_pow_mul_two_pow_add_mul_exp_lt (κ := κ) zero_le_one (hdiv hs) (hdiv ht)
  have harg : (ε ^ 3 * #s * #t) / (Fintype.card κ : ℝ) =
      (ε ^ 3 / Fintype.card κ) * #s * #t := by ring
  rw [harg]
  simpa [card_product, card_powerset] using hub

/-- Summing `IsRegularPair.abs_card_filter_colorOfPair_sub_le` over all colors `c₀ : κ` bounds the
total subrectangle count discrepancy by `card κ * (δ * #s * #t)`. -/
private theorem sum_abs_card_filter_colorOfPair_sub_le [Fintype κ] [DecidableEq κ]
    {S : PairColorSystem κ V} {s t s' t' : Finset V} {δ : ℝ} (hst : Disjoint s t)
    (hreg : S.IsRegularPair δ s t) (hs' : s' ⊆ s) (ht' : t' ⊆ t) :
    ∑ c₀, |(#{q ∈ s' ×ˢ t' | S.colorOfPair q.1 q.2 = some c₀} : ℝ) -
      pairColorDensity S c₀ s t * #(s' ×ˢ t')| ≤ Fintype.card κ * (δ * #s * #t) :=
  (sum_le_sum (g := fun _ ↦ δ * #s * #t) fun c₀ _ ↦ by
    rw [card_product, Nat.cast_mul, ← mul_assoc]
    exact hreg.abs_card_filter_colorOfPair_sub_le hst hs' ht').trans_eq
    (by rw [sum_const, card_univ, nsmul_eq_mul])

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
  let : DecidableEq V := Classical.typeDecidableEq V
  have : Nonempty κ :=
    Classical.byContradiction fun hκ ↦ by have := not_nonempty_iff.1 hκ; simp at hp1
  have hs0 : (0 : ℝ) < #s :=
    pos_of_mul_pos_right (lt_of_lt_of_le (by positivity) hs) (by positivity)
  have ht0 : (0 : ℝ) < #t :=
    pos_of_mul_pos_right (lt_of_lt_of_le (by positivity) ht) (by positivity)
  let y : V × V → κ := fun q ↦ if h : q.1 ≠ q.2 then S.color ⟨q, h⟩ else Classical.arbitrary κ
  have hy_iff {q : V × V} (hq : q ∈ s ×ˢ t) (c : κ) : y q = c ↔ S.colorOfPair q.1 q.2 = some c := by
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
    (coupled_powerset_exp_lt hs ht)
  refine ⟨S.recolorProduct hst x, S.recolorProduct_rev hst x,
    fun u v ↦ colorOfPair_recolorProduct_of_not_mem hst x, ?_, fun c s' hs' t' ht' ↦ ?_⟩
  · have hne_eq : #{q ∈ s ×ˢ t | (S.recolorProduct hst x).colorOfPair q.1 q.2 ≠
        S.colorOfPair q.1 q.2} = #{q ∈ s ×ˢ t | x q ≠ y q} :=
      congrArg card (filter_congr fun ⟨u, v⟩ hq ↦ by
        rw [colorOfPair_recolorProduct_of_mem hst x hq, ne_eq, eq_comm, ← hy_iff hq, eq_comm])
    have htv : ∑ c, |(#{q ∈ s ×ˢ t | y q = c} : ℝ) - p c * #(s ×ˢ t)| =
        (∑ c, |(pairColorDensity S c s t : ℝ) - p c|) * (#s * #t) := by
      rw [sum_mul]; exact sum_congr rfl fun c _ ↦ by
        rw [hy_st, card_product, Nat.cast_mul, ← sub_mul, abs_mul, abs_of_pos (mul_pos hs0 ht0)]
    rw [hne_eq]; linarith [hne_lt]
  · have hdev := hrect ⟨(s', t'), mem_product.2 ⟨mem_powerset.2 hs', mem_powerset.2 ht'⟩⟩ c
    have hx_eq : #{q ∈ s' ×ˢ t' | (S.recolorProduct hst x).colorOfPair q.1 q.2 = some c} =
        #{q ∈ s' ×ˢ t' | x q = c} :=
      congrArg card (filter_congr fun q hq ↦ by
        rw [colorOfPair_recolorProduct_of_mem hst x (product_subset_product hs' ht' hq),
          Option.some_inj])
    have hy_sum : ∑ c₀, |(#{q ∈ s' ×ˢ t' | y q = c₀} : ℝ) -
        (#{q ∈ s ×ˢ t | y q = c₀} : ℝ) / #(s ×ˢ t) * #(s' ×ˢ t')| ≤
        Fintype.card κ * (δ * #s * #t) :=
      (sum_congr rfl fun c₀ _ ↦ by
        rw [hy_st c₀, hy_card hs' ht', card_product s t, Nat.cast_mul,
          mul_div_cancel_right₀ _ (mul_pos hs0 ht0).ne']).trans_le
        (sum_abs_card_filter_colorOfPair_sub_le hst hreg hs' ht')
    rw [hx_eq, ← Nat.cast_mul, ← card_product]; linarith

/-- Rectangle count discrepancy on `t' ×ˢ s'` around `d` for color `S.rev c` transfers to
`s' ×ˢ t'` around `d` for color `c` whenever `S'.rev = S.rev`. -/
private theorem abs_card_filter_colorOfPair_sub_le_swap [DecidableEq κ]
    {S S' : PairColorSystem κ V} (hrev : S'.rev = S.rev) {s t s' t' : Finset V}
    {c : κ} {d η : ℝ}
    (h : |(#{q ∈ t' ×ˢ s' | S'.colorOfPair q.1 q.2 = some (S.rev c)} : ℝ) - d * (#t' * #s')| ≤
      η * (#t * #s)) :
    |(#{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some c} : ℝ) - d * (#s' * #t')| ≤
      η * (#s * #t) := by
  have hcard : #{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some c} =
      #{q ∈ t' ×ˢ s' | S'.colorOfPair q.1 q.2 = some (S.rev c)} := by
    apply card_equiv (Equiv.prodComm V V)
    rintro ⟨u, v⟩
    simp only [mem_filter, mem_product, Equiv.prodComm_apply, Prod.swap_prod_mk, ← hrev]
    rw [and_comm (a := u ∈ s'), S'.colorOfPair_swap_eq_some_iff u v c]
  rw [hcard, mul_comm (#s' : ℝ) #t', mul_comm (#s : ℝ) #t]
  exact h

/-- **Coarse rectangle discrepancy from fine blocks.** Let `Q ≤ P` be finite partitions of `u`, and
let `A, B ∈ P.parts` be coarse parts. If for `X ⊆ A`, `Y ⊆ B`, and a color `c`, every pair
`(A', B')` of fine parts in `A` and `B` has count discrepancy at most `η * (#A' * #B')` around `d`
on `(X ∩ A') ×ˢ (Y ∩ B')`, then `X ×ˢ Y` has count discrepancy at most `η * (#A * #B)` around
`d`. -/
theorem abs_card_filter_colorOfPair_sub_le_of_refines [DecidableEq V] [DecidableEq κ]
    (T : PairColorSystem κ V) {u : Finset V} {P Q : Finpartition u} (hQP : Q ≤ P)
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) {d η : ℝ}
    (c : κ) {X Y : Finset V} (hX : X ⊆ A) (hY : Y ⊆ B)
    (hfine : ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B →
      |(#{q ∈ (X ∩ A') ×ˢ (Y ∩ B') | T.colorOfPair q.1 q.2 = some c} : ℝ) -
        d * (#(X ∩ A') * #(Y ∩ B'))| ≤ η * (#A' * #B')) :
    |(#{q ∈ X ×ˢ Y | T.colorOfPair q.1 q.2 = some c} : ℝ) - d * (#X * #Y)| ≤
      η * (#A * #B) := by
  let pA : P.parts := ⟨A, hA⟩
  let pB : P.parts := ⟨B, hB⟩
  set QA : Finset Q.parts := {A' | Finpartition.refinementParent hQP A' = pA}
  set QB : Finset Q.parts := {B' | Finpartition.refinementParent hQP B' = pB}
  let r (x y : V) : Prop := T.colorOfPair x y = some c
  have hinter (s t : Finset V) :
      {q ∈ s ×ˢ t | T.colorOfPair q.1 q.2 = some c} = Rel.interedges r s t := rfl
  have hXA : QA.biUnion (fun A' ↦ X ∩ A'.1) = X := by
    rw [← inter_biUnion, Finpartition.biUnion_filter_refinementParent_eq hQP pA,
      inter_eq_left.2 hX]
  have hYB : QB.biUnion (fun B' ↦ Y ∩ B'.1) = Y := by
    rw [← inter_biUnion, Finpartition.biUnion_filter_refinementParent_eq hQP pB,
      inter_eq_left.2 hY]
  have hXcard : (#X : ℝ) = ∑ A' ∈ QA, (#(X ∩ A'.1) : ℝ) := by
    exact_mod_cast (congrArg card (inter_eq_left.2 hX).symm).trans
      (Finpartition.sum_card_inter_filter_refinementParent_eq hQP pA X).symm
  have hYcard : (#Y : ℝ) = ∑ B' ∈ QB, (#(Y ∩ B'.1) : ℝ) := by
    exact_mod_cast (congrArg card (inter_eq_left.2 hY).symm).trans
      (Finpartition.sum_card_inter_filter_refinementParent_eq hQP pB Y).symm
  have hAcard : (#A : ℝ) = ∑ A' ∈ QA, (#A'.1 : ℝ) := by
    exact_mod_cast (Finpartition.sum_card_filter_refinementParent_eq hQP pA).symm
  have hBcard : (#B : ℝ) = ∑ B' ∈ QB, (#B'.1 : ℝ) := by
    exact_mod_cast (Finpartition.sum_card_filter_refinementParent_eq hQP pB).symm
  have hcount : (#{q ∈ X ×ˢ Y | T.colorOfPair q.1 q.2 = some c} : ℝ) =
      ∑ A' ∈ QA, ∑ B' ∈ QB,
        (#{q ∈ (X ∩ A'.1) ×ˢ (Y ∩ B'.1) | T.colorOfPair q.1 q.2 = some c} : ℝ) := by
    simp_rw [hinter]
    have hnat : #(Rel.interedges r X Y) =
        ∑ A' ∈ QA, ∑ B' ∈ QB, #(Rel.interedges r (X ∩ A'.1) (Y ∩ B'.1)) := by
      conv_lhs => rw [← hXA, ← hYB]
      rw [Rel.card_interedges_biUnion_left r QA _ _
        ((Q.pairwiseDisjoint_subtype_val _).mono fun _ ↦ inter_subset_right)]
      exact sum_congr rfl fun A' _ ↦ Rel.card_interedges_biUnion_right r _ QB _
        ((Q.pairwiseDisjoint_subtype_val _).mono fun _ ↦ inter_subset_right)
    exact_mod_cast hnat
  have hmean : d * (#X * #Y) = ∑ A' ∈ QA, ∑ B' ∈ QB, d * (#(X ∩ A'.1) * #(Y ∩ B'.1)) := by
    rw [hXcard, hYcard, sum_mul_sum, mul_sum]
    exact sum_congr rfl fun _ _ ↦ mul_sum _ _ _
  rw [hcount, hmean, ← sum_sub_distrib, hAcard, hBcard, sum_mul_sum, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun A' hA' ↦ ?_)
  rw [← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun B' hB' ↦ ?_)
  exact hfine A'.1 A'.2 ((Finpartition.refinementParent_eq_iff hQP).1 (mem_filter.1 hA').2)
    B'.1 B'.2 ((Finpartition.refinementParent_eq_iff hQP).1 (mem_filter.1 hB').2)

/-- Two pair-color systems sharing `S.rev` have the same number of disagreements with `S` on
`s ×ˢ t` and on `t ×ˢ s`. -/
private theorem card_colorOfPair_ne_swap [DecidableEq κ] {S S' : PairColorSystem κ V}
    (hrev : S'.rev = S.rev) (s t : Finset V) :
    #{q ∈ s ×ˢ t | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
      #{q ∈ t ×ˢ s | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} := by
  apply card_equiv (Equiv.prodComm V V)
  rintro ⟨u, v⟩
  have hinj := Option.map_injective S.rev_involutive.injective
  have heq : S'.colorOfPair v u = S.colorOfPair v u ↔ S'.colorOfPair u v = S.colorOfPair u v := by
    rw [← hinj.eq_iff, ← S.colorOfPair_swap v u, ← hrev, ← S'.colorOfPair_swap v u]
  simp only [Equiv.prodComm_apply, Prod.swap_prod_mk, mem_filter, mem_product, ne_eq]
  rw [and_comm (a := u ∈ s), heq]

section OffDiagGluing

variable [Fintype V] [DecidableEq V]

/-- When local systems on `Q ≤ P` default to `S` on same-parent fine pairs, a cellwise gluing
preserving `S.rev` agrees with `S` on every pair within a single coarse cell of `P`. -/
private theorem recoloring_agrees_of_part_eq {S R : PairColorSystem κ V}
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (order : LinearOrder Q.parts)
    (L : Q.parts → Q.parts → PairColorSystem κ V) (hRrev : R.rev = S.rev)
    (hlocal : ∀ A' B' : Q.parts, order.le A' B' → ∀ x ∈ A'.1, ∀ y ∈ B'.1,
      R.colorOfPair x y = (L A' B').colorOfPair x y)
    (hLdiag : ∀ A' B', Finpartition.refinementParent hQP A' =
      Finpartition.refinementParent hQP B' → L A' B' = S)
    {u v : V} (hP : P.part u = P.part v) :
    R.colorOfPair u v = S.colorOfPair u v := by
  let : LinearOrder Q.parts := order
  let : LE Q.parts := order.toLE
  let qU : Q.parts := ⟨Q.part u, Q.part_mem.2 (mem_univ u)⟩
  let qV : Q.parts := ⟨Q.part v, Q.part_mem.2 (mem_univ v)⟩
  have hu : u ∈ qU.1 := Q.mem_part (mem_univ u)
  have hv : v ∈ qV.1 := Q.mem_part (mem_univ v)
  have hpar : Finpartition.refinementParent hQP qU = Finpartition.refinementParent hQP qV :=
    Subtype.ext <| (Finpartition.part_eq_refinementParent hQP qU hu).symm.trans
      (hP.trans (Finpartition.part_eq_refinementParent hQP qV hv))
  rcases le_total qU qV with hle | hle
  · rw [hlocal qU qV hle u hu v hv, hLdiag qU qV hpar]
  · rw [R.colorOfPair_swap v u, S.colorOfPair_swap v u, hRrev,
      hlocal qV qU hle v hv u hu, hLdiag qV qU hpar.symm]

/-- Bound global ordered-pair edits of a cellwise gluing across `Q ≤ P` by summing symmetric
fine-block edit bounds over all ordered fine pairs lying in distinct coarse parts. -/
private theorem card_colorOfPair_ne_le_of_cellwise [DecidableEq κ] {S R : PairColorSystem κ V}
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (order : LinearOrder Q.parts)
    (L : Q.parts → Q.parts → PairColorSystem κ V) (hRrev : R.rev = S.rev)
    (hlocal : ∀ A' B' : Q.parts, order.le A' B' → ∀ x ∈ A'.1, ∀ y ∈ B'.1,
      R.colorOfPair x y = (L A' B').colorOfPair x y)
    (hdiag : ∀ u v, P.part u = P.part v → R.colorOfPair u v = S.colorOfPair u v)
    {b : Q.parts → Q.parts → ℝ}
    (hb_symm : ∀ A' B', Finpartition.refinementParent hQP A' ≠
      Finpartition.refinementParent hQP B' → b A' B' = b B' A')
    (hb : ∀ A' B', Finpartition.refinementParent hQP A' ≠ Finpartition.refinementParent hQP B' →
      (#{q ∈ A'.1 ×ˢ B'.1 | (L A' B').colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        b A' B') :
    (#{q : V × V | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
      ∑ A' : Q.parts, ∑ B' : Q.parts with
        Finpartition.refinementParent hQP A' ≠ Finpartition.refinementParent hQP B', b A' B' := by
  let : LinearOrder Q.parts := order
  let : LE Q.parts := order.toLE
  set Ω := (univ ×ˢ univ : Finset (Q.parts × Q.parts)).filter fun AB ↦
    Finpartition.refinementParent hQP AB.1 ≠ Finpartition.refinementParent hQP AB.2
  have hsub : (univ.filter fun q : V × V ↦ R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2) ⊆
      Ω.biUnion fun AB ↦
        {q ∈ AB.1.1 ×ˢ AB.2.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} := by
    intro ⟨u, v⟩ hq
    have hne := (mem_filter.1 hq).2
    have hPne : P.part u ≠ P.part v := fun hP ↦ hne (hdiag u v hP)
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
      (#{q ∈ A'.1 ×ˢ B'.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤ b A' B' := by
    rcases le_total A' B' with hle | hle
    · have heq : {q ∈ A'.1 ×ˢ B'.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
          {q ∈ A'.1 ×ˢ B'.1 | (L A' B').colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} :=
        filter_congr fun q hq ↦ by
          rw [hlocal A' B' hle q.1 (mem_product.1 hq).1 q.2 (mem_product.1 hq).2]
      exact heq ▸ hb A' B' hP
    · rw [card_colorOfPair_ne_swap hRrev A'.1 B'.1, hb_symm A' B' hP]
      have heq : {q ∈ B'.1 ×ˢ A'.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
          {q ∈ B'.1 ×ˢ A'.1 | (L B' A').colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} :=
        filter_congr fun q hq ↦ by
          rw [hlocal B' A' hle q.1 (mem_product.1 hq).1 q.2 (mem_product.1 hq).2]
      exact heq ▸ hb B' A' hP.symm
  calc (#{q : V × V | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ)
      ≤ ∑ AB ∈ Ω, (#{q ∈ AB.1.1 ×ˢ AB.2.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) :=
        mod_cast (card_le_card hsub).trans card_biUnion_le
    _ ≤ ∑ AB ∈ Ω, b AB.1 AB.2 := sum_le_sum fun AB hAB ↦ hblock (mem_filter.1 hAB).2
    _ = _ := by simp only [Ω, sum_filter, sum_product]

/-- Aggregate fine-block rectangle bounds across `Q ≤ P` for a cellwise-glued system `R`, using
`hp_swap` on reversed fine pairs `qB ≤ qA`. -/
private theorem abs_card_filter_colorOfPair_le_of_cellwise [DecidableEq κ]
    {S R : PairColorSystem κ V} {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P)
    (order : LinearOrder Q.parts) (L : Q.parts → Q.parts → PairColorSystem κ V)
    {p : Finset V → Finset V → κ → ℝ} {η : ℝ}
    (hp_swap : ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c, p B A c = p A B (S.rev c))
    (hRrev : R.rev = S.rev)
    (hlocal : ∀ A' B', order.le A' B' → ∀ x ∈ A'.1, ∀ y ∈ B'.1,
      R.colorOfPair x y = (L A' B').colorOfPair x y)
    (hLrect : ∀ A' B' : Q.parts,
      Finpartition.refinementParent hQP A' ≠ Finpartition.refinementParent hQP B' →
      ∀ c, ∀ s' ⊆ A'.1, ∀ t' ⊆ B'.1,
        |(#{q ∈ s' ×ˢ t' | (L A' B').colorOfPair q.1 q.2 = some c} : ℝ) -
          p (Finpartition.refinementParent hQP A').1
            (Finpartition.refinementParent hQP B').1 c * (#s' * #t')| ≤
          η * (#A'.1 * #B'.1))
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B)
    (c : κ) {X Y : Finset V} (hX : X ⊆ A) (hY : Y ⊆ B) :
    |(#{q ∈ X ×ˢ Y | R.colorOfPair q.1 q.2 = some c} : ℝ) - p A B c * (#X * #Y)| ≤
      η * (#A * #B) := by
  let : LinearOrder Q.parts := order
  let : LE Q.parts := order.toLE
  refine R.abs_card_filter_colorOfPair_sub_le_of_refines hQP hA hB c hX hY
    fun A' hA' hA'A B' hB' hB'B ↦ ?_
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
  rcases le_total qA qB with hle | hle
  · have hfilter : {q ∈ (X ∩ A') ×ˢ (Y ∩ B') | R.colorOfPair q.1 q.2 = some c} =
        {q ∈ (X ∩ A') ×ˢ (Y ∩ B') | (L qA qB).colorOfPair q.1 q.2 = some c} :=
      filter_congr fun q hq ↦ by
        rw [hlocal qA qB hle q.1 (inter_subset_right (mem_product.1 hq).1)
          q.2 (inter_subset_right (mem_product.1 hq).2)]
    have hpAB : p A B c =
        p (Finpartition.refinementParent hQP qA).1 (Finpartition.refinementParent hQP qB).1 c := by
      rw [hpA, hpB]
    rw [hfilter, hpAB]
    exact hLrect qA qB hpar c (X ∩ A') inter_subset_right (Y ∩ B') inter_subset_right
  · refine abs_card_filter_colorOfPair_sub_le_swap hRrev ?_
    have hfilter : {q ∈ (Y ∩ B') ×ˢ (X ∩ A') | R.colorOfPair q.1 q.2 = some (S.rev c)} =
        {q ∈ (Y ∩ B') ×ˢ (X ∩ A') | (L qB qA).colorOfPair q.1 q.2 = some (S.rev c)} :=
      filter_congr fun q hq ↦ by
        rw [hlocal qB qA hle q.1 (inter_subset_right (mem_product.1 hq).1)
          q.2 (inter_subset_right (mem_product.1 hq).2)]
    have hpAB : p A B c = p (Finpartition.refinementParent hQP qB).1
        (Finpartition.refinementParent hQP qA).1 (S.rev c) := by
      rw [hpB, hpA, hp_swap A hA B hB hAB (S.rev c), S.rev_rev]
    rw [hfilter, hpAB]
    exact hLrect qB qA hpar.symm (S.rev c) (Y ∩ B') inter_subset_right (X ∩ A') inter_subset_right

/-- **Gluing local fine-block recolorings across `Q ≤ P`.** Suppose for every ordered pair of fine
parts `(A', B')` of `Q ≤ P` lying in distinct coarse parts `(A, B)` of `P` there is a local
pair-color system with reversal `S.rev`, edit count on `A' ×ˢ B'` at most `b A' B'` (`b` symmetric
on off-diagonal fine pairs), and rectangle count discrepancy at most `η * (#A' * #B')` around
`p A B` (`p B A c = p A B (S.rev c)` on distinct coarse parts). Then there is a single
`T : PairColorSystem κ V` with `T.rev = S.rev` that preserves all colors within parts of `P`, edits
at most `∑ A', ∑ B' (in different P-part), b A' B'` ordered pairs of `V × V`, and has rectangle
count discrepancy at most `η * (#A * #B)` around `p A B` on every pair `A ≠ B` of parts of `P`. -/
theorem exists_offDiag_recoloring_of_refines [DecidableEq κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P)
    {p : Finset V → Finset V → κ → ℝ}
    (hp_swap : ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c, p B A c = p A B (S.rev c))
    {b : Q.parts → Q.parts → ℝ}
    (hb_symm : ∀ A' B', Finpartition.refinementParent hQP A' ≠
      Finpartition.refinementParent hQP B' → b A' B' = b B' A')
    {η : ℝ}
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
  let order : LinearOrder Q.parts := LinearOrder.lift' (Fintype.equivFin Q.parts)
    (Fintype.equivFin Q.parts).injective
  let L (A' B' : Q.parts) : PairColorSystem κ V :=
    if h : Finpartition.refinementParent hQP A' ≠ Finpartition.refinementParent hQP B'
    then (hloc A' B' h).choose else S
  have hL {A' B' : Q.parts}
      (h : Finpartition.refinementParent hQP A' ≠ Finpartition.refinementParent hQP B') :
      L A' B' = (hloc A' B' h).choose := dite_eq_left h
  have hLdiag (A' B' : Q.parts)
      (h : Finpartition.refinementParent hQP A' = Finpartition.refinementParent hQP B') :
      L A' B' = S := dite_eq_right (not_not.2 h)
  have hLrev (A' B' : Q.parts) : (L A' B').rev = S.rev := by
    by_cases h : Finpartition.refinementParent hQP A' ≠ Finpartition.refinementParent hQP B'
    · rw [hL h]; exact (hloc A' B' h).choose_spec.1
    · simp only [L, dite_eq_right h]
  obtain ⟨R, hRrev, hlocal⟩ := S.exists_cellwise_recoloring Q order L fun A' B' _ ↦ hLrev A' B'
  have hdiag (u v : V) (hP : P.part u = P.part v) : R.colorOfPair u v = S.colorOfPair u v :=
    recoloring_agrees_of_part_eq hQP order L hRrev hlocal hLdiag hP
  refine ⟨R, hRrev, hdiag, card_colorOfPair_ne_le_of_cellwise hQP order L hRrev hlocal hdiag
    hb_symm (fun A' B' h ↦ hL h ▸ (hloc A' B' h).choose_spec.2.1),
    fun A hA B hB hAB c X hX Y hY ↦
      abs_card_filter_colorOfPair_le_of_cellwise hQP order L hp_swap hRrev hlocal
        (fun A' B' h ↦ hL h ▸ (hloc A' B' h).choose_spec.2.2) hA hB hAB c hX hY⟩

end OffDiagGluing

end TauCeti.PairColorSystem
