/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Colored.EditDiscrepancy
public import TauCeti.Combinatorics.Hypergraph.Triadic.StrongTopRegularization

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Order.BigOperators.Sum.PosPart
import TauCeti.Combinatorics.Enumerative.RandomColoring
import TauCeti.Combinatorics.Hypergraph.Colored.Stability
import TauCeti.Combinatorics.Hypergraph.Polyad.Perm
import TauCeti.Combinatorics.Hypergraph.Polyad.Rank

/-!
# Coupled triple recoloring and strong top-regular approximation

Strong top regularization (`Colored3Graph.exists_strong_topRegularOverMostPolyads`) produces a
coarse complex `C` and a fine palette refinement `D` with arbitrarily small polyad energy gap `g`
such that the original coloring `H` is top-regular over most polyads of `D` at schedules evaluated
at `C.complexity`. Passing top regularity directly down to `C` without modifying `H`
(`Colored3Graph.TopRegularOverMostPolyads.of_polyadEnergy_sub_le`) forces the energy gap `g` to
be smaller than the coarse tolerance and exceptional mass, so only the rank can be scheduled at
`C.complexity` while the top tolerance must stay fixed in advance.

Allowing a small global edit discrepancy `H.Approximates3 H' ε` removes that obstruction. On each
sufficiently large fine polyad `Q` over `D.skeleton`, we couple `H` to a recoloring `H'` whose
target color distribution is the coarse parent density `c ↦ H.relativeDensity c (Q.coarsen hV f)`:

1. **Simplex transition coupling:** between the fine density `p c = H.relativeDensity c Q` and the
   coarse parent density `q c = H.relativeDensity c (Q.coarsen hV f)`, a stochastic transition
   matrix `M` pushes `p` forward to `q` while moving at most `|p c₀ - q c₀|` mass out of each
   diagonal entry `c₀`.
2. **Orbit-glued low-discrepancy recoloring:** unordered 3-subsets are grouped by the
   `Equiv.Perm (Fin 3)`-orbits of their fine polyads (`Polyad3.perm`), on which `#Q.support`,
   `H.relativeDensity c Q`, and `H.relativeDensity c (Q.coarsen hV f)` are all invariant. Applying
   `TauCeti.exists_forall_abs_card_filter_sub_mul_card_lt` to each old color class and all six
   ordered-fiber multiplicities across all six role permutations yields a single unordered coloring
   `H'` whose subpolyad color counts on every good fine child track `H.relativeDensity c P` while
   its global edit discrepancy is controlled by `g`.
3. **Rank amplification on the coarse complex:** summing over the fine children of a coarse polyad
   `P` gives rank-one top regularity of `H'` over `P` at `δ² / 2 ^ r`, which
   `Colored3Graph.IsTopRegularOverPolyad.of_rank_one_div_pow` amplifies to rank `r` at `δ`
   (`Colored3Graph.TopRegularOverMostPolyads.exists_approximates3_of_polyadEnergy_sub_le`).

Combining this coupled recoloring with `Colored3Graph.exists_strong_topRegularOverMostPolyads` at
fine rank one yields `Colored3Graph.exists_approximates3_topRegularOverMostPolyads`: for any fixed
edit budget `ε > 0` and any schedules `δ μ : ℕ → ℝ` and `r : ℕ → ℕ`, every lower skeleton `S` on a
sufficiently large vertex set admits a bounded palette refinement `C` and an `ε`-close coloring
`H'` that is `(δ C.complexity, r C.complexity)`-top-regular off a `μ C.complexity`-proportion of
the polyads of `C`.

## Main definitions

* `TauCeti.topRegularApproximationPaletteBound`: host-independent bound on `C.pairColorCount`.
* `TauCeti.topRegularApproximationCardBound`: host-size threshold for the probabilistic recoloring
  and small-polyad mass estimates.

## Main results

* `TauCeti.Colored3Graph.TopRegularOverMostPolyads.exists_approximates3_of_polyadEnergy_sub_le`:
  coupled recoloring from fine rank-one top regularity across a small polyad energy gap to coarse
  rank-`r` top regularity.
* `TauCeti.Colored3Graph.exists_approximates3_topRegularOverMostPolyads`: scheduled strong
  top-regular approximation over any lower skeleton.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Lemma 4.2 and Theorem 2.5 (regular approximation).
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), Lemma 4.2 (regular approximation via fine-to-coarse recoloring).
* N. Alon and J. H. Spencer, *The Probabilistic Method*, 4th ed., Wiley (2016), Theorem 13.1.1.
-/

public section

open Finset

namespace TauCeti

section Helpers

/-- Between any two probability distributions `p` and `q` on a finite palette `κ`, there is a
row-stochastic transition matrix `M` pushing `p` forward to `q` whose off-diagonal mass from each
state `c₀` is at most `|p c₀ - q c₀|`. -/
private theorem exists_transition_coupling {κ : Type*} [Fintype κ] {p q : κ → ℝ}
    (hp1 : ∑ c, p c = 1) (hq : ∀ c, 0 ≤ q c) (hq1 : ∑ c, q c = 1) :
    ∃ M : κ → κ → ℝ,
      (∀ c₀ c, 0 ≤ M c₀ c) ∧
      (∀ c₀, ∑ c, M c₀ c = 1) ∧
      (∀ c, ∑ c₀, p c₀ * M c₀ c = q c) ∧
      ∀ c₀, p c₀ * (1 - M c₀ c₀) ≤ |p c₀ - q c₀| := by
  classical
  let pos : κ → ℝ := fun c ↦ max (p c - q c) 0
  let neg : κ → ℝ := fun c ↦ max (q c - p c) 0
  set Δ : ℝ := ∑ c, pos c
  have hbal : ∑ c, (p c - q c) = 0 := by rw [sum_sub_distrib, hp1, hq1, sub_self]
  have hneg_sum : ∑ c, neg c = Δ := by
    simpa only [neg, pos, neg_sub] using sum_max_neg_eq_sum_max univ (fun c ↦ p c - q c) hbal
  have hpos (c : κ) : 0 ≤ pos c := le_max_right _ _
  have hneg (c : κ) : 0 ≤ neg c := le_max_right _ _
  have hΔ0 : 0 ≤ Δ := sum_nonneg fun c _ ↦ hpos c
  by_cases hΔ : Δ = 0
  · have hpeq (c : κ) : p c = q c := by
      have h1 : pos c ≤ 0 := hΔ ▸ single_le_sum (fun k _ ↦ hpos k) (mem_univ c)
      have h2 : neg c ≤ 0 := (hneg_sum.trans hΔ) ▸ single_le_sum (fun k _ ↦ hneg k) (mem_univ c)
      have h1' : p c - q c ≤ 0 := (le_max_left _ _).trans h1
      have h2' : q c - p c ≤ 0 := (le_max_left _ _).trans h2
      linarith
    refine ⟨fun c₀ c ↦ if c = c₀ then 1 else 0, fun c₀ c ↦ by dsimp only; split_ifs <;> norm_num,
      fun c₀ ↦ by simp, fun c ↦ by simp [hpeq c], fun c₀ ↦ by simp⟩
  · have hΔpos : 0 < Δ := lt_of_le_of_ne hΔ0 (Ne.symm hΔ)
    let M : κ → κ → ℝ := fun c₀ c ↦
      if q c₀ < p c₀ then
        (if c = c₀ then q c₀ / p c₀ else 0) + (pos c₀ / p c₀) * (neg c / Δ)
      else
        if c = c₀ then 1 else 0
    have hM0 (c₀ c : κ) : 0 ≤ M c₀ c := by
      dsimp only [M]
      by_cases h : q c₀ < p c₀ <;> by_cases hc : c = c₀ <;> simp only [h, hc, ↓reduceIte]
      · have hp0 : 0 < p c₀ := (hq c₀).trans_lt h
        have hq0 := hq c₀
        positivity
      · have hp0 : 0 < p c₀ := (hq c₀).trans_lt h
        positivity
      · norm_num
      · norm_num
    have hMsum (c₀ : κ) : ∑ c, M c₀ c = 1 := by
      dsimp only [M]
      split_ifs with h
      · have hp0 : 0 < p c₀ := (hq c₀).trans_lt h
        have hpos_eq : pos c₀ = p c₀ - q c₀ := max_eq_left (sub_nonneg.2 h.le)
        rw [sum_add_distrib, sum_ite_eq' univ c₀]
        simp only [mem_univ, ↓reduceIte]
        rw [← mul_sum, ← sum_div, hneg_sum, div_self hΔpos.ne', mul_one, hpos_eq]
        field_simp
        ring
      · simp
    -- On both branches, multiplying `M c₀ c` by `p c₀` gives a single smooth formula.
    have hpM (c₀ c : κ) :
        p c₀ * M c₀ c = (if c = c₀ then min (p c₀) (q c₀) else 0) + pos c₀ * (neg c / Δ) := by
      dsimp only [M]
      by_cases h : q c₀ < p c₀ <;> by_cases hc : c = c₀
      · have hp0 : 0 < p c₀ := (hq c₀).trans_lt h
        simp only [h, hc, ↓reduceIte, min_eq_right h.le]
        rw [mul_add, mul_div_cancel₀ _ hp0.ne', ← mul_assoc, mul_div_cancel₀ _ hp0.ne']
      · have hp0 : 0 < p c₀ := (hq c₀).trans_lt h
        simp only [h, hc, ↓reduceIte, zero_add]
        rw [← mul_assoc, mul_div_cancel₀ _ hp0.ne']
      · have hle : p c₀ ≤ q c₀ := not_lt.1 h
        simp [h, hc, min_eq_left hle, show pos c₀ = 0 from max_eq_right (sub_nonpos.2 hle)]
      · have hle : p c₀ ≤ q c₀ := not_lt.1 h
        simp [h, hc, show pos c₀ = 0 from max_eq_right (sub_nonpos.2 hle)]
    refine ⟨M, hM0, hMsum, fun c ↦ ?_, fun c₀ ↦ ?_⟩
    · simp_rw [hpM]
      rw [sum_add_distrib, sum_ite_eq univ c]
      simp only [mem_univ, ↓reduceIte]
      rw [← sum_mul, show ∑ c₀, pos c₀ = Δ from rfl, mul_div_cancel₀ _ hΔpos.ne']
      rcases le_total (p c) (q c) with hle | hle
      · rw [min_eq_left hle, show neg c = q c - p c from max_eq_left (sub_nonneg.2 hle)]
        ring
      · rw [min_eq_right hle, show neg c = 0 from max_eq_right (sub_nonpos.2 hle)]
        ring
    · have hex : 0 ≤ pos c₀ * (neg c₀ / Δ) :=
        mul_nonneg (hpos c₀) (div_nonneg (hneg c₀) hΔpos.le)
      have hdiag : p c₀ * M c₀ c₀ = min (p c₀) (q c₀) + pos c₀ * (neg c₀ / Δ) := by
        simpa using hpM c₀ c₀
      have hle1 : p c₀ * (1 - M c₀ c₀) ≤ p c₀ - min (p c₀) (q c₀) := by linarith
      refine hle1.trans ?_
      rcases le_total (p c₀) (q c₀) with hle | hle
      · rw [min_eq_left hle, sub_self]
        exact abs_nonneg _
      · rw [min_eq_right hle, abs_of_nonneg (sub_nonneg.2 hle)]

/-- Every polyad on `V` has at most `2 ^ (3 * |V|²)` subpolyads, since a subpolyad is determined
by three subsets of the off-diagonal ordered pairs. -/
private theorem card_subpolyad3_le {κ₂ V : Type*} [Fintype V] [DecidableEq V]
    {S : PairSkeleton3 κ₂ V} (P : Polyad3 S) :
    Fintype.card (Subpolyad3 P) ≤ 2 ^ (3 * Fintype.card V ^ 2) := by
  let encode : Subpolyad3 P →
      Finset {p : V × V // p.1 ≠ p.2} ×
        Finset {p : V × V // p.1 ≠ p.2} ×
        Finset {p : V × V // p.1 ≠ p.2} :=
    fun Q ↦ (Q.pair₀₁, Q.pair₀₂, Q.pair₁₂)
  have hinj : Function.Injective encode := fun Q R h ↦ by
    simp only [encode, Prod.mk.injEq] at h
    exact Subpolyad3.ext_data h.1 h.2.1 h.2.2
  have hpair : Fintype.card {p : V × V // p.1 ≠ p.2} ≤ Fintype.card V ^ 2 :=
    (Fintype.card_subtype_le _).trans_eq (by rw [Fintype.card_prod, sq])
  have hfin : Fintype.card (Finset {p : V × V // p.1 ≠ p.2}) ≤ 2 ^ (Fintype.card V ^ 2) := by
    rw [Fintype.card_finset]
    exact Nat.pow_le_pow_right two_pos hpair
  calc Fintype.card (Subpolyad3 P)
      ≤ Fintype.card (Finset {p : V × V // p.1 ≠ p.2} ×
          Finset {p : V × V // p.1 ≠ p.2} ×
          Finset {p : V × V // p.1 ≠ p.2}) := Fintype.card_le_of_injective encode hinj
    _ = Fintype.card (Finset {p : V × V // p.1 ≠ p.2}) *
          (Fintype.card (Finset {p : V × V // p.1 ≠ p.2}) *
            Fintype.card (Finset {p : V × V // p.1 ≠ p.2})) := by
        simp only [Fintype.card_prod]
    _ ≤ 2 ^ (Fintype.card V ^ 2) * (2 ^ (Fintype.card V ^ 2) * 2 ^ (Fintype.card V ^ 2)) :=
        Nat.mul_le_mul hfin (Nat.mul_le_mul hfin hfin)
    _ = 2 ^ (3 * Fintype.card V ^ 2) := by
        rw [← pow_add, ← pow_add]
        congr 1
        ring

/-- Index type for the discrepancy tests attached to a canonical orbit representative `Q₀`: a
role permutation `σ`, a subpolyad of `Q₀.perm σ`, and an ordered-fiber multiplicity `k + 1` in
`{1, …, 6}`. -/
private abbrev TestIdx {κ₂ V : Type*} [Fintype V] [DecidableEq V] {T : PairSkeleton3 κ₂ V}
    (Q₀ : Polyad3 T) : Type _ :=
  Σ σ : Equiv.Perm (Fin 3), Subpolyad3 (Q₀.perm σ) × Fin 6

private theorem card_testIdx_le {κ₂ V : Type*} [Fintype V] [DecidableEq V]
    {T : PairSkeleton3 κ₂ V} (Q₀ : Polyad3 T) :
    Fintype.card (TestIdx Q₀) ≤ 36 * 2 ^ (3 * Fintype.card V ^ 2) := by
  classical
  dsimp only [TestIdx]
  rw [Fintype.card_sigma]
  calc ∑ σ : Equiv.Perm (Fin 3), Fintype.card (Subpolyad3 (Q₀.perm σ) × Fin 6)
      ≤ ∑ _σ : Equiv.Perm (Fin 3), 2 ^ (3 * Fintype.card V ^ 2) * 6 := by
        refine sum_le_sum fun σ _ ↦ ?_
        rw [Fintype.card_prod, Fintype.card_fin]
        exact Nat.mul_le_mul_right 6 (card_subpolyad3_le (Q₀.perm σ))
    _ = 36 * 2 ^ (3 * Fintype.card V ^ 2) := by
        rw [sum_const, card_univ, Fintype.card_perm, Fintype.card_fin, smul_eq_mul]
        norm_num [Nat.factorial]
        ring

open Real in
/-- The polynomial support lower bound `221 * (3 |V|² + |κ| + 7) ≤ β² N₀` ensures both positivity
of `N₀` and the Hoeffding union-bound inequality for `TestIdx Q₀` at deviation `(β / 21) #Q₀`. -/
private theorem testIdx_union_bound {κ κ₂ V : Type*} [Fintype κ] [Nonempty κ] [Fintype V]
    [DecidableEq V] {T : PairSkeleton3 κ₂ V} {β N₀ : ℝ} (hβ : 0 < β)
    (hN₀ : 221 * (3 * (Fintype.card V : ℝ) ^ 2 + Fintype.card κ + 7) ≤ β ^ 2 * N₀)
    (Q₀ : Polyad3 T) (hQ₀ : N₀ ≤ (#Q₀.support : ℝ)) :
    0 < (β / 21) * (#Q₀.support : ℝ) ∧
      2 * Fintype.card (TestIdx Q₀) * Fintype.card κ *
        exp (-2 * ((β / 21) * (#Q₀.support : ℝ)) ^ 2 / (#Q₀.support : ℝ)) < 1 := by
  set n := Fintype.card V
  set B : ℝ := 3 * (n : ℝ) ^ 2 + Fintype.card κ + 7
  have hBpos : 0 < B := by positivity
  have hN₀pos : 0 < N₀ := by
    by_contra! hle
    have : β ^ 2 * N₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
    linarith [mul_pos (by norm_num : (0 : ℝ) < 221) hBpos]
  have hQpos : (0 : ℝ) < #Q₀.support := hN₀pos.trans_le hQ₀
  refine ⟨by positivity, ?_⟩
  -- Bound `2 * card (TestIdx Q₀)` and `card κ` by exponentials.
  have hcard2 : (2 * Fintype.card (TestIdx Q₀) : ℕ) ≤ 2 ^ (3 * n ^ 2 + 7) := by
    have h1 := Nat.mul_le_mul_left 2 (card_testIdx_le Q₀)
    calc 2 * Fintype.card (TestIdx Q₀)
        ≤ 72 * 2 ^ (3 * n ^ 2) := by linarith
      _ ≤ 128 * 2 ^ (3 * n ^ 2) := by gcongr; norm_num
      _ = 2 ^ (3 * n ^ 2 + 7) := by rw [pow_add]; ring
  have h2exp : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have hIexp : (2 : ℝ) * Fintype.card (TestIdx Q₀) ≤ exp (3 * (n : ℝ) ^ 2 + 7) := by
    have hcast : (2 : ℝ) * Fintype.card (TestIdx Q₀) ≤ (2 : ℝ) ^ (3 * n ^ 2 + 7) := by
      exact_mod_cast hcard2
    refine hcast.trans ?_
    calc (2 : ℝ) ^ (3 * n ^ 2 + 7)
        ≤ exp 1 ^ (3 * n ^ 2 + 7) := pow_le_pow_left₀ (by norm_num) h2exp _
      _ = exp ((3 * n ^ 2 + 7 : ℕ) : ℝ) := by rw [← exp_nat_mul, mul_one]
      _ = exp (3 * (n : ℝ) ^ 2 + 7) := by push_cast; rfl
  have hKpos : (0 : ℝ) < Fintype.card κ := Nat.cast_pos.2 Fintype.card_pos
  have hKexp : (Fintype.card κ : ℝ) ≤ exp (Fintype.card κ) := by
    linarith [add_one_le_exp (Fintype.card κ : ℝ)]
  have hexp_eq : -2 * ((β / 21) * (#Q₀.support : ℝ)) ^ 2 / (#Q₀.support : ℝ) =
      -(2 / 441) * (β ^ 2 * (#Q₀.support : ℝ)) := by
    field_simp [hQpos.ne']
    ring
  have hBN : 221 * B ≤ β ^ 2 * (#Q₀.support : ℝ) :=
    hN₀.trans (mul_le_mul_of_nonneg_left hQ₀ (by positivity))
  have hexp_lt : -2 * ((β / 21) * (#Q₀.support : ℝ)) ^ 2 / (#Q₀.support : ℝ) < -B := by
    rw [hexp_eq]
    linarith
  calc 2 * (Fintype.card (TestIdx Q₀) : ℝ) * Fintype.card κ *
          exp (-2 * ((β / 21) * (#Q₀.support : ℝ)) ^ 2 / (#Q₀.support : ℝ))
      ≤ exp (3 * (n : ℝ) ^ 2 + 7) * exp (Fintype.card κ) *
          exp (-2 * ((β / 21) * (#Q₀.support : ℝ)) ^ 2 / (#Q₀.support : ℝ)) := by
        gcongr
    _ < exp (3 * (n : ℝ) ^ 2 + 7) * exp (Fintype.card κ) * exp (-B) := by
        gcongr
    _ = 1 := by
        rw [← exp_add, ← exp_add]
        have hsum : 3 * (n : ℝ) ^ 2 + 7 + Fintype.card κ + -B = 0 := by
          dsimp only [B]
          ring
        rw [hsum, exp_zero]

/-- Partitioning a finite set `W` of injective triples by unordered 3-subset `ofFinEmb` expresses
the count of triples in `W` satisfying an unordered predicate `P` as a weighted sum over the six
possible positive fiber multiplicities `1, …, 6`. -/
private theorem card_filter_ofFinEmb_eq_sum_fin6 {V : Type*} [Fintype V] [DecidableEq V]
    (W : Finset {x : Fin 3 → V // Function.Injective x})
    (P : Set.powersetCard V 3 → Prop) [DecidablePred P] :
    #{x ∈ W | P (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} =
      ∑ k : Fin 6, (k.1 + 1) * #{s : Set.powersetCard V 3 | P s ∧
        #{x ∈ W | Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ = s} = k.1 + 1} := by
  classical
  have hlhs : #{x ∈ W | P (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} =
      ∑ s : Set.powersetCard V 3,
        if P s then #{x ∈ W | Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ = s} else 0 := by
    rw [← sum_filter, card_eq_sum_card_fiberwise
      (f := fun x : {x : Fin 3 → V // Function.Injective x} ↦
        Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)
      (t := univ.filter P) (fun x hx ↦ mem_filter.2 ⟨mem_univ _, (mem_filter.1 hx).2⟩)]
    refine sum_congr rfl fun s hs ↦ congrArg card (ext fun x ↦ ?_)
    simp only [mem_filter]
    exact ⟨fun hx ↦ ⟨hx.1.1, hx.2⟩, fun hx ↦ ⟨⟨hx.1, hx.2 ▸ (mem_filter.1 hs).2⟩, hx.2⟩⟩
  have hrhs (k : Fin 6) :
      (k.1 + 1) * #{s : Set.powersetCard V 3 | P s ∧
          #{x ∈ W | Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ = s} = k.1 + 1} =
        ∑ s : Set.powersetCard V 3,
          if P s ∧ #{x ∈ W | Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ = s} = k.1 + 1 then k.1 + 1
          else 0 := by
    rw [← sum_filter, sum_const, smul_eq_mul, mul_comm]
  rw [hlhs]
  simp_rw [hrhs]
  rw [sum_comm]
  refine sum_congr rfl fun s _ ↦ ?_
  set ms := #{x ∈ W | Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ = s}
  have hms_le : ms ≤ 6 :=
    (card_le_card (filter_subset_filter _ (subset_univ W))).trans_eq
      ((card_filter_ofFinEmb_eq s).trans (by decide))
  by_cases hPs : P s
  · rcases ms.eq_zero_or_pos with hm0 | hmpos
    · simp [hPs, hm0]
    · have hklt : ms - 1 < 6 := by omega
      let k₀ : Fin 6 := ⟨ms - 1, hklt⟩
      simp only [hPs, ↓reduceIte, true_and]
      rw [sum_eq_single k₀]
      · simp [k₀, Nat.sub_add_cancel hmpos]
      · intro k _ hkne
        simp only [ite_eq_right_iff]
        intro hmk
        exact absurd (Fin.ext (by dsimp [k₀]; omega)) hkne
      · intro hk
        exact absurd (mem_univ k₀) hk
  · simp [hPs]

end Helpers

/-! ### Explicit bounds for scheduled top-regular approximation -/

/-- Host-independent upper bound on `C.pairColorCount` in
`Colored3Graph.exists_approximates3_topRegularOverMostPolyads`, starting from a lower skeleton
with `t` vertex cells and `m` pair colors over a top palette of size `q`. -/
noncomputable def topRegularApproximationPaletteBound (q t : ℕ) (ε : ℝ) (δ μ : ℕ → ℝ)
    (r : ℕ → ℕ) (m : ℕ) : ℕ :=
  strongTopRegularityBound t ((ε / (2 * ((q : ℝ) + 1))) ^ 2)
    (fun n ↦ ((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / (8 * ((q : ℝ) + 1)))
    (fun n ↦ μ n * (((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / 4) / 2)
    (fun _ ↦ 1) m

/-- Unfolding lemma for `topRegularApproximationPaletteBound`. -/
theorem topRegularApproximationPaletteBound_def (q t : ℕ) (ε : ℝ) (δ μ : ℕ → ℝ) (r : ℕ → ℕ)
    (m : ℕ) :
    topRegularApproximationPaletteBound q t ε δ μ r m =
      strongTopRegularityBound t ((ε / (2 * ((q : ℝ) + 1))) ^ 2)
        (fun n ↦ ((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / (8 * ((q : ℝ) + 1)))
        (fun n ↦ μ n * (((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / 4) / 2)
        (fun _ ↦ 1) m :=
  (rfl)

/-- Host-size threshold above which the Hoeffding recoloring union bound and the small-polyad
support bound hold simultaneously at every coarse complexity reachable within
`topRegularApproximationPaletteBound`. -/
noncomputable def topRegularApproximationCardBound (q t : ℕ) (ε : ℝ) (δ μ : ℕ → ℝ) (r : ℕ → ℕ)
    (m : ℕ) : ℕ :=
  let M := topRegularApproximationPaletteBound q t ε δ μ r m
  let η' : ℕ → ℝ := fun n ↦ ((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / (8 * ((q : ℝ) + 1))
  let μ' : ℕ → ℝ := fun n ↦ μ n * (((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / 4) / 2
  let M' := strongTopRegularityStep t η' μ' (fun _ ↦ 1) M
  let P : ℝ := ((t ^ 3 * M' ^ 3 + 1 : ℕ) : ℝ)
  let β : ℕ → ℝ := fun n ↦ min (ε / (2 * ((q : ℝ) + 1))) (η' n)
  max 4 ((range (t + M + t ^ 3 * M ^ 3 + 1)).sup fun n ↦
    ⌊4 * P * 221 * ((q : ℝ) + 10) / ((β n) ^ 2 * μ' n)⌋₊ + 1)

/-- Unfolding lemma for `topRegularApproximationCardBound`. -/
theorem topRegularApproximationCardBound_def (q t : ℕ) (ε : ℝ) (δ μ : ℕ → ℝ) (r : ℕ → ℕ)
    (m : ℕ) :
    topRegularApproximationCardBound q t ε δ μ r m =
      let M := topRegularApproximationPaletteBound q t ε δ μ r m
      let η' : ℕ → ℝ := fun n ↦ ((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / (8 * ((q : ℝ) + 1))
      let μ' : ℕ → ℝ := fun n ↦ μ n * (((δ n) ^ 2 / (2 : ℝ) ^ r n) ^ 2 / 4) / 2
      let M' := strongTopRegularityStep t η' μ' (fun _ ↦ 1) M
      let P : ℝ := ((t ^ 3 * M' ^ 3 + 1 : ℕ) : ℝ)
      let β : ℕ → ℝ := fun n ↦ min (ε / (2 * ((q : ℝ) + 1))) (η' n)
      max 4 ((range (t + M + t ^ 3 * M ^ 3 + 1)).sup fun n ↦
        ⌊4 * P * 221 * ((q : ℝ) + 10) / ((β n) ^ 2 * μ' n)⌋₊ + 1) :=
  (rfl)

namespace Colored3Graph

section EnergyGapRecoloring

variable {κ V : Type*} [Fintype V] [DecidableEq V] [DecidableEq κ]

open Classical in
/-- Local coarse regularity criterion after coupled recoloring: if on every large `(η, 1)`-regular
fine child `Q` of `P` the recolored subpolyad counts track `H.relativeDensity c P` within
`Fintype.card κ * (η + β) * #Q.support`, and the remaining fine children of `P` have total support
at most `θ * #P.support`, then `H'` is `(δ, r)`-top-regular over `P`. -/
private theorem isTopRegularOverPolyad_of_recolored_children [Fintype κ]
    {H H' : Colored3Graph κ V} {C D : TriadicComplex3 V} {η δ β θ N₀ : ℝ} {r : ℕ}
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    {P : Polyad3 C.skeleton} (hη : 0 ≤ η) (hδ : 0 < δ) (hβ : 0 < β)
    (htol : 2 * (Fintype.card κ * (η + β) + θ) ≤ (δ ^ 2 / (2 : ℝ) ^ r) ^ 2)
    (hgood : ∀ Q : Polyad3 D.skeleton, Q.coarsen hV f = P → N₀ ≤ (#Q.support : ℝ) →
      H.IsTopRegularOverPolyad Q η 1 → ∀ (c : κ) (S' : Subpolyad3 Q),
        |(H'.relDensityOn c S'.support : ℝ) - H.relativeDensity c P| * #S'.support ≤
          Fintype.card κ * (η + β) * #Q.support)
    (hbad : ∑ Q : Polyad3 D.skeleton with
        Q.coarsen hV f = P ∧ (¬N₀ ≤ (#Q.support : ℝ) ∨ ¬H.IsTopRegularOverPolyad Q η 1),
        (#Q.support : ℝ) ≤ θ * #P.support) :
    H'.IsTopRegularOverPolyad P δ r := by
  set δ₁ := δ ^ 2 / (2 : ℝ) ^ r
  have hδ₁ : 0 < δ₁ := by positivity
  set α := (Fintype.card κ : ℝ) * (η + β)
  have hα : 0 ≤ α := by positivity
  set B := ∑ Q : Polyad3 D.skeleton with
    Q.coarsen hV f = P ∧ (¬N₀ ≤ (#Q.support : ℝ) ∨ ¬H.IsTopRegularOverPolyad Q η 1),
    (#Q.support : ℝ)
  -- Every subpolyad `U` of `P` deviates from `H.relativeDensity c P` by at most `α #P + B`.
  have hU_dev (c : κ) (U : Subpolyad3 P) :
      |(H'.relDensityOn c U.support : ℝ) - H.relativeDensity c P| * #U.support ≤
        α * #P.support + B := by
    have hmiss (Q : Polyad3 D.skeleton) (hQ : Q.coarsen hV f ≠ P) :
        U.support ∩ Q.support = ∅ :=
      disjoint_iff_inter_eq_empty.1 ((Polyad3.pairwise_disjoint_support hQ.symm).mono
        U.support_subset (Polyad3.support_subset_coarsen hV f hf Q))
    calc |(H'.relDensityOn c U.support : ℝ) - H.relativeDensity c P| * #U.support
        = |∑ Q : Polyad3 D.skeleton, ((H'.relDensityOn c (U.support ∩ Q.support) : ℝ) -
            H.relativeDensity c P) * #(U.support ∩ Q.support)| := by
          rw [← H'.relDensityOn_sub_mul_card_eq_sum_inter_support D.skeleton, abs_mul,
            Nat.abs_cast]
      _ ≤ ∑ Q : Polyad3 D.skeleton with Q.coarsen hV f = P, (α * #Q.support +
            if ¬N₀ ≤ (#Q.support : ℝ) ∨ ¬H.IsTopRegularOverPolyad Q η 1 then (#Q.support : ℝ)
            else 0) := by
          rw [sum_filter]
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun Q _ ↦ ?_)
          by_cases hQP : Q.coarsen hV f = P
          · simp only [hQP, ↓reduceIte]
            rw [abs_mul, Nat.abs_cast]
            by_cases hQb : ¬N₀ ≤ (#Q.support : ℝ) ∨ ¬H.IsTopRegularOverPolyad Q η 1
            · simp only [hQb, ↓reduceIte]
              have h1 : |(H'.relDensityOn c (U.support ∩ Q.support) : ℝ) -
                  H.relativeDensity c P| ≤ 1 :=
                abs_sub_le_of_nonneg_of_le (mod_cast H'.relDensityOn_nonneg c _)
                  (mod_cast H'.relDensityOn_le_one c _) (mod_cast H.relativeDensity_nonneg c P)
                  (mod_cast H.relativeDensity_le_one c P)
              have h2 : (#(U.support ∩ Q.support) : ℝ) ≤ #Q.support := by
                exact_mod_cast card_le_card inter_subset_right
              nlinarith [Nat.cast_nonneg (α := ℝ) #(U.support ∩ Q.support),
                Nat.cast_nonneg (α := ℝ) #Q.support]
            · simp only [hQb, ↓reduceIte, add_zero]
              rw [not_or, not_not, not_not] at hQb
              simpa only [Subpolyad3.support_restrict] using
                hgood Q hQP hQb.1 hQb.2 c (U.restrict Q)
          · simp [hQP, hmiss Q hQP]
      _ = α * #P.support + B := by
          rw [sum_add_distrib, ← mul_sum, ← sum_filter, filter_filter]
          congr 2
          have hsum :
              ∑ Q : Polyad3 D.skeleton with Q.coarsen hV f = P, #Q.support = #P.support := by
            convert Polyad3.sum_card_support_coarsen hV f hf P
          exact_mod_cast hsum
  -- Specializing `U` to the full support of `P` compares `H'.relativeDensity c P` to `H` as well.
  have hP_dev (c : κ) :
      |(H'.relativeDensity c P : ℝ) - H.relativeDensity c P| * #P.support ≤
        α * #P.support + B := by
    simpa only [Subpolyad3.support_ofSubcells_cells, H'.relativeDensity_def] using
      hU_dev c (Subpolyad3.ofSubcells P P.c₀ P.c₁ P.c₂)
  -- Amplify from rank one at `δ₁ = δ² / 2 ^ r`.
  refine IsTopRegularOverPolyad.of_rank_one_div_pow ?_ hδ
  rw [isTopRegularOverPolyad_one_iff]
  intro c U hU
  obtain hP0 | hPpos := P.support.eq_empty_or_nonempty
  · have hU0 : U.support = ∅ := subset_empty.1 (hP0 ▸ U.support_subset)
    simpa [hU0, H'.relativeDensity_of_support_eq_empty c hP0] using hδ₁.le
  · have hUpos : (0 : ℝ) < #U.support := (mul_pos hδ₁ (Nat.cast_pos.2 hPpos.card_pos)).trans_le hU
    have hUP : (#U.support : ℝ) ≤ #P.support := by exact_mod_cast card_le_card U.support_subset
    have hbase : |(H'.relativeDensity c P : ℝ) - H.relativeDensity c P| * #U.support ≤
        α * #P.support + B :=
      (mul_le_mul_of_nonneg_left hUP (abs_nonneg _)).trans (hP_dev c)
    have htri : |(H'.relDensityOn c U.support : ℝ) - H'.relativeDensity c P| * #U.support ≤
        2 * (α + θ) * #P.support := by
      have hsplit : |(H'.relDensityOn c U.support : ℝ) - H'.relativeDensity c P| ≤
          |(H'.relDensityOn c U.support : ℝ) - H.relativeDensity c P| +
            |(H'.relativeDensity c P : ℝ) - H.relativeDensity c P| := by
        rw [abs_sub_comm (H'.relativeDensity c P : ℝ)]
        exact abs_sub_le _ _ _
      have hmul := mul_le_mul_of_nonneg_right hsplit hUpos.le
      rw [add_mul] at hmul
      linarith [hU_dev c U, hbase, hbad]
    have hfin : |(H'.relDensityOn c U.support : ℝ) - H'.relativeDensity c P| * #U.support ≤
        δ₁ * #U.support := by
      calc |(H'.relDensityOn c U.support : ℝ) - H'.relativeDensity c P| * #U.support
          ≤ 2 * (α + θ) * #P.support := htri
        _ ≤ δ₁ ^ 2 * #P.support := by gcongr
        _ ≤ δ₁ * #U.support := by nlinarith
    exact le_of_mul_le_mul_right hfin hUpos

/-- **Coupled triple recoloring across a small polyad energy gap.** Let `D` refine `C` along a
reversal-compatible pair-color projection `f`, both selecting polyad decompositions, and suppose
`H` is `(η, 1)`-top-regular over most polyads of `D` with polyad energy gap from `C` to `D` at
most `g`. When `N₀` satisfies the Hoeffding support bound `221 (3 |V|² + |κ| + 7) ≤ β² N₀` and
`2 (|κ| (η + β) + θ) ≤ (δ² / 2 ^ r)²`, there is a coloring `H'` within edit discrepancy
`|κ| (√g + β)` of `H` that is `(δ, r)`-top-regular over all polyads of `C` outside an exceptional
proportion bounded by `(μ + card (Polyad3 D.skeleton) * N₀ / |V|.descFactorial 3) / θ`. -/
theorem TopRegularOverMostPolyads.exists_approximates3_of_polyadEnergy_sub_le [Fintype κ]
    {H : Colored3Graph κ V} {C D : TriadicComplex3 V} {η μ δ β θ N₀ g : ℝ} {r : ℕ}
    (h : H.TopRegularOverMostPolyads D η μ 1)
    (hC : C.IsPolyadDecomposition) (hD : D.IsPolyadDecomposition)
    (hV : D.skeleton.vertexPart ≤ C.skeleton.vertexPart)
    (f : Fin D.pairColorCount → Fin C.pairColorCount)
    (hf : ∀ p, C.skeleton.pairColors.color p = f (D.skeleton.pairColors.color p))
    (hrev : ∀ c, f (D.skeleton.pairColors.rev c) = C.skeleton.pairColors.rev (f c))
    (hgap : H.polyadEnergy D.skeleton - H.polyadEnergy C.skeleton ≤ g)
    (hη : 0 ≤ η) (hδ : 0 < δ) (hβ : 0 < β) (hθ : 0 < θ)
    (hN₀ : 221 * (3 * (Fintype.card V : ℝ) ^ 2 + Fintype.card κ + 7) ≤ β ^ 2 * N₀)
    (htol : 2 * (Fintype.card κ * (η + β) + θ) ≤ (δ ^ 2 / (2 : ℝ) ^ r) ^ 2) :
    ∃ H' : Colored3Graph κ V,
      H.Approximates3 H' (Fintype.card κ * (√g + β)) ∧
      H'.TopRegularOverMostPolyads C δ
        ((μ + Fintype.card (Polyad3 D.skeleton) * N₀ /
          (Fintype.card V).descFactorial 3) / θ) r := by
  classical
  have hN₀_pos : 0 < N₀ := by
    by_contra! hle
    have : β ^ 2 * N₀ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hle
    have hpos : (0 : ℝ) < 221 * (3 * (Fintype.card V : ℝ) ^ 2 + Fintype.card κ + 7) := by
      positivity
    linarith
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · -- Over an empty top palette, `H` itself needs zero edits and every polyad is vacuously regular.
    refine ⟨H, ?_, ?_⟩
    · simp only [Fintype.card_eq_zero, Nat.cast_zero, zero_mul]
      exact H.approximates3_self le_rfl
    · refine topRegularOverMostPolyads_of_forall
        (fun P _ ↦ isTopRegularOverPolyad_iff.2 fun c ↦ isEmptyElim c) ?_
      have hμ0 := h.nonneg
      positivity
  -- Group fine polyads into `Equiv.Perm (Fin 3)`-orbits and choose a canonical representative.
  let orbit (Q : Polyad3 D.skeleton) : Finset (Polyad3 D.skeleton) :=
    univ.image fun σ : Equiv.Perm (Fin 3) ↦ Q.perm σ
  have horbit_perm (Q : Polyad3 D.skeleton) (σ : Equiv.Perm (Fin 3)) :
      orbit (Q.perm σ) = orbit Q := by
    ext R
    simp only [orbit, mem_image, mem_univ, true_and]
    exact ⟨fun ⟨τ, hτ⟩ ↦ ⟨σ * τ, by rw [← Q.perm_mul, hτ]⟩,
      fun ⟨τ, hτ⟩ ↦ ⟨σ⁻¹ * τ, by rw [← (Q.perm σ).perm_mul, Polyad3.perm_inv_self, hτ]⟩⟩
  let pick (O : Finset (Polyad3 D.skeleton)) (hO : ∃ Q₀, orbit Q₀ = O) : Polyad3 D.skeleton :=
    hO.choose
  have hpick_congr {O₁ O₂ : Finset (Polyad3 D.skeleton)} (hO : O₁ = O₂)
      (h₁ : ∃ Q₀, orbit Q₀ = O₁) (h₂ : ∃ Q₀, orbit Q₀ = O₂) : pick O₁ h₁ = pick O₂ h₂ := by
    subst hO
    rfl
  let canonPolyad (Q : Polyad3 D.skeleton) : Polyad3 D.skeleton := pick (orbit Q) ⟨Q, rfl⟩
  have hcanon_perm (Q : Polyad3 D.skeleton) : ∃ σ : Equiv.Perm (Fin 3),
      (canonPolyad Q).perm σ = Q := by
    have hmem : Q ∈ orbit (canonPolyad Q) := by
      have heq : orbit (canonPolyad Q) = orbit Q :=
        (⟨Q, rfl⟩ : ∃ Q₀, orbit Q₀ = orbit Q).choose_spec
      rw [heq]
      exact mem_image.2 ⟨1, mem_univ _, Q.perm_one⟩
    simpa only [orbit, mem_image, mem_univ, true_and] using hmem
  have hcanon_card (Q : Polyad3 D.skeleton) : #(canonPolyad Q).support = #Q.support := by
    obtain ⟨σ₀, hσ₀⟩ := hcanon_perm Q
    conv_rhs => rw [← hσ₀]
    exact ((canonPolyad Q).card_support_perm σ₀).symm
  -- Choose an ordering representative for each unordered triple `s` to assign its orbit.
  let rep (s : Set.powersetCard V 3) : {x : Fin 3 → V // Function.Injective x} :=
    let e := (Set.powersetCard.ofFinEmb_surjective 3 V s).choose
    ⟨e.1, e.2⟩
  have hrep (s : Set.powersetCard V 3) :
      Set.powersetCard.ofFinEmb 3 V ⟨(rep s).1, (rep s).2⟩ = s :=
    (Set.powersetCard.ofFinEmb_surjective 3 V s).choose_spec
  let canonTriple (s : Set.powersetCard V 3) : Polyad3 D.skeleton :=
    pick (orbit (Polyad3.ofTriple D.skeleton (rep s))) ⟨_, rfl⟩
  have hcanonTriple_eq {Q : Polyad3 D.skeleton} {x : {x : Fin 3 → V // Function.Injective x}}
      (hx : x ∈ Q.support) :
      canonTriple (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = canonPolyad Q := by
    set s := Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩
    obtain ⟨σ, hσ⟩ := (Set.powersetCard.ofFinEmb_eq_iff_exists_perm
      ⟨x.1, x.2⟩ ⟨(rep s).1, (rep s).2⟩).1 (hrep s).symm
    have hx_eq : x = ⟨(rep s).1 ∘ σ, (rep s).2.comp σ.injective⟩ := Subtype.ext hσ
    have hQ_eq : Q = (Polyad3.ofTriple D.skeleton (rep s)).perm σ := by
      rw [Polyad3.mem_support_iff_eq_ofTriple.1 hx, hx_eq, Polyad3.ofTriple_comp_perm]
    exact hpick_congr (by rw [hQ_eq, horbit_perm]) _ _
  -- Build a coupled transition matrix `M Q₀` and low-discrepancy colorings `φ Q₀ c₀` for each
  -- canonical representative `Q₀` with `N₀ ≤ #Q₀.support`.
  let L (Q₀ : Polyad3 D.skeleton) (c₀ : κ) (idx : TestIdx Q₀) :
      Finset (Set.powersetCard V 3) :=
    univ.filter fun s ↦ H.color s = c₀ ∧
      #{x ∈ idx.2.1.support | Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ = s} = idx.2.2.1 + 1
  have hL_card (Q₀ : Polyad3 D.skeleton) (c₀ : κ) (idx : TestIdx Q₀) :
      #(L Q₀ c₀ idx) ≤ #Q₀.support := by
    obtain ⟨σ, S', k⟩ := idx
    calc #(L Q₀ c₀ ⟨σ, S', k⟩)
        = ∑ _s ∈ L Q₀ c₀ ⟨σ, S', k⟩, 1 := by simp
      _ ≤ ∑ s ∈ L Q₀ c₀ ⟨σ, S', k⟩,
            #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ = s} := by
          refine sum_le_sum fun s hs ↦ ?_
          rw [(mem_filter.1 hs).2.2]
          omega
      _ ≤ ∑ s : Set.powersetCard V 3,
            #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ = s} :=
          sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ Nat.zero_le _
      _ = #S'.support :=
          (card_eq_sum_card_fiberwise fun _ _ ↦ mem_univ _).symm
      _ ≤ #(Q₀.perm σ).support := card_le_card S'.support_subset
      _ = #Q₀.support := Q₀.card_support_perm σ
  have hcouple (Q₀ : Polyad3 D.skeleton) :
      ∃ (M : κ → κ → ℝ) (φ : κ → Set.powersetCard V 3 → κ),
        N₀ ≤ (#Q₀.support : ℝ) →
          (∀ c₀ c, 0 ≤ M c₀ c) ∧
          (∀ c₀, ∑ c, M c₀ c = 1) ∧
          (∀ c, ∑ c₀, (H.relativeDensity c₀ Q₀ : ℝ) * M c₀ c =
            H.relativeDensity c (Q₀.coarsen hV f)) ∧
          (∀ c₀, (H.relativeDensity c₀ Q₀ : ℝ) * (1 - M c₀ c₀) ≤
            |(H.relativeDensity c₀ Q₀ : ℝ) - H.relativeDensity c₀ (Q₀.coarsen hV f)|) ∧
          ∀ c₀ (idx : TestIdx Q₀) c,
            |(#{s ∈ L Q₀ c₀ idx | φ c₀ s = c} : ℝ) - M c₀ c * #(L Q₀ c₀ idx)| <
              (β / 21) * #Q₀.support := by
    by_cases hQ₀ : N₀ ≤ (#Q₀.support : ℝ)
    · have hQ₀_ne : Q₀.support.Nonempty := card_pos.1 (by exact_mod_cast hN₀_pos.trans_le hQ₀)
      have hP₀_ne : (Q₀.coarsen hV f).support.Nonempty :=
        hQ₀_ne.mono (Polyad3.support_subset_coarsen hV f hf Q₀)
      obtain ⟨M, hM0, hM1, hMpush, hMdiag⟩ := exists_transition_coupling
        (p := fun c ↦ (H.relativeDensity c Q₀ : ℝ))
        (q := fun c ↦ (H.relativeDensity c (Q₀.coarsen hV f) : ℝ))
        (by exact_mod_cast H.sum_relativeDensity hQ₀_ne)
        (fun c ↦ mod_cast H.relativeDensity_nonneg c _)
        (by exact_mod_cast H.sum_relativeDensity hP₀_ne)
      obtain ⟨ha, hub⟩ := testIdx_union_bound (κ := κ) hβ hN₀ Q₀ hQ₀
      have hφ (c₀ : κ) : ∃ φ₀ : Set.powersetCard V 3 → κ, ∀ (idx : TestIdx Q₀) c,
          |(#{s ∈ L Q₀ c₀ idx | φ₀ s = c} : ℝ) - M c₀ c * #(L Q₀ c₀ idx)| <
            (β / 21) * #Q₀.support :=
        exists_forall_abs_card_filter_sub_mul_card_lt (hM0 c₀) (hM1 c₀) (L Q₀ c₀)
          (hL_card Q₀ c₀) ha hub
      choose φ hφ using hφ
      exact ⟨M, φ, fun _ ↦ ⟨hM0, hM1, hMpush, hMdiag, hφ⟩⟩
    · exact ⟨fun _ _ ↦ 0, fun c₀ _ ↦ c₀, fun h' ↦ absurd h' hQ₀⟩
  choose M φ hMφ using hcouple
  -- Assemble the global unordered-triple coloring `H'`.
  let H' : Colored3Graph κ V :=
    ⟨fun s ↦ if N₀ ≤ (#(canonTriple s).support : ℝ) then φ (canonTriple s) (H.color s) s
      else H.color s⟩
  -- Key count transfer on any subpolyad `S'` of any large fine polyad `Q`.
  have hsub_count {Q : Polyad3 D.skeleton} (hQ : N₀ ≤ (#Q.support : ℝ)) (S' : Subpolyad3 Q)
      (c₀ c : κ) :
      |(#{x ∈ S'.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
          H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℝ) -
        M (canonPolyad Q) c₀ c *
          #{x ∈ S'.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀}| ≤
        β * #Q.support := by
    set Q₀ := canonPolyad Q
    obtain ⟨σ₀, hσ₀⟩ := hcanon_perm Q
    have hQ₀_card : #Q₀.support = #Q.support := hcanon_card Q
    have hQ₀ : N₀ ≤ (#Q₀.support : ℝ) := by rwa [hQ₀_card]
    obtain ⟨-, -, -, -, hφ_disc⟩ := hMφ Q₀ hQ₀
    let S₀ : Subpolyad3 (Q₀.perm σ₀) :=
      S'.inclusion (hσ₀ ▸ Subset.rfl) (hσ₀ ▸ Subset.rfl) (hσ₀ ▸ Subset.rfl)
    have hS₀ : S₀.support = S'.support := Subpolyad3.support_inclusion _ _ _ S'
    -- On every triple `s` meeting `S'.support`, `canonTriple s = Q₀` so `H'.color s = φ Q₀ c₀ s`.
    have hH'_on_L (k : Fin 6) :
        #{s : Set.powersetCard V 3 | (H.color s = c₀ ∧ H'.color s = c) ∧
            #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ = s} = k.1 + 1} =
          #{s ∈ L Q₀ c₀ ⟨σ₀, S₀, k⟩ | φ Q₀ c₀ s = c} := by
      refine congrArg card (ext fun s ↦ ?_)
      simp only [L, mem_filter, mem_univ, true_and, hS₀]
      by_cases hm : #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ = s} = k.1 + 1
      · have hpos : 0 < #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ = s} := by
          omega
        obtain ⟨x, hx⟩ := card_pos.1 hpos
        obtain ⟨hxS, hxs⟩ := mem_filter.1 hx
        have hcan : canonTriple s = Q₀ := by
          rw [← hxs]
          exact hcanonTriple_eq (S'.support_subset hxS)
        by_cases hc₀ : H.color s = c₀ <;> simp [H', hcan, hQ₀, hc₀, hm]
      · simp [hm]
    have h1 := card_filter_ofFinEmb_eq_sum_fin6 S'.support fun s ↦ H.color s = c₀
    have h2 := card_filter_ofFinEmb_eq_sum_fin6 S'.support fun s ↦ H.color s = c₀ ∧ H'.color s = c
    rw [h1, h2]
    simp_rw [hH'_on_L]
    have h1' (k : Fin 6) :
        #{s : Set.powersetCard V 3 | H.color s = c₀ ∧
            #{x ∈ S'.support | Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩ = s} = k.1 + 1} =
          #(L Q₀ c₀ ⟨σ₀, S₀, k⟩) := by
      simp only [L, hS₀]
    simp_rw [h1']
    push_cast
    rw [mul_sum, ← sum_sub_distrib]
    calc |∑ k : Fin 6, ((k.1 + 1 : ℝ) * #{s ∈ L Q₀ c₀ ⟨σ₀, S₀, k⟩ | φ Q₀ c₀ s = c} -
            M Q₀ c₀ c * ((k.1 + 1 : ℝ) * #(L Q₀ c₀ ⟨σ₀, S₀, k⟩)))|
        = |∑ k : Fin 6, (k.1 + 1 : ℝ) *
            ((#{s ∈ L Q₀ c₀ ⟨σ₀, S₀, k⟩ | φ Q₀ c₀ s = c} : ℝ) -
              M Q₀ c₀ c * #(L Q₀ c₀ ⟨σ₀, S₀, k⟩))| := by
          congr 1
          refine sum_congr rfl fun k _ ↦ by ring
      _ ≤ ∑ k : Fin 6, |(k.1 + 1 : ℝ) *
            ((#{s ∈ L Q₀ c₀ ⟨σ₀, S₀, k⟩ | φ Q₀ c₀ s = c} : ℝ) -
              M Q₀ c₀ c * #(L Q₀ c₀ ⟨σ₀, S₀, k⟩))| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ k : Fin 6, (k.1 + 1 : ℝ) * ((β / 21) * #Q₀.support) := by
          refine sum_le_sum fun k _ ↦ ?_
          rw [abs_mul, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (hφ_disc c₀ ⟨σ₀, S₀, k⟩ c).le (by positivity)
      _ = β * #Q.support := by
          rw [← sum_mul, hQ₀_card]
          have hsum21 : ∑ k : Fin 6, ((k : ℕ) + 1 : ℝ) = 21 := by
            rw [Fin.sum_univ_six]
            norm_num
          rw [hsum21]
          ring
  -- Invariance of fine and coarse densities along `canonPolyad Q`.
  have hQ₀_dens (Q : Polyad3 D.skeleton) (c : κ) :
      H.relativeDensity c (canonPolyad Q) = H.relativeDensity c Q ∧
        H.relativeDensity c ((canonPolyad Q).coarsen hV f) =
          H.relativeDensity c (Q.coarsen hV f) := by
    obtain ⟨σ₀, hσ₀⟩ := hcanon_perm Q
    refine ⟨?_, ?_⟩
    · conv_rhs => rw [← hσ₀]
      exact (H.relativeDensity_perm c (canonPolyad Q) σ₀).symm
    · conv_rhs => rw [← hσ₀]
      rw [Polyad3.coarsen_perm _ _ hV f hrev, H.relativeDensity_perm]
  refine ⟨H', ?_, ?_⟩
  · -- Part 1: Global edit discrepancy `H.Approximates3 H' (card κ * (√g + β))`.
    have hedit_Q (Q : Polyad3 D.skeleton) :
        (#(H.editedOn H' Q.support) : ℝ) ≤
          (∑ c₀, #Q.support *
            |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)|) +
            Fintype.card κ * β * #Q.support := by
      by_cases hQ : N₀ ≤ (#Q.support : ℝ)
      · set Q₀ := canonPolyad Q
        have hQ₀ : N₀ ≤ (#Q₀.support : ℝ) := by rwa [hcanon_card Q]
        obtain ⟨-, -, -, hMdiag, -⟩ := hMφ Q₀ hQ₀
        -- Partition edited triples of `Q.support` by their old color `c₀`.
        have hpart : #(H.editedOn H' Q.support) =
            ∑ c₀ : κ, #{x ∈ Q.support |
              H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
              H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
                H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} := by
          rw [editedOn_def, card_eq_sum_card_fiberwise
            (f := fun x ↦ H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩))
            (t := univ) (fun _ _ ↦ mem_univ _)]
          refine sum_congr rfl fun c₀ _ ↦ congrArg card (ext fun x ↦ ?_)
          simp only [mem_filter]
          tauto
        rw [hpart, Nat.cast_sum]
        have hbound_c₀ (c₀ : κ) :
            (#{x ∈ Q.support |
                H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
                H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
                  H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ) ≤
              #Q.support *
                |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)| +
                β * #Q.support := by
          let S_full := Subpolyad3.ofSubcells Q Q.c₀ Q.c₁ Q.c₂
          have hkeep := hsub_count hQ S_full c₀ c₀
          rw [Subpolyad3.support_ofSubcells_cells] at hkeep
          have hsplit :
              #{x ∈ Q.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
                  H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
                    H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} +
                #{x ∈ Q.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
                  H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀} =
                #{x ∈ Q.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀} := by
            let s₀ := {x ∈ Q.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀}
            have hfilter :
                {x ∈ Q.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
                    H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
                      H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} =
                  s₀.filter fun x ↦ ¬H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ := by
              ext x
              simp only [s₀, mem_filter]
              exact ⟨fun ⟨hx, hc₀, hne⟩ ↦ ⟨⟨hx, hc₀⟩, fun hc' ↦ hne (hc₀.trans hc'.symm)⟩,
                fun ⟨⟨hx, hc₀⟩, hne⟩ ↦ ⟨hx, hc₀, fun hc' ↦ hne (hc'.symm.trans hc₀)⟩⟩
            have hfilter2 :
                {x ∈ Q.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
                    H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀} =
                  s₀.filter fun x ↦ H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ := by
              ext x
              simp only [s₀, mem_filter, and_assoc]
            rw [hfilter, hfilter2, add_comm]
            exact card_filter_add_card_filter_not _
          have hdens : (#{x ∈ Q.support |
              H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀} : ℝ) =
              (H.relativeDensity c₀ Q₀ : ℝ) * #Q.support := by
            rw [(hQ₀_dens Q c₀).1, H.relativeDensity_def]
            exact_mod_cast (H.relDensityOn_mul_card c₀ Q.support).symm
          have hkeep_lo : M Q₀ c₀ c₀ * ((H.relativeDensity c₀ Q₀ : ℝ) * #Q.support) -
              β * #Q.support ≤
              (#{x ∈ Q.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
                H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀} : ℝ) := by
            dsimp only [Q₀] at hdens ⊢
            rw [hdens] at hkeep
            linarith [(abs_le.1 hkeep).1]
          have hsplitR : (#{x ∈ Q.support |
                H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
                H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
                  H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ) +
              (#{x ∈ Q.support | H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
                H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀} : ℝ) =
              (H.relativeDensity c₀ Q₀ : ℝ) * #Q.support := by
            rw [← Nat.cast_add, hsplit, hdens]
          have hdiag_Q : (H.relativeDensity c₀ Q₀ : ℝ) * (1 - M Q₀ c₀ c₀) * #Q.support ≤
              |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)| *
                #Q.support := by
            rw [← (hQ₀_dens Q c₀).1, ← (hQ₀_dens Q c₀).2]
            exact mul_le_mul_of_nonneg_right (hMdiag c₀) (Nat.cast_nonneg _)
          nlinarith
        calc (∑ c₀ : κ, (#{x ∈ Q.support |
                H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
                H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) ≠
                  H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)} : ℝ))
            ≤ ∑ c₀ : κ, (#Q.support *
                |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)| +
                β * #Q.support) := sum_le_sum fun c₀ _ ↦ hbound_c₀ c₀
          _ = (∑ c₀, #Q.support *
                |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)|) +
                Fintype.card κ * β * #Q.support := by
              rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
              ring
      · -- Small fine polyads are untouched by `H'`, so they contribute zero edits.
        have hempty : H.editedOn H' Q.support = ∅ := by
          rw [eq_empty_iff_forall_notMem]
          intro x hx
          obtain ⟨hxQ, hne⟩ := (H.mem_editedOn H' Q.support x).1 hx
          have hcan := hcanonTriple_eq hxQ
          have hcard_eq : #(canonTriple (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)).support =
              #Q.support := by rw [hcan, hcanon_card Q]
          have hnot : ¬N₀ ≤
              (#(canonTriple (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩)).support : ℝ) := by
            simpa only [hcard_eq] using hQ
          exact hne (by simp [H', hnot])
        rw [hempty, card_empty, Nat.cast_zero]
        exact add_nonneg (sum_nonneg fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
          (by positivity)
    -- Sum `hedit_Q` over all fine polyads `Q`.
    have huniv : (univ : Finset {x : Fin 3 → V // Function.Injective x}) =
        univ.biUnion Polyad3.support :=
      (eq_univ_of_forall fun x ↦ mem_biUnion.2
        ⟨Polyad3.ofTriple D.skeleton x, mem_univ _, Polyad3.mem_support_ofTriple x⟩).symm
    have hedit_total : (#(H.editedOn H' univ) : ℝ) ≤
        Fintype.card κ * (√g + β) * (Fintype.card V : ℝ) ^ 3 := by
      have hbi : #(H.editedOn H' univ) = ∑ Q : Polyad3 D.skeleton, #(H.editedOn H' Q.support) := by
        conv_lhs => rw [huniv]
        exact H.card_editedOn_biUnion H' univ Polyad3.support
          fun _ _ _ _ hne ↦ Polyad3.pairwise_disjoint_support hne
      have hsumQ : ∑ Q : Polyad3 D.skeleton, (#Q.support : ℝ) =
          (Fintype.card V).descFactorial 3 := by
        rw [← Nat.cast_sum, ← card_biUnion fun _ _ _ _ hne ↦ Polyad3.pairwise_disjoint_support hne,
          ← huniv, card_univ, Fintype.card_subtype_injective, Fintype.card_fin]
      calc (#(H.editedOn H' univ) : ℝ)
          = ∑ Q : Polyad3 D.skeleton, (#(H.editedOn H' Q.support) : ℝ) := by exact_mod_cast hbi
        _ ≤ ∑ Q : Polyad3 D.skeleton, ((∑ c₀, #Q.support *
              |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)|) +
              Fintype.card κ * β * #Q.support) := sum_le_sum fun Q _ ↦ hedit_Q Q
        _ = (∑ c₀, ∑ Q : Polyad3 D.skeleton, #Q.support *
              |(H.relativeDensity c₀ Q : ℝ) - H.relativeDensity c₀ (Q.coarsen hV f)|) +
              Fintype.card κ * β * (Fintype.card V).descFactorial 3 := by
            rw [sum_add_distrib, sum_comm, ← mul_sum, hsumQ]
        _ ≤ (∑ _c₀ : κ, √g * (Fintype.card V).descFactorial 3) +
              Fintype.card κ * β * (Fintype.card V).descFactorial 3 := by
            gcongr with c₀
            exact H.sum_card_support_mul_abs_relativeDensity_coarsen_le hV f hf hgap c₀
        _ = Fintype.card κ * (√g + β) * (Fintype.card V).descFactorial 3 := by
            rw [sum_const, card_univ, nsmul_eq_mul]
            ring
        _ ≤ Fintype.card κ * (√g + β) * (Fintype.card V : ℝ) ^ 3 := by
            gcongr
            exact_mod_cast Nat.descFactorial_le_pow (Fintype.card V) 3
    exact approximates3_of_card_editedOn_univ_le (by positivity) hedit_total
  · -- Part 2: Coarse top regularity `H'.TopRegularOverMostPolyads C δ ... r`.
    have hgood_child (P : Polyad3 C.skeleton) (Q : Polyad3 D.skeleton) (hQP : Q.coarsen hV f = P)
        (hQ : N₀ ≤ (#Q.support : ℝ)) (hQreg : H.IsTopRegularOverPolyad Q η 1) (c : κ)
        (S' : Subpolyad3 Q) :
        |(H'.relDensityOn c S'.support : ℝ) - H.relativeDensity c P| * #S'.support ≤
          Fintype.card κ * (η + β) * #Q.support := by
      set Q₀ := canonPolyad Q
      have hQ₀ : N₀ ≤ (#Q₀.support : ℝ) := by rwa [hcanon_card Q]
      obtain ⟨hM0, hM1, hMpush, -, -⟩ := hMφ Q₀ hQ₀
      -- Split `H'.relDensityOn c S'.support * #S'.support` by the old color `c₀`.
      have hnew_split : (H'.relDensityOn c S'.support : ℝ) * #S'.support =
          ∑ c₀ : κ, (#{x ∈ S'.support |
            H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
            H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℝ) := by
        have hpart : #{x ∈ S'.support |
              H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} =
            ∑ c₀ : κ, #{x ∈ S'.support |
              H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
              H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} := by
          rw [card_eq_sum_card_fiberwise
            (f := fun x ↦ H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩))
            (t := univ) (fun _ _ ↦ mem_univ _)]
          refine sum_congr rfl fun c₀ _ ↦ congrArg card (ext fun x ↦ ?_)
          simp only [mem_filter]
          tauto
        have hmul : (H'.relDensityOn c S'.support : ℝ) * #S'.support =
            (#{x ∈ S'.support | H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℝ) := by
          exact_mod_cast H'.relDensityOn_mul_card c S'.support
        rw [hmul, hpart, Nat.cast_sum]
      -- Express `H.relativeDensity c P * #S'.support` via `hMpush`.
      have htarget_split : (H.relativeDensity c P : ℝ) * #S'.support =
          ∑ c₀ : κ, M Q₀ c₀ c * ((H.relativeDensity c₀ Q : ℝ) * #S'.support) := by
        rw [← hQP, ← (hQ₀_dens Q c).2, ← hMpush c, sum_mul]
        refine sum_congr rfl fun c₀ _ ↦ ?_
        rw [(hQ₀_dens Q c₀).1]
        ring
      rw [← abs_of_nonneg (Nat.cast_nonneg (α := ℝ) #S'.support), ← abs_mul, sub_mul,
        hnew_split, htarget_split, ← sum_sub_distrib]
      calc |∑ c₀ : κ, ((#{x ∈ S'.support |
              H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
              H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℝ) -
            M Q₀ c₀ c * ((H.relativeDensity c₀ Q : ℝ) * #S'.support))|
          ≤ ∑ c₀ : κ, |(#{x ∈ S'.support |
              H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
              H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℝ) -
            M Q₀ c₀ c * ((H.relativeDensity c₀ Q : ℝ) * #S'.support)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _c₀ : κ, (η + β) * #Q.support := by
            refine sum_le_sum fun c₀ _ ↦ ?_
            have hold_mul : (#{x ∈ S'.support |
                H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀} : ℝ) =
                (H.relDensityOn c₀ S'.support : ℝ) * #S'.support := by
              exact_mod_cast (H.relDensityOn_mul_card c₀ S'.support).symm
            have hM_le1 : M Q₀ c₀ c ≤ 1 :=
              (single_le_sum (fun c' _ ↦ hM0 c₀ c') (mem_univ c)).trans_eq (hM1 c₀)
            have hreg_c₀ := hQreg.abs_relDensityOn_sub_mul_card_le c₀ S'
            have htri_c₀ :
                |(#{x ∈ S'.support |
                    H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
                    H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℝ) -
                  M Q₀ c₀ c * ((H.relativeDensity c₀ Q : ℝ) * #S'.support)| ≤
                |(#{x ∈ S'.support |
                    H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
                    H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℝ) -
                  M Q₀ c₀ c * #{x ∈ S'.support |
                    H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀}| +
                M Q₀ c₀ c * (|(H.relDensityOn c₀ S'.support : ℝ) - H.relativeDensity c₀ Q| *
                  #S'.support) := by
              rw [hold_mul]
              have hdiff :
                  (#{x ∈ S'.support |
                      H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
                      H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℝ) -
                    M Q₀ c₀ c * ((H.relativeDensity c₀ Q : ℝ) * #S'.support) =
                  ((#{x ∈ S'.support |
                      H.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c₀ ∧
                      H'.color (Set.powersetCard.ofFinEmb 3 V ⟨x.1, x.2⟩) = c} : ℝ) -
                    M Q₀ c₀ c * ((H.relDensityOn c₀ S'.support : ℝ) * #S'.support)) +
                  M Q₀ c₀ c * (((H.relDensityOn c₀ S'.support : ℝ) - H.relativeDensity c₀ Q) *
                    #S'.support) := by ring
              rw [hdiff]
              refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
              rw [abs_mul, abs_of_nonneg (hM0 c₀ c), abs_mul, Nat.abs_cast]
            have hM_term :
                M Q₀ c₀ c * (|(H.relDensityOn c₀ S'.support : ℝ) - H.relativeDensity c₀ Q| *
                  #S'.support) ≤ η * #Q.support :=
              (mul_le_mul hM_le1 hreg_c₀
                (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (by norm_num)).trans_eq (one_mul _)
            linarith [hsub_count hQ S' c₀ c]
        _ = Fintype.card κ * (η + β) * #Q.support := by
            rw [sum_const, card_univ, nsmul_eq_mul]
            ring
    -- Charge each irregular coarse polyad `P` to its small or irregular fine children.
    let badChild (P : Polyad3 C.skeleton) : ℝ :=
      ∑ Q : Polyad3 D.skeleton with
        Q.coarsen hV f = P ∧ (¬N₀ ≤ (#Q.support : ℝ) ∨ ¬H.IsTopRegularOverPolyad Q η 1),
        (#Q.support : ℝ)
    have hcharge (P : Polyad3 C.skeleton) :
        (if ¬H'.IsTopRegularOverPolyad P δ r then θ * #P.support else 0) ≤ badChild P := by
      by_cases hP : H'.IsTopRegularOverPolyad P δ r
      · simp only [hP, not_true_eq_false, ↓reduceIte]
        exact sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
      · simp only [hP, not_false_eq_true, ↓reduceIte]
        by_contra! hlt
        exact hP (isTopRegularOverPolyad_of_recolored_children hV f hf hη hδ hβ htol
          (hgood_child P) (by convert hlt.le))
    have hsum_bad : ∑ P : Polyad3 C.skeleton, badChild P ≤
        Fintype.card (Polyad3 D.skeleton) * N₀ +
          ∑ Q : Polyad3 D.skeleton with ¬H.IsTopRegularOverPolyad Q η 1, (#Q.support : ℝ) := by
      have hfib : ∑ P : Polyad3 C.skeleton, badChild P =
          ∑ Q : Polyad3 D.skeleton with ¬N₀ ≤ (#Q.support : ℝ) ∨ ¬H.IsTopRegularOverPolyad Q η 1,
            (#Q.support : ℝ) := by
        dsimp only [badChild]
        rw [sum_filter, ← sum_fiberwise univ (fun Q : Polyad3 D.skeleton ↦ Q.coarsen hV f)]
        refine sum_congr rfl fun P _ ↦ ?_
        rw [← sum_filter, filter_filter]
      rw [hfib]
      let s₁ := univ.filter fun Q : Polyad3 D.skeleton ↦ ¬N₀ ≤ (#Q.support : ℝ)
      let s₂ := univ.filter fun Q : Polyad3 D.skeleton ↦ ¬H.IsTopRegularOverPolyad Q η 1
      have hunion : (univ.filter fun Q : Polyad3 D.skeleton ↦
            ¬N₀ ≤ (#Q.support : ℝ) ∨ ¬H.IsTopRegularOverPolyad Q η 1) = s₁ ∪ s₂ := by
        ext Q
        simp only [s₁, s₂, mem_union, mem_filter, mem_univ, true_and]
      have hunion_le : ∑ Q ∈ s₁ ∪ s₂, (#Q.support : ℝ) ≤
          ∑ Q ∈ s₁, (#Q.support : ℝ) + ∑ Q ∈ s₂, (#Q.support : ℝ) := by
        have hinter : 0 ≤ ∑ Q ∈ s₁ ∩ s₂, (#Q.support : ℝ) :=
          sum_nonneg fun _ _ ↦ Nat.cast_nonneg _
        linarith [sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := fun Q ↦ (#Q.support : ℝ))]
      rw [hunion]
      refine hunion_le.trans (add_le_add ?_ le_rfl)
      calc ∑ Q ∈ s₁, (#Q.support : ℝ)
          ≤ ∑ _Q ∈ s₁, N₀ :=
            sum_le_sum fun Q hQ ↦ (not_le.1 (mem_filter.1 hQ).2).le
        _ ≤ ∑ _Q : Polyad3 D.skeleton, N₀ :=
            sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ ↦ hN₀_pos.le
        _ = Fintype.card (Polyad3 D.skeleton) * N₀ := by
            rw [sum_const, card_univ, nsmul_eq_mul]
    rw [topRegularOverMostPolyads_iff, exceptionalPolyadMass_eq_sum_div hC]
    obtain hdesc0 | hdesc := (Nat.cast_nonneg (α := ℝ) ((Fintype.card V).descFactorial 3)).eq_or_lt
    · rw [← hdesc0, div_zero, div_zero, add_zero]
      have hμ0 := h.nonneg
      positivity
    · have hirr_D : ∑ Q : Polyad3 D.skeleton with ¬H.IsTopRegularOverPolyad Q η 1,
          (#Q.support : ℝ) ≤ μ * (Fintype.card V).descFactorial 3 := by
        have hm := topRegularOverMostPolyads_iff.1 h
        rw [exceptionalPolyadMass_eq_sum_div hD, div_le_iff₀ hdesc] at hm
        exact hm
      have htot : θ * ∑ P : Polyad3 C.skeleton with ¬H'.IsTopRegularOverPolyad P δ r,
          (#P.support : ℝ) ≤
          μ * (Fintype.card V).descFactorial 3 + Fintype.card (Polyad3 D.skeleton) * N₀ := by
        rw [mul_sum, sum_filter]
        calc ∑ P : Polyad3 C.skeleton,
              (if ¬H'.IsTopRegularOverPolyad P δ r then θ * (#P.support : ℝ) else 0)
            ≤ ∑ P : Polyad3 C.skeleton, badChild P := sum_le_sum fun P _ ↦ hcharge P
          _ ≤ _ := by linarith [hsum_bad, hirr_D]
      rw [div_le_div_iff₀ hdesc hθ, add_mul, div_mul_cancel₀ _ hdesc.ne']
      linarith

/-- **Scheduled strong top-regular approximation.** Let `ε > 0`, let `δ μ : ℕ → ℝ` be positive
schedules, and let `r : ℕ → ℕ` be a rank schedule. On every host `V` of cardinality at least
`topRegularApproximationCardBound (Nat.card κ) #S.vertexPart.parts ε δ μ r (Fintype.card κ₂)`,
every lower skeleton `S` has a palette refinement `C` with the vertex cells of `S` and all its
polyads, bounded independently of `V` by `topRegularApproximationPaletteBound`, together with an
`ε`-close coloring `H'` that is `(δ C.complexity, r C.complexity)`-top-regular off a
`μ C.complexity`-proportion of the polyads of `C`. -/
theorem exists_approximates3_topRegularOverMostPolyads [Finite κ] [Fintype κ₂]
    (H : Colored3Graph κ V) (S : PairSkeleton3 κ₂ V) {ε : ℝ} (hε : 0 < ε)
    {δ μ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hμ : ∀ n, 0 < μ n) (r : ℕ → ℕ)
    (hcard : topRegularApproximationCardBound (Nat.card κ) #S.vertexPart.parts ε δ μ r
      (Fintype.card κ₂) ≤ Fintype.card V) :
    ∃ (C : TriadicComplex3 V) (π : Fin C.pairColorCount → κ₂) (H' : Colored3Graph κ V),
      C.pairColorCount ≤ topRegularApproximationPaletteBound (Nat.card κ)
        #S.vertexPart.parts ε δ μ r (Fintype.card κ₂) ∧
      C.skeleton.vertexPart = S.vertexPart ∧
      (∀ p, π (C.skeleton.pairColors.color p) = S.pairColors.color p) ∧
      (∀ c, π (C.skeleton.pairColors.rev c) = S.pairColors.rev (π c)) ∧
      C.polyads = univ ∧
      H.Approximates3 H' ε ∧
      H'.TopRegularOverMostPolyads C (δ C.complexity) (μ C.complexity) (r C.complexity) := by
  have := Fintype.ofFinite κ
  set q := Nat.card κ
  set t := #S.vertexPart.parts
  set m₀ := Fintype.card κ₂
  let δ₁ : ℕ → ℝ := fun n ↦ (δ n) ^ 2 / (2 : ℝ) ^ r n
  let θ : ℕ → ℝ := fun n ↦ (δ₁ n) ^ 2 / 4
  let η' : ℕ → ℝ := fun n ↦ (δ₁ n) ^ 2 / (8 * ((q : ℝ) + 1))
  let μ' : ℕ → ℝ := fun n ↦ μ n * θ n / 2
  let β : ℕ → ℝ := fun n ↦ min (ε / (2 * ((q : ℝ) + 1))) (η' n)
  set γ : ℝ := ε / (2 * ((q : ℝ) + 1))
  have hγ : 0 < γ := by positivity
  have hδ₁ (n : ℕ) : 0 < δ₁ n := by
    have := hδ n
    positivity
  have hθ (n : ℕ) : 0 < θ n := by
    have := hδ₁ n
    positivity
  have hη' (n : ℕ) : 0 < η' n := by
    have := hδ₁ n
    positivity
  have hμ' (n : ℕ) : 0 < μ' n := by
    have := hμ n
    have := hθ n
    positivity
  have hβ (n : ℕ) : 0 < β n := lt_min hγ (hη' n)
  -- Run strong top regularization at fine rank `1`.
  obtain ⟨C, D, π, f, hCcard, hDcard, hCV, hDV, hπ, hrev, hf, hfrev, hCpol, hDpol, hDreg, hgap⟩ :=
    H.exists_strong_topRegularOverMostPolyads S (pow_pos hγ 2) hη' hμ' (fun _ ↦ 1)
  set M := topRegularApproximationPaletteBound q t ε δ μ r m₀
  have hCM : C.pairColorCount ≤ M := hCcard
  have hCcomp : C.complexity ≤ t + M + t ^ 3 * M ^ 3 := by
    refine C.complexity_le.trans ?_
    rw [hCV]
    gcongr
  set M' := strongTopRegularityStep t η' μ' (fun _ ↦ 1) M
  have hDM' : D.pairColorCount ≤ M' :=
    hDcard.trans (topRegularRefinementBound_le_strongTopRegularityStep η' μ' (fun _ ↦ 1) hCM hCcomp)
  have hDpoly : Fintype.card (Polyad3 D.skeleton) ≤ t ^ 3 * M' ^ 3 := by
    refine (card_polyad3_le D.skeleton).trans ?_
    rw [hDV, Fintype.card_fin]
    gcongr
  -- Extract the host-size inequalities at `n = C.complexity`.
  set n := C.complexity
  set P : ℝ := ((t ^ 3 * M' ^ 3 + 1 : ℕ) : ℝ)
  have hv4 : 4 ≤ Fintype.card V := (le_max_left _ _).trans hcard
  have hv_sup : ⌊4 * P * 221 * ((q : ℝ) + 10) / ((β n) ^ 2 * μ' n)⌋₊ + 1 ≤ Fintype.card V := by
    refine (le_sup (f := fun k ↦ ⌊4 * P * 221 * ((q : ℝ) + 10) / ((β k) ^ 2 * μ' k)⌋₊ + 1)
      (mem_range.2 (Nat.lt_succ_of_le hCcomp))).trans ?_
    exact (le_max_right _ _).trans hcard
  have hv_real : 4 * P * 221 * ((q : ℝ) + 10) / ((β n) ^ 2 * μ' n) < Fintype.card V :=
    (Nat.lt_floor_add_one _).trans_le (by exact_mod_cast hv_sup)
  -- Calibrate the polyad support cutoff `N₀`.
  set N₀ : ℝ := 221 * (3 * (Fintype.card V : ℝ) ^ 2 + q + 7) / (β n) ^ 2
  have hN₀_bound : 221 * (3 * (Fintype.card V : ℝ) ^ 2 + q + 7) ≤ (β n) ^ 2 * N₀ := by
    dsimp only [N₀]
    rw [mul_div_cancel₀ _ (pow_ne_zero 2 (hβ n).ne')]
  have htol_n : 2 * ((q : ℝ) * (η' n + β n) + θ n) ≤ (δ₁ n) ^ 2 := by
    have hβ_le : β n ≤ η' n := min_le_right _ _
    have hqη : (q : ℝ) * (2 * η' n) ≤ (δ₁ n) ^ 2 / 4 := by
      dsimp only [η']
      rw [show (q : ℝ) * (2 * ((δ₁ n) ^ 2 / (8 * ((q : ℝ) + 1)))) =
        (q : ℝ) * (δ₁ n) ^ 2 / (4 * ((q : ℝ) + 1)) by field_simp; ring]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (δ₁ n), (Nat.cast_nonneg q : (0 : ℝ) ≤ q)]
    have hq_sum : (q : ℝ) * (η' n + β n) ≤ (q : ℝ) * (2 * η' n) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg q)
    dsimp only [θ]
    linarith
  have hq_card : q = Fintype.card κ := Nat.card_eq_fintype_card
  have hdec {K : TriadicComplex3 V} (hK : K.polyads = univ) : K.IsPolyadDecomposition :=
    K.isPolyadDecomposition_iff_ofTriple_mem.2 fun _ ↦ hK ▸ mem_univ _
  obtain ⟨H', happrox, hreg⟩ := hDreg.exists_approximates3_of_polyadEnergy_sub_le (hdec hCpol)
    (hdec hDpol) (hDV.trans hCV.symm).le f (fun p ↦ (hf p).symm) hfrev hgap (hη' n).le (hδ n)
    (hβ n) (hθ n) (by rwa [← hq_card]) (by rwa [← hq_card])
  refine ⟨C, π, H', hCM, hCV, hπ, hrev, hCpol, happrox.mono ?_, hreg.mono le_rfl ?_ le_rfl⟩
  · -- Edit discrepancy: `q * (√(γ²) + β n) ≤ q * (2 γ) ≤ ε`.
    rw [← hq_card, Real.sqrt_sq hγ.le]
    have hβ_γ : β n ≤ γ := min_le_left _ _
    have hq1 : (0 : ℝ) < (q : ℝ) + 1 := by positivity
    have hq_le : (q : ℝ) * (2 * γ) ≤ ε := by
      dsimp only [γ]
      rw [show (q : ℝ) * (2 * (ε / (2 * ((q : ℝ) + 1)))) = (q : ℝ) * ε / ((q : ℝ) + 1) by
        field_simp]
      rw [div_le_iff₀ hq1]
      linarith
    have : (q : ℝ) * (γ + β n) ≤ (q : ℝ) * (2 * γ) :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg q)
    linarith
  · -- Exceptional mass bound at `n = C.complexity`.
    set v := Fintype.card V
    have hv_desc : v ^ 3 ≤ 4 * v.descFactorial 3 := by
      rw [Nat.descFactorial_succ, Nat.descFactorial_succ, Nat.descFactorial_one]
      have h1 : v ≤ 2 * (v - 1) := by omega
      have h2 : v ≤ 2 * (v - 2) := by omega
      have hmul : v * (v * v) ≤ v * ((2 * (v - 1)) * (2 * (v - 2))) :=
        Nat.mul_le_mul_left v (Nat.mul_le_mul h1 h2)
      calc v ^ 3 = v * (v * v) := by ring
        _ ≤ v * ((2 * (v - 1)) * (2 * (v - 2))) := hmul
        _ = 4 * (v * ((v - 1) * (v - 2))) := by ring
        _ = 4 * ((v - 2) * ((v - 1) * v)) := by ring
    have hv_desc_pos : (0 : ℝ) < v.descFactorial 3 := by
      have : 0 < 4 * v.descFactorial 3 := (pow_pos (by omega : 0 < v) 3).trans_le hv_desc
      have : 0 < v.descFactorial 3 := by omega
      exact_mod_cast this
    have hv1 : (1 : ℝ) ≤ (v : ℝ) ^ 2 := by
      have : 1 ≤ v ^ 2 := by nlinarith
      exact_mod_cast this
    have hN₀_le : N₀ ≤ 221 * ((q : ℝ) + 10) * (v : ℝ) ^ 2 / (β n) ^ 2 := by
      dsimp only [N₀]
      refine div_le_div_of_nonneg_right ?_ (sq_nonneg _)
      change 221 * (3 * (v : ℝ) ^ 2 + q + 7) ≤ 221 * ((q : ℝ) + 10) * (v : ℝ) ^ 2
      have hqv : (q : ℝ) ≤ q * (v : ℝ) ^ 2 := le_mul_of_one_le_right (Nat.cast_nonneg q) hv1
      linarith
    have hDP : (Fintype.card (Polyad3 D.skeleton) : ℝ) ≤ P := by
      dsimp only [P]
      exact_mod_cast hDpoly.trans (Nat.le_succ _)
    have hv_mul : 4 * P * 221 * ((q : ℝ) + 10) ≤ (v : ℝ) * ((β n) ^ 2 * μ' n) := by
      exact ((div_lt_iff₀ (mul_pos (pow_pos (hβ n) 2) (hμ' n))).1 hv_real).le
    have hsmall : (Fintype.card (Polyad3 D.skeleton) : ℝ) * N₀ / v.descFactorial 3 ≤ μ' n := by
      rw [div_le_iff₀ hv_desc_pos]
      have hN₀_pos' : 0 ≤ N₀ := by positivity
      calc (Fintype.card (Polyad3 D.skeleton) : ℝ) * N₀
          ≤ P * (221 * ((q : ℝ) + 10) * (v : ℝ) ^ 2 / (β n) ^ 2) :=
            mul_le_mul hDP hN₀_le hN₀_pos' (by positivity)
        _ = (4 * P * 221 * ((q : ℝ) + 10)) * ((v : ℝ) ^ 2 / (4 * (β n) ^ 2)) := by
            field_simp [(hβ n).ne']
        _ ≤ ((v : ℝ) * ((β n) ^ 2 * μ' n)) * ((v : ℝ) ^ 2 / (4 * (β n) ^ 2)) :=
            mul_le_mul_of_nonneg_right hv_mul (by positivity)
        _ = μ' n * ((v : ℝ) ^ 3 / 4) := by
            field_simp [(hβ n).ne']
        _ ≤ μ' n * v.descFactorial 3 := by
            have hv_descR : (v : ℝ) ^ 3 ≤ 4 * (v.descFactorial 3 : ℝ) := by exact_mod_cast hv_desc
            exact mul_le_mul_of_nonneg_left (by linarith) (hμ' n).le
    rw [div_le_iff₀ (hθ n)]
    have : μ' n + μ' n = μ n * θ n := by
      dsimp only [μ']
      ring
    linarith

end EnergyGapRecoloring

end Colored3Graph

end TauCeti
