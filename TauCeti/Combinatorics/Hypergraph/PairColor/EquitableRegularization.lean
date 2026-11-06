/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Regularization
public import Mathlib.Order.Partition.Equipartition
import Mathlib.Order.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import TauCeti.Combinatorics.Regularity.Partition.Equitabilise
import TauCeti.Order.Partition.Finpartition

/-!
# An equitable regularity lemma for pair-color systems

Let `S` be a pair-color system with a finite palette on a finite vertex type `V`. For `ε > 0` and
`l ≤ |V|`, there is an equipartition of the vertices into at least `l` and at most
`equitablePairColorRegularityBound ε l` parts such that the ordered pairs `(A, B)` of distinct
parts that are not `ε`-regular for `S` cover at most `ε |V|²` ordered pairs of vertices
(`TauCeti.PairColorSystem.exists_equipartition_sum_irregularPairs_le`). The bound depends only on
`ε` and `l`. Regularity is coordinatewise, `TauCeti.PairColorSystem.IsRegularPair`, and colors
need not be symmetric. This is the equitable form of
`TauCeti.PairColorSystem.exists_refinement_sum_irregularPairs_le`, in the shape of Mathlib's
`szemeredi_regularity`. A regular lower skeleton over cells of equal size is what the
counting lemmas for colored three-graphs need, since equal cells make the repeated-cell
placements negligible.

Equitability is not inherited by refinements, so the energy increment has to rebalance the parts
after every round. Cutting the parts of an equipartition `P` along witnesses of irregularity
raises the energy by more than `ε⁵` (`TauCeti.PairColorSystem.exists_refinement_energy_add_lt`),
at the price of at most `#P.parts * 4 ^ #P.parts ^ 2` parts of uncontrolled sizes. Mathlib's
`Finpartition.equitabilise` then rebalances them into `T` parts of size `⌊|V| / T⌋` or one more.
That moves at most `⌊|V| / T⌋` points of each of the cut parts
(`Finpartition.card_filter_not_part_equitabilise_subset_part_le`), and moving `b` points changes
the energy by at most `2 b |V|` over the number of ordered distinct pairs
(`TauCeti.PairColorSystem.abs_energy_sub_energy_le`), so rebalancing loses little energy
(`TauCeti.PairColorSystem.exists_equipartition_card_eq_energy_le_energy_add`). For `T` a large
multiple of the number of cut parts, the energy still rises by more than `ε⁵ / 2`
(`TauCeti.PairColorSystem.exists_equipartition_energy_add_lt`). The energy lies in `[0, 1]`, so
`⌊2 / ε⁵⌋ + 1` rounds suffice. A host with fewer vertices than the bound is cut into singletons,
which form regular pairs.

## Main definitions

* `TauCeti.equitablePairColorRegularityBound`: the bound on the number of parts.

## Main results

* `TauCeti.PairColorSystem.exists_equipartition_card_eq_energy_le_energy_add`: rebalancing a
  partition into an equipartition with a prescribed number of parts loses little energy.
* `TauCeti.PairColorSystem.exists_equipartition_energy_add_lt`: the equitable energy increment.
* `TauCeti.PairColorSystem.exists_equipartition_sum_irregularPairs_le`: the equitable regularity
  lemma.

## References

* E. Szemerédi, *Regular partitions of graphs* (1978).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), where equitable vertex partitions with regular pair
  partitions underlie the regularity lemma for three-uniform hypergraphs.
* Y. Dillies and B. Mehta, *Formalising Szemerédi's Regularity Lemma in Lean*, ITP 2022: the
  statement shape and the use of `Finpartition.equitabilise` follow Mathlib's
  `szemeredi_regularity`.
-/

public section

open Finset Finpartition

namespace TauCeti

/-- The bound on the number of parts in the equitable regularity lemma for pair-color systems,
asking for at least `l` parts. Each round of the energy increment replaces a number `k` of parts
by `⌈8 / ε⁵⌉ * (k * 4 ^ k ^ 2)`, and `⌊2 / ε⁵⌋ + 1` rounds suffice, starting from `max l 1`
parts. -/
noncomputable def equitablePairColorRegularityBound (ε : ℝ) (l : ℕ) : ℕ :=
  (fun k ↦ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2))^[⌊2 / ε ^ 5⌋₊ + 1] (max l 1)

/-- Unfolding lemma for `TauCeti.equitablePairColorRegularityBound`. -/
theorem equitablePairColorRegularityBound_def (ε : ℝ) (l : ℕ) :
    equitablePairColorRegularityBound ε l =
      (fun k ↦ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2))^[⌊2 / ε ^ 5⌋₊ + 1] (max l 1) :=
  (rfl)

/-- One round of the equitable energy increment grows the number of parts monotonically. -/
private theorem monotone_ceil_mul_mul_four_pow_sq (ε : ℝ) :
    Monotone fun k : ℕ ↦ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2) := fun _ _ hab ↦
  Nat.mul_le_mul_left _ (Nat.mul_le_mul hab (Nat.pow_le_pow_right (by norm_num)
    (Nat.pow_le_pow_left hab 2)))

/-- One round of the equitable energy increment does not decrease the number of parts. -/
private theorem le_ceil_mul_mul_four_pow_sq {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    k ≤ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2) :=
  calc k ≤ k * 4 ^ k ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2) :=
      Nat.le_mul_of_pos_left _ (Nat.ceil_pos.2 (by positivity))

namespace PairColorSystem

variable {κ V : Type*} [Fintype V] [DecidableEq V] (S : PairColorSystem κ V) {ε : ℝ}

variable [Fintype κ]

/-- **Rebalancing loses little energy.** Every partition `R` of the vertices is close in energy to
an equipartition into any number `T` of parts with `0 < T ≤ |V|`: the energy drops by at most
`2 #R.parts ⌊|V| / T⌋ |V|` over the number of ordered distinct pairs. The equipartition need not
refine `R`. -/
theorem exists_equipartition_card_eq_energy_le_energy_add (R : Finpartition (univ : Finset V))
    {T : ℕ} (hT : T ≠ 0) (hTV : T ≤ Fintype.card V) :
    ∃ Q : Finpartition (univ : Finset V), Q.IsEquipartition ∧ #Q.parts = T ∧
      S.energy R ≤ S.energy Q + 2 * (#R.parts * (Fintype.card V / T) : ℕ) *
        Fintype.card V / #(univ : Finset V).offDiag := by
  obtain ⟨Q, hQ, hQcard, hM⟩ :=
    R.exists_equipartition_card_eq_card_filter_not_part_subset_le hT (by rwa [card_univ])
  rw [card_univ] at hM
  refine ⟨Q, hQ, hQcard, ?_⟩
  -- `Q` agrees with its common refinement with `R` outside the few moved points.
  set M := {x ∈ (univ : Finset V) | ¬Q.part x ⊆ R.part x}
  have hpart : ∀ x ∉ M, Q.part x = (Q ⊓ R).part x := fun x hx ↦ by
    rw [part_inf, inter_eq_left.2]
    simpa [M] using hx
  have hloss := (abs_le.1 (S.abs_energy_sub_energy_le M hpart)).1
  have hmono := S.energy_mono_of_refines (inf_le_right : Q ⊓ R ≤ R)
  have hcost : 2 * (#M : ℝ) * Fintype.card V / #(univ : Finset V).offDiag ≤
      2 * (#R.parts * (Fintype.card V / T) : ℕ) * Fintype.card V /
        #(univ : Finset V).offDiag := by
    gcongr -- the remaining comparison of the numbers of moved points is `hM`
  linarith

/-- **Equitable energy increment.** If the ordered pairs of distinct parts of a partition `P` that
are not `ε`-regular for `S` cover more than `ε |V|²` ordered pairs of vertices, then for every
`T ≤ |V|` with `8 (#P.parts * 4 ^ #P.parts ^ 2) ≤ ε⁵ T` there is an equipartition into exactly `T`
parts whose energy exceeds that of `P` by more than `ε⁵ / 2`. The equipartition need not refine
`P`. -/
theorem exists_equipartition_energy_add_lt (P : Finpartition (univ : Finset V)) (hε : 0 < ε)
    (hbad : ε * (Fintype.card V : ℝ) ^ 2 <
      ∑ AB ∈ S.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ))
    {T : ℕ} (hT : 8 * (#P.parts * 4 ^ #P.parts ^ 2 : ℕ) ≤ ε ^ 5 * T)
    (hTV : T ≤ Fintype.card V) :
    ∃ Q : Finpartition (univ : Finset V), Q.IsEquipartition ∧ #Q.parts = T ∧
      S.energy P + ε ^ 5 / 2 < S.energy Q := by
  set n := Fintype.card V
  set K := #P.parts * 4 ^ #P.parts ^ 2
  -- Cut `P` along witnesses of irregularity, then rebalance into `T` parts.
  obtain ⟨R, -, hRcard, hRenergy⟩ := S.exists_refinement_energy_add_lt P hε hbad
  -- An irregular pair consists of two distinct parts, so `2 ≤ #P.parts ≤ n`.
  obtain ⟨AB, hAB⟩ : (S.irregularPairs ε P).Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro hempty
    rw [hempty, sum_empty] at hbad
    nlinarith [sq_nonneg (n : ℝ)]
  obtain ⟨hA, hB, hAB', -⟩ := S.mem_irregularPairs.1 hAB
  have hP₂ : 2 ≤ #P.parts := one_lt_card.2 ⟨_, hA, _, hB, hAB'⟩
  have hn : (2 : ℝ) ≤ n := by
    have := hP₂.trans (P.card_parts_le_card.trans_eq card_univ)
    exact_mod_cast this
  have hK : (1 : ℝ) ≤ K := by exact_mod_cast Nat.mul_pos (by omega) (by positivity)
  have hT' : (0 : ℝ) < T := by nlinarith [pow_pos hε 5]
  obtain ⟨Q, hQ, hQcard, hQenergy⟩ :=
    S.exists_equipartition_card_eq_energy_le_energy_add R (T := T) (by exact_mod_cast hT'.ne')
      hTV
  refine ⟨Q, hQ, hQcard, ?_⟩
  -- The rebalancing costs at most `ε⁵ / 2`, since `8 #R.parts ≤ 8 K ≤ ε⁵ T`.
  set D := (#(univ : Finset V).offDiag : ℝ) with hDdef
  have hD : D = n * (n - 1) := by
    have hcard : #(univ : Finset V).offDiag = n * n - n := by rw [offDiag_card, card_univ]
    rw [hDdef, hcard, Nat.cast_sub (Nat.le_mul_self n), Nat.cast_mul]
    ring
  have hDpos : 0 < D := by rw [hD]; nlinarith
  have hRT : ((#R.parts * (n / T) : ℕ) : ℝ) * T ≤ K * n := by
    have : #R.parts * (n / T) * T ≤ K * n := by
      rw [mul_assoc]
      exact Nat.mul_le_mul hRcard (Nat.div_mul_le_self n T)
    exact_mod_cast this
  have hcost : 2 * ((#R.parts * (n / T) : ℕ) : ℝ) * n / D ≤ ε ^ 5 / 2 := by
    rw [div_le_iff₀ hDpos]
    have h₁ : 2 * ((#R.parts * (n / T) : ℕ) : ℝ) * n * T ≤ 2 * K * (n : ℝ) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hRT (by positivity : (0 : ℝ) ≤ 2 * n)]
    have h₂ : 2 * K * (n : ℝ) ^ 2 ≤ 4 * K * D := by
      rw [hD]
      nlinarith [mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ 2 * K * n)]
    have h₃ : 4 * K * D ≤ ε ^ 5 / 2 * D * T := by
      nlinarith [mul_le_mul_of_nonneg_left hT hDpos.le]
    exact le_of_mul_le_mul_right (by linarith) hT'
  linarith

/-- The rounds of the equitable energy increment: after `r` rounds starting from an equipartition
into `max l 1` parts, either the irregular pairs cover at most `ε |V|²` ordered pairs of vertices,
or the energy is at least `r ε⁵ / 2`. This needs the host to have at least as many vertices as
the number of parts after `r` rounds. -/
private theorem exists_equipartition_sum_irregularPairs_le_or_le_energy (hε : 0 < ε) (l r : ℕ)
    (hr : (fun k ↦ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2))^[r] (max l 1) ≤ Fintype.card V) :
    ∃ P : Finpartition (univ : Finset V), P.IsEquipartition ∧ max l 1 ≤ #P.parts ∧
      #P.parts ≤ (fun k ↦ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2))^[r] (max l 1) ∧
      (∑ AB ∈ S.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 ∨
        r * (ε ^ 5 / 2) ≤ S.energy P) := by
  set g : ℕ → ℕ := fun k ↦ ⌈8 / ε ^ 5⌉₊ * (k * 4 ^ k ^ 2)
  have hg : Monotone g := monotone_ceil_mul_mul_four_pow_sq ε
  have hid : id ≤ g := le_ceil_mul_mul_four_pow_sq hε
  induction r with
  | zero =>
    obtain ⟨P, hP, hPcard⟩ := exists_equipartition_card_eq (univ : Finset V)
      (by positivity : max l 1 ≠ 0) (by rw [card_univ]; exact hr)
    exact ⟨P, hP, hPcard.ge, hPcard.le, Or.inr (by simpa using S.energy_nonneg P)⟩
  | succ r ih =>
    have hstep : g^[r] (max l 1) ≤ g^[r + 1] (max l 1) := by
      rw [Function.iterate_succ_apply']
      exact hid _
    obtain ⟨P, hP, hlP, hPcard, hP'⟩ := ih (hstep.trans hr)
    by_cases hgood : ∑ AB ∈ S.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ) ≤
      ε * (Fintype.card V : ℝ) ^ 2
    · exact ⟨P, hP, hlP, hPcard.trans hstep, Or.inl hgood⟩
    -- Rebalance into `g #P.parts` parts; `ε⁵ ⌈8 / ε⁵⌉ ≥ 8` makes this enough.
    have hgP : g #P.parts ≤ g^[r + 1] (max l 1) := by
      rw [Function.iterate_succ_apply']
      exact hg hPcard
    have hT : 8 * (#P.parts * 4 ^ #P.parts ^ 2 : ℕ) ≤ ε ^ 5 * (g #P.parts : ℕ) := by
      have hceil : 8 ≤ ε ^ 5 * ⌈8 / ε ^ 5⌉₊ :=
        (div_le_iff₀' (by positivity)).1 (Nat.le_ceil (8 / ε ^ 5))
      calc 8 * ((#P.parts * 4 ^ #P.parts ^ 2 : ℕ) : ℝ)
          ≤ ε ^ 5 * ⌈8 / ε ^ 5⌉₊ * (#P.parts * 4 ^ #P.parts ^ 2 : ℕ) :=
            mul_le_mul_of_nonneg_right hceil (by positivity)
        _ = ε ^ 5 * (g #P.parts : ℕ) := by
            simp only [g]
            push_cast
            ring
    obtain ⟨Q, hQ, hQcard, hQenergy⟩ :=
      S.exists_equipartition_energy_add_lt P hε (not_le.1 hgood) hT (hgP.trans hr)
    refine ⟨Q, hQ, ?_, hQcard ▸ hgP, Or.inr ?_⟩
    · rw [hQcard]
      exact hlP.trans (hid _)
    · push_cast
      linarith [hP'.resolve_left hgood]

omit [Fintype κ] in
/-- **Equitable regularity lemma for pair-color systems.** For `ε > 0` and `l ≤ |V|`, there is an
equipartition of the vertices into at least `l` and at most `equitablePairColorRegularityBound ε l`
parts such that the ordered pairs `(A, B)` of distinct parts that are not `ε`-regular for `S`
cover at most `ε |V|²` ordered pairs of vertices. The bound depends only on `ε` and `l`. -/
theorem exists_equipartition_sum_irregularPairs_le [Finite κ] (hε : 0 < ε) {l : ℕ}
    (hl : l ≤ Fintype.card V) :
    ∃ P : Finpartition (univ : Finset V), P.IsEquipartition ∧ l ≤ #P.parts ∧
      #P.parts ≤ equitablePairColorRegularityBound ε l ∧
      ∑ AB ∈ S.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  have := Fintype.ofFinite κ
  by_cases hV : equitablePairColorRegularityBound ε l ≤ Fintype.card V
  · rw [equitablePairColorRegularityBound_def] at hV
    obtain ⟨P, hP, hlP, hPcard, hP'⟩ :=
      S.exists_equipartition_sum_irregularPairs_le_or_le_energy hε l (⌊2 / ε ^ 5⌋₊ + 1) hV
    refine ⟨P, hP, (le_max_left _ _).trans hlP,
      hPcard.trans_eq (equitablePairColorRegularityBound_def ε l).symm,
      hP'.resolve_right fun h ↦ ?_⟩
    -- After `⌊2 / ε⁵⌋ + 1` rounds the energy would exceed one.
    have hN : 2 / ε ^ 5 < (⌊2 / ε ^ 5⌋₊ + 1 : ℕ) := by
      push_cast
      exact Nat.lt_floor_add_one _
    rw [div_lt_iff₀ (by positivity)] at hN
    linarith [S.energy_le_one P]
  -- A small host is cut into singletons, all of whose pairs are regular.
  refine ⟨⊥, bot_isEquipartition _, by rwa [card_bot, card_univ], ?_, ?_⟩
  · rw [card_bot, card_univ]
    exact (not_le.1 hV).le
  · refine (sum_eq_zero fun AB hAB ↦ ?_).trans_le (by positivity)
    obtain ⟨hA, hB, -, hreg⟩ := S.mem_irregularPairs.1 hAB
    obtain ⟨u, -, hu⟩ := mem_bot_iff.1 hA
    obtain ⟨v, -, hv⟩ := mem_bot_iff.1 hB
    exact (hreg (hu ▸ hv ▸ S.isRegularPair_singleton hε u v)).elim

end PairColorSystem

end TauCeti
