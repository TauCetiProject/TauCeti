/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular
public import Mathlib.Data.Finset.Sym
import TauCeti.Algebra.BigOperators.Finset.BoxCauchySchwarz
import TauCeti.Data.Fintype.BigOperators
import TauCeti.Data.Finset.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Quasirandom splitting of pair colors

A symmetric labelling `f : Sym2 V → ι` of the unordered vertex pairs splits every color `c` of a
coherent pair coloring `S` into the colors `(c, i)`, for `i : ι`; this is `PairColorSystem.split`,
defined in `TauCeti.Combinatorics.Hypergraph.PairColor.Basic`. This file shows that some
splitting is quasirandom on a prescribed finite family of vertex cells: on every rectangle
`A' ×ˢ B'` inside two cells `A` and `B`, each color `(c, i)` occupies a `1 / |ι|` share of the
pairs of color `c`, up to an error `δ |A| |B|`
(`PairColorSystem.exists_split_abs_card_sub_le`). The cells may coincide, so the diagonal cell
pairs are covered as well.

The proof is an averaging argument over all labellings of the unordered pairs inside the union of
the cells; the vertex type itself may be infinite. The deviation of the indicator of `(c, i)`
from a `1 / |ι|` share of the indicator of `c` has mean zero at every pair, independently over
the unordered pairs. Its box sum on two cells, a weighted count of the
rectangles `{x, x'} × {y, y'}`, therefore averages to the contribution of the degenerate
rectangles, at most `|A| |B| (|A| + |B|) + |B| ^ 2` (`Fintype.sum_apply_mul_eq_zero`). Some
labelling achieves at most the average of the normalized box sums over all cells and colors,
and two applications of the Cauchy–Schwarz inequality turn a small box sum into a small
discrepancy on every rectangle (`Finset.sum_sum_pow_four_le`). No probability theory is used.

Splitting preserves regularity: if `(A, B)` is an `ε`-regular pair for `S` and the splitting is
quasirandom on `A` and `B` at scale `ε ^ 3 / 2`, then `(A, B)` is `2 ε`-regular for the split
coloring (`PairColorSystem.IsRegularPair.split`). Consequently every regular lower skeleton with
large vertex cells has a split palette, `|ι|` times larger, that is still regular and in which, on
every pair of cells, the density of each split color is within `ε ^ 3` of a `1 / |ι|` share of the
density of its parent (`PairSkeleton3.IsPairColorRegular.exists_split`). Splitting the one-color
skeleton gives regular lower skeletons whose `|ι|` colors all have density within `ε ^ 3` of
`1 / |ι|` on every cell pair.

A coloring of triples carries no pair structure of its own, so a regular approximation of a
three-uniform hypergraph has to construct pair colorings that are regular on every pair of
cells, with prescribed densities. Quasirandom splittings supply such colorings: their classes
are regular pieces of approximately a `1 / |ι|` share of their parent's density, and merging
classes adjusts densities in steps of approximately `1 / |ι|` times the parent density, with the
errors of the merged classes adding up.

## Main results

* `TauCeti.PairColorSystem.exists_split_abs_card_sub_le`: a splitting that is quasirandom on
  every pair of cells of a finite family.
* `TauCeti.PairColorSystem.abs_pairColorDensity_split_sub_le`: the corresponding density bound.
* `TauCeti.PairColorSystem.IsRegularPair.split`: quasirandom splitting preserves regularity.
* `TauCeti.PairSkeleton3.IsPairColorRegular.exists_split`: a regular lower skeleton with large
  cells has a regular quasirandom splitting of its palette.

## References

* F. R. K. Chung, R. L. Graham and R. M. Wilson, *Quasi-random graphs*, Combinatorica 9 (1989):
  four-cycle counts control quasirandomness.
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007): regular approximation by perfectly regular partitions.
-/

public section

open Finset

namespace TauCeti

namespace PairColorSystem

variable {κ ι V : Type*}

section ExtendLabel

variable [Nonempty ι] [DecidableEq V] (U : Finset V)

/-- Extend a labelling of the unordered pairs inside `U` to all unordered pairs. -/
private noncomputable def extendLabel (g : U.sym2 → ι) (z : Sym2 V) : ι :=
  if h : z ∈ U.sym2 then g ⟨z, h⟩ else Classical.arbitrary ι

private theorem extendLabel_of_mem {g : U.sym2 → ι} {z : Sym2 V} (hz : z ∈ U.sym2) :
    extendLabel U g z = g ⟨z, hz⟩ :=
  dite_eq_left hz

private theorem extendLabel_update_of_ne (g : U.sym2 → ι) (e : U.sym2) (v : ι) {z : Sym2 V}
    (hz : z ≠ e.1) : extendLabel U (Function.update g e v) z = extendLabel U g z := by
  unfold extendLabel
  split_ifs
  · exact Function.update_of_ne (fun h ↦ hz (congrArg Subtype.val h)) _ _
  · rfl

end ExtendLabel

section Discrepancy

variable [DecidableEq κ] [Fintype ι] [DecidableEq ι]

/-- The deviation, at the pair `(x, y)` with label `v`, of the indicator of the split color
`(c, i)` from a `1 / |ι|` share of the indicator of `c`. -/
private noncomputable def splitDev (S : PairColorSystem κ V) (c : κ) (i : ι) (x y : V) (v : ι) :
    ℝ :=
  if S.colorOfPair x y = some c then (if v = i then 1 else 0) - (Fintype.card ι : ℝ)⁻¹ else 0

variable (S : PairColorSystem κ V) (c : κ) (i : ι)

/-- The deviation has mean zero over the labels. -/
private theorem sum_splitDev [Nonempty ι] (x y : V) : ∑ v, splitDev S c i x y v = 0 := by
  unfold splitDev
  split_ifs
  · simp [sum_sub_distrib]
  · simp

private theorem abs_splitDev_le_one [Nonempty ι] (x y : V) (v : ι) :
    |splitDev S c i x y v| ≤ 1 := by
  have hq : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have h₀ : 0 < (Fintype.card ι : ℝ)⁻¹ := by positivity
  have h₁ : (Fintype.card ι : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hq
  unfold splitDev
  split_ifs <;> rw [abs_le] <;> constructor <;> linarith

/-- On a rectangle, the deviations add up to the count of the split color minus a `1 / |ι|`
share of the count of the original color. -/
private theorem sum_sum_splitDev (f : Sym2 V → ι) (s t : Finset V) :
    ∑ x ∈ s, ∑ y ∈ t, splitDev S c i x y (f s(x, y)) =
      #{p ∈ s ×ˢ t | (S.split f).colorOfPair p.1 p.2 = some (c, i)} -
        (#{p ∈ s ×ˢ t | S.colorOfPair p.1 p.2 = some c} : ℝ) / Fintype.card ι := by
  simp only [card_filter, sum_product, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    sum_div, ← sum_sub_distrib, colorOfPair_split_eq_some_iff]
  refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ ?_
  unfold splitDev
  split_ifs <;> simp_all [div_eq_mul_inv]

/-- A bound on the count discrepancy of a split color, relative to the number of ordered distinct
pairs of the rectangle, bounds its density discrepancy. -/
theorem abs_pairColorDensity_split_sub_le [DecidableEq V] (f : Sym2 V → ι) (s t : Finset V) {b : ℝ}
    (hb : 0 ≤ b)
    (h : |(#{p ∈ s ×ˢ t | (S.split f).colorOfPair p.1 p.2 = some (c, i)} : ℝ) -
        #{p ∈ s ×ˢ t | S.colorOfPair p.1 p.2 = some c} / Fintype.card ι| ≤
      b * #{p ∈ s ×ˢ t | p.1 ≠ p.2}) :
    |(pairColorDensity (S.split f) (c, i) s t : ℝ) - pairColorDensity S c s t / Fintype.card ι| ≤
      b := by
  obtain hσ | hσ := Nat.eq_zero_or_pos #{p ∈ s ×ˢ t | p.1 ≠ p.2}
  · rw [card_eq_zero] at hσ
    simp [pairColorDensity_eq_zero_of_support_eq_empty _ _ _ _ hσ, hb]
  have hσ' : (0 : ℝ) < #{p ∈ s ×ˢ t | p.1 ≠ p.2} := by exact_mod_cast hσ
  have hsplit := congrArg (fun q : ℚ ↦ (q : ℝ)) (pairColorDensity_mul_card_support (S.split f)
    (c, i) s t)
  have hS := congrArg (fun q : ℚ ↦ (q : ℝ)) (pairColorDensity_mul_card_support S c s t)
  push_cast at hsplit hS
  rw [← mul_le_mul_iff_of_pos_right hσ']
  calc _ = |((pairColorDensity (S.split f) (c, i) s t : ℝ) -
        pairColorDensity S c s t / Fintype.card ι) * #{p ∈ s ×ˢ t | p.1 ≠ p.2}| := by
        rw [abs_mul, abs_of_pos hσ']
    _ = _ := by rw [sub_mul, div_mul_eq_mul_div, hsplit, hS]
    _ ≤ _ := h

/-- The box sum of the deviations of the split color `(c, i)` on two cells `A` and `B`: a
weighted count of the rectangles `{x, x'} × {y, y'}` with `x, x' ∈ A` and `y, y' ∈ B`. -/
private noncomputable def splitBox (f : Sym2 V → ι) (A B : Finset V) : ℝ :=
  ∑ y ∈ B, ∑ y' ∈ B,
    (∑ x ∈ A, splitDev S c i x y (f s(x, y)) * splitDev S c i x y' (f s(x, y'))) ^ 2

private theorem splitBox_nonneg (f : Sym2 V → ι) (A B : Finset V) : 0 ≤ splitBox S c i f A B :=
  sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _

variable [Nonempty ι]

section Averaging

variable [DecidableEq V] (U : Finset V)

/-- A rectangle `{x, x'} × {y, y'}` inside `U` that is not degenerate contributes nothing on
average: the label of `s(x, y)` occurs in only one of its four factors. -/
private theorem sum_splitDev_mul_eq_zero {x x' y y' : V} (hxU : x ∈ U) (hyU : y ∈ U)
    (hx : x ≠ x') (hy : y ≠ y') (hxy : x = y' → y ≠ x') :
    ∑ g : U.sym2 → ι, splitDev S c i x y (extendLabel U g s(x, y)) *
      splitDev S c i x y' (extendLabel U g s(x, y')) *
      (splitDev S c i x' y (extendLabel U g s(x', y)) *
        splitDev S c i x' y' (extendLabel U g s(x', y'))) = 0 := by
  have h₁ : s(x, y') ≠ s(x, y) := by
    rw [Ne, Sym2.eq_iff]
    rintro (⟨-, rfl⟩ | ⟨rfl, rfl⟩) <;> exact hy rfl
  have h₂ : s(x', y) ≠ s(x, y) := by
    rw [Ne, Sym2.eq_iff]
    rintro (⟨rfl, -⟩ | ⟨rfl, rfl⟩) <;> exact hx rfl
  have h₃ : s(x', y') ≠ s(x, y) := by
    rw [Ne, Sym2.eq_iff]
    rintro (⟨rfl, -⟩ | ⟨rfl, rfl⟩)
    exacts [hx rfl, hxy rfl rfl]
  have he : s(x, y) ∈ U.sym2 := mk_mem_sym2_iff.2 ⟨hxU, hyU⟩
  simp_rw [mul_assoc, extendLabel_of_mem U he]
  exact Fintype.sum_apply_mul_eq_zero ⟨s(x, y), he⟩ (sum_splitDev S c i x y)
    (G := fun g ↦ splitDev S c i x y' (extendLabel U g s(x, y')) *
      (splitDev S c i x' y (extendLabel U g s(x', y)) *
        splitDev S c i x' y' (extendLabel U g s(x', y'))))
    fun g v ↦ by
      simp only [extendLabel_update_of_ne U g ⟨s(x, y), he⟩ v h₁,
        extendLabel_update_of_ne U g ⟨s(x, y), he⟩ v h₂,
        extendLabel_update_of_ne U g ⟨s(x, y), he⟩ v h₃]

/-- On average over the labellings of the pairs inside `U`, a rectangle `{x, x'} × {y, y'}`
inside `U` contributes at most one, and nothing unless it is degenerate. -/
private theorem sum_splitDev_mul_le {x y : V} (x' y' : V) (hxU : x ∈ U) (hyU : y ∈ U) :
    ∑ g : U.sym2 → ι, splitDev S c i x y (extendLabel U g s(x, y)) *
      splitDev S c i x y' (extendLabel U g s(x, y')) *
      (splitDev S c i x' y (extendLabel U g s(x', y)) *
        splitDev S c i x' y' (extendLabel U g s(x', y'))) ≤
    (Fintype.card (U.sym2 → ι) : ℝ) * ((if x = x' then 1 else 0) + (if y = y' then 1 else 0) +
      (if x = y' then 1 else 0) * (if y = x' then 1 else 0)) := by
  by_cases hd : x = x' ∨ y = y' ∨ (x = y' ∧ y = x')
  · have hone : (1 : ℝ) ≤ (if x = x' then 1 else 0) + (if y = y' then 1 else 0) +
        (if x = y' then 1 else 0) * (if y = x' then 1 else 0) := by
      split_ifs <;> norm_num <;> tauto
    have hterm (g : U.sym2 → ι) : splitDev S c i x y (extendLabel U g s(x, y)) *
        splitDev S c i x y' (extendLabel U g s(x, y')) *
        (splitDev S c i x' y (extendLabel U g s(x', y)) *
          splitDev S c i x' y' (extendLabel U g s(x', y'))) ≤ 1 := by
      refine (le_abs_self _).trans ?_
      simp only [abs_mul]
      calc _ ≤ (1 : ℝ) * 1 * (1 * 1) := by gcongr <;> exact abs_splitDev_le_one ..
        _ = 1 := by norm_num
    calc _ ≤ ∑ _g : U.sym2 → ι, (1 : ℝ) := sum_le_sum fun g _ ↦ hterm g
      _ = Fintype.card (U.sym2 → ι) * 1 := by simp
      _ ≤ _ := by gcongr
  · push Not at hd
    rw [sum_splitDev_mul_eq_zero S c i U hxU hyU hd.1 hd.2.1 hd.2.2]
    positivity

/-- The number of degenerate rectangles `(x, x', y, y')` in `A × A × B × B`, those with `x = x'`,
`y = y'`, or `x = y'` and `y = x'`, is at most `#A #B² + #A² #B + #B²`. -/
private theorem sum_degenerate_le (A B : Finset V) :
    ∑ y ∈ B, ∑ y' ∈ B, ∑ x ∈ A, ∑ x' ∈ A,
      ((if x = x' then (1 : ℝ) else 0) + (if y = y' then 1 else 0) +
        (if x = y' then 1 else 0) * (if y = x' then 1 else 0)) ≤
      #B * #B * #A + #B * (#A * #A) + #B * #B := by
  have hI (a : V) (s : Finset V) : ∑ b ∈ s, (if a = b then (1 : ℝ) else 0) ≤ 1 := by
    rw [sum_ite_eq]
    split_ifs <;> norm_num
  have hI' (a : V) (s : Finset V) : ∑ b ∈ s, (if b = a then (1 : ℝ) else 0) ≤ 1 := by
    rw [sum_ite_eq']
    split_ifs <;> norm_num
  have h₁ : ∑ y ∈ B, ∑ y' ∈ B, ∑ x ∈ A, ∑ x' ∈ A, (if x = x' then (1 : ℝ) else 0) ≤
      #B * #B * #A := by
    calc _ ≤ ∑ _y ∈ B, ∑ _y' ∈ B, ∑ _x ∈ A, (1 : ℝ) :=
          sum_le_sum fun _ _ ↦ sum_le_sum fun _ _ ↦ sum_le_sum fun x _ ↦ hI x A
      _ = _ := by simp only [sum_const, nsmul_eq_mul, mul_one, mul_assoc]
  have h₂ : ∑ y ∈ B, ∑ y' ∈ B, ∑ x ∈ A, ∑ x' ∈ A, (if y = y' then (1 : ℝ) else 0) ≤
      #B * (#A * #A) := by
    calc _ = ∑ y ∈ B, ∑ y' ∈ B, (#A : ℝ) * (#A * if y = y' then 1 else 0) := by
          simp only [sum_const, nsmul_eq_mul]
      _ ≤ ∑ _y ∈ B, (#A : ℝ) * (#A * 1) := by
          refine sum_le_sum fun y _ ↦ ?_
          rw [← mul_sum, ← mul_sum]
          gcongr
          exact hI y B
      _ = _ := by simp
  have h₃ : ∑ y ∈ B, ∑ y' ∈ B, ∑ x ∈ A, ∑ x' ∈ A,
      (if x = y' then (1 : ℝ) else 0) * (if y = x' then 1 else 0) ≤ #B * #B := by
    calc _ = ∑ y ∈ B, ∑ y' ∈ B, (∑ x ∈ A, if x = y' then (1 : ℝ) else 0) *
          ∑ x' ∈ A, if y = x' then (1 : ℝ) else 0 := by
          simp only [sum_mul_sum]
      _ ≤ ∑ _y ∈ B, ∑ _y' ∈ B, (1 : ℝ) * 1 := by
          gcongr with y _ y' _
          exacts [hI' y' A, hI y A]
      _ = _ := by simp
  simp only [sum_add_distrib]
  exact add_le_add (add_le_add h₁ h₂) h₃

/-- The box sum of the deviations on two cells inside `U` averages, over the labellings of the
pairs inside `U`, to at most the number of degenerate rectangles. -/
private theorem sum_splitBox_le {A B : Finset V} (hA : A ⊆ U) (hB : B ⊆ U) :
    ∑ g : U.sym2 → ι, splitBox S c i (extendLabel U g) A B ≤
      Fintype.card (U.sym2 → ι) * (#A * #B ^ 2 + #A ^ 2 * #B + #B ^ 2) := by
  calc _ = ∑ y ∈ B, ∑ y' ∈ B, ∑ x ∈ A, ∑ x' ∈ A, ∑ g : U.sym2 → ι,
        splitDev S c i x y (extendLabel U g s(x, y)) *
          splitDev S c i x y' (extendLabel U g s(x, y')) *
          (splitDev S c i x' y (extendLabel U g s(x', y)) *
            splitDev S c i x' y' (extendLabel U g s(x', y'))) := by
        simp_rw [splitBox, sq, sum_mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun y _ ↦ ?_
        rw [sum_comm]
        refine sum_congr rfl fun y' _ ↦ ?_
        rw [sum_comm]
        exact sum_congr rfl fun x _ ↦ sum_comm
    _ ≤ ∑ y ∈ B, ∑ y' ∈ B, ∑ x ∈ A, ∑ x' ∈ A, (Fintype.card (U.sym2 → ι) : ℝ) *
        ((if x = x' then 1 else 0) + (if y = y' then 1 else 0) +
          (if x = y' then 1 else 0) * (if y = x' then 1 else 0)) := by
        gcongr with y hy y' _ x hx x' _
        exact sum_splitDev_mul_le S c i U x' y' (hA hx) (hB hy)
    _ = (Fintype.card (U.sym2 → ι) : ℝ) * ∑ y ∈ B, ∑ y' ∈ B, ∑ x ∈ A, ∑ x' ∈ A,
        ((if x = x' then 1 else 0) + (if y = y' then 1 else 0) +
          (if x = y' then 1 else 0) * (if y = x' then 1 else 0)) := by
        simp only [mul_sum]
    _ ≤ (Fintype.card (U.sym2 → ι) : ℝ) * (#B * #B * #A + #B * (#A * #A) + #B * #B) :=
        mul_le_mul_of_nonneg_left (sum_degenerate_le A B) (by positivity)
    _ = _ := by ring

end Averaging

/-- Normalized by the squared cell sizes, the box sums of the cell pairs of `𝒜 ×ˢ 𝒜` and the
colors of `κ × ι` average to at most `3 |𝒜| ^ 2 |κ| |ι| / N` over all labellings, so that some
labelling makes each of them at most this average. -/
private theorem exists_forall_splitBox_le [Fintype κ] (𝒜 : Finset (Finset V)) {N : ℕ}
    (hN₀ : 0 < N) (hN : ∀ A ∈ 𝒜, N ≤ #A) :
    ∃ f : Sym2 V → ι, ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, ∀ (c : κ) (i : ι),
      splitBox S c i f A B ≤
        3 * #𝒜 ^ 2 * Fintype.card κ * Fintype.card ι / N * (#A * #B) ^ 2 := by
  classical
  -- Only the labels of the pairs inside the union `U` of the cells matter.
  let U := 𝒜.sup id
  have hU {A : Finset V} (hA : A ∈ 𝒜) : A ⊆ U := le_sup (f := id) hA
  have hN₀' : (0 : ℝ) < N := by exact_mod_cast hN₀
  have hcell {A : Finset V} (hA : A ∈ 𝒜) : (1 : ℝ) ≤ #A := by exact_mod_cast hN₀.trans_le (hN A hA)
  let P := 𝒜 ×ˢ 𝒜 ×ˢ (univ : Finset (κ × ι))
  -- The sum, over all cell pairs and colors, of the normalized box sums.
  let W (g : U.sym2 → ι) : ℝ :=
    ∑ p ∈ P, splitBox S p.2.2.1 p.2.2.2 (extendLabel U g) p.1 p.2.1 / (#p.1 * #p.2.1) ^ 2
  -- Each normalized box sum averages to at most `3 / N`: there are at most
  -- `|A| |B| (|A| + |B|) + |B| ^ 2 ≤ 3 |A| ^ 2 |B| ^ 2 / N` degenerate rectangles.
  have hp {p} (hp : p ∈ P) : ∑ g, splitBox S p.2.2.1 p.2.2.2 (extendLabel U g) p.1 p.2.1 /
      (#p.1 * #p.2.1) ^ 2 ≤ Fintype.card (U.sym2 → ι) * 3 / N := by
    simp only [P, mem_product] at hp
    have hA : (N : ℝ) ≤ #p.1 := by exact_mod_cast hN _ hp.1
    have hB : (N : ℝ) ≤ #p.2.1 := by exact_mod_cast hN _ hp.2.1
    have hA₁ := hcell hp.1
    have hB₁ := hcell hp.2.1
    have key : (#p.1 * #p.2.1 ^ 2 + #p.1 ^ 2 * #p.2.1 + #p.2.1 ^ 2 : ℝ) * N ≤
        3 * (#p.1 * #p.2.1) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ #p.1 * #p.2.1 ^ 2),
        mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ #p.1 ^ 2 * #p.2.1),
        mul_le_mul_of_nonneg_left (hA.trans (le_mul_of_one_le_left (by positivity) hA₁))
          (by positivity : (0 : ℝ) ≤ #p.2.1 ^ 2)]
    rw [← sum_div, div_le_div_iff₀ (by positivity) hN₀']
    calc (∑ g, splitBox S p.2.2.1 p.2.2.2 (extendLabel U g) p.1 p.2.1) * N
        ≤ Fintype.card (U.sym2 → ι) *
            ((#p.1 * #p.2.1 ^ 2 + #p.1 ^ 2 * #p.2.1 + #p.2.1 ^ 2) * N) := by
          rw [← mul_assoc]
          gcongr
          exact sum_splitBox_le S _ _ U (hU hp.1) (hU hp.2.1)
      _ ≤ Fintype.card (U.sym2 → ι) * (3 * (#p.1 * #p.2.1) ^ 2) := by gcongr
      _ = _ := by ring
  have hW : ∑ g, W g ≤
      ∑ _g : U.sym2 → ι, (3 * #𝒜 ^ 2 * Fintype.card κ * Fintype.card ι / N : ℝ) := by
    rw [sum_comm]
    refine (sum_le_sum fun p hp' ↦ hp hp').trans_eq ?_
    simp only [P, sum_const, card_product, card_univ, Fintype.card_prod, nsmul_eq_mul,
      Nat.cast_mul]
    ring
  obtain ⟨g, -, hf⟩ := exists_le_of_sum_le univ_nonempty hW
  refine ⟨extendLabel U g, fun A hA B hB c i ↦ ?_⟩
  have hle := (single_le_sum (s := P) (fun p _ ↦ div_nonneg (splitBox_nonneg ..) (sq_nonneg _))
    (by simp [P, hA, hB] : (A, B, c, i) ∈ P)).trans hf
  have hAB : (0 : ℝ) < (#A * #B) ^ 2 := by
    have := hcell hA
    have := hcell hB
    positivity
  rwa [div_le_iff₀ hAB] at hle

/-- **Quasirandom splitting.** Let `𝒜` be a finite family of vertex cells, each of size at
least `N`. If `3 |𝒜| ^ 2 |κ| |ι| ≤ δ ^ 4 N`, then some symmetric labelling `f : Sym2 V → ι` of
the vertex pairs splits every color `c` evenly on every rectangle inside two cells of `𝒜`: for
`A, B ∈ 𝒜`, `A' ⊆ A` and `B' ⊆ B`, the number of pairs of `A' ×ˢ B'` of split color `(c, i)` is
within `δ |A| |B|` of `1 / |ι|` times the number of pairs of color `c`. -/
theorem exists_split_abs_card_sub_le [Fintype κ] (𝒜 : Finset (Finset V)) {N : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hN : ∀ A ∈ 𝒜, N ≤ #A)
    (h : 3 * #𝒜 ^ 2 * Fintype.card κ * Fintype.card ι ≤ δ ^ 4 * N) :
    ∃ f : Sym2 V → ι, ∀ A ∈ 𝒜, ∀ B ∈ 𝒜, ∀ c i, ∀ A' ⊆ A, ∀ B' ⊆ B,
      |(#{p ∈ A' ×ˢ B' | (S.split f).colorOfPair p.1 p.2 = some (c, i)} : ℝ) -
        #{p ∈ A' ×ˢ B' | S.colorOfPair p.1 p.2 = some c} / Fintype.card ι| ≤ δ * #A * #B := by
  obtain rfl | hN₀ := Nat.eq_zero_or_pos N
  · -- With `N = 0`, the hypothesis forces `𝒜` or the palette to be empty.
    refine ⟨fun _ ↦ Classical.arbitrary ι, fun A hA B _ c _ ↦ absurd h (not_le.2 ?_)⟩
    have h𝒜 : (1 : ℝ) ≤ #𝒜 := by exact_mod_cast card_pos.2 ⟨A, hA⟩
    have hκ : (1 : ℝ) ≤ Fintype.card κ := by
      have : Nonempty κ := ⟨c⟩
      exact_mod_cast Fintype.card_pos
    have hι : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
    simp only [Nat.cast_zero, mul_zero]
    positivity
  obtain ⟨f, hf⟩ := exists_forall_splitBox_le (ι := ι) S 𝒜 hN₀ hN
  refine ⟨f, fun A hA B hB c i A' hA' B' hB' ↦ ?_⟩
  -- Two applications of Cauchy–Schwarz bound the fourth power of the discrepancy by the box sum.
  rw [← sum_sum_splitDev]
  refine (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) four_ne_zero).1 ?_
  rw [(by decide : Even 4).pow_abs]
  calc _ ≤ (#A * #B : ℝ) ^ 2 * splitBox S c i f A B := sum_sum_pow_four_le hA' hB' _
    _ ≤ (#A * #B) ^ 2 * (δ ^ 4 * (#A * #B) ^ 2) := by
        gcongr
        refine (hf A hA B hB c i).trans ?_
        gcongr
        rwa [div_le_iff₀ (by exact_mod_cast hN₀)]
    _ = _ := by ring

variable {S} {ε : ℝ} {A B : Finset V} {f : Sym2 V → ι}

/-- **Quasirandom splitting preserves regularity.** If `(A, B)` is `ε`-regular for `S`, the cell
`B` has at least `1 / ε` vertices, and the splitting by `f` is quasirandom on `A` and `B` at
scale `ε ^ 3 / 2`, then `(A, B)` is `2 ε`-regular for the split coloring. -/
theorem IsRegularPair.split (h : S.IsRegularPair ε A B) (hε : 0 < ε) (hB : 1 ≤ ε * #B)
    (hdisc : ∀ c i, ∀ A' ⊆ A, ∀ B' ⊆ B,
      |(#{p ∈ A' ×ˢ B' | (S.split f).colorOfPair p.1 p.2 = some (c, i)} : ℝ) -
        #{p ∈ A' ×ˢ B' | S.colorOfPair p.1 p.2 = some c} / Fintype.card ι| ≤
      ε ^ 3 / 2 * #A * #B) :
    (S.split f).IsRegularPair (2 * ε) A B := by
  classical
  rw [isRegularPair_iff]
  rintro ⟨c, i⟩ A' hA' B' hB' hA'ε hB'ε
  obtain hε₂ | hε₂ := le_or_gt (1 / 2) ε
  · exact isRegularPair_iff.1 (isRegularPair_of_one_le (by linarith)) _ A' hA' B' hB' hA'ε hB'ε
  have hq : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hA₀ : (0 : ℝ) ≤ #A := by positivity
  have hB₀ : (0 : ℝ) ≤ #B := by positivity
  -- Both cells and test sets are large enough for distinct pairs to fill half of a rectangle.
  have hσ (s t : Finset V) (ht : (2 : ℝ) ≤ #t) :
      (#s * #t : ℝ) ≤ 2 * #{p ∈ s ×ˢ t | p.1 ≠ p.2} := by
    exact_mod_cast card_mul_card_le_two_mul_card_filter_ne_product s t (by exact_mod_cast ht)
  have hB'₂ : (2 : ℝ) ≤ #B' := by linarith
  have hB₂ : (2 : ℝ) ≤ #B := by nlinarith [mul_nonneg (sub_nonneg.2 hε₂.le) hB₀]
  have hprod : 2 * ε * #A * (2 * ε * #B) ≤ #A' * #B' :=
    mul_le_mul hA'ε hB'ε (by positivity) (by positivity)
  -- The split densities are within `ε / 4` of a `1 / |ι|` share of the original ones.
  have k₁ : ε ^ 3 / 2 * #A * #B ≤ ε / 4 * #{p ∈ A' ×ˢ B' | p.1 ≠ p.2} := by
    nlinarith [mul_le_mul_of_nonneg_left (hσ A' B' hB'₂) hε.le,
      mul_le_mul_of_nonneg_left hprod hε.le]
  have k₂ : ε ^ 3 / 2 * #A * #B ≤ ε / 4 * #{p ∈ A ×ˢ B | p.1 ≠ p.2} := by
    have hε₃ : ε ^ 3 / 2 ≤ ε / 8 := by
      have h₂ : ε ^ 2 ≤ 1 / 4 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left h₂ hε.le]
    calc ε ^ 3 / 2 * #A * #B ≤ ε / 8 * (#A * #B) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right hε₃ (by positivity)
      _ ≤ ε / 4 * #{p ∈ A ×ˢ B | p.1 ≠ p.2} := by nlinarith [hσ A B hB₂]
  have e₁ := abs_pairColorDensity_split_sub_le S c i f A' B' (b := ε / 4) (by positivity)
    ((hdisc c i A' hA' B' hB').trans k₁)
  have e₂ := abs_pairColorDensity_split_sub_le S c i f A B (b := ε / 4) (by positivity)
    ((hdisc c i A subset_rfl B subset_rfl).trans k₂)
  have e₃ := isRegularPair_iff.1 h c A' hA' B' hB' (by linarith [mul_nonneg hε.le hA₀])
    (by linarith [mul_nonneg hε.le hB₀])
  have e₄ : |((pairColorDensity S c A' B' : ℝ) - pairColorDensity S c A B) /
      Fintype.card ι| ≤ ε := by
    rw [abs_div, abs_of_pos (show (0 : ℝ) < Fintype.card ι by linarith)]
    exact (div_le_self (abs_nonneg _) hq).trans e₃
  rw [sub_div] at e₄
  rw [abs_le] at e₁ e₂ e₄ ⊢
  constructor <;> linarith

end Discrepancy

end PairColorSystem

namespace PairSkeleton3

variable {κ ι V : Type*} [Fintype V] [DecidableEq V] [Fintype κ] [Fintype ι] [Nonempty ι]

/-- **Regular lower skeletons split quasirandomly.** Let `S` be an `ε`-regular lower skeleton
whose vertex cells all have at least `N` vertices, where
`48 t ^ 2 |κ| |ι| ≤ ε ^ 12 N` for `t` vertex cells. Then some symmetric labelling of the vertex
pairs by `ι` splits the palette of `S` into a `2 ε`-regular palette on the same vertex cells, in
which each split color `(c, i)` has, on every pair of cells, density within `ε ^ 3` of
`1 / |ι|` times the density of `c`. -/
theorem IsPairColorRegular.exists_split {S : PairSkeleton3 κ V} {ε : ℝ}
    (h : S.IsPairColorRegular ε) (hε : 0 < ε) {N : ℕ} (hN : ∀ A ∈ S.vertexPart.parts, N ≤ #A)
    (hNε : 48 * #S.vertexPart.parts ^ 2 * Fintype.card κ * Fintype.card ι ≤ ε ^ 12 * N) :
    ∃ f : Sym2 V → ι,
      (⟨S.vertexPart, S.pairColors.split f⟩ : PairSkeleton3 (κ × ι) V).IsPairColorRegular
        (2 * ε) ∧
      ∀ A ∈ S.vertexPart.parts, ∀ B ∈ S.vertexPart.parts, ∀ c i,
        |(pairColorDensity (S.pairColors.split f) (c, i) A B : ℝ) -
          pairColorDensity S.pairColors c A B / Fintype.card ι| ≤ ε ^ 3 := by
  classical
  obtain ⟨f, hf⟩ := S.pairColors.exists_split_abs_card_sub_le (ι := ι) S.vertexPart.parts
    (δ := ε ^ 3 / 2) (by positivity) hN (by nlinarith)
  refine ⟨f, isPairColorRegular_iff.2 fun c A hA B hB ↦ PairColorSystem.isRegularPair_iff.1 ?_ c,
    fun A hA B hB c i ↦ ?_⟩
  · have : Nonempty κ := ⟨c.1⟩
    obtain hε₂ | hε₂ := le_or_gt (1 / 2) ε
    · exact PairColorSystem.isRegularPair_of_one_le (by linarith)
    -- The cells are large: `ε N ≥ ε ^ 12 N ≥ 48`.
    have h₁ : (1 : ℝ) ≤ #S.vertexPart.parts := by exact_mod_cast card_pos.2 ⟨A, hA⟩
    have hκ₁ : (1 : ℝ) ≤ Fintype.card κ := by exact_mod_cast Fintype.card_pos
    have hι₁ : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hε₁₂ : ε ^ 12 ≤ ε := pow_le_of_le_one hε.le (by linarith) (by norm_num)
    have hBN : (N : ℝ) ≤ #B := by exact_mod_cast hN B hB
    refine (h.isRegularPair hA hB).split hε ?_ (hf A hA B hB)
    nlinarith [mul_le_mul_of_nonneg_left hBN hε.le, mul_le_mul_of_nonneg_right hε₁₂
      (Nat.cast_nonneg (α := ℝ) N), mul_le_mul h₁ h₁ zero_le_one (by positivity),
      mul_le_mul hκ₁ hι₁ zero_le_one (by positivity)]
  · obtain hε₁ | hε₁ := le_or_gt 1 ε
    · -- Both densities lie in `[0, 1]`.
      have hq : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
      have h₀ : (0 : ℝ) ≤ pairColorDensity (S.pairColors.split f) (c, i) A B := by
        exact_mod_cast pairColorDensity_nonneg _ _ _ _
      have h₁ : (pairColorDensity (S.pairColors.split f) (c, i) A B : ℝ) ≤ 1 := by
        exact_mod_cast pairColorDensity_le_one _ _ _ _
      have h₀' : (0 : ℝ) ≤ pairColorDensity S.pairColors c A B / Fintype.card ι := by
        have : (0 : ℝ) ≤ pairColorDensity S.pairColors c A B := by
          exact_mod_cast pairColorDensity_nonneg _ _ _ _
        positivity
      have h₁' : (pairColorDensity S.pairColors c A B : ℝ) / Fintype.card ι ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact (by exact_mod_cast pairColorDensity_le_one _ _ _ _ :
          (pairColorDensity S.pairColors c A B : ℝ) ≤ 1).trans hq
      rw [abs_le]
      constructor <;> nlinarith [one_le_pow₀ (n := 3) hε₁]
    -- The cells have at least `48` vertices, so distinct pairs fill half of `A ×ˢ B`.
    have h₁ : (1 : ℝ) ≤ #S.vertexPart.parts := by exact_mod_cast card_pos.2 ⟨A, hA⟩
    have hκ₁ : (1 : ℝ) ≤ Fintype.card κ := by
      have : Nonempty κ := ⟨c⟩
      exact_mod_cast Fintype.card_pos
    have hι₁ : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
    have hε₁₂ : ε ^ 12 ≤ 1 := pow_le_one₀ hε.le hε₁.le
    have hBN : (N : ℝ) ≤ #B := by exact_mod_cast hN B hB
    have hB₂ : (2 : ℝ) ≤ #B := by
      nlinarith [mul_le_mul_of_nonneg_right hε₁₂ (Nat.cast_nonneg (α := ℝ) N),
        mul_le_mul h₁ h₁ zero_le_one (by positivity), mul_le_mul hκ₁ hι₁ zero_le_one
          (by positivity)]
    have hσ : (#A * #B : ℝ) ≤ 2 * #{p ∈ A ×ˢ B | p.1 ≠ p.2} := by
      exact_mod_cast card_mul_card_le_two_mul_card_filter_ne_product A B (by exact_mod_cast hB₂)
    refine PairColorSystem.abs_pairColorDensity_split_sub_le _ c i f A B (by positivity)
      ((hf A hA B hB c i A subset_rfl B subset_rfl).trans ?_)
    nlinarith [(by positivity : (0 : ℝ) ≤ #A), (by positivity : (0 : ℝ) ≤ ε ^ 3)]

end PairSkeleton3

end TauCeti
