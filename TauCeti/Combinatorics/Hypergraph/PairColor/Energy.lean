/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Density
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Linarith
import TauCeti.Order.Partition.Finpartition

/-!
# The energy of a vertex partition for a pair-color system

For a pair-color system `S` with a finite palette on a finite vertex type `V`, and a partition `P`
of the vertices, every ordered distinct pair `(u, v)` lies in the block `P.part u ×ˢ P.part v`.
The energy of `P` is the mean, over the `|V| (|V| - 1)` ordered distinct pairs, of the squared
color densities of the blocks through them:
`S.energy P = (∑ (u, v), ∑ c, d_c(P.part u, P.part v)²) / |V| (|V| - 1)`,
where `d_c = pairColorDensity S c` is taken among ordered distinct pairs. This is the index of a
vertex partition for a coloring of pairs, with one term for each color; it is the pair-level
analogue of the polyad energy `TauCeti.Colored3Graph.polyadEnergy`. Diagonal blocks `A ×ˢ A` are
included, with their densities taken among distinct pairs.

The block density of `c` at `(u, v)` is the average over the block of the indicator that a pair has
color `c`. Hence weighting any function constant on blocks by these densities is the same as
summing it over the pairs of color `c` (`TauCeti.PairColorSystem.sum_pairColorDensity_part_mul`).
Consequently, for a refinement `Q ≤ P`, the mean square deviation of the fine block densities
from the coarse ones is exactly the energy gap
(`TauCeti.PairColorSystem.sum_sq_pairColorDensity_sub_div_eq_energy_sub`), so the energy does not
decrease under refinement and lies in `[0, 1]`. Since each block contributes a term in `[0, 1]`,
moving a few points between parts changes the energy only a little, even when neither partition
refines the other.

If a family of coarse blocks has rectangles `X ×ˢ Y` inside them whose sides are unions of parts
of `Q`, each carrying a positive proportion of its block and a color density far from the block
density, then the energy of `Q` exceeds that of `P` by a definite amount
(`TauCeti.PairColorSystem.energy_increment_of_witnesses`). Applied to the witnesses of irregular
pairs of parts, this is the energy increment of the regularity lemma for pair-color systems.

## Main definitions

* `TauCeti.PairColorSystem.energy`: the energy of a vertex partition for a pair-color system.

## Main results

* `TauCeti.PairColorSystem.sum_pairColorDensity_part_mul`: block densities act as conditional
  expectations of the color indicators.
* `TauCeti.PairColorSystem.energy_nonneg` and `TauCeti.PairColorSystem.energy_le_one`.
* `TauCeti.PairColorSystem.abs_energy_sub_energy_le`: two partitions with the same parts through
  all points outside a set `B` have energies within `2 #B |V| / (|V| (|V| - 1))`.
* `TauCeti.PairColorSystem.sum_sq_pairColorDensity_sub_div_eq_energy_sub`: the refinement defect
  identity.
* `TauCeti.PairColorSystem.energy_mono_of_refines`: refining the partition does not decrease the
  energy.
* `TauCeti.PairColorSystem.card_mul_sq_pairColorDensity_sub_le_sum`: Cauchy–Schwarz on a rectangle
  whose sides are unions of parts.
* `TauCeti.PairColorSystem.mul_card_le_sum_sq_pairColorDensity_sub_of_witness`: the deviation gain
  on a single block from one resolved witness rectangle.
* `TauCeti.PairColorSystem.energy_increment_of_witnesses`: the quantitative energy gain from a
  family of resolved witness rectangles.

## References

* E. Szemerédi, *Regular partitions of graphs* (1978), the index of a partition.
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the index-increment argument.
-/

public section

open Finset

namespace TauCeti.PairColorSystem

variable {κ V : Type*} [Fintype V] [DecidableEq V] (S : PairColorSystem κ V)
  {P Q : Finpartition (univ : Finset V)}

/-- The ordered distinct pairs in the block of `P` through `x` are the ordered distinct pairs whose
coordinates lie in the same parts as those of `x`. -/
private theorem mem_filter_ne_part_product_iff (P : Finpartition (univ : Finset V))
    (x y : V × V) :
    y ∈ (P.part x.1 ×ˢ P.part x.2).filter (fun p => p.1 ≠ p.2) ↔
      P.part y.1 = P.part x.1 ∧ P.part y.2 = P.part x.2 ∧ y.1 ≠ y.2 := by
  simp only [mem_filter, mem_product, P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _),
    and_assoc]

section CondExp

variable [DecidableEq κ]

/-- **Block densities are conditional expectations.** If `φ` is constant on each block
`P.part u ×ˢ P.part v`, then weighting `φ` at each ordered distinct pair by the density of `c` on
the block through it gives the sum of `φ` over the pairs of color `c`. -/
theorem sum_pairColorDensity_part_mul (P : Finpartition (univ : Finset V)) (c : κ)
    (φ : V × V → ℝ) (hφ : ∀ x y, P.part x.1 = P.part y.1 → P.part x.2 = P.part y.2 → φ x = φ y) :
    ∑ p ∈ (univ : Finset V).offDiag,
        (pairColorDensity S c (P.part p.1) (P.part p.2) : ℝ) * φ p =
      ∑ p ∈ (univ : Finset V).offDiag with S.colorOfPair p.1 p.2 = some c, φ p := by
  set T : V × V → Finset (V × V) := fun x ↦ (P.part x.1 ×ˢ P.part x.2).filter fun p ↦ p.1 ≠ p.2
  have hT (x y : V × V) : y ∈ T x ↔ P.part y.1 = P.part x.1 ∧ P.part y.2 = P.part x.2 ∧
      y.1 ≠ y.2 := mem_filter_ne_part_product_iff P x y
  -- The pairs sharing the block of `y` contribute `φ y` in total.
  have key : ∀ y ∈ (univ : Finset V).offDiag, ∑ x ∈ T y, φ x / #(T x) = φ y := by
    intro y hy
    have hyy : y ∈ T y := (hT y y).2 ⟨rfl, rfl, (mem_offDiag.1 hy).2.2⟩
    have heq : ∀ x ∈ T y, φ x / #(T x) = φ y / #(T y) := fun x hx ↦ by
      obtain ⟨h₁, h₂, -⟩ := (hT y x).1 hx
      have hTx : T x = T y := by simp only [T, h₁, h₂]
      rw [hTx, hφ x y h₁ h₂]
    rw [sum_congr rfl heq, sum_const, nsmul_eq_mul,
      mul_div_cancel₀ _ (Nat.cast_ne_zero.2 (card_pos.2 ⟨y, hyy⟩).ne')]
  -- Expand each density as a count over its block, then exchange the two sums.
  calc ∑ p ∈ (univ : Finset V).offDiag,
        (pairColorDensity S c (P.part p.1) (P.part p.2) : ℝ) * φ p
      = ∑ x ∈ (univ : Finset V).offDiag,
          ∑ y ∈ (univ : Finset V).offDiag with S.colorOfPair y.1 y.2 = some c,
            if y ∈ T x then φ x / #(T x) else 0 := by
        refine sum_congr rfl fun x _ ↦ ?_
        have hcount : {y ∈ (univ : Finset V).offDiag | S.colorOfPair y.1 y.2 = some c} ∩ T x =
            (P.part x.1 ×ˢ P.part x.2).filter fun p ↦ S.colorOfPair p.1 p.2 = some c := by
          ext y
          have hne : S.colorOfPair y.1 y.2 = some c → y.1 ≠ y.2 := fun hc ↦
            ((S.colorOfPair_eq_some_iff _ _ _).1 hc).1
          simp only [T, mem_inter, mem_filter, mem_offDiag, mem_univ, true_and, mem_product]
          tauto
        rw [sum_ite_mem, sum_const, nsmul_eq_mul, hcount, pairColorDensity_def]
        push_cast
        ring
    _ = ∑ y ∈ (univ : Finset V).offDiag with S.colorOfPair y.1 y.2 = some c,
          ∑ x ∈ T y, φ x / #(T x) := by
        rw [sum_comm]
        refine sum_congr rfl fun y hy ↦ ?_
        have hy' := (mem_offDiag.1 (mem_filter.1 hy).1).2.2
        rw [← sum_filter]
        refine sum_congr (Finset.ext fun x ↦ ?_) fun _ _ ↦ rfl
        simp only [mem_filter, mem_offDiag, mem_univ, true_and, hT]
        constructor
        · rintro ⟨hx, h₁, h₂, -⟩
          exact ⟨h₁.symm, h₂.symm, hx⟩
        · rintro ⟨h₁, h₂, hx⟩
          exact ⟨hx, h₁.symm, h₂.symm, hy'⟩
    _ = _ := sum_congr rfl fun y hy ↦ key y (mem_filter.1 hy).1

/-- On a rectangle `X ×ˢ Y` whose sides are unions of parts of `Q`, the block densities of `c` sum,
over the ordered distinct pairs of the rectangle, to the number of its pairs of color `c`. -/
theorem sum_pairColorDensity_part_eq_card {X Y : Finset V}
    (hX : ∀ C ∈ Q.parts, C ⊆ X ∨ Disjoint C X) (hY : ∀ C ∈ Q.parts, C ⊆ Y ∨ Disjoint C Y)
    (c : κ) :
    ∑ p ∈ (X ×ˢ Y).filter (fun p => p.1 ≠ p.2),
        (pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) =
      #((X ×ˢ Y).filter fun p => S.colorOfPair p.1 p.2 = some c) := by
  have h := S.sum_pairColorDensity_part_mul Q c (fun p ↦ if p.1 ∈ X ∧ p.2 ∈ Y then 1 else 0)
    fun x y h₁ h₂ ↦ by
      simp only [Q.mem_iff_mem_of_part_eq_part hX (mem_univ _) h₁,
        Q.mem_iff_mem_of_part_eq_part hY (mem_univ _) h₂]
  have hXY : (X ×ˢ Y).filter (fun p => p.1 ≠ p.2) =
      (univ : Finset V).offDiag.filter fun p ↦ p.1 ∈ X ∧ p.2 ∈ Y := by
    ext p
    simp only [mem_filter, mem_product, mem_offDiag, mem_univ, true_and]
    tauto
  have hcol : (X ×ˢ Y).filter (fun p => S.colorOfPair p.1 p.2 = some c) =
      ((univ : Finset V).offDiag.filter fun p ↦ S.colorOfPair p.1 p.2 = some c).filter
        fun p ↦ p.1 ∈ X ∧ p.2 ∈ Y := by
    ext p
    simp only [mem_filter, mem_product, mem_offDiag, mem_univ, true_and]
    constructor
    · rintro ⟨hp, hc⟩
      exact ⟨⟨((S.colorOfPair_eq_some_iff _ _ _).1 hc).1, hc⟩, hp⟩
    · rintro ⟨⟨-, hc⟩, hp⟩
      exact ⟨hp, hc⟩
  rw [hXY, sum_filter, hcol, ← sum_boole]
  simpa only [mul_ite, mul_one, mul_zero] using h

end CondExp

/-- **Cauchy–Schwarz on a resolved rectangle.** For a rectangle `X ×ˢ Y` whose sides are unions of
parts of `Q`, the squared deviation of the density of `c` on the rectangle from any real number
`a`, multiplied by the number of ordered distinct pairs of the rectangle, is at most the sum over
those pairs of the squared deviations of the block densities of `Q` from `a`. -/
theorem card_mul_sq_pairColorDensity_sub_le_sum {X Y : Finset V}
    (hX : ∀ C ∈ Q.parts, C ⊆ X ∨ Disjoint C X) (hY : ∀ C ∈ Q.parts, C ⊆ Y ∨ Disjoint C Y)
    (c : κ) (a : ℝ) :
    #((X ×ˢ Y).filter fun p => p.1 ≠ p.2) * ((pairColorDensity S c X Y : ℝ) - a) ^ 2 ≤
      ∑ p ∈ (X ×ˢ Y).filter (fun p => p.1 ≠ p.2),
        ((pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) - a) ^ 2 := by
  classical
  set U := (X ×ˢ Y).filter fun p => p.1 ≠ p.2
  have hsum : ∑ p ∈ U, ((pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) - a) =
      #U * ((pairColorDensity S c X Y : ℝ) - a) := by
    have hd : (pairColorDensity S c X Y : ℝ) * #U =
        #((X ×ˢ Y).filter fun p => S.colorOfPair p.1 p.2 = some c) :=
      mod_cast pairColorDensity_mul_card_support S c X Y
    rw [sum_sub_distrib, S.sum_pairColorDensity_part_eq_card hX hY c, ← hd, sum_const,
      nsmul_eq_mul]
    ring
  have hcs := sum_mul_sq_le_sq_mul_sq U (fun _ ↦ (1 : ℝ))
    (fun p ↦ (pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) - a)
  simp only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [hsum] at hcs
  obtain hU | hU := (Nat.cast_nonneg (α := ℝ) #U).eq_or_lt
  · rw [← hU, zero_mul]
    exact sum_nonneg fun _ _ ↦ sq_nonneg _
  · nlinarith

variable [Fintype κ]

/-- The **energy** of a partition `P` of the vertices for the pair-color system `S`: the mean,
over the ordered distinct pairs `(u, v)`, of `∑ c, d_c(P.part u, P.part v)²`, where
`d_c = pairColorDensity S c` is the density of `c` among the ordered distinct pairs of a block. It
is `0` when `V` has fewer than two vertices. -/
noncomputable def energy (P : Finpartition (univ : Finset V)) : ℝ :=
  (∑ p ∈ (univ : Finset V).offDiag, ∑ c,
      (pairColorDensity S c (P.part p.1) (P.part p.2) : ℝ) ^ 2) / #(univ : Finset V).offDiag

/-- Unfolding lemma for `TauCeti.PairColorSystem.energy`. -/
theorem energy_def (P : Finpartition (univ : Finset V)) :
    S.energy P = (∑ p ∈ (univ : Finset V).offDiag, ∑ c,
      (pairColorDensity S c (P.part p.1) (P.part p.2) : ℝ) ^ 2) / #(univ : Finset V).offDiag :=
  (rfl)

/-- The energy is nonnegative. -/
theorem energy_nonneg (P : Finpartition (univ : Finset V)) : 0 ≤ S.energy P :=
  div_nonneg (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg _)

omit [Fintype V] [DecidableEq V] in
/-- The squared color densities of a pair of sets sum to at most one, since the densities lie in
`[0, 1]` and sum to at most one. -/
theorem sum_sq_pairColorDensity_le_one (s t : Finset V) :
    ∑ c, (pairColorDensity S c s t : ℝ) ^ 2 ≤ 1 :=
  calc ∑ c, (pairColorDensity S c s t : ℝ) ^ 2
      ≤ ∑ c, (pairColorDensity S c s t : ℝ) :=
        sum_le_sum fun c _ ↦ pow_le_of_le_one (mod_cast pairColorDensity_nonneg S c _ _)
          (mod_cast pairColorDensity_le_one S c _ _) two_ne_zero
    _ ≤ 1 := by
        have h : ((∑ c, pairColorDensity S c s t : ℚ) : ℝ) ≤ 1 :=
          mod_cast sum_pairColorDensity_le_one S s t
        rwa [Rat.cast_sum] at h

/-- The energy is at most one, since on each block the color densities lie in `[0, 1]` and sum to
at most one. -/
theorem energy_le_one (P : Finpartition (univ : Finset V)) : S.energy P ≤ 1 := by
  refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
  calc _ ≤ ∑ _p ∈ (univ : Finset V).offDiag, (1 : ℝ) :=
        sum_le_sum fun p _ ↦ S.sum_sq_pairColorDensity_le_one _ _
    _ = #(univ : Finset V).offDiag := by rw [sum_const, nsmul_one]

/-- **Energy is stable under moving few points.** If two partitions have the same part through
every point outside a set `B`, then their energies differ by at most `2 #B |V|` divided by the
number `|V| (|V| - 1)` of ordered distinct pairs: only the blocks through pairs meeting `B`
change, and each contributes a term in `[0, 1]`. -/
theorem abs_energy_sub_energy_le (B : Finset V) (hB : ∀ u ∉ B, P.part u = Q.part u) :
    |S.energy P - S.energy Q| ≤
      2 * #B * Fintype.card V / #(univ : Finset V).offDiag := by
  classical
  set f : Finpartition (univ : Finset V) → V × V → ℝ :=
    fun R p ↦ ∑ c, (pairColorDensity S c (R.part p.1) (R.part p.2) : ℝ) ^ 2
  -- Only the ordered distinct pairs meeting `B` contribute, each by at most one.
  have hpair (p : V × V) : |f P p - f Q p| ≤ if p.1 ∈ B ∨ p.2 ∈ B then 1 else 0 := by
    split_ifs with hp
    · have h₀ (R) : 0 ≤ f R p := sum_nonneg fun _ _ ↦ sq_nonneg _
      have h₁ (R) : f R p ≤ 1 := S.sum_sq_pairColorDensity_le_one _ _
      rw [abs_le]
      constructor <;> linarith [h₀ P, h₀ Q, h₁ P, h₁ Q]
    · rw [not_or] at hp
      simp [f, hB _ hp.1, hB _ hp.2]
  have hcard : #{p ∈ (univ : Finset V).offDiag | p.1 ∈ B ∨ p.2 ∈ B} ≤
      2 * #B * Fintype.card V :=
    calc #{p ∈ (univ : Finset V).offDiag | p.1 ∈ B ∨ p.2 ∈ B}
        ≤ #(B ×ˢ (univ : Finset V) ∪ (univ : Finset V) ×ˢ B) :=
          card_le_card fun p hp ↦ by
            obtain hp₁ | hp₂ := (mem_filter.1 hp).2
            · exact mem_union_left _ (mem_product.2 ⟨hp₁, mem_univ _⟩)
            · exact mem_union_right _ (mem_product.2 ⟨mem_univ _, hp₂⟩)
      _ ≤ #(B ×ˢ (univ : Finset V)) + #((univ : Finset V) ×ˢ B) := card_union_le _ _
      _ = 2 * #B * Fintype.card V := by rw [card_product, card_product, card_univ]; ring
  rw [energy_def, energy_def, ← sub_div, abs_div, Nat.abs_cast, ← sum_sub_distrib]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  calc |∑ p ∈ (univ : Finset V).offDiag, (f P p - f Q p)|
      ≤ ∑ p ∈ (univ : Finset V).offDiag, |f P p - f Q p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ (univ : Finset V).offDiag, if p.1 ∈ B ∨ p.2 ∈ B then (1 : ℝ) else 0 :=
        sum_le_sum fun p _ ↦ hpair p
    _ = #{p ∈ (univ : Finset V).offDiag | p.1 ∈ B ∨ p.2 ∈ B} := by
        rw [← sum_filter, sum_const, nsmul_one]
    _ ≤ 2 * #B * Fintype.card V := by exact_mod_cast hcard

/-! ### Refinement -/

section Refinement

variable (h : Q ≤ P)
include h

omit [Fintype κ] in
/-- The correlation between the fine and the coarse block densities of a color is the mean square
of the coarse density, since the coarse density is constant on the fine blocks. -/
private theorem sum_pairColorDensity_part_mul_pairColorDensity_part (c : κ) :
    ∑ p ∈ (univ : Finset V).offDiag, (pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) *
        pairColorDensity S c (P.part p.1) (P.part p.2) =
      ∑ p ∈ (univ : Finset V).offDiag,
        (pairColorDensity S c (P.part p.1) (P.part p.2) : ℝ) ^ 2 := by
  classical
  simp_rw [sq]
  rw [S.sum_pairColorDensity_part_mul Q c _ fun x y h₁ h₂ ↦ by
      rw [Finpartition.part_eq_part_of_le h h₁, Finpartition.part_eq_part_of_le h h₂],
    S.sum_pairColorDensity_part_mul P c _ fun x y h₁ h₂ ↦ by rw [h₁, h₂]]

/-- **Refinement defect identity.** For a refinement `Q ≤ P`, the mean over the ordered distinct
pairs of the squared deviations of the block densities of `Q` from those of `P`, summed over
colors, equals the energy gap. -/
theorem sum_sq_pairColorDensity_sub_div_eq_energy_sub :
    (∑ p ∈ (univ : Finset V).offDiag, ∑ c,
        ((pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
          pairColorDensity S c (P.part p.1) (P.part p.2)) ^ 2) / #(univ : Finset V).offDiag =
      S.energy Q - S.energy P := by
  rw [energy_def, energy_def, ← sub_div, sum_comm,
    sum_comm (s := (univ : Finset V).offDiag) (t := univ)
      (f := fun p c ↦ (pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) ^ 2),
    sum_comm (s := (univ : Finset V).offDiag) (t := univ)
      (f := fun p c ↦ (pairColorDensity S c (P.part p.1) (P.part p.2) : ℝ) ^ 2),
    ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun c _ ↦ ?_
  have hc := S.sum_pairColorDensity_part_mul_pairColorDensity_part h c
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, mul_assoc, ← mul_sum] at hc ⊢
  rw [hc]
  ring

/-- **Monotonicity under refinement.** If `Q` refines `P`, the energy of `Q` is at least the
energy of `P`. -/
theorem energy_mono_of_refines : S.energy P ≤ S.energy Q := by
  rw [← sub_nonneg, ← S.sum_sq_pairColorDensity_sub_div_eq_energy_sub h]
  exact div_nonneg (sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ sq_nonneg _) (Nat.cast_nonneg _)

omit h in
/-- **A resolved witness forces a gain on its block.** Let `A ×ˢ B` be a block of parts of `P`,
and let `X ×ˢ Y ⊆ A ×ˢ B` be a rectangle whose sides are unions of parts of `Q`. If the rectangle
has at least an `α`-fraction of the ordered distinct pairs of the block, and its density of `c` is
at least `δ` away from that of the block, then the squared deviations of the block densities of
`Q` from those of `P`, summed over the colors and over the ordered distinct pairs of the block,
total at least `α δ²` times the number of those pairs. -/
theorem mul_card_le_sum_sq_pairColorDensity_sub_of_witness {A B X Y : Finset V} (hA : A ∈ P.parts)
    (hB : B ∈ P.parts) (hXA : X ⊆ A) (hYB : Y ⊆ B) (hX : ∀ C ∈ Q.parts, C ⊆ X ∨ Disjoint C X)
    (hY : ∀ C ∈ Q.parts, C ⊆ Y ∨ Disjoint C Y) (c : κ) {α δ : ℝ} (hδ : 0 ≤ δ)
    (hsize : α * #((A ×ˢ B).filter fun p => p.1 ≠ p.2) ≤ #((X ×ˢ Y).filter fun p => p.1 ≠ p.2))
    (hdev : δ ≤ |(pairColorDensity S c X Y : ℝ) - pairColorDensity S c A B|) :
    α * δ ^ 2 * #((A ×ˢ B).filter fun p => p.1 ≠ p.2) ≤
      ∑ x ∈ (A ×ˢ B).filter (fun p => p.1 ≠ p.2), ∑ k,
        ((pairColorDensity S k (Q.part x.1) (Q.part x.2) : ℝ) -
          pairColorDensity S k (P.part x.1) (P.part x.2)) ^ 2 := by
  set T := (A ×ˢ B).filter fun p ↦ p.1 ≠ p.2
  set U := (X ×ˢ Y).filter fun p ↦ p.1 ≠ p.2
  have hUT : U ⊆ T := filter_subset_filter _ (product_subset_product hXA hYB)
  have hsq : δ ^ 2 ≤ ((pairColorDensity S c X Y : ℝ) - pairColorDensity S c A B) ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ hδ hdev 2
  -- The size and deviation bounds give `α δ² #T ≤ #U · dev²`; Cauchy–Schwarz on the resolved
  -- rectangle bounds this by the deviations of the fine densities over `U`, where the coarse
  -- density is constant, and finally we enlarge to all colors and to the whole block.
  calc α * δ ^ 2 * #T = δ ^ 2 * (α * #T) := by ring
    _ ≤ δ ^ 2 * #U := mul_le_mul_of_nonneg_left hsize (sq_nonneg _)
    _ ≤ #U * ((pairColorDensity S c X Y : ℝ) - pairColorDensity S c A B) ^ 2 := by
      nlinarith [Nat.cast_nonneg (α := ℝ) #U]
    _ ≤ ∑ x ∈ U, ((pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
        pairColorDensity S c A B) ^ 2 :=
      S.card_mul_sq_pairColorDensity_sub_le_sum hX hY c _
    _ = ∑ x ∈ U, ((pairColorDensity S c (Q.part x.1) (Q.part x.2) : ℝ) -
        pairColorDensity S c (P.part x.1) (P.part x.2)) ^ 2 := by
      refine sum_congr rfl fun x hx ↦ ?_
      obtain ⟨hx, -⟩ := mem_filter.1 (hUT hx)
      obtain ⟨hx₁, hx₂⟩ := mem_product.1 hx
      rw [P.part_eq_of_mem hA hx₁, P.part_eq_of_mem hB hx₂]
    _ ≤ _ := by
      refine (sum_le_sum fun x _ ↦ single_le_sum
        (f := fun k ↦ ((pairColorDensity S k (Q.part x.1) (Q.part x.2) : ℝ) -
          pairColorDensity S k (P.part x.1) (P.part x.2)) ^ 2)
        (fun k _ ↦ sq_nonneg _) (mem_univ c)).trans ?_
      exact sum_le_sum_of_subset_of_nonneg hUT fun x _ _ ↦ sum_nonneg fun k _ ↦ sq_nonneg _

/-- **Resolved witnesses force an energy gain.** Let `Q` refine `P`, and let `B` be a family of
pairs of parts of `P`. For each block `A ×ˢ B` in the family choose a color and a rectangle
`X ×ˢ Y ⊆ A ×ˢ B` whose sides are unions of parts of `Q`. If each rectangle has at least an
`α`-fraction of the ordered distinct pairs of its block, and a color density at least `δ` away
from the density on the block, then the energy gap is at least `α δ²` times the proportion of
ordered distinct pairs lying in the blocks of the family. -/
theorem energy_increment_of_witnesses (B : Finset (Finset V × Finset V))
    (hB : ∀ AB ∈ B, AB.1 ∈ P.parts ∧ AB.2 ∈ P.parts) (c : Finset V × Finset V → κ)
    (X Y : Finset V × Finset V → Finset V) {α δ : ℝ} (hδ : 0 ≤ δ)
    (hXsub : ∀ AB ∈ B, X AB ⊆ AB.1) (hYsub : ∀ AB ∈ B, Y AB ⊆ AB.2)
    (hX : ∀ AB ∈ B, ∀ C ∈ Q.parts, C ⊆ X AB ∨ Disjoint C (X AB))
    (hY : ∀ AB ∈ B, ∀ C ∈ Q.parts, C ⊆ Y AB ∨ Disjoint C (Y AB))
    (hsize : ∀ AB ∈ B, α * #((AB.1 ×ˢ AB.2).filter fun p => p.1 ≠ p.2) ≤
      #((X AB ×ˢ Y AB).filter fun p => p.1 ≠ p.2))
    (hdev : ∀ AB ∈ B, δ ≤
      |(pairColorDensity S (c AB) (X AB) (Y AB) : ℝ) - pairColorDensity S (c AB) AB.1 AB.2|) :
    α * δ ^ 2 * ((∑ AB ∈ B, (#((AB.1 ×ˢ AB.2).filter fun p => p.1 ≠ p.2) : ℝ)) /
        #(univ : Finset V).offDiag) ≤
      S.energy Q - S.energy P := by
  set T : Finset V × Finset V → Finset (V × V) := fun AB ↦ (AB.1 ×ˢ AB.2).filter fun p ↦ p.1 ≠ p.2
  let d : V × V → κ → ℝ := fun x k ↦ ((pairColorDensity S k (Q.part x.1) (Q.part x.2) : ℝ) -
    pairColorDensity S k (P.part x.1) (P.part x.2)) ^ 2
  have hlocal (AB : Finset V × Finset V) (hAB : AB ∈ B) :
      α * δ ^ 2 * #(T AB) ≤ ∑ x ∈ T AB, ∑ k, d x k :=
    S.mul_card_le_sum_sq_pairColorDensity_sub_of_witness (hB AB hAB).1 (hB AB hAB).2 (hXsub AB hAB)
      (hYsub AB hAB) (hX AB hAB) (hY AB hAB) (c AB) hδ (hsize AB hAB) (hdev AB hAB)
  -- Blocks of distinct pairs of parts are disjoint.
  have hdisj : (B : Set (Finset V × Finset V)).PairwiseDisjoint T := by
    intro AB hAB AB' hAB' hne
    refine disjoint_filter_filter (disjoint_product.2 ?_)
    by_cases h₁ : AB.1 = AB'.1
    · exact Or.inr (P.disjoint (hB AB hAB).2 (hB AB' hAB').2 fun h₂ ↦ hne (Prod.ext h₁ h₂))
    · exact Or.inl (P.disjoint (hB AB hAB).1 (hB AB' hAB').1 h₁)
  have hsub : B.biUnion T ⊆ (univ : Finset V).offDiag := fun x hx ↦ by
    obtain ⟨AB, -, hx⟩ := mem_biUnion.1 hx
    exact mem_offDiag.2 ⟨mem_univ _, mem_univ _, (mem_filter.1 hx).2⟩
  have hsum : α * δ ^ 2 * (∑ AB ∈ B, (#(T AB) : ℝ)) ≤
      ∑ x ∈ (univ : Finset V).offDiag, ∑ k, d x k := by
    calc _ = ∑ AB ∈ B, α * δ ^ 2 * #(T AB) := mul_sum ..
      _ ≤ ∑ AB ∈ B, ∑ x ∈ T AB, ∑ k, d x k := sum_le_sum hlocal
      _ = ∑ x ∈ B.biUnion T, ∑ k, d x k := (sum_biUnion hdisj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hsub fun x _ _ ↦ sum_nonneg fun k _ ↦ sq_nonneg _
  rw [← S.sum_sq_pairColorDensity_sub_div_eq_energy_sub h, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

end Refinement

end TauCeti.PairColorSystem
