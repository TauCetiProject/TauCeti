/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Energy
public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Tactic.Linarith
import TauCeti.Algebra.Order.Field.Basic
import TauCeti.Data.Finset.Basic
import TauCeti.Order.Partition.Finpartition

/-!
# A regularity lemma for pair-color systems

Let `S` be a pair-color system with a finite palette on a finite vertex type `V`, and let
`P₀` be a partition of the vertices. For `ε > 0`, `P₀` has a refinement `P` with a number of
parts bounded independently of `S` and of `|V|`, all of its parts having at most `ε |V| + 1`
vertices, such that the ordered pairs `(A, B)` of distinct parts of `P` that are not `ε`-regular
for `S` cover at most `ε |V|²` ordered pairs of vertices
(`TauCeti.PairColorSystem.exists_refinement_sum_irregularPairs_le`). Regularity is
coordinatewise, `TauCeti.PairColorSystem.IsRegularPair`: every color is controlled at once, and
colors need not be symmetric. For the two-color system of a simple graph, where regular pairs of
disjoint sets are uniform at every larger parameter
(`TauCeti.PairColorSystem.IsRegularPair.isUniform`), it gives a
size-weighted form of Szemerédi's regularity lemma without equitability.

Diagonal pairs `(A, A)` are not tested for regularity, and the lemma says nothing about them.
Since every part has at most `ε |V| + 1` vertices, the diagonal blocks together contain at most
`∑ A, #A (#A - 1) ≤ ε |V| ∑ A, #A = ε |V|²` ordered distinct pairs.

The proof first cuts `P₀` along an equipartition into `⌈1 / ε⌉` parts, which makes the parts
small; refining further keeps them small. It then runs the energy increment argument for
`TauCeti.PairColorSystem.energy`. If the irregular pairs of `P` cover more than `ε |V|²` pairs,
choose for each of them a color and a witness rectangle `X ×ˢ Y` with `ε |A| ≤ |X|`,
`ε |B| ≤ |Y|` and color density more than `ε` away from that of `A ×ˢ B`. Cutting all parts
along all the witnesses (`Finpartition.atomise`) gives a refinement with at most
`#P.parts * 4 ^ #P.parts ^ 2` parts, over which every witness is a union of parts, so its energy
exceeds that of `P` by more than `ε⁵`
(`TauCeti.PairColorSystem.exists_refinement_energy_add_lt`). The energy lies in `[0, 1]`, so
`⌈1 / ε⁵⌉` rounds suffice.

## Main definitions

* `TauCeti.PairColorSystem.irregularPairs`: the ordered pairs of distinct parts that are not
  `ε`-regular.
* `TauCeti.pairColorRegularityBound`: the bound on the number of parts.

## Main results

* `TauCeti.PairColorSystem.exists_refinement_energy_add_lt`: the energy increment step.
* `TauCeti.PairColorSystem.exists_refinement_sum_irregularPairs_le`: the regularity lemma,
  refining a given partition.

## References

* E. Szemerédi, *Regular partitions of graphs* (1978).
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), where the pair-level regularization of a partition of the
  pairs underlies the regularity lemma for three-uniform hypergraphs.
* The cutting step follows Mathlib's `SzemerediRegularity.chunk`, which uses
  `Finpartition.atomise` along nonuniformity witnesses.
-/

public section

open Finset Finpartition

namespace TauCeti

/-- The bound on the number of parts in the regularity lemma for pair-color systems, starting
from `m` parts. Cutting along an equipartition into `⌈1 / ε⌉` parts gives at most `m ⌈1 / ε⌉`
parts, each round of the energy increment multiplies a number `m'` of parts by at most
`4 ^ m' ^ 2`, and `⌈1 / ε⁵⌉` rounds suffice. -/
noncomputable def pairColorRegularityBound (ε : ℝ) (m : ℕ) : ℕ :=
  (fun m ↦ m * 4 ^ m ^ 2)^[⌈1 / ε ^ 5⌉₊] (m * ⌈1 / ε⌉₊)

/-- Unfolding lemma for `TauCeti.pairColorRegularityBound`. -/
theorem pairColorRegularityBound_def (ε : ℝ) (m : ℕ) :
    pairColorRegularityBound ε m = (fun m ↦ m * 4 ^ m ^ 2)^[⌈1 / ε ^ 5⌉₊] (m * ⌈1 / ε⌉₊) :=
  (rfl)

/-- The growth of the number of parts in one round of the energy increment is monotone. -/
private theorem monotone_mul_four_pow_sq : Monotone fun m : ℕ ↦ m * 4 ^ m ^ 2 := fun a b hab ↦
  Nat.mul_le_mul hab (Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_left hab 2))

namespace PairColorSystem

variable {κ V : Type*} [Fintype V] [DecidableEq V] (S : PairColorSystem κ V) {ε : ℝ}
  {P : Finpartition (univ : Finset V)}

open Classical in
/-- The ordered pairs `(A, B)` of distinct parts of `P` that are not `ε`-regular for `S`. -/
noncomputable def irregularPairs (ε : ℝ) (P : Finpartition (univ : Finset V)) :
    Finset (Finset V × Finset V) :=
  P.parts.offDiag.filter fun AB ↦ ¬S.IsRegularPair ε AB.1 AB.2

/-- Membership in `TauCeti.PairColorSystem.irregularPairs`. -/
@[simp]
theorem mem_irregularPairs {AB : Finset V × Finset V} :
    AB ∈ S.irregularPairs ε P ↔
      AB.1 ∈ P.parts ∧ AB.2 ∈ P.parts ∧ AB.1 ≠ AB.2 ∧ ¬S.IsRegularPair ε AB.1 AB.2 := by
  simp only [irregularPairs, mem_filter, mem_offDiag, and_assoc]

/-- The irregular pairs are ordered pairs of distinct parts. -/
theorem irregularPairs_subset_offDiag : S.irregularPairs ε P ⊆ P.parts.offDiag := fun AB hAB ↦ by
  obtain ⟨h₁, h₂, h₃, -⟩ := S.mem_irregularPairs.1 hAB
  exact mem_offDiag.2 ⟨h₁, h₂, h₃⟩

/-- Choosing two sets for each irregular pair gives at most `2 * #P.parts ^ 2` sets. -/
private theorem card_image_union_irregularPairs_le (P : Finpartition (univ : Finset V))
    (X Y : Finset V × Finset V → Finset V) :
    #((S.irregularPairs ε P).image X ∪ (S.irregularPairs ε P).image Y) ≤ 2 * #P.parts ^ 2 := by
  have hI : #(S.irregularPairs ε P) ≤ #P.parts * #P.parts :=
    (card_le_card S.irregularPairs_subset_offDiag).trans
      ((card_offDiag_le_sq P.parts).trans_eq (sq _))
  calc _ ≤ #((S.irregularPairs ε P).image X) + #((S.irregularPairs ε P).image Y) :=
        card_union_le _ _
    _ ≤ #(S.irregularPairs ε P) + #(S.irregularPairs ε P) :=
        add_le_add card_image_le card_image_le
    _ ≤ 2 * #P.parts ^ 2 := by rw [sq]; omega

variable [Fintype κ]

/-- **Energy increment.** If the ordered pairs of distinct parts of `P` that are not `ε`-regular
for `S` cover more than `ε |V|²` ordered pairs of vertices, then cutting the parts of `P` along
witnesses of irregularity gives a refinement with at most `#P.parts * 4 ^ #P.parts ^ 2` parts
whose energy exceeds that of `P` by more than `ε⁵`. -/
theorem exists_refinement_energy_add_lt (P : Finpartition (univ : Finset V)) (hε : 0 < ε)
    (hbad : ε * (Fintype.card V : ℝ) ^ 2 <
      ∑ AB ∈ S.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ)) :
    ∃ Q : Finpartition (univ : Finset V), Q ≤ P ∧ #Q.parts ≤ #P.parts * 4 ^ #P.parts ^ 2 ∧
      S.energy P + ε ^ 5 < S.energy Q := by
  classical
  set I := S.irregularPairs ε P
  have hmem {AB} (hAB : AB ∈ I) := (S.mem_irregularPairs).1 hAB
  have hdisj {AB} (hAB : AB ∈ I) : Disjoint AB.1 AB.2 :=
    P.disjoint (hmem hAB).1 (hmem hAB).2.1 (hmem hAB).2.2.1
  -- Each irregular pair has a color and a witness rectangle.
  have hw : ∀ AB ∈ I, ∃ c : κ, ∃ X ⊆ AB.1, ∃ Y ⊆ AB.2, ε * #AB.1 ≤ #X ∧ ε * #AB.2 ≤ #Y ∧
      ε < |(pairColorDensity S c X Y : ℝ) - pairColorDensity S c AB.1 AB.2| := by
    intro AB hAB
    simpa only [isRegularPair_iff, not_forall, not_le, exists_prop] using (hmem hAB).2.2.2
  obtain ⟨AB₀, hAB₀⟩ : I.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro hempty
    rw [hempty, sum_empty] at hbad
    nlinarith [sq_nonneg (Fintype.card V : ℝ)]
  have : Nonempty κ := ⟨(hw AB₀ hAB₀).choose⟩
  choose! c X hXsub Y hYsub hXcard hYcard hdev using hw
  set R := atomise univ (I.image X ∪ I.image Y)
  refine ⟨P ⊓ R, inf_le_left, ?_, ?_⟩
  · -- There are at most `2 * #P.parts ^ 2` witnesses to cut along.
    calc #(P ⊓ R).parts ≤ #P.parts * 2 ^ #(I.image X ∪ I.image Y) :=
          P.card_parts_inf_atomise_le _
      _ ≤ #P.parts * 2 ^ (2 * #P.parts ^ 2) :=
          Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right two_pos (S.card_image_union_irregularPairs_le P X Y))
      _ = #P.parts * 4 ^ #P.parts ^ 2 := by rw [pow_mul]; norm_num
  · -- Every witness is a union of parts of the refinement.
    have hres {Z : Finset V} (hZ : Z ∈ I.image X ∪ I.image Y) :
        ∀ C ∈ (P ⊓ R).parts, C ⊆ Z ∨ Disjoint C Z :=
      fun _ hC ↦ subset_or_disjoint_of_mem_inf_atomise hC hZ
    -- Each witness rectangle carries an `ε²`-fraction of its block.
    have hsize : ∀ AB ∈ I, ε ^ 2 * #((AB.1 ×ˢ AB.2).filter fun p => p.1 ≠ p.2) ≤
        (#((X AB ×ˢ Y AB).filter fun p => p.1 ≠ p.2) : ℝ) := fun AB hAB ↦
      Finset.sq_mul_card_filter_ne_product_le hε.le (hdisj hAB) (hXsub AB hAB) (hYsub AB hAB)
        (hXcard AB hAB) (hYcard AB hAB)
    have hgain := S.energy_increment_of_witnesses (inf_le_left : P ⊓ R ≤ P) I
      (fun AB hAB ↦ ⟨(hmem hAB).1, (hmem hAB).2.1⟩) c X Y hε.le hXsub hYsub
      (fun AB hAB ↦ hres (mem_union_left _ (mem_image_of_mem X hAB)))
      (fun AB hAB ↦ hres (mem_union_right _ (mem_image_of_mem Y hAB))) hsize
      (fun AB hAB ↦ (hdev AB hAB).le)
    -- The blocks of the irregular pairs are the full rectangles `A ×ˢ B`.
    have hblocks : ∑ AB ∈ I, (#((AB.1 ×ˢ AB.2).filter fun p => p.1 ≠ p.2) : ℝ) =
        ∑ AB ∈ I, (#AB.1 * #AB.2 : ℝ) := sum_congr rfl fun AB hAB ↦ by
      rw [filter_ne_product_of_disjoint (hdisj hAB), card_product, Nat.cast_mul]
    rw [hblocks] at hgain
    set M := ∑ AB ∈ I, (#AB.1 * #AB.2 : ℝ)
    set D := (#(univ : Finset V).offDiag : ℝ)
    set n := (Fintype.card V : ℝ)
    -- An irregular pair supplies an ordered distinct pair, so `0 < D ≤ n²`.
    have hD : 0 < D := by
      obtain ⟨a, ha⟩ := P.nonempty_of_mem_parts (hmem hAB₀).1
      obtain ⟨b, hb⟩ := P.nonempty_of_mem_parts (hmem hAB₀).2.1
      exact Nat.cast_pos.2 (card_pos.2 ⟨(a, b), mem_offDiag.2 ⟨mem_univ _, mem_univ _,
        (hdisj hAB₀).forall_ne_finset ha hb⟩⟩)
    have hDn : D ≤ n ^ 2 := by
      have h := (Nat.cast_le (α := ℝ)).2 (card_offDiag_le_sq (univ : Finset V))
      rw [card_univ] at h
      push_cast at h
      exact h
    linarith [TauCeti.pow_five_lt_of_mul_div_le hε hD hDn hbad hgain]

/-- The refinement invariant: after `k` rounds starting from `P₀`, either the irregular pairs
cover at most `ε |V|²` ordered pairs of vertices, or the energy has grown by at least `k ε⁵`. -/
private theorem exists_le_sum_irregularPairs_le_or_energy_add_le
    (P₀ : Finpartition (univ : Finset V)) (hε : 0 < ε) (k : ℕ) :
    ∃ P : Finpartition (univ : Finset V), P ≤ P₀ ∧
      #P.parts ≤ (fun m ↦ m * 4 ^ m ^ 2)^[k] #P₀.parts ∧
      (∑ AB ∈ S.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 ∨
        S.energy P₀ + k * ε ^ 5 ≤ S.energy P) := by
  induction k with
  | zero => exact ⟨P₀, le_rfl, by simp, Or.inr (by simp)⟩
  | succ k ih =>
    obtain ⟨P, hP, hcard, hP'⟩ := ih
    by_cases hgood : ∑ AB ∈ S.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ) ≤
      ε * (Fintype.card V : ℝ) ^ 2
    · refine ⟨P, hP, hcard.trans ?_, Or.inl hgood⟩
      rw [Function.iterate_succ_apply']
      exact Nat.le_mul_of_pos_right _ (by positivity)
    obtain ⟨Q, hQ, hQcard, hQenergy⟩ := S.exists_refinement_energy_add_lt P hε (not_le.1 hgood)
    refine ⟨Q, hQ.trans hP, ?_, Or.inr ?_⟩
    · rw [Function.iterate_succ_apply']
      exact hQcard.trans (monotone_mul_four_pow_sq hcard)
    · push_cast
      linarith [hP'.resolve_left hgood]

omit [Fintype κ] in
/-- **Regularity lemma for pair-color systems**, refining form. For `ε > 0`, every partition
`P₀` of the vertices is refined by a partition `P` with at most
`pairColorRegularityBound ε #P₀.parts` parts, each with at most `ε |V| + 1` vertices, such that
the ordered pairs `(A, B)` of distinct parts of `P` that are not `ε`-regular for `S` cover at most
`ε |V|²` ordered pairs of vertices. The bound depends only on `ε` and `#P₀.parts`. Diagonal pairs
`(A, A)` are not tested for regularity; the bound on the parts makes their blocks contain at most
`ε |V|²` ordered distinct pairs in total. -/
theorem exists_refinement_sum_irregularPairs_le [Finite κ] (P₀ : Finpartition (univ : Finset V))
    (hε : 0 < ε) :
    ∃ P : Finpartition (univ : Finset V), P ≤ P₀ ∧
      #P.parts ≤ pairColorRegularityBound ε #P₀.parts ∧
      (∀ A ∈ P.parts, (#A : ℝ) ≤ ε * Fintype.card V + 1) ∧
      ∑ AB ∈ S.irregularPairs ε P, (#AB.1 * #AB.2 : ℝ) ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  have := Fintype.ofFinite κ
  -- Cut `P₀` along an equipartition into `⌈1 / ε⌉` parts, then run the energy increment.
  set k := ⌈1 / ε⌉₊
  have hk₀ : 0 < k := Nat.ceil_pos.2 (by positivity)
  have hk : (1 : ℝ) ≤ ε * k := (div_le_iff₀' hε).1 (Nat.le_ceil _)
  obtain ⟨E, hEcard, hEsize⟩ := exists_card_parts_le_card_le (univ : Finset V) hk₀.ne'
  obtain ⟨P, hP, hcard, hP'⟩ :=
    S.exists_le_sum_irregularPairs_le_or_energy_add_le (P₀ ⊓ E) hε ⌈1 / ε ^ 5⌉₊
  refine ⟨P, hP.trans inf_le_left, ?_, fun A hA ↦ ?_, ?_⟩
  · rw [pairColorRegularityBound_def]
    exact hcard.trans (monotone_mul_four_pow_sq.iterate _
      ((card_parts_inf_le_mul P₀ E).trans (Nat.mul_le_mul_left _ hEcard)))
  · -- Each part lies in a part of `E`, which has at most `|V| / k + 1 ≤ ε |V| + 1` vertices.
    obtain ⟨C, hC, hAC⟩ := (hP.trans inf_le_right) hA
    have hdiv : ((Fintype.card V / k : ℕ) : ℝ) ≤ ε * Fintype.card V := by
      calc ((Fintype.card V / k : ℕ) : ℝ) ≤ (Fintype.card V : ℝ) / k := Nat.cast_div_le
        _ ≤ ε * Fintype.card V := by
          rw [div_le_iff₀ (Nat.cast_pos.2 hk₀)]
          nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card V)]
    have hC' := Nat.cast_le (α := ℝ) |>.2 ((card_le_card hAC).trans (hEsize C hC))
    rw [card_univ, Nat.cast_add, Nat.cast_one] at hC'
    linarith
  obtain hgood | henergy := hP'
  · exact hgood
  -- Otherwise one more increment would push the energy above its upper bound `1`.
  by_contra! hbad
  obtain ⟨Q, -, -, hQ⟩ := S.exists_refinement_energy_add_lt P hε hbad
  have hN : 1 ≤ (⌈1 / ε ^ 5⌉₊ : ℝ) * ε ^ 5 :=
    (div_le_iff₀ (by positivity)).1 (Nat.le_ceil (1 / ε ^ 5))
  linarith [S.energy_nonneg (P₀ ⊓ E), S.energy_le_one Q, pow_pos hε 5]

end PairColorSystem

end TauCeti
