/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.SeededRegularization
public import TauCeti.Combinatorics.Hypergraph.PairColor.CoupledRecoloring
public import TauCeti.Combinatorics.Hypergraph.PairColor.Diagonal
public import Mathlib.Data.Fintype.Option
import TauCeti.Algebra.BigOperators.Finset.WeightedCauchySchwarz
import TauCeti.Combinatorics.Regularity.Partition.Equitabilise
import TauCeti.Data.Finset.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Rat.BigOperators
import Mathlib.Order.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Strong regular approximation for pair-color systems

Let `S` be a pair-color system with a finite palette `κ` on a finite vertex type `V`, let `P₀` be
an equipartition of `V`, let `ε > 0`, and let `F : ℕ → ℝ` be an arbitrary positive regularity
schedule (`∀ m, 0 < F m`). Provided `V` has at least `strongPairColorApproximationBound` vertices
(a bound depending only on `|κ|`, `ε`, `F`, the requested minimum part count `t₀`, and
`#P₀.parts`), there exist an exact-refining equipartition `P ≤ P₀` with `t₀ ≤ #P.parts` and a
pair-color system `T` over `Option κ` whose lower skeleton `⟨P, T⟩` satisfies
`PairSkeleton3.LowerSkeletonRegular F` and edits `S` on at most `ε |V|²` ordered pairs of
vertices (`TauCeti.PairColorSystem.exists_strong_regular_approximation`).

Unlike ordinary pair-color regularity, here the regularity accuracy `F (#P.parts + |Option κ|)` is
permitted to shrink arbitrarily fast with `#P.parts`, with *no* exceptional irregular pairs left
behind. Achieving this requires modifying `S` on `o(|V|²)` pairs via the strong-regularity +
coupled-recoloring method:

1. **Strong regularity witness (`exists_strong_regular_witness`).** Iterating seeded equitable
   pair-color regularization (`PairColorSystem.exists_refining_equipartition_sum_irregularPairs_le`)
   at the schedule-dependent accuracy `τ (#P.parts)` and applying pigeonhole to
   `PairColorSystem.energy ∈ [0, 1]` yields equipartitions `Q ≤ P ≤ P₀` such that `Q` is
   `τ (#P.parts)`-regular up to `τ (#P.parts) |V|²` irregular fine pairs while
   `S.energy Q - S.energy P ≤ g`.
2. **Energy-gap `L¹` control (`sum_sum_abs_pairColorDensity_sub_le_of_energy_sub_le`).** By the
   orthogonality identity `PairColorSystem.sum_sq_pairColorDensity_sub_div_eq_energy_sub` and
   weighted Cauchy–Schwarz (`Finset.weighted_sum_abs_le_sqrt`), the small energy gap bounds the
   size-weighted `L¹` deviation between fine block densities on `Q` and their coarse parent
   densities on `P`.
3. **Off-diagonal coupled recoloring (`exists_strong_regular_approximation_offDiag`).** Regular
   fine blocks in distinct coarse cells are recolored toward their coarse parent densities using
   `PairColorSystem.exists_coupled_recoloring_abs_card_filter_sub_le`, paying edit cost controlled
   by the `L¹` density deviation; rare irregular fine blocks are recolored unconditionally via
   `PairColorSystem.exists_recoloring_abs_card_filter_sub_le`. Gluing via
   `PairColorSystem.exists_offDiag_recoloring_of_refines` makes every distinct coarse pair
   `(A, B)` of `P` `G (#P.parts)`-regular within `ε |V|²` edits while preserving `S.rev` and
   within-cell colors.
4. **Diagonal cleanup (`exists_strong_regular_approximation`).** Applying
   `PairColorSystem.fillDiagonal` assigns the fresh reversal-fixed color `none` inside each cell of
   `P`, upgrading off-diagonal regularity to full `PairSkeleton3.LowerSkeletonRegular F` at diagonal
   edit cost at most `(|V|² / #P.parts) ≤ (ε / 2) |V|²`.

## Main definitions

* `TauCeti.strongPairColorWitnessBound`: upper bound on the number of parts of the witness
  equipartition.
* `TauCeti.strongPairColorOffDiagBound`: host-size threshold for off-diagonal strong regular
  approximation.
* `TauCeti.strongPairColorApproximationBound`: host-size threshold for lower-skeleton strong
  regular approximation.

## Main results

* `TauCeti.PairColorSystem.exists_strong_regular_approximation_offDiag`: off-diagonal strong
  regular approximation preserving the palette `κ` and within-cell colors.
* `TauCeti.PairColorSystem.exists_strong_regular_approximation`: seeded lower-skeleton strong
  regular approximation over `Option κ`.
* `TauCeti.PairColorSystem.exists_strong_regular_approximation_univ`: unseeded lower-skeleton
  strong regular approximation.

## References

* N. Alon, E. Fischer, M. Krivelevich, and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), 451–476.
* L. Lovász and B. Szegedy, *Szemerédi's lemma for the analyst*, Geom. Funct. Anal. 17 (2007),
  252–270.
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*, Combin. Probab.
  Comput. 16 (2007), 833–885, Lemma 4.2 (the Regular Approximation Lemma, adapted here to
  arity-two coherent pair-color systems).
-/

public section

open Finset Finpartition

namespace TauCeti

/-- Fine-regularity accuracy at coarse part count `m` in off-diagonal strong regular
approximation. -/
private noncomputable def strongPairColorFineParam (K : ℕ) (ε : ℝ) (G : ℕ → ℝ) (m : ℕ) : ℝ :=
  min (ε / 3) (min 1 (G m) ^ 3 / (4 * (K + 1)))

/-- Coupled-recoloring parameter at coarse part count `m`. -/
private noncomputable def strongPairColorCoupledParam (ε : ℝ) (G : ℕ → ℝ) (m : ℕ) : ℝ :=
  min (min 1 (ε / 6)) (min 1 (G m) / 2)

/-- Uncoupled-recoloring parameter at coarse part count `m`. -/
private noncomputable def strongPairColorUncoupledParam (G : ℕ → ℝ) (m : ℕ) : ℝ :=
  min 1 (G m) ^ 3 / 6

/-- Monotone envelope of one round of seeded equitable pair-color regularization at the fine
accuracy `strongPairColorFineParam K ε G`. -/
private noncomputable def strongPairColorStep (K : ℕ) (ε : ℝ) (G : ℕ → ℝ) (m : ℕ) : ℕ :=
  (range (m + 1)).sup fun j ↦
    equitablePairColorRegularityBound (strongPairColorFineParam K ε G j) j

private theorem monotone_strongPairColorStep (K : ℕ) (ε : ℝ) (G : ℕ → ℝ) :
    Monotone (strongPairColorStep K ε G) :=
  fun _ _ hm ↦ sup_mono (range_mono (Nat.succ_le_succ hm))

private theorem le_strongPairColorStep {K : ℕ} {ε : ℝ} (hε : 0 < ε) {G : ℕ → ℝ}
    (hG : ∀ m, 0 < G m) (m : ℕ) :
    m ≤ strongPairColorStep K ε G m := by
  have hτ : 0 < strongPairColorFineParam K ε G m := by
    have := hG m
    dsimp [strongPairColorFineParam]
    positivity
  calc m ≤ max m 1 := le_max_left m 1
    _ ≤ equitablePairColorRegularityBound (strongPairColorFineParam K ε G m) m := by
        rw [equitablePairColorRegularityBound_def]
        exact Function.monotone_iterate_of_id_le (le_ceil_mul_mul_four_pow_sq hτ) (Nat.zero_le _) _
    _ ≤ strongPairColorStep K ε G m :=
        le_sup (f := fun j ↦ equitablePairColorRegularityBound
          (strongPairColorFineParam K ε G j) j) (mem_range.2 (Nat.lt_succ_self m))

/-- Upper bound on the part count of the strong-regularity witness equipartitions starting from at
most `m₀` parts. -/
noncomputable def strongPairColorWitnessBound (K : ℕ) (ε : ℝ) (G : ℕ → ℝ) (m₀ : ℕ) : ℕ :=
  (fun m ↦ (range (m + 1)).sup fun j ↦
    equitablePairColorRegularityBound
      (min (ε / 3) (min 1 (G j) ^ 3 / (4 * (K + 1)))) j)^[⌊1 / (ε / (3 * (K + 1))) ^ 2⌋₊ + 1]
    (max m₀ 1)

/-- Unfolding lemma for `TauCeti.strongPairColorWitnessBound`. -/
theorem strongPairColorWitnessBound_def (K : ℕ) (ε : ℝ) (G : ℕ → ℝ) (m₀ : ℕ) :
    strongPairColorWitnessBound K ε G m₀ =
      (fun m ↦ (range (m + 1)).sup fun j ↦
        equitablePairColorRegularityBound
          (min (ε / 3) (min 1 (G j) ^ 3 / (4 * (K + 1)))) j)^[⌊1 / (ε / (3 * (K + 1))) ^ 2⌋₊ + 1]
        (max m₀ 1) :=
  (rfl)

/-- Host-size threshold for `TauCeti.PairColorSystem.exists_strong_regular_approximation_offDiag`:
ensures every fine cell of the witness equipartition passes both the coupled and uncoupled
concentration thresholds. -/
noncomputable def strongPairColorOffDiagBound (K : ℕ) (ε : ℝ) (G : ℕ → ℝ) (m₀ : ℕ) : ℕ :=
  let M := strongPairColorWitnessBound K ε G m₀
  M * ((range (M + 1)).sup (fun j ↦
    max ⌈(K : ℝ) ^ 2 * (K + 2) / min (min 1 (ε / 6)) (min 1 (G j) / 2) ^ 6⌉₊
      ⌈((K : ℝ) + 1) / (min 1 (G j) ^ 3 / 6) ^ 6⌉₊) + 1)

/-- Unfolding lemma for `TauCeti.strongPairColorOffDiagBound`. -/
theorem strongPairColorOffDiagBound_def (K : ℕ) (ε : ℝ) (G : ℕ → ℝ) (m₀ : ℕ) :
    strongPairColorOffDiagBound K ε G m₀ =
      strongPairColorWitnessBound K ε G m₀ *
        ((range (strongPairColorWitnessBound K ε G m₀ + 1)).sup (fun j ↦
          max ⌈(K : ℝ) ^ 2 * (K + 2) / min (min 1 (ε / 6)) (min 1 (G j) / 2) ^ 6⌉₊
            ⌈((K : ℝ) + 1) / (min 1 (G j) ^ 3 / 6) ^ 6⌉₊) + 1) :=
  (rfl)

/-- Host-size threshold for `TauCeti.PairColorSystem.exists_strong_regular_approximation`. -/
noncomputable def strongPairColorApproximationBound
    (K : ℕ) (ε : ℝ) (F : ℕ → ℝ) (t₀ l₀ : ℕ) : ℕ :=
  strongPairColorOffDiagBound K (ε / 2) (fun m ↦ F (m + K + 1))
    (max (max t₀ ⌈2 / ε⌉₊) 1 * l₀)

/-- Unfolding lemma for `TauCeti.strongPairColorApproximationBound`. -/
theorem strongPairColorApproximationBound_def (K : ℕ) (ε : ℝ) (F : ℕ → ℝ) (t₀ l₀ : ℕ) :
    strongPairColorApproximationBound K ε F t₀ l₀ =
      strongPairColorOffDiagBound K (ε / 2) (fun m ↦ F (m + K + 1))
        (max (max t₀ ⌈2 / ε⌉₊) 1 * l₀) :=
  (rfl)

namespace PairColorSystem

section EnergyGap

variable {κ V : Type*} [Fintype V] [DecidableEq V] [Fintype κ] (S : PairColorSystem κ V)

/-- Bound the size-weighted squared deviation of a single color `c` across off-diagonal fine-part
pairs by `g * |V|²` when `S.energy Q - S.energy P ≤ g`. -/
private theorem sum_sq_pairColorDensity_sub_offDiag_le
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {g : ℝ} (hg : 0 ≤ g)
    (hgap : S.energy Q - S.energy P ≤ g) (hoff_pos : 0 < #(univ : Finset V).offDiag) (c : κ) :
    ∑ AB ∈ (univ : Finset (Q.parts × Q.parts)).filter
        (fun AB ↦ refinementParent hQP AB.1 ≠ refinementParent hQP AB.2),
      (#AB.1.1 * #AB.2.1 : ℝ) *
        ((pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1) ^ 2 ≤
      g * (Fintype.card V : ℝ) ^ 2 := by
  set Ω := (univ : Finset (Q.parts × Q.parts)).filter
    fun AB ↦ refinementParent hQP AB.1 ≠ refinementParent hQP AB.2
  have hdisj_rect : (Ω : Set (Q.parts × Q.parts)).PairwiseDisjoint
      (fun AB ↦ AB.1.1 ×ˢ AB.2.1) := fun AB _ CD _ hne ↦ disjoint_product.2 <|
    if h1 : AB.1 = CD.1 then Or.inr (Q.disjoint AB.2.2 CD.2.2 fun h2 ↦
      hne (Prod.ext h1 (Subtype.ext h2)))
    else Or.inl (Q.disjoint AB.1.2 CD.1.2 fun h1' ↦ h1 (Subtype.ext h1'))
  have hsub : Ω.biUnion (fun AB ↦ AB.1.1 ×ˢ AB.2.1) ⊆ (univ : Finset V).offDiag :=
    biUnion_subset.2 fun AB hAB p hp ↦ mem_offDiag.2 ⟨mem_univ _, mem_univ _,
      (Q.disjoint AB.1.2 AB.2.2 fun h ↦
        (mem_filter.1 hAB).2 (congrArg _ (Subtype.ext h))).forall_ne_finset
        (mem_product.1 hp).1 (mem_product.1 hp).2⟩
  have htot := (div_eq_iff (Nat.cast_ne_zero.2 hoff_pos.ne')).1
    (S.sum_sq_pairColorDensity_sub_div_eq_energy_sub hQP)
  have hcard_off : (#(univ : Finset V).offDiag : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    exact_mod_cast (card_offDiag_le_sq (univ : Finset V)).trans_eq (by rw [card_univ])
  calc ∑ AB ∈ Ω, (#AB.1.1 * #AB.2.1 : ℝ) *
          ((pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1) ^ 2
      = ∑ AB ∈ Ω, ∑ p ∈ AB.1.1 ×ˢ AB.2.1,
          ((pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
            pairColorDensity S c (P.part p.1) (P.part p.2)) ^ 2 :=
        sum_congr rfl fun AB _ ↦ by
          rw [sum_congr rfl fun p hp ↦ by
            rw [Q.part_eq_of_mem AB.1.2 (mem_product.1 hp).1,
              Q.part_eq_of_mem AB.2.2 (mem_product.1 hp).2,
              part_eq_refinementParent hQP AB.1 (mem_product.1 hp).1,
              part_eq_refinementParent hQP AB.2 (mem_product.1 hp).2],
            sum_const, card_product, nsmul_eq_mul, Nat.cast_mul]
    _ ≤ ∑ p ∈ (univ : Finset V).offDiag, ∑ k,
          ((pairColorDensity S k (Q.part p.1) (Q.part p.2) : ℝ) -
            pairColorDensity S k (P.part p.1) (P.part p.2)) ^ 2 := by
        rw [← sum_biUnion hdisj_rect]
        exact (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ sq_nonneg _).trans
          (sum_le_sum fun p _ ↦ single_le_sum
            (f := fun k ↦ ((pairColorDensity S k (Q.part p.1) (Q.part p.2) : ℝ) -
              pairColorDensity S k (P.part p.1) (P.part p.2)) ^ 2)
            (fun _ _ ↦ sq_nonneg _) (mem_univ c))
    _ ≤ g * (Fintype.card V : ℝ) ^ 2 := by
        rw [htot]; exact mul_le_mul hgap hcard_off (Nat.cast_nonneg _) hg

/-- For a single color `c`, a refinement `Q ≤ P` with energy gap at most `g` has off-diagonal
block-density `L¹` deviation at most `√g * |V|²`. -/
private theorem sum_abs_pairColorDensity_sub_le_of_energy_sub_le
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {g : ℝ} (hg : 0 ≤ g)
    (hgap : S.energy Q - S.energy P ≤ g) (c : κ) :
    ∑ AB ∈ (univ : Finset (Q.parts × Q.parts)).filter
        (fun AB ↦ refinementParent hQP AB.1 ≠ refinementParent hQP AB.2),
      |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
        pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1| *
        (#AB.1.1 * #AB.2.1) ≤ √g * (Fintype.card V : ℝ) ^ 2 := by
  set Ω := (univ : Finset (Q.parts × Q.parts)).filter
    fun AB ↦ refinementParent hQP AB.1 ≠ refinementParent hQP AB.2
  rcases Ω.eq_empty_or_nonempty with hΩ | ⟨AB₀, hAB₀⟩
  · rw [hΩ, sum_empty]; positivity
  have hdisj₀ : Disjoint AB₀.1.1 AB₀.2.1 := Q.disjoint AB₀.1.2 AB₀.2.2
    fun h ↦ (mem_filter.1 hAB₀).2 (congrArg _ (Subtype.ext h))
  obtain ⟨u₀, hu₀⟩ := Q.nonempty_of_mem_parts AB₀.1.2
  obtain ⟨v₀, hv₀⟩ := Q.nonempty_of_mem_parts AB₀.2.2
  have hoff_pos : 0 < #(univ : Finset V).offDiag := card_pos.2
    ⟨(u₀, v₀), mem_offDiag.2 ⟨mem_univ _, mem_univ _, hdisj₀.forall_ne_finset hu₀ hv₀⟩⟩
  have hV2_pos : (0 : ℝ) < (Fintype.card V : ℝ) ^ 2 := by
    have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨u₀⟩
    positivity
  let d : Q.parts × Q.parts → ℝ := fun AB ↦ (pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
    pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1
  let w : Q.parts × Q.parts → ℝ := fun AB ↦ (#AB.1.1 * #AB.2.1 : ℝ) / (Fintype.card V : ℝ) ^ 2
  have hw1 : ∑ AB ∈ Ω, w AB ≤ 1 := (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
    fun _ _ _ ↦ by positivity).trans (by
      dsimp only [w]
      rw [Fintype.sum_prod_type'
        (f := fun A' B' : Q.parts ↦ (#A'.1 * #B'.1 : ℝ) / (Fintype.card V : ℝ) ^ 2)]
      simpa using Q.sum_sum_weight_le_one)
  have hsq : ∑ AB ∈ Ω, w AB * d AB ^ 2 ≤ g := by
    refine le_of_mul_le_mul_right ?_ hV2_pos
    have hlhs : (∑ AB ∈ Ω, w AB * d AB ^ 2) * (Fintype.card V : ℝ) ^ 2 =
        ∑ AB ∈ Ω, (#AB.1.1 * #AB.2.1 : ℝ) * d AB ^ 2 := by
      rw [sum_mul]; exact sum_congr rfl fun AB _ ↦ by
        dsimp [w]; rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hV2_pos.ne']
    rw [hlhs]
    exact S.sum_sq_pairColorDensity_sub_offDiag_le hQP hg hgap hoff_pos c
  have hcs := weighted_sum_abs_le_sqrt Ω w d (fun _ _ ↦ by positivity) hw1 hsq
  calc ∑ AB ∈ Ω, |d AB| * (#AB.1.1 * #AB.2.1)
      = (∑ AB ∈ Ω, w AB * |d AB|) * (Fintype.card V : ℝ) ^ 2 := by
        rw [sum_mul]; exact sum_congr rfl fun AB _ ↦ by
          dsimp [w]; rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hV2_pos.ne']; ring
    _ ≤ √g * (Fintype.card V : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hcs (by positivity)

/-- **Energy gap controls `L¹` block-density deviation.** If `Q ≤ P` has energy gap at most `g`,
the sum over all colors and all off-diagonal fine-part pairs `(A', B')` (lying in distinct coarse
cells of `P`) of `|d_c(A', B') - d_c(A, B)| * (#A' * #B')` is at most `|κ| * √g * |V|²`. -/
private theorem sum_sum_abs_pairColorDensity_sub_le_of_energy_sub_le
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {g : ℝ} (hg : 0 ≤ g)
    (hgap : S.energy Q - S.energy P ≤ g) :
    ∑ A' : Q.parts, ∑ B' : Q.parts with refinementParent hQP A' ≠ refinementParent hQP B',
      (∑ c, |(pairColorDensity S c A'.1 B'.1 : ℝ) -
        pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1|) *
        (#A'.1 * #B'.1) ≤
      Fintype.card κ * √g * (Fintype.card V : ℝ) ^ 2 := by
  set Ω := (univ : Finset (Q.parts × Q.parts)).filter
    fun AB ↦ refinementParent hQP AB.1 ≠ refinementParent hQP AB.2
  have hprod : ∑ A' : Q.parts,
      ∑ B' : Q.parts with refinementParent hQP A' ≠ refinementParent hQP B',
        (∑ c, |(pairColorDensity S c A'.1 B'.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1|) *
          (#A'.1 * #B'.1) =
      ∑ c, ∑ AB ∈ Ω,
        |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1| *
          (#AB.1.1 * #AB.2.1) := by
    simp_rw [sum_filter, ← Fintype.sum_prod_type', ← sum_filter (p := fun AB : Q.parts × Q.parts ↦
      refinementParent hQP AB.1 ≠ refinementParent hQP AB.2), sum_mul]
    exact sum_comm
  rw [hprod]
  exact (sum_le_sum (g := fun _ ↦ √g * (Fintype.card V : ℝ) ^ 2) fun c _ ↦
    S.sum_abs_pairColorDensity_sub_le_of_energy_sub_le hQP hg hgap c).trans_eq
    (by rw [sum_const, card_univ, nsmul_eq_mul, mul_assoc])

end EnergyGap

section Witness

variable {κ V : Type*} [Fintype V] [DecidableEq V] [Fintype κ] (S : PairColorSystem κ V)

/-- Iterate seeded equitable pair-color regularization `n + 1` times: either one step has energy
gap at most `g`, or the final partition has energy strictly greater than `(n + 1) * g`. -/
private theorem exists_equipartition_iterate_energy_sub_le
    (P₁ : Finpartition (univ : Finset V)) (hP₁ : P₁.IsEquipartition)
    {ε : ℝ} (hε : 0 < ε) {G : ℕ → ℝ} (hG : ∀ m, 0 < G m) {g : ℝ} (n : ℕ) :
    ∃ P Q : Finpartition (univ : Finset V), Q ≤ P ∧ P ≤ P₁ ∧
      P.IsEquipartition ∧ Q.IsEquipartition ∧ #P₁.parts ≤ #P.parts ∧
      #P.parts ≤ (strongPairColorStep (Fintype.card κ) ε G)^[n] #P₁.parts ∧
      #Q.parts ≤ (strongPairColorStep (Fintype.card κ) ε G)^[n + 1] #P₁.parts ∧
      ∑ AB ∈ S.irregularPairs (strongPairColorFineParam (Fintype.card κ) ε G #P.parts) Q,
        (#AB.1 * #AB.2 : ℝ) ≤
        strongPairColorFineParam (Fintype.card κ) ε G #P.parts * (Fintype.card V : ℝ) ^ 2 ∧
      (S.energy Q - S.energy P ≤ g ∨ (n + 1 : ℝ) * g < S.energy Q) := by
  let K := Fintype.card κ
  let step := strongPairColorStep K ε G
  have hmono : Monotone step := monotone_strongPairColorStep K ε G
  have hid : id ≤ step := le_strongPairColorStep hε hG
  have hτ (m : ℕ) : 0 < strongPairColorFineParam K ε G m := by
    have := hG m; dsimp [strongPairColorFineParam]; positivity
  induction n with
  | zero =>
    obtain ⟨Q, hQP₁, hQ, hQcard, hreg⟩ :=
      S.exists_refining_equipartition_sum_irregularPairs_le P₁ hP₁ (hτ #P₁.parts)
    have hQstep : #Q.parts ≤ step #P₁.parts := hQcard.trans
      (le_sup (f := fun j ↦ equitablePairColorRegularityBound
        (strongPairColorFineParam K ε G j) j) (mem_range.2 (Nat.lt_succ_self _)))
    refine ⟨P₁, Q, hQP₁, le_rfl, hP₁, hQ, le_rfl, le_rfl, hQstep, hreg, ?_⟩
    rcases le_or_gt (S.energy Q - S.energy P₁) g with hle | hgt
    · exact Or.inl hle
    · exact Or.inr (by have := S.energy_nonneg P₁; push_cast; linarith)
  | succ k ih =>
    obtain ⟨P, Q, hQP, hPP₁, hP, hQ, hP₁P, hPk, hQk, hreg, hgap⟩ := ih
    have hstep_k : step^[k] #P₁.parts ≤ step^[k + 1] #P₁.parts :=
      Function.monotone_iterate_of_id_le hid k.le_succ _
    have hstep_k1 : step^[k + 1] #P₁.parts ≤ step^[k + 2] #P₁.parts :=
      Function.monotone_iterate_of_id_le hid (k + 1).le_succ _
    rcases hgap with hle | hE
    · exact ⟨P, Q, hQP, hPP₁, hP, hQ, hP₁P, hPk.trans hstep_k, hQk.trans hstep_k1,
        hreg, Or.inl hle⟩
    · obtain ⟨R, hRQ, hR, hRcard, hRreg⟩ :=
        S.exists_refining_equipartition_sum_irregularPairs_le Q hQ (hτ #Q.parts)
      have hRstep : #R.parts ≤ step^[k + 2] #P₁.parts := by
        rw [Function.iterate_succ_apply' step (k + 1)]
        exact hRcard.trans ((le_sup (f := fun j ↦ equitablePairColorRegularityBound
          (strongPairColorFineParam K ε G j) j) (mem_range.2 (Nat.lt_succ_self _))).trans
          (hmono hQk))
      refine ⟨Q, R, hRQ, hQP.trans hPP₁, hQ, hR, hP₁P.trans (card_mono hQP), hQk, hRstep,
        hRreg, ?_⟩
      rcases le_or_gt (S.energy R - S.energy Q) g with hle' | hgt'
      · exact Or.inl hle'
      · exact Or.inr (by push_cast at hE ⊢; linarith)

/-- **Strong-regularity equipartition witness.** Every equipartition `P₁` has exact-refining
equipartitions `Q ≤ P ≤ P₁` bounded by `strongPairColorWitnessBound` such that `Q` is
`τ (#P.parts)`-regular up to `τ (#P.parts) |V|²` irregular pairs and
`S.energy Q - S.energy P ≤ (ε / (3 * (|κ| + 1))) ^ 2`. -/
private theorem exists_strong_regular_witness
    (P₁ : Finpartition (univ : Finset V)) (hP₁ : P₁.IsEquipartition)
    {ε : ℝ} (hε : 0 < ε) {G : ℕ → ℝ} (hG : ∀ m, 0 < G m) :
    let K := Fintype.card κ
    let M := strongPairColorWitnessBound K ε G #P₁.parts
    ∃ P Q : Finpartition (univ : Finset V), Q ≤ P ∧ P ≤ P₁ ∧
      P.IsEquipartition ∧ Q.IsEquipartition ∧ #P₁.parts ≤ #P.parts ∧
      #P.parts ≤ M ∧ #Q.parts ≤ M ∧
      ∑ AB ∈ S.irregularPairs (strongPairColorFineParam K ε G #P.parts) Q,
        (#AB.1 * #AB.2 : ℝ) ≤
        strongPairColorFineParam K ε G #P.parts * (Fintype.card V : ℝ) ^ 2 ∧
      S.energy Q - S.energy P ≤ (ε / (3 * (K + 1))) ^ 2 := by
  let K := Fintype.card κ
  let g := (ε / (3 * (K + 1))) ^ 2
  have hg : 0 < g := by positivity
  let n := ⌊1 / g⌋₊
  obtain ⟨P, Q, hQP, hPP₁, hP, hQ, hP₁P, hPn, hQn, hreg, hgap⟩ :=
    S.exists_equipartition_iterate_energy_sub_le P₁ hP₁ hε hG (g := g) n
  have hstep_le : (strongPairColorStep K ε G)^[n] #P₁.parts ≤
      strongPairColorWitnessBound K ε G #P₁.parts := by
    calc (strongPairColorStep K ε G)^[n] #P₁.parts
        ≤ (strongPairColorStep K ε G)^[n + 1] #P₁.parts :=
          Function.monotone_iterate_of_id_le (le_strongPairColorStep hε hG) n.le_succ _
      _ ≤ (strongPairColorStep K ε G)^[n + 1] (max #P₁.parts 1) :=
          (monotone_strongPairColorStep K ε G).iterate (n + 1) (le_max_left _ _)
      _ = strongPairColorWitnessBound K ε G #P₁.parts := rfl
  have hQ_le : #Q.parts ≤ strongPairColorWitnessBound K ε G #P₁.parts :=
    hQn.trans ((monotone_strongPairColorStep K ε G).iterate (n + 1) (le_max_left _ _))
  refine ⟨P, Q, hQP, hPP₁, hP, hQ, hP₁P, hPn.trans hstep_le, hQ_le, hreg,
    hgap.resolve_right fun hE ↦ ?_⟩
  have h1 : 1 < (n + 1 : ℝ) * g := (div_lt_iff₀ hg).1 (Nat.lt_floor_add_one (1 / g))
  linarith [S.energy_le_one Q]

end Witness

section OffDiagApproximation

variable {κ V : Type*} [Fintype V] [DecidableEq V] [Fintype κ] (S : PairColorSystem κ V)

open Classical in
/-- Local edit cost bound on a fine block `(A', B')` of `Q ≤ P`: coupled cost when `(A', B')` is
`τ (#P.parts)`-regular, and the full block area `#A' * #B'` otherwise. -/
private noncomputable def localOffDiagEditBound
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (ε : ℝ) (G : ℕ → ℝ)
    (A' B' : Q.parts) : ℝ :=
  if S.IsRegularPair (strongPairColorFineParam (Fintype.card κ) ε G #P.parts) A'.1 B'.1 then
    ((∑ c, |(pairColorDensity S c A'.1 B'.1 : ℝ) -
      pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1|) / 2 +
      strongPairColorCoupledParam ε G #P.parts ^ 3) * (#A'.1 * #B'.1)
  else
    #A'.1 * #B'.1

private theorem localOffDiagEditBound_symm
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (ε : ℝ) (G : ℕ → ℝ)
    (A' B' : Q.parts) :
    S.localOffDiagEditBound hQP ε G A' B' = S.localOffDiagEditBound hQP ε G B' A' := by
  have hsum : ∑ c, |(pairColorDensity S c A'.1 B'.1 : ℝ) -
      pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1| =
    ∑ c, |(pairColorDensity S c B'.1 A'.1 : ℝ) -
      pairColorDensity S c (refinementParent hQP B').1 (refinementParent hQP A').1| := by
    rw [← Equiv.sum_comp S.rev_involutive.toPerm]
    refine sum_congr rfl fun c _ ↦ ?_
    change |(pairColorDensity S (S.rev c) A'.1 B'.1 : ℝ) -
      pairColorDensity S (S.rev c) (refinementParent hQP A').1 (refinementParent hQP B').1| = _
    rw [← S.rev_rev c, pairColorDensity_swap S (S.rev (S.rev c)) B'.1 A'.1,
      pairColorDensity_swap S (S.rev (S.rev c)) (refinementParent hQP B').1
        (refinementParent hQP A').1, S.rev_rev]
  dsimp only [localOffDiagEditBound]
  rw [hsum, mul_comm (#A'.1 : ℝ) (#B'.1 : ℝ)]
  by_cases h : S.IsRegularPair (strongPairColorFineParam (Fintype.card κ) ε G #P.parts) A'.1 B'.1
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right fun h' ↦ h h'.symm]

/-- Construct the local recoloring on an off-diagonal fine pair `(A', B')`, using coupled
recoloring when `(A', B')` is regular and uncoupled recoloring otherwise. -/
private theorem exists_local_offDiag_recoloring [DecidableEq κ]
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {ε : ℝ} (hε : 0 < ε)
    {G : ℕ → ℝ} (hG : ∀ m, 0 < G m)
    (hc_size : ∀ A' : Q.parts, (Fintype.card κ : ℝ) ^ 2 * (Fintype.card κ + 2) ≤
      strongPairColorCoupledParam ε G #P.parts ^ 6 * #A'.1)
    (hu_size : ∀ A' : Q.parts, (Fintype.card κ : ℝ) + 1 ≤
      strongPairColorUncoupledParam G #P.parts ^ 6 * #A'.1)
    (A' B' : Q.parts) (hpar : refinementParent hQP A' ≠ refinementParent hQP B') :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (#{q ∈ A'.1 ×ˢ B'.1 | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        S.localOffDiagEditBound hQP ε G A' B' ∧
      ∀ c, ∀ s' ⊆ A'.1, ∀ t' ⊆ B'.1,
        |(#{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some c} : ℝ) -
          pairColorDensity S c (refinementParent hQP A').1 (refinementParent hQP B').1 *
            (#s' * #t')| ≤
          (min 1 (G #P.parts) ^ 3 / 2) * (#A'.1 * #B'.1) := by
  let A := (refinementParent hQP A').1
  let B := (refinementParent hQP B').1
  have hAB_disj : Disjoint A B := P.disjoint (refinementParent hQP A').2
    (refinementParent hQP B').2 fun h ↦ hpar (Subtype.ext h)
  have hA'B'_disj : Disjoint A'.1 B'.1 := hAB_disj.mono (le_refinementParent hQP A')
    (le_refinementParent hQP B')
  obtain ⟨u₀, hu₀⟩ := P.nonempty_of_mem_parts (refinementParent hQP A').2
  obtain ⟨v₀, hv₀⟩ := P.nonempty_of_mem_parts (refinementParent hQP B').2
  have hp0 (c : κ) : (0 : ℝ) ≤ pairColorDensity S c A B := mod_cast pairColorDensity_nonneg S c A B
  have hp1 : ∑ c, (pairColorDensity S c A B : ℝ) = 1 := by
    have h : ((∑ c, pairColorDensity S c A B : ℚ) : ℝ) = 1 := mod_cast sum_pairColorDensity S A B
      ⟨(u₀, v₀), mem_filter.2 ⟨mem_product.2 ⟨hu₀, hv₀⟩, hAB_disj.forall_ne_finset hu₀ hv₀⟩⟩
    simpa using h
  set θ := min 1 (G #P.parts)
  have hθ3 : 0 ≤ θ ^ 3 := pow_nonneg (lt_min zero_lt_one (hG #P.parts)).le 3
  by_cases hreg : S.IsRegularPair (strongPairColorFineParam (Fintype.card κ) ε G #P.parts)
      A'.1 B'.1
  · have hεc : 0 < strongPairColorCoupledParam ε G #P.parts := by
      have := hG #P.parts; dsimp [strongPairColorCoupledParam]; positivity
    obtain ⟨S', hrev, -, hedit, hrect⟩ := S.exists_coupled_recoloring_abs_card_filter_sub_le
      hA'B'_disj hreg hp0 hp1 hεc (hc_size A') (hc_size B')
    have hεc_le : strongPairColorCoupledParam ε G #P.parts ^ 3 ≤ θ ^ 3 / 8 :=
      (pow_le_pow_left₀ hεc.le (min_le_right _ _) 3).trans_eq (by ring)
    have hτ_le : (Fintype.card κ : ℝ) * strongPairColorFineParam (Fintype.card κ) ε G #P.parts ≤
        θ ^ 3 / 4 :=
      (mul_le_mul (by linarith : (Fintype.card κ : ℝ) ≤ Fintype.card κ + 1) (min_le_right _ _)
        (by have := hG #P.parts; positivity) (by positivity)).trans_eq (by field_simp; rfl)
    refine ⟨S', hrev, by dsimp only [localOffDiagEditBound]; rwa [ite_eq_left hreg],
      fun c s' hs' t' ht' ↦ (hrect c s' hs' t' ht').trans ?_⟩
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hεu : 0 < strongPairColorUncoupledParam G #P.parts := by
      have := hG #P.parts; dsimp [strongPairColorUncoupledParam]; positivity
    obtain ⟨S', hrev, -, hrect⟩ := S.exists_recoloring_abs_card_filter_sub_le
      hA'B'_disj hp0 hp1 hεu (hu_size A') (hu_size B')
    have hedit : (#{q ∈ A'.1 ×ˢ B'.1 | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        S.localOffDiagEditBound hQP ε G A' B' := by
      dsimp only [localOffDiagEditBound]; rw [ite_eq_right hreg]
      exact_mod_cast (card_filter_le _ _).trans_eq (card_product _ _)
    refine ⟨S', hrev, hedit, fun c s' hs' t' ht' ↦ (hrect c s' hs' t' ht').trans_eq ?_⟩
    dsimp [strongPairColorUncoupledParam, θ]; ring

/-- Bound the total vertex mass of off-diagonal fine pairs failing `τ`-regularity by
`(ε / 3) |V|²`. -/
private theorem sum_card_mul_card_not_isRegularPair_le
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {ε : ℝ} {G : ℕ → ℝ}
    [DecidablePred fun AB : Q.parts × Q.parts ↦
      ¬S.IsRegularPair (strongPairColorFineParam (Fintype.card κ) ε G #P.parts) AB.1.1 AB.2.1]
    (hirreg : ∑ AB ∈ S.irregularPairs (strongPairColorFineParam (Fintype.card κ) ε G #P.parts) Q,
      (#AB.1 * #AB.2 : ℝ) ≤
      strongPairColorFineParam (Fintype.card κ) ε G #P.parts * (Fintype.card V : ℝ) ^ 2) :
    (∑ AB ∈ (univ : Finset (Q.parts × Q.parts)).filter
        (fun AB ↦ refinementParent hQP AB.1 ≠ refinementParent hQP AB.2),
      if ¬S.IsRegularPair (strongPairColorFineParam (Fintype.card κ) ε G #P.parts) AB.1.1 AB.2.1
      then (#AB.1.1 * #AB.2.1 : ℝ) else 0) ≤ (ε / 3) * (Fintype.card V : ℝ) ^ 2 := by
  let τ := strongPairColorFineParam (Fintype.card κ) ε G #P.parts
  set Ω := (univ : Finset (Q.parts × Q.parts)).filter
    fun AB ↦ refinementParent hQP AB.1 ≠ refinementParent hQP AB.2
  rw [← sum_filter]
  let f : Q.parts × Q.parts → Finset V × Finset V := fun AB ↦ (AB.1.1, AB.2.1)
  have hinj : ∀ a ∈ Ω.filter (fun AB ↦ ¬S.IsRegularPair τ AB.1.1 AB.2.1),
      ∀ b ∈ Ω.filter (fun AB ↦ ¬S.IsRegularPair τ AB.1.1 AB.2.1), f a = f b → a = b :=
    fun _ _ _ _ h ↦ Prod.ext (Subtype.ext (Prod.mk.inj h).1) (Subtype.ext (Prod.mk.inj h).2)
  have hsub : (Ω.filter (fun AB ↦ ¬S.IsRegularPair τ AB.1.1 AB.2.1)).image f ⊆
      S.irregularPairs τ Q := fun _ hx ↦ by
    obtain ⟨AB, hAB, rfl⟩ := mem_image.1 hx
    exact S.mem_irregularPairs.2 ⟨AB.1.2, AB.2.2,
      fun h ↦ (mem_filter.1 (mem_filter.1 hAB).1).2 (congrArg _ (Subtype.ext h)),
      (mem_filter.1 hAB).2⟩
  calc ∑ AB ∈ Ω.filter (fun AB ↦ ¬S.IsRegularPair τ AB.1.1 AB.2.1), (#AB.1.1 * #AB.2.1 : ℝ)
      = ∑ x ∈ (Ω.filter (fun AB ↦ ¬S.IsRegularPair τ AB.1.1 AB.2.1)).image f,
          (#x.1 * #x.2 : ℝ) :=
        (sum_image (f := fun x : Finset V × Finset V ↦ (#x.1 * #x.2 : ℝ)) hinj).symm
    _ ≤ ∑ x ∈ S.irregularPairs τ Q, (#x.1 * #x.2 : ℝ) :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
    _ ≤ τ * (Fintype.card V : ℝ) ^ 2 := hirreg
    _ ≤ (ε / 3) * (Fintype.card V : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)

/-- Pointwise upper bound splitting `localOffDiagEditBound` into the coupled `L¹` term, the
coupled `εc³` term, and the indicator of irregular fine blocks. -/
private theorem localOffDiagEditBound_le_add
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {ε : ℝ} (hε : 0 < ε)
    {G : ℕ → ℝ} (hG : ∀ m, 0 < G m)
    [DecidablePred fun AB : Q.parts × Q.parts ↦
      ¬S.IsRegularPair (strongPairColorFineParam (Fintype.card κ) ε G #P.parts) AB.1.1 AB.2.1]
    (AB : Q.parts × Q.parts) :
    S.localOffDiagEditBound hQP ε G AB.1 AB.2 ≤
      ((∑ c, |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
        pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1|) *
        (#AB.1.1 * #AB.2.1)) / 2 +
      strongPairColorCoupledParam ε G #P.parts ^ 3 * (#AB.1.1 * #AB.2.1) +
      (if ¬S.IsRegularPair (strongPairColorFineParam (Fintype.card κ) ε G #P.parts) AB.1.1 AB.2.1
        then (#AB.1.1 * #AB.2.1 : ℝ) else 0) := by
  dsimp only [localOffDiagEditBound]
  by_cases h : S.IsRegularPair (strongPairColorFineParam (Fintype.card κ) ε G #P.parts)
      AB.1.1 AB.2.1
  · rw [ite_eq_left h, ite_eq_right (not_not.2 h)]; linarith
  · rw [ite_eq_right h, ite_eq_left h]
    have : 0 ≤ strongPairColorCoupledParam ε G #P.parts := by
      have := hG #P.parts; dsimp [strongPairColorCoupledParam]; positivity
    have : 0 ≤ ((∑ c, |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
        pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1|) *
        (#AB.1.1 * #AB.2.1)) / 2 +
        strongPairColorCoupledParam ε G #P.parts ^ 3 * (#AB.1.1 * #AB.2.1) := by positivity
    linarith

/-- Sum the local edit bounds across all off-diagonal fine pairs: the energy-gap `L¹` term, the
coupled additive error, and the irregular fine pairs together total at most `ε * |V|²`. -/
private theorem sum_localOffDiagEditBound_le
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {ε : ℝ} (hε : 0 < ε)
    {G : ℕ → ℝ} (hG : ∀ m, 0 < G m)
    (hirreg : ∑ AB ∈ S.irregularPairs (strongPairColorFineParam (Fintype.card κ) ε G #P.parts) Q,
      (#AB.1 * #AB.2 : ℝ) ≤
      strongPairColorFineParam (Fintype.card κ) ε G #P.parts * (Fintype.card V : ℝ) ^ 2)
    (hgap : S.energy Q - S.energy P ≤ (ε / (3 * (Fintype.card κ + 1))) ^ 2) :
    ∑ A' : Q.parts, ∑ B' : Q.parts with refinementParent hQP A' ≠ refinementParent hQP B',
      S.localOffDiagEditBound hQP ε G A' B' ≤ ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  let K := Fintype.card κ
  let εc := strongPairColorCoupledParam ε G #P.parts
  have hεc0 : 0 ≤ εc := by have := hG #P.parts; dsimp [εc, strongPairColorCoupledParam]; positivity
  set Ω := (univ : Finset (Q.parts × Q.parts)).filter
    fun AB ↦ refinementParent hQP AB.1 ≠ refinementParent hQP AB.2
  have hS1 : (∑ AB ∈ Ω, ((∑ c, |(pairColorDensity S c AB.1.1 AB.2.1 : ℝ) -
        pairColorDensity S c (refinementParent hQP AB.1).1 (refinementParent hQP AB.2).1|) *
        (#AB.1.1 * #AB.2.1)) / 2) ≤ (ε / 6) * (Fintype.card V : ℝ) ^ 2 := by
    rw [← sum_div]
    have hL1 := S.sum_sum_abs_pairColorDensity_sub_le_of_energy_sub_le hQP (by positivity) hgap
    simp_rw [sum_filter, ← Fintype.sum_prod_type', ← sum_filter (p := fun AB : Q.parts × Q.parts ↦
      refinementParent hQP AB.1 ≠ refinementParent hQP AB.2)] at hL1
    rw [Real.sqrt_sq (by positivity : 0 ≤ ε / (3 * (K + 1)))] at hL1
    have hK : (K : ℝ) * (ε / (3 * (K + 1))) ≤ ε / 3 :=
      (mul_le_mul_of_nonneg_right (by linarith : (K : ℝ) ≤ K + 1)
        (by positivity)).trans_eq (by field_simp)
    nlinarith [mul_le_mul_of_nonneg_right hK (sq_nonneg (Fintype.card V : ℝ))]
  have hS2 : ∑ AB ∈ Ω, εc ^ 3 * (#AB.1.1 * #AB.2.1) ≤ (ε / 6) * (Fintype.card V : ℝ) ^ 2 := by
    have hεc3 : εc ^ 3 ≤ ε / 6 := (pow_le_of_le_one hεc0
      ((min_le_left _ _).trans (min_le_left _ _)) (by omega)).trans
      ((min_le_left _ _).trans (min_le_right _ _))
    calc ∑ AB ∈ Ω, εc ^ 3 * (#AB.1.1 * #AB.2.1)
        ≤ ∑ AB : Q.parts × Q.parts, εc ^ 3 * (#AB.1.1 * #AB.2.1) :=
          sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun _ _ _ ↦ by positivity
      _ = εc ^ 3 * (Fintype.card V : ℝ) ^ 2 := by
          rw [← mul_sum, Fintype.sum_prod_type' (f := fun A' B' : Q.parts ↦ (#A'.1 : ℝ) * #B'.1),
            ← sum_mul_sum, Q.sum_card_subtype, card_univ, ← sq]
      _ ≤ (ε / 6) * (Fintype.card V : ℝ) ^ 2 := mul_le_mul_of_nonneg_right hεc3 (by positivity)
  have hS3 := S.sum_card_mul_card_not_isRegularPair_le hQP hirreg
  have hrewrite : ∑ A' : Q.parts,
      ∑ B' : Q.parts with refinementParent hQP A' ≠ refinementParent hQP B',
        S.localOffDiagEditBound hQP ε G A' B' =
      ∑ AB ∈ Ω, S.localOffDiagEditBound hQP ε G AB.1 AB.2 := by
    simp_rw [Ω, sum_filter, ← Fintype.sum_prod_type']
  rw [hrewrite]
  have hsum := sum_le_sum fun AB (_ : AB ∈ Ω) ↦ S.localOffDiagEditBound_le_add hQP hε hG AB
  simp only [sum_add_distrib] at hsum
  nlinarith [sq_nonneg (Fintype.card V : ℝ)]

/-- Deduce the fine-cell concentration thresholds and coarse-cell diagonal threshold from
`strongPairColorOffDiagBound ≤ |V|`. -/
private theorem cell_size_bounds_of_offDiagBound_le
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (hQ : Q.IsEquipartition)
    {K m₀ : ℕ} {ε : ℝ} (hε : 0 < ε) {G : ℕ → ℝ} (hG : ∀ m, 0 < G m)
    (hQ_pos : 0 < #Q.parts)
    (hPM : #P.parts ≤ strongPairColorWitnessBound K ε G m₀)
    (hQM : #Q.parts ≤ strongPairColorWitnessBound K ε G m₀)
    (hV : strongPairColorOffDiagBound K ε G m₀ ≤ Fintype.card V) :
    (∀ A' : Q.parts, (K : ℝ) ^ 2 * (K + 2) ≤
      strongPairColorCoupledParam ε G #P.parts ^ 6 * #A'.1) ∧
    (∀ A' : Q.parts, (K : ℝ) + 1 ≤
      strongPairColorUncoupledParam G #P.parts ^ 6 * #A'.1) ∧
    (∀ A ∈ P.parts, 1 < G #P.parts * #A) := by
  let M := strongPairColorWitnessBound K ε G m₀
  let C := (range (M + 1)).sup (fun j ↦
    max ⌈(K : ℝ) ^ 2 * (K + 2) / min (min 1 (ε / 6)) (min 1 (G j) / 2) ^ 6⌉₊
      ⌈((K : ℝ) + 1) / (min 1 (G j) ^ 3 / 6) ^ 6⌉₊) + 1
  have hC_card (A' : Q.parts) : C ≤ #A'.1 := by
    have hMC : C * #Q.parts ≤ #(univ : Finset V) := by
      rw [card_univ]
      calc C * #Q.parts ≤ C * M := Nat.mul_le_mul_left C hQM
        _ = strongPairColorOffDiagBound K ε G m₀ := mul_comm C M
        _ ≤ Fintype.card V := hV
    exact ((Nat.le_div_iff_mul_le hQ_pos).2 hMC).trans
      (IsEquipartition.average_le_card_part hQ A'.2)
  have hsup : max ⌈(K : ℝ) ^ 2 * (K + 2) / strongPairColorCoupledParam ε G #P.parts ^ 6⌉₊
      ⌈((K : ℝ) + 1) / strongPairColorUncoupledParam G #P.parts ^ 6⌉₊ ≤ C :=
    (le_sup (f := fun j ↦
      max ⌈(K : ℝ) ^ 2 * (K + 2) / min (min 1 (ε / 6)) (min 1 (G j) / 2) ^ 6⌉₊
        ⌈((K : ℝ) + 1) / (min 1 (G j) ^ 3 / 6) ^ 6⌉₊)
      (mem_range.2 (Nat.lt_succ_of_le hPM))).trans (Nat.le_succ _)
  have hc (A' : Q.parts) : (K : ℝ) ^ 2 * (K + 2) ≤
      strongPairColorCoupledParam ε G #P.parts ^ 6 * #A'.1 := by
    have hpos : 0 < strongPairColorCoupledParam ε G #P.parts ^ 6 := by
      have := hG #P.parts; dsimp [strongPairColorCoupledParam]; positivity
    exact (div_le_iff₀' hpos).1 ((Nat.le_ceil _).trans
      (Nat.cast_le.2 ((le_max_left _ _).trans (hsup.trans (hC_card A')))))
  have hu (A' : Q.parts) : (K : ℝ) + 1 ≤
      strongPairColorUncoupledParam G #P.parts ^ 6 * #A'.1 := by
    have hpos : 0 < strongPairColorUncoupledParam G #P.parts ^ 6 := by
      have := hG #P.parts; dsimp [strongPairColorUncoupledParam]; positivity
    exact (div_le_iff₀' hpos).1 ((Nat.le_ceil _).trans
      (Nat.cast_le.2 ((le_max_right _ _).trans (hsup.trans (hC_card A')))))
  refine ⟨hc, hu, fun A hA ↦ ?_⟩
  obtain ⟨A', hA', hA'A⟩ := exists_le_of_le hQP hA
  have hA_pos : (0 : ℝ) < #A := Nat.cast_pos.2 (P.nonempty_of_mem_parts hA).card_pos
  have hθ0 : 0 < min 1 (G #P.parts) := lt_min zero_lt_one (hG #P.parts)
  have hlt : strongPairColorUncoupledParam G #P.parts ^ 6 < G #P.parts := by
    calc strongPairColorUncoupledParam G #P.parts ^ 6
        = min 1 (G #P.parts) ^ 18 / 6 ^ 6 := by dsimp [strongPairColorUncoupledParam]; ring
      _ < min 1 (G #P.parts) ^ 18 := div_lt_self (by positivity) (by norm_num)
      _ ≤ min 1 (G #P.parts) := pow_le_of_le_one hθ0.le (min_le_left _ _) (by omega)
      _ ≤ G #P.parts := min_le_right _ _
  have hle : 1 ≤ strongPairColorUncoupledParam G #P.parts ^ 6 * #A :=
    calc (1 : ℝ) ≤ (K : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) K]
      _ ≤ strongPairColorUncoupledParam G #P.parts ^ 6 * #A' := hu ⟨A', hA'⟩
      _ ≤ strongPairColorUncoupledParam G #P.parts ^ 6 * #A :=
          mul_le_mul_of_nonneg_left (Nat.cast_le.2 (card_le_card hA'A)) (by positivity)
  exact hle.trans_lt (mul_lt_mul_of_pos_right hlt hA_pos)

open Classical in
/-- **Off-diagonal strong regular approximation for pair-color systems.** Given a seed
equipartition `P₀`, accuracy `ε > 0`, positive schedule `G : ℕ → ℝ`, and target minimum part count
`t₀`, once `|V| ≥ strongPairColorOffDiagBound |κ| ε G (max t₀ 1 * #P₀.parts)`, there exist an
exact-refining equipartition `P ≤ P₀` with `t₀ ≤ #P.parts` and a recolored pair-color system `T`
on `κ` preserving `S.rev` and within-cell colors, editing at most `ε |V|²` ordered pairs, and
making every pair `(A, B)` of distinct parts of `P` `G (#P.parts)`-regular. -/
theorem exists_strong_regular_approximation_offDiag
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {ε : ℝ} (hε : 0 < ε)
    {G : ℕ → ℝ} (hG : ∀ m, 0 < G m) {t₀ : ℕ}
    (hV : strongPairColorOffDiagBound (Fintype.card κ) ε G (max t₀ 1 * #P₀.parts) ≤
      Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem κ V),
      P ≤ P₀ ∧ P.IsEquipartition ∧ t₀ ≤ #P.parts ∧
      #P.parts ≤ strongPairColorWitnessBound (Fintype.card κ) ε G (max t₀ 1 * #P₀.parts) ∧
      T.rev = S.rev ∧
      (∀ u v, P.part u = P.part v → T.colorOfPair u v = S.colorOfPair u v) ∧
      (∀ A ∈ P.parts, 1 < G #P.parts * #A) ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → T.IsRegularPair (G #P.parts) A B) ∧
      (#{q : V × V | T.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        ε * (Fintype.card V : ℝ) ^ 2 := by
  classical
  let K := Fintype.card κ
  let m₀ := max t₀ 1 * #P₀.parts
  have hM_ge : max m₀ 1 ≤ strongPairColorWitnessBound K ε G m₀ :=
    Function.monotone_iterate_of_id_le (le_strongPairColorStep hε hG) (Nat.zero_le _) _
  have hm₀_le_V : max m₀ 1 ≤ Fintype.card V :=
    (hM_ge.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))).trans hV
  have : Nonempty V := Fintype.card_pos_iff.1 ((le_max_right m₀ 1).trans hm₀_le_V)
  have hP₀_pos : 0 < #P₀.parts := (P₀.parts_nonempty univ_nonempty.ne_empty).card_pos
  obtain ⟨P₁, hP₁, hP₁_card, hP₁P₀, -⟩ :=
    IsEquipartition.exists_refining_equipartition_card_eq_mul hP₀ P₀ le_rfl
      (by positivity : max t₀ 1 ≠ 0) (by rw [card_univ]; exact (le_max_left m₀ 1).trans hm₀_le_V)
  obtain ⟨P, Q, hQP, hPP₁, hP, hQ, hP₁P, hPM, hQM, hirreg, hgap⟩ :=
    S.exists_strong_regular_witness P₁ hP₁ hε hG
  rw [hP₁_card] at hP₁P hPM hQM
  have hQ_pos : 0 < #Q.parts :=
    (Nat.mul_pos (by positivity) hP₀_pos).trans_le (hP₁P.trans (card_mono hQP))
  obtain ⟨hc_size, hu_size, hsize⟩ :=
    cell_size_bounds_of_offDiagBound_le hQP hQ hε hG hQ_pos hPM hQM hV
  obtain ⟨T, hrev, hdiag_eq, hedit_le, hrect⟩ := S.exists_offDiag_recoloring_of_refines hQP
    (p := fun A B c ↦ (pairColorDensity S c A B : ℝ))
    (fun A B c ↦ by rw [← S.rev_rev c, pairColorDensity_swap S (S.rev c) A B, S.rev_rev])
    (S.localOffDiagEditBound_symm hQP ε G)
    (S.exists_local_offDiag_recoloring hQP hε hG hc_size hu_size)
  refine ⟨P, T, hPP₁.trans hP₁P₀, hP,
    (le_max_left t₀ 1).trans ((Nat.le_mul_of_pos_right _ hP₀_pos).trans hP₁P), hPM, hrev,
    hdiag_eq, hsize, fun A hA B hB hAB ↦ ?_, ?_⟩
  · exact (T.isRegularPair_of_abs_card_filter_colorOfPair_sub_le (P.disjoint hA hB hAB)
      (P.nonempty_of_mem_parts hA) (P.nonempty_of_mem_parts hB) (hG #P.parts) (by linarith)
      (hrect A hA B hB hAB)).1
  · exact hedit_le.trans (S.sum_localOffDiagEditBound_le hQP hε hG hirreg hgap)

open Classical in
/-- **Strong regular approximation for pair-color systems (seeded).** Given an equipartition `P₀`
of `V`, an edit budget `ε > 0`, an arbitrary positive regularity schedule `F : ℕ → ℝ`, and a
target minimum part count `t₀`, once
`strongPairColorApproximationBound |κ| ε F t₀ #P₀.parts ≤ |V|`, there exist an exact-refining
equipartition `P ≤ P₀` with `t₀ ≤ #P.parts` and a pair-color system `T` over `Option κ` whose
lower skeleton `⟨P, T⟩` satisfies `PairSkeleton3.LowerSkeletonRegular F` and edits `S` on at most
`ε |V|²` ordered pairs of vertices. -/
theorem exists_strong_regular_approximation
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {ε : ℝ} (hε : 0 < ε)
    {F : ℕ → ℝ} (hF : ∀ m, 0 < F m) {t₀ : ℕ}
    (hV : strongPairColorApproximationBound (Fintype.card κ) ε F t₀ #P₀.parts ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem (Option κ) V),
      P ≤ P₀ ∧ P.IsEquipartition ∧ t₀ ≤ #P.parts ∧
      #P.parts ≤ strongPairColorWitnessBound (Fintype.card κ) (ε / 2)
        (fun m ↦ F (m + Fintype.card κ + 1)) (max (max t₀ ⌈2 / ε⌉₊) 1 * #P₀.parts) ∧
      T.rev = Option.map S.rev ∧
      (⟨P, T⟩ : PairSkeleton3 (Option κ) V).LowerSkeletonRegular F ∧
      (#{q : V × V | T.colorOfPair q.1 q.2 ≠ (S.colorOfPair q.1 q.2).map some} : ℝ) ≤
        ε * (Fintype.card V : ℝ) ^ 2 := by
  obtain ⟨P, T₀, hPP₀, hP, ht₀, hPM, hrev, -, hsize, hreg, hedit₀⟩ :=
    S.exists_strong_regular_approximation_offDiag P₀ hP₀ (half_pos hε) (fun m ↦ hF _) hV
  let T := T₀.fillDiagonal P
  have hreg_full : (⟨P, T⟩ : PairSkeleton3 (Option κ) V).LowerSkeletonRegular F := by
    rw [PairSkeleton3.lowerSkeletonRegular_iff]
    dsimp only
    rw [Fintype.card_option, ← add_assoc]
    exact T₀.isPairColorRegular_fillDiagonal P hsize hreg
  have hdiag_le : (#{q : V × V | T.colorOfPair q.1 q.2 ≠ (T₀.colorOfPair q.1 q.2).map some} : ℝ) ≤
      (ε / 2) * (Fintype.card V : ℝ) ^ 2 := by
    have hceil : (2 / ε : ℝ) ≤ #P.parts :=
      (Nat.le_ceil _).trans (Nat.cast_le.2 ((le_max_right t₀ _).trans ht₀))
    have hP_pos : (0 : ℝ) < #P.parts := (by positivity : 0 < 2 / ε).trans_le hceil
    have hmul : 2 ≤ ε * #P.parts := (div_le_iff₀' hε).1 hceil
    have hnat : (#{q : V × V | T.colorOfPair q.1 q.2 ≠ (T₀.colorOfPair q.1 q.2).map some} : ℝ) ≤
        (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) / #P.parts) := by
      rw [T₀.card_fillDiagonal_colorOfPair_ne P]
      refine (Nat.cast_le.2 (IsEquipartition.sum_card_mul_sub_one_le hP)).trans ?_
      rw [Nat.cast_mul, card_univ]
      exact mul_le_mul_of_nonneg_left Nat.cast_div_le (by positivity)
    refine hnat.trans ?_
    rw [mul_div_assoc', ← sq, div_le_iff₀ hP_pos]
    nlinarith [sq_nonneg (Fintype.card V : ℝ)]
  have htri : #{q : V × V | T.colorOfPair q.1 q.2 ≠ (S.colorOfPair q.1 q.2).map some} ≤
      #{q : V × V | T.colorOfPair q.1 q.2 ≠ (T₀.colorOfPair q.1 q.2).map some} +
        #{q : V × V | T₀.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} := by
    refine (card_le_card fun q hq ↦ ?_).trans (card_union_le _ _)
    rw [mem_union, mem_filter, mem_filter]
    by_cases h1 : T₀.colorOfPair q.1 q.2 = S.colorOfPair q.1 q.2
    · exact Or.inl ⟨mem_univ _, h1 ▸ (mem_filter.1 hq).2⟩
    · exact Or.inr ⟨mem_univ _, h1⟩
  refine ⟨P, T, hPP₀, hP, (le_max_left t₀ _).trans ht₀, hPM, funext fun c ↦ by simp [T, hrev],
    hreg_full, ?_⟩
  have htriR : (#{q : V × V | T.colorOfPair q.1 q.2 ≠ (S.colorOfPair q.1 q.2).map some} : ℝ) ≤
      (#{q : V × V | T.colorOfPair q.1 q.2 ≠ (T₀.colorOfPair q.1 q.2).map some} : ℝ) +
        (#{q : V × V | T₀.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) := by
    exact_mod_cast htri
  linarith

open Classical in
/-- **Strong regular approximation for pair-color systems (unseeded).** Specializing
`exists_strong_regular_approximation` to the trivial equipartition `⊤` produces an equipartition
`P` with `t₀ ≤ #P.parts` and a recolored pair-color system `T` over `Option κ` whose lower skeleton
`⟨P, T⟩` satisfies `PairSkeleton3.LowerSkeletonRegular F` within `ε |V|²` ordered-pair edits. -/
theorem exists_strong_regular_approximation_univ {ε : ℝ} (hε : 0 < ε)
    {F : ℕ → ℝ} (hF : ∀ m, 0 < F m) {t₀ : ℕ}
    (hV : strongPairColorApproximationBound (Fintype.card κ) ε F t₀ 1 ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem (Option κ) V),
      P.IsEquipartition ∧ t₀ ≤ #P.parts ∧
      #P.parts ≤ strongPairColorWitnessBound (Fintype.card κ) (ε / 2)
        (fun m ↦ F (m + Fintype.card κ + 1)) (max (max t₀ ⌈2 / ε⌉₊) 1) ∧
      T.rev = Option.map S.rev ∧
      (⟨P, T⟩ : PairSkeleton3 (Option κ) V).LowerSkeletonRegular F ∧
      (#{q : V × V | T.colorOfPair q.1 q.2 ≠ (S.colorOfPair q.1 q.2).map some} : ℝ) ≤
        ε * (Fintype.card V : ℝ) ^ 2 := by
  have h1 : 1 ≤ strongPairColorApproximationBound (Fintype.card κ) ε F t₀ 1 := by
    have hM : 1 ≤ strongPairColorWitnessBound (Fintype.card κ) (ε / 2)
        (fun m ↦ F (m + Fintype.card κ + 1)) (max (max t₀ ⌈2 / ε⌉₊) 1 * 1) :=
      (le_max_right _ 1).trans (Function.monotone_iterate_of_id_le
        (le_strongPairColorStep (half_pos hε) fun m ↦ hF _) (Nat.zero_le _) _)
    exact hM.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
  have : Nonempty V := Fintype.card_pos_iff.1 (h1.trans hV)
  have htop : #(⊤ : Finpartition (univ : Finset V)).parts = 1 := by
    rw [parts_top univ_nonempty.ne_empty, card_singleton]
  obtain ⟨P, T, -, hP, ht₀, hPM, hrev, hreg, hedit⟩ :=
    S.exists_strong_regular_approximation ⊤ (top_isEquipartition _) hε hF (htop.symm ▸ hV)
  rw [htop, mul_one] at hPM
  exact ⟨P, T, hP, ht₀, hPM, hrev, hreg, hedit⟩

end OffDiagApproximation

end PairColorSystem

end TauCeti
