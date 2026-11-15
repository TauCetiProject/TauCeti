/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import TauCeti.Combinatorics.Hypergraph.PairColor.Diagonal
public import TauCeti.Combinatorics.Hypergraph.PairColor.SeededRegularization
import Mathlib.Data.Rat.BigOperators
import TauCeti.Algebra.BigOperators.Finset.WeightedCauchySchwarz
import TauCeti.Combinatorics.Enumerative.CoupledRecoloring

/-!
# Strong regular approximation of pair-color systems

Let `S` be a pair-color system on a finite vertex set `V` with palette `κ`, let `P₀` be an
equitable vertex partition, let `δ > 0` be an edit budget, and let `G : ℕ → ℝ` be a positive
regularity schedule. Regularizing `S` once below `P₀` and cleaning up irregular pairs at tolerance
`G #P.parts` can fail when `G` decays faster than the growth of `#P.parts`, because the irregular
mass at scale `G #P.parts` need not be small.

This file resolves the schedule dependence by combining an energy-gap stopping argument with
coupled recoloring:

1. Iterating `PairColorSystem.exists_refining_equipartition_sum_irregularPairs_le` produces
   equipartitions `Q ≤ P ≤ P₀` of bounded size such that `S.energy Q - S.energy P` is at most a
   prescribed gap `γ`, while `Q` is quasi-regular at a fine scale `ξ #P.parts` calibrated to
   `G #P.parts` and `#P.parts`.
2. On each canonical coarse cell pair `A < B` of `P` and each fine subblock `U ×ˢ W` of `Q` inside
   `A ×ˢ B`, `TauCeti.exists_coupled_recoloring_abs_card_filter_sub_le` recolors `U ×ˢ W` toward the
   coarse block densities of `S` on `A ×ˢ B`, and reverses colors on `B ×ˢ A`.
3. By Cauchy–Schwarz (`PairColorSystem.sum_abs_pairColorDensity_sub_le`), the energy gap bounds the
   total-variation density shifts summed over all fine subblocks by `card κ * √γ * |V|²`, so few
   off-diagonal pairs change color. Simultaneously, fine regularity on `Q` makes every coarse pair
   `(A, B)` `(G #P.parts)`-regular without exceptional coarse pairs.
4. Filling the diagonal blocks via `PairColorSystem.fillDiagonal` adds one reversal-fixed color and
   yields an everywhere `(G #P.parts)`-regular lower skeleton editing at most `δ * |V|²` ordered
   distinct pairs.

## Main definitions

* `TauCeti.strongPairColorStepBound`: one-round part bound for strong pair-color regularity.
* `TauCeti.strongPairColorPartBound`: upper bound on the coarse part count `#P.parts`.
* `TauCeti.strongPairColorHostBound`: host-size threshold ensuring large fine cells and small
  diagonal edits.

## Main results

* `TauCeti.PairColorSystem.sum_abs_pairColorDensity_sub_le`: an energy gap `γ` across `Q ≤ P`
  bounds the `L¹` block-density deviation of each color by `√γ * |V|²`.
* `TauCeti.PairColorSystem.exists_strong_recoloring_isPairColorRegular`: refines `P₀` to an
  equipartition `P` of bounded size and recolors at most `δ * |V|²` pairs to make `(P, T)`
  `(G #P.parts)`-regular.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Lemma 4.2.
* N. Alon, E. Fischer, M. Krivelevich and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000).
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006).
-/

public section

open Finset Finpartition Real

namespace TauCeti

section Bounds

/-- Quarter-tolerance capped at `1 / 4`, used to achieve `G k`-regularity after doubling twice. -/
private noncomputable def pairQuarterTol (G : ℕ → ℝ) (k : ℕ) : ℝ :=
  min (1 / 4) (G k / 4)

/-- Energy-gap threshold for strong pair-color approximation with palette size `q₂` and edit budget
`δ`. -/
private noncomputable def pairEnergyGap (q₂ : ℕ) (δ : ℝ) : ℝ :=
  (min δ 1 / (8 * (q₂ + 1))) ^ 2

/-- Fine regularity scale at coarse part count `k`. It pays both for the sampling slack in the edit
bound and for converting global fine irregular mass `ξ * |V|²` into local coarse-pair regularity
across `k` equitable cells. -/
private noncomputable def pairFineScale (q₂ : ℕ) (δ : ℝ) (G : ℕ → ℝ) (k : ℕ) : ℝ :=
  min (min δ 1 / (8 * (q₂ + 1)))
    (pairQuarterTol G k ^ 3 / (16 * (q₂ + 1) * ((k : ℝ) + 1) ^ 2))

private theorem pairQuarterTol_pos {G : ℕ → ℝ} (hG : ∀ k, 0 < G k) (k : ℕ) :
    0 < pairQuarterTol G k :=
  lt_min (by norm_num) (by linarith [hG k])

private theorem pairQuarterTol_le_quarter (G : ℕ → ℝ) (k : ℕ) :
    pairQuarterTol G k ≤ 1 / 4 :=
  min_le_left _ _

private theorem four_mul_pairQuarterTol_le (G : ℕ → ℝ) (k : ℕ) :
    4 * pairQuarterTol G k ≤ G k := by
  have h := min_le_right (1 / 4) (G k / 4)
  dsimp [pairQuarterTol]
  linarith

private theorem pairEnergyGap_pos (q₂ : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 < pairEnergyGap q₂ δ := by
  have : 0 < min δ 1 := lt_min hδ zero_lt_one
  unfold pairEnergyGap
  positivity

private theorem pairFineScale_pos (q₂ : ℕ) {δ : ℝ} (hδ : 0 < δ) {G : ℕ → ℝ}
    (hG : ∀ k, 0 < G k) (k : ℕ) :
    0 < pairFineScale q₂ δ G k := by
  have : 0 < min δ 1 := lt_min hδ zero_lt_one
  have : 0 < pairQuarterTol G k := pairQuarterTol_pos hG k
  unfold pairFineScale
  exact lt_min (by positivity) (by positivity)

/-- One-round part bound for strong pair-color regularity, maximized over `j ≤ k` so that it is
monotone in `k` for every schedule `G`. -/
noncomputable def strongPairColorStepBound (q₂ : ℕ) (δ : ℝ) (G : ℕ → ℝ) (k : ℕ) : ℕ :=
  (range (k + 1)).sup fun j ↦ equitablePairColorRegularityBound (pairFineScale q₂ δ G j) j

/-- `strongPairColorStepBound` is monotone in the starting part count. -/
theorem strongPairColorStepBound_mono (q₂ : ℕ) (δ : ℝ) (G : ℕ → ℝ) :
    Monotone (strongPairColorStepBound q₂ δ G) :=
  fun _ _ hab ↦ sup_mono (range_mono (Nat.add_le_add_right hab 1))

private theorem equitablePairColorRegularityBound_le_step {q₂ j k : ℕ} {δ : ℝ} {G : ℕ → ℝ}
    (hjk : j ≤ k) :
    equitablePairColorRegularityBound (pairFineScale q₂ δ G j) j ≤
      strongPairColorStepBound q₂ δ G k :=
  le_sup (f := fun j ↦ equitablePairColorRegularityBound (pairFineScale q₂ δ G j) j)
    (mem_range.2 (Nat.lt_succ_of_le hjk))

/-- One round of strong pair-color regularity never decreases the number of parts when `0 < δ` and
`G` is positive. -/
theorem le_strongPairColorStepBound (q₂ : ℕ) {δ : ℝ} (hδ : 0 < δ) {G : ℕ → ℝ}
    (hG : ∀ k, 0 < G k) (k : ℕ) :
    k ≤ strongPairColorStepBound q₂ δ G k := by
  have hξ : 0 < pairFineScale q₂ δ G k := pairFineScale_pos q₂ hδ hG k
  have hk : k ≤ equitablePairColorRegularityBound (pairFineScale q₂ δ G k) k := by
    rw [equitablePairColorRegularityBound_def]
    exact (le_max_left k 1).trans
      (Function.id_le_iterate_of_id_le (le_ceil_mul_mul_four_pow_sq hξ) _ _)
  exact hk.trans (equitablePairColorRegularityBound_le_step le_rfl)

/-- Upper bound on the number of coarse parts `#P.parts` produced by strong pair-color
regularization from `l₀` initial parts. -/
noncomputable def strongPairColorPartBound (q₂ : ℕ) (δ : ℝ) (G : ℕ → ℝ) (l₀ : ℕ) : ℕ :=
  (strongPairColorStepBound q₂ δ G)^[⌊1 / pairEnergyGap q₂ δ⌋₊] l₀

/-- `strongPairColorPartBound` is monotone in `l₀`. -/
theorem strongPairColorPartBound_mono (q₂ : ℕ) (δ : ℝ) (G : ℕ → ℝ) :
    Monotone (strongPairColorPartBound q₂ δ G) :=
  (strongPairColorStepBound_mono q₂ δ G).iterate _

/-- `strongPairColorPartBound` is at least `l₀` when `0 < δ` and `G` is positive. -/
theorem le_strongPairColorPartBound (q₂ : ℕ) {δ : ℝ} (hδ : 0 < δ) {G : ℕ → ℝ}
    (hG : ∀ k, 0 < G k) (l₀ : ℕ) :
    l₀ ≤ strongPairColorPartBound q₂ δ G l₀ :=
  Function.id_le_iterate_of_id_le (le_strongPairColorStepBound q₂ hδ hG) _ l₀

/-- Host-size threshold for strong pair-color regular approximation from `l₀` initial parts. -/
noncomputable def strongPairColorHostBound (q₂ : ℕ) (δ : ℝ) (G : ℕ → ℝ) (l₀ : ℕ) : ℕ :=
  let B := strongPairColorPartBound q₂ δ G l₀
  let M := strongPairColorStepBound q₂ δ G B
  let K := (range (B + 1)).sup
    (fun k ↦ ⌈(q₂ + 3 : ℝ) / (pairFineScale q₂ δ G k / (q₂ + 1)) ^ 2⌉₊ + 1)
  max (max 2 ⌈8 / δ⌉₊) (K * max M 1)

/-- `strongPairColorHostBound` is monotone in `l₀`. -/
theorem strongPairColorHostBound_mono (q₂ : ℕ) (δ : ℝ) (G : ℕ → ℝ) :
    Monotone (strongPairColorHostBound q₂ δ G) := by
  intro a b hab
  dsimp [strongPairColorHostBound]
  have hB : strongPairColorPartBound q₂ δ G a ≤ strongPairColorPartBound q₂ δ G b :=
    strongPairColorPartBound_mono q₂ δ G hab
  have hM : strongPairColorStepBound q₂ δ G (strongPairColorPartBound q₂ δ G a) ≤
      strongPairColorStepBound q₂ δ G (strongPairColorPartBound q₂ δ G b) :=
    strongPairColorStepBound_mono q₂ δ G hB
  have hK : (range (strongPairColorPartBound q₂ δ G a + 1)).sup
        (fun k ↦ ⌈(q₂ + 3 : ℝ) / (pairFineScale q₂ δ G k / (q₂ + 1)) ^ 2⌉₊ + 1) ≤
      (range (strongPairColorPartBound q₂ δ G b + 1)).sup
        (fun k ↦ ⌈(q₂ + 3 : ℝ) / (pairFineScale q₂ δ G k / (q₂ + 1)) ^ 2⌉₊ + 1) :=
    sup_mono (range_mono (Nat.add_le_add_right hB 1))
  exact max_le_max le_rfl (Nat.mul_le_mul hK (max_le_max hM le_rfl))

private theorem union_bound_powerset_product {V : Type*} {q₂ : ℕ} {ξ₀ : ℝ} {u w : Finset V}
    (hu : (q₂ + 3 : ℝ) ≤ ξ₀ ^ 2 * #u) (hw : (q₂ + 3 : ℝ) ≤ ξ₀ ^ 2 * #w) :
    2 * (Fintype.card ↥(u.powerset ×ˢ w.powerset) + 1) * q₂ *
      exp (-2 * (ξ₀ * (#u * #w : ℕ)) ^ 2 / #(u ×ˢ w)) < 1 := by
  classical
  rcases Nat.eq_zero_or_pos q₂ with rfl | hq₂pos
  · simp
  have hu_pos : (0 : ℝ) < #u := by
    by_contra! hle
    have : ξ₀ ^ 2 * #u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle
    linarith [Nat.cast_nonneg (α := ℝ) q₂]
  have hw_pos : (0 : ℝ) < #w := by
    by_contra! hle
    have : ξ₀ ^ 2 * #w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hle
    linarith [Nat.cast_nonneg (α := ℝ) q₂]
  have hw1 : (1 : ℝ) ≤ #w := Nat.one_le_cast.2 (Nat.cast_pos.1 hw_pos)
  have hcard : Fintype.card ↥(u.powerset ×ˢ w.powerset) = 2 ^ #u * 2 ^ #w := by
    rw [Fintype.card_coe, card_product, card_powerset, card_powerset]
  have h2 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have hpow (k : ℕ) : (2 : ℝ) ^ k ≤ exp k :=
    calc (2 : ℝ) ^ k ≤ exp 1 ^ k := pow_le_pow_left₀ (by norm_num) h2 k
      _ = exp k := by rw [← exp_nat_mul, mul_one]
  have h4 : (4 : ℝ) ≤ exp 2 :=
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h2 2
      _ = exp 2 := by rw [← exp_nat_mul]; norm_num
  have hq_exp : (q₂ : ℝ) ≤ exp ((q₂ : ℝ) - 1) := by
    linarith [add_one_le_exp ((q₂ : ℝ) - 1)]
  have h1le_pow : (1 : ℝ) ≤ (2 : ℝ) ^ #u * (2 : ℝ) ^ #w :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have hpre : 2 * ((Fintype.card ↥(u.powerset ×ˢ w.powerset) : ℝ) + 1) * q₂ ≤
      exp 2 * (exp #u * exp #w) * exp ((q₂ : ℝ) - 1) := by
    rw [hcard]
    push_cast
    have hstep1 : 2 * ((2 : ℝ) ^ #u * (2 : ℝ) ^ #w + 1) ≤ 4 * ((2 : ℝ) ^ #u * (2 : ℝ) ^ #w) := by
      linarith
    calc 2 * ((2 : ℝ) ^ #u * (2 : ℝ) ^ #w + 1) * q₂
        ≤ 4 * ((2 : ℝ) ^ #u * (2 : ℝ) ^ #w) * q₂ := by gcongr
      _ ≤ exp 2 * (exp #u * exp #w) * exp ((q₂ : ℝ) - 1) := by
        gcongr
        · exact hpow #u
        · exact hpow #w
  have hexp_arg : -2 * (ξ₀ * (#u * #w : ℕ)) ^ 2 / (#(u ×ˢ w) : ℝ) =
      -2 * (ξ₀ ^ 2 * #u) * #w := by
    rw [card_product]
    push_cast
    field_simp
  calc 2 * ((Fintype.card ↥(u.powerset ×ˢ w.powerset) : ℝ) + 1) * q₂ *
        exp (-2 * (ξ₀ * (#u * #w : ℕ)) ^ 2 / #(u ×ˢ w))
      ≤ exp 2 * (exp #u * exp #w) * exp ((q₂ : ℝ) - 1) * exp (-2 * (ξ₀ ^ 2 * #u) * #w) := by
        rw [hexp_arg]
        exact mul_le_mul_of_nonneg_right hpre (exp_pos _).le
    _ = exp (1 + #u + #w + q₂ - 2 * (ξ₀ ^ 2 * #u) * #w) := by
        simp only [← exp_add]
        ring_nf
    _ < 1 := by
        rw [exp_lt_one_iff, sub_neg]
        have hmul1 : ((q₂ : ℝ) + 3) * #w ≤ (ξ₀ ^ 2 * #u) * #w :=
          mul_le_mul_of_nonneg_right hu hw_pos.le
        have hmul2 : ((q₂ : ℝ) + 3) * #u ≤ (ξ₀ ^ 2 * #w) * #u :=
          mul_le_mul_of_nonneg_right hw hu_pos.le
        have hqw : (q₂ : ℝ) ≤ (q₂ : ℝ) * #w := le_mul_of_one_le_right (Nat.cast_nonneg _) hw1
        have hqu : 0 ≤ (q₂ : ℝ) * #u := mul_nonneg (Nat.cast_nonneg _) hu_pos.le
        nlinarith

end Bounds

namespace PairColorSystem

variable {κ V : Type*} [Fintype V] [DecidableEq V]

/-- **Energy gap controls `L¹` block-density deviation.** If `Q ≤ P` and
`S.energy Q - S.energy P ≤ γ`, then for every color `c` the sum over all ordered distinct pairs of
the absolute block-density difference between `Q` and `P` is at most `√γ * |V|²`. -/
theorem sum_abs_pairColorDensity_sub_le [Fintype κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) {γ : ℝ}
    (hgap : S.energy Q - S.energy P ≤ γ) (c : κ) :
    ∑ p ∈ (univ : Finset V).offDiag,
        |(pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
          pairColorDensity S c (P.part p.1) (P.part p.2)| ≤
      √γ * (Fintype.card V : ℝ) ^ 2 := by
  set D := #(univ : Finset V).offDiag
  obtain hD | hD := eq_or_ne D 0
  · have hemp : (univ : Finset V).offDiag = ∅ := card_eq_zero.1 hD
    rw [hemp, sum_empty]
    exact mul_nonneg (sqrt_nonneg _) (sq_nonneg _)
  have hDpos : (0 : ℝ) < D := Nat.cast_pos.2 (Nat.pos_of_ne_zero hD)
  have hDle : (D : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have : D ≤ #(univ : Finset (V × V)) := card_le_card (subset_univ _)
    rw [card_univ, Fintype.card_prod, ← sq] at this
    exact_mod_cast this
  rw [← S.sum_sq_pairColorDensity_sub_div_eq_energy_sub hQP] at hgap
  have hw : ∑ _p ∈ (univ : Finset V).offDiag, (D : ℝ)⁻¹ ≤ 1 := by
    rw [sum_const, nsmul_eq_mul, mul_inv_cancel₀ hDpos.ne']
  have hsq : ∑ p ∈ (univ : Finset V).offDiag, (D : ℝ)⁻¹ *
      ((pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
        pairColorDensity S c (P.part p.1) (P.part p.2)) ^ 2 ≤ γ := by
    refine le_trans ?_ hgap
    rw [← mul_sum, inv_mul_eq_div]
    gcongr with p _hp
    exact single_le_sum (f := fun b ↦
      ((pairColorDensity S b (Q.part p.1) (Q.part p.2) : ℝ) -
        pairColorDensity S b (P.part p.1) (P.part p.2)) ^ 2)
      (fun _ _ ↦ sq_nonneg _) (mem_univ c)
  have hcs := weighted_sum_abs_le_sqrt (univ : Finset V).offDiag (fun _ ↦ (D : ℝ)⁻¹) _
    (fun _ _ ↦ inv_nonneg.2 hDpos.le) hw hsq
  rw [← mul_sum, inv_mul_le_iff₀ hDpos] at hcs
  exact hcs.trans ((mul_le_mul_of_nonneg_right hDle (sqrt_nonneg _)).trans_eq (mul_comm _ _))

/-- Iterated seeded regularization stops within `⌊1 / γ⌋₊` coarse steps at an equipartition pair
`Q ≤ P ≤ P₀` with small energy gap and fine quasi-regularity. -/
private theorem exists_strong_pairColor_witness [Fintype κ] (S : PairColorSystem κ V)
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {δ : ℝ} (hδ : 0 < δ)
    {G : ℕ → ℝ} (hG : ∀ k, 0 < G k) :
    ∃ P Q : Finpartition (univ : Finset V),
      Q ≤ P ∧ P ≤ P₀ ∧ P.IsEquipartition ∧ Q.IsEquipartition ∧
      #P.parts ≤ strongPairColorPartBound (Fintype.card κ) δ G #P₀.parts ∧
      #Q.parts ≤ strongPairColorStepBound (Fintype.card κ) δ G
        (strongPairColorPartBound (Fintype.card κ) δ G #P₀.parts) ∧
      S.energy Q - S.energy P ≤ pairEnergyGap (Fintype.card κ) δ ∧
      ∑ UV ∈ S.irregularPairs (pairFineScale (Fintype.card κ) δ G #P.parts) Q,
          (#UV.1 * #UV.2 : ℝ) ≤
        pairFineScale (Fintype.card κ) δ G #P.parts * (Fintype.card V : ℝ) ^ 2 := by
  set q₂ := Fintype.card κ
  set γ := pairEnergyGap q₂ δ
  have hγ : 0 < γ := pairEnergyGap_pos q₂ hδ
  set step := strongPairColorStepBound q₂ δ G
  have hstep_mono : Monotone step := strongPairColorStepBound_mono q₂ δ G
  have hid : id ≤ step := le_strongPairColorStepBound q₂ hδ hG
  let Good (P : Finpartition (univ : Finset V)) : Prop :=
    ∃ Q : Finpartition (univ : Finset V), Q ≤ P ∧ Q.IsEquipartition ∧
      #Q.parts ≤ step #P.parts ∧ S.energy Q - S.energy P ≤ γ ∧
      ∑ UV ∈ S.irregularPairs (pairFineScale q₂ δ G #P.parts) Q, (#UV.1 * #UV.2 : ℝ) ≤
        pairFineScale q₂ δ G #P.parts * (Fintype.card V : ℝ) ^ 2
  have advance (P : Finpartition (univ : Finset V)) (hP : P.IsEquipartition) :
      Good P ∨ ∃ Q : Finpartition (univ : Finset V), Q ≤ P ∧ Q.IsEquipartition ∧
        #Q.parts ≤ step #P.parts ∧ S.energy P + γ < S.energy Q := by
    obtain ⟨Q, hQP, hQ, hQcard, hQreg⟩ := S.exists_refining_equipartition_sum_irregularPairs_le P
      hP (pairFineScale_pos q₂ hδ hG #P.parts)
    have hQstep : #Q.parts ≤ step #P.parts :=
      hQcard.trans (equitablePairColorRegularityBound_le_step le_rfl)
    by_cases hgap : S.energy Q - S.energy P ≤ γ
    · exact Or.inl ⟨Q, hQP, hQ, hQstep, hgap, hQreg⟩
    · exact Or.inr ⟨Q, hQP, hQ, hQstep, by linarith⟩
  have key (j : ℕ) :
      (∃ P : Finpartition (univ : Finset V), P ≤ P₀ ∧ P.IsEquipartition ∧
        #P.parts ≤ step^[j] #P₀.parts ∧ Good P) ∨
      ∃ P : Finpartition (univ : Finset V), P ≤ P₀ ∧ P.IsEquipartition ∧
        #P.parts ≤ step^[j] #P₀.parts ∧ j * γ ≤ S.energy P := by
    induction j with
    | zero =>
      exact Or.inr ⟨P₀, le_rfl, hP₀, le_rfl, by simpa using S.energy_nonneg P₀⟩
    | succ j ih =>
      have hle : step^[j] #P₀.parts ≤ step^[j + 1] #P₀.parts := by
        rw [Function.iterate_succ_apply']
        exact hid _
      obtain ⟨P, hPP₀, hP, hPcard, hgood⟩ | ⟨P, hPP₀, hP, hPcard, hE⟩ := ih
      · exact Or.inl ⟨P, hPP₀, hP, hPcard.trans hle, hgood⟩
      obtain hgood | ⟨Q, hQP, hQ, hQcard, hE'⟩ := advance P hP
      · exact Or.inl ⟨P, hPP₀, hP, hPcard.trans hle, hgood⟩
      refine Or.inr ⟨Q, hQP.trans hPP₀, hQ, ?_, ?_⟩
      · rw [Function.iterate_succ_apply']
        exact hQcard.trans (hstep_mono hPcard)
      · push_cast
        linarith
  have hK : 1 < (⌊1 / γ⌋₊ + 1 : ℕ) * γ := by
    rw [← div_lt_iff₀ hγ, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  obtain ⟨P, hPP₀, hP, hPcard, ⟨Q, hQP, hQ, hQcard, hgap, hQreg⟩⟩ :
      ∃ P : Finpartition (univ : Finset V), P ≤ P₀ ∧ P.IsEquipartition ∧
        #P.parts ≤ step^[⌊1 / γ⌋₊] #P₀.parts ∧ Good P := by
    obtain hgood | ⟨P, hPP₀, hP, hPcard, hE⟩ := key ⌊1 / γ⌋₊
    · exact hgood
    obtain hgood | ⟨Q, -, -, -, hE'⟩ := advance P hP
    · exact ⟨P, hPP₀, hP, hPcard, hgood⟩
    push_cast at hK
    linarith [S.energy_le_one Q]
  exact ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard, hQcard.trans (hstep_mono hPcard), hgap, hQreg⟩

/-- In an equipartition `P` of `univ` with `#P.parts ≤ |V|`, every cell `A` satisfies
`|V| ≤ 2 * #P.parts * #A`. -/
private theorem card_univ_le_two_mul_parts_mul_card {P : Finpartition (univ : Finset V)}
    (hP : P.IsEquipartition) (hPV : #P.parts ≤ Fintype.card V) {A : Finset V} (hA : A ∈ P.parts) :
    Fintype.card V ≤ 2 * #P.parts * #A := by
  have hPpos : 0 < #P.parts := card_pos.2 ⟨A, hA⟩
  have hdiv_pos : 1 ≤ Fintype.card V / #P.parts := Nat.div_pos hPV hPpos
  have havg : Fintype.card V / #P.parts ≤ #A := by
    simpa [card_univ] using hP.average_le_card_part hA
  have hmod : Fintype.card V % #P.parts < #P.parts := Nat.mod_lt _ hPpos
  have hdiv_eq := Nat.div_add_mod (Fintype.card V) #P.parts
  calc Fintype.card V
      = #P.parts * (Fintype.card V / #P.parts) + Fintype.card V % #P.parts := hdiv_eq.symm
    _ ≤ #P.parts * (Fintype.card V / #P.parts) + #P.parts * 1 := by omega
    _ ≤ #P.parts * (Fintype.card V / #P.parts) +
          #P.parts * (Fintype.card V / #P.parts) :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ hdiv_pos) _
    _ = 2 * #P.parts * (Fintype.card V / #P.parts) := by ring
    _ ≤ 2 * #P.parts * #A := Nat.mul_le_mul_left _ havg

/-- Under `strongPairColorHostBound`, every cell of a bounded fine equipartition `Q` satisfies the
quadratic size threshold needed for the exponential union bound on `U ×ˢ W`. -/
private theorem fine_part_card_bound {q₂ l₀ : ℕ} {δ : ℝ} {G : ℕ → ℝ}
    {P Q : Finpartition (univ : Finset V)} (hQ : Q.IsEquipartition)
    (hPbound : #P.parts ≤ strongPairColorPartBound q₂ δ G l₀)
    (hQbound : #Q.parts ≤ strongPairColorStepBound q₂ δ G (strongPairColorPartBound q₂ δ G l₀))
    (hδ : 0 < δ) (hG : ∀ k, 0 < G k)
    (hV : strongPairColorHostBound q₂ δ G l₀ ≤ Fintype.card V)
    {U : Finset V} (hU : U ∈ Q.parts) :
    (q₂ + 3 : ℝ) ≤ (pairFineScale q₂ δ G #P.parts / (q₂ + 1)) ^ 2 * #U := by
  have hKM_le_n :
      ((range (strongPairColorPartBound q₂ δ G l₀ + 1)).sup
        fun k ↦ ⌈(q₂ + 3 : ℝ) / (pairFineScale q₂ δ G k / (q₂ + 1)) ^ 2⌉₊ + 1) *
        max (strongPairColorStepBound q₂ δ G (strongPairColorPartBound q₂ δ G l₀)) 1 ≤
          Fintype.card V :=
    (le_max_right _ _).trans hV
  generalize strongPairColorPartBound q₂ δ G l₀ = B_P at hPbound hQbound hKM_le_n
  generalize strongPairColorStepBound q₂ δ G B_P = M_P at hQbound hKM_le_n
  set ξ₀ := pairFineScale q₂ δ G #P.parts / (q₂ + 1)
  have hξP_pos : 0 < pairFineScale q₂ δ G #P.parts := pairFineScale_pos q₂ hδ hG #P.parts
  have hξ₀_pos : 0 < ξ₀ := by positivity
  set K_req := (range (B_P + 1)).sup
    (fun k ↦ ⌈(q₂ + 3 : ℝ) / (pairFineScale q₂ δ G k / (q₂ + 1)) ^ 2⌉₊ + 1)
  have hQpos : 0 < #Q.parts := card_pos.2 ⟨U, hU⟩
  have hQM : #Q.parts ≤ max M_P 1 := hQbound.trans (le_max_left _ _)
  have hK_mul : K_req * #Q.parts ≤ Fintype.card V :=
    (Nat.mul_le_mul_left K_req hQM).trans hKM_le_n
  have hK_div : K_req ≤ Fintype.card V / #Q.parts := (Nat.le_div_iff_mul_le hQpos).2 hK_mul
  have havg : Fintype.card V / #Q.parts ≤ #U := by
    simpa [card_univ] using hQ.average_le_card_part hU
  have hKt : ⌈(q₂ + 3 : ℝ) / ξ₀ ^ 2⌉₊ + 1 ≤ K_req :=
    le_sup (f := fun k ↦ ⌈(q₂ + 3 : ℝ) / (pairFineScale q₂ δ G k / (q₂ + 1)) ^ 2⌉₊ + 1)
      (mem_range.2 (Nat.lt_succ_of_le hPbound))
  have hceil_U : (⌈(q₂ + 3 : ℝ) / ξ₀ ^ 2⌉₊ : ℝ) ≤ #U := by
    exact_mod_cast (Nat.le_succ _).trans (hKt.trans (hK_div.trans havg))
  exact (div_le_iff₀' (sq_pos_of_pos hξ₀_pos)).1 ((Nat.le_ceil _).trans hceil_U)

open Classical in
/-- Coupled recoloring on a single fine rectangle `U ×ˢ W` inside disjoint coarse parent cells,
controlling both total edits and all subrectangle color counts. -/
private theorem exists_local_block_recoloring [Fintype κ] [Nonempty κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P)
    {ξ_P ξ₀ : ℝ} (hξP_pos : 0 < ξ_P) (hξ₀_pos : 0 < ξ₀)
    (hU_large : ∀ U ∈ Q.parts, (Fintype.card κ + 3 : ℝ) ≤ ξ₀ ^ 2 * #U)
    (x₀ : V × V → κ)
    (hx₀ : ∀ p : V × V, ∀ h : p.1 ≠ p.2, x₀ p = S.color ⟨p, h⟩)
    (U W : Q.parts) :
    ∃ x : V × V → κ,
      refinementParent hQP U ≠ refinementParent hQP W →
        (#{q ∈ U.1 ×ˢ W.1 | x q ≠ x₀ q} : ℝ) ≤
          ((∑ c, |(pairColorDensity S c U.1 W.1 : ℝ) -
              pairColorDensity S c (refinementParent hQP U).1 (refinementParent hQP W).1|) / 2 +
            Fintype.card κ * ξ₀) * (#U.1 * #W.1 : ℕ) ∧
        ∀ U' ⊆ U.1, ∀ W' ⊆ W.1, ∀ c',
          |(#{q ∈ U' ×ˢ W' | x q = c'} : ℝ) -
              (pairColorDensity S c' (refinementParent hQP U).1 (refinementParent hQP W).1 : ℝ) *
                (#U' * #W' : ℕ)| ≤
            (Fintype.card κ * ξ₀ + Fintype.card κ * ξ_P) * (#U.1 * #W.1 : ℕ) +
              if (U.1, W.1) ∈ S.irregularPairs ξ_P Q then
                (Fintype.card κ : ℝ) * (#U.1 * #W.1 : ℕ) else 0 := by
  classical
  set q₂ := Fintype.card κ
  let parent (X : Q.parts) : P.parts := refinementParent hQP X
  by_cases hAB : parent U = parent W
  · exact ⟨x₀, fun hne ↦ (hne hAB).elim⟩
  have hAB_val : (parent U).1 ≠ (parent W).1 := fun heq ↦ hAB (Subtype.ext heq)
  have hdisjAB : Disjoint (parent U).1 (parent W).1 :=
    P.disjoint (parent U).2 (parent W).2 hAB_val
  have hsubU : U.1 ⊆ (parent U).1 := le_refinementParent hQP U
  have hsubW : W.1 ⊆ (parent W).1 := le_refinementParent hQP W
  have hdisjUW : Disjoint U.1 W.1 := hdisjAB.mono hsubU hsubW
  have hAB_nonempty : (((parent U).1 ×ˢ (parent W).1).filter fun p ↦ p.1 ≠ p.2).Nonempty := by
    obtain ⟨u, hu⟩ := P.nonempty_of_mem_parts (parent U).2
    obtain ⟨w, hw⟩ := P.nonempty_of_mem_parts (parent W).2
    exact ⟨(u, w), mem_filter.2 ⟨mem_product.2 ⟨hu, hw⟩, hdisjAB.forall_ne_finset hu hw⟩⟩
  have hU_nonempty : U.1.Nonempty := Q.nonempty_of_mem_parts U.2
  have hW_nonempty : W.1.Nonempty := Q.nonempty_of_mem_parts W.2
  have hUW_pos : (0 : ℝ) < (#U.1 * #W.1 : ℕ) :=
    Nat.cast_pos.2 (Nat.mul_pos hU_nonempty.card_pos hW_nonempty.card_pos)
  have hp_nonneg (c : κ) : 0 ≤ (pairColorDensity S c (parent U).1 (parent W).1 : ℝ) := by
    exact_mod_cast pairColorDensity_nonneg S c (parent U).1 (parent W).1
  have hp_sum : ∑ c, (pairColorDensity S c (parent U).1 (parent W).1 : ℝ) = 1 := by
    exact_mod_cast sum_pairColorDensity S (parent U).1 (parent W).1 hAB_nonempty
  obtain ⟨x, -, hx_edit, hx_rect⟩ := exists_coupled_recoloring_abs_card_filter_sub_le
    (U.1 ×ˢ W.1) x₀ hp_nonneg hp_sum
    (I := ↥(U.1.powerset ×ˢ W.1.powerset)) (fun i ↦ i.1.1 ×ˢ i.1.2)
    (fun i ↦ product_subset_product (mem_powerset.1 (mem_product.1 i.2).1)
      (mem_powerset.1 (mem_product.1 i.2).2))
    (a := ξ₀ * (#U.1 * #W.1 : ℕ)) (mul_pos hξ₀_pos hUW_pos)
    (union_bound_powerset_product (hU_large U.1 U.2) (hU_large W.1 W.2))
  have hx₀_count {s : Finset V} {t' : Finset V} (hs : s ⊆ U.1) (ht' : t' ⊆ W.1) (c : κ) :
      (#{q ∈ s ×ˢ t' | x₀ q = c} : ℝ) =
        (pairColorDensity S c s t' : ℝ) * (#s * #t' : ℕ) := by
    have hfilt : {q ∈ s ×ˢ t' | S.colorOfPair q.1 q.2 = some c} =
        {q ∈ s ×ˢ t' | x₀ q = c} := filter_congr fun q hq ↦ by
      have hne : q.1 ≠ q.2 :=
        (hdisjUW.mono hs ht').forall_ne_finset (mem_product.1 hq).1 (mem_product.1 hq).2
      rw [S.colorOfPair_of_ne hne, Option.some_inj, hx₀ q hne]
    rw [← hfilt, Nat.cast_mul]
    exact_mod_cast (pairColorDensity_mul_card_of_disjoint S c (hdisjUW.mono hs ht')).symm
  refine ⟨x, fun _ ↦ ⟨?_, ?_⟩⟩
  · rw [card_product] at hx_edit
    have hsum_eq : ∑ c, |(#{q ∈ U.1 ×ˢ W.1 | x₀ q = c} : ℝ) -
          (pairColorDensity S c (parent U).1 (parent W).1 : ℝ) * (#U.1 * #W.1 : ℕ)| =
        (∑ c, |(pairColorDensity S c U.1 W.1 : ℝ) -
          pairColorDensity S c (parent U).1 (parent W).1|) * (#U.1 * #W.1 : ℕ) := by
      rw [sum_mul]
      refine sum_congr rfl fun c _ ↦ ?_
      rw [hx₀_count Subset.rfl Subset.rfl c, ← sub_mul, abs_mul, abs_of_pos hUW_pos]
    linarith [hx_edit, hsum_eq]
  · intro U' hU' W' hW' c'
    have htest := hx_rect ⟨(U', W'), mem_product.2 ⟨mem_powerset.2 hU', mem_powerset.2 hW'⟩⟩ c'
    simp only [card_product] at htest
    have hratio (c : κ) :
        (#{q ∈ U.1 ×ˢ W.1 | x₀ q = c} : ℝ) / (#U.1 * #W.1 : ℕ) =
          pairColorDensity S c U.1 W.1 := by
      rw [hx₀_count Subset.rfl Subset.rfl c, mul_div_cancel_right₀ _ hUW_pos.ne']
    have hsub_prod : ((#U' * #W' : ℕ) : ℝ) ≤ (#U.1 * #W.1 : ℕ) := by
      exact_mod_cast Nat.mul_le_mul (card_le_card hU') (card_le_card hW')
    have herr_term (c : κ) :
        |(#{q ∈ U' ×ˢ W' | x₀ q = c} : ℝ) -
            (#{q ∈ U.1 ×ˢ W.1 | x₀ q = c} : ℝ) / (#U.1 * #W.1 : ℕ) * (#U' * #W' : ℕ)| ≤
          if S.IsRegularPair ξ_P U.1 W.1 then ξ_P * (#U.1 * #W.1 : ℕ)
          else (#U.1 * #W.1 : ℕ) := by
      have habs_UW : |((#U' * #W' : ℕ) : ℝ)| = (#U' * #W' : ℕ) :=
        abs_of_nonneg (Nat.cast_nonneg _)
      rw [hx₀_count hU' hW' c, hratio c, ← sub_mul, abs_mul, habs_UW]
      have hd_le_one : |(pairColorDensity S c U' W' : ℝ) - pairColorDensity S c U.1 W.1| ≤ 1 := by
        have h01 : (0 : ℝ) ≤ pairColorDensity S c U' W' := by
          exact_mod_cast pairColorDensity_nonneg S c U' W'
        have h11 : (pairColorDensity S c U' W' : ℝ) ≤ 1 := by
          exact_mod_cast pairColorDensity_le_one S c U' W'
        have h02 : (0 : ℝ) ≤ pairColorDensity S c U.1 W.1 := by
          exact_mod_cast pairColorDensity_nonneg S c U.1 W.1
        have h12 : (pairColorDensity S c U.1 W.1 : ℝ) ≤ 1 := by
          exact_mod_cast pairColorDensity_le_one S c U.1 W.1
        exact abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
      split_ifs with hregUW
      · by_cases hsizeUW : ξ_P * #U.1 ≤ #U' ∧ ξ_P * #W.1 ≤ #W'
        · have hdev := isRegularPair_iff.1 hregUW c U' hU' W' hW' hsizeUW.1 hsizeUW.2
          exact mul_le_mul hdev hsub_prod (Nat.cast_nonneg _) hξP_pos.le
        · rcases not_and_or.1 hsizeUW with hUsmall | hWsmall
          · have hUlt : (#U' : ℝ) < ξ_P * #U.1 := lt_of_not_ge hUsmall
            have hprod_small : ((#U' * #W' : ℕ) : ℝ) ≤ ξ_P * (#U.1 * #W.1 : ℕ) := by
              calc ((#U' * #W' : ℕ) : ℝ) = #U' * #W' := by push_cast; ring
                _ ≤ (ξ_P * #U.1) * #W.1 :=
                  mul_le_mul hUlt.le (by exact_mod_cast card_le_card hW')
                    (Nat.cast_nonneg _) (mul_nonneg hξP_pos.le (Nat.cast_nonneg _))
                _ = ξ_P * (#U.1 * #W.1 : ℕ) := by push_cast; ring
            exact (mul_le_of_le_one_left (Nat.cast_nonneg _) hd_le_one).trans hprod_small
          · have hWlt : (#W' : ℝ) < ξ_P * #W.1 := lt_of_not_ge hWsmall
            have hprod_small : ((#U' * #W' : ℕ) : ℝ) ≤ ξ_P * (#U.1 * #W.1 : ℕ) := by
              calc ((#U' * #W' : ℕ) : ℝ) = #U' * #W' := by push_cast; ring
                _ ≤ #U.1 * (ξ_P * #W.1) :=
                  mul_le_mul (by exact_mod_cast card_le_card hU') hWlt.le
                    (Nat.cast_nonneg _) (Nat.cast_nonneg _)
                _ = ξ_P * (#U.1 * #W.1 : ℕ) := by push_cast; ring
            exact (mul_le_of_le_one_left (Nat.cast_nonneg _) hd_le_one).trans hprod_small
      · exact (mul_le_of_le_one_left (Nat.cast_nonneg _) hd_le_one).trans hsub_prod
    have hsum_err :
        ∑ c, |(#{q ∈ U' ×ˢ W' | x₀ q = c} : ℝ) -
            (#{q ∈ U.1 ×ˢ W.1 | x₀ q = c} : ℝ) / (#U.1 * #W.1 : ℕ) * (#U' * #W' : ℕ)| ≤
          q₂ * ξ_P * (#U.1 * #W.1 : ℕ) +
            if (U.1, W.1) ∈ S.irregularPairs ξ_P Q then
              (q₂ : ℝ) * (#U.1 * #W.1 : ℕ) else 0 := by
      calc _ ≤ ∑ _c : κ, (if S.IsRegularPair ξ_P U.1 W.1 then ξ_P * (#U.1 * #W.1 : ℕ)
                else (#U.1 * #W.1 : ℕ)) := sum_le_sum fun c _ ↦ herr_term c
        _ = q₂ * (if S.IsRegularPair ξ_P U.1 W.1 then ξ_P * (#U.1 * #W.1 : ℕ)
              else (#U.1 * #W.1 : ℕ)) := by
            rw [sum_const, card_univ, nsmul_eq_mul]
        _ ≤ _ := by
            by_cases hregUW : S.IsRegularPair ξ_P U.1 W.1
            · have hnot_irr : (U.1, W.1) ∉ S.irregularPairs ξ_P Q := fun hm ↦
                (S.mem_irregularPairs.1 hm).2.2.2 hregUW
              simp only [ite_eq_left hregUW, ite_eq_right hnot_irr, add_zero]
              ring_nf
              exact le_rfl
            · have hUW_ne : U.1 ≠ W.1 := fun heq ↦
                hU_nonempty.ne_empty (disjoint_self.1 (heq ▸ hdisjUW))
              have hirr : (U.1, W.1) ∈ S.irregularPairs ξ_P Q :=
                S.mem_irregularPairs.2 ⟨U.2, W.2, hUW_ne, hregUW⟩
              simp only [ite_eq_right hregUW, ite_eq_left hirr]
              have : 0 ≤ (q₂ : ℝ) * ξ_P * (#U.1 * #W.1 : ℕ) := by positivity
              linarith
    linarith [htest, hsum_err]

/-- Pure algebraic calibration converting the combined local sampling and fine-irregularity errors
into `2 * τ * (a' * b')` whenever `2 * τ * a ≤ a'` and `2 * τ * b ≤ b'`. -/
private theorem pairFineScale_err_le_subrect {q₂ t n a b a' b' : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {G : ℕ → ℝ} (hG : ∀ k, 0 < G k) (hn_a : (n : ℝ) ≤ 2 * t * a) (hn_b : (n : ℝ) ≤ 2 * t * b)
    (ha' : 2 * pairQuarterTol G t * a ≤ a') (hb' : 2 * pairQuarterTol G t * b ≤ b') :
    (q₂ * (pairFineScale q₂ δ G t / (q₂ + 1)) + q₂ * pairFineScale q₂ δ G t) * (a * b : ℝ) +
        q₂ * pairFineScale q₂ δ G t * (n : ℝ) ^ 2 ≤
      2 * pairQuarterTol G t * (a' * b' : ℕ) := by
  set τ := pairQuarterTol G t
  set ξ_P := pairFineScale q₂ δ G t
  set ξ₀ := ξ_P / (q₂ + 1)
  have hτ_pos : 0 < τ := pairQuarterTol_pos hG t
  have hξP_pos : 0 < ξ_P := pairFineScale_pos q₂ hδ hG t
  have hn2 : (n : ℝ) ^ 2 ≤ 4 * (t : ℝ) ^ 2 * (a * b : ℝ) := by
    calc (n : ℝ) ^ 2 = n * n := sq _
      _ ≤ (2 * t * a) * (2 * t * b) := mul_le_mul hn_a hn_b (Nat.cast_nonneg _) (by positivity)
      _ = 4 * (t : ℝ) ^ 2 * (a * b : ℝ) := by ring
  have hqξ₀ : (q₂ : ℝ) * ξ₀ ≤ ξ_P := by
    dsimp [ξ₀]
    rw [mul_div_left_comm]
    refine mul_le_of_le_one_right hξP_pos.le (div_le_one_of_le₀ ?_ (by positivity))
    linarith
  have h1 : (q₂ : ℝ) * ξ_P * (n : ℝ) ^ 2 ≤ 4 * q₂ * (t : ℝ) ^ 2 * ξ_P * (a * b : ℝ) := by
    calc (q₂ : ℝ) * ξ_P * (n : ℝ) ^ 2
        ≤ (q₂ : ℝ) * ξ_P * (4 * (t : ℝ) ^ 2 * (a * b : ℝ)) :=
          mul_le_mul_of_nonneg_left hn2 (by positivity)
      _ = 4 * q₂ * (t : ℝ) ^ 2 * ξ_P * (a * b : ℝ) := by ring
  have hcoeff : q₂ * ξ₀ + q₂ * ξ_P + 4 * q₂ * (t : ℝ) ^ 2 * ξ_P ≤
      16 * (q₂ + 1 : ℝ) * ((t : ℝ) + 1) ^ 2 * ξ_P := by
    have hrem : 0 ≤ (15 + 15 * (q₂ : ℝ) + 32 * (q₂ + 1) * t +
        (12 * q₂ + 16) * (t : ℝ) ^ 2) * ξ_P := by positivity
    have hid : 16 * (q₂ + 1 : ℝ) * ((t : ℝ) + 1) ^ 2 * ξ_P =
        ξ_P + q₂ * ξ_P + 4 * q₂ * (t : ℝ) ^ 2 * ξ_P +
          (15 + 15 * (q₂ : ℝ) + 32 * (q₂ + 1) * t + (12 * q₂ + 16) * (t : ℝ) ^ 2) * ξ_P := by
      ring
    linarith [hqξ₀, hrem, hid]
  have hξ_bound : ξ_P ≤ τ ^ 3 / (16 * (q₂ + 1 : ℝ) * ((t : ℝ) + 1) ^ 2) := by
    dsimp only [ξ_P, pairFineScale]
    exact min_le_right _ _
  have hden_pos : 0 < 16 * (q₂ + 1 : ℝ) * ((t : ℝ) + 1) ^ 2 := by positivity
  have hmul : 16 * (q₂ + 1 : ℝ) * ((t : ℝ) + 1) ^ 2 * ξ_P ≤ τ ^ 3 :=
    (le_div_iff₀' hden_pos).1 hξ_bound
  have hτ_le8 : τ ^ 3 ≤ 8 * τ ^ 3 := by linarith [pow_pos hτ_pos 3]
  calc (q₂ * ξ₀ + q₂ * ξ_P) * (a * b : ℝ) + q₂ * ξ_P * (n : ℝ) ^ 2
      ≤ (q₂ * ξ₀ + q₂ * ξ_P + 4 * q₂ * (t : ℝ) ^ 2 * ξ_P) * (a * b : ℝ) := by linarith
    _ ≤ 16 * (q₂ + 1 : ℝ) * ((t : ℝ) + 1) ^ 2 * ξ_P * (a * b : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
    _ ≤ τ ^ 3 * (a * b : ℝ) := mul_le_mul_of_nonneg_right hmul (by positivity)
    _ ≤ 8 * τ ^ 3 * (a * b : ℝ) := mul_le_mul_of_nonneg_right hτ_le8 (by positivity)
    _ = 2 * τ * ((2 * τ * a) * (2 * τ * b)) := by ring
    _ ≤ 2 * τ * ((a' : ℝ) * b') :=
        mul_le_mul_of_nonneg_left (mul_le_mul ha' hb' (by positivity) (Nat.cast_nonneg _))
          (by positivity)
    _ = 2 * τ * (a' * b' : ℕ) := by rw [Nat.cast_mul]

open Classical in
/-- If `R` agrees with the local block recolorings `xloc` on `A ×ˢ B` for distinct coarse parts
`A ≠ B`, then `(A, B)` is `(4 * τ)`-regular in `R`. -/
private theorem glued_isRegularPair_of_ne [Fintype κ] (S R : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (hP : P.IsEquipartition)
    {δ : ℝ} (hδ : 0 < δ) {G : ℕ → ℝ} (hG : ∀ k, 0 < G k)
    (hQreg : ∑ UV ∈ S.irregularPairs (pairFineScale (Fintype.card κ) δ G #P.parts) Q,
        (#UV.1 * #UV.2 : ℝ) ≤
      pairFineScale (Fintype.card κ) δ G #P.parts * (Fintype.card V : ℝ) ^ 2)
    (xloc : Q.parts → Q.parts → V × V → κ)
    (hxloc_rect : ∀ U W : Q.parts, refinementParent hQP U ≠ refinementParent hQP W →
      ∀ U' ⊆ U.1, ∀ W' ⊆ W.1, ∀ c',
        |(#{q ∈ U' ×ˢ W' | xloc U W q = c'} : ℝ) -
            (pairColorDensity S c' (refinementParent hQP U).1 (refinementParent hQP W).1 : ℝ) *
              (#U' * #W' : ℕ)| ≤
          (Fintype.card κ * (pairFineScale (Fintype.card κ) δ G #P.parts / (Fintype.card κ + 1)) +
              Fintype.card κ * pairFineScale (Fintype.card κ) δ G #P.parts) * (#U.1 * #W.1 : ℕ) +
            if (U.1, W.1) ∈ S.irregularPairs (pairFineScale (Fintype.card κ) δ G #P.parts) Q then
              (Fintype.card κ : ℝ) * (#U.1 * #W.1 : ℕ) else 0)
    {A B : P.parts} (hAB_ne : A ≠ B)
    (hR_AB : ∀ p : {p : V × V // p.1 ≠ p.2}, p.1.1 ∈ A.1 → p.1.2 ∈ B.1 →
      R.color p = xloc ⟨Q.part p.1.1, Q.part_mem.2 (mem_univ _)⟩
        ⟨Q.part p.1.2, Q.part_mem.2 (mem_univ _)⟩ p.1) :
    R.IsRegularPair (4 * pairQuarterTol G #P.parts) A.1 B.1 := by
  classical
  set q₂ := Fintype.card κ
  set n := Fintype.card V
  set t := #P.parts
  set τ := pairQuarterTol G t
  set ξ_P := pairFineScale q₂ δ G t
  set ξ₀ := ξ_P / (q₂ + 1)
  have hτ_pos : 0 < τ := pairQuarterTol_pos hG t
  let cellP (u : V) : P.parts := ⟨P.part u, P.part_mem.2 (mem_univ u)⟩
  let cellQ (u : V) : Q.parts := ⟨Q.part u, Q.part_mem.2 (mem_univ u)⟩
  have hcellQ_parent (u : V) : refinementParent hQP (cellQ u) = cellP u := by
    apply Subtype.ext
    have hmem : u ∈ (refinementParent hQP (cellQ u)).1 :=
      le_refinementParent hQP (cellQ u) (Q.mem_part_self.2 (mem_univ u))
    exact (P.part_eq_of_mem (refinementParent hQP (cellQ u)).2 hmem).symm
  have hPV : t ≤ n := P.card_parts_le_card.trans_eq card_univ
  have hAB_val : A.1 ≠ B.1 := fun heq ↦ hAB_ne (Subtype.ext heq)
  have hdisjAB : Disjoint A.1 B.1 := P.disjoint A.2 B.2 hAB_val
  have hrect_dev (c' : κ) {A' B' : Finset V} (hA' : A' ⊆ A.1) (hB' : B.1 ⊇ B')
      (hA'size : 2 * τ * #A.1 ≤ #A') (hB'size : 2 * τ * #B.1 ≤ #B') :
      |(pairColorDensity R c' A' B' : ℝ) - pairColorDensity S c' A.1 B.1| ≤ 2 * τ := by
    let QA : Finset Q.parts := univ.filter fun U ↦ U.1 ⊆ A.1
    let QB : Finset Q.parts := univ.filter fun W ↦ W.1 ⊆ B.1
    have hQA_union : QA.biUnion (fun U ↦ U.1) = A.1 := by
      ext u
      simp only [QA, mem_biUnion, mem_filter, mem_univ, true_and]
      refine ⟨fun ⟨_, hUA, huU⟩ ↦ hUA huU, fun huA ↦ ⟨cellQ u, ?_, Q.mem_part_self.2 (mem_univ u)⟩⟩
      have hp : refinementParent hQP (cellQ u) = A :=
        (hcellQ_parent u).trans (Subtype.ext (P.part_eq_of_mem A.2 huA))
      exact hp ▸ le_refinementParent hQP (cellQ u)
    have hQB_union : QB.biUnion (fun W ↦ W.1) = B.1 := by
      ext v
      simp only [QB, mem_biUnion, mem_filter, mem_univ, true_and]
      refine ⟨fun ⟨_, hWB, hvW⟩ ↦ hWB hvW, fun hvB ↦ ⟨cellQ v, ?_, Q.mem_part_self.2 (mem_univ v)⟩⟩
      have hp : refinementParent hQP (cellQ v) = B :=
        (hcellQ_parent v).trans (Subtype.ext (P.part_eq_of_mem B.2 hvB))
      exact hp ▸ le_refinementParent hQP (cellQ v)
    have hQA_disj : (QA : Set Q.parts).PairwiseDisjoint (fun U ↦ U.1) :=
      fun U _ U' _ hne ↦ Q.disjoint U.2 U'.2 fun heq ↦ hne (Subtype.ext heq)
    have hQB_disj : (QB : Set Q.parts).PairwiseDisjoint (fun W ↦ W.1) :=
      fun W _ W' _ hne ↦ Q.disjoint W.2 W'.2 fun heq ↦ hne (Subtype.ext heq)
    have hQA_card : ∑ U ∈ QA, #U.1 = #A.1 := by
      rw [← card_biUnion hQA_disj, hQA_union]
    have hQB_card : ∑ W ∈ QB, #W.1 = #B.1 := by
      rw [← card_biUnion hQB_disj, hQB_union]
    have hA'_union : QA.biUnion (fun U ↦ A' ∩ U.1) = A' := by
      ext u
      simp only [mem_biUnion, mem_inter]
      refine ⟨fun ⟨_, _, huA', _⟩ ↦ huA', fun huA' ↦ ?_⟩
      obtain ⟨U, hUQA, huU⟩ := mem_biUnion.1 (hQA_union.symm ▸ hA' huA')
      exact ⟨U, hUQA, huA', huU⟩
    have hB'_union : QB.biUnion (fun W ↦ B' ∩ W.1) = B' := by
      ext v
      simp only [mem_biUnion, mem_inter]
      refine ⟨fun ⟨_, _, hvB', _⟩ ↦ hvB', fun hvB' ↦ ?_⟩
      obtain ⟨W, hWQB, hvW⟩ := mem_biUnion.1 (hQB_union.symm ▸ hB' hvB')
      exact ⟨W, hWQB, hvB', hvW⟩
    have hA'_card : ∑ U ∈ QA, #(A' ∩ U.1) = #A' := by
      rw [← card_biUnion (fun U hU U' hU' hne ↦
        (hQA_disj hU hU' hne).mono inter_subset_right inter_subset_right), hA'_union]
    have hB'_card : ∑ W ∈ QB, #(B' ∩ W.1) = #B' := by
      rw [← card_biUnion (fun W hW W' hW' hne ↦
        (hQB_disj hW hW' hne).mono inter_subset_right inter_subset_right), hB'_union]
    have hprod_union : (QA ×ˢ QB).biUnion (fun UW ↦ (A' ∩ UW.1.1) ×ˢ (B' ∩ UW.2.1)) =
        A' ×ˢ B' := by
      ext ⟨u, v⟩
      simp only [mem_biUnion, mem_product, mem_inter, Prod.exists]
      refine ⟨fun ⟨_, _, _, ⟨huA', _⟩, ⟨hvB', _⟩⟩ ↦ ⟨huA', hvB'⟩, fun ⟨huA', hvB'⟩ ↦ ?_⟩
      obtain ⟨U, hUQ, huU⟩ := mem_biUnion.1 (hQA_union.symm ▸ hA' huA')
      obtain ⟨W, hWQ, hvW⟩ := mem_biUnion.1 (hQB_union.symm ▸ hB' hvB')
      exact ⟨U, W, ⟨hUQ, hWQ⟩, ⟨huA', huU⟩, ⟨hvB', hvW⟩⟩
    have hprod_disj :
        ((QA ×ˢ QB : Finset (Q.parts × Q.parts)) : Set (Q.parts × Q.parts)).PairwiseDisjoint
          (fun UW : Q.parts × Q.parts ↦ (A' ∩ UW.1.1) ×ˢ (B' ∩ UW.2.1)) := by
      intro UW₁ h₁ UW₂ h₂ hne
      refine disjoint_product.2 ?_
      by_cases hfst : UW₁.1 = UW₂.1
      · have hsnd : UW₁.2 ≠ UW₂.2 := fun hs ↦ hne (Prod.ext hfst hs)
        exact Or.inr ((hQB_disj (mem_product.1 h₁).2 (mem_product.1 h₂).2 hsnd).mono
          inter_subset_right inter_subset_right)
      · exact Or.inl ((hQA_disj (mem_product.1 h₁).1 (mem_product.1 h₂).1 hfst).mono
          inter_subset_right inter_subset_right)
    have hR_count :
        (pairColorDensity R c' A' B' : ℝ) * (#A' * #B' : ℕ) =
          ∑ UW ∈ QA ×ˢ QB, (#{q ∈ (A' ∩ UW.1.1) ×ˢ (B' ∩ UW.2.1) |
            xloc UW.1 UW.2 q = c'} : ℝ) := by
      have h1 : (pairColorDensity R c' A' B' : ℝ) * (#A' * #B' : ℕ) =
          #{q ∈ A' ×ˢ B' | R.colorOfPair q.1 q.2 = some c'} := by
        rw [Nat.cast_mul]
        exact_mod_cast pairColorDensity_mul_card_of_disjoint R c' (hdisjAB.mono hA' hB')
      rw [h1, ← hprod_union, filter_biUnion,
        card_biUnion (fun UW₁ h₁ UW₂ h₂ hne ↦
          (hprod_disj h₁ h₂ hne).mono (filter_subset _ _) (filter_subset _ _)),
        Nat.cast_sum]
      refine sum_congr rfl fun UW hUW ↦ ?_
      obtain ⟨hUQA, hWQB⟩ := mem_product.1 hUW
      have hUA : UW.1.1 ⊆ A.1 := (mem_filter.1 hUQA).2
      have hWB : UW.2.1 ⊆ B.1 := (mem_filter.1 hWQB).2
      congr 2
      refine filter_congr fun q hq ↦ ?_
      obtain ⟨hq1, hq2⟩ := mem_product.1 hq
      have huU : q.1 ∈ UW.1.1 := (mem_inter.1 hq1).2
      have hvW : q.2 ∈ UW.2.1 := (mem_inter.1 hq2).2
      have huA : q.1 ∈ A.1 := hUA huU
      have hvB : q.2 ∈ B.1 := hWB hvW
      have hne_q : q.1 ≠ q.2 := hdisjAB.forall_ne_finset huA hvB
      have hcQ1 : cellQ q.1 = UW.1 := Subtype.ext (Q.part_eq_of_mem UW.1.2 huU)
      have hcQ2 : cellQ q.2 = UW.2 := Subtype.ext (Q.part_eq_of_mem UW.2.2 hvW)
      rw [R.colorOfPair_of_ne hne_q, Option.some_inj, hR_AB ⟨q, hne_q⟩ huA hvB]
      change xloc (cellQ q.1) (cellQ q.2) q = c' ↔ _
      rw [hcQ1, hcQ2]
    have htarget_sum :
        (pairColorDensity S c' A.1 B.1 : ℝ) * (#A' * #B' : ℕ) =
          ∑ UW ∈ QA ×ˢ QB, (pairColorDensity S c' A.1 B.1 : ℝ) *
            (#(A' ∩ UW.1.1) * #(B' ∩ UW.2.1) : ℕ) := by
      rw [← mul_sum, ← Nat.cast_sum, sum_product, ← hA'_card, ← hB'_card, sum_mul]
      simp_rw [mul_sum]
    have hAB_sum_card : ∑ UW ∈ QA ×ˢ QB, (#UW.1.1 * #UW.2.1 : ℝ) = (#A.1 * #B.1 : ℝ) := by
      rw [sum_product, ← hQA_card, ← hQB_card]
      push_cast
      rw [sum_mul]
      simp_rw [mul_sum]
    have hirr_sum :
        ∑ UW ∈ QA ×ˢ QB, (if (UW.1.1, UW.2.1) ∈ S.irregularPairs ξ_P Q then
            (q₂ : ℝ) * (#UW.1.1 * #UW.2.1 : ℕ) else 0) ≤
          q₂ * ξ_P * (n : ℝ) ^ 2 := by
      rw [← sum_filter]
      let emb : Q.parts × Q.parts ↪ Finset V × Finset V :=
        ⟨fun UW ↦ (UW.1.1, UW.2.1), fun UW₁ UW₂ h ↦
          Prod.ext (Subtype.ext (Prod.mk.inj h).1) (Subtype.ext (Prod.mk.inj h).2)⟩
      have hmap_sub : ((QA ×ˢ QB).filter fun UW ↦ (UW.1.1, UW.2.1) ∈ S.irregularPairs ξ_P Q).map
          emb ⊆ S.irregularPairs ξ_P Q := by
        intro UV hUV
        obtain ⟨UW, hUW, rfl⟩ := mem_map.1 hUV
        exact (mem_filter.1 hUW).2
      have hsum_map :
          ∑ UW ∈ (QA ×ˢ QB).filter (fun UW ↦ (UW.1.1, UW.2.1) ∈ S.irregularPairs ξ_P Q),
            (q₂ : ℝ) * (#UW.1.1 * #UW.2.1 : ℕ) =
          ∑ UV ∈ ((QA ×ˢ QB).filter (fun UW ↦ (UW.1.1, UW.2.1) ∈ S.irregularPairs ξ_P Q)).map emb,
            (q₂ : ℝ) * (#UV.1 * #UV.2 : ℝ) := by
        rw [sum_map]
        refine sum_congr rfl fun UW _ ↦ ?_
        dsimp [emb]
        push_cast
        rfl
      rw [hsum_map]
      calc _ ≤ ∑ UV ∈ S.irregularPairs ξ_P Q, (q₂ : ℝ) * (#UV.1 * #UV.2 : ℝ) :=
            sum_le_sum_of_subset_of_nonneg hmap_sub fun _ _ _ ↦ by positivity
        _ = q₂ * ∑ UV ∈ S.irregularPairs ξ_P Q, (#UV.1 * #UV.2 : ℝ) := (mul_sum ..).symm
        _ ≤ q₂ * (ξ_P * (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hQreg (Nat.cast_nonneg _)
        _ = q₂ * ξ_P * (n : ℝ) ^ 2 := by ring
    have hn_le_A : (n : ℝ) ≤ 2 * t * #A.1 := by
      exact_mod_cast card_univ_le_two_mul_parts_mul_card hP hPV A.2
    have hn_le_B : (n : ℝ) ≤ 2 * t * #B.1 := by
      exact_mod_cast card_univ_le_two_mul_parts_mul_card hP hPV B.2
    have hA_pos : (0 : ℝ) < #A.1 := Nat.cast_pos.2 (P.nonempty_of_mem_parts A.2).card_pos
    have hB_pos : (0 : ℝ) < #B.1 := Nat.cast_pos.2 (P.nonempty_of_mem_parts B.2).card_pos
    have hA'_pos : (0 : ℝ) < #A' := (mul_pos (by positivity) hA_pos).trans_le hA'size
    have hB'_pos : (0 : ℝ) < #B' := (mul_pos (by positivity) hB_pos).trans_le hB'size
    have hA'B'_pos : (0 : ℝ) < (#A' * #B' : ℕ) := by
      rw [Nat.cast_mul]
      exact mul_pos hA'_pos hB'_pos
    have htotal_count_dev :
        |(pairColorDensity R c' A' B' : ℝ) - pairColorDensity S c' A.1 B.1| *
            (#A' * #B' : ℕ) ≤
          2 * τ * (#A' * #B' : ℕ) := by
      have hrew : |(pairColorDensity R c' A' B' : ℝ) - pairColorDensity S c' A.1 B.1| *
          (#A' * #B' : ℕ) =
          |((pairColorDensity R c' A' B' : ℝ) * (#A' * #B' : ℕ)) -
            ((pairColorDensity S c' A.1 B.1 : ℝ) * (#A' * #B' : ℕ))| := by
        rw [← sub_mul, abs_mul, abs_of_pos hA'B'_pos]
      rw [hrew, hR_count, htarget_sum, ← sum_sub_distrib]
      calc |∑ UW ∈ QA ×ˢ QB,
              ((#{q ∈ (A' ∩ UW.1.1) ×ˢ (B' ∩ UW.2.1) | xloc UW.1 UW.2 q = c'} : ℝ) -
                (pairColorDensity S c' A.1 B.1 : ℝ) * (#(A' ∩ UW.1.1) * #(B' ∩ UW.2.1) : ℕ))|
          ≤ ∑ UW ∈ QA ×ˢ QB,
              |(#{q ∈ (A' ∩ UW.1.1) ×ˢ (B' ∩ UW.2.1) | xloc UW.1 UW.2 q = c'} : ℝ) -
                (pairColorDensity S c' A.1 B.1 : ℝ) * (#(A' ∩ UW.1.1) * #(B' ∩ UW.2.1) : ℕ)| :=
            abs_sum_le_sum_abs _ _
        _ ≤ ∑ UW ∈ QA ×ˢ QB, ((q₂ * ξ₀ + q₂ * ξ_P) * (#UW.1.1 * #UW.2.1 : ℕ) +
              if (UW.1.1, UW.2.1) ∈ S.irregularPairs ξ_P Q then
                (q₂ : ℝ) * (#UW.1.1 * #UW.2.1 : ℕ) else 0) := by
            refine sum_le_sum fun UW hUW ↦ ?_
            obtain ⟨hUQA, hWQB⟩ := mem_product.1 hUW
            have hpU : refinementParent hQP UW.1 = A :=
              (refinementParent_eq_iff hQP).2 (mem_filter.1 hUQA).2
            have hpW : refinementParent hQP UW.2 = B :=
              (refinementParent_eq_iff hQP).2 (mem_filter.1 hWQB).2
            have hpne : refinementParent hQP UW.1 ≠ refinementParent hQP UW.2 := by
              rwa [hpU, hpW]
            have hloc := hxloc_rect UW.1 UW.2 hpne (A' ∩ UW.1.1) inter_subset_right
              (B' ∩ UW.2.1) inter_subset_right c'
            rw [hpU, hpW] at hloc
            exact hloc
        _ ≤ (q₂ * ξ₀ + q₂ * ξ_P) * (#A.1 * #B.1 : ℝ) + q₂ * ξ_P * (n : ℝ) ^ 2 := by
            rw [sum_add_distrib, ← mul_sum]
            have hcast : ∑ UW ∈ QA ×ˢ QB, ((#UW.1.1 * #UW.2.1 : ℕ) : ℝ) = (#A.1 * #B.1 : ℝ) := by
              simpa [Nat.cast_mul] using hAB_sum_card
            rw [hcast]
            exact add_le_add le_rfl hirr_sum
        _ ≤ 2 * τ * (#A' * #B' : ℕ) :=
            pairFineScale_err_le_subrect hδ hG hn_le_A hn_le_B hA'size hB'size
    exact le_of_mul_le_mul_right htotal_count_dev hA'B'_pos
  rw [isRegularPair_iff]
  intro c' A' hA' B' hB' hA's hB's
  have h4τ1 : 2 * τ ≤ 1 := by linarith [pairQuarterTol_le_quarter G t]
  have hfull := hrect_dev c' Subset.rfl Subset.rfl
    (mul_le_of_le_one_left (Nat.cast_nonneg _) h4τ1)
    (mul_le_of_le_one_left (Nat.cast_nonneg _) h4τ1)
  have hsub := hrect_dev c' hA' hB'
    ((mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)).trans hA's)
    ((mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)).trans hB's)
  calc |(pairColorDensity R c' A' B' : ℝ) - pairColorDensity R c' A.1 B.1|
      ≤ |(pairColorDensity R c' A' B' : ℝ) - pairColorDensity S c' A.1 B.1| +
          |pairColorDensity S c' A.1 B.1 - (pairColorDensity R c' A.1 B.1 : ℝ)| :=
        abs_sub_le _ _ _
    _ ≤ 4 * τ := by
        rw [abs_sub_comm _ (pairColorDensity R c' A.1 B.1 : ℝ)]
        linarith

open Classical in
/-- Gluing local block recolorings across canonical coarse pairs `A < B` yields a coherent
`PairColorSystem κ V` that is `(4 * τ)`-regular on every off-diagonal pair of `P` and edits at most
`(3 / 8) * δ * |V|²` ordered distinct pairs. -/
private theorem exists_glued_offDiag_recoloring [Fintype κ] [Nonempty κ] (S : PairColorSystem κ V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (hP : P.IsEquipartition)
    {δ : ℝ} (hδ : 0 < δ) {G : ℕ → ℝ} (hG : ∀ k, 0 < G k)
    (hgap : S.energy Q - S.energy P ≤ pairEnergyGap (Fintype.card κ) δ)
    (hQreg : ∑ UV ∈ S.irregularPairs (pairFineScale (Fintype.card κ) δ G #P.parts) Q,
        (#UV.1 * #UV.2 : ℝ) ≤
      pairFineScale (Fintype.card κ) δ G #P.parts * (Fintype.card V : ℝ) ^ 2)
    (hU_large : ∀ U ∈ Q.parts,
      (Fintype.card κ + 3 : ℝ) ≤
        (pairFineScale (Fintype.card κ) δ G #P.parts / (Fintype.card κ + 1)) ^ 2 * #U) :
    ∃ R : PairColorSystem κ V,
      R.rev = S.rev ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B →
        R.IsRegularPair (4 * pairQuarterTol G #P.parts) A B) ∧
      (#{p | R.color p ≠ S.color p} : ℝ) ≤ (3 / 8) * δ * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set q₂ := Fintype.card κ
  set n := Fintype.card V
  set t := #P.parts
  set τ := pairQuarterTol G t
  set ξ_P := pairFineScale q₂ δ G t
  set ξ₀ := ξ_P / (q₂ + 1)
  have hξP_pos : 0 < ξ_P := pairFineScale_pos q₂ hδ hG t
  have hξ₀_pos : 0 < ξ₀ := by positivity
  let idx : P.parts ≃ Fin (Fintype.card P.parts) := Fintype.equivFin P.parts
  let parent (U : Q.parts) : P.parts := refinementParent hQP U
  let x₀ (q : V × V) : κ := if h : q.1 ≠ q.2 then S.color ⟨q, h⟩ else Classical.arbitrary κ
  choose xloc hxloc using fun U W ↦
    exists_local_block_recoloring S hQP hξP_pos hξ₀_pos hU_large x₀
      (fun q h ↦ by simp [x₀, h]) U W
  let cellP (u : V) : P.parts := ⟨P.part u, P.part_mem.2 (mem_univ u)⟩
  let cellQ (u : V) : Q.parts := ⟨Q.part u, Q.part_mem.2 (mem_univ u)⟩
  have hcellQ_parent (u : V) : parent (cellQ u) = cellP u := by
    apply Subtype.ext
    have hmem : u ∈ (parent (cellQ u)).1 :=
      le_refinementParent hQP (cellQ u) (Q.mem_part_self.2 (mem_univ u))
    exact (P.part_eq_of_mem (parent (cellQ u)).2 hmem).symm
  let R : PairColorSystem κ V :=
    { color := fun p ↦
        if idx (cellP p.1.1) < idx (cellP p.1.2) then xloc (cellQ p.1.1) (cellQ p.1.2) p.1
        else if idx (cellP p.1.2) < idx (cellP p.1.1) then
          S.rev (xloc (cellQ p.1.2) (cellQ p.1.1) p.1.swap)
        else S.color p
      rev := S.rev
      rev_involutive := S.rev_involutive
      color_rev := fun p ↦ by
        obtain ⟨⟨u, v⟩, huv⟩ := p
        dsimp only [Prod.fst_swap, Prod.snd_swap, Prod.swap_prod_mk]
        rcases lt_trichotomy (idx (cellP u)) (idx (cellP v)) with hlt | heq | hgt
        · have hnot : ¬idx (cellP v) < idx (cellP u) := lt_asymm hlt
          simp [hlt, hnot]
        · simp only [heq, lt_irrefl, ↓reduceIte]
          exact S.color_rev ⟨(u, v), huv⟩
        · have hnot : ¬idx (cellP u) < idx (cellP v) := lt_asymm hgt
          simp [hgt, hnot, S.rev_involutive (xloc (cellQ v) (cellQ u) (v, u))] }
  have hR_reg_lt (A B : P.parts) (hAB_lt : idx A < idx B) : R.IsRegularPair (4 * τ) A.1 B.1 := by
    refine glued_isRegularPair_of_ne S R hQP hP hδ hG hQreg xloc
      (fun U W hne ↦ (hxloc U W hne).2) (fun h ↦ (ne_of_lt hAB_lt) (congrArg idx h))
      fun p huA hvB ↦ ?_
    have hcP1 : cellP p.1.1 = A := Subtype.ext (P.part_eq_of_mem A.2 huA)
    have hcP2 : cellP p.1.2 = B := Subtype.ext (P.part_eq_of_mem B.2 hvB)
    simp [R, hcP1, hcP2, hAB_lt, cellQ]
  have hR_reg (A : Finset V) (hA : A ∈ P.parts) (B : Finset V) (hB : B ∈ P.parts)
      (hAB : A ≠ B) : R.IsRegularPair (4 * τ) A B := by
    have hne : idx ⟨A, hA⟩ ≠ idx ⟨B, hB⟩ := fun h ↦
      hAB (congrArg Subtype.val (idx.injective h))
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hR_reg_lt ⟨A, hA⟩ ⟨B, hB⟩ hlt
    · exact (hR_reg_lt ⟨B, hB⟩ ⟨A, hA⟩ hgt).symm
  -- Bound the off-diagonal edited pairs of `R`.
  have hR_edits : (#{p | R.color p ≠ S.color p} : ℝ) ≤ (3 / 8) * δ * (n : ℝ) ^ 2 := by
    let Elt : Finset {p : V × V // p.1 ≠ p.2} :=
      univ.filter fun p ↦ idx (cellP p.1.1) < idx (cellP p.1.2) ∧ R.color p ≠ S.color p
    let Egt : Finset {p : V × V // p.1 ≠ p.2} :=
      univ.filter fun p ↦ idx (cellP p.1.2) < idx (cellP p.1.1) ∧ R.color p ≠ S.color p
    have hsplit : (univ.filter fun p ↦ R.color p ≠ S.color p) ⊆ Elt ∪ Egt := by
      intro p hp
      have hne := (mem_filter.1 hp).2
      rcases lt_trichotomy (idx (cellP p.1.1)) (idx (cellP p.1.2)) with hlt | heq | hgt
      · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hlt, hne⟩)
      · exfalso
        apply hne
        simp [R, heq]
      · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, hgt, hne⟩)
    have hEgt_eq : #Egt = #Elt := by
      refine card_bij (fun p _ ↦ ⟨p.1.swap, p.2.symm⟩) (fun p hp ↦ ?_)
        (fun p₁ _ p₂ _ h ↦ Subtype.ext (Prod.swap_injective (Subtype.mk.inj h)))
        (fun p hp ↦ ⟨⟨p.1.swap, p.2.symm⟩, ?_, Subtype.ext (Prod.swap_swap p.1)⟩)
      · obtain ⟨-, hgt, hne⟩ := mem_filter.1 hp
        refine mem_filter.2 ⟨mem_univ _, hgt, fun heq ↦ hne ?_⟩
        have hnot : ¬idx (cellP p.1.1) < idx (cellP p.1.2) := lt_asymm hgt
        simp only [R, Prod.fst_swap, Prod.snd_swap, hgt, hnot, ↓reduceIte] at heq ⊢
        rw [heq, S.color_rev, S.rev_involutive]
      · obtain ⟨-, hlt, hne⟩ := mem_filter.1 hp
        refine mem_filter.2 ⟨mem_univ _, hlt, fun heq ↦ hne ?_⟩
        have hnot : ¬idx (cellP p.1.2) < idx (cellP p.1.1) := lt_asymm hlt
        simp only [R, Prod.fst_swap, Prod.snd_swap, hlt, hnot, ↓reduceIte] at heq ⊢
        have := congrArg S.rev heq
        simpa [S.rev_involutive, S.color_rev] using this
    let Fpairs : Finset (Q.parts × Q.parts) :=
      univ.filter fun UW ↦ idx (parent UW.1) < idx (parent UW.2)
    have hElt_le : #Elt ≤ ∑ UW ∈ Fpairs, #{q ∈ UW.1.1 ×ˢ UW.2.1 | xloc UW.1 UW.2 q ≠ x₀ q} := by
      have hinj : Function.Injective (Subtype.val : {p : V × V // p.1 ≠ p.2} → V × V) :=
        Subtype.val_injective
      have himg_sub : Elt.image Subtype.val ⊆
          Fpairs.biUnion (fun UW ↦ {q ∈ UW.1.1 ×ˢ UW.2.1 | xloc UW.1 UW.2 q ≠ x₀ q}) := by
        intro q hq
        obtain ⟨p, hp, rfl⟩ := mem_image.1 hq
        obtain ⟨-, hlt, hne⟩ := mem_filter.1 hp
        have hp1 : parent (cellQ p.1.1) = cellP p.1.1 := hcellQ_parent p.1.1
        have hp2 : parent (cellQ p.1.2) = cellP p.1.2 := hcellQ_parent p.1.2
        refine mem_biUnion.2 ⟨(cellQ p.1.1, cellQ p.1.2),
          mem_filter.2 ⟨mem_univ _, by rwa [hp1, hp2]⟩, ?_⟩
        refine mem_filter.2 ⟨mem_product.2 ⟨Q.mem_part_self.2 (mem_univ _),
          Q.mem_part_self.2 (mem_univ _)⟩, ?_⟩
        simpa [R, hlt, x₀, p.2] using hne
      calc #Elt = #(Elt.image Subtype.val) := (card_image_of_injective Elt hinj).symm
        _ ≤ #(Fpairs.biUnion fun UW ↦ {q ∈ UW.1.1 ×ˢ UW.2.1 | xloc UW.1 UW.2 q ≠ x₀ q}) :=
          card_le_card himg_sub
        _ ≤ _ := card_biUnion_le
    have hFpairs_sum :
        2 * (∑ UW ∈ Fpairs, (#{q ∈ UW.1.1 ×ˢ UW.2.1 | xloc UW.1 UW.2 q ≠ x₀ q} : ℝ)) ≤
          (∑ c, ∑ p ∈ (univ : Finset V).offDiag,
            |(pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
              pairColorDensity S c (P.part p.1) (P.part p.2)|) +
          2 * q₂ * ξ₀ * (n : ℝ) ^ 2 := by
      have hterm_le :
          2 * (∑ UW ∈ Fpairs, (#{q ∈ UW.1.1 ×ˢ UW.2.1 | xloc UW.1 UW.2 q ≠ x₀ q} : ℝ)) ≤
            (∑ UW ∈ Fpairs, ∑ c, |(pairColorDensity S c UW.1.1 UW.2.1 : ℝ) -
                pairColorDensity S c (parent UW.1).1 (parent UW.2).1| * (#UW.1.1 * #UW.2.1 : ℕ)) +
              2 * q₂ * ξ₀ * ∑ UW ∈ Fpairs, ((#UW.1.1 * #UW.2.1 : ℕ) : ℝ) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_le_sum fun UW hUW ↦ ?_
        have hlt := (mem_filter.1 hUW).2
        have hne_par : parent UW.1 ≠ parent UW.2 := fun h ↦ (ne_of_lt hlt) (congrArg idx h)
        have hed := (hxloc UW.1 UW.2 hne_par).1
        dsimp only [parent]
        rw [← sum_mul]
        linarith
      have hblock_disj : (Fpairs : Set (Q.parts × Q.parts)).PairwiseDisjoint
          (fun UW ↦ UW.1.1 ×ˢ UW.2.1) := by
        intro UW₁ _ UW₂ _ hne
        refine disjoint_product.2 ?_
        by_cases hfst : UW₁.1 = UW₂.1
        · have hsnd : UW₁.2 ≠ UW₂.2 := fun hs ↦ hne (Prod.ext hfst hs)
          exact Or.inr (Q.disjoint UW₁.2.2 UW₂.2.2 fun heq ↦ hsnd (Subtype.ext heq))
        · exact Or.inl (Q.disjoint UW₁.1.2 UW₂.1.2 fun heq ↦ hfst (Subtype.ext heq))
      have hblock_offDiag : Fpairs.biUnion (fun UW ↦ UW.1.1 ×ˢ UW.2.1) ⊆
          (univ : Finset V).offDiag := by
        intro q hq
        obtain ⟨UW, hUW, hqUW⟩ := mem_biUnion.1 hq
        have hlt := (mem_filter.1 hUW).2
        have hdisj : Disjoint (parent UW.1).1 (parent UW.2).1 :=
          P.disjoint (parent UW.1).2 (parent UW.2).2 fun heq ↦
            (ne_of_lt hlt) (congrArg idx (Subtype.ext heq))
        have hdisjUW : Disjoint UW.1.1 UW.2.1 :=
          hdisj.mono (le_refinementParent hQP UW.1) (le_refinementParent hQP UW.2)
        have hne_q : q.1 ≠ q.2 :=
          hdisjUW.forall_ne_finset (mem_product.1 hqUW).1 (mem_product.1 hqUW).2
        exact mem_offDiag.2 ⟨mem_univ _, mem_univ _, hne_q⟩
      have hsum_card_le : ∑ UW ∈ Fpairs, ((#UW.1.1 * #UW.2.1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
        rw [← Nat.cast_sum]
        have h1 : ∑ UW ∈ Fpairs, (#UW.1.1 * #UW.2.1) =
            #(Fpairs.biUnion fun UW ↦ UW.1.1 ×ˢ UW.2.1) := by
          rw [card_biUnion hblock_disj]
          simp [card_product]
        have h2 : #(Fpairs.biUnion fun UW ↦ UW.1.1 ×ˢ UW.2.1) ≤ n ^ 2 := by
          calc _ ≤ #(univ : Finset (V × V)) := card_le_card (subset_univ _)
            _ = n ^ 2 := by rw [card_univ, Fintype.card_prod, ← sq]
        exact_mod_cast h1.trans_le h2
      have hsum_dev_le :
          ∑ UW ∈ Fpairs, ∑ c, |(pairColorDensity S c UW.1.1 UW.2.1 : ℝ) -
              pairColorDensity S c (parent UW.1).1 (parent UW.2).1| * (#UW.1.1 * #UW.2.1 : ℕ) ≤
            ∑ c, ∑ p ∈ (univ : Finset V).offDiag,
              |(pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
                pairColorDensity S c (P.part p.1) (P.part p.2)| := by
        rw [sum_comm]
        refine sum_le_sum fun c _ ↦ ?_
        have hpoint (UW : Q.parts × Q.parts) :
            |(pairColorDensity S c UW.1.1 UW.2.1 : ℝ) -
                pairColorDensity S c (parent UW.1).1 (parent UW.2).1| *
              (#UW.1.1 * #UW.2.1 : ℕ) =
            ∑ p ∈ UW.1.1 ×ˢ UW.2.1,
              |(pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
                pairColorDensity S c (P.part p.1) (P.part p.2)| := by
          have hcongr : ∑ p ∈ UW.1.1 ×ˢ UW.2.1,
              |(pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
                pairColorDensity S c (P.part p.1) (P.part p.2)| =
              ∑ _p ∈ UW.1.1 ×ˢ UW.2.1,
                |(pairColorDensity S c UW.1.1 UW.2.1 : ℝ) -
                  pairColorDensity S c (parent UW.1).1 (parent UW.2).1| := by
            refine sum_congr rfl fun p hp ↦ ?_
            obtain ⟨hp1, hp2⟩ := mem_product.1 hp
            have hQ1 : Q.part p.1 = UW.1.1 := Q.part_eq_of_mem UW.1.2 hp1
            have hQ2 : Q.part p.2 = UW.2.1 := Q.part_eq_of_mem UW.2.2 hp2
            have hP1 : P.part p.1 = (parent UW.1).1 :=
              P.part_eq_of_mem (parent UW.1).2 (le_refinementParent hQP UW.1 hp1)
            have hP2 : P.part p.2 = (parent UW.2).1 :=
              P.part_eq_of_mem (parent UW.2).2 (le_refinementParent hQP UW.2 hp2)
            rw [hQ1, hQ2, hP1, hP2]
          rw [hcongr, sum_const, card_product, nsmul_eq_mul, mul_comm]
        simp_rw [hpoint]
        rw [← sum_biUnion hblock_disj]
        exact sum_le_sum_of_subset_of_nonneg hblock_offDiag fun _ _ _ ↦ abs_nonneg _
      have hmul_card : 2 * (q₂ : ℝ) * ξ₀ * ∑ UW ∈ Fpairs, ((#UW.1.1 * #UW.2.1 : ℕ) : ℝ) ≤
          2 * q₂ * ξ₀ * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsum_card_le (by positivity)
      linarith
    have hcs_sum :
        ∑ c, ∑ p ∈ (univ : Finset V).offDiag,
            |(pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
              pairColorDensity S c (P.part p.1) (P.part p.2)| ≤
          (δ / 8) * (n : ℝ) ^ 2 := by
      have hsqrt : √(pairEnergyGap q₂ δ) = min δ 1 / (8 * (q₂ + 1)) := by
        unfold pairEnergyGap
        have : 0 ≤ min δ 1 := le_min hδ.le zero_le_one
        exact sqrt_sq (by positivity)
      calc _ ≤ ∑ _c : κ, √(pairEnergyGap q₂ δ) * (n : ℝ) ^ 2 :=
            sum_le_sum fun c _ ↦ S.sum_abs_pairColorDensity_sub_le hQP hgap c
        _ = q₂ * (min δ 1 / (8 * (q₂ + 1))) * (n : ℝ) ^ 2 := by
            rw [sum_const, card_univ, nsmul_eq_mul, hsqrt, mul_assoc]
        _ ≤ (δ / 8) * (n : ℝ) ^ 2 := by
            refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            have hm : min δ 1 ≤ δ := min_le_left _ _
            rw [mul_div_left_comm]
            have hfrac : (q₂ : ℝ) / (8 * (q₂ + 1)) ≤ 1 / 8 := by
              rw [div_le_div_iff₀ (by positivity) (by norm_num)]
              linarith
            have hm0 : 0 ≤ min δ 1 := le_min hδ.le zero_le_one
            calc min δ 1 * ((q₂ : ℝ) / (8 * (q₂ + 1))) ≤ min δ 1 * (1 / 8) :=
                  mul_le_mul_of_nonneg_left hfrac hm0
              _ ≤ δ * (1 / 8) := mul_le_mul_of_nonneg_right hm (by norm_num)
              _ = δ / 8 := by ring
    have hξ₀_term : 2 * (q₂ : ℝ) * ξ₀ * (n : ℝ) ^ 2 ≤ (δ / 4) * (n : ℝ) ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have hqξ₀ : (q₂ : ℝ) * ξ₀ ≤ ξ_P := by
        dsimp [ξ₀]
        rw [mul_div_left_comm]
        refine mul_le_of_le_one_right hξP_pos.le (div_le_one_of_le₀ ?_ (by positivity))
        linarith
      have hξ_δ : ξ_P ≤ δ / 8 := by
        have h1 : ξ_P ≤ min δ 1 / (8 * (q₂ + 1)) := by
          dsimp only [ξ_P, pairFineScale]
          exact min_le_left _ _
        have h2 : min δ 1 / (8 * (q₂ + 1)) ≤ δ / 8 := by
          calc min δ 1 / (8 * (q₂ + 1)) ≤ δ / (8 * (q₂ + 1)) :=
                div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)
            _ ≤ δ / 8 := div_le_div_of_nonneg_left hδ.le (by norm_num)
                  (by linarith [Nat.cast_nonneg (α := ℝ) q₂])
        exact h1.trans h2
      linarith
    have hcard_tot : #(univ.filter fun p ↦ R.color p ≠ S.color p) ≤ 2 * #Elt := by
      calc _ ≤ #(Elt ∪ Egt) := card_le_card hsplit
        _ ≤ #Elt + #Egt := card_union_le _ _
        _ = 2 * #Elt := by rw [hEgt_eq, two_mul]
    have hElt_R : 2 * (#Elt : ℝ) ≤ (3 / 8) * δ * (n : ℝ) ^ 2 := by
      have h1 : 2 * (#Elt : ℝ) ≤
          2 * (∑ UW ∈ Fpairs, (#{q ∈ UW.1.1 ×ˢ UW.2.1 | xloc UW.1 UW.2 q ≠ x₀ q} : ℝ)) := by
        rw [← Nat.cast_sum]
        exact_mod_cast Nat.mul_le_mul_left 2 hElt_le
      linarith
    exact (by exact_mod_cast hcard_tot :
      (#{p | R.color p ≠ S.color p} : ℝ) ≤ 2 * #Elt).trans hElt_R
  exact ⟨R, rfl, hR_reg, hR_edits⟩

open Classical in
/-- **Strong regular approximation of a pair-color system.** Let `S` be a pair-color system on `V`
with finite palette `κ`, let `P₀` be an equipartition of `V` with `8 ≤ δ * #P₀.parts`, let `δ > 0`,
and let `G : ℕ → ℝ` be a positive regularity schedule. If
`strongPairColorHostBound (card κ) δ G #P₀.parts ≤ card V`, then there exist a refining
equipartition `P ≤ P₀` and a pair-color system `T` on `Option κ` such that:

* `#P.parts ≤ strongPairColorPartBound (card κ) δ G #P₀.parts`;
* `(⟨P, T⟩ : PairSkeleton3 (Option κ) V).IsPairColorRegular (G #P.parts)`;
* `T` disagrees with `some ∘ S` on at most `δ * |V|²` ordered distinct pairs. -/
theorem exists_strong_recoloring_isPairColorRegular [Fintype κ] (S : PairColorSystem κ V)
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {δ : ℝ} (hδ : 0 < δ)
    (hl₀ : 8 ≤ δ * #P₀.parts) {G : ℕ → ℝ} (hG : ∀ k, 0 < G k)
    (hV : strongPairColorHostBound (Fintype.card κ) δ G #P₀.parts ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem (Option κ) V),
      P ≤ P₀ ∧ P.IsEquipartition ∧
      #P.parts ≤ strongPairColorPartBound (Fintype.card κ) δ G #P₀.parts ∧
      T.rev = Option.map S.rev ∧
      (⟨P, T⟩ : PairSkeleton3 (Option κ) V).IsPairColorRegular (G #P.parts) ∧
      (#{p | T.color p ≠ some (S.color p)} : ℝ) ≤
        δ * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set q₂ := Fintype.card κ
  set n := Fintype.card V
  have hn2 : 2 ≤ n := (le_max_left 2 ⌈8 / δ⌉₊).trans ((le_max_left _ _).trans hV)
  have hceil_n : ⌈8 / δ⌉₊ ≤ n := (le_max_right 2 ⌈8 / δ⌉₊).trans ((le_max_left _ _).trans hV)
  have h8n : (8 : ℝ) ≤ δ * n := by
    have hc : 8 / δ ≤ ⌈8 / δ⌉₊ := Nat.le_ceil _
    have hc' : (⌈8 / δ⌉₊ : ℝ) ≤ n := by exact_mod_cast hceil_n
    exact (div_le_iff₀' hδ).1 (hc.trans hc')
  have : Nonempty κ := by
    have hcard_one_lt : 1 < #(univ : Finset V) := by rw [card_univ]; omega
    obtain ⟨u, -, v, -, huv⟩ := one_lt_card.1 hcard_one_lt
    exact ⟨S.color ⟨(u, v), huv⟩⟩
  obtain ⟨P, Q, hQP, hPP₀, hP, hQ, hPbound, hQbound, hgap, hQreg⟩ :=
    S.exists_strong_pairColor_witness P₀ hP₀ hδ hG
  have hU_large (U : Finset V) (hU : U ∈ Q.parts) :
      (q₂ + 3 : ℝ) ≤ (pairFineScale q₂ δ G #P.parts / (q₂ + 1)) ^ 2 * #U :=
    fine_part_card_bound hQ hPbound hQbound hδ hG hV hU
  obtain ⟨R, hR_rev, hR_reg, hR_edits⟩ :=
    S.exists_glued_offDiag_recoloring hQP hP hδ hG hgap hQreg hU_large
  set t := #P.parts
  set τ := pairQuarterTol G t
  set ξ_P := pairFineScale q₂ δ G t
  set ξ₀ := ξ_P / (q₂ + 1)
  have hτ_pos : 0 < τ := pairQuarterTol_pos hG t
  have hξP_pos : 0 < ξ_P := pairFineScale_pos q₂ hδ hG t
  have hξ₀_pos : 0 < ξ₀ := by positivity
  -- Fill diagonal blocks via `R.fillDiagonal P`.
  have hlarge_diag (A : Finset V) (hA : A ∈ P.parts) : 1 < 4 * τ * #A := by
    obtain ⟨u, huA⟩ := P.nonempty_of_mem_parts hA
    obtain ⟨U, hUQ, huU⟩ := Q.exists_mem (mem_univ u)
    obtain ⟨A', hA', hUA'⟩ := hQP hUQ
    have hA'_eq : A' = A := P.eq_of_mem_parts hA' hA (hUA' huU) huA
    rw [hA'_eq] at hUA'
    have hUA : (#U : ℝ) ≤ #A := by exact_mod_cast card_le_card hUA'
    have hU3 := hU_large U hUQ
    have hξ₀_le_4τ : ξ₀ ^ 2 ≤ 4 * τ := by
      have hξP_le : ξ_P ≤ τ ^ 3 := by
        have h1 : ξ_P ≤ τ ^ 3 / (16 * (q₂ + 1 : ℝ) * ((t : ℝ) + 1) ^ 2) := by
          dsimp only [ξ_P, pairFineScale]
          exact min_le_right _ _
        refine h1.trans (div_le_self (by positivity) ?_)
        have hpos : 0 ≤ 15 + 16 * (q₂ : ℝ) + 16 * (q₂ + 1) * (2 * (t : ℝ) + (t : ℝ) ^ 2) := by
          positivity
        linarith
      have hξ₀_le_ξP : ξ₀ ≤ ξ_P :=
        div_le_self hξP_pos.le (by linarith [Nat.cast_nonneg (α := ℝ) q₂])
      have hτ1 : τ ≤ 1 / 4 := pairQuarterTol_le_quarter G t
      have hτ_pow : τ ^ 3 ≤ τ := by
        calc τ ^ 3 = τ ^ 2 * τ := by ring
          _ ≤ 1 * τ := mul_le_mul_of_nonneg_right (pow_le_one₀ hτ_pos.le (by linarith)) hτ_pos.le
          _ = τ := one_mul _
      have hξ₀_le_τ : ξ₀ ≤ 2 * τ := by linarith
      calc ξ₀ ^ 2 ≤ (2 * τ) ^ 2 := pow_le_pow_left₀ hξ₀_pos.le hξ₀_le_τ 2
        _ = 4 * τ * τ := by ring
        _ ≤ 4 * τ * 1 := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = 4 * τ := mul_one _
    calc (1 : ℝ) < q₂ + 3 := by linarith [Nat.cast_nonneg (α := ℝ) q₂]
      _ ≤ ξ₀ ^ 2 * #U := hU3
      _ ≤ (4 * τ) * #A := mul_le_mul hξ₀_le_4τ hUA (Nat.cast_nonneg _) (by positivity)
  have hT_reg4τ : (⟨P, R.fillDiagonal P⟩ : PairSkeleton3 (Option κ) V).IsPairColorRegular (4 * τ) :=
    R.isPairColorRegular_fillDiagonal P hlarge_diag hR_reg
  have hT_regG :
      (⟨P, R.fillDiagonal P⟩ : PairSkeleton3 (Option κ) V).IsPairColorRegular (G t) :=
    hT_reg4τ.mono (four_mul_pairQuarterTol_le G t)
  let E_off : Finset {p : V × V // p.1 ≠ p.2} := univ.filter fun p ↦ R.color p ≠ S.color p
  let E_diag : Finset {p : V × V // p.1 ≠ p.2} :=
    univ.filter fun p ↦ (R.fillDiagonal P).color p ≠ some (R.color p)
  let E_tot : Finset {p : V × V // p.1 ≠ p.2} :=
    univ.filter fun p ↦ (R.fillDiagonal P).color p ≠ some (S.color p)
  have hdiag_edits : (#E_diag : ℝ) ≤ (δ / 4) * (n : ℝ) ^ 2 := by
    have hinj : Function.Injective (Subtype.val : {p : V × V // p.1 ≠ p.2} → V × V) :=
      Subtype.val_injective
    have himg : E_diag.image Subtype.val ⊆
        (univ : Finset (V × V)).filter fun p ↦
          (R.fillDiagonal P).colorOfPair p.1 p.2 ≠ (R.colorOfPair p.1 p.2).map some := by
      intro q hq
      obtain ⟨p, hp, rfl⟩ := mem_image.1 hq
      have hne := (mem_filter.1 hp).2
      refine mem_filter.2 ⟨mem_univ _, ?_⟩
      rw [(R.fillDiagonal P).colorOfPair_of_ne p.2, R.colorOfPair_of_ne p.2]
      simpa using hne
    have hcard_le : #E_diag ≤ (n / t + 1) * n := by
      have hmA (A : Finset V) (hA : A ∈ P.parts) : #A ≤ n / t + 1 := by
        simpa [card_univ, n, t] using hP.card_part_le_average_add_one hA
      calc #E_diag = #(E_diag.image Subtype.val) := (card_image_of_injective _ hinj).symm
        _ ≤ #((univ : Finset (V × V)).filter fun p ↦
              (R.fillDiagonal P).colorOfPair p.1 p.2 ≠ (R.colorOfPair p.1 p.2).map some) :=
            card_le_card himg
        _ ≤ (n / t + 1) * n := R.card_fillDiagonal_colorOfPair_ne_le_of_card_le P hmA
    have ht_ge_l₀ : #P₀.parts ≤ t := card_mono hPP₀
    have h8t : (8 : ℝ) ≤ δ * t := hl₀.trans (mul_le_mul_of_nonneg_left
      (by exact_mod_cast ht_ge_l₀) hδ.le)
    have ht_pos : (0 : ℝ) < t := by
      by_contra! hle
      have : δ * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hδ.le hle
      linarith
    have hdiv_le : ((n / t : ℕ) : ℝ) ≤ (δ / 8) * n := by
      have h1 : ((n / t : ℕ) : ℝ) * t ≤ n := by exact_mod_cast Nat.div_mul_le_self n t
      have h2 : (8 : ℝ) * ((n / t : ℕ) : ℝ) * t ≤ δ * t * n := by
        calc (8 : ℝ) * ((n / t : ℕ) : ℝ) * t = 8 * (((n / t : ℕ) : ℝ) * t) := by ring
          _ ≤ 8 * n := mul_le_mul_of_nonneg_left h1 (by norm_num)
          _ ≤ (δ * t) * n := mul_le_mul_of_nonneg_right h8t (Nat.cast_nonneg _)
      have h3 : (8 : ℝ) * ((n / t : ℕ) : ℝ) ≤ δ * n :=
        le_of_mul_le_mul_right (by linarith : ((8 : ℝ) * ((n / t : ℕ) : ℝ)) * t ≤ (δ * n) * t)
          ht_pos
      linarith
    have hone_le : (1 : ℝ) ≤ (δ / 8) * n := by linarith
    calc (#E_diag : ℝ)
        ≤ ((n / t + 1 : ℕ) : ℝ) * n := by exact_mod_cast hcard_le
      _ = (((n / t : ℕ) : ℝ) + 1) * n := by push_cast; ring
      _ ≤ ((δ / 8) * n + (δ / 8) * n) * n :=
          mul_le_mul_of_nonneg_right (add_le_add hdiv_le hone_le) (Nat.cast_nonneg _)
      _ = (δ / 4) * (n : ℝ) ^ 2 := by ring
  refine ⟨P, R.fillDiagonal P, hPP₀, hP, hPbound,
    funext (fun c ↦ (R.fillDiagonal_rev P c).trans (by rw [hR_rev])), hT_regG, ?_⟩
  have htot_sub : E_tot ⊆ E_off ∪ E_diag := by
    intro p hp
    have hne := (mem_filter.1 hp).2
    by_cases hRS : R.color p = S.color p
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, by rwa [hRS]⟩)
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hRS⟩)
  have htot_card : (#E_tot : ℝ) ≤ (#E_off : ℝ) + (#E_diag : ℝ) := by
    exact_mod_cast (card_le_card htot_sub).trans (card_union_le _ _)
  have hR_edits' : (#E_off : ℝ) ≤ (3 / 8) * δ * (n : ℝ) ^ 2 := hR_edits
  change (#E_tot : ℝ) ≤ δ * (n : ℝ) ^ 2
  linarith [htot_card, hR_edits', hdiag_edits, mul_nonneg hδ.le (sq_nonneg (n : ℝ))]

end PairColorSystem

end TauCeti
