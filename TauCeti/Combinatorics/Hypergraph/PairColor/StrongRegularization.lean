/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.SeededRegularization
public import TauCeti.Order.Partition.Finpartition
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import TauCeti.Algebra.BigOperators.Finset.WeightedCauchySchwarz
import TauCeti.Data.Finset.Basic

/-!
# Strong pair-color regularity and fine-to-coarse discrepancy

In Szemerédi's regularity lemma, the tolerance `ε` is fixed in advance and the number of cells
grows as a tower in `1 / ε`. When a schedule `Φ : ℕ → ℝ` asks for regularity at a parameter
`Φ #P.parts` that shrinks with the number of coarse cells, a single regularization pass cannot keep
up with its own cell count. Iterating
`PairColorSystem.exists_refining_equipartition_sum_irregularPairs_le` instead produces a pair of
nested equipartitions `Q ≤ P ≤ P₀` such that:

* `Q` is `Φ #P.parts`-regular for `S` outside at most `Φ #P.parts |V|²` ordered vertex pairs;
* the pair-color energy gap `S.energy Q - S.energy P` is at most `g` (`> 0`).

Because `S.energy` takes values in `[0, 1]` and is monotone under refinement, at most `⌊1 / g⌋ + 1`
jumps can exceed `g`, bounding both `#P.parts` and `#Q.parts` in terms of `g`, `Φ`, and `#P₀.parts`
(`TauCeti.strongPairColorRegularityBound`).

We also record the two bridges that turn `(P, Q)` into a regular approximation on the coarse
partition `P`:

1. **Energy gap controls `L¹` density drift**
   (`PairColorSystem.sum_abs_pairColorDensity_sub_mul_card_le`): by weighted Cauchy–Schwarz
   (`Finset.weighted_sum_abs_le_sqrt`) applied to the refinement defect identity,
   `S.energy Q - S.energy P ≤ g` bounds the size-weighted `L¹` drift between the fine densities on
   `Q` and their coarse parent densities on `P` by `√(card κ · g) |V|²`.
2. **Fine rectangle discrepancy aggregates to coarse regularity**
   (`PairColorSystem.abs_card_filter_colorOfPair_sub_le_of_refines` and
   `PairColorSystem.isRegularPair_of_abs_card_filter_colorOfPair_sub_le`): if a pair-color system
   matches a target distribution `p` with small rectangle discrepancy on all regular fine subblocks
   of `A ×ˢ C`, then `(A, C)` has small rectangle discrepancy against `p` up to the mass of bad
   fine subblocks, and small rectangle discrepancy implies `PairColorSystem.IsRegularPair`.

## Main definitions

* `TauCeti.strongPairColorRegularityStep`: monotone envelope of one seeded equitable regularization
  step at schedule `Φ`.
* `TauCeti.strongPairColorRegularityBound`: upper bound on the number of parts in the strong
  pair-color regularity lemma.

## Main results

* `TauCeti.PairColorSystem.sum_abs_pairColorDensity_sub_le` and
  `TauCeti.PairColorSystem.sum_abs_pairColorDensity_sub_mul_card_le`: `L¹` density drift between a
  refinement `Q ≤ P` and `P` in terms of the energy gap.
* `TauCeti.PairColorSystem.isRegularPair_of_abs_card_filter_colorOfPair_sub_le`: uniform rectangle
  discrepancy against a reference vector implies `IsRegularPair`.
* `TauCeti.PairColorSystem.abs_card_filter_colorOfPair_sub_le_of_refines`: coarse rectangle
  discrepancy bounded by fine rectangle discrepancy plus bad-child mass.
* `TauCeti.PairColorSystem.exists_strong_refining_equipartition`: strong pair-color regularity
  producing `Q ≤ P ≤ P₀` with small energy gap and `Φ #P.parts`-regular fine partition `Q`.

## References

* N. Alon, E. Fischer, M. Krivelevich, and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), 451–476 (strong regularity via iterated Szemerédi steps).
* T. Tao, *Szemerédi's regularity lemma revisited*, Contrib. Discrete Math. 1 (2006), the
  energy-gap stopping argument.
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
-/

public section

open Finset Finpartition Real

namespace TauCeti

/-- Monotone envelope of one seeded equitable regularization step at schedule `Φ`: starting from at
most `k` coarse parts, the fine partition has at most `strongPairColorRegularityStep Φ k` parts.
Taking the supremum over `m ≤ k` makes the step function monotone without requiring `Φ` to be
antitone. -/
noncomputable def strongPairColorRegularityStep (Φ : ℕ → ℝ) (k : ℕ) : ℕ :=
  (Iic k).sup fun m ↦ equitablePairColorRegularityBound (Φ m) m

/-- Unfolding lemma for `TauCeti.strongPairColorRegularityStep`. -/
theorem strongPairColorRegularityStep_def (Φ : ℕ → ℝ) (k : ℕ) :
    strongPairColorRegularityStep Φ k =
      (Iic k).sup fun m ↦ equitablePairColorRegularityBound (Φ m) m :=
  (rfl)

/-- `strongPairColorRegularityStep Φ` is monotone for every schedule `Φ`. -/
theorem monotone_strongPairColorRegularityStep (Φ : ℕ → ℝ) :
    Monotone (strongPairColorRegularityStep Φ) := fun _ _ hab ↦
  Finset.sup_mono (Iic_subset_Iic.2 hab)

/-- `strongPairColorRegularityStep Φ k` dominates `equitablePairColorRegularityBound (Φ k) k`. -/
theorem equitablePairColorRegularityBound_le_strongPairColorRegularityStep (Φ : ℕ → ℝ) (k : ℕ) :
    equitablePairColorRegularityBound (Φ k) k ≤ strongPairColorRegularityStep Φ k :=
  le_sup (f := fun m ↦ equitablePairColorRegularityBound (Φ m) m) (mem_Iic.2 le_rfl)

/-- One step of `strongPairColorRegularityStep` does not decrease the number of parts when
`0 < Φ k`. -/
theorem le_strongPairColorRegularityStep {Φ : ℕ → ℝ} {k : ℕ} (h : 0 < Φ k) :
    k ≤ strongPairColorRegularityStep Φ k := by
  refine (le_max_left k 1).trans ((?_ : max k 1 ≤ equitablePairColorRegularityBound (Φ k) k).trans
    (equitablePairColorRegularityBound_le_strongPairColorRegularityStep Φ k))
  rw [equitablePairColorRegularityBound_def]
  exact Function.monotone_iterate_of_id_le (le_ceil_mul_mul_four_pow_sq h) (Nat.zero_le _) _

/-- Upper bound on the number of parts produced by the strong pair-color regularity lemma with
energy-gap tolerance `g` and schedule `Φ`, starting from `k₀` parts. -/
noncomputable def strongPairColorRegularityBound (g : ℝ) (Φ : ℕ → ℝ) (k₀ : ℕ) : ℕ :=
  (strongPairColorRegularityStep Φ)^[⌊1 / g⌋₊ + 1] k₀

/-- Unfolding lemma for `TauCeti.strongPairColorRegularityBound`. -/
theorem strongPairColorRegularityBound_def (g : ℝ) (Φ : ℕ → ℝ) (k₀ : ℕ) :
    strongPairColorRegularityBound g Φ k₀ =
      (strongPairColorRegularityStep Φ)^[⌊1 / g⌋₊ + 1] k₀ :=
  (rfl)

/-- `strongPairColorRegularityBound g Φ` is monotone in the initial number of parts. -/
theorem monotone_strongPairColorRegularityBound (g : ℝ) (Φ : ℕ → ℝ) :
    Monotone (strongPairColorRegularityBound g Φ) :=
  (monotone_strongPairColorRegularityStep Φ).iterate _

/-- `strongPairColorRegularityBound g Φ k₀` is at least `k₀` when `Φ` is positive. -/
theorem le_strongPairColorRegularityBound (g : ℝ) {Φ : ℕ → ℝ} (hΦ : ∀ k, 0 < Φ k) (k₀ : ℕ) :
    k₀ ≤ strongPairColorRegularityBound g Φ k₀ :=
  Function.monotone_iterate_of_id_le (fun _ ↦ le_strongPairColorRegularityStep (hΦ _))
    (Nat.zero_le _) k₀

namespace PairColorSystem

variable {κ V : Type*}

/-! ### `L¹` density stability from small energy gap -/

section EnergyDrift

variable [Fintype κ] [Fintype V] [DecidableEq V] (S : PairColorSystem κ V)
  {P Q : Finpartition (univ : Finset V)}

/-- **Energy gap bounds `L¹` density drift.** For a refinement `Q ≤ P` with
`S.energy Q - S.energy P ≤ g`, the `L¹` palette distance between fine and coarse block densities,
summed over all ordered distinct vertex pairs, is at most `√(card κ · g) · #(univ.offDiag)`. -/
theorem sum_abs_pairColorDensity_sub_le (h : Q ≤ P) {g : ℝ} (hg : S.energy Q - S.energy P ≤ g) :
    ∑ p ∈ (univ : Finset V).offDiag, ∑ c,
        |(pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
          pairColorDensity S c (P.part p.1) (P.part p.2)| ≤
      √(Fintype.card κ * g) * #(univ : Finset V).offDiag := by
  set D := #(univ : Finset V).offDiag
  set K := Fintype.card κ
  by_cases hDK : D * K = 0
  · rcases mul_eq_zero.1 hDK with hD | hK
    · rw [card_eq_zero.1 hD, sum_empty]
      exact mul_nonneg (sqrt_nonneg _) (Nat.cast_nonneg _)
    · have : IsEmpty κ := Fintype.card_eq_zero_iff.1 hK
      simp only [univ_eq_empty, sum_empty, sum_const_zero]
      exact mul_nonneg (sqrt_nonneg _) (Nat.cast_nonneg _)
  have hDpos : (0 : ℝ) < D := Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h0 ↦ hDK (by simp [h0]))
  have hKpos : (0 : ℝ) < K := Nat.cast_pos.2 (Nat.pos_of_ne_zero fun h0 ↦ hDK (by simp [h0]))
  set M : ℝ := (D : ℝ) * K
  have hMpos : 0 < M := mul_pos hDpos hKpos
  let f : (V × V) × κ → ℝ := fun pc ↦
    (pairColorDensity S pc.2 (Q.part pc.1.1) (Q.part pc.1.2) : ℝ) -
      pairColorDensity S pc.2 (P.part pc.1.1) (P.part pc.1.2)
  have hw1 : ∑ _pc ∈ (univ : Finset V).offDiag ×ˢ (univ : Finset κ), (1 / M) ≤ 1 := by
    rw [sum_const, card_product, card_univ, nsmul_eq_mul, Nat.cast_mul,
      mul_one_div_cancel hMpos.ne']
  have hsq : ∑ pc ∈ (univ : Finset V).offDiag ×ˢ (univ : Finset κ), 1 / M * f pc ^ 2 ≤ g / K := by
    rw [← mul_sum, sum_product, one_div, inv_mul_eq_div]
    have hdef := S.sum_sq_pairColorDensity_sub_div_eq_energy_sub h
    have hrew : (∑ x ∈ (univ : Finset V).offDiag, ∑ y, f (x, y) ^ 2) / M =
        ((∑ x ∈ (univ : Finset V).offDiag, ∑ y, f (x, y) ^ 2) / D) / K := div_mul_eq_div_div _ _ _
    rw [hrew, hdef]
    exact div_le_div_of_nonneg_right hg hKpos.le
  have hcs := weighted_sum_abs_le_sqrt ((univ : Finset V).offDiag ×ˢ (univ : Finset κ))
    (fun _ ↦ 1 / M) f (fun _ _ ↦ by positivity) hw1 hsq
  rw [← mul_sum, sum_product, one_div, inv_mul_le_iff₀ hMpos] at hcs
  refine hcs.trans_eq ?_
  have hKsqrt : (K : ℝ) * √(g / K) = √(K * g) := by
    have h1 : (K : ℝ) ^ 2 * (g / K) = K * g := by field_simp
    rw [← h1, sqrt_mul (sq_nonneg _), sqrt_sq hKpos.le]
  calc M * √(g / K) = ((K : ℝ) * √(g / K)) * D := by dsimp [M]; ring
    _ = √(K * g) * D := by rw [hKsqrt]

/-- **Blockwise `L¹` density drift.** Summing the `L¹` palette distance between fine blocks of `Q`
and their coarse parents in `P` over all fine block pairs whose coarse parents are distinct gives at
most `√(card κ · g) · |V|²`. -/
theorem sum_abs_pairColorDensity_sub_mul_card_le (h : Q ≤ P) {g : ℝ}
    (hg : S.energy Q - S.energy P ≤ g) :
    ∑ BD ∈ (univ : Finset (Q.parts × Q.parts)).filter
        (fun BD ↦ refinementParent h BD.1 ≠ refinementParent h BD.2),
      (∑ c, |(pairColorDensity S c BD.1.1 BD.2.1 : ℝ) -
        pairColorDensity S c (refinementParent h BD.1).1 (refinementParent h BD.2).1|) *
          (#BD.1.1 * #BD.2.1 : ℝ) ≤
      √(Fintype.card κ * g) * (Fintype.card V : ℝ) ^ 2 := by
  classical
  set I := (univ : Finset (Q.parts × Q.parts)).filter
    fun BD ↦ refinementParent h BD.1 ≠ refinementParent h BD.2
  let T : Q.parts × Q.parts → Finset (V × V) := fun BD ↦ BD.1.1 ×ˢ BD.2.1
  let d : V × V → ℝ := fun p ↦ ∑ c,
    |(pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
      pairColorDensity S c (P.part p.1) (P.part p.2)|
  have hterm (BD : Q.parts × Q.parts) :
      (∑ c, |(pairColorDensity S c BD.1.1 BD.2.1 : ℝ) -
        pairColorDensity S c (refinementParent h BD.1).1 (refinementParent h BD.2).1|) *
          (#BD.1.1 * #BD.2.1 : ℝ) = ∑ p ∈ T BD, d p := by
    have hconst : ∀ p ∈ T BD, d p = ∑ c, |(pairColorDensity S c BD.1.1 BD.2.1 : ℝ) -
        pairColorDensity S c (refinementParent h BD.1).1 (refinementParent h BD.2).1| := by
      intro p hp
      obtain ⟨hp₁, hp₂⟩ := mem_product.1 hp
      simp only [d, Q.part_eq_of_mem BD.1.2 hp₁, Q.part_eq_of_mem BD.2.2 hp₂,
        part_eq_refinementParent h BD.1 hp₁, part_eq_refinementParent h BD.2 hp₂]
    rw [sum_congr rfl hconst, sum_const, card_product, nsmul_eq_mul, Nat.cast_mul, mul_comm]
  have hdisj : (I : Set (Q.parts × Q.parts)).PairwiseDisjoint T := by
    intro BD _ BD' _ hne
    by_cases h₁ : BD.1 = BD'.1
    · exact disjoint_product.2 (Or.inr (Q.disjoint BD.2.2 BD'.2.2
        (Subtype.coe_injective.ne fun h₂ ↦ hne (Prod.ext h₁ h₂))))
    · exact disjoint_product.2 (Or.inl (Q.disjoint BD.1.2 BD'.1.2 (Subtype.coe_injective.ne h₁)))
  have hsub : I.biUnion T ⊆ (univ : Finset V).offDiag := fun p hp ↦ by
    obtain ⟨BD, hBD, hpT⟩ := mem_biUnion.1 hp
    obtain ⟨hp₁, hp₂⟩ := mem_product.1 hpT
    have hPdisj := P.disjoint (refinementParent h BD.1).2 (refinementParent h BD.2).2
      (Subtype.coe_injective.ne (mem_filter.1 hBD).2)
    exact mem_offDiag.2 ⟨mem_univ _, mem_univ _,
      hPdisj.forall_ne_finset (le_refinementParent h BD.1 hp₁) (le_refinementParent h BD.2 hp₂)⟩
  have hoff : (#(univ : Finset V).offDiag : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    simpa [card_univ] using (Nat.cast_le (α := ℝ)).2 (card_offDiag_le_sq (univ : Finset V))
  calc ∑ BD ∈ I, _ = ∑ BD ∈ I, ∑ p ∈ T BD, d p := sum_congr rfl fun BD _ ↦ hterm BD
    _ = ∑ p ∈ I.biUnion T, d p := (sum_biUnion hdisj).symm
    _ ≤ ∑ p ∈ (univ : Finset V).offDiag, d p :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ sum_nonneg fun _ _ ↦ abs_nonneg _
    _ ≤ √(Fintype.card κ * g) * #(univ : Finset V).offDiag := S.sum_abs_pairColorDensity_sub_le h hg
    _ ≤ √(Fintype.card κ * g) * (Fintype.card V : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hoff (sqrt_nonneg _)

end EnergyDrift

/-! ### Coarse regularity from fine rectangle discrepancy -/

section CoarseRegularity

/-- **Rectangle discrepancy against a reference vector implies `IsRegularPair`.** Let `s` and `t` be
disjoint vertex sets. If for every color `c` and all `s' ⊆ s`, `t' ⊆ t` the count of color `c` on
`s' ×ˢ t'` deviates from `p c * (#s' * #t')` by at most `β * (#s * #t)`, and `2 * β ≤ ε ^ 3` with
`0 < ε`, then `(s, t)` is `ε`-regular for `R`. -/
theorem isRegularPair_of_abs_card_filter_colorOfPair_sub_le [DecidableEq κ]
    (R : PairColorSystem κ V) {s t : Finset V} (hst : Disjoint s t) {p : κ → ℝ} {β ε : ℝ}
    (hε : 0 < ε) (hβ : 2 * β ≤ ε ^ 3)
    (hdisc : ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t,
      |(#{q ∈ s' ×ˢ t' | R.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#s' * #t')| ≤
        β * (#s * #t)) :
    R.IsRegularPair ε s t := by
  classical
  obtain hε1 | hε1 := le_or_gt 1 ε
  · exact isRegularPair_of_one_le hε1
  rw [isRegularPair_iff]
  intro c s' hs' t' ht' hs's ht't
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · obtain rfl := subset_empty.1 hs'
    simp [hε.le]
  rcases t.eq_empty_or_nonempty with rfl | htne
  · obtain rfl := subset_empty.1 ht'
    simp [hε.le]
  have hs0 : (0 : ℝ) < #s := Nat.cast_pos.2 hsne.card_pos
  have ht0 : (0 : ℝ) < #t := Nat.cast_pos.2 htne.card_pos
  have hst0 : (0 : ℝ) < #s * #t := mul_pos hs0 ht0
  have hβ0 : 0 ≤ β := nonneg_of_mul_nonneg_left
    ((abs_nonneg _).trans (hdisc c ∅ (empty_subset _) ∅ (empty_subset _))) hst0
  have hsub (u v : Finset V) (hu : u ⊆ s) (hv : v ⊆ t) :
      |(pairColorDensity R c u v : ℝ) - p c| * (#u * #v) ≤ β * (#s * #t) := by
    have hc : (#{q ∈ u ×ˢ v | R.colorOfPair q.1 q.2 = some c} : ℝ) =
        pairColorDensity R c u v * (#u * #v) :=
      mod_cast (pairColorDensity_mul_card_of_disjoint R c (hst.mono hu hv)).symm
    have hd := hdisc c u hu v hv
    rwa [hc, ← sub_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ #u * #v)] at hd
  have h₁ : |(pairColorDensity R c s' t' : ℝ) - p c| * (ε ^ 2 * (#s * #t)) ≤ β * (#s * #t) :=
    calc |(pairColorDensity R c s' t' : ℝ) - p c| * (ε ^ 2 * (#s * #t))
        = |(pairColorDensity R c s' t' : ℝ) - p c| * ((ε * #s) * (ε * #t)) := by ring
      _ ≤ |(pairColorDensity R c s' t' : ℝ) - p c| * (#s' * #t') :=
          mul_le_mul_of_nonneg_left (mul_le_mul hs's ht't (by positivity) (by positivity))
            (abs_nonneg _)
      _ ≤ β * (#s * #t) := hsub s' t' hs' ht'
  have h₁' : |(pairColorDensity R c s' t' : ℝ) - p c| * ε ^ 2 ≤ β :=
    le_of_mul_le_mul_right (by simpa [mul_assoc] using h₁) hst0
  have h₂' : |(pairColorDensity R c s t : ℝ) - p c| ≤ β :=
    le_of_mul_le_mul_right (hsub s t subset_rfl subset_rfl) hst0
  have htri : |(pairColorDensity R c s' t' : ℝ) - pairColorDensity R c s t| ≤
      |(pairColorDensity R c s' t' : ℝ) - p c| + |(pairColorDensity R c s t : ℝ) - p c| := by
    simpa [abs_sub_comm (p c)] using abs_sub_le (pairColorDensity R c s' t' : ℝ) (p c)
      (pairColorDensity R c s t : ℝ)
  have hmul : |(pairColorDensity R c s' t' : ℝ) - pairColorDensity R c s t| * ε ^ 2 ≤ ε * ε ^ 2 :=
    calc |(pairColorDensity R c s' t' : ℝ) - pairColorDensity R c s t| * ε ^ 2
        ≤ |(pairColorDensity R c s' t' : ℝ) - p c| * ε ^ 2 +
            |(pairColorDensity R c s t : ℝ) - p c| * ε ^ 2 := by nlinarith [sq_pos_of_pos hε]
      _ ≤ β + β * 1 := by
          gcongr
          nlinarith [hε.le, hε1.le]
      _ ≤ ε * ε ^ 2 := by linarith
  exact le_of_mul_le_mul_right hmul (sq_pos_of_pos hε)

/-- Decompose the color count on a coarse rectangle `X ×ˢ Y ⊆ A ×ˢ C` across fine subblocks. -/
private theorem card_filter_colorOfPair_eq_sum_refines [DecidableEq κ] [Fintype V] [DecidableEq V]
    (R : PairColorSystem κ V) {P Q : Finpartition (univ : Finset V)} (h : Q ≤ P)
    {A C : P.parts} (c : κ) {X Y : Finset V} (hX : X ⊆ A.1) (hY : Y ⊆ C.1) :
    #{q ∈ X ×ˢ Y | R.colorOfPair q.1 q.2 = some c} =
      ∑ B with refinementParent h B = A, ∑ D with refinementParent h D = C,
        #{q ∈ (X ∩ B.1) ×ˢ (Y ∩ D.1) | R.colorOfPair q.1 q.2 = some c} := by
  classical
  set FA : Finset Q.parts := {B | refinementParent h B = A}
  set FC : Finset Q.parts := {D | refinementParent h D = C}
  have hXeq : X = FA.biUnion fun B ↦ X ∩ B.1 := by
    rw [← inter_biUnion, biUnion_filter_refinementParent_eq h A, inter_eq_left.2 hX]
  have hYeq : Y = FC.biUnion fun D ↦ Y ∩ D.1 := by
    rw [← inter_biUnion, biUnion_filter_refinementParent_eq h C, inter_eq_left.2 hY]
  have hrect : {q ∈ X ×ˢ Y | R.colorOfPair q.1 q.2 = some c} =
      (FA ×ˢ FC).biUnion fun BD ↦
        {q ∈ (X ∩ BD.1.1) ×ˢ (Y ∩ BD.2.1) | R.colorOfPair q.1 q.2 = some c} := by
    ext q
    simp only [mem_filter, mem_product, mem_biUnion, Prod.exists]
    constructor
    · rintro ⟨⟨hqX, hqY⟩, hqc⟩
      rw [hXeq, mem_biUnion] at hqX
      rw [hYeq, mem_biUnion] at hqY
      obtain ⟨B, hB, hqB⟩ := hqX
      obtain ⟨D, hD, hqD⟩ := hqY
      exact ⟨B, D, ⟨hB, hD⟩, ⟨hqB, hqD⟩, hqc⟩
    · rintro ⟨B, D, -, ⟨hqB, hqD⟩, hqc⟩
      exact ⟨⟨inter_subset_left hqB, inter_subset_left hqD⟩, hqc⟩
  have hdisj : ((FA ×ˢ FC : Finset (Q.parts × Q.parts)) : Set (Q.parts × Q.parts)).PairwiseDisjoint
      fun BD ↦ {q ∈ (X ∩ BD.1.1) ×ˢ (Y ∩ BD.2.1) | R.colorOfPair q.1 q.2 = some c} := by
    intro BD _ BD' _ hne
    refine disjoint_filter_filter (disjoint_product.2 ?_)
    by_cases h₁ : BD.1 = BD'.1
    · exact Or.inr ((Q.disjoint BD.2.2 BD'.2.2
        (Subtype.coe_injective.ne fun h₂ ↦ hne (Prod.ext h₁ h₂))).mono
        inter_subset_right inter_subset_right)
    · exact Or.inl ((Q.disjoint BD.1.2 BD'.1.2 (Subtype.coe_injective.ne h₁)).mono
        inter_subset_right inter_subset_right)
  rw [hrect, card_biUnion hdisj, sum_product]

/-- **Aggregating fine rectangle discrepancy to coarse cells.** Let `Q ≤ P` be partitions of `univ`
and `A, C` parts of `P`. Suppose `p : κ → ℝ` takes values in `[0, 1]`, `0 ≤ δ`, and every fine
subblock pair `(B, D)` of `(A, C)` outside `Bad` has rectangle discrepancy at most `δ * (#B * #D)`
against `p`. Then on every coarse rectangle `X ×ˢ Y ⊆ A ×ˢ C`, the count of color `c` deviates from
`p c * (#X * #Y)` by at most `δ * (#A * #C)` plus the vertex-pair mass of the pairs in `Bad` under
`(A, C)`. -/
theorem abs_card_filter_colorOfPair_sub_le_of_refines [DecidableEq κ] [Fintype V] [DecidableEq V]
    (R : PairColorSystem κ V) {P Q : Finpartition (univ : Finset V)} (h : Q ≤ P)
    {A C : P.parts} {p : κ → ℝ} (hp₀ : ∀ c, 0 ≤ p c) (hp₁ : ∀ c, p c ≤ 1)
    (Bad : Finset (Finset V × Finset V)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hgood : ∀ B D : Q.parts, refinementParent h B = A → refinementParent h D = C →
      (B.1, D.1) ∉ Bad → ∀ c, ∀ s' ⊆ B.1, ∀ t' ⊆ D.1,
        |(#{q ∈ s' ×ˢ t' | R.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#s' * #t')| ≤
          δ * (#B.1 * #D.1))
    (c : κ) {X Y : Finset V} (hX : X ⊆ A.1) (hY : Y ⊆ C.1) :
    |(#{q ∈ X ×ˢ Y | R.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#X * #Y)| ≤
      δ * (#A.1 * #C.1) +
        ∑ B with refinementParent h B = A, ∑ D with refinementParent h D = C,
          if (B.1, D.1) ∈ Bad then (#B.1 * #D.1 : ℝ) else 0 := by
  classical
  set FA : Finset Q.parts := {B | refinementParent h B = A}
  set FC : Finset Q.parts := {D | refinementParent h D = C}
  have hcount : (#{q ∈ X ×ˢ Y | R.colorOfPair q.1 q.2 = some c} : ℝ) =
      ∑ B ∈ FA, ∑ D ∈ FC,
        (#{q ∈ (X ∩ B.1) ×ˢ (Y ∩ D.1) | R.colorOfPair q.1 q.2 = some c} : ℝ) := by
    simpa [FA, FC] using congrArg (Nat.cast (R := ℝ))
      (card_filter_colorOfPair_eq_sum_refines R h c hX hY)
  have harea : (#X * #Y : ℝ) = ∑ B ∈ FA, ∑ D ∈ FC, (#(X ∩ B.1) * #(Y ∩ D.1) : ℝ) := by
    rw [← sum_mul_sum, ← Nat.cast_sum, ← Nat.cast_sum,
      sum_card_inter_filter_refinementParent_eq h A X, inter_eq_left.2 hX,
      sum_card_inter_filter_refinementParent_eq h C Y, inter_eq_left.2 hY]
  have hACarea : (#A.1 * #C.1 : ℝ) = ∑ B ∈ FA, ∑ D ∈ FC, (#B.1 * #D.1 : ℝ) := by
    rw [← sum_mul_sum, ← Nat.cast_sum, ← Nat.cast_sum, sum_card_filter_refinementParent_eq h A,
      sum_card_filter_refinementParent_eq h C]
  have hcell (B : Q.parts) (hB : B ∈ FA) (D : Q.parts) (hD : D ∈ FC) :
      |(#{q ∈ (X ∩ B.1) ×ˢ (Y ∩ D.1) | R.colorOfPair q.1 q.2 = some c} : ℝ) -
          p c * (#(X ∩ B.1) * #(Y ∩ D.1))| ≤
        δ * (#B.1 * #D.1) + if (B.1, D.1) ∈ Bad then (#B.1 * #D.1 : ℝ) else 0 := by
    by_cases hbad : (B.1, D.1) ∈ Bad
    · have hsub : (#(X ∩ B.1) * #(Y ∩ D.1) : ℝ) ≤ #B.1 * #D.1 :=
        mul_le_mul (mod_cast card_le_card inter_subset_right)
          (mod_cast card_le_card inter_subset_right) (by positivity) (by positivity)
      have hc_le : (#{q ∈ (X ∩ B.1) ×ˢ (Y ∩ D.1) | R.colorOfPair q.1 q.2 = some c} : ℝ) ≤
          #B.1 * #D.1 := by
        have h1 : #{q ∈ (X ∩ B.1) ×ˢ (Y ∩ D.1) | R.colorOfPair q.1 q.2 = some c} ≤
            #(X ∩ B.1) * #(Y ∩ D.1) := (card_filter_le _ _).trans_eq (card_product _ _)
        exact (by exact_mod_cast h1 : _ ≤ (#(X ∩ B.1) * #(Y ∩ D.1) : ℝ)).trans hsub
      have hp_le : p c * (#(X ∩ B.1) * #(Y ∩ D.1)) ≤ #B.1 * #D.1 :=
        (mul_le_of_le_one_left (by positivity) (hp₁ c)).trans hsub
      have hp_nn : 0 ≤ p c * (#(X ∩ B.1) * #(Y ∩ D.1)) := mul_nonneg (hp₀ c) (by positivity)
      have hbd : |(#{q ∈ (X ∩ B.1) ×ˢ (Y ∩ D.1) | R.colorOfPair q.1 q.2 = some c} : ℝ) -
          p c * (#(X ∩ B.1) * #(Y ∩ D.1))| ≤ #B.1 * #D.1 :=
        abs_sub_le_of_nonneg_of_le (Nat.cast_nonneg _) hc_le hp_nn hp_le
      simp only [hbad, ↓reduceIte]
      linarith [mul_nonneg hδ (by positivity : (0 : ℝ) ≤ #B.1 * #D.1)]
    · simp only [hbad, ↓reduceIte, add_zero]
      exact hgood B D (mem_filter.1 hB).2 (mem_filter.1 hD).2 hbad c
        (X ∩ B.1) inter_subset_right (Y ∩ D.1) inter_subset_right
  have hdecomp : (#{q ∈ X ×ˢ Y | R.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#X * #Y) =
      ∑ B ∈ FA, ∑ D ∈ FC, ((#{q ∈ (X ∩ B.1) ×ˢ (Y ∩ D.1) | R.colorOfPair q.1 q.2 = some c} : ℝ) -
        p c * (#(X ∩ B.1) * #(Y ∩ D.1))) := by
    rw [hcount, harea, mul_sum]
    simp_rw [mul_sum, ← sum_sub_distrib]
  rw [hdecomp, hACarea, mul_sum]
  simp_rw [mul_sum, ← sum_add_distrib]
  exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun B hB ↦
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun D hD ↦ hcell B hB D hD))

end CoarseRegularity

/-! ### Strong refining equipartitions -/

section StrongIteration

variable [Fintype κ] [Fintype V] [DecidableEq V] (S : PairColorSystem κ V)

/-- After `j` rounds of seeded regularization, either some step had energy gap at most `g`, or the
current partition has energy at least `j · g`. -/
private theorem exists_strong_refining_equipartition_iterate
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition)
    (g : ℝ) {Φ : ℕ → ℝ} (hΦ : ∀ k, 0 < Φ k) (j : ℕ) :
    (∃ P Q : Finpartition (univ : Finset V),
      Q ≤ P ∧ P ≤ P₀ ∧ P.IsEquipartition ∧ Q.IsEquipartition ∧
        #P.parts ≤ #Q.parts ∧
        #Q.parts ≤ (strongPairColorRegularityStep Φ)^[j] #P₀.parts ∧
        S.energy Q - S.energy P ≤ g ∧
        ∑ BD ∈ S.irregularPairs (Φ #P.parts) Q, (#BD.1 * #BD.2 : ℝ) ≤
          Φ #P.parts * (Fintype.card V : ℝ) ^ 2) ∨
      ∃ P : Finpartition (univ : Finset V),
        P ≤ P₀ ∧ P.IsEquipartition ∧
          #P.parts ≤ (strongPairColorRegularityStep Φ)^[j] #P₀.parts ∧
          j * g ≤ S.energy P := by
  induction j with
  | zero =>
    exact Or.inr ⟨P₀, le_rfl, hP₀, le_rfl, by simpa using S.energy_nonneg P₀⟩
  | succ j ih =>
    have hstep : (strongPairColorRegularityStep Φ)^[j] #P₀.parts ≤
        (strongPairColorRegularityStep Φ)^[j + 1] #P₀.parts :=
      Function.monotone_iterate_of_id_le (fun _ ↦ le_strongPairColorRegularityStep (hΦ _))
        j.le_succ _
    rcases ih with ⟨P, Q, hQP, hPP₀, hP, hQ, hPQcard, hQcard, hgap, hreg⟩ |
      ⟨P, hPP₀, hP, hPcard, hE⟩
    · exact Or.inl ⟨P, Q, hQP, hPP₀, hP, hQ, hPQcard, hQcard.trans hstep, hgap, hreg⟩
    obtain ⟨Q, hQP, hQ, hQcard, hreg⟩ :=
      S.exists_refining_equipartition_sum_irregularPairs_le P hP (hΦ #P.parts)
    have hQcard' : #Q.parts ≤ (strongPairColorRegularityStep Φ)^[j + 1] #P₀.parts := by
      rw [Function.iterate_succ_apply']
      exact (hQcard.trans
        (equitablePairColorRegularityBound_le_strongPairColorRegularityStep Φ _)).trans
        (monotone_strongPairColorRegularityStep Φ hPcard)
    by_cases hgap : S.energy Q - S.energy P ≤ g
    · exact Or.inl ⟨P, Q, hQP, hPP₀, hP, hQ, card_mono hQP, hQcard', hgap, hreg⟩
    · refine Or.inr ⟨Q, hQP.trans hPP₀, hQ, hQcard', ?_⟩
      push_cast
      linarith [not_le.1 hgap]

/-- **Strong pair-color regularity lemma.** Given an equipartition `P₀`, an energy-gap tolerance
`g > 0`, and a positive schedule `Φ : ℕ → ℝ`, there exist refining equipartitions `Q ≤ P ≤ P₀` with
at most `strongPairColorRegularityBound g Φ #P₀.parts` parts such that `S.energy Q - S.energy P ≤ g`
and the `Φ #P.parts`-irregular distinct-cell pairs of `Q` cover at most `Φ #P.parts |V|²` ordered
vertex pairs. -/
theorem exists_strong_refining_equipartition
    (P₀ : Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition)
    {g : ℝ} (hg : 0 < g) {Φ : ℕ → ℝ} (hΦ : ∀ k, 0 < Φ k) :
    ∃ P Q : Finpartition (univ : Finset V),
      Q ≤ P ∧ P ≤ P₀ ∧ P.IsEquipartition ∧ Q.IsEquipartition ∧
        #P.parts ≤ #Q.parts ∧
        #Q.parts ≤ strongPairColorRegularityBound g Φ #P₀.parts ∧
        S.energy Q - S.energy P ≤ g ∧
        ∑ BD ∈ S.irregularPairs (Φ #P.parts) Q, (#BD.1 * #BD.2 : ℝ) ≤
          Φ #P.parts * (Fintype.card V : ℝ) ^ 2 := by
  rcases S.exists_strong_refining_equipartition_iterate P₀ hP₀ g hΦ (⌊1 / g⌋₊ + 1) with
    hfound | ⟨P, -, -, -, hE⟩
  · simpa only [strongPairColorRegularityBound_def] using hfound
  exfalso
  have hgt : 1 / g < (⌊1 / g⌋₊ + 1 : ℕ) := by
    push_cast
    exact Nat.lt_floor_add_one _
  rw [div_lt_iff₀ hg] at hgt
  linarith [S.energy_le_one P]

end StrongIteration

end PairColorSystem

end TauCeti
