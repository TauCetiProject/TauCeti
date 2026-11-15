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
import TauCeti.Combinatorics.Enumerative.RandomColoring

/-!
# Strong regular approximation of pair-color systems

* `TauCeti.strongPairColorStepBound`, `TauCeti.strongPairColorPartBound`,
  `TauCeti.strongPairColorHostBound`: quantitative bounds for strong pair-color regularity.
* `TauCeti.PairColorSystem.sum_abs_pairColorDensity_sub_le`: `L¹` block-density energy-gap bound.
* `TauCeti.PairColorSystem.exists_strong_recoloring_isPairColorRegular`: strong regular
  approximation of a pair-color system along an arbitrary positive schedule `G`.
-/

public section

open Finset Finpartition Real

namespace TauCeti
private noncomputable def pairQuarterTol (G : ℕ → ℝ) (k : ℕ) : ℝ := min (1 / 4) (G k / 4)
private noncomputable def pairEnergyGap (q₂ : ℕ) (δ : ℝ) : ℝ := (min δ 1 / (8 * (q₂ + 1))) ^ 2
private noncomputable def pairFineScale (q₂ : ℕ) (δ : ℝ) (G : ℕ → ℝ) (k : ℕ) : ℝ := min (min δ 1 /
  (8 * (q₂ + 1))) (pairQuarterTol G k ^ 3 / (16 * (q₂ + 1) * ((k : ℝ) + 1) ^ 2))
private theorem pairQuarterTol_pos {G : ℕ → ℝ} (hG : ∀ k, 0 < G k) (k : ℕ) : 0 < pairQuarterTol G k
    := lt_min (by norm_num) (by linarith [hG k])
private theorem pairQuarterTol_le_quarter (G : ℕ → ℝ) (k : ℕ) : pairQuarterTol G k ≤ 1 / 4 :=
  min_le_left _ _
private theorem four_mul_pairQuarterTol_le (G : ℕ → ℝ) (k : ℕ) : 4 * pairQuarterTol G k ≤ G k := by
  dsimp [pairQuarterTol]; linarith [min_le_right (1 / 4) (G k / 4)]
private theorem pairEnergyGap_pos (q₂ : ℕ) {δ : ℝ} (hδ : 0 < δ) : 0 < pairEnergyGap q₂ δ := by
  have := lt_min hδ zero_lt_one; unfold pairEnergyGap; positivity
private theorem pairFineScale_pos (q₂ : ℕ) {δ : ℝ} (hδ : 0 < δ) {G : ℕ → ℝ} (hG : ∀ k, 0 < G k) (k
    : ℕ) : 0 < pairFineScale q₂ δ G k := by
  have := lt_min hδ zero_lt_one; have := pairQuarterTol_pos hG k
  unfold pairFineScale; exact lt_min (by positivity) (by positivity)
/-- One-round part bound for strong pair-color regularity, maximized over `j ≤ k`. -/
noncomputable def strongPairColorStepBound (q₂ : ℕ) (δ : ℝ) (G : ℕ → ℝ) (k : ℕ) : ℕ := (range (k +
  1)).sup fun j ↦ equitablePairColorRegularityBound (pairFineScale q₂ δ G j) j
/-- `strongPairColorStepBound` is monotone in the starting part count. -/
theorem strongPairColorStepBound_mono (q₂ : ℕ) (δ : ℝ) (G : ℕ → ℝ) : Monotone
    (strongPairColorStepBound q₂ δ G) := fun _ _ hab ↦ sup_mono (range_mono (Nat.add_le_add_right
    hab 1))
private theorem equitablePairColorRegularityBound_le_step {q₂ j k : ℕ} {δ : ℝ} {G : ℕ → ℝ} (hjk : j
    ≤ k) : equitablePairColorRegularityBound (pairFineScale q₂ δ G j) j ≤ strongPairColorStepBound
    q₂ δ G k := le_sup (f := fun j ↦ equitablePairColorRegularityBound (pairFineScale q₂ δ G j) j)
    (mem_range.2 (Nat.lt_succ_of_le hjk))
/-- One round of strong pair-color regularity never decreases the number of parts. -/
theorem le_strongPairColorStepBound (q₂ : ℕ) {δ : ℝ} (hδ : 0 < δ) {G : ℕ → ℝ} (hG : ∀ k, 0 < G k)
    (k : ℕ) : k ≤ strongPairColorStepBound q₂ δ G k := by
  refine le_trans ?_ (equitablePairColorRegularityBound_le_step le_rfl)
  rw [equitablePairColorRegularityBound_def]; exact (le_max_left k 1).trans <|
    Function.id_le_iterate_of_id_le (le_ceil_mul_mul_four_pow_sq (pairFineScale_pos q₂ hδ hG k))
      _ _
/-- Upper bound on `#P.parts` produced by strong pair-color regularization from `l₀` parts. -/
noncomputable def strongPairColorPartBound (q₂ : ℕ) (δ : ℝ) (G : ℕ → ℝ) (l₀ : ℕ) : ℕ :=
  (strongPairColorStepBound q₂ δ G)^[⌊1 / pairEnergyGap q₂ δ⌋₊] l₀
/-- `strongPairColorPartBound` is monotone in `l₀`. -/
theorem strongPairColorPartBound_mono (q₂ : ℕ) (δ : ℝ) (G : ℕ → ℝ) : Monotone
    (strongPairColorPartBound q₂ δ G) := (strongPairColorStepBound_mono q₂ δ G).iterate _
/-- `strongPairColorPartBound` is at least `l₀` when `0 < δ` and `G` is positive. -/
theorem le_strongPairColorPartBound (q₂ : ℕ) {δ : ℝ} (hδ : 0 < δ) {G : ℕ → ℝ} (hG : ∀ k, 0 < G k)
    (l₀ : ℕ) : l₀ ≤ strongPairColorPartBound q₂ δ G l₀ := Function.id_le_iterate_of_id_le
    (le_strongPairColorStepBound q₂ hδ hG) _ l₀
/-- Host-size threshold for strong pair-color regular approximation from `l₀` initial parts. -/
noncomputable def strongPairColorHostBound (q₂ : ℕ) (δ : ℝ) (G : ℕ → ℝ) (l₀ : ℕ) : ℕ :=
  let B := strongPairColorPartBound q₂ δ G l₀; max (max 2 ⌈8 / δ⌉₊) (((range (B + 1)).sup fun k ↦
    ⌈(q₂ + 3 : ℝ) / (pairFineScale q₂ δ G k / (q₂ + 1)) ^ 2⌉₊ + 1) *
    max (strongPairColorStepBound q₂ δ G B) 1)
/-- `strongPairColorHostBound` is monotone in `l₀`. -/
theorem strongPairColorHostBound_mono (q₂ : ℕ) (δ : ℝ) (G : ℕ → ℝ) : Monotone
    (strongPairColorHostBound q₂ δ G) := fun _ _ hab ↦ by
  dsimp [strongPairColorHostBound]; have hB := strongPairColorPartBound_mono q₂ δ G hab
  exact max_le_max le_rfl (Nat.mul_le_mul (sup_mono (range_mono (Nat.add_le_add_right hB 1)))
    (max_le_max (strongPairColorStepBound_mono q₂ δ G hB) le_rfl))

namespace PairColorSystem
variable {κ V : Type*} [Fintype V] [DecidableEq V]
/-- **Energy gap controls `L¹` block-density deviation.** -/
theorem sum_abs_pairColorDensity_sub_le [Fintype κ] (S : PairColorSystem κ V) {P Q : Finpartition
    (univ : Finset V)} (hQP : Q ≤ P) {γ : ℝ} (hgap : S.energy Q - S.energy P ≤ γ) (c : κ) : ∑ p ∈
    (univ : Finset V).offDiag, |(pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
    pairColorDensity S c (P.part p.1) (P.part p.2)| ≤ √γ * (Fintype.card V : ℝ) ^ 2 := by
  set D := #(univ : Finset V).offDiag; obtain hD | hD := eq_or_ne D 0
  · rw [card_eq_zero.1 hD, sum_empty]; exact mul_nonneg (sqrt_nonneg _) (sq_nonneg _)
  have hDpos : (0 : ℝ) < D := Nat.cast_pos.2 (Nat.pos_of_ne_zero hD)
  have hDle : (D : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := mod_cast (card_le_card (subset_univ (univ :
    Finset V).offDiag)).trans_eq (by rw [card_univ, Fintype.card_prod, ← sq])
  rw [← S.sum_sq_pairColorDensity_sub_div_eq_energy_sub hQP] at hgap
  have hcs := weighted_sum_abs_le_sqrt (univ : Finset V).offDiag (fun _ ↦ (D : ℝ)⁻¹) (fun p ↦
    (pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) - pairColorDensity S c (P.part p.1)
    (P.part p.2)) (fun _ _ ↦ inv_nonneg.2 hDpos.le)
    (by rw [sum_const, nsmul_eq_mul, mul_inv_cancel₀ hDpos.ne']) <| by
      refine le_trans ?_ hgap; rw [← mul_sum, inv_mul_eq_div]; gcongr with p
      exact single_le_sum (f := fun b ↦ ((pairColorDensity S b (Q.part p.1) (Q.part p.2) : ℝ) -
        pairColorDensity S b (P.part p.1) (P.part p.2)) ^ 2) (fun _ _ ↦ sq_nonneg _) (mem_univ c)
  rw [← mul_sum, inv_mul_le_iff₀ hDpos] at hcs
  exact hcs.trans ((mul_le_mul_of_nonneg_right hDle (sqrt_nonneg _)).trans_eq (mul_comm _ _))
private theorem card_univ_le_two_mul_parts_mul_card {P : Finpartition (univ : Finset V)} (hP :
    P.IsEquipartition) (hPV : #P.parts ≤ Fintype.card V) {A : Finset V} (hA : A ∈ P.parts) :
    Fintype.card V ≤ 2 * #P.parts * #A := by
  have hPpos : 0 < #P.parts := card_pos.2 ⟨A, hA⟩; have := Nat.div_pos hPV hPpos
  have : Fintype.card V / #P.parts ≤ #A := (by simpa [card_univ] using hP.average_le_card_part hA)
  have := Nat.mod_lt (Fintype.card V) hPpos; have := Nat.div_add_mod (Fintype.card V) #P.parts
  nlinarith
private theorem pairFineScale_err_le_subrect {q₂ t n a b a' b' : ℕ} {δ : ℝ} (hδ : 0 < δ) {G : ℕ →
    ℝ} (hG : ∀ k, 0 < G k) (hn_a : (n : ℝ) ≤ 2 * t * a) (hn_b : (n : ℝ) ≤ 2 * t * b) (ha' : 2 *
    pairQuarterTol G t * a ≤ a') (hb' : 2 * pairQuarterTol G t * b ≤ b') : (q₂ * (pairFineScale q₂
    δ G t / (q₂ + 1)) + q₂ * pairFineScale q₂ δ G t) * (a * b : ℝ) + q₂ * pairFineScale q₂ δ G t *
    (n : ℝ) ^ 2 ≤ 2 * pairQuarterTol G t * (a' * b' : ℕ) := by
  set τ := pairQuarterTol G t; set ξ_P := pairFineScale q₂ δ G t; set ξ₀ := ξ_P / (q₂ + 1)
  have hτ_pos := pairQuarterTol_pos hG t; have hξP_pos := pairFineScale_pos q₂ hδ hG t
  have hn2 : (n : ℝ) ^ 2 ≤ 4 * (t : ℝ) ^ 2 * (a * b : ℝ) := (sq (n : ℝ)).trans_le ((mul_le_mul hn_a
    hn_b (Nat.cast_nonneg _) (by positivity)).trans_eq (by ring))
  have hqξ₀ : (q₂ : ℝ) * ξ₀ ≤ ξ_P := by
    rw [mul_div_left_comm]
    exact mul_le_of_le_one_right hξP_pos.le (div_le_one_of_le₀ (by linarith) (by positivity))
  have hcoeff : q₂ * ξ₀ + q₂ * ξ_P + 4 * q₂ * (t : ℝ) ^ 2 * ξ_P ≤ 8 * τ ^ 3 :=
    (by linarith [hqξ₀, show 0 ≤ (15 + 15 * (q₂ : ℝ) + 32 * (q₂ + 1) * t + (12 * q₂ + 16) * (t : ℝ)
        ^ 2) * ξ_P by positivity] :
      _ ≤ 16 * (q₂ + 1 : ℝ) * ((t : ℝ) + 1) ^ 2 * ξ_P).trans
      (((le_div_iff₀' (by positivity)).1 (min_le_right _ _)).trans (by linarith [pow_pos hτ_pos 3]))
  refine (by nlinarith [mul_le_mul_of_nonneg_left hn2 (show 0 ≤ (q₂ : ℝ) * ξ_P by positivity)] :
      _ ≤ (q₂ * ξ₀ + q₂ * ξ_P + 4 * q₂ * (t : ℝ) ^ 2 * ξ_P) * (a * b : ℝ)).trans
    ((mul_le_mul_of_nonneg_right hcoeff (by positivity)).trans ?_)
  rw [show 8 * τ ^ 3 * (a * b : ℝ) = 2 * τ * ((2 * τ * a) * (2 * τ * b)) by ring, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left (mul_le_mul ha' hb' (by positivity) (Nat.cast_nonneg _)) (by
    positivity)
open Classical in
private theorem fineSub_biUnion {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (C : P.parts)
    {X : Finset V} (hX : X ⊆ C.1) : ((univ.filter fun U : Q.parts ↦ U.1 ⊆ C.1) : Set
    Q.parts).PairwiseDisjoint (fun U ↦ X ∩ U.1) ∧ (univ.filter fun U : Q.parts ↦ U.1 ⊆ C.1).biUnion
    (fun U ↦ X ∩ U.1) = X ∧ ∑ U ∈ univ.filter (fun U : Q.parts ↦ U.1 ⊆ C.1), #(X ∩ U.1) = #X := by
  have hdisj : ((univ.filter fun U : Q.parts ↦ U.1 ⊆ C.1) : Set Q.parts).PairwiseDisjoint (fun U ↦
      X ∩ U.1) := fun U _ U' _ hne ↦ (Q.disjoint U.2 U'.2 fun heq ↦ hne (Subtype.ext heq)).mono
      inter_subset_right inter_subset_right
  have hunion : (univ.filter fun U : Q.parts ↦ U.1 ⊆ C.1).biUnion (fun U ↦ X ∩ U.1) = X := by
    ext u; simp only [mem_biUnion, mem_filter, mem_univ, true_and, mem_inter]
    refine ⟨fun ⟨_, _, huX, _⟩ ↦ huX, fun huX ↦ ?_⟩
    let cQ : Q.parts := ⟨Q.part u, Q.part_mem.2 (mem_univ u)⟩
    have hp : refinementParent hQP cQ = C := Subtype.ext <| (P.part_eq_of_mem (refinementParent hQP
      cQ).2 (le_refinementParent hQP cQ (Q.mem_part_self.2 (mem_univ u)))).symm.trans
      (P.part_eq_of_mem C.2 (hX huX))
    exact ⟨cQ, hp ▸ le_refinementParent hQP cQ, huX, Q.mem_part_self.2 (mem_univ u)⟩
  exact ⟨hdisj, hunion, by rw [← card_biUnion hdisj, hunion]⟩
open Classical in
/-- **Strong regular approximation of a pair-color system.** -/
theorem exists_strong_recoloring_isPairColorRegular [Fintype κ] (S : PairColorSystem κ V) (P₀ :
    Finpartition (univ : Finset V)) (hP₀ : P₀.IsEquipartition) {δ : ℝ} (hδ : 0 < δ) (hl₀ : 8 ≤ δ *
    #P₀.parts) {G : ℕ → ℝ} (hG : ∀ k, 0 < G k) (hV : strongPairColorHostBound (Fintype.card κ) δ G
    #P₀.parts ≤ Fintype.card V) : ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem
    (Option κ) V), P ≤ P₀ ∧ P.IsEquipartition ∧ #P.parts ≤ strongPairColorPartBound (Fintype.card
    κ) δ G #P₀.parts ∧ T.rev = Option.map S.rev ∧ (⟨P, T⟩ : PairSkeleton3 (Option κ)
    V).IsPairColorRegular (G #P.parts) ∧ (#{p | T.color p ≠ some (S.color p)} : ℝ) ≤ δ *
    (Fintype.card V : ℝ) ^ 2 := by
  classical
  let q₂ := Fintype.card κ; let n := Fintype.card V; let γ := pairEnergyGap q₂ δ
  have hn2 : 2 ≤ n := (le_max_left 2 ⌈8 / δ⌉₊).trans ((le_max_left _ _).trans hV)
  have h8n : (8 : ℝ) ≤ δ * n := (div_le_iff₀' hδ).1 ((Nat.le_ceil _).trans (mod_cast (le_max_right
    2 ⌈8 / δ⌉₊).trans ((le_max_left _ _).trans hV)))
  have : Nonempty κ := by
    obtain ⟨u, -, v, -, huv⟩ := one_lt_card.1 (by rw [card_univ]; omega : 1 < #(univ : Finset V))
    exact ⟨S.color ⟨(u, v), huv⟩⟩
  obtain ⟨P, Q, hQP, hPP₀, hP, hQ, hPbound, hQbound, hgap, hQreg⟩ : ∃ P Q : Finpartition (univ :
      Finset V), Q ≤ P ∧ P ≤ P₀ ∧ P.IsEquipartition ∧ Q.IsEquipartition ∧ #P.parts ≤
      strongPairColorPartBound q₂ δ G #P₀.parts ∧ #Q.parts ≤ strongPairColorStepBound q₂ δ G
      (strongPairColorPartBound q₂ δ G #P₀.parts) ∧ S.energy Q - S.energy P ≤ γ ∧ ∑ UV ∈
      S.irregularPairs (pairFineScale q₂ δ G #P.parts) Q, (#UV.1 * #UV.2 : ℝ) ≤ pairFineScale q₂ δ
      G #P.parts * (n : ℝ) ^ 2 := by
    let step := strongPairColorStepBound q₂ δ G; have hγ := pairEnergyGap_pos q₂ hδ
    have hstep_mono := strongPairColorStepBound_mono q₂ δ G
    have hid := le_strongPairColorStepBound q₂ hδ hG
    let Good (P : Finpartition (univ : Finset V)) : Prop := ∃ Q, Q ≤ P ∧ Q.IsEquipartition ∧
      #Q.parts ≤ step #P.parts ∧ S.energy Q - S.energy P ≤ γ ∧ ∑ UV ∈ S.irregularPairs
      (pairFineScale q₂ δ G #P.parts) Q, (#UV.1 * #UV.2 : ℝ) ≤ pairFineScale q₂ δ G #P.parts * (n :
      ℝ) ^ 2
    have advance (P) (hP : P.IsEquipartition) : Good P ∨ ∃ Q, Q ≤ P ∧ Q.IsEquipartition ∧ #Q.parts
        ≤ step #P.parts ∧ S.energy P + γ < S.energy Q := by
      obtain ⟨Q, hQP, hQ, hQcard, hQreg⟩ := S.exists_refining_equipartition_sum_irregularPairs_le P
        hP (pairFineScale_pos q₂ hδ hG #P.parts)
      have hQs := hQcard.trans (equitablePairColorRegularityBound_le_step le_rfl)
      by_cases hgap : S.energy Q - S.energy P ≤ γ
      exacts [Or.inl ⟨Q, hQP, hQ, hQs, hgap, hQreg⟩, Or.inr ⟨Q, hQP, hQ, hQs, by linarith⟩]
    have key (j : ℕ) : (∃ P, P ≤ P₀ ∧ P.IsEquipartition ∧ #P.parts ≤ step^[j] #P₀.parts ∧ Good P) ∨
        ∃ P, P ≤ P₀ ∧ P.IsEquipartition ∧ #P.parts ≤ step^[j] #P₀.parts ∧ j * γ ≤ S.energy P := by
      induction j with
      | zero => exact Or.inr ⟨P₀, le_rfl, hP₀, le_rfl, by simpa using S.energy_nonneg P₀⟩
      | succ j ih =>
        have hle : step^[j] #P₀.parts ≤ step^[j + 1] #P₀.parts := by
          rw [Function.iterate_succ_apply']; exact hid _
        obtain ⟨P, h1, h2, h3, hg⟩ | ⟨P, h1, h2, h3, hE⟩ := ih
        · exact Or.inl ⟨P, h1, h2, h3.trans hle, hg⟩
        obtain hg | ⟨Q, hQP, hQ, hQc, hE'⟩ := advance P h2
        · exact Or.inl ⟨P, h1, h2, h3.trans hle, hg⟩
        refine Or.inr ⟨Q, hQP.trans h1, hQ, ?_, by push_cast; linarith⟩
        rw [Function.iterate_succ_apply']; exact hQc.trans (hstep_mono h3)
    have hK : 1 < (⌊1 / γ⌋₊ + 1 : ℕ) * γ := by
      rw [← div_lt_iff₀ hγ, Nat.cast_add, Nat.cast_one]; exact Nat.lt_floor_add_one _
    obtain ⟨P, hPP₀, hP, hPcard, ⟨Q, hQP, hQ, hQcard, hgap, hQreg⟩⟩ : ∃ P, P ≤ P₀ ∧
        P.IsEquipartition ∧ #P.parts ≤ step^[⌊1 / γ⌋₊] #P₀.parts ∧ Good P := by
      obtain hg | ⟨P, h1, h2, h3, hE⟩ := key ⌊1 / γ⌋₊; · exact hg
      obtain hg | ⟨Q, -, -, -, hE'⟩ := advance P h2; · exact ⟨P, h1, h2, h3, hg⟩
      push_cast at hK; linarith [S.energy_le_one Q]
    exact ⟨P, Q, hQP, hPP₀, hP, hQ, hPcard, hQcard.trans (hstep_mono hPcard), hgap, hQreg⟩
  let t := #P.parts; let τ := pairQuarterTol G t
  let ξ_P := pairFineScale q₂ δ G t; let ξ₀ := ξ_P / (q₂ + 1)
  have hτ_pos := pairQuarterTol_pos hG t; have hξP_pos := pairFineScale_pos q₂ hδ hG t
  have hξ₀_pos : 0 < ξ₀ := (by positivity)
  have hU_large (U : Finset V) (hU : U ∈ Q.parts) : (q₂ + 3 : ℝ) ≤ ξ₀ ^ 2 * #U := by
    have hKM := (le_max_right _ _).trans hV
    have hK_div := (Nat.le_div_iff_mul_le (card_pos.2 ⟨U, hU⟩)).2 ((Nat.mul_le_mul_left _
      (hQbound.trans (le_max_left _ _))).trans hKM)
    have havg : n / #Q.parts ≤ #U := (by simpa [card_univ, n] using hQ.average_le_card_part hU)
    have hKt := le_sup (f := fun k ↦ ⌈(q₂ + 3 : ℝ) / (pairFineScale q₂ δ G k / (q₂ + 1)) ^ 2⌉₊ + 1)
      (mem_range.2 (Nat.lt_succ_of_le hPbound))
    exact (div_le_iff₀' (sq_pos_of_pos hξ₀_pos)).1 ((Nat.le_ceil _).trans (Nat.cast_le.2
      ((Nat.le_succ _).trans (hKt.trans (hK_div.trans havg)))))
  obtain ⟨R, hR_rev, hR_reg, hR_edits⟩ : ∃ R : PairColorSystem κ V, R.rev = S.rev ∧ (∀ A ∈ P.parts,
      ∀ B ∈ P.parts, A ≠ B → R.IsRegularPair (4 * τ) A B) ∧ (#{p | R.color p ≠ S.color p} : ℝ) ≤ (3
      / 8) * δ * (n : ℝ) ^ 2 := by
    have hPV : t ≤ n := P.card_parts_le_card.trans_eq card_univ
    let idx := Fintype.equivFin P.parts; let parent (U : Q.parts) := refinementParent hQP U
    let x₀ (q : V × V) : κ := if h : q.1 ≠ q.2 then S.color ⟨q, h⟩ else Classical.arbitrary κ
    have hloc (U W : Q.parts) : ∃ x : V × V → κ, parent U ≠ parent W → (#{q ∈ U.1 ×ˢ W.1 | x q ≠ x₀
        q} : ℝ) ≤ ((∑ c, |(pairColorDensity S c U.1 W.1 : ℝ) - pairColorDensity S c (parent U).1
        (parent W).1|) / 2 + q₂ * ξ₀) * (#U.1 * #W.1 : ℕ) ∧ ∀ U' ⊆ U.1, ∀ W' ⊆ W.1, ∀ c', |(#{q ∈
        U' ×ˢ W' | x q = c'} : ℝ) - (pairColorDensity S c' (parent U).1 (parent W).1 : ℝ) * (#U' *
        #W' : ℕ)| ≤ (q₂ * ξ₀ + q₂ * ξ_P) * (#U.1 * #W.1 : ℕ) + if (U.1, W.1) ∈ S.irregularPairs ξ_P
        Q then (q₂ : ℝ) * (#U.1 * #W.1 : ℕ) else 0 := by
      by_cases hAB : parent U = parent W; · exact ⟨x₀, fun hne ↦ (hne hAB).elim⟩
      have hdisjAB : Disjoint (parent U).1 (parent W).1 := P.disjoint (parent U).2 (parent W).2 fun
        heq ↦ hAB (Subtype.ext heq)
      have hdisjUW := hdisjAB.mono (le_refinementParent hQP U) (le_refinementParent hQP W)
      have hAB_ne : (((parent U).1 ×ˢ (parent W).1).filter fun p ↦ p.1 ≠ p.2).Nonempty := by
        obtain ⟨u, hu⟩ := P.nonempty_of_mem_parts (parent U).2
        obtain ⟨w, hw⟩ := P.nonempty_of_mem_parts (parent W).2
        exact ⟨(u, w), mem_filter.2 ⟨mem_product.2 ⟨hu, hw⟩, hdisjAB.forall_ne_finset hu hw⟩⟩
      have hUW_pos : (0 : ℝ) < (#U.1 * #W.1 : ℕ) := Nat.cast_pos.2 (Nat.mul_pos
        (Q.nonempty_of_mem_parts U.2).card_pos (Q.nonempty_of_mem_parts W.2).card_pos)
      obtain ⟨x, -, hx_edit, hx_rect⟩ := exists_coupled_recoloring_abs_card_filter_sub_le (U.1 ×ˢ
        W.1) x₀ (p := fun c ↦ (pairColorDensity S c (parent U).1 (parent W).1 : ℝ)) (fun c ↦
        mod_cast pairColorDensity_nonneg S c (parent U).1 (parent W).1) (mod_cast
        sum_pairColorDensity S _ _ hAB_ne) (I := ↥(U.1.powerset ×ˢ W.1.powerset)) (fun i ↦ i.1.1 ×ˢ
        i.1.2) (fun i ↦ product_subset_product (mem_powerset.1 (mem_product.1 i.2).1)
        (mem_powerset.1 (mem_product.1 i.2).2)) (a := ξ₀ * (#U.1 * #W.1 : ℕ)) (mul_pos hξ₀_pos
        hUW_pos) (by
          rw [card_product]; refine two_mul_add_one_mul_exp_lt_one (k := #U.1 + #W.1)
            (by rw [Fintype.card_coe, card_product, card_powerset, card_powerset, ← pow_add]) ?_
          have hU1 : (1 : ℝ) ≤ #U.1 := Nat.one_le_cast.2 (Q.nonempty_of_mem_parts U.2).card_pos
          rw [Nat.cast_add, Nat.cast_mul]; linarith only [hU1, Nat.one_le_cast (α := ℝ).2
            (Q.nonempty_of_mem_parts W.2).card_pos, mul_le_mul_of_nonneg_right (hU_large U.1 U.2)
            (Nat.cast_nonneg #W.1), mul_le_mul_of_nonneg_right (hU_large W.1 W.2)
            (Nat.cast_nonneg #U.1), le_mul_of_one_le_right (Nat.cast_nonneg (α := ℝ) q₂) hU1,
            mul_nonneg (Nat.cast_nonneg (α := ℝ) q₂) (Nat.cast_nonneg #W.1)])
      have hx₀_cnt {s t' : Finset V} (hs : s ⊆ U.1) (ht' : t' ⊆ W.1) (c : κ) : (#{q ∈ s ×ˢ t' | x₀
          q = c} : ℝ) = (pairColorDensity S c s t' : ℝ) * (#s * #t' : ℕ) := by
        rw [← show {q ∈ s ×ˢ t' | S.colorOfPair q.1 q.2 = some c} = {q ∈ s ×ˢ t' | x₀ q = c} from
          filter_congr fun q hq ↦ by
            have hne := (hdisjUW.mono hs ht').forall_ne_finset (mem_product.1 hq).1 (mem_product.1
              hq).2
            simp [x₀, hne], Nat.cast_mul]
        exact_mod_cast (pairColorDensity_mul_card_of_disjoint S c (hdisjUW.mono hs ht')).symm
      refine ⟨x, fun _ ↦ ⟨?_, fun U' hU' W' hW' c' ↦ ?_⟩⟩
      · rw [card_product, show ∑ c, |(#{q ∈ U.1 ×ˢ W.1 | x₀ q = c} : ℝ) - (pairColorDensity S c
            (parent U).1 (parent W).1 : ℝ) * (#U.1 * #W.1 : ℕ)| = (∑ c, |(pairColorDensity S c U.1
            W.1 : ℝ) - pairColorDensity S c (parent U).1 (parent W).1|) * (#U.1 * #W.1 : ℕ) by
          rw [sum_mul]; refine sum_congr rfl fun c _ ↦ ?_
          rw [hx₀_cnt Subset.rfl Subset.rfl c, ← sub_mul, abs_mul, abs_of_pos hUW_pos]] at hx_edit
        linarith
      · have htest := hx_rect ⟨(U', W'), mem_product.2 ⟨mem_powerset.2 hU', mem_powerset.2 hW'⟩⟩ c'
        simp only [card_product] at htest
        have hsub_prod : ((#U' * #W' : ℕ) : ℝ) ≤ (#U.1 * #W.1 : ℕ) := mod_cast Nat.mul_le_mul
          (card_le_card hU') (card_le_card hW')
        have hsum_err : ∑ c, |(#{q ∈ U' ×ˢ W' | x₀ q = c} : ℝ) - (#{q ∈ U.1 ×ˢ W.1 | x₀ q = c} : ℝ)
              / (#U.1 * #W.1 : ℕ) * (#U' * #W' : ℕ)| ≤ q₂ * ξ_P * (#U.1 * #W.1 : ℕ) + if (U.1, W.1)
              ∈ S.irregularPairs ξ_P Q then (q₂ : ℝ) * (#U.1 * #W.1 : ℕ) else 0 := by
          refine (sum_le_sum (g := fun _ ↦ if S.IsRegularPair ξ_P U.1 W.1 then ξ_P * (#U.1 * #W.1 :
            ℕ) else (#U.1 * #W.1 : ℕ)) fun c _ ↦ ?_).trans ?_
          · rw [hx₀_cnt hU' hW' c, hx₀_cnt Subset.rfl Subset.rfl c, mul_div_cancel_right₀ _
              hUW_pos.ne', ← sub_mul, abs_mul, abs_of_nonneg (a := ((#U' * #W' : ℕ) : ℝ))
              (Nat.cast_nonneg _)]
            have hd1 : |(pairColorDensity S c U' W' : ℝ) - pairColorDensity S c U.1 W.1| ≤ 1 :=
              abs_sub_le_of_nonneg_of_le (mod_cast pairColorDensity_nonneg S c U' W') (mod_cast
              pairColorDensity_le_one S c U' W') (mod_cast pairColorDensity_nonneg S c U.1 W.1)
              (mod_cast pairColorDensity_le_one S c U.1 W.1)
            split_ifs with hregUW
            · by_cases hsize : ξ_P * #U.1 ≤ #U' ∧ ξ_P * #W.1 ≤ #W'
              · exact mul_le_mul (isRegularPair_iff.1 hregUW c U' hU' W' hW' hsize.1 hsize.2)
                  hsub_prod (Nat.cast_nonneg _) hξP_pos.le
              · refine (mul_le_of_le_one_left (Nat.cast_nonneg _) hd1).trans ?_; push_cast
                rcases not_and_or.1 hsize with hUs | hWs
                · exact (mul_le_mul (not_le.1 hUs).le (Nat.cast_le (α := ℝ).2 (card_le_card hW'))
                    (Nat.cast_nonneg _) (by positivity)).trans_eq (by ring)
                · exact (mul_le_mul (Nat.cast_le (α := ℝ).2 (card_le_card hU')) (not_le.1 hWs).le
                    (Nat.cast_nonneg _) (Nat.cast_nonneg _)).trans_eq (by ring)
            · exact (mul_le_of_le_one_left (Nat.cast_nonneg _) hd1).trans hsub_prod
          · rw [sum_const, card_univ, nsmul_eq_mul]
            by_cases hregUW : S.IsRegularPair ξ_P U.1 W.1
            · have hnot : (U.1, W.1) ∉ S.irregularPairs ξ_P Q := fun hm ↦ (S.mem_irregularPairs.1
                hm).2.2.2 hregUW
              simp only [ite_eq_left hregUW, ite_eq_right hnot, add_zero]; linarith
            · have hirr : (U.1, W.1) ∈ S.irregularPairs ξ_P Q := S.mem_irregularPairs.2 ⟨U.2, W.2,
                fun heq : U.1 = W.1 ↦ (Q.nonempty_of_mem_parts U.2).ne_empty (disjoint_self.1 (heq
                ▸ hdisjUW)), hregUW⟩
              simp only [ite_eq_right hregUW, ite_eq_left hirr]
              linarith [show 0 ≤ (q₂ : ℝ) * ξ_P * (#U.1 * #W.1 : ℕ) by positivity]
        linarith [htest, hsum_err]
    choose xloc hxloc using hloc
    let cellP (u : V) : P.parts := ⟨P.part u, P.part_mem.2 (mem_univ u)⟩
    let cellQ (u : V) : Q.parts := ⟨Q.part u, Q.part_mem.2 (mem_univ u)⟩
    have hcellQ_parent (u : V) : parent (cellQ u) = cellP u := Subtype.ext <| (P.part_eq_of_mem
      (parent (cellQ u)).2 (le_refinementParent hQP (cellQ u) (Q.mem_part_self.2 (mem_univ
      u)))).symm
    let R : PairColorSystem κ V := ⟨fun p ↦ if idx (cellP p.1.1) < idx (cellP p.1.2) then
      xloc (cellQ p.1.1) (cellQ p.1.2) p.1 else if idx (cellP p.1.2) < idx (cellP p.1.1) then
      S.rev (xloc (cellQ p.1.2) (cellQ p.1.1) p.1.swap) else S.color p, S.rev, S.rev_involutive,
      fun ⟨⟨u, v⟩, huv⟩ ↦ by
        dsimp only [Prod.fst_swap, Prod.snd_swap, Prod.swap_prod_mk]
        rcases lt_trichotomy (idx (cellP u)) (idx (cellP v)) with hlt | heq | hgt
        · simp [hlt, lt_asymm hlt]
        · simp only [heq, lt_irrefl, ↓reduceIte]; exact S.color_rev ⟨(u, v), huv⟩
        · simp [hgt, lt_asymm hgt, S.rev_involutive (xloc (cellQ v) (cellQ u) (v, u))]⟩
    have hR_reg_lt (A B : P.parts) (hlt : idx A < idx B) : R.IsRegularPair (4 * τ) A.1 B.1 := by
      have hdisjAB : Disjoint A.1 B.1 := P.disjoint A.2 B.2 fun heq ↦ hlt.ne (congrArg idx
        (Subtype.ext heq))
      let QA : Finset Q.parts := univ.filter fun U ↦ U.1 ⊆ A.1
      let QB : Finset Q.parts := univ.filter fun W ↦ W.1 ⊆ B.1
      have hcard_p (C : P.parts) : ∑ U ∈ univ.filter (fun U : Q.parts ↦ U.1 ⊆ C.1), #U.1 = #C.1 :=
        (sum_congr rfl fun U hU ↦ congrArg card (inter_eq_right.2 (mem_filter.1 hU).2).symm).trans
        (fineSub_biUnion hQP C Subset.rfl).2.2
      have hirr_sum : ∑ UW ∈ QA ×ˢ QB, (if (UW.1.1, UW.2.1) ∈ S.irregularPairs ξ_P Q then (q₂ : ℝ)
          * (#UW.1.1 * #UW.2.1 : ℕ) else 0) ≤ q₂ * ξ_P * (n : ℝ) ^ 2 := by
        rw [← sum_filter]
        let emb : Q.parts × Q.parts ↪ Finset V × Finset V := ⟨fun UW ↦ (UW.1.1, UW.2.1), fun _ _ h
          ↦ Prod.ext (Subtype.ext (Prod.mk.inj h).1) (Subtype.ext (Prod.mk.inj h).2)⟩
        have hmap : ((QA ×ˢ QB).filter fun UW ↦ (UW.1.1, UW.2.1) ∈ S.irregularPairs ξ_P Q).map emb
            ⊆ S.irregularPairs ξ_P Q := fun _ h ↦ by
          obtain ⟨_, hUW, rfl⟩ := mem_map.1 h; exact (mem_filter.1 hUW).2
        rw [show ∑ UW ∈ (QA ×ˢ QB).filter (fun UW ↦ (UW.1.1, UW.2.1) ∈ S.irregularPairs ξ_P Q), (q₂
              : ℝ) * (#UW.1.1 * #UW.2.1 : ℕ) = ∑ UV ∈ ((QA ×ˢ QB).filter (fun UW ↦ (UW.1.1, UW.2.1)
              ∈ S.irregularPairs ξ_P Q)).map emb, (q₂ : ℝ) * (#UV.1 * #UV.2 : ℝ) by
          rw [sum_map]; refine sum_congr rfl fun _ _ ↦ ?_; dsimp [emb]; push_cast; rfl]
        exact (sum_le_sum_of_subset_of_nonneg hmap fun _ _ _ ↦ by positivity).trans (by
          rw [← mul_sum, mul_assoc]; exact mul_le_mul_of_nonneg_left hQreg (Nat.cast_nonneg _))
      have hrect_dev (c' : κ) {A' B' : Finset V} (hA' : A' ⊆ A.1) (hB' : B' ⊆ B.1) (hA's : 2 * τ *
          #A.1 ≤ #A') (hB's : 2 * τ * #B.1 ≤ #B') : |(pairColorDensity R c' A' B' : ℝ) -
          pairColorDensity S c' A.1 B.1| ≤ 2 * τ := by
        obtain ⟨hA'd, hA'u, hA'c⟩ := fineSub_biUnion hQP A hA'
        obtain ⟨hB'd, hB'u, hB'c⟩ := fineSub_biUnion hQP B hB'
        have hprod_u : (QA ×ˢ QB).biUnion (fun UW ↦ (A' ∩ UW.1.1) ×ˢ (B' ∩ UW.2.1)) = A' ×ˢ B' := by
          conv_rhs => rw [← hA'u, ← hB'u]
          ext ⟨u, v⟩; simp only [QA, QB, mem_biUnion, mem_product, Prod.exists]; tauto
        have hprod_d : ((QA ×ˢ QB : Finset _) : Set (Q.parts × Q.parts)).PairwiseDisjoint (fun UW ↦
            (A' ∩ UW.1.1) ×ˢ (B' ∩ UW.2.1)) := fun UW₁ h₁ UW₂ h₂ hne ↦ by
          refine disjoint_product.2 ?_; by_cases hf : UW₁.1 = UW₂.1
          · exact Or.inr (hB'd (mem_product.1 h₁).2 (mem_product.1 h₂).2 fun hs ↦ hne (Prod.ext hf
              hs))
          · exact Or.inl (hA'd (mem_product.1 h₁).1 (mem_product.1 h₂).1 hf)
        have hR_cnt : (pairColorDensity R c' A' B' : ℝ) * (#A' * #B' : ℕ) = ∑ UW ∈ QA ×ˢ QB, (#{q ∈
            (A' ∩ UW.1.1) ×ˢ (B' ∩ UW.2.1) | xloc UW.1 UW.2 q = c'} : ℝ) := by
          have h1 : (pairColorDensity R c' A' B' : ℝ) * (#A' * #B' : ℕ) = #{q ∈ A' ×ˢ B' |
              R.colorOfPair q.1 q.2 = some c'} := by
            rw [Nat.cast_mul]
            exact_mod_cast pairColorDensity_mul_card_of_disjoint R c' (hdisjAB.mono hA' hB')
          rw [h1, ← hprod_u, filter_biUnion, card_biUnion (fun _ h₁ _ h₂ hne ↦ (hprod_d h₁ h₂
            hne).mono (filter_subset _ _) (filter_subset _ _)), Nat.cast_sum]
          refine sum_congr rfl fun UW hUW ↦ congrArg (Nat.cast ∘ card) (filter_congr fun q hq ↦ ?_)
          have huU := (mem_inter.1 (mem_product.1 hq).1).2; have hvW := (mem_inter.1 (mem_product.1
            hq).2).2
          have huA := (mem_filter.1 (mem_product.1 hUW).1).2 huU
          have hvB := (mem_filter.1 (mem_product.1 hUW).2).2 hvW
          have hne_q := hdisjAB.forall_ne_finset huA hvB
          have hRq : R.color ⟨q, hne_q⟩ = xloc (cellQ q.1) (cellQ q.2) q := by
            simp [R, show cellP q.1 = A from Subtype.ext (P.part_eq_of_mem A.2 huA), show cellP q.2
              = B from Subtype.ext (P.part_eq_of_mem B.2 hvB), hlt]
          rw [R.colorOfPair_of_ne hne_q, Option.some_inj, hRq, show cellQ q.1 = UW.1 from
            Subtype.ext (Q.part_eq_of_mem UW.1.2 huU), show cellQ q.2 = UW.2 from Subtype.ext
            (Q.part_eq_of_mem UW.2.2 hvW)]
        have hS_cnt : (pairColorDensity S c' A.1 B.1 : ℝ) * (#A' * #B' : ℕ) = ∑ UW ∈ QA ×ˢ QB,
            (pairColorDensity S c' A.1 B.1 : ℝ) * (#(A' ∩ UW.1.1) * #(B' ∩ UW.2.1) : ℕ) := by
          rw [← mul_sum, ← Nat.cast_sum, sum_product, ← hA'c, ← hB'c, sum_mul]; simp_rw [mul_sum];
            rfl
        have hAB_card : ∑ UW ∈ QA ×ˢ QB, ((#UW.1.1 * #UW.2.1 : ℕ) : ℝ) = (#A.1 * #B.1 : ℝ) := by
          rw [← Nat.cast_sum, sum_product]; dsimp only [QA, QB]
          rw [← hcard_p A, ← hcard_p B, ← Nat.cast_mul, sum_mul]; simp_rw [mul_sum]
        have hA'B'_pos : (0 : ℝ) < (#A' * #B' : ℕ) := by
          rw [Nat.cast_mul]; exact mul_pos ((mul_pos (by positivity) (Nat.cast_pos.2
            (P.nonempty_of_mem_parts A.2).card_pos)).trans_le hA's) ((mul_pos (by positivity)
            (Nat.cast_pos.2 (P.nonempty_of_mem_parts B.2).card_pos)).trans_le hB's)
        refine le_of_mul_le_mul_right ?_ hA'B'_pos
        rw [show |(pairColorDensity R c' A' B' : ℝ) - pairColorDensity S c' A.1 B.1| * (#A' * #B' :
            ℕ) = |(pairColorDensity R c' A' B' : ℝ) * (#A' * #B' : ℕ) - (pairColorDensity S c' A.1
            B.1 : ℝ) * (#A' * #B' : ℕ)| by
          rw [← sub_mul, abs_mul, abs_of_pos hA'B'_pos], hR_cnt, hS_cnt, ← sum_sub_distrib]
        refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (g := fun UW ↦ (q₂ * ξ₀ + q₂ * ξ_P) *
          (#UW.1.1 * #UW.2.1 : ℕ) + if (UW.1.1, UW.2.1) ∈ S.irregularPairs ξ_P Q then (q₂ : ℝ) *
          (#UW.1.1 * #UW.2.1 : ℕ) else 0) fun UW hUW ↦ ?_).trans ?_)
        · have hpU : refinementParent hQP UW.1 = A := (refinementParent_eq_iff hQP).2 (mem_filter.1
            (mem_product.1 hUW).1).2
          have hpW : refinementParent hQP UW.2 = B := (refinementParent_eq_iff hQP).2 (mem_filter.1
            (mem_product.1 hUW).2).2
          simpa only [parent, hpU, hpW] using (hxloc UW.1 UW.2 (by
            dsimp [parent]; rw [hpU, hpW]; exact fun h ↦ hlt.ne (congrArg idx h))).2
            (A' ∩ UW.1.1) inter_subset_right (B' ∩ UW.2.1) inter_subset_right c'
        · rw [sum_add_distrib, ← mul_sum, hAB_card]
          exact (add_le_add le_rfl hirr_sum).trans (pairFineScale_err_le_subrect hδ hG (mod_cast
            card_univ_le_two_mul_parts_mul_card hP hPV A.2) (mod_cast
            card_univ_le_two_mul_parts_mul_card hP hPV B.2) hA's hB's)
      rw [isRegularPair_iff]; intro c' A' hA' B' hB' hA's hB's
      have h2τ1 : 2 * τ ≤ 1 := (by linarith [pairQuarterTol_le_quarter G t])
      have hfull := hrect_dev c' Subset.rfl Subset.rfl (mul_le_of_le_one_left (Nat.cast_nonneg _)
        h2τ1) (mul_le_of_le_one_left (Nat.cast_nonneg _) h2τ1)
      have hsub := hrect_dev c' hA' hB' ((mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg
        _)).trans hA's) ((mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)).trans hB's)
      have := abs_sub_le (pairColorDensity R c' A' B' : ℝ) (pairColorDensity S c' A.1 B.1)
        (pairColorDensity R c' A.1 B.1)
      rw [abs_sub_comm (pairColorDensity S c' A.1 B.1 : ℝ)] at this; linarith
    refine ⟨R, rfl, fun A hA B hB hAB ↦ ?_, ?_⟩
    · rcases lt_or_gt_of_ne (fun h ↦ hAB (congrArg Subtype.val (idx.injective h)) : idx ⟨A, hA⟩ ≠
          idx ⟨B, hB⟩) with hlt | hgt
      exacts [hR_reg_lt ⟨A, hA⟩ ⟨B, hB⟩ hlt, (hR_reg_lt ⟨B, hB⟩ ⟨A, hA⟩ hgt).symm]
    · let Elt := univ.filter fun p : {p : V × V // p.1 ≠ p.2} ↦ idx (cellP p.1.1) < idx (cellP
        p.1.2) ∧ R.color p ≠ S.color p
      let Egt := univ.filter fun p : {p : V × V // p.1 ≠ p.2} ↦ idx (cellP p.1.2) < idx (cellP
        p.1.1) ∧ R.color p ≠ S.color p
      have htot : #{p | R.color p ≠ S.color p} ≤ 2 * #Elt := by
        have hsub : (univ.filter fun p ↦ R.color p ≠ S.color p) ⊆ Elt ∪ Egt := fun p hp ↦ by
          have hne := (mem_filter.1 hp).2
          rcases lt_trichotomy (idx (cellP p.1.1)) (idx (cellP p.1.2)) with hlt | heq | hgt
          · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hlt, hne⟩)
          · exact absurd (by simp [R, heq]) hne
          · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, hgt, hne⟩)
        have hmap_eq : Egt.map pairSwap.toEmbedding = Elt := by
          ext p; rw [mem_map_equiv]
          have hcol : R.color (pairSwap p) = S.color (pairSwap p) ↔ R.color p = S.color p := by
            rw [R.color_pairSwap, S.color_pairSwap]; exact S.rev_involutive.injective.eq_iff
          simp only [Egt, Elt, mem_filter, mem_univ, true_and, pairSwap_symm, coe_pairSwap,
            Prod.fst_swap, Prod.snd_swap, ne_eq, hcol]
        exact (card_le_card hsub).trans ((card_union_le _ _).trans_eq
          (by rw [← hmap_eq, card_map, two_mul]))
      let Fpairs := univ.filter fun UW : Q.parts × Q.parts ↦ idx (parent UW.1) < idx (parent UW.2)
      have hElt_le : #Elt ≤ ∑ UW ∈ Fpairs, #{q ∈ UW.1.1 ×ˢ UW.2.1 | xloc UW.1 UW.2 q ≠ x₀ q} := by
        have himg : Elt.image Subtype.val ⊆ Fpairs.biUnion (fun UW ↦ {q ∈ UW.1.1 ×ˢ UW.2.1 | xloc
            UW.1 UW.2 q ≠ x₀ q}) := by
          intro q hq; obtain ⟨p, hp, rfl⟩ := mem_image.1 hq; obtain ⟨-, hlt, hne⟩ := mem_filter.1 hp
          exact mem_biUnion.2 ⟨(cellQ p.1.1, cellQ p.1.2), mem_filter.2 ⟨mem_univ _,
            by rwa [hcellQ_parent, hcellQ_parent]⟩, mem_filter.2 ⟨mem_product.2 ⟨Q.mem_part_self.2
            (mem_univ _), Q.mem_part_self.2 (mem_univ _)⟩, by simpa [R, hlt, x₀, p.2] using hne⟩⟩
        exact (card_image_of_injective Elt Subtype.val_injective).symm.trans_le ((card_le_card
          himg).trans card_biUnion_le)
      have hblk_disj : (Fpairs : Set (Q.parts × Q.parts)).PairwiseDisjoint (fun UW ↦ UW.1.1 ×ˢ
          UW.2.1) := fun UW₁ _ UW₂ _ hne ↦ by
        refine disjoint_product.2 ?_; by_cases hf : UW₁.1 = UW₂.1
        · exact Or.inr (Q.disjoint UW₁.2.2 UW₂.2.2 fun e ↦ hne (Prod.ext hf (Subtype.ext e)))
        · exact Or.inl (Q.disjoint UW₁.1.2 UW₂.1.2 fun e ↦ hf (Subtype.ext e))
      have hblk_off : Fpairs.biUnion (fun UW ↦ UW.1.1 ×ˢ UW.2.1) ⊆ (univ : Finset V).offDiag := by
        intro q hq; obtain ⟨UW, hUW, hqUW⟩ := mem_biUnion.1 hq
        have hdisj : Disjoint (parent UW.1).1 (parent UW.2).1 := P.disjoint (parent UW.1).2 (parent
          UW.2).2 fun e ↦ (mem_filter.1 hUW).2.ne (congrArg idx (Subtype.ext e))
        have hdUW := hdisj.mono (le_refinementParent hQP UW.1) (le_refinementParent hQP UW.2)
        exact mem_offDiag.2 ⟨mem_univ _, mem_univ _, hdUW.forall_ne_finset (mem_product.1 hqUW).1
          (mem_product.1 hqUW).2⟩
      have hcard_le : ∑ UW ∈ Fpairs, ((#UW.1.1 * #UW.2.1 : ℕ) : ℝ) ≤ (n : ℝ) ^ 2 := by
        rw [← Nat.cast_sum, show ∑ UW ∈ Fpairs, (#UW.1.1 * #UW.2.1) = #(Fpairs.biUnion fun UW ↦
          UW.1.1 ×ˢ UW.2.1) by rw [card_biUnion hblk_disj]; simp [card_product]]
        exact_mod_cast (card_le_card (subset_univ _)).trans_eq
          (by rw [card_univ, Fintype.card_prod, ← sq])
      have hdev_le : ∑ UW ∈ Fpairs, ∑ c, |(pairColorDensity S c UW.1.1 UW.2.1 : ℝ) -
            pairColorDensity S c (parent UW.1).1 (parent UW.2).1| * (#UW.1.1 * #UW.2.1 : ℕ) ≤ (δ /
            8) * (n : ℝ) ^ 2 := by
        rw [sum_comm]; refine (sum_le_sum (g := fun _ ↦ √γ * (n : ℝ) ^ 2) fun c _ ↦ ?_).trans ?_
        · have hpt (UW : Q.parts × Q.parts) : |(pairColorDensity S c UW.1.1 UW.2.1 : ℝ) -
              pairColorDensity S c (parent UW.1).1 (parent UW.2).1| * (#UW.1.1 * #UW.2.1 : ℕ) = ∑ p
              ∈ UW.1.1 ×ˢ UW.2.1, |(pairColorDensity S c (Q.part p.1) (Q.part p.2) : ℝ) -
              pairColorDensity S c (P.part p.1) (P.part p.2)| := by
            rw [← nsmul_eq_mul', ← card_product, ← sum_const]; refine sum_congr rfl fun p hp ↦ ?_
            obtain ⟨hp1, hp2⟩ := mem_product.1 hp
            rw [Q.part_eq_of_mem UW.1.2 hp1, Q.part_eq_of_mem UW.2.2 hp2, P.part_eq_of_mem (parent
              UW.1).2 (le_refinementParent hQP UW.1 hp1), P.part_eq_of_mem (parent UW.2).2
              (le_refinementParent hQP UW.2 hp2)]
          simp_rw [hpt]; rw [← sum_biUnion hblk_disj]
          exact (sum_le_sum_of_subset_of_nonneg hblk_off fun _ _ _ ↦ abs_nonneg _).trans
            (S.sum_abs_pairColorDensity_sub_le hQP hgap c)
        · rw [sum_const, card_univ, nsmul_eq_mul]; dsimp only [γ, pairEnergyGap]
          rw [sqrt_sq (div_nonneg (le_min hδ.le zero_le_one) (by positivity)), ← mul_assoc]
          exact mul_le_mul_of_nonneg_right ((mul_le_mul (by linarith : (q₂ : ℝ) ≤ q₂ + 1)
            (div_le_div_of_nonneg_right (min_le_left _ _) (by positivity)) (div_nonneg (le_min
            hδ.le zero_le_one) (by positivity)) (by positivity)).trans_eq (by field_simp))
            (sq_nonneg _)
      have hξ_term : 2 * (q₂ : ℝ) * ξ₀ * ∑ UW ∈ Fpairs, ((#UW.1.1 * #UW.2.1 : ℕ) : ℝ) ≤ (δ / 4) *
          (n : ℝ) ^ 2 := by
        refine (mul_le_mul_of_nonneg_left hcard_le (by positivity)).trans
          (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
        have hqξ : (q₂ : ℝ) * ξ₀ ≤ ξ_P := by
          rw [mul_div_left_comm]
          exact mul_le_of_le_one_right hξP_pos.le (div_le_one_of_le₀ (by linarith) (by positivity))
        have hξδ : ξ_P ≤ δ / 8 := (min_le_left _ _).trans ((div_le_div_of_nonneg_right
          (min_le_left _ _) (by positivity)).trans (div_le_div_of_nonneg_left hδ.le (by norm_num)
          (by linarith [Nat.cast_nonneg (α := ℝ) q₂])))
        linarith
      have hsum_loc := (sum_le_sum (s := Fpairs) (g := fun UW ↦ ∑ c, |(pairColorDensity S c UW.1.1
          UW.2.1 : ℝ) - pairColorDensity S c (parent UW.1).1 (parent UW.2).1| * (#UW.1.1 * #UW.2.1
          : ℕ) + 2 * q₂ * ξ₀ * (#UW.1.1 * #UW.2.1 : ℕ)) fun UW hUW ↦ by
        have hed := (hxloc UW.1 UW.2 fun h ↦ (mem_filter.1 hUW).2.ne (congrArg idx h)).1
        rw [← sum_mul]; linarith :
        ∑ UW ∈ Fpairs, 2 * (#{q ∈ UW.1.1 ×ˢ UW.2.1 | xloc UW.1 UW.2 q ≠ x₀ q} : ℝ) ≤ _)
      rw [← mul_sum, sum_add_distrib, ← mul_sum] at hsum_loc
      have h2 : (#{p | R.color p ≠ S.color p} : ℝ) ≤ 2 * ∑ UW ∈ Fpairs, (#{q ∈ UW.1.1 ×ˢ UW.2.1 |
          xloc UW.1 UW.2 q ≠ x₀ q} : ℝ) := by
        rw [← Nat.cast_sum]; exact_mod_cast htot.trans (Nat.mul_le_mul_left 2 hElt_le)
      linarith
  have hlarge_diag (A : Finset V) (hA : A ∈ P.parts) : 1 < 4 * τ * #A := by
    obtain ⟨u, huA⟩ := P.nonempty_of_mem_parts hA; obtain ⟨U, hUQ, huU⟩ := Q.exists_mem (mem_univ u)
    obtain ⟨A', hA', hUA'⟩ := hQP hUQ; rw [P.eq_of_mem_parts hA' hA (hUA' huU) huA] at hUA'
    have hξP_le : ξ_P ≤ τ ^ 3 := (min_le_right _ _).trans <| div_le_self (by positivity) <| by
      have : 0 ≤ 15 + 16 * (q₂ : ℝ) + 16 * (q₂ + 1) * (2 * (t : ℝ) + (t : ℝ) ^ 2) := by positivity
      linarith
    have hξ₀_le : ξ₀ ≤ 2 * τ := by
      have h1 : ξ₀ ≤ ξ_P := div_le_self hξP_pos.le (by linarith [Nat.cast_nonneg (α := ℝ) q₂])
      nlinarith [pairQuarterTol_le_quarter G t, sq_nonneg τ]
    have hξ₀2 : ξ₀ ^ 2 ≤ 4 * τ := (pow_le_pow_left₀ (by positivity) hξ₀_le 2).trans
      (by nlinarith [pairQuarterTol_le_quarter G t])
    exact (by linarith [Nat.cast_nonneg (α := ℝ) q₂] : (1 : ℝ) < q₂ + 3).trans_le ((hU_large U
      hUQ).trans (mul_le_mul hξ₀2 (mod_cast card_le_card hUA') (Nat.cast_nonneg _) (by
      positivity)))
  have hdiag_edits : (#{p | (R.fillDiagonal P).color p ≠ some (R.color p)} : ℝ) ≤ (δ / 4) * (n : ℝ)
      ^ 2 := by
    have himg : ({p | (R.fillDiagonal P).color p ≠ some (R.color p)} : Finset _).image Subtype.val
        ⊆ (univ : Finset (V × V)).filter fun p ↦ (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
        (R.colorOfPair p.1 p.2).map some := by
      intro q hq; obtain ⟨p, hp, rfl⟩ := mem_image.1 hq; refine mem_filter.2 ⟨mem_univ _, ?_⟩
      rw [(R.fillDiagonal P).colorOfPair_of_ne p.2, R.colorOfPair_of_ne p.2]
      simpa using (mem_filter.1 hp).2
    have hcard_le : #{p | (R.fillDiagonal P).color p ≠ some (R.color p)} ≤ (n / t + 1) * n :=
      (card_image_of_injective _ Subtype.val_injective).symm.trans_le ((card_le_card himg).trans <|
      R.card_fillDiagonal_colorOfPair_ne_le_of_card_le P fun A hA ↦
      by simpa [card_univ, n, t] using hP.card_part_le_average_add_one hA)
    have h8t : (8 : ℝ) ≤ δ * t := hl₀.trans (mul_le_mul_of_nonneg_left (mod_cast card_mono hPP₀)
      hδ.le)
    have ht_pos : (0 : ℝ) < t := by
      by_contra! h; nlinarith [mul_nonpos_of_nonneg_of_nonpos hδ.le h]
    have hdiv_le : ((n / t : ℕ) : ℝ) ≤ (δ / 8) * n := by
      have h1 : ((n / t : ℕ) : ℝ) * t ≤ n := mod_cast Nat.div_mul_le_self n t
      linarith [le_of_mul_le_mul_right (by nlinarith : (8 * ((n / t : ℕ) : ℝ)) * t ≤ (δ * n) * t)
        ht_pos]
    exact (mod_cast hcard_le : _ ≤ (((n / t : ℕ) : ℝ) + 1) * n).trans ((mul_le_mul_of_nonneg_right
      (add_le_add hdiv_le (by linarith : (1 : ℝ) ≤ (δ / 8) * n)) (Nat.cast_nonneg _)).trans_eq (by
      ring))
  refine ⟨P, R.fillDiagonal P, hPP₀, hP, hPbound, funext (fun c ↦ (R.fillDiagonal_rev P c).trans
    (by rw [hR_rev])), (R.isPairColorRegular_fillDiagonal P hlarge_diag hR_reg).mono
    (four_mul_pairQuarterTol_le G t), ?_⟩
  have hsub : (univ.filter fun p ↦ (R.fillDiagonal P).color p ≠ some (S.color p)) ⊆ (univ.filter
      fun p ↦ R.color p ≠ S.color p) ∪ (univ.filter fun p ↦ (R.fillDiagonal P).color p ≠ some
      (R.color p)) := fun p hp ↦ by
    by_cases hRS : R.color p = S.color p
    · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, by rw [hRS]; exact (mem_filter.1 hp).2⟩)
    · exact mem_union_left _ (mem_filter.2 ⟨mem_univ _, hRS⟩)
  have htot : (#{p | (R.fillDiagonal P).color p ≠ some (S.color p)} : ℝ) ≤ (#{p | R.color p ≠
      S.color p} : ℝ) + (#{p | (R.fillDiagonal P).color p ≠ some (R.color p)} : ℝ) := mod_cast
      (card_le_card hsub).trans (card_union_le _ _)
  linarith [mul_nonneg hδ.le (sq_nonneg (n : ℝ))]
end PairColorSystem
end TauCeti
