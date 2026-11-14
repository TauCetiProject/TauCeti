/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Cleanup
public import TauCeti.Combinatorics.Hypergraph.PairColor.StrongRegularization
import TauCeti.Combinatorics.Enumerative.CoupledColoring
import TauCeti.Combinatorics.Regularity.Partition.Equitabilise
import TauCeti.Data.Finset.Basic

/-!
# Scheduled regular approximation of pair-color systems

Given a pair-color system `S : PairColorSystem κ V`, an equipartition `P₀` of `V`, an edit budget
`α > 0`, and an arbitrary positive error schedule `F : ℕ → ℝ`, we construct a refining equipartition
`P ≤ P₀` (with `#P.parts` bounded independently of `|V|`) and a recolored pair-color system
`T : PairColorSystem (Option κ) V` such that:

* `(⟨P, T⟩ : PairSkeleton3 (Option κ) V)` satisfies `PairSkeleton3.LowerSkeletonRegular F`, i.e.
  every pair of cells of `P` (diagonal included) is `F (#P.parts + card κ + 1)`-regular;
* at most `α |V|²` ordered vertex pairs have `T.colorOfPair x y ≠ (S.colorOfPair x y).map some`.

Unlike single-tolerance Szemerédi regularization followed by
`PairColorSystem.exists_recoloring_isPairColorRegular`, here the edit budget `α` is independent of
the scheduled tolerance `F (#P.parts + card κ + 1)`. Achieving both simultaneously uses the strong
regularity pair `Q ≤ P` from `PairColorSystem.exists_strong_refining_equipartition`:

1. Presplit `P₀` into `max ⌈4 / α⌉ 1 · #P₀.parts` equitable cells `P₁` so within-cell pairs occupy
   at most `(α / 4) |V|²` ordered pairs.
2. Choose `Q ≤ P ≤ P₁` with energy gap `S.energy Q - S.energy P ≤ α² / (4 (card κ + 1))` and fine
   regularity `η = Φ #P.parts` small enough relative to `ε = min (F (#P.parts + card κ + 1) / 2) …`.
3. On each `η`-regular fine block `B ×ˢ D` whose coarse parents `A ≠ C` in `P` are distinct, apply
   coupled recoloring (`TauCeti.exists_coupled_recoloring_abs_card_filter_sub_lt`) toward the
   coarse density `pairColorDensity S · A C`. By
   `PairColorSystem.sum_abs_pairColorDensity_sub_mul_card_le`, the total `L¹` edit cost across all
   fine blocks is at most `(α / 2) |V|²`.
4. Aggregate fine rectangle discrepancies via
   `PairColorSystem.abs_card_filter_colorOfPair_sub_le_of_refines` to make `R` `ε`-regular on `P`
   outside at most `(α / 4) |V|²` ordered pairs, and finish with
   `PairColorSystem.exists_recoloring_isPairColorRegular` to clean up irregular off-diagonal
   and diagonal blocks at edit cost at most `(α / 2) |V|²`.

## Main definitions

* `TauCeti.pairRegularApproximationPartBound`: upper bound on `#P.parts` in the scheduled regular
  approximation lemma.
* `TauCeti.pairRegularApproximationBound`: host-size threshold ensuring all fine cells are large
  enough for the probabilistic union bound and diagonal cleanup.

## Main results

* `TauCeti.PairColorSystem.exists_coupled_recoloring_abs_card_filter_colorOfPair_sub_le`: coupled
  recoloring on a single `η`-regular disjoint pair `(s, t)`.
* `TauCeti.PairColorSystem.exists_equipartition_lowerSkeletonRegular`: scheduled regular
  approximation of a pair-color system with edit budget `α |V|²`.

## References

* N. Alon, E. Fischer, M. Krivelevich, and M. Szegedy, *Efficient testing of large graphs*,
  Combinatorica 20 (2000), 451–476.
* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), Theorem 2.5 (regular approximation lemma).
-/

public section

open Finset Finpartition Real

namespace TauCeti

/-- Target off-diagonal cleanup tolerance at `k` coarse vertex cells and base palette size `K` for
edit budget `α` and schedule `F`. -/
noncomputable def pairApproxEps (α : ℝ) (F : ℕ → ℝ) (K k : ℕ) : ℝ :=
  min (F (k + (K + 1)) / 2) (min (α / 8) 1)

/-- Unfolding lemma for `TauCeti.pairApproxEps`. -/
theorem pairApproxEps_def (α : ℝ) (F : ℕ → ℝ) (K k : ℕ) :
    pairApproxEps α F K k = min (F (k + (K + 1)) / 2) (min (α / 8) 1) :=
  (rfl)

/-- Fine regularity schedule passed to `strongPairColorRegularityBound` during pair-color regular
approximation. -/
noncomputable def pairApproxSchedule (α : ℝ) (F : ℕ → ℝ) (K k : ℕ) : ℝ :=
  pairApproxEps α F K k ^ 4 / (8 * (K + 1))

/-- Unfolding lemma for `TauCeti.pairApproxSchedule`. -/
theorem pairApproxSchedule_def (α : ℝ) (F : ℕ → ℝ) (K k : ℕ) :
    pairApproxSchedule α F K k = pairApproxEps α F K k ^ 4 / (8 * (K + 1)) :=
  (rfl)

private theorem pairApproxEps_pos {α : ℝ} (hα : 0 < α) {F : ℕ → ℝ} (hF : ∀ m, 0 < F m)
    (K k : ℕ) : 0 < pairApproxEps α F K k := by
  unfold pairApproxEps
  refine lt_min (half_pos (hF _)) (lt_min (by positivity) zero_lt_one)

private theorem pairApproxEps_le_one (α : ℝ) (F : ℕ → ℝ) (K k : ℕ) :
    pairApproxEps α F K k ≤ 1 :=
  (min_le_right _ _).trans (min_le_right _ _)

private theorem pairApproxEps_le_div_eight (α : ℝ) (F : ℕ → ℝ) (K k : ℕ) :
    pairApproxEps α F K k ≤ α / 8 :=
  (min_le_right _ _).trans (min_le_left _ _)

private theorem two_mul_pairApproxEps_le (α : ℝ) (F : ℕ → ℝ) (K k : ℕ) :
    2 * pairApproxEps α F K k ≤ F (k + (K + 1)) := by
  have h : pairApproxEps α F K k ≤ F (k + (K + 1)) / 2 := min_le_left _ _
  linarith

private theorem pairApproxSchedule_pos {α : ℝ} (hα : 0 < α) {F : ℕ → ℝ} (hF : ∀ m, 0 < F m)
    (K k : ℕ) : 0 < pairApproxSchedule α F K k := by
  have hε := pairApproxEps_pos hα hF K k
  unfold pairApproxSchedule
  positivity

/-- Upper bound on the number of vertex cells produced by
`PairColorSystem.exists_equipartition_lowerSkeletonRegular` starting from `k₀` cells, with edit
budget `α`, schedule `F`, and base palette size `K`. -/
noncomputable def pairRegularApproximationPartBound (α : ℝ) (F : ℕ → ℝ) (K k₀ : ℕ) : ℕ :=
  strongPairColorRegularityBound (α ^ 2 / (4 * (K + 1))) (pairApproxSchedule α F K)
    (max ⌈4 / α⌉₊ 1 * k₀)

/-- Unfolding lemma for `TauCeti.pairRegularApproximationPartBound`. -/
theorem pairRegularApproximationPartBound_def (α : ℝ) (F : ℕ → ℝ) (K k₀ : ℕ) :
    pairRegularApproximationPartBound α F K k₀ =
      strongPairColorRegularityBound (α ^ 2 / (4 * (K + 1))) (pairApproxSchedule α F K)
        (max ⌈4 / α⌉₊ 1 * k₀) :=
  (rfl)

/-- `pairRegularApproximationPartBound α F K` is monotone in the initial cell count `k₀`. -/
theorem monotone_pairRegularApproximationPartBound (α : ℝ) (F : ℕ → ℝ) (K : ℕ) :
    Monotone (pairRegularApproximationPartBound α F K) := fun _ _ hab ↦
  monotone_strongPairColorRegularityBound _ _ (Nat.mul_le_mul_left _ hab)

/-- Host-size threshold for `PairColorSystem.exists_equipartition_lowerSkeletonRegular` starting
from at most `k₀` cells. -/
noncomputable def pairRegularApproximationBound (α : ℝ) (F : ℕ → ℝ) (K k₀ : ℕ) : ℕ :=
  let M := pairRegularApproximationPartBound α F K k₀
  let ηmin := ((Iic M).image (pairApproxSchedule α F K)).min'
    (Nonempty.image ⟨0, mem_Iic.2 (Nat.zero_le M)⟩ _)
  max M 1 * (⌈(K + 2 : ℝ) / ηmin ^ 2⌉₊ + 1)

/-- Unfolding lemma for `TauCeti.pairRegularApproximationBound`. -/
theorem pairRegularApproximationBound_def (α : ℝ) (F : ℕ → ℝ) (K k₀ : ℕ) :
    pairRegularApproximationBound α F K k₀ =
      let M := pairRegularApproximationPartBound α F K k₀
      let ηmin := ((Iic M).image (pairApproxSchedule α F K)).min'
        (Nonempty.image ⟨0, mem_Iic.2 (Nat.zero_le M)⟩ _)
      max M 1 * (⌈(K + 2 : ℝ) / ηmin ^ 2⌉₊ + 1) :=
  (rfl)

/-- `pairRegularApproximationBound α F K` is monotone in `k₀` whenever `α > 0` and `F > 0`. -/
theorem monotone_pairRegularApproximationBound {α : ℝ} (hα : 0 < α) {F : ℕ → ℝ}
    (hF : ∀ m, 0 < F m) (K : ℕ) :
    Monotone (pairRegularApproximationBound α F K) := by
  intro k₁ k₂ hk
  have hM := monotone_pairRegularApproximationPartBound α F K hk
  set M₁ := pairRegularApproximationPartBound α F K k₁
  set M₂ := pairRegularApproximationPartBound α F K k₂
  set s₁ := (Iic M₁).image (pairApproxSchedule α F K)
  set s₂ := (Iic M₂).image (pairApproxSchedule α F K)
  have hs₁ : s₁.Nonempty := Nonempty.image ⟨0, mem_Iic.2 (Nat.zero_le M₁)⟩ _
  have hs₂ : s₂.Nonempty := Nonempty.image ⟨0, mem_Iic.2 (Nat.zero_le M₂)⟩ _
  have hsub : s₁ ⊆ s₂ := image_subset_image (Iic_subset_Iic.2 hM)
  have hmin_le : s₂.min' hs₂ ≤ s₁.min' hs₁ := min'_subset hs₁ hsub
  obtain ⟨m, -, hm⟩ := mem_image.1 (min'_mem s₂ hs₂)
  have hmin_pos : 0 < s₂.min' hs₂ := hm ▸ pairApproxSchedule_pos hα hF K m
  have hdiv : (K + 2 : ℝ) / (s₁.min' hs₁) ^ 2 ≤ (K + 2 : ℝ) / (s₂.min' hs₂) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hmin_pos)
      (pow_le_pow_left₀ hmin_pos.le hmin_le 2)
  rw [pairRegularApproximationBound_def, pairRegularApproximationBound_def]
  exact Nat.mul_le_mul (max_le_max_right 1 hM) (Nat.add_le_add_right (Nat.ceil_mono hdiv) 1)

namespace PairColorSystem

variable {κ V : Type*}

/-! ### Local coupled recoloring on a single regular pair -/

section LocalCoupledRecoloring

private theorem cast_card_pos_of_add_two_le [Fintype κ] {η : ℝ} {u : Finset V}
    (h : Fintype.card κ + 2 ≤ η ^ 2 * #u) : (0 : ℝ) < #u := by
  by_contra! h'
  have : η ^ 2 * #u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg η) h'
  linarith [(Nat.cast_nonneg (Fintype.card κ) : (0 : ℝ) ≤ _)]

/-- The union bound for coupled recoloring on `s ×ˢ t` succeeds once `card κ + 2 ≤ η² #s` and
`card κ + 2 ≤ η² #t`. -/
private theorem two_mul_pow_add_one_mul_exp_lt [Fintype κ] [Nonempty κ] {η : ℝ} {s t : Finset V}
    (hs : Fintype.card κ + 2 ≤ η ^ 2 * #s) (ht : Fintype.card κ + 2 ≤ η ^ 2 * #t) :
    2 * (2 ^ #s * 2 ^ #t + 1 : ℕ) * Fintype.card κ *
      exp (-2 * (η * #s * #t) ^ 2 / (#s * #t : ℕ)) < 1 := by
  have hm := cast_card_pos_of_add_two_le hs
  have hn := cast_card_pos_of_add_two_le ht
  have h2 : (2 : ℝ) ≤ exp 1 := by linarith [add_one_le_exp (1 : ℝ)]
  have hpow (k : ℕ) : (2 : ℝ) ^ k ≤ exp k :=
    (pow_le_pow_left₀ (by norm_num) h2 k).trans_eq (by rw [← exp_nat_mul, mul_one])
  have h1le : (1 : ℝ) ≤ (2 : ℝ) ^ #s * (2 : ℝ) ^ #t :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have hcard : 2 * ((2 ^ #s * 2 ^ #t + 1 : ℕ) : ℝ) ≤ exp 1 * exp 1 * (exp #s * exp #t) := by
    have h4 : 2 * ((2 ^ #s * 2 ^ #t + 1 : ℕ) : ℝ) ≤ 2 * 2 * ((2 : ℝ) ^ #s * (2 : ℝ) ^ #t) := by
      push_cast
      linarith
    exact h4.trans (by gcongr <;> exact hpow _)
  have hKexp : (Fintype.card κ : ℝ) ≤ exp (Fintype.card κ - 1) := by
    linarith [add_one_le_exp ((Fintype.card κ : ℝ) - 1)]
  have hexp : -2 * (η * #s * #t) ^ 2 / ((#s * #t : ℕ) : ℝ) = -2 * (η ^ 2 * #s) * #t := by
    push_cast
    field_simp
  calc 2 * ((2 ^ #s * 2 ^ #t + 1 : ℕ) : ℝ) * Fintype.card κ *
        exp (-2 * (η * #s * #t) ^ 2 / (#s * #t : ℕ))
      ≤ (exp 1 * exp 1 * (exp #s * exp #t)) * exp (Fintype.card κ - 1) *
          exp (-2 * (η ^ 2 * #s) * #t) := by
        rw [hexp]
        gcongr
    _ = exp (#s + #t + Fintype.card κ + 1 - 2 * (η ^ 2 * #s) * #t) := by
        simp only [← exp_add]
        ring_nf
    _ < 1 := by
        rw [exp_lt_one_iff, sub_neg]
        have hm1 : (1 : ℝ) ≤ #s := Nat.one_le_cast.2 (Nat.cast_pos.1 hm)
        have hK1 : (1 : ℝ) ≤ Fintype.card κ := Nat.one_le_cast.2 Fintype.card_pos
        nlinarith [mul_le_mul_of_nonneg_right hs hn.le, mul_le_mul_of_nonneg_right ht hm.le]

open Classical in
/-- Sum the rectangle count deviations of an `η`-regular pair `(s, t)` over all palette colors. -/
private theorem sum_abs_card_filter_colorOfPair_sub_le [Fintype κ] (S : PairColorSystem κ V)
    {s t s' t' : Finset V} (hst : Disjoint s t) {η : ℝ} (hreg : S.IsRegularPair η s t)
    (hs' : s' ⊆ s) (ht' : t' ⊆ t) :
    ∑ c₀, |(#{q ∈ s' ×ˢ t' | S.colorOfPair q.1 q.2 = some c₀} : ℝ) -
      pairColorDensity S c₀ s t * (#s' * #t')| ≤ Fintype.card κ * (η * #s * #t) :=
  calc ∑ c₀, |(#{q ∈ s' ×ˢ t' | S.colorOfPair q.1 q.2 = some c₀} : ℝ) -
          pairColorDensity S c₀ s t * (#s' * #t')|
      ≤ ∑ _c₀ : κ, (η * #s * #t) := sum_le_sum fun c₀ _ ↦ by
          rw [← mul_assoc]
          exact hreg.abs_card_filter_colorOfPair_sub_le hst hs' ht'
    _ = Fintype.card κ * (η * #s * #t) := by rw [sum_const, card_univ, nsmul_eq_mul]

open Classical in
/-- **Coupled recoloring of an `η`-regular pair.** Let `(s, t)` be a disjoint `η`-regular pair for
`S` with `card κ + 2 ≤ η² #s` and `card κ + 2 ≤ η² #t`, and let `p` be a probability distribution
on `κ`. There is a pair-color system `S'` with the reversal of `S`, agreeing with `S` outside
`s ×ˢ t ∪ t ×ˢ s`, such that:

* on every subrectangle `s' ×ˢ t' ⊆ s ×ˢ t`, the count of color `c` deviates from
  `p c * (#s' * #t')` by at most `2 · card κ · η · (#s * #t)`;
* the number of pairs in `s ×ˢ t` whose color changes is at most
  `((∑ c, |d_S(c, s, t) - p c|) / 2 + card κ · η) · (#s * #t)`. -/
theorem exists_coupled_recoloring_abs_card_filter_colorOfPair_sub_le [Fintype κ]
    (S : PairColorSystem κ V) {s t : Finset V} (hst : Disjoint s t) {η : ℝ} (hη : 0 < η)
    (hreg : S.IsRegularPair η s t) (hs : Fintype.card κ + 2 ≤ η ^ 2 * #s)
    (ht : Fintype.card κ + 2 ≤ η ^ 2 * #t) {p : κ → ℝ} (hp : ∀ c, 0 ≤ p c)
    (hp1 : ∑ c, p c = 1) :
    ∃ S' : PairColorSystem κ V, S'.rev = S.rev ∧
      (∀ u v, (u ∈ s → v ∉ t) → (u ∈ t → v ∉ s) → S'.colorOfPair u v = S.colorOfPair u v) ∧
      (∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t,
        |(#{q ∈ s' ×ˢ t' | S'.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#s' * #t')| ≤
          2 * Fintype.card κ * η * (#s * #t)) ∧
      (#{q ∈ s ×ˢ t | S'.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        ((∑ c, |(pairColorDensity S c s t : ℝ) - p c|) / 2 + Fintype.card κ * η) *
          (#s * #t) := by
  have : Nonempty κ := by
    by_contra! h
    simp at hp1
  have hs0 := cast_card_pos_of_add_two_le hs
  have ht0 := cast_card_pos_of_add_two_le ht
  let x₀ : V × V → κ := fun q ↦ if h : q.1 ≠ q.2 then S.color ⟨q, h⟩ else Classical.arbitrary κ
  have hx₀ {u v : Finset V} (hu : u ⊆ s) (hv : v ⊆ t) (c : κ) :
      {q ∈ u ×ˢ v | x₀ q = c} = {q ∈ u ×ˢ v | S.colorOfPair q.1 q.2 = some c} :=
    filter_congr fun q hq ↦ by
      have hne := hst.forall_ne_finset (hu (mem_product.1 hq).1) (hv (mem_product.1 hq).2)
      simp [x₀, hne]
  let p₀ : κ → ℝ := fun c ↦ pairColorDensity S c s t
  have hp₀ (c : κ) : 0 ≤ p₀ c := Rat.cast_nonneg.2 (pairColorDensity_nonneg S c s t)
  have hp₀1 : ∑ c, p₀ c = 1 := by
    dsimp only [p₀]
    rw [← Rat.cast_sum, sum_pairColorDensity S s t
      ((filter_ne_product_of_disjoint hst).symm ▸
        (card_pos.1 (Nat.cast_pos.1 hs0)).product (card_pos.1 (Nat.cast_pos.1 ht0))),
      Rat.cast_one]
  obtain ⟨x, -, hdisc, hedit⟩ := exists_coupled_recoloring_abs_card_filter_sub_lt x₀ (s ×ˢ t)
    hp₀ hp₀1 hp hp1 (I := ↥(s.powerset ×ˢ t.powerset)) (fun i ↦ i.1.1 ×ˢ i.1.2)
    (fun i ↦ product_subset_product (mem_powerset.1 (mem_product.1 i.2).1)
      (mem_powerset.1 (mem_product.1 i.2).2))
    (N := #s * #t) (card_product s t).le (b := η * #s * #t) (mul_pos (mul_pos hη hs0) ht0)
    (by simpa [Fintype.card_coe] using two_mul_pow_add_one_mul_exp_lt hs ht)
  refine ⟨S.recolorProduct hst x, S.recolorProduct_rev hst x,
    fun u v ↦ colorOfPair_recolorProduct_of_not_mem hst x, fun c s' hs' t' ht' ↦ ?_, ?_⟩
  · have hrect := hdisc ⟨(s', t'), mem_product.2 ⟨mem_powerset.2 hs', mem_powerset.2 ht'⟩⟩ c
    dsimp only at hrect
    simp_rw [card_product, Nat.cast_mul, hx₀ hs' ht'] at hrect
    have hold := S.sum_abs_card_filter_colorOfPair_sub_le hst hreg hs' ht'
    have hnew : {q ∈ s' ×ˢ t' | (S.recolorProduct hst x).colorOfPair q.1 q.2 = some c} =
        {q ∈ s' ×ˢ t' | x q = c} := filter_congr fun ⟨u, v⟩ hq ↦ by
      rw [colorOfPair_recolorProduct_of_mem hst x (product_subset_product hs' ht' hq),
        Option.some_inj]
    rw [hnew, mul_assoc (2 * (Fintype.card κ : ℝ))]
    linarith
  · have heq : {q ∈ s ×ˢ t | (S.recolorProduct hst x).colorOfPair q.1 q.2 ≠
        S.colorOfPair q.1 q.2} = {q ∈ s ×ˢ t | x q ≠ x₀ q} := filter_congr fun ⟨u, v⟩ hq ↦ by
      have hne := hst.forall_ne_finset (mem_product.1 hq).1 (mem_product.1 hq).2
      rw [colorOfPair_recolorProduct_of_mem hst x hq, colorOfPair_of_ne S hne]
      simp [x₀, hne]
    have hzero : ∑ c₀, |(#{q ∈ s ×ˢ t | x₀ q = c₀} : ℝ) - p₀ c₀ * #(s ×ˢ t)| = 0 :=
      sum_eq_zero fun c₀ _ ↦ by
        have hc : (#{q ∈ s ×ˢ t | S.colorOfPair q.1 q.2 = some c₀} : ℝ) =
            pairColorDensity S c₀ s t * (#s * #t) :=
          mod_cast (pairColorDensity_mul_card_of_disjoint S c₀ hst).symm
        simp [hx₀ subset_rfl subset_rfl, p₀, hc, card_product]
    rw [hzero, add_zero, card_product, Nat.cast_mul] at hedit
    linarith [congrArg (fun u ↦ (#u : ℝ)) heq]

end LocalCoupledRecoloring

/-! ### Cellwise coupled recoloring across a strong pair `(P, Q)` -/

section CellwiseCoupledRecoloring

private theorem card_filter_colorOfPair_ne_comm [DecidableEq κ]
    {R S : PairColorSystem κ V} (hrev : R.rev = S.rev) (s t : Finset V) :
    #{q ∈ s ×ˢ t | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
      #{q ∈ t ×ˢ s | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} := by
  refine card_equiv (Equiv.prodComm V V) fun q ↦ ?_
  simp only [mem_filter, mem_product, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, and_comm]
  refine and_congr_right fun _ ↦ not_congr ?_
  rw [R.colorOfPair_swap q.2 q.1, S.colorOfPair_swap q.2 q.1, hrev]
  exact (Option.map_injective S.rev_involutive.injective).eq_iff

private theorem sum_abs_pairColorDensity_sub_swap [Fintype κ] (S : PairColorSystem κ V)
    (B D A C : Finset V) :
    ∑ c, |(pairColorDensity S c D B : ℝ) - pairColorDensity S c C A| =
      ∑ c, |(pairColorDensity S c B D : ℝ) - pairColorDensity S c A C| :=
  Fintype.sum_equiv S.rev_involutive.toPerm _ _ fun c ↦ by
    simp [Function.Involutive.toPerm, pairColorDensity_swap]

open Classical in
private theorem exists_local_coupled_recoloring [Fintype κ] [Fintype V]
    [DecidableEq V] (S : PairColorSystem κ V) {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P)
    {η : ℝ} (hη : 0 < η) (hsize : ∀ B ∈ Q.parts, Fintype.card κ + 2 ≤ η ^ 2 * #B)
    (B D : Q.parts) :
    ∃ T : PairColorSystem κ V, T.rev = S.rev ∧
      (refinementParent hQP B = refinementParent hQP D ∨ ¬S.IsRegularPair η B.1 D.1 → T = S) ∧
      (refinementParent hQP B ≠ refinementParent hQP D → S.IsRegularPair η B.1 D.1 →
        (∀ c, ∀ s' ⊆ B.1, ∀ t' ⊆ D.1,
          |(#{q ∈ s' ×ˢ t' | T.colorOfPair q.1 q.2 = some c} : ℝ) -
            pairColorDensity S c (refinementParent hQP B).1 (refinementParent hQP D).1 *
              (#s' * #t')| ≤
            2 * Fintype.card κ * η * (#B.1 * #D.1)) ∧
        (#{q ∈ B.1 ×ˢ D.1 | T.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
          ((∑ c, |(pairColorDensity S c B.1 D.1 : ℝ) -
              pairColorDensity S c (refinementParent hQP B).1 (refinementParent hQP D).1|) / 2 +
            Fintype.card κ * η) * (#B.1 * #D.1)) := by
  by_cases hskip : refinementParent hQP B = refinementParent hQP D ∨ ¬S.IsRegularPair η B.1 D.1
  · exact ⟨S, rfl, fun _ ↦ rfl, fun hne hreg ↦ (hskip.elim hne fun hn ↦ hn hreg).elim⟩
  push Not at hskip
  obtain ⟨hne, hreg⟩ := hskip
  set A := refinementParent hQP B
  set C := refinementParent hQP D
  have hACdisj : Disjoint A.1 C.1 := P.disjoint A.2 C.2 (Subtype.coe_injective.ne hne)
  have hBDdisj : Disjoint B.1 D.1 :=
    hACdisj.mono (le_refinementParent hQP B) (le_refinementParent hQP D)
  have hACne : ((A.1 ×ˢ C.1).filter fun q ↦ q.1 ≠ q.2).Nonempty := by
    rw [filter_ne_product_of_disjoint hACdisj]
    exact (P.nonempty_of_mem_parts A.2).product (P.nonempty_of_mem_parts C.2)
  obtain ⟨T, hrev, -, hdisc, hedit⟩ :=
    S.exists_coupled_recoloring_abs_card_filter_colorOfPair_sub_le hBDdisj hη hreg
      (hsize B.1 B.2) (hsize D.1 D.2)
      (p := fun c ↦ pairColorDensity S c A.1 C.1)
      (fun c ↦ mod_cast pairColorDensity_nonneg S c A.1 C.1)
      (mod_cast sum_pairColorDensity S A.1 C.1 hACne)
  exact ⟨T, hrev, fun h ↦ (h.elim hne fun hn ↦ hn hreg).elim, fun _ _ ↦ ⟨hdisc, hedit⟩⟩

open Classical in
/-- Edit bound on a single fine block `B ×ˢ D` when local coupled recolorings are glued along a
linear order on `Q.parts`. -/
private theorem card_edits_fine_block_le [Fintype κ] [DecidableEq κ] [Fintype V] [DecidableEq V]
    {S R : PairColorSystem κ V} (hRrev : R.rev = S.rev) {P Q : Finpartition (univ : Finset V)}
    (hQP : Q ≤ P) (order : LinearOrder Q.parts) (T : Q.parts → Q.parts → PairColorSystem κ V)
    {η : ℝ} (hη : 0 < η) (hlocal : ∀ B D : Q.parts, order.le B D → ∀ x ∈ B.1, ∀ y ∈ D.1,
      R.colorOfPair x y = (T B D).colorOfPair x y)
    (hkeep : ∀ B D : Q.parts,
      refinementParent hQP B = refinementParent hQP D ∨ ¬S.IsRegularPair η B.1 D.1 → T B D = S)
    (hedit : ∀ B D : Q.parts, refinementParent hQP B ≠ refinementParent hQP D →
      S.IsRegularPair η B.1 D.1 →
      (#{q ∈ B.1 ×ˢ D.1 | (T B D).colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        ((∑ c, |(pairColorDensity S c B.1 D.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP B).1 (refinementParent hQP D).1|) / 2 +
          Fintype.card κ * η) * (#B.1 * #D.1))
    (B D : Q.parts) (hne : refinementParent hQP B ≠ refinementParent hQP D) :
    (#{q ∈ B.1 ×ˢ D.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
      ((∑ c, |(pairColorDensity S c B.1 D.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP B).1 (refinementParent hQP D).1|) / 2 +
        Fintype.card κ * η) * (#B.1 * #D.1) := by
  let : LinearOrder Q.parts := order
  let : LE Q.parts := order.toLE
  by_cases hreg : S.IsRegularPair η B.1 D.1
  · rcases le_total B D with hle | hle
    · have hf : {q ∈ B.1 ×ˢ D.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
          {q ∈ B.1 ×ˢ D.1 | (T B D).colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} :=
        filter_congr fun q hq ↦ by
          rw [hlocal B D hle q.1 (mem_product.1 hq).1 q.2 (mem_product.1 hq).2]
      rw [hf]
      exact hedit B D hne hreg
    · rw [card_filter_colorOfPair_ne_comm hRrev B.1 D.1]
      have hf : {q ∈ D.1 ×ˢ B.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} =
          {q ∈ D.1 ×ˢ B.1 | (T D B).colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} :=
        filter_congr fun q hq ↦ by
          rw [hlocal D B hle q.1 (mem_product.1 hq).1 q.2 (mem_product.1 hq).2]
      rw [hf, ← sum_abs_pairColorDensity_sub_swap S B.1 D.1
        (refinementParent hQP B).1 (refinementParent hQP D).1, mul_comm (#B.1 : ℝ) #D.1]
      exact hedit D B hne.symm hreg.symm
  · have hempty : {q ∈ B.1 ×ˢ D.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} = ∅ :=
      filter_false_of_mem fun q hq ↦ not_not.2 <| by
        rcases le_total B D with hle | hle
        · rw [hlocal B D hle q.1 (mem_product.1 hq).1 q.2 (mem_product.1 hq).2,
            hkeep B D (Or.inr hreg)]
        · rw [R.colorOfPair_swap q.2 q.1, S.colorOfPair_swap q.2 q.1, hRrev,
            hlocal D B hle q.2 (mem_product.1 hq).2 q.1 (mem_product.1 hq).1,
            hkeep D B (Or.inr fun h ↦ hreg h.symm)]
    rw [hempty, card_empty, Nat.cast_zero]
    exact mul_nonneg (add_nonneg (div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _) (by norm_num))
      (by positivity)) (by positivity)

open Classical in
/-- Sum the fine-block edit bounds over all pairs `(B, D)` with distinct coarse parents, using
`sum_abs_pairColorDensity_sub_mul_card_le` to bound the `L¹` density drift by the energy gap. -/
private theorem card_edits_cellwise_recoloring_le [Fintype κ] [Fintype V] [DecidableEq V]
    {S R : PairColorSystem κ V} (hRrev : R.rev = S.rev) {P Q : Finpartition (univ : Finset V)}
    (hQP : Q ≤ P) {g η : ℝ} (hg : S.energy Q - S.energy P ≤ g) (hη : 0 < η)
    (order : LinearOrder Q.parts) (T : Q.parts → Q.parts → PairColorSystem κ V)
    (hlocal : ∀ B D : Q.parts, order.le B D → ∀ x ∈ B.1, ∀ y ∈ D.1,
      R.colorOfPair x y = (T B D).colorOfPair x y)
    (hkeep : ∀ B D : Q.parts,
      refinementParent hQP B = refinementParent hQP D ∨ ¬S.IsRegularPair η B.1 D.1 → T B D = S)
    (hedit : ∀ B D : Q.parts, refinementParent hQP B ≠ refinementParent hQP D →
      S.IsRegularPair η B.1 D.1 →
      (#{q ∈ B.1 ×ˢ D.1 | (T B D).colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) ≤
        ((∑ c, |(pairColorDensity S c B.1 D.1 : ℝ) -
            pairColorDensity S c (refinementParent hQP B).1 (refinementParent hQP D).1|) / 2 +
          Fintype.card κ * η) * (#B.1 * #D.1)) :
    (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ) ≤
      (√(Fintype.card κ * g) / 2 + Fintype.card κ * η) * (Fintype.card V : ℝ) ^ 2 := by
  let : LinearOrder Q.parts := order
  let : LE Q.parts := order.toLE
  let cell (x : V) : Q.parts := ⟨Q.part x, Q.part_mem.2 (mem_univ x)⟩
  set I := (univ : Finset (Q.parts × Q.parts)).filter
    fun BD ↦ refinementParent hQP BD.1 ≠ refinementParent hQP BD.2
  have hsub : (univ.filter fun p : V × V ↦ R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2) ⊆
      I.biUnion fun BD ↦ {q ∈ BD.1.1 ×ˢ BD.2.1 |
        R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} := fun p hp ↦ by
    have hne_col := (mem_filter.1 hp).2
    have hpar : refinementParent hQP (cell p.1) ≠ refinementParent hQP (cell p.2) := fun heq ↦
      hne_col <| by
        rcases le_total (cell p.1) (cell p.2) with hle | hle
        · rw [hlocal _ _ hle p.1 (Q.mem_part_self.2 (mem_univ _)) p.2
            (Q.mem_part_self.2 (mem_univ _)), hkeep _ _ (Or.inl heq)]
        · rw [R.colorOfPair_swap p.2 p.1, S.colorOfPair_swap p.2 p.1, hRrev,
            hlocal _ _ hle p.2 (Q.mem_part_self.2 (mem_univ _)) p.1
              (Q.mem_part_self.2 (mem_univ _)), hkeep _ _ (Or.inl heq.symm)]
    exact mem_biUnion.2 ⟨(cell p.1, cell p.2), mem_filter.2 ⟨mem_univ _, hpar⟩, mem_filter.2
      ⟨mem_product.2 ⟨Q.mem_part_self.2 (mem_univ _), Q.mem_part_self.2 (mem_univ _)⟩, hne_col⟩⟩
  have hcard_le : (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ) ≤
      ∑ BD ∈ I, (#{q ∈ BD.1.1 ×ˢ BD.2.1 | R.colorOfPair q.1 q.2 ≠ S.colorOfPair q.1 q.2} : ℝ) :=
    by exact_mod_cast (card_le_card hsub).trans card_biUnion_le
  have hIarea : ∑ BD ∈ I, (#BD.1.1 * #BD.2.1 : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ I) fun _ _ _ ↦ by positivity).trans_eq
      (by rw [Fintype.sum_prod_type]; dsimp only; rw [← sum_mul_sum, Q.sum_card_subtype,
        card_univ, sq])
  calc (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ)
      ≤ ∑ BD ∈ I, _ := hcard_le
    _ ≤ ∑ BD ∈ I, (((∑ c, |(pairColorDensity S c BD.1.1 BD.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP BD.1).1 (refinementParent hQP BD.2).1|) / 2 +
            Fintype.card κ * η) * (#BD.1.1 * #BD.2.1)) := sum_le_sum fun BD hBD ↦
        card_edits_fine_block_le hRrev hQP order T hη hlocal hkeep hedit BD.1 BD.2
          (mem_filter.1 hBD).2
    _ = (∑ BD ∈ I, (∑ c, |(pairColorDensity S c BD.1.1 BD.2.1 : ℝ) -
          pairColorDensity S c (refinementParent hQP BD.1).1 (refinementParent hQP BD.2).1|) *
            (#BD.1.1 * #BD.2.1)) / 2 +
          Fintype.card κ * η * ∑ BD ∈ I, (#BD.1.1 * #BD.2.1 : ℝ) := by
        simp_rw [add_mul, sum_add_distrib, div_mul_eq_mul_div, ← sum_div, ← mul_sum]
    _ ≤ √(Fintype.card κ * g) * (Fintype.card V : ℝ) ^ 2 / 2 +
          Fintype.card κ * η * (Fintype.card V : ℝ) ^ 2 :=
        add_le_add (div_le_div_of_nonneg_right
          (S.sum_abs_pairColorDensity_sub_mul_card_le hQP hg) (by norm_num))
          (mul_le_mul_of_nonneg_left hIarea (by positivity))
    _ = (√(Fintype.card κ * g) / 2 + Fintype.card κ * η) * (Fintype.card V : ℝ) ^ 2 := by ring

open Classical in
/-- Glue local coupled recolorings across all fine block pairs of `Q` with distinct coarse parents
in `P`. -/
private theorem exists_cellwise_coupled_recoloring [Fintype κ] [Fintype V]
    [DecidableEq V] (S : PairColorSystem κ V) {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P)
    {g η : ℝ} (hg : S.energy Q - S.energy P ≤ g) (hη : 0 < η)
    (hsize : ∀ B ∈ Q.parts, Fintype.card κ + 2 ≤ η ^ 2 * #B) :
    ∃ R : PairColorSystem κ V, R.rev = S.rev ∧
      (∀ B D : Q.parts, refinementParent hQP B ≠ refinementParent hQP D →
        (B.1, D.1) ∉ S.irregularPairs η Q → ∀ c, ∀ s' ⊆ B.1, ∀ t' ⊆ D.1,
          |(#{q ∈ s' ×ˢ t' | R.colorOfPair q.1 q.2 = some c} : ℝ) -
            pairColorDensity S c (refinementParent hQP B).1 (refinementParent hQP D).1 *
              (#s' * #t')| ≤
            2 * Fintype.card κ * η * (#B.1 * #D.1)) ∧
      (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ) ≤
        (√(Fintype.card κ * g) / 2 + Fintype.card κ * η) * (Fintype.card V : ℝ) ^ 2 := by
  let order : LinearOrder Q.parts := LinearOrder.lift' (Fintype.equivFin Q.parts)
    (Fintype.equivFin Q.parts).injective
  let : LinearOrder Q.parts := order
  let : LE Q.parts := order.toLE
  choose T hrev hkeep hprop using S.exists_local_coupled_recoloring hQP hη hsize
  obtain ⟨R, hRrev, hlocal⟩ := S.exists_cellwise_recoloring Q order T hrev
  refine ⟨R, hRrev, fun B D hne hnotbad c s' hs' t' ht' ↦ ?_,
    card_edits_cellwise_recoloring_le hRrev hQP hg hη order T hlocal hkeep
      fun B D h1 h2 ↦ (hprop B D h1 h2).2⟩
  have hBDne : B.1 ≠ D.1 := fun heq ↦ hne (congrArg (refinementParent hQP) (Subtype.ext heq))
  have hreg : S.IsRegularPair η B.1 D.1 := by
    by_contra hnr
    exact hnotbad (S.mem_irregularPairs.2 ⟨B.2, D.2, hBDne, hnr⟩)
  rcases le_total B D with hle | hle
  · have hfilt : {q ∈ s' ×ˢ t' | R.colorOfPair q.1 q.2 = some c} =
        {q ∈ s' ×ˢ t' | (T B D).colorOfPair q.1 q.2 = some c} :=
      filter_congr fun q hq ↦ by
        rw [hlocal B D hle q.1 (hs' (mem_product.1 hq).1) q.2 (ht' (mem_product.1 hq).2)]
    rw [hfilt]
    exact (hprop B D hne hreg).1 c s' hs' t' ht'
  · have hswap : #{q ∈ s' ×ˢ t' | R.colorOfPair q.1 q.2 = some c} =
        #{q ∈ t' ×ˢ s' | (T D B).colorOfPair q.1 q.2 = some (S.rev c)} :=
      card_equiv (Equiv.prodComm V V) fun q ↦ by
        simp only [mem_filter, mem_product, Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap,
          and_comm]
        exact and_congr_right fun hq ↦ by
          rw [← R.colorOfPair_swap_eq_some_iff, hRrev,
            hlocal D B hle q.2 (ht' hq.2) q.1 (hs' hq.1)]
    rw [hswap, ← pairColorDensity_swap S c (refinementParent hQP B).1
      (refinementParent hQP D).1, mul_comm (#s' : ℝ) #t', mul_comm (#B.1 : ℝ) #D.1]
    exact (hprop D B hne.symm hreg.symm).1 (S.rev c) t' ht' s' hs'

/-- Bound the `ε`-irregular coarse pairs of `R` on `P` in terms of the `η`-irregular fine pairs of
`S` on `Q`. -/
private theorem sum_irregularPairs_coarse_le [Fintype κ] [DecidableEq κ] [Fintype V]
    [DecidableEq V] (S R : PairColorSystem κ V) {P Q : Finpartition (univ : Finset V)}
    (hQP : Q ≤ P) {η ε : ℝ} (hη : 0 ≤ η) (hε : 0 < ε)
    (hηε : 2 * Fintype.card κ * η ≤ ε ^ 3 / 4)
    (hgood : ∀ B D : Q.parts, refinementParent hQP B ≠ refinementParent hQP D →
      (B.1, D.1) ∉ S.irregularPairs η Q → ∀ c, ∀ s' ⊆ B.1, ∀ t' ⊆ D.1,
        |(#{q ∈ s' ×ˢ t' | R.colorOfPair q.1 q.2 = some c} : ℝ) -
          pairColorDensity S c (refinementParent hQP B).1 (refinementParent hQP D).1 *
            (#s' * #t')| ≤
          2 * Fintype.card κ * η * (#B.1 * #D.1)) :
    ε ^ 3 / 4 * ∑ AC ∈ R.irregularPairs ε P, (#AC.1 * #AC.2 : ℝ) ≤
      ∑ BD ∈ S.irregularPairs η Q, (#BD.1 * #BD.2 : ℝ) := by
  classical
  let badMass (A C : P.parts) : ℝ :=
    ∑ B with refinementParent hQP B = A, ∑ D with refinementParent hQP D = C,
      if (B.1, D.1) ∈ S.irregularPairs η Q then (#B.1 * #D.1 : ℝ) else 0
  have hbad_lower {A C : P.parts} (hirr : (A.1, C.1) ∈ R.irregularPairs ε P) :
      ε ^ 3 / 4 * (#A.1 * #C.1 : ℝ) ≤ badMass A C := by
    obtain ⟨-, -, hACne, hnotreg⟩ := R.mem_irregularPairs.1 hirr
    have hACsub : A ≠ C := fun h ↦ hACne (congrArg Subtype.val h)
    have hdisj : Disjoint A.1 C.1 := P.disjoint A.2 C.2 hACne
    by_contra! hlt
    apply hnotreg
    refine R.isRegularPair_of_abs_card_filter_colorOfPair_sub_le hdisj
      (p := fun c ↦ pairColorDensity S c A.1 C.1)
      (β := 2 * Fintype.card κ * η + ε ^ 3 / 4) hε (by linarith) fun c X hX Y hY ↦ ?_
    have hagg := R.abs_card_filter_colorOfPair_sub_le_of_refines hQP
      (A := A) (C := C) (p := fun c ↦ pairColorDensity S c A.1 C.1)
      (fun c ↦ mod_cast pairColorDensity_nonneg S c A.1 C.1)
      (fun c ↦ mod_cast pairColorDensity_le_one S c A.1 C.1)
      (S.irregularPairs η Q) (δ := 2 * Fintype.card κ * η) (by positivity)
      (fun B D hB hD hnb ↦ by
        rw [← hB, ← hD]
        exact hgood B D (by rw [hB, hD]; exact hACsub) hnb) c hX hY
    linarith
  let J : Finset (P.parts × P.parts) :=
    univ.filter fun AC ↦ (AC.1.1, AC.2.1) ∈ R.irregularPairs ε P
  have hsumJ : ∑ AC ∈ R.irregularPairs ε P, (#AC.1 * #AC.2 : ℝ) =
      ∑ AC ∈ J, (#AC.1.1 * #AC.2.1 : ℝ) := by
    refine sum_bij (fun AC hAC ↦ (⟨AC.1, (R.mem_irregularPairs.1 hAC).1⟩,
      ⟨AC.2, (R.mem_irregularPairs.1 hAC).2.1⟩)) (fun AC hAC ↦ mem_filter.2 ⟨mem_univ _, hAC⟩)
      (fun _ _ _ _ h ↦ Prod.ext (congrArg Subtype.val (Prod.mk.inj h).1)
        (congrArg Subtype.val (Prod.mk.inj h).2))
      (fun AC hAC ↦ ⟨(AC.1.1, AC.2.1), (mem_filter.1 hAC).2, rfl⟩) fun _ _ ↦ rfl
  have htot : ∑ A : P.parts, ∑ C : P.parts, badMass A C =
      ∑ BD ∈ S.irregularPairs η Q, (#BD.1 * #BD.2 : ℝ) := by
    rw [← sum_sum_eq_sum_sum_fiber hQP, ← Fintype.sum_prod_type', sum_ite, sum_const_zero, add_zero]
    refine sum_bij (fun BD _ ↦ (BD.1.1, BD.2.1)) (fun BD hBD ↦ (mem_filter.1 hBD).2)
      (fun _ _ _ _ h ↦ Prod.ext (Subtype.ext (Prod.mk.inj h).1) (Subtype.ext (Prod.mk.inj h).2))
      (fun BD hBD ↦ ⟨(⟨BD.1, (S.mem_irregularPairs.1 hBD).1⟩,
        ⟨BD.2, (S.mem_irregularPairs.1 hBD).2.1⟩), mem_filter.2 ⟨mem_univ _, hBD⟩, rfl⟩)
      fun _ _ ↦ rfl
  calc ε ^ 3 / 4 * ∑ AC ∈ R.irregularPairs ε P, (#AC.1 * #AC.2 : ℝ)
      = ∑ AC ∈ J, ε ^ 3 / 4 * (#AC.1.1 * #AC.2.1 : ℝ) := by rw [hsumJ, mul_sum]
    _ ≤ ∑ AC ∈ J, badMass AC.1 AC.2 := sum_le_sum fun AC hAC ↦ hbad_lower (mem_filter.1 hAC).2
    _ ≤ ∑ AC : P.parts × P.parts, badMass AC.1 AC.2 :=
        sum_le_sum_of_subset_of_nonneg (subset_univ J) fun _ _ _ ↦
          sum_nonneg fun _ _ ↦ sum_nonneg fun _ _ ↦ by split_ifs <;> positivity
    _ = ∑ BD ∈ S.irregularPairs η Q, (#BD.1 * #BD.2 : ℝ) := by
        rw [Fintype.sum_prod_type', htot]

end CellwiseCoupledRecoloring

/-! ### Scheduled regular approximation -/

section ScheduledApproximation

/-- For an equipartition `P` of `univ`, the within-cell distinct-pair count is at most
`|V|² / #P.parts`. -/
private theorem sum_card_mul_pred_le_of_isEquipartition [Fintype V] [DecidableEq V]
    {P : Finpartition (univ : Finset V)} (hP : P.IsEquipartition) :
    (∑ A ∈ P.parts, #A * (#A - 1) : ℕ) ≤ (Fintype.card V : ℝ) ^ 2 / #P.parts := by
  by_cases hk : #P.parts = 0
  · simp [card_eq_zero.1 hk]
  have hnat : ∑ A ∈ P.parts, #A * (#A - 1) ≤ Fintype.card V * (Fintype.card V / #P.parts) :=
    calc ∑ A ∈ P.parts, #A * (#A - 1)
        ≤ ∑ A ∈ P.parts, #A * (Fintype.card V / #P.parts) := sum_le_sum fun A hA ↦ by
            have hle := hP.card_part_le_average_add_one hA
            rw [card_univ] at hle
            exact Nat.mul_le_mul_left _ (Nat.sub_le_iff_le_add.2 hle)
      _ = (∑ A ∈ P.parts, #A) * (Fintype.card V / #P.parts) := (sum_mul ..).symm
      _ = Fintype.card V * (Fintype.card V / #P.parts) := by rw [P.sum_card_parts, card_univ]
  calc ((∑ A ∈ P.parts, #A * (#A - 1) : ℕ) : ℝ)
      ≤ (Fintype.card V : ℝ) * ((Fintype.card V / #P.parts : ℕ) : ℝ) := by exact_mod_cast hnat
    _ ≤ (Fintype.card V : ℝ) * ((Fintype.card V : ℝ) / #P.parts) :=
        mul_le_mul_of_nonneg_left Nat.cast_div_le (Nat.cast_nonneg _)
    _ = (Fintype.card V : ℝ) ^ 2 / #P.parts := by ring

/-- Fine and coarse cell-size thresholds from `pairRegularApproximationBound ≤ |V|`. -/
private theorem cell_sizes_of_pairRegularApproximationBound [Fintype V] [DecidableEq V]
    {α : ℝ} (hα : 0 < α) {F : ℕ → ℝ} (hF : ∀ m, 0 < F m) {K k₀ : ℕ}
    (hV : pairRegularApproximationBound α F K k₀ ≤ Fintype.card V)
    {P Q : Finpartition (univ : Finset V)} (hQP : Q ≤ P) (hQeq : Q.IsEquipartition)
    (hQM : #Q.parts ≤ pairRegularApproximationPartBound α F K k₀)
    (hPM : #P.parts ≤ pairRegularApproximationPartBound α F K k₀) :
    (∀ B ∈ Q.parts, (K : ℝ) + 2 ≤ (pairApproxSchedule α F K #P.parts) ^ 2 * #B) ∧
      (∀ A ∈ P.parts, (K : ℝ) + 1 ≤ (pairApproxEps α F K #P.parts) ^ 6 * #A) := by
  set M := pairRegularApproximationPartBound α F K k₀
  set Φ := pairApproxSchedule α F K
  have hΦ : ∀ k, 0 < Φ k := pairApproxSchedule_pos hα hF K
  set ηmin := ((Iic M).image Φ).min' (Nonempty.image ⟨0, mem_Iic.2 (Nat.zero_le M)⟩ _)
  have hV' : max M 1 * (⌈(K + 2 : ℝ) / ηmin ^ 2⌉₊ + 1) ≤ Fintype.card V := by
    simpa [pairRegularApproximationBound_def, M, ηmin] using hV
  obtain ⟨m₀, -, hm₀⟩ := mem_image.1 (min'_mem ((Iic M).image Φ)
    (Nonempty.image ⟨0, mem_Iic.2 (Nat.zero_le M)⟩ _))
  have hηmin_pos : 0 < ηmin := by linarith [hΦ m₀, hm₀]
  have hηmin_le : ηmin ≤ Φ #P.parts := min'_le _ _ (mem_image_of_mem Φ (mem_Iic.2 hPM))
  have hsizeQ (B : Finset V) (hB : B ∈ Q.parts) : (K : ℝ) + 2 ≤ (Φ #P.parts) ^ 2 * #B := by
    have hQpos : 0 < #Q.parts := card_pos.2 ⟨B, hB⟩
    have hm : ⌈(K + 2 : ℝ) / ηmin ^ 2⌉₊ * #Q.parts ≤ Fintype.card V :=
      (Nat.mul_le_mul (Nat.le_succ _) (hQM.trans (le_max_left M 1))).trans
        ((mul_comm ..).le.trans hV')
    have hceil_le : ⌈(K + 2 : ℝ) / ηmin ^ 2⌉₊ ≤ #B :=
      ((Nat.le_div_iff_mul_le hQpos).2 hm).trans
        (card_univ (α := V) ▸ hQeq.average_le_card_part hB)
    have hBreal : (K + 2 : ℝ) / ηmin ^ 2 ≤ #B := (Nat.le_ceil _).trans (mod_cast hceil_le)
    exact ((div_le_iff₀' (sq_pos_of_pos hηmin_pos)).1 hBreal).trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hηmin_pos.le hηmin_le 2) (Nat.cast_nonneg _))
  refine ⟨hsizeQ, fun A hA ↦ ?_⟩
  obtain ⟨B, hB, hBA⟩ := exists_le_of_le hQP hA
  set ε := pairApproxEps α F K #P.parts
  have hεpos : 0 < ε := pairApproxEps_pos hα hF K #P.parts
  have hΦeq : Φ #P.parts = ε ^ 4 / (8 * (K + 1)) := rfl
  have hΦε : (Φ #P.parts) ^ 2 ≤ ε ^ 6 := by
    have hd : (1 : ℝ) ≤ (8 * (K + 1)) ^ 2 := by
      have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      nlinarith
    calc (Φ #P.parts) ^ 2 = ε ^ 8 / (8 * (K + 1)) ^ 2 := by rw [hΦeq, div_pow, ← pow_mul]
      _ ≤ ε ^ 8 := div_le_self (by positivity) hd
      _ ≤ ε ^ 6 := pow_le_pow_of_le_one hεpos.le (pairApproxEps_le_one α F K #P.parts) (by norm_num)
  exact (by linarith : (K : ℝ) + 1 ≤ K + 2).trans
    ((hsizeQ B hB).trans (mul_le_mul hΦε (mod_cast card_le_card hBA) (by positivity)
      (by positivity)))

/-- Parameter inequalities splitting the edit budget into four `α / 4` shares. -/
private theorem pairApprox_budget_bounds {α : ℝ} (hα : 0 < α) {F : ℕ → ℝ} (hF : ∀ m, 0 < F m)
    (K k : ℕ) :
    √(K * (α ^ 2 / (4 * (K + 1)))) / 2 + K * pairApproxSchedule α F K k ≤ α / 2 ∧
      2 * (K : ℝ) * pairApproxSchedule α F K k ≤ pairApproxEps α F K k ^ 3 / 4 ∧
      pairApproxSchedule α F K k ≤ pairApproxEps α F K k ^ 3 / 4 * (α / 4) := by
  set ε := pairApproxEps α F K k
  set Φ := pairApproxSchedule α F K k
  have hΦeq : Φ = ε ^ 4 / (8 * (K + 1)) := rfl
  have hεpos : 0 < ε := pairApproxEps_pos hα hF K k
  have hε1 : ε ≤ 1 := pairApproxEps_le_one α F K k
  have hεα : ε ≤ α / 8 := pairApproxEps_le_div_eight α F K k
  have hb₁ : √(K * (α ^ 2 / (4 * (K + 1)))) / 2 ≤ α / 4 := by
    have hKg : (K : ℝ) * (α ^ 2 / (4 * (K + 1))) ≤ (α / 2) ^ 2 :=
      (mul_le_mul_of_nonneg_right (by linarith : (K : ℝ) ≤ K + 1) (by positivity)).trans_eq
        (by field_simp; ring)
    have hsq := (sqrt_le_sqrt hKg).trans_eq (sqrt_sq (by positivity : 0 ≤ α / 2))
    linarith
  have hb₂ : (K : ℝ) * Φ ≤ α / 4 := by
    have hε4 : ε ^ 4 ≤ ε := pow_le_of_le_one hεpos.le hε1 (by norm_num)
    have hKdiv : (K : ℝ) / (8 * (K + 1)) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    calc (K : ℝ) * Φ = (K / (8 * (K + 1))) * ε ^ 4 := by rw [hΦeq]; ring
      _ ≤ (1 / 8) * ε := mul_le_mul hKdiv hε4 (by positivity) (by norm_num)
      _ ≤ α / 4 := by linarith
  have hηε : 2 * (K : ℝ) * Φ ≤ ε ^ 3 / 4 := by
    have hε4 : ε ^ 4 ≤ ε ^ 3 := pow_le_pow_of_le_one hεpos.le hε1 (by norm_num)
    have hKdiv : 2 * (K : ℝ) / (8 * (K + 1)) ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
    calc 2 * (K : ℝ) * Φ = (2 * K / (8 * (K + 1))) * ε ^ 4 := by rw [hΦeq]; ring
      _ ≤ (1 / 4) * ε ^ 3 := mul_le_mul hKdiv hε4 (by positivity) (by norm_num)
      _ = ε ^ 3 / 4 := by ring
  have hΦα : Φ ≤ ε ^ 3 / 4 * (α / 4) := by
    calc Φ = ε ^ 4 / (8 * (K + 1)) := hΦeq
      _ ≤ ε ^ 4 / 8 := div_le_div_of_nonneg_left (by positivity) (by norm_num)
          (by linarith [Nat.cast_nonneg (α := ℝ) K])
      _ = ε ^ 3 * (ε / 8) := by ring
      _ ≤ ε ^ 3 * (α / 16) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = ε ^ 3 / 4 * (α / 4) := by ring
  exact ⟨by linarith, hηε, hΦα⟩

open Classical in
/-- Split the ordered-pair edit distance from `S` to `T : PairColorSystem (Option κ) V` through an
intermediate recoloring `R : PairColorSystem κ V`. -/
private theorem card_edits_cleanup_of_recoloring_le [Fintype V] [DecidableEq V]
    {S R : PairColorSystem κ V} {T : PairColorSystem (Option κ) V}
    {P : Finpartition (univ : Finset V)} {ε : ℝ}
    (hTedit : #{p : V × V | T.colorOfPair p.1 p.2 ≠ (R.colorOfPair p.1 p.2).map some} ≤
      (∑ AC ∈ R.irregularPairs ε P, #AC.1 * #AC.2) + ∑ A ∈ P.parts, #A * (#A - 1)) :
    (#{p : V × V | T.colorOfPair p.1 p.2 ≠ (S.colorOfPair p.1 p.2).map some} : ℝ) ≤
      (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ) +
        (∑ AC ∈ R.irregularPairs ε P, (#AC.1 * #AC.2 : ℝ)) +
        (∑ A ∈ P.parts, #A * (#A - 1) : ℕ) := by
  have hsub : (univ.filter fun p : V × V ↦ T.colorOfPair p.1 p.2 ≠
        (S.colorOfPair p.1 p.2).map some) ⊆
      (univ.filter fun p : V × V ↦ R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2) ∪
        (univ.filter fun p : V × V ↦ T.colorOfPair p.1 p.2 ≠
          (R.colorOfPair p.1 p.2).map some) := fun p hp ↦ by
    simp only [mem_union, mem_filter, mem_univ, true_and] at hp ⊢
    exact if h : R.colorOfPair p.1 p.2 = S.colorOfPair p.1 p.2 then Or.inr (h ▸ hp) else Or.inl h
  have hnat : (#{p : V × V | T.colorOfPair p.1 p.2 ≠ (S.colorOfPair p.1 p.2).map some} : ℝ) ≤
      (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} +
        ((∑ AC ∈ R.irregularPairs ε P, #AC.1 * #AC.2) +
          ∑ A ∈ P.parts, #A * (#A - 1)) : ℕ) :=
    Nat.cast_le.2
      ((card_le_card hsub).trans ((card_union_le _ _).trans (add_le_add le_rfl hTedit)))
  have hcast : ((∑ AC ∈ R.irregularPairs ε P, #AC.1 * #AC.2 : ℕ) : ℝ) =
      ∑ AC ∈ R.irregularPairs ε P, (#AC.1 * #AC.2 : ℝ) := by push_cast; rfl
  rw [Nat.cast_add, Nat.cast_add, hcast, ← add_assoc] at hnat
  exact hnat

open Classical in
/-- **Scheduled regular approximation of a pair-color system.** Given an equipartition `P₀` of `V`,
an edit-fraction budget `α > 0`, and any positive schedule `F : ℕ → ℝ`, once `|V|` is at least
`pairRegularApproximationBound α F (card κ) #P₀.parts`, there exist a refining equipartition
`P ≤ P₀` (with `#P₀.parts ≤ #P.parts ≤ pairRegularApproximationPartBound α F (card κ) #P₀.parts`)
and a pair-color system `T : PairColorSystem (Option κ) V` such that `(⟨P, T⟩)` satisfies
`LowerSkeletonRegular F` and at most `α |V|²` ordered vertex pairs are edited. -/
theorem exists_equipartition_lowerSkeletonRegular [Fintype κ] [Fintype V]
    [DecidableEq V] (S : PairColorSystem κ V) (P₀ : Finpartition (univ : Finset V))
    (hP₀ : P₀.IsEquipartition) {α : ℝ} (hα : 0 < α) {F : ℕ → ℝ} (hF : ∀ m, 0 < F m)
    (hV : pairRegularApproximationBound α F (Fintype.card κ) #P₀.parts ≤ Fintype.card V) :
    ∃ (P : Finpartition (univ : Finset V)) (T : PairColorSystem (Option κ) V),
      P ≤ P₀ ∧ P.IsEquipartition ∧
        #P₀.parts ≤ #P.parts ∧
        #P.parts ≤ pairRegularApproximationPartBound α F (Fintype.card κ) #P₀.parts ∧
        T.rev = Option.map S.rev ∧
        (⟨P, T⟩ : PairSkeleton3 (Option κ) V).LowerSkeletonRegular F ∧
        (#{p : V × V | T.colorOfPair p.1 p.2 ≠ (S.colorOfPair p.1 p.2).map some} : ℝ) ≤
          α * (Fintype.card V : ℝ) ^ 2 := by
  set K := Fintype.card κ
  set n := Fintype.card V
  set a₀ := max ⌈4 / α⌉₊ 1
  set g : ℝ := α ^ 2 / (4 * (K + 1))
  set Φ := pairApproxSchedule α F K
  set M := pairRegularApproximationPartBound α F K #P₀.parts
  have hΦ : ∀ k, 0 < Φ k := pairApproxSchedule_pos hα hF K
  have hVpos : 0 < pairRegularApproximationBound α F K #P₀.parts := by
    dsimp only [pairRegularApproximationBound]; positivity
  have : Nonempty V := Fintype.card_pos_iff.1 (hVpos.trans_le hV)
  have hP₀pos : 0 < #P₀.parts := (P₀.parts_nonempty univ_nonempty.ne_empty).card_pos
  -- Pre-split `P₀` into `a₀ * #P₀.parts` equitable cells, then apply strong regularization.
  have ha₀V : a₀ * #P₀.parts ≤ #(univ : Finset V) := by
    rw [card_univ]
    refine ((le_strongPairColorRegularityBound g hΦ _).trans (le_max_left M 1)).trans ?_
    dsimp only [pairRegularApproximationBound] at hV
    exact (Nat.le_mul_of_pos_right _ (by positivity)).trans hV
  obtain ⟨P₁, hP₁eq, hP₁card, hP₁P₀, -⟩ :=
    hP₀.exists_refining_equipartition_card_eq_mul P₀ le_rfl (by positivity : a₀ ≠ 0) ha₀V
  obtain ⟨P, Q, hQP, hPP₁, hPeq, hQeq, hPQcard, hQcard, hgap, hQreg⟩ :=
    S.exists_strong_refining_equipartition P₁ hP₁eq (by positivity : 0 < g) hΦ
  have hQM : #Q.parts ≤ M := by rwa [hP₁card] at hQcard
  have hPM : #P.parts ≤ M := hPQcard.trans hQM
  have hP₀P : #P₀.parts ≤ #P.parts :=
    (Nat.le_mul_of_pos_left _ (by positivity : 0 < a₀)).trans
      (hP₁card.symm.le.trans (card_mono hPP₁))
  -- Couple fine blocks of `Q` to coarse densities on `P`, then clean up `P`.
  obtain ⟨hsizeQ, hsizeP⟩ := cell_sizes_of_pairRegularApproximationBound hα hF hV hQP hQeq hQM hPM
  obtain ⟨R, hRrev, hRgood, hRedit⟩ :=
    S.exists_cellwise_coupled_recoloring hQP hgap (hΦ #P.parts) hsizeQ
  set ε := pairApproxEps α F K #P.parts
  have hεpos : 0 < ε := pairApproxEps_pos hα hF K #P.parts
  obtain ⟨T, hTrev, hTreg, -, hTedit⟩ := R.exists_recoloring_isPairColorRegular P hεpos hsizeP
  refine ⟨P, T, hPP₁.trans hP₁P₀, hPeq, hP₀P, hPM, hTrev.trans (congrArg Option.map hRrev),
    PairSkeleton3.lowerSkeletonRegular_iff.2 (hTreg.mono (by
      simpa [Fintype.card_option] using two_mul_pairApproxEps_le α F K #P.parts)), ?_⟩
  have hsplit := card_edits_cleanup_of_recoloring_le (S := S) hTedit
  obtain ⟨hb₁₂, hηε, hΦα⟩ := pairApprox_budget_bounds hα hF K #P.parts
  have hb₃ : ∑ AC ∈ R.irregularPairs ε P, (#AC.1 * #AC.2 : ℝ) ≤ α / 4 * (n : ℝ) ^ 2 :=
    le_of_mul_le_mul_left (((sum_irregularPairs_coarse_le S R hQP (hΦ #P.parts).le hεpos hηε
      hRgood).trans hQreg).trans (by nlinarith [sq_nonneg (n : ℝ)])) (by positivity)
  have hb₄ : ((∑ A ∈ P.parts, #A * (#A - 1) : ℕ) : ℝ) ≤ α / 4 * (n : ℝ) ^ 2 := by
    have ha₀le : ⌈4 / α⌉₊ ≤ #P.parts := (le_max_left _ 1).trans
      ((Nat.le_mul_of_pos_right _ hP₀pos).trans (hP₁card.symm.le.trans (card_mono hPP₁)))
    have h4α : 4 / α ≤ #P.parts := (Nat.le_ceil _).trans (mod_cast ha₀le)
    have hPpos : (0 : ℝ) < #P.parts := by linarith [div_pos (by norm_num : (0 : ℝ) < 4) hα]
    refine (sum_card_mul_pred_le_of_isEquipartition hPeq).trans ((div_le_iff₀ hPpos).2 ?_)
    nlinarith [(div_le_iff₀ hα).1 h4α, sq_nonneg (n : ℝ)]
  have hbR : (#{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} : ℝ) ≤
      α / 2 * (n : ℝ) ^ 2 := hRedit.trans (by nlinarith [sq_nonneg (n : ℝ)])
  linarith

end ScheduledApproximation

end PairColorSystem

end TauCeti
