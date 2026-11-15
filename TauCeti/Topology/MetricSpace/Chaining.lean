/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.CoveringNumbers
public import Mathlib.Topology.MetricSpace.Holder

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Sparse star-bridge covers and multiscale Hölder chaining

To deduce Hölder continuity on a metric parameter set `S` of covering dimension `d` from
increment bounds along a countable family of edges, naive all-pairs neighbor graphs at scale
`r ^ n` have `O(r ^ (-2 d n))` edges, losing a factor of two in the dimension threshold, while
tree-only parent pointers miss nearby points separated by net cell boundaries.

We resolve both issues in two steps:

1. **Sparse star-bridge covers (`TauCeti.exists_finset_edist_le_card_le_rpow`).**
   For any finite subset `F` of a pseudo-emetric space, threshold `δ`, and shell count `K ≥ 1`,
   concentric ball-doubling selects `O(|F| ^ (1 + 1 / K))` directed edges of length at most
   `2 K δ` such that every pair of points in `F` within distance `2 δ` shares a common star
   center in `F`. Taking `K` large makes the cardinality exponent arbitrarily close to `1`.

2. **Multiscale deterministic chaining
   (`TauCeti.exists_edges_and_holderOnWith_of_coveringNumber_le`).**
   When `S` has finite diameter at most `D` and internal covering numbers bounded by
   `C ε ^ (-d)` for `0 < ε ≤ 1`, combining cumulative minimal covers at scales `r ^ n` with
   parent edges, sparse star-bridge edges, and a level-zero global star produces a countable
   dense-in-`S` subset `U ⊆ S` and edge families of size `O((r ^ (-d')) ^ n)` (for any `d' > d`)
   and length `O(r ^ n)`. Any map into a pseudo-emetric space satisfying a `γ`-Hölder bound along
   these edges is `γ`-Hölder on `U`.

## References

* B. Awerbuch, D. Peleg, *Sparse partitions*, 31st IEEE Symposium on Foundations of Computer
  Science, 1990, 503–513 (concentric neighborhood clustering).
* V. Krätschmer, M. Urusov, *A general Kolmogorov–Chentsov type theorem on general metric spaces*,
  arXiv:2107.13837v2, Theorem 1.1.
-/

public section

open Filter Metric Set
open scoped ENNReal NNReal Topology

namespace TauCeti

section StarBridge

variable {T : Type*} [PseudoEMetricSpace T]

/-- Auxiliary induction on subsets `U ⊆ F` for `exists_finset_edist_le_card_le_rpow`. -/
private lemma exists_star_bridge_subset (F : Finset T) (δ : ℝ≥0∞) {K : ℕ} (hK : 0 < K) :
    ∀ n : ℕ, ∀ U : Finset T, U.card = n → U ⊆ F →
      ∃ E : Finset (T × T),
        (E : Set (T × T)) ⊆ (U : Set T) ×ˢ (U : Set T) ∧
        (∀ p ∈ E, edist p.1 p.2 ≤ (2 * K : ℕ) * δ) ∧
        (E.card : ℝ≥0) ≤ (F.card : ℝ≥0) ^ (K : ℝ)⁻¹ * (U.card : ℝ≥0) ∧
        ∀ u ∈ U, ∀ v ∈ U, edist u v ≤ 2 * δ → ∃ z ∈ U, (u, z) ∈ E ∧ (v, z) ∈ E := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro U hcard hUF
    rcases U.eq_empty_or_nonempty with rfl | ⟨z, hzU⟩
    · refine ⟨∅, by simp, by simp, by simp, by simp⟩
    have hzF : z ∈ F := hUF hzU
    have hF_pos : (0 : ℝ≥0) < F.card := by
      exact_mod_cast Finset.card_pos.2 ⟨z, hzF⟩
    set α : ℝ≥0 := (F.card : ℝ≥0) ^ (K : ℝ)⁻¹
    have hα_pos : 0 < α := NNReal.rpow_pos hF_pos
    let B : ℕ → Finset T := fun j ↦ U.filter fun w ↦ edist w z ≤ (2 * j : ℕ) * δ
    have hzB0 : z ∈ B 0 := by simp [B, hzU]
    have hB_sub_U : ∀ j, B j ⊆ U := fun j ↦ Finset.filter_subset _ U
    have hB_mono : Monotone B := by
      intro i j hij w hw
      simp only [B, Finset.mem_filter] at hw ⊢
      refine ⟨hw.1, hw.2.trans ?_⟩
      gcongr
    have hB_step : ∀ {j u v}, u ∈ B j → v ∈ U → edist u v ≤ 2 * δ → v ∈ B (j + 1) := by
      intro j u v hu hv huv
      simp only [B, Finset.mem_filter] at hu ⊢
      refine ⟨hv, ?_⟩
      calc
        edist v z ≤ edist v u + edist u z := edist_triangle v u z
        _ = edist u v + edist u z := by rw [edist_comm v u]
        _ ≤ 2 * δ + (2 * j : ℕ) * δ := add_le_add huv hu.2
        _ = (2 * (j + 1) : ℕ) * δ := by
          push_cast
          ring
    -- By pigeonhole over `K` concentric shells, some shell grows by at most `|F| ^ (1 / K)`.
    have hex_shell : ∃ j < K, ((B (j + 1)).card : ℝ≥0) ≤ α * ((B j).card : ℝ≥0) := by
      by_contra! hgt
      have hpow : ∀ m, 0 < m → m ≤ K → α ^ m * ((B 0).card : ℝ≥0) < ((B m).card : ℝ≥0) := by
        intro m hm_pos hmK
        induction m with
        | zero => omega
        | succ m ihm =>
          rcases Nat.eq_zero_or_pos m with rfl | hm'
          · simpa using hgt 0 hK
          · calc
              α ^ (m + 1) * ((B 0).card : ℝ≥0) = α * (α ^ m * ((B 0).card : ℝ≥0)) := by ring
              _ < α * ((B m).card : ℝ≥0) := mul_lt_mul_of_pos_left (ihm hm' (by omega)) hα_pos
              _ < ((B (m + 1)).card : ℝ≥0) := hgt m hmK
      have hK_lt := hpow K hK le_rfl
      have hαK : α ^ K = (F.card : ℝ≥0) := by
        have hK_ne : (K : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hK.ne'
        rw [← NNReal.rpow_natCast, ← NNReal.rpow_mul, inv_mul_cancel₀ hK_ne, NNReal.rpow_one]
      have hB0_ge : (1 : ℝ≥0) ≤ (B 0).card := by
        exact_mod_cast Finset.card_pos.2 ⟨z, hzB0⟩
      have hBK_le : ((B K).card : ℝ≥0) ≤ F.card := by
        exact_mod_cast Finset.card_le_card ((hB_sub_U K).trans hUF)
      have hcontra : (F.card : ℝ≥0) < F.card :=
        calc
          (F.card : ℝ≥0) = (F.card : ℝ≥0) * 1 := (mul_one _).symm
          _ ≤ α ^ K * ((B 0).card : ℝ≥0) := by rw [hαK]; gcongr
          _ < ((B K).card : ℝ≥0) := hK_lt
          _ ≤ F.card := hBK_le
      exact hcontra.false
    obtain ⟨j, hjK, hj_card⟩ := hex_shell
    let U' : Finset T := U \ B j
    have hzj : z ∈ B j := hB_mono (Nat.zero_le j) hzB0
    have hU'_lt : U'.card < n := by
      rw [← hcard]
      exact Finset.card_lt_card (Finset.sdiff_ssubset (hB_sub_U j) ⟨z, hzj⟩)
    obtain ⟨E', hE'_sub, hE'_len, hE'_card, hE'_bridge⟩ :=
      ih U'.card hU'_lt U' rfl (Finset.sdiff_subset.trans hUF)
    let Sz : Finset (T × T) := (B (j + 1)).image fun w ↦ (w, z)
    refine ⟨Sz ∪ E', ?_, ?_, ?_, ?_⟩
    · intro p hp
      rcases Finset.mem_union.1 (Finset.mem_coe.1 hp) with hpS | hpE'
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hpS
        exact ⟨hB_sub_U (j + 1) hw, hzU⟩
      · exact Set.prod_mono Finset.sdiff_subset Finset.sdiff_subset (hE'_sub hpE')
    · intro p hp
      rcases Finset.mem_union.1 hp with hpS | hpE'
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hpS
        have hw' : edist w z ≤ (2 * (j + 1) : ℕ) * δ := (Finset.mem_filter.1 hw).2
        refine hw'.trans ?_
        have hjK' : 2 * (j + 1) ≤ 2 * K := by omega
        gcongr
      · exact hE'_len p hpE'
    · have hSz_card : (Sz.card : ℝ≥0) ≤ (B (j + 1)).card := by
        exact_mod_cast Finset.card_image_le
      have hpart : U'.card + (B j).card = U.card :=
        Finset.card_sdiff_add_card_eq_card (hB_sub_U j)
      calc
        ((Sz ∪ E').card : ℝ≥0) ≤ (Sz.card : ℝ≥0) + (E'.card : ℝ≥0) := by
          exact_mod_cast Finset.card_union_le Sz E'
        _ ≤ ((B (j + 1)).card : ℝ≥0) + α * (U'.card : ℝ≥0) :=
          add_le_add hSz_card hE'_card
        _ ≤ α * ((B j).card : ℝ≥0) + α * (U'.card : ℝ≥0) :=
          add_le_add hj_card le_rfl
        _ = α * (((U'.card + (B j).card : ℕ) : ℝ≥0)) := by
          push_cast
          ring
        _ = α * (U.card : ℝ≥0) := by rw [hpart]
    · intro u hu v hv huv
      by_cases huj : u ∈ B j
      · refine ⟨z, hzU, Finset.mem_union_left _ ?_, Finset.mem_union_left _ ?_⟩
        · exact Finset.mem_image_of_mem _ (hB_mono (Nat.le_succ j) huj)
        · exact Finset.mem_image_of_mem _ (hB_step huj hv huv)
      · by_cases hvj : v ∈ B j
        · refine ⟨z, hzU, Finset.mem_union_left _ ?_, Finset.mem_union_left _ ?_⟩
          · exact Finset.mem_image_of_mem _ (hB_step hvj hu (edist_comm u v ▸ huv))
          · exact Finset.mem_image_of_mem _ (hB_mono (Nat.le_succ j) hvj)
        · have hu' : u ∈ U' := Finset.mem_sdiff.2 ⟨hu, huj⟩
          have hv' : v ∈ U' := Finset.mem_sdiff.2 ⟨hv, hvj⟩
          obtain ⟨z', hz', huz', hvz'⟩ := hE'_bridge u hu' v hv' huv
          exact ⟨z', Finset.sdiff_subset hz', Finset.mem_union_right _ huz',
            Finset.mem_union_right _ hvz'⟩

/-- **Sparse star-bridge cover.** Every finite set `F` in a pseudo-emetric space admits at most
`|F| ^ (1 + 1 / K)` directed edges of length at most `2 K δ` in `F × F` such that any two points
of `F` within distance `2 δ` connect to a common center in `F`. -/
theorem exists_finset_edist_le_card_le_rpow (F : Finset T) (δ : ℝ≥0∞) {K : ℕ} (hK : 0 < K) :
    ∃ E : Finset (T × T),
      (E : Set (T × T)) ⊆ (F : Set T) ×ˢ (F : Set T) ∧
      (∀ p ∈ E, edist p.1 p.2 ≤ (2 * K : ℕ) * δ) ∧
      (E.card : ℝ≥0) ≤ (F.card : ℝ≥0) ^ (1 + (K : ℝ)⁻¹) ∧
      ∀ u ∈ F, ∀ v ∈ F, edist u v ≤ 2 * δ → ∃ z ∈ F, (u, z) ∈ E ∧ (v, z) ∈ E := by
  obtain ⟨E, hsub, hlen, hcard, hbridge⟩ := exists_star_bridge_subset F δ hK F.card F rfl subset_rfl
  refine ⟨E, hsub, hlen, hcard.trans ?_, hbridge⟩
  rcases F.eq_empty_or_nonempty with rfl | hF
  · simp [NNReal.zero_rpow (by positivity : (1 : ℝ) + (K : ℝ)⁻¹ ≠ 0)]
  · have hF_pos : (0 : ℝ≥0) < F.card := by exact_mod_cast Finset.card_pos.2 hF
    rw [add_comm, NNReal.rpow_add hF_pos.ne', NNReal.rpow_one]

end StarBridge

section MultiscaleChaining

/-- Recursive ancestor descent along scale pointers `parent n` from level `N` down to `m`. -/
private def descend {T : Type*} (parent : ℕ → T → T) : ℕ → ℕ → T → T
  | 0, _, x => x
  | N + 1, m, x => if m = N + 1 then x else descend parent N m (parent N x)

private lemma descend_self {T : Type*} (parent : ℕ → T → T) (N : ℕ) (x : T) :
    descend parent N N x = x := by
  cases N <;> simp [descend]

private lemma descend_succ_of_le {T : Type*} (parent : ℕ → T → T) {N m : ℕ} (hm : m ≤ N) (x : T) :
    descend parent (N + 1) m x = descend parent N m (parent N x) := by
  simp [descend, Nat.ne_of_lt (Nat.lt_succ_of_le hm)]

private lemma descend_eq_parent {T : Type*} (parent : ℕ → T → T) :
    ∀ {N k : ℕ}, k < N → ∀ x : T, descend parent N k x = parent k (descend parent N (k + 1) x)
  | 0, _, hk, _ => absurd hk (Nat.not_lt_zero _)
  | N + 1, k, hk, x => by
    rcases eq_or_lt_of_le (Nat.le_of_lt_succ hk) with rfl | hk'
    · rw [descend_succ_of_le parent le_rfl, descend_self, descend_self]
    · rw [descend_succ_of_le parent (le_of_lt hk'),
        descend_eq_parent parent hk' (parent N x),
        descend_succ_of_le parent (Nat.succ_le_of_lt hk')]

private lemma edist_le_sum_Ico_descend {E : Type*} [PseudoEMetricSpace E] {T : Type*}
    (parent : ℕ → T → T) (f : T → E) {m N : ℕ} (hmN : m ≤ N) (x : T) :
    edist (f x) (f (descend parent N m x)) ≤
      ∑ k ∈ Finset.Ico m N,
        edist (f (descend parent N (k + 1) x)) (f (descend parent N k x)) := by
  induction N generalizing x with
  | zero =>
    obtain rfl := Nat.eq_zero_of_le_zero hmN
    simp [descend_self]
  | succ N ih =>
    rcases eq_or_lt_of_le hmN with rfl | hmN'
    · simp [descend_self]
    · have hmN_le : m ≤ N := Nat.le_of_lt_succ hmN'
      rw [Finset.sum_Ico_succ_top hmN_le]
      calc
        edist (f x) (f (descend parent (N + 1) m x)) ≤
            edist (f x) (f (descend parent (N + 1) N x)) +
              edist (f (descend parent (N + 1) N x)) (f (descend parent (N + 1) m x)) :=
          edist_triangle _ _ _
        _ = edist (f (descend parent (N + 1) N x)) (f (descend parent (N + 1) m x)) +
              edist (f (descend parent (N + 1) (N + 1) x))
                (f (descend parent (N + 1) N x)) := by
          rw [descend_self, add_comm]
        _ ≤ (∑ k ∈ Finset.Ico m N,
              edist (f (descend parent (N + 1) (k + 1) x))
                (f (descend parent (N + 1) k x))) +
              edist (f (descend parent (N + 1) (N + 1) x))
                (f (descend parent (N + 1) N x)) := by
          gcongr
          simpa only [descend_succ_of_le parent le_rfl, descend_self,
            descend_succ_of_le parent hmN_le] using
            (ih hmN_le (parent N x)).trans_eq
              (Finset.sum_congr rfl fun k hk ↦ by
                have hkN : k < N := (Finset.mem_Ico.1 hk).2
                rw [descend_succ_of_le parent (Nat.succ_le_of_lt hkN),
                  descend_succ_of_le parent (le_of_lt hkN)])

/-- **Multiscale deterministic Hölder chaining.** Let `S` be a subset of a pseudo-emetric space
with extended diameter at most `D` and covering numbers bounded by `C ε ^ (-d)` for `0 < ε ≤ 1`.
For any `r ∈ (0, 1)` and any `d' > d` (`0 ≤ d`), there exist a countable subset `U ⊆ S` whose
closure contains `S` and edge families `(s n, t n)` in `U` at each scale `n` with at most
`C_edge (r ^ (-d')) ^ n` edges of length at most `A r ^ n`, such that any map `f` into a
pseudo-emetric space obeying a `γ`-Hölder bound (`γ > 0`) along those edges is `γ`-Hölder on `U`
with a deterministic multiple of the edge constant. -/
theorem exists_edges_and_holderOnWith_of_coveringNumber_le {T : Type*} [PseudoEMetricSpace T]
    {S : Set T} {D C r : ℝ≥0} {d d' : ℝ}
    (hdiam : ediam S ≤ D) (hr0 : 0 < r) (hr1 : r < 1)
    (hd : 0 ≤ d) (hdd' : d < d')
    (hcov : ∀ ε : ℝ≥0, 0 < ε → ε ≤ 1 →
      (coveringNumber ε S : ℝ≥0∞) ≤ (C : ℝ≥0∞) * (ε : ℝ≥0∞) ^ (-d)) :
    ∃ (U : Set T) (k : ℕ → ℕ) (s t : (n : ℕ) → Fin (k n) → T) (C_edge A : ℝ≥0),
      U.Countable ∧ U ⊆ S ∧ S ⊆ closure U ∧
      (∀ n i, s n i ∈ U ∧ t n i ∈ U) ∧
      (∀ n, (k n : ℝ≥0) ≤ C_edge * (r ^ (-d')) ^ n) ∧
      (∀ n i, edist (s n i) (t n i) ≤ (A : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) ∧
      ∀ {γ : ℝ≥0}, 0 < γ → ∃ C_H : ℝ≥0,
        ∀ {E : Type*} [PseudoEMetricSpace E] (f : T → E) (K_f : ℝ≥0),
          (∀ n i, edist (f (s n i)) (f (t n i)) ≤
            (K_f : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n) ^ (γ : ℝ)) →
          HolderOnWith (C_H * K_f) γ f U := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀S⟩
  · refine ⟨∅, fun _ ↦ 0, fun _ ↦ Fin.elim0, fun _ ↦ Fin.elim0, 0, 0,
      countable_empty, subset_rfl, subset_closure, fun _ i ↦ i.elim0,
      fun _ ↦ by simp, fun _ i ↦ i.elim0, fun _ ↦ ⟨0, fun _ _ _ ↦ by simp [HolderOnWith]⟩⟩
  -- Pick an intermediate dimension `d < d₁ < d'` and shell count `K` with `d₁ (1 + 1/K) ≤ d'`.
  let d₁ : ℝ := (d + d') / 2
  have hd_lt_d₁ : d < d₁ := by dsimp [d₁]; linarith
  have hd₁_lt_d' : d₁ < d' := by dsimp [d₁]; linarith
  have hd₁_pos : 0 < d₁ := hd.trans_lt hd_lt_d₁
  obtain ⟨K₀, hK₀⟩ := exists_nat_gt (d₁ / (d' - d₁))
  let K : ℕ := max 1 K₀
  have hK_pos : 0 < K := by positivity
  have hd₁K_le : d₁ * (1 + (K : ℝ)⁻¹) ≤ d' := by
    have hK_gt : d₁ / (d' - d₁) < K := hK₀.trans_le (by exact_mod_cast le_max_right 1 K₀)
    have hsub_pos : 0 < d' - d₁ := sub_pos.2 hd₁_lt_d'
    have hinv : (K : ℝ)⁻¹ ≤ (d' - d₁) / d₁ := by
      rw [inv_le_iff_one_le_mul₀ (by exact_mod_cast hK_pos)]
      have := (div_lt_iff₀ hsub_pos).1 hK_gt
      rw [div_mul_eq_mul_div, one_le_div hd₁_pos]
      linarith
    calc
      d₁ * (1 + (K : ℝ)⁻¹) ≤ d₁ * (1 + (d' - d₁) / d₁) := by gcongr
      _ = d' := by field_simp; ring
  -- Finite minimal covers `N n` at scales `r ^ n` and cumulative nets `M n`.
  have hrn_pos : ∀ n : ℕ, 0 < r ^ n := fun n ↦ pow_pos hr0 n
  have hrn_le_one : ∀ n : ℕ, r ^ n ≤ 1 := fun n ↦ pow_le_one₀ zero_le hr1.le
  have hcov_ne_top : ∀ n : ℕ, coveringNumber (r ^ n) S ≠ ⊤ := by
    intro n
    rw [← ENat.toENNReal_ne_top]
    refine ne_top_of_le_ne_top ?_ (hcov (r ^ n) (hrn_pos n) (hrn_le_one n))
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.rpow_ne_top_of_ne_zero (by exact_mod_cast (hrn_pos n).ne') ENNReal.coe_ne_top)
  let N : ℕ → Finset T := fun n ↦ (finite_minimalCover (ε := r ^ n) (A := S)).toFinset
  have hN_sub : ∀ n, (N n : Set T) ⊆ S := by
    intro n
    simpa [N] using (minimalCover_subset (ε := r ^ n) (A := S))
  have hN_cover : ∀ n, IsCover (r ^ n) S (N n) := by
    intro n
    simpa [N] using isCover_minimalCover (hcov_ne_top n)
  have hN_card : ∀ n, ((N n).card : ℝ≥0) ≤ C * (r ^ (-d)) ^ n := by
    intro n
    have hencard : ((N n).card : ℝ≥0∞) = (coveringNumber (r ^ n) S : ℝ≥0∞) := by
      have h1 := (finite_minimalCover (ε := r ^ n) (A := S)).encard_eq_coe_toFinset_card
      have h2 := encard_minimalCover (hcov_ne_top n)
      exact_mod_cast h1.symm.trans h2
    have hle := hencard.trans_le (hcov (r ^ n) (hrn_pos n) (hrn_le_one n))
    have hrhs : (C : ℝ≥0∞) * ((r ^ n : ℝ≥0) : ℝ≥0∞) ^ (-d) =
        ((C * (r ^ (-d)) ^ n : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.pow_rpow_comm,
        ← ENNReal.coe_rpow_of_ne_zero hr0.ne', ← ENNReal.coe_pow]
    rw [hrhs] at hle
    exact_mod_cast hle
  let M : ℕ → Finset T := fun n ↦ (Finset.range (n + 1)).biUnion N
  have hM_mono : Monotone M := fun m n hmn ↦
    Finset.biUnion_subset_biUnion_of_subset_left N
      (Finset.range_mono (Nat.add_le_add_right hmn 1))
  have hN_sub_M : ∀ n, N n ⊆ M n := fun n ↦
    Finset.subset_biUnion_of_mem N (Finset.mem_range.2 (Nat.lt_succ_self n))
  have hM_sub : ∀ n, (M n : Set T) ⊆ S := by
    intro n x hx
    obtain ⟨j, -, hxj⟩ := Finset.mem_biUnion.1 hx
    exact hN_sub j hxj
  have hM_cover : ∀ n, IsCover (r ^ n) S (M n) := fun n x hx ↦ by
    obtain ⟨y, hy, hxy⟩ := hN_cover n hx
    exact ⟨y, Finset.mem_coe.2 (hN_sub_M n (Finset.mem_coe.1 hy)), hxy⟩
  obtain ⟨w₀, hw₀M0, -⟩ := hM_cover 0 hx₀S
  have hw₀M : ∀ n, w₀ ∈ M n := fun n ↦ hM_mono (Nat.zero_le n) (Finset.mem_coe.1 hw₀M0)
  -- Polynomial factor `(n + 1)` absorbed into the exponential gap `r ^ (d - d₁) > 1`.
  have hM_card : ∃ C₁ : ℝ≥0, ∀ n, ((M n).card : ℝ≥0) ≤ C₁ * (r ^ (-d₁)) ^ n := by
    let α : ℝ≥0 := r ^ (d - d₁)
    have hα_gt : 1 < α := by
      simpa using NNReal.rpow_lt_rpow_of_exponent_gt hr0 hr1 (y := 0) (by linarith)
    let δ : ℝ≥0 := α - 1
    have hδ_pos : 0 < δ := tsub_pos_iff_lt.2 hα_gt
    have hα_eq : 1 + δ = α := add_tsub_cancel_of_le hα_gt.le
    refine ⟨(1 + δ⁻¹) * C, fun n ↦ ?_⟩
    have h1_le_rd : 1 ≤ r ^ (-d) := by
      simpa using NNReal.rpow_le_rpow_of_exponent_ge hr0 hr1.le (y := 0) (neg_nonpos.2 hd)
    have hsum : ((M n).card : ℝ≥0) ≤ (n + 1 : ℝ≥0) * C * (r ^ (-d)) ^ n := by
      calc
        ((M n).card : ℝ≥0) ≤ ∑ j ∈ Finset.range (n + 1), ((N j).card : ℝ≥0) := by
          exact_mod_cast Finset.card_biUnion_le
        _ ≤ ∑ _ ∈ Finset.range (n + 1), C * (r ^ (-d)) ^ n := by
          refine Finset.sum_le_sum fun j hj ↦ (hN_card j).trans ?_
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ h1_le_rd (Nat.le_of_lt_succ (Finset.mem_range.1 hj))) zero_le
        _ = (n + 1 : ℝ≥0) * C * (r ^ (-d)) ^ n := by
          simp [mul_assoc]
    have hbern : (n + 1 : ℝ≥0) ≤ (1 + δ⁻¹) * α ^ n := by
      rw [← NNReal.coe_le_coe]
      have hpow : 1 + (n : ℝ) * (δ : ℝ) ≤ ((1 + δ : ℝ≥0) : ℝ) ^ n := by
        simpa using one_add_mul_le_pow (by linarith [δ.coe_nonneg] : (-2 : ℝ) ≤ δ) n
      have hlin : (n + 1 : ℝ) ≤ (1 + (δ : ℝ)⁻¹) * (1 + (n : ℝ) * δ) := by
        have hδ_ne : (δ : ℝ) ≠ 0 := by exact_mod_cast hδ_pos.ne'
        have : (1 + (δ : ℝ)⁻¹) * (1 + (n : ℝ) * δ) =
            (n + 1 : ℝ) + ((n : ℝ) * δ + (δ : ℝ)⁻¹) := by
          calc
            (1 + (δ : ℝ)⁻¹) * (1 + (n : ℝ) * δ) =
                1 + (n : ℝ) * δ + (δ : ℝ)⁻¹ + (δ : ℝ)⁻¹ * (δ : ℝ) * n := by ring
            _ = (n + 1 : ℝ) + ((n : ℝ) * δ + (δ : ℝ)⁻¹) := by
              rw [inv_mul_cancel₀ hδ_ne]; ring
        linarith [show (0 : ℝ) ≤ (n : ℝ) * δ + (δ : ℝ)⁻¹ by positivity]
      rw [hα_eq] at hpow
      exact hlin.trans (by push_cast; gcongr)
    calc
      ((M n).card : ℝ≥0) ≤ (n + 1 : ℝ≥0) * C * (r ^ (-d)) ^ n := hsum
      _ ≤ ((1 + δ⁻¹) * α ^ n) * C * (r ^ (-d)) ^ n := by gcongr
      _ = ((1 + δ⁻¹) * C) * (α * r ^ (-d)) ^ n := by ring
      _ = ((1 + δ⁻¹) * C) * (r ^ (-d₁)) ^ n := by
        congr 2
        rw [← NNReal.rpow_add hr0.ne']
        congr 1
        ring
  obtain ⟨C₁, hM_card⟩ := hM_card
  let U : Set T := ⋃ n, (M n : Set T)
  have hU_count : U.Countable := countable_iUnion fun n ↦ (M n).countable_toSet
  have hU_sub : U ⊆ S := iUnion_subset hM_sub
  have hS_closure : S ⊆ closure U := by
    intro x hx
    rw [EMetric.mem_closure_iff]
    intro ε hε
    have htend : Tendsto (fun n : ℕ ↦ (r : ℝ≥0∞) ^ n) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.coe_lt_one_iff.2 hr1)
    obtain ⟨n, hn⟩ := ((tendsto_order.1 htend).2 ε hε).exists
    obtain ⟨y, hy, hxy⟩ := hM_cover n hx
    exact ⟨y, mem_iUnion.2 ⟨n, hy⟩, hxy.trans_lt (by simpa [ENNReal.coe_pow] using hn)⟩
  -- Parent pointers from `S` into `M n` within distance `r ^ n`.
  let parent : ℕ → T → T := fun n w ↦
    if hw : w ∈ S then (hM_cover n hw).choose else w₀
  have hparent_mem : ∀ n {w}, w ∈ S → parent n w ∈ M n := by
    intro n w hw
    simp only [parent, hw, ↓reduceDIte]
    exact Finset.mem_coe.1 (hM_cover n hw).choose_spec.1
  have hparent_edist : ∀ n {w}, w ∈ S → edist w (parent n w) ≤ (r : ℝ≥0∞) ^ n := by
    intro n w hw
    simp only [parent, hw, ↓reduceDIte]
    simpa [ENNReal.coe_pow] using (hM_cover n hw).choose_spec.2
  -- Sparse star-bridge edges on `M n` at threshold `δ_n = ((1 - r)⁻¹ + 1) * r ^ n`.
  let c_δ : ℝ≥0 := (1 - r)⁻¹ + 1
  have h1mr_pos : 0 < 1 - r := tsub_pos_iff_lt.2 hr1
  let bridge : ∀ n : ℕ, _ := fun n ↦
    exists_finset_edist_le_card_le_rpow (M n) ((c_δ : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) hK_pos
  let E_bridge : ℕ → Finset (T × T) := fun n ↦ (bridge n).choose
  let E_parent : ℕ → Finset (T × T) := fun n ↦ (M (n + 1)).image fun w ↦ (w, parent n w)
  let E_global : ℕ → Finset (T × T) := fun n ↦
    if n = 0 then (M 0).image (fun w ↦ (w, w₀)) else ∅
  let E_all : ℕ → Finset (T × T) := fun n ↦ E_parent n ∪ E_bridge n ∪ E_global n
  let L_all : ℕ → List (T × T) := fun n ↦ (E_all n).toList
  let k : ℕ → ℕ := fun n ↦ (L_all n).length
  let s : (n : ℕ) → Fin (k n) → T := fun n i ↦ ((L_all n)[i]).1
  let t : (n : ℕ) → Fin (k n) → T := fun n i ↦ ((L_all n)[i]).2
  have hmem_of_idx : ∀ n (i : Fin (k n)), (s n i, t n i) ∈ E_all n := fun n i ↦
    Finset.mem_toList.1 (List.getElem_mem _)
  have hex_idx : ∀ n {p : T × T}, p ∈ E_all n → ∃ i : Fin (k n), s n i = p.1 ∧ t n i = p.2 := by
    intro n p hp
    obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.1 (Finset.mem_toList.2 hp)
    exact ⟨⟨i, hi⟩, congrArg Prod.fst heq, congrArg Prod.snd heq⟩
  -- Edge membership in `U × U`, length bound `A * r ^ n`, and size bound `C_edge * r ^ (-d' * n)`.
  have hE_all_U : ∀ n {p : T × T}, p ∈ E_all n → p.1 ∈ U ∧ p.2 ∈ U := by
    intro n p hp
    rcases Finset.mem_union.1 hp with hp12 | hp3
    · rcases Finset.mem_union.1 hp12 with hp1 | hp2
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hp1
        exact ⟨mem_iUnion.2 ⟨n + 1, hw⟩,
          mem_iUnion.2 ⟨n, hparent_mem n (hM_sub (n + 1) hw)⟩⟩
      · have hsub := (bridge n).choose_spec.1 (Finset.mem_coe.2 hp2)
        exact ⟨mem_iUnion.2 ⟨n, hsub.1⟩, mem_iUnion.2 ⟨n, hsub.2⟩⟩
    · by_cases hn0 : n = 0
      · subst hn0
        simp only [E_global, ↓reduceIte] at hp3
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hp3
        exact ⟨mem_iUnion.2 ⟨0, hw⟩, mem_iUnion.2 ⟨0, hw₀M 0⟩⟩
      · simp [E_global, hn0] at hp3
  let A : ℝ≥0 := max 1 (max ((2 * K : ℕ) * c_δ) D)
  have hE_all_len : ∀ n {p : T × T}, p ∈ E_all n → edist p.1 p.2 ≤ (A : ℝ≥0∞) * (r : ℝ≥0∞) ^ n := by
    intro n p hp
    rcases Finset.mem_union.1 hp with hp12 | hp3
    · rcases Finset.mem_union.1 hp12 with hp1 | hp2
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hp1
        calc
          edist w (parent n w) ≤ (r : ℝ≥0∞) ^ n := hparent_edist n (hM_sub (n + 1) hw)
          _ = 1 * (r : ℝ≥0∞) ^ n := (one_mul _).symm
          _ ≤ (A : ℝ≥0∞) * (r : ℝ≥0∞) ^ n := by
            gcongr; exact_mod_cast le_max_left 1 _
      · calc
          edist p.1 p.2 ≤ (2 * K : ℕ) * ((c_δ : ℝ≥0∞) * (r : ℝ≥0∞) ^ n) :=
            (bridge n).choose_spec.2.1 p hp2
          _ = (((2 * K : ℕ) * c_δ : ℝ≥0) : ℝ≥0∞) * (r : ℝ≥0∞) ^ n := by
            push_cast; ring
          _ ≤ (A : ℝ≥0∞) * (r : ℝ≥0∞) ^ n := by
            gcongr
            exact_mod_cast (le_max_left _ D).trans (le_max_right 1 _)
    · by_cases hn0 : n = 0
      · subst hn0
        simp only [E_global, ↓reduceIte] at hp3
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hp3
        calc
          edist w w₀ ≤ ediam S := edist_le_ediam_of_mem (hM_sub 0 hw) (hM_sub 0 (hw₀M 0))
          _ ≤ D := hdiam
          _ ≤ (A : ℝ≥0∞) * (r : ℝ≥0∞) ^ 0 := by
            rw [pow_zero, mul_one]
            exact_mod_cast (le_max_right _ D).trans (le_max_right 1 _)
      · simp [E_global, hn0] at hp3
  let C_edge : ℝ≥0 := C₁ * r ^ (-d₁) + C₁ ^ (1 + (K : ℝ)⁻¹) + C₁
  have hk_card : ∀ n, (k n : ℝ≥0) ≤ C_edge * (r ^ (-d')) ^ n := by
    intro n
    have hk_eq : k n = (E_all n).card := Finset.length_toList _
    have hparent_card : ((E_parent n).card : ℝ≥0) ≤ (C₁ * r ^ (-d₁)) * (r ^ (-d')) ^ n := by
      calc
        ((E_parent n).card : ℝ≥0) ≤ ((M (n + 1)).card : ℝ≥0) := by
          exact_mod_cast Finset.card_image_le
        _ ≤ C₁ * (r ^ (-d₁)) ^ (n + 1) := hM_card (n + 1)
        _ = (C₁ * r ^ (-d₁)) * (r ^ (-d₁)) ^ n := by ring
        _ ≤ (C₁ * r ^ (-d₁)) * (r ^ (-d')) ^ n := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left' ?_ n) zero_le
          exact NNReal.rpow_le_rpow_of_exponent_ge hr0 hr1.le (by linarith)
    have hbridge_card : ((E_bridge n).card : ℝ≥0) ≤ C₁ ^ (1 + (K : ℝ)⁻¹) * (r ^ (-d')) ^ n := by
      have hexp_pos : (0 : ℝ) ≤ 1 + (K : ℝ)⁻¹ := by positivity
      calc
        ((E_bridge n).card : ℝ≥0) ≤ ((M n).card : ℝ≥0) ^ (1 + (K : ℝ)⁻¹) :=
          (bridge n).choose_spec.2.2.1
        _ ≤ (C₁ * (r ^ (-d₁)) ^ n) ^ (1 + (K : ℝ)⁻¹) := NNReal.rpow_le_rpow (hM_card n) hexp_pos
        _ = C₁ ^ (1 + (K : ℝ)⁻¹) * ((r ^ (-d₁)) ^ (1 + (K : ℝ)⁻¹)) ^ n := by
          rw [NNReal.mul_rpow, ← NNReal.rpow_natCast_mul, mul_comm (n : ℝ), NNReal.rpow_mul_natCast]
        _ ≤ C₁ ^ (1 + (K : ℝ)⁻¹) * (r ^ (-d')) ^ n := by
          refine mul_le_mul_of_nonneg_left (pow_le_pow_left' ?_ n) zero_le
          rw [← NNReal.rpow_mul, neg_mul]
          exact NNReal.rpow_le_rpow_of_exponent_ge hr0 hr1.le (neg_le_neg hd₁K_le)
    have hglobal_card : ((E_global n).card : ℝ≥0) ≤ C₁ * (r ^ (-d')) ^ n := by
      by_cases hn0 : n = 0
      · subst hn0
        simp only [E_global, ↓reduceIte, pow_zero, mul_one]
        have h1 : (((M 0).image fun w ↦ (w, w₀)).card : ℝ≥0) ≤ (M 0).card := by
          exact_mod_cast Finset.card_image_le
        exact h1.trans (by simpa using hM_card 0)
      · simp [E_global, hn0]
    rw [hk_eq]
    calc
      ((E_all n).card : ℝ≥0) ≤
          ((E_parent n).card : ℝ≥0) + ((E_bridge n).card : ℝ≥0) + ((E_global n).card : ℝ≥0) := by
        have h1 := Finset.card_union_le (E_parent n ∪ E_bridge n) (E_global n)
        have h2 := Finset.card_union_le (E_parent n) (E_bridge n)
        exact_mod_cast h1.trans (Nat.add_le_add_right h2 _)
      _ ≤ (C₁ * r ^ (-d₁)) * (r ^ (-d')) ^ n + C₁ ^ (1 + (K : ℝ)⁻¹) * (r ^ (-d')) ^ n +
            C₁ * (r ^ (-d')) ^ n :=
        add_le_add (add_le_add hparent_card hbridge_card) hglobal_card
      _ = C_edge * (r ^ (-d')) ^ n := by dsimp [C_edge]; ring
  refine ⟨U, k, s, t, C_edge, A, hU_count, hU_sub, hS_closure,
    fun n i ↦ hE_all_U n (hmem_of_idx n i), hk_card,
    fun n i ↦ hE_all_len n (hmem_of_idx n i), ?_⟩
  -- Deterministic Hölder assembly along `descend parent`.
  intro γ hγ
  have hrγ_lt : r ^ (γ : ℝ) < 1 := NNReal.rpow_lt_one hr1 (by exact_mod_cast hγ)
  let c_chain : ℝ≥0 := 2 * (1 - r ^ (γ : ℝ))⁻¹ + 2
  let C_H : ℝ≥0 := c_chain * r⁻¹ ^ (γ : ℝ)
  refine ⟨C_H, fun {E} _ f K_f hf ↦ ?_⟩
  have hf_edge : ∀ n {p : T × T}, p ∈ E_all n →
      edist (f p.1) (f p.2) ≤ (K_f : ℝ≥0∞) * ((r : ℝ≥0∞) ^ n) ^ (γ : ℝ) := by
    intro n p hp
    obtain ⟨i, hs_eq, ht_eq⟩ := hex_idx n hp
    simpa [hs_eq, ht_eq] using hf n i
  -- Properties of `descend parent N` when `x ∈ M N`.
  have hdesc_mem : ∀ {N m : ℕ} {x : T}, m ≤ N → x ∈ M N → descend parent N m x ∈ M m := by
    intro N
    induction N with
    | zero =>
      intro m x hm hx
      obtain rfl := Nat.eq_zero_of_le_zero hm
      simpa [descend_self] using hx
    | succ N ih =>
      intro m x hm hx
      rcases eq_or_lt_of_le hm with rfl | hm'
      · simpa [descend_self] using hx
      · rw [descend_succ_of_le parent (Nat.le_of_lt_succ hm')]
        exact ih (Nat.le_of_lt_succ hm') (hparent_mem N (hM_sub (N + 1) hx))
  have hdesc_T : ∀ {N m : ℕ} {x : T}, m ≤ N → x ∈ M N →
      edist x (descend parent N m x) ≤ ((1 - r)⁻¹ : ℝ≥0) * (r : ℝ≥0∞) ^ m := by
    intro N m x hmN hx
    have hstep : ∀ k ∈ Finset.Ico m N,
        edist (descend parent N (k + 1) x) (descend parent N k x) ≤ (r : ℝ≥0∞) ^ k := by
      intro k hk
      have hkN : k < N := (Finset.mem_Ico.1 hk).2
      rw [descend_eq_parent parent hkN]
      exact hparent_edist k (hM_sub (k + 1) (hdesc_mem (Nat.succ_le_of_lt hkN) hx))
    calc
      edist x (descend parent N m x) ≤
          ∑ k ∈ Finset.Ico m N,
            edist (descend parent N (k + 1) x) (descend parent N k x) :=
        edist_le_sum_Ico_descend parent id hmN x
      _ ≤ ∑ k ∈ Finset.Ico m N, (r : ℝ≥0∞) ^ k := Finset.sum_le_sum hstep
      _ = ∑ j ∈ Finset.range (N - m), (r : ℝ≥0∞) ^ m * (r : ℝ≥0∞) ^ j := by
        rw [Finset.sum_Ico_eq_sum_range]
        exact Finset.sum_congr rfl fun j _ ↦ pow_add (r : ℝ≥0∞) m j
      _ ≤ ∑' j : ℕ, (r : ℝ≥0∞) ^ m * (r : ℝ≥0∞) ^ j :=
        sum_le_tsum (Finset.range (N - m))
      _ = (r : ℝ≥0∞) ^ m * (1 - (r : ℝ≥0∞))⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ = ((1 - r)⁻¹ : ℝ≥0) * (r : ℝ≥0∞) ^ m := by
        rw [mul_comm, ENNReal.coe_inv h1mr_pos.ne', ENNReal.coe_sub, ENNReal.coe_one]
  have hdesc_f : ∀ {N m : ℕ} {x : T}, m ≤ N → x ∈ M N →
      edist (f x) (f (descend parent N m x)) ≤
        (((1 - r ^ (γ : ℝ))⁻¹ * K_f : ℝ≥0) : ℝ≥0∞) * ((r : ℝ≥0∞) ^ m) ^ (γ : ℝ) := by
    intro N m x hmN hx
    let q : ℝ≥0 := r ^ (γ : ℝ)
    have h1mq_pos : 0 < 1 - q := tsub_pos_iff_lt.2 hrγ_lt
    have hstep : ∀ k ∈ Finset.Ico m N,
        edist (f (descend parent N (k + 1) x)) (f (descend parent N k x)) ≤
          (K_f : ℝ≥0∞) * (q : ℝ≥0∞) ^ k := by
      intro k hk
      have hkN : k < N := (Finset.mem_Ico.1 hk).2
      have hw : descend parent N (k + 1) x ∈ M (k + 1) := hdesc_mem (Nat.succ_le_of_lt hkN) hx
      have hp : (descend parent N (k + 1) x, descend parent N k x) ∈ E_all k := by
        rw [descend_eq_parent parent hkN]
        exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hw))
      simpa [q, ENNReal.coe_rpow_of_ne_zero hr0.ne', ENNReal.pow_rpow_comm] using hf_edge k hp
    calc
      edist (f x) (f (descend parent N m x)) ≤
          ∑ k ∈ Finset.Ico m N,
            edist (f (descend parent N (k + 1) x)) (f (descend parent N k x)) :=
        edist_le_sum_Ico_descend parent f hmN x
      _ ≤ ∑ k ∈ Finset.Ico m N, (K_f : ℝ≥0∞) * (q : ℝ≥0∞) ^ k := Finset.sum_le_sum hstep
      _ = ∑ j ∈ Finset.range (N - m), ((K_f : ℝ≥0∞) * (q : ℝ≥0∞) ^ m) * (q : ℝ≥0∞) ^ j := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [pow_add, mul_assoc]
      _ ≤ ∑' j : ℕ, ((K_f : ℝ≥0∞) * (q : ℝ≥0∞) ^ m) * (q : ℝ≥0∞) ^ j :=
        sum_le_tsum (Finset.range (N - m))
      _ = ((K_f : ℝ≥0∞) * (q : ℝ≥0∞) ^ m) * (1 - (q : ℝ≥0∞))⁻¹ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
      _ = (((1 - q)⁻¹ * K_f : ℝ≥0) : ℝ≥0∞) * ((r : ℝ≥0∞) ^ m) ^ (γ : ℝ) := by
        have hqm : (q : ℝ≥0∞) ^ m = ((r : ℝ≥0∞) ^ m) ^ (γ : ℝ) := by
          simp [q, ENNReal.coe_rpow_of_ne_zero hr0.ne', ENNReal.pow_rpow_comm]
        rw [ENNReal.coe_mul, ENNReal.coe_inv h1mq_pos.ne', ENNReal.coe_sub, ENNReal.coe_one, hqm]
        ring
  -- Scale-`m` oscillation bound whenever `x, y ∈ U` satisfy `edist x y ≤ r ^ m`.
  have hscale : ∀ {x y : T}, x ∈ U → y ∈ U → ∀ (m : ℕ),
      edist x y ≤ (r : ℝ≥0∞) ^ m →
      edist (f x) (f y) ≤ ((c_chain * K_f : ℝ≥0) : ℝ≥0∞) * ((r : ℝ≥0∞) ^ m) ^ (γ : ℝ) := by
    intro x y hx hy m hxy
    obtain ⟨Nx, hNx⟩ := mem_iUnion.1 hx
    obtain ⟨Ny, hNy⟩ := mem_iUnion.1 hy
    let N := max m (max Nx Ny)
    have hmN : m ≤ N := le_max_left _ _
    have hxN : x ∈ M N :=
      hM_mono ((le_max_left Nx Ny).trans (le_max_right m _)) (Finset.mem_coe.1 hNx)
    have hyN : y ∈ M N :=
      hM_mono ((le_max_right Nx Ny).trans (le_max_right m _)) (Finset.mem_coe.1 hNy)
    let u := descend parent N m x
    let v := descend parent N m y
    have huM : u ∈ M m := hdesc_mem hmN hxN
    have hvM : v ∈ M m := hdesc_mem hmN hyN
    have huv_edist : edist u v ≤ 2 * ((c_δ : ℝ≥0∞) * (r : ℝ≥0∞) ^ m) := by
      calc
        edist u v ≤ edist u x + edist x y + edist y v := edist_triangle4 u x y v
        _ = edist x u + edist x y + edist y v := by rw [edist_comm u x]
        _ ≤ ((1 - r)⁻¹ : ℝ≥0) * (r : ℝ≥0∞) ^ m + (r : ℝ≥0∞) ^ m +
              ((1 - r)⁻¹ : ℝ≥0) * (r : ℝ≥0∞) ^ m :=
          add_le_add (add_le_add (hdesc_T hmN hxN) hxy) (hdesc_T hmN hyN)
        _ ≤ 2 * ((c_δ : ℝ≥0∞) * (r : ℝ≥0∞) ^ m) := by
          dsimp [c_δ]
          calc
            (((1 - r)⁻¹ : ℝ≥0) : ℝ≥0∞) * (r : ℝ≥0∞) ^ m + (r : ℝ≥0∞) ^ m +
                (((1 - r)⁻¹ : ℝ≥0) : ℝ≥0∞) * (r : ℝ≥0∞) ^ m =
              (2 * (((1 - r)⁻¹ : ℝ≥0) : ℝ≥0∞) + 1) * (r : ℝ≥0∞) ^ m := by ring
            _ ≤ (2 * (((1 - r)⁻¹ : ℝ≥0) : ℝ≥0∞) + 2) * (r : ℝ≥0∞) ^ m := by
              gcongr; norm_num
            _ = 2 * (((((1 - r)⁻¹ : ℝ≥0) : ℝ≥0∞) + 1) * (r : ℝ≥0∞) ^ m) := by ring
    obtain ⟨z, -, huz, hvz⟩ := (bridge m).choose_spec.2.2.2 u huM v hvM huv_edist
    have huz_all : (u, z) ∈ E_all m := Finset.mem_union_left _ (Finset.mem_union_right _ huz)
    have hvz_all : (v, z) ∈ E_all m := Finset.mem_union_left _ (Finset.mem_union_right _ hvz)
    have hf_uv : edist (f u) (f v) ≤ 2 * ((K_f : ℝ≥0∞) * ((r : ℝ≥0∞) ^ m) ^ (γ : ℝ)) := by
      calc
        edist (f u) (f v) ≤ edist (f u) (f z) + edist (f z) (f v) := edist_triangle _ _ _
        _ = edist (f u) (f z) + edist (f v) (f z) := by rw [edist_comm (f z) (f v)]
        _ ≤ (K_f : ℝ≥0∞) * ((r : ℝ≥0∞) ^ m) ^ (γ : ℝ) +
              (K_f : ℝ≥0∞) * ((r : ℝ≥0∞) ^ m) ^ (γ : ℝ) :=
          add_le_add (hf_edge m huz_all) (hf_edge m hvz_all)
        _ = 2 * ((K_f : ℝ≥0∞) * ((r : ℝ≥0∞) ^ m) ^ (γ : ℝ)) := (two_mul _).symm
    calc
      edist (f x) (f y) ≤ edist (f x) (f u) + edist (f u) (f v) + edist (f v) (f y) :=
        edist_triangle4 _ _ _ _
      _ = edist (f x) (f u) + edist (f u) (f v) + edist (f y) (f v) := by
        rw [edist_comm (f v) (f y)]
      _ ≤ (((1 - r ^ (γ : ℝ))⁻¹ * K_f : ℝ≥0) : ℝ≥0∞) * ((r : ℝ≥0∞) ^ m) ^ (γ : ℝ) +
            2 * ((K_f : ℝ≥0∞) * ((r : ℝ≥0∞) ^ m) ^ (γ : ℝ)) +
            (((1 - r ^ (γ : ℝ))⁻¹ * K_f : ℝ≥0) : ℝ≥0∞) * ((r : ℝ≥0∞) ^ m) ^ (γ : ℝ) :=
        add_le_add (add_le_add (hdesc_f hmN hxN) hf_uv) (hdesc_f hmN hyN)
      _ = ((c_chain * K_f : ℝ≥0) : ℝ≥0∞) * ((r : ℝ≥0∞) ^ m) ^ (γ : ℝ) := by
        dsimp [c_chain]
        ring
  -- Check `x, y ∈ U` across the zero, small-scale (`≤ 1`), and large-scale (`> 1`) regimes.
  intro x hx y hy
  have h1_le_rinv : (1 : ℝ≥0) ≤ r⁻¹ ^ (γ : ℝ) := by
    have h1_le : (1 : ℝ≥0) ≤ r⁻¹ := one_le_inv₀ hr0 |>.2 hr1.le
    exact NNReal.one_le_rpow h1_le γ.coe_nonneg
  rcases eq_zero_or_pos (edist x y) with hxy0 | hxy_pos
  · -- Regime 1: `edist x y = 0`; let `m → ∞` in the scale-`m` bound.
    have hle_all : ∀ m : ℕ,
        edist (f x) (f y) ≤ ((c_chain * K_f : ℝ≥0) : ℝ≥0∞) * ((r ^ (γ : ℝ) : ℝ≥0) : ℝ≥0∞) ^ m := by
      intro m
      simpa [ENNReal.coe_rpow_of_ne_zero hr0.ne', ENNReal.pow_rpow_comm] using
        hscale hx hy m (by simp [hxy0])
    have htend : Tendsto
        (fun m : ℕ ↦ ((c_chain * K_f : ℝ≥0) : ℝ≥0∞) * ((r ^ (γ : ℝ) : ℝ≥0) : ℝ≥0∞) ^ m)
        atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (ENNReal.coe_lt_one_iff.2 hrγ_lt))
        (Or.inr ENNReal.coe_ne_top)
    have h0 : edist (f x) (f y) ≤ 0 := ge_of_tendsto' htend hle_all
    simp [nonpos_iff_eq_zero.1 h0]
  · rcases le_or_gt (edist x y) 1 with hxy_le1 | hxy_gt1
    · -- Regime 2: `0 < edist x y ≤ 1`; pick `m` with `r ^ (m + 1) < edist x y ≤ r ^ m`.
      have hex_lt : ∃ k : ℕ, (r : ℝ≥0∞) ^ k < edist x y :=
        ((tendsto_order.1 (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
          (ENNReal.coe_lt_one_iff.2 hr1))).2 _ hxy_pos).exists
      let k₀ := Nat.find hex_lt
      have hk₀_spec : (r : ℝ≥0∞) ^ k₀ < edist x y := Nat.find_spec hex_lt
      have hk₀_pos : 0 < k₀ := by
        by_contra hk0
        have : k₀ = 0 := Nat.eq_zero_of_not_pos hk0
        rw [this, pow_zero] at hk₀_spec
        exact (hxy_le1.trans_lt hk₀_spec).false
      let m := k₀ - 1
      have hm_succ : m + 1 = k₀ := Nat.sub_add_cancel hk₀_pos
      have hm_le : edist x y ≤ (r : ℝ≥0∞) ^ m :=
        le_of_not_gt (Nat.find_min hex_lt (by omega))
      have hm_gt : (r : ℝ≥0∞) ^ m ≤ (r⁻¹ : ℝ≥0) * edist x y := by
        have hrm : (r : ℝ≥0∞) ^ m = (r⁻¹ : ℝ≥0) * (r : ℝ≥0∞) ^ (m + 1) := by
          rw [pow_succ', ← mul_assoc, ← ENNReal.coe_mul, inv_mul_cancel₀ hr0.ne',
            ENNReal.coe_one, one_mul]
        rw [hrm, hm_succ]
        exact mul_le_mul_right hk₀_spec.le _
      calc
        edist (f x) (f y) ≤ ((c_chain * K_f : ℝ≥0) : ℝ≥0∞) * ((r : ℝ≥0∞) ^ m) ^ (γ : ℝ) :=
          hscale hx hy m hm_le
        _ ≤ ((c_chain * K_f : ℝ≥0) : ℝ≥0∞) * ((r⁻¹ : ℝ≥0) * edist x y) ^ (γ : ℝ) := by
          gcongr
        _ = ((C_H * K_f : ℝ≥0) : ℝ≥0∞) * edist x y ^ (γ : ℝ) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ γ.coe_nonneg,
            ← ENNReal.coe_rpow_of_nonneg _ γ.coe_nonneg]
          dsimp [C_H]
          ring
    · -- Regime 3: `1 < edist x y`; combine ancestor chains to `M 0` with the global star at `w₀`.
      obtain ⟨Nx, hNx⟩ := mem_iUnion.1 hx
      obtain ⟨Ny, hNy⟩ := mem_iUnion.1 hy
      let N := max Nx Ny
      have hxN : x ∈ M N := hM_mono (le_max_left Nx Ny) (Finset.mem_coe.1 hNx)
      have hyN : y ∈ M N := hM_mono (le_max_right Nx Ny) (Finset.mem_coe.1 hNy)
      let u := descend parent N 0 x
      let v := descend parent N 0 y
      have huM0 : u ∈ M 0 := hdesc_mem (Nat.zero_le N) hxN
      have hvM0 : v ∈ M 0 := hdesc_mem (Nat.zero_le N) hyN
      have huw₀ : (u, w₀) ∈ E_all 0 := by
        refine Finset.mem_union_right _ ?_
        simp only [E_global, ↓reduceIte]
        exact Finset.mem_image_of_mem _ huM0
      have hvw₀ : (v, w₀) ∈ E_all 0 := by
        refine Finset.mem_union_right _ ?_
        simp only [E_global, ↓reduceIte]
        exact Finset.mem_image_of_mem _ hvM0
      have hf_uv : edist (f u) (f v) ≤ 2 * (K_f : ℝ≥0∞) := by
        calc
          edist (f u) (f v) ≤ edist (f u) (f w₀) + edist (f w₀) (f v) := edist_triangle _ _ _
          _ = edist (f u) (f w₀) + edist (f v) (f w₀) := by rw [edist_comm (f w₀) (f v)]
          _ ≤ (K_f : ℝ≥0∞) + (K_f : ℝ≥0∞) := by
            have h1 := hf_edge 0 huw₀
            have h2 := hf_edge 0 hvw₀
            simp only [pow_zero, ENNReal.one_rpow, mul_one] at h1 h2
            exact add_le_add h1 h2
          _ = 2 * (K_f : ℝ≥0∞) := (two_mul _).symm
      have hx_u := hdesc_f (Nat.zero_le N) hxN
      have hy_v := hdesc_f (Nat.zero_le N) hyN
      simp only [pow_zero, ENNReal.one_rpow, mul_one] at hx_u hy_v
      have hCH_le : c_chain * K_f ≤ C_H * K_f :=
        mul_le_mul_of_nonneg_right (le_mul_of_one_le_right' h1_le_rinv) zero_le
      calc
        edist (f x) (f y) ≤ edist (f x) (f u) + edist (f u) (f v) + edist (f v) (f y) :=
          edist_triangle4 _ _ _ _
        _ = edist (f x) (f u) + edist (f u) (f v) + edist (f y) (f v) := by
          rw [edist_comm (f v) (f y)]
        _ ≤ (((1 - r ^ (γ : ℝ))⁻¹ * K_f : ℝ≥0) : ℝ≥0∞) + 2 * (K_f : ℝ≥0∞) +
              (((1 - r ^ (γ : ℝ))⁻¹ * K_f : ℝ≥0) : ℝ≥0∞) :=
          add_le_add (add_le_add hx_u hf_uv) hy_v
        _ = ((c_chain * K_f : ℝ≥0) : ℝ≥0∞) * 1 := by
          dsimp [c_chain]; ring
        _ ≤ ((C_H * K_f : ℝ≥0) : ℝ≥0∞) * edist x y ^ (γ : ℝ) := by
          gcongr
          rw [← ENNReal.one_rpow (γ : ℝ)]
          exact ENNReal.rpow_le_rpow hxy_gt1.le γ.coe_nonneg

end MultiscaleChaining

end TauCeti
