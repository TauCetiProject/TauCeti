/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.CoveringExponent
public import Mathlib.Topology.MetricSpace.Holder
import Mathlib.Analysis.SpecificLimits.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Sparse multiscale chaining under a covering-exponent bound

To deduce sample-path Hölder regularity on a metric parameter set `A` with covering exponent `d`
for every exponent `γ < (q - d) / p` (rather than `(q - 2 d) / p`), the edge family at dyadic scale
`2⁻ⁿ` cannot consist of all pairs in an `ε`-net, whose cardinality scales like `2^{2 d n}`. Instead
we combine parent edges between nested minimal covers with a ball-growing star cover at each scale:

1. **Ball-growing star cover (`Finset.exists_star_edges_of_card_le_pow`).** Given a finite set `S`
   in a pseudoemetric space with `|S| ≤ b ^ t` (`t ≥ 1`) and a threshold `R`, growing concentric
   shells of radii `R, 2 R, …, t R` around a point `x₀ ∈ U` always finds a shell index `k < t`
   where `|B((k + 1) R)| ≤ b |B(k R)|`. Recording the star edges `(y, x₀)` for `y ∈ B((k + 1) R)`
   and recursing on `U \ B(k R)` produces at most `b |S|` edges of length at most `t R` such that
   every pair `x, y ∈ S` with `edist x y ≤ R` shares a common star centre in two hops.
2. **Multiscale chaining (`Metric.HasCoveringExponent.exists_countable_dense_edges`).** When `A`
   satisfies `Metric.HasCoveringExponent A c d` (`c ≠ ∞`) and `d < d'`, `0 ≤ d` follows
   automatically whenever `A` is nonempty (`Metric.HasCoveringExponent.nonneg_of_nonempty`), and
   choosing an intermediate exponent `d₁ ∈ (d, d')`, a shell count `t` with `d₁ (1 + 1 / t) ≤ d'`,
   and a dyadic shift `L = 5 t` yields nested finite subsets `Vₙ ⊆ A` whose union `D`
   `2⁻ⁿ`-approximates `A`, together with at most `C · 2^{d' n}` edges at scale `2⁻ⁿ` whose
   `γ`-Hölder edge bounds transfer to `HolderOnWith` on `D`. We also record
   `Isometry.hasCoveringExponent_of_injOn` and `Isometry.hasCoveringExponent` for pulling covering
   exponents back along isometries.

## References

* V. Krätschmer, M. Urusov, *A general Kolmogorov–Chentsov type theorem on general metric spaces*,
  arXiv:2107.13837v2, Theorem 1.1.
-/

public section

open Metric Set Filter
open scoped ENNReal NNReal Topology

/-- Pulling back along an isometry that is injective on `A` preserves `HasCoveringExponent` on any
pseudoemetric space. -/
theorem Isometry.hasCoveringExponent_of_injOn {X Y : Type*} [PseudoEMetricSpace X]
    [PseudoEMetricSpace Y] {f : X → Y} (hf : Isometry f) {A : Set X} (hinj : InjOn f A)
    {c : ℝ≥0∞} {d : ℝ} (h : HasCoveringExponent (f '' A) c d) :
    HasCoveringExponent A c d where
  ediam_lt_top := hf.ediam_image A ▸ h.ediam_lt_top
  coveringNumber_le ε hε := by
    rw [← hf.coveringNumber_image' hinj]
    exact h.coveringNumber_le ε (hf.ediam_image A ▸ hε)

/-- Pulling back along an isometry from an extended metric space preserves `HasCoveringExponent`. -/
theorem Isometry.hasCoveringExponent {X Y : Type*} [EMetricSpace X] [PseudoEMetricSpace Y]
    {f : X → Y} (hf : Isometry f) {A : Set X} {c : ℝ≥0∞} {d : ℝ}
    (h : HasCoveringExponent (f '' A) c d) :
    HasCoveringExponent A c d :=
  hf.hasCoveringExponent_of_injOn hf.injective.injOn h

/-- A nonempty set with covering exponent `d` satisfies `0 ≤ d`. -/
theorem Metric.HasCoveringExponent.nonneg_of_nonempty {T : Type*} [PseudoEMetricSpace T]
    {A : Set T} {c : ℝ≥0∞} {d : ℝ} (h : HasCoveringExponent A c d)
    (hA : A.Nonempty) : 0 ≤ d := by
  by_contra! hd
  have h0 := h.coveringNumber_le 0 zero_le
  rw [ENNReal.coe_zero, ENNReal.inv_zero, ENNReal.top_rpow_of_neg hd, mul_zero,
    nonpos_iff_eq_zero, ENat.toENNReal_eq_zero, coveringNumber_eq_zero] at h0
  exact hA.ne_empty h0

private lemma exists_shell_card_le_mul {T : Type*} [PseudoEMetricSpace T]
    {U : Finset T} {x₀ : T} (hx₀ : x₀ ∈ U) {t : ℕ} (ht : t ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hUbt : (U.card : ℝ) ≤ b ^ t) (R : ℝ≥0∞) :
    ∃ k < t,
      (((U.filter fun z ↦ edist x₀ z ≤ ((k + 1 : ℕ) : ℝ≥0∞) * R).card : ℕ) : ℝ) ≤
        b * (U.filter fun z ↦ edist x₀ z ≤ (k : ℝ≥0∞) * R).card := by
  classical
  let B : ℕ → Finset T := fun k ↦ U.filter fun z ↦ edist x₀ z ≤ (k : ℝ≥0∞) * R
  have hx₀B : ∀ k, x₀ ∈ B k := fun k ↦ by simp [B, hx₀]
  have hb_pos : 0 < b := by
    rcases hb.eq_or_lt with rfl | hpos
    · have h1 : (1 : ℝ) ≤ U.card := mod_cast Finset.one_le_card.mpr ⟨x₀, hx₀⟩
      have h0 : (0 : ℝ) ^ t = 0 := zero_pow ht
      linarith
    · exact hpos
  by_contra! hgrow
  have hpow : ∀ j ≤ t, b ^ j * (B 0).card ≤ ((B j).card : ℝ) := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ihj =>
      have hj_lt : j < t := Nat.lt_of_succ_le hj
      calc b ^ (j + 1) * (B 0).card
          = b * (b ^ j * (B 0).card) := by ring
        _ ≤ b * (B j).card := mul_le_mul_of_nonneg_left (ihj hj_lt.le) hb
        _ ≤ (B (j + 1)).card := (hgrow j hj_lt).le
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
  have ht_strict : b ^ (m + 1) * (B 0).card < (B (m + 1)).card :=
    calc b ^ (m + 1) * (B 0).card
        = b * (b ^ m * (B 0).card) := by ring
      _ ≤ b * (B m).card := mul_le_mul_of_nonneg_left (hpow m (Nat.le_succ m)) hb
      _ < (B (m + 1)).card := hgrow m (Nat.lt_succ_self m)
  have hB0 : (1 : ℝ) ≤ (B 0).card := mod_cast Finset.one_le_card.mpr ⟨x₀, hx₀B 0⟩
  have hBt : ((B (m + 1)).card : ℝ) ≤ U.card := mod_cast Finset.card_filter_le _ _
  have hbt_le : b ^ (m + 1) ≤ b ^ (m + 1) * (B 0).card :=
    le_mul_of_one_le_right (by positivity) hB0
  exact lt_irrefl _ (hbt_le.trans_lt (ht_strict.trans_le (hBt.trans hUbt)))

private lemma star_append_spec {T : Type*} [PseudoEMetricSpace T] [DecidableEq T]
    {U : Finset T} {x₀ : T} (hx₀ : x₀ ∈ U) {k t : ℕ} (hkt : k < t) {b : ℝ} {R : ℝ≥0∞}
    (hk_card : (((U.filter fun z ↦ edist x₀ z ≤ ((k + 1 : ℕ) : ℝ≥0∞) * R).card : ℕ) : ℝ) ≤
      b * (U.filter fun z ↦ edist x₀ z ≤ (k : ℝ≥0∞) * R).card)
    {L' : List (T × T)}
    (hL'_mem : ∀ e ∈ L', e.1 ∈ U \ U.filter (fun z ↦ edist x₀ z ≤ (k : ℝ≥0∞) * R) ∧
      e.2 ∈ U \ U.filter (fun z ↦ edist x₀ z ≤ (k : ℝ≥0∞) * R))
    (hL'_len : (L'.length : ℝ) ≤
      b * (U \ U.filter (fun z ↦ edist x₀ z ≤ (k : ℝ≥0∞) * R)).card)
    (hL'_edist : ∀ e ∈ L', edist e.1 e.2 ≤ t * R)
    (hL'_chain : ∀ x ∈ U \ U.filter (fun z ↦ edist x₀ z ≤ (k : ℝ≥0∞) * R),
      ∀ y ∈ U \ U.filter (fun z ↦ edist x₀ z ≤ (k : ℝ≥0∞) * R),
        edist x y ≤ R → ∃ z, (x, z) ∈ L' ∧ (y, z) ∈ L') :
    let L := ((U.filter fun z ↦ edist x₀ z ≤ ((k + 1 : ℕ) : ℝ≥0∞) * R).toList.map
      fun y ↦ (y, x₀)) ++ L'
    (∀ e ∈ L, e.1 ∈ U ∧ e.2 ∈ U) ∧
    (L.length : ℝ) ≤ b * U.card ∧
    (∀ e ∈ L, edist e.1 e.2 ≤ t * R) ∧
    (∀ x ∈ U, ∀ y ∈ U, edist x y ≤ R → ∃ z, (x, z) ∈ L ∧ (y, z) ∈ L) := by
  let B : ℕ → Finset T := fun j ↦ U.filter fun z ↦ edist x₀ z ≤ (j : ℝ≥0∞) * R
  let Lstar : List (T × T) := (B (k + 1)).toList.map fun y ↦ (y, x₀)
  have hcard_split : (U \ B k).card + (B k).card = U.card :=
    Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ U)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
      exact ⟨Finset.filter_subset _ U (Finset.mem_toList.mp hy), hx₀⟩
    · exact ⟨Finset.sdiff_subset (hL'_mem e he).1, Finset.sdiff_subset (hL'_mem e he).2⟩
  · rw [List.length_append, Nat.cast_add]
    have hLstar_len : Lstar.length = (B (k + 1)).card := by simp [Lstar]
    have hsplitR : (U.card : ℝ) = (U \ B k).card + (B k).card := by exact_mod_cast hcard_split.symm
    rw [hLstar_len, hsplitR, mul_add]
    linarith
  · intro e he
    rcases List.mem_append.mp he with he | he
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp he
      have hyB : edist x₀ y ≤ ((k + 1 : ℕ) : ℝ≥0∞) * R :=
        (Finset.mem_filter.mp (Finset.mem_toList.mp hy)).2
      rw [edist_comm]
      exact hyB.trans (mul_le_mul' (Nat.cast_le.mpr (Nat.succ_le_of_lt hkt)) le_rfl)
    · exact hL'_edist e he
  · intro x hx y hy hxy
    have hmem_B1 {u v : T} (hu : u ∈ B k) (hv : v ∈ U) (huv : edist u v ≤ R) :
        v ∈ B (k + 1) := by
      refine Finset.mem_filter.mpr ⟨hv, (edist_triangle x₀ u v).trans ?_⟩
      exact (add_le_add (Finset.mem_filter.mp hu).2 huv).trans_eq
        (by rw [Nat.cast_add, Nat.cast_one, add_one_mul])
    by_cases hxk : x ∈ B k
    · exact ⟨x₀, List.mem_append_left _ (List.mem_map.mpr
        ⟨x, Finset.mem_toList.mpr (hmem_B1 hxk hx (by simp)), rfl⟩),
        List.mem_append_left _ (List.mem_map.mpr
          ⟨y, Finset.mem_toList.mpr (hmem_B1 hxk hy hxy), rfl⟩)⟩
    · by_cases hyk : y ∈ B k
      · exact ⟨x₀, List.mem_append_left _ (List.mem_map.mpr
          ⟨x, Finset.mem_toList.mpr (hmem_B1 hyk hx (edist_comm x y ▸ hxy)), rfl⟩),
          List.mem_append_left _ (List.mem_map.mpr
            ⟨y, Finset.mem_toList.mpr (hmem_B1 hyk hy (by simp)), rfl⟩)⟩
      · obtain ⟨z, hxz, hyz⟩ := hL'_chain x (Finset.mem_sdiff.mpr ⟨hx, hxk⟩)
          y (Finset.mem_sdiff.mpr ⟨hy, hyk⟩) hxy
        exact ⟨z, List.mem_append_right _ hxz, List.mem_append_right _ hyz⟩

private lemma exists_list_star_edges {T : Type*} [PseudoEMetricSpace T]
    {t : ℕ} (ht : t ≠ 0) {b : ℝ} (hb : 0 ≤ b) {R : ℝ≥0∞} :
    ∀ (n : ℕ) (U : Finset T), U.card ≤ n → (U.card : ℝ) ≤ b ^ t →
      ∃ L : List (T × T),
        (∀ e ∈ L, e.1 ∈ U ∧ e.2 ∈ U) ∧
        (L.length : ℝ) ≤ b * U.card ∧
        (∀ e ∈ L, edist e.1 e.2 ≤ t * R) ∧
        (∀ x ∈ U, ∀ y ∈ U, edist x y ≤ R → ∃ z, (x, z) ∈ L ∧ (y, z) ∈ L) := by
  classical
  intro n
  induction n with
  | zero =>
    intro U hU _
    have hU0 : U = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hU)
    subst hU0
    exact ⟨[], by simp, by simp, by simp, by simp⟩
  | succ n ih =>
    intro U hUn hUbt
    rcases U.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · exact ⟨[], by simp, by simp, by simp, by simp⟩
    let B : ℕ → Finset T := fun k ↦ U.filter fun z ↦ edist x₀ z ≤ (k : ℝ≥0∞) * R
    obtain ⟨k, hkt, hk_card⟩ := exists_shell_card_le_mul hx₀ ht hb hUbt R
    have hcard_split : (U \ B k).card + (B k).card = U.card :=
      Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ U)
    have hBk_pos : 0 < (B k).card := Finset.card_pos.mpr ⟨x₀, by simp [B, hx₀]⟩
    have hU'_bt : ((U \ B k).card : ℝ) ≤ b ^ t :=
      (Nat.cast_le.mpr (Finset.card_le_card Finset.sdiff_subset)).trans hUbt
    obtain ⟨L', hL'_mem, hL'_len, hL'_edist, hL'_chain⟩ := ih (U \ B k) (by omega) hU'_bt
    exact ⟨_, star_append_spec hx₀ hkt hk_card hL'_mem hL'_len hL'_edist hL'_chain⟩

/-- **Sparse two-hop star cover on a finite set.** If `S` is a finite subset of a pseudoemetric
space with `|S| ≤ b ^ t` (`t ≠ 0`, `0 ≤ b`), then for any threshold `R : ℝ≥0∞` there is a family
of at most `b |S|` edges in `S` of length at most `t R` such that every pair `x, y ∈ S` at
extended distance at most `R` is joined in two hops through a common centre. -/
theorem Finset.exists_star_edges_of_card_le_pow {T : Type*} [PseudoEMetricSpace T]
    (S : Finset T) (R : ℝ≥0∞) {t : ℕ} (ht : t ≠ 0) {b : ℝ} (hb : 0 ≤ b)
    (hcard : (S.card : ℝ) ≤ b ^ t) :
    ∃ (m : ℕ) (u v : Fin m → T),
      (∀ i, u i ∈ S ∧ v i ∈ S) ∧
      (m : ℝ) ≤ b * S.card ∧
      (∀ i, edist (u i) (v i) ≤ t * R) ∧
      (∀ x ∈ S, ∀ y ∈ S, edist x y ≤ R → ∃ i j, u i = x ∧ u j = y ∧ v i = v j) := by
  obtain ⟨L, hmem, hlen, hedist, hchain⟩ := exists_list_star_edges ht hb S.card S le_rfl hcard
  refine ⟨L.length, fun i ↦ (L.get i).1, fun i ↦ (L.get i).2,
    fun i ↦ hmem _ (L.get_mem i), hlen, fun i ↦ hedist _ (L.get_mem i), ?_⟩
  intro x hx y hy hxy
  obtain ⟨z, hxz, hyz⟩ := hchain x hx y hy hxy
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hxz
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp hyz
  exact ⟨i, j, congrArg Prod.fst hi, congrArg Prod.fst hj,
    (congrArg Prod.snd hi).trans (congrArg Prod.snd hj).symm⟩

namespace Metric

/-- Parent-chain descent across nested covers `V`: starting at `z ∈ V (m + k)`, stepping along
projections `π` reaches a point `z' ∈ V m` while accumulating geometric distance and `f`-increment
sums. -/
private lemma exists_descent_mem {T E : Type*} [PseudoEMetricSpace T] [PseudoEMetricSpace E]
    {V : ℕ → Finset T} {π : ℕ → T → T} {L : ℕ}
    (hπ_mem : ∀ n z, z ∈ V (n + 1) → π n z ∈ V n)
    (hπ_edist : ∀ n z, z ∈ V (n + 1) → edist z (π n z) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + L))
    {f : T → E} {K γ : ℝ≥0}
    (hπ_f : ∀ n z, z ∈ V (n + 1) →
      edist (f z) (f (π n z)) ≤ (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ))
    (m : ℕ) :
    ∀ k : ℕ, ∀ z ∈ V (m + k), ∃ z' ∈ V m,
      edist z z' ≤ ∑ j ∈ Finset.range k, (2⁻¹ : ℝ≥0∞) ^ (m + j + L) ∧
      edist (f z) (f z') ≤
        (K : ℝ≥0∞) * ∑ j ∈ Finset.range k, ((2⁻¹ : ℝ≥0∞) ^ (m + j)) ^ (γ : ℝ) := by
  intro k
  induction k with
  | zero =>
    intro z hz
    exact ⟨z, hz, by simp, by simp⟩
  | succ k ih =>
    intro z hz
    have hz1 : z ∈ V ((m + k) + 1) := by simpa [Nat.add_assoc] using hz
    obtain ⟨z', hz'V, hz'_ed, hz'_f⟩ := ih (π (m + k) z) (hπ_mem (m + k) z hz1)
    refine ⟨z', hz'V, ?_, ?_⟩
    · rw [Finset.sum_range_succ, add_comm (∑ j ∈ _, _)]
      exact (edist_triangle z (π (m + k) z) z').trans (add_le_add (hπ_edist (m + k) z hz1) hz'_ed)
    · rw [Finset.sum_range_succ, mul_add, add_comm ((K : ℝ≥0∞) * ∑ j ∈ _, _)]
      exact (edist_triangle (f z) (f (π (m + k) z)) (f z')).trans
        (add_le_add (hπ_f (m + k) z hz1) hz'_f)

private lemma exists_descent_geom {T E : Type*} [PseudoEMetricSpace T] [PseudoEMetricSpace E]
    {V : ℕ → Finset T} {π : ℕ → T → T} {L : ℕ}
    (hπ_mem : ∀ n z, z ∈ V (n + 1) → π n z ∈ V n)
    (hπ_edist : ∀ n z, z ∈ V (n + 1) → edist z (π n z) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + L))
    {f : T → E} {K γ : ℝ≥0}
    (hπ_f : ∀ n z, z ∈ V (n + 1) →
      edist (f z) (f (π n z)) ≤ (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ))
    (m q : ℕ) {z : T} (hz : z ∈ V (m + q)) :
    ∃ z' ∈ V m, edist z z' ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ (m + L) ∧
      edist (f z) (f z') ≤
        (K : ℝ≥0∞) * (1 - (2⁻¹ : ℝ≥0∞) ^ (γ : ℝ))⁻¹ * ((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ) := by
  obtain ⟨z', hz'V, hz'_ed, hz'_f⟩ := exists_descent_mem hπ_mem hπ_edist hπ_f m q z hz
  refine ⟨z', hz'V, ?_, ?_⟩
  · calc edist z z'
        ≤ ∑ j ∈ Finset.range q, (2⁻¹ : ℝ≥0∞) ^ (m + L) * (2⁻¹ : ℝ≥0∞) ^ j := by
            refine hz'_ed.trans_eq (Finset.sum_congr rfl fun j _ ↦ ?_)
            simp [pow_add]
            ring
      _ ≤ (2⁻¹ : ℝ≥0∞) ^ (m + L) * ∑' j : ℕ, (2⁻¹ : ℝ≥0∞) ^ j := by
            rw [← Finset.mul_sum]
            gcongr
            exact CompleteLattice.summable.sum_le_tsum _ fun _ _ ↦ zero_le
      _ = 2 * (2⁻¹ : ℝ≥0∞) ^ (m + L) := by
            rw [ENNReal.tsum_geometric, mul_comm]
            norm_num
  · calc edist (f z) (f z')
        ≤ (K : ℝ≥0∞) * ∑ j ∈ Finset.range q,
            ((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ) * (((2⁻¹ : ℝ≥0∞) ^ (γ : ℝ)) ^ j) := by
            refine hz'_f.trans_eq (congrArg ((K : ℝ≥0∞) * ·) (Finset.sum_congr rfl fun j _ ↦ ?_))
            rw [pow_add, ENNReal.mul_rpow_of_nonneg _ _ γ.coe_nonneg,
              ENNReal.pow_rpow_comm _ j]
      _ ≤ (K : ℝ≥0∞) * (((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ) *
            ∑' j : ℕ, ((2⁻¹ : ℝ≥0∞) ^ (γ : ℝ)) ^ j) := by
            rw [← Finset.mul_sum]
            gcongr
            exact CompleteLattice.summable.sum_le_tsum _ fun _ _ ↦ zero_le
      _ = (K : ℝ≥0∞) * (1 - (2⁻¹ : ℝ≥0∞) ^ (γ : ℝ))⁻¹ * ((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ) := by
            rw [ENNReal.tsum_geometric]
            ring

private lemma edist_le_of_parent_and_star_scale {T E : Type*} [PseudoEMetricSpace T]
    [PseudoEMetricSpace E] {V : ℕ → Finset T} (hV_mono : Monotone V) {π : ℕ → T → T} {L : ℕ}
    (hπ_mem : ∀ n z, z ∈ V (n + 1) → π n z ∈ V n)
    (hπ_edist : ∀ n z, z ∈ V (n + 1) → edist z (π n z) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + L))
    {m_star : ℕ → ℕ} {u_star v_star : (n : ℕ) → Fin (m_star n) → T}
    (hstar_chain : ∀ n, ∀ x ∈ V n, ∀ y ∈ V n, edist x y ≤ 5 * (2⁻¹ : ℝ≥0∞) ^ (n + L) →
      ∃ i j, u_star n i = x ∧ u_star n j = y ∧ v_star n i = v_star n j)
    {γ : ℝ≥0} {f : T → E} {K : ℝ≥0}
    (hparent_f : ∀ n z, z ∈ V (n + 1) →
      edist (f z) (f (π n z)) ≤ (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ))
    (hstar_f : ∀ n i,
      edist (f (u_star n i)) (f (v_star n i)) ≤ (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ))
    {x y : T} (hx : x ∈ ⋃ n, (V n : Set T)) (hy : y ∈ ⋃ n, (V n : Set T))
    (m : ℕ) (hxy : edist x y ≤ (2⁻¹ : ℝ≥0∞) ^ (m + L)) :
    edist (f x) (f y) ≤
      2 * ((1 - (2⁻¹ : ℝ≥0∞) ^ (γ : ℝ))⁻¹ + 1) * (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ) := by
  let S_ser : ℝ≥0∞ := (1 - (2⁻¹ : ℝ≥0∞) ^ (γ : ℝ))⁻¹
  obtain ⟨nx, hnx⟩ := mem_iUnion.mp hx
  obtain ⟨ny, hny⟩ := mem_iUnion.mp hy
  let q : ℕ := max nx ny
  obtain ⟨x', hx'V, hx'_ed, hx'_f⟩ := exists_descent_geom hπ_mem hπ_edist hparent_f m q
    (hV_mono ((le_max_left nx ny).trans (Nat.le_add_left q m)) hnx)
  obtain ⟨y', hy'V, hy'_ed, hy'_f⟩ := exists_descent_geom hπ_mem hπ_edist hparent_f m q
    (hV_mono ((le_max_right nx ny).trans (Nat.le_add_left q m)) hny)
  have hxy'_ed : edist x' y' ≤ 5 * (2⁻¹ : ℝ≥0∞) ^ (m + L) := by
    calc edist x' y'
        ≤ edist x' x + edist x y + edist y y' := edist_triangle4 x' x y y'
      _ ≤ 2 * (2⁻¹ : ℝ≥0∞) ^ (m + L) + (2⁻¹ : ℝ≥0∞) ^ (m + L) +
            2 * (2⁻¹ : ℝ≥0∞) ^ (m + L) := by
          rw [edist_comm x' x]
          exact add_le_add (add_le_add hx'_ed hxy) hy'_ed
      _ = 5 * (2⁻¹ : ℝ≥0∞) ^ (m + L) := by ring
  obtain ⟨i₁, i₂, hi₁, hi₂, hv⟩ := hstar_chain m x' hx'V y' hy'V hxy'_ed
  have hx'y'_f : edist (f x') (f y') ≤ 2 * (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ) := by
    calc edist (f x') (f y')
        ≤ edist (f (u_star m i₁)) (f (v_star m i₁)) +
            edist (f (v_star m i₂)) (f (u_star m i₂)) := by
            simpa [hi₁, hi₂, hv] using edist_triangle (f x') (f (v_star m i₁)) (f y')
      _ ≤ (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ) +
            (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ) := by
            rw [edist_comm (f (v_star m i₂))]
            exact add_le_add (hstar_f m i₁) (hstar_f m i₂)
      _ = 2 * (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ) := by ring
  calc edist (f x) (f y)
      ≤ edist (f x) (f x') + edist (f x') (f y') + edist (f y') (f y) :=
        edist_triangle4 (f x) (f x') (f y') (f y)
    _ ≤ (K : ℝ≥0∞) * S_ser * ((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ) +
          2 * (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ) +
          (K : ℝ≥0∞) * S_ser * ((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ) := by
        rw [edist_comm (f y')]
        exact add_le_add (add_le_add hx'_f hx'y'_f) hy'_f
    _ = 2 * (S_ser + 1) * (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ) := by ring

private lemma edist_le_mul_rpow_of_fine {T E : Type*} [PseudoEMetricSpace T]
    [PseudoEMetricSpace E] {L : ℕ} {γ K K₀ : ℝ≥0} {S_ser : ℝ≥0∞} {f : T → E} {x y : T}
    (hxy_pos : edist x y ≠ 0) (hxyL : edist x y ≤ (2⁻¹ : ℝ≥0∞) ^ L)
    (hscale : ∀ m, edist x y ≤ (2⁻¹ : ℝ≥0∞) ^ (m + L) →
      edist (f x) (f y) ≤ 2 * (S_ser + 1) * (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ)) :
    edist (f x) (f y) ≤
      2 * (S_ser + 1) * ((2 : ℝ≥0∞) ^ (L + 1)) ^ (γ : ℝ) *
        ((K : ℝ≥0∞) + K₀) * edist x y ^ (γ : ℝ) := by
  have hex_n : ∃ n : ℕ, ¬ (edist x y ≤ (2⁻¹ : ℝ≥0∞) ^ (n + L)) := by
    have hlim0 : Tendsto (fun n : ℕ ↦ (2⁻¹ : ℝ≥0∞) ^ (n + L)) atTop (𝓝 0) := by
      simpa [pow_add] using ENNReal.Tendsto.mul_const
        (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num)) (Or.inr (by finiteness))
    exact ((tendsto_order.1 hlim0).2 (edist x y) (pos_iff_ne_zero.mpr hxy_pos)).exists.imp
      fun n hn ↦ not_le.mpr hn
  classical
  have hn₀_ne : Nat.find hex_n ≠ 0 := fun h0 ↦ by
    have hspec := Nat.find_spec hex_n
    rw [h0, zero_add] at hspec
    exact hspec hxyL
  obtain ⟨m, hm_eq⟩ := Nat.exists_eq_succ_of_ne_zero hn₀_ne
  have hm_le : edist x y ≤ (2⁻¹ : ℝ≥0∞) ^ (m + L) :=
    not_not.mp (Nat.find_min hex_n (by omega))
  have hm_gt : (2⁻¹ : ℝ≥0∞) ^ (m + 1 + L) < edist x y := by
    have hspec := Nat.find_spec hex_n
    rw [hm_eq] at hspec
    exact not_le.mp hspec
  have h2m_le : (2⁻¹ : ℝ≥0∞) ^ m ≤ (2 : ℝ≥0∞) ^ (L + 1) * edist x y := by
    calc (2⁻¹ : ℝ≥0∞) ^ m
        = (2 : ℝ≥0∞) ^ (L + 1) * (2⁻¹ : ℝ≥0∞) ^ (L + 1) * (2⁻¹ : ℝ≥0∞) ^ m := by
            rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]
      _ = (2 : ℝ≥0∞) ^ (L + 1) * (2⁻¹ : ℝ≥0∞) ^ (m + 1 + L) := by simp [pow_add]; ring
      _ ≤ (2 : ℝ≥0∞) ^ (L + 1) * edist x y := mul_le_mul' le_rfl hm_gt.le
  calc edist (f x) (f y)
      ≤ 2 * (S_ser + 1) * (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ m) ^ (γ : ℝ) := hscale m hm_le
    _ ≤ 2 * (S_ser + 1) * (K : ℝ≥0∞) *
          (((2 : ℝ≥0∞) ^ (L + 1)) ^ (γ : ℝ) * edist x y ^ (γ : ℝ)) := by
        gcongr
        exact (ENNReal.rpow_le_rpow h2m_le γ.coe_nonneg).trans_eq
          (ENNReal.mul_rpow_of_nonneg _ _ γ.coe_nonneg)
    _ = 2 * (S_ser + 1) * ((2 : ℝ≥0∞) ^ (L + 1)) ^ (γ : ℝ) *
          (K : ℝ≥0∞) * edist x y ^ (γ : ℝ) := by ring
    _ ≤ 2 * (S_ser + 1) * ((2 : ℝ≥0∞) ^ (L + 1)) ^ (γ : ℝ) *
          ((K : ℝ≥0∞) + K₀) * edist x y ^ (γ : ℝ) := by
        gcongr
        exact le_self_add

private lemma edist_le_mul_rpow_of_coarse {T E : Type*} [PseudoEMetricSpace T]
    [PseudoEMetricSpace E] {V : ℕ → Finset T} {π : ℕ → T → T} {L : ℕ}
    (hπ_mem : ∀ n z, z ∈ V (n + 1) → π n z ∈ V n)
    (hπ_edist : ∀ n z, z ∈ V (n + 1) → edist z (π n z) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + L))
    {γ K K₀ : ℝ≥0} {f : T → E}
    (hparent_f : ∀ n z, z ∈ V (n + 1) →
      edist (f z) (f (π n z)) ≤ (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ))
    (hf_V0 : ∀ x ∈ V 0, ∀ y ∈ V 0, edist (f x) (f y) ≤ K₀)
    {x y : T} (hx : x ∈ ⋃ n, (V n : Set T)) (hy : y ∈ ⋃ n, (V n : Set T))
    (hxy_ge : (2⁻¹ : ℝ≥0∞) ^ L ≤ edist x y) :
    let S_ser : ℝ≥0∞ := (1 - (2⁻¹ : ℝ≥0∞) ^ (γ : ℝ))⁻¹
    edist (f x) (f y) ≤
      2 * (S_ser + 1) * ((2 : ℝ≥0∞) ^ (L + 1)) ^ (γ : ℝ) *
        ((K : ℝ≥0∞) + K₀) * edist x y ^ (γ : ℝ) := by
  intro S_ser
  obtain ⟨nx, hnx⟩ := mem_iUnion.mp hx
  obtain ⟨ny, hny⟩ := mem_iUnion.mp hy
  obtain ⟨x₀, hx₀V, -, hx₀_f⟩ :=
    exists_descent_geom hπ_mem hπ_edist hparent_f 0 nx (by simpa using hnx)
  obtain ⟨y₀, hy₀V, -, hy₀_f⟩ :=
    exists_descent_geom hπ_mem hπ_edist hparent_f 0 ny (by simpa using hny)
  have hone_le : (1 : ℝ≥0∞) ≤ ((2 : ℝ≥0∞) ^ (L + 1)) ^ (γ : ℝ) * edist x y ^ (γ : ℝ) := by
    have h1 : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ (L + 1) * edist x y := by
      calc (1 : ℝ≥0∞) = (2 : ℝ≥0∞) ^ L * (2⁻¹ : ℝ≥0∞) ^ L := by
              rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow]
        _ ≤ (2 : ℝ≥0∞) ^ (L + 1) * edist x y :=
              mul_le_mul' (pow_le_pow_right₀ one_le_two (Nat.le_succ L)) hxy_ge
    simpa [ENNReal.mul_rpow_of_nonneg _ _ γ.coe_nonneg] using
      ENNReal.rpow_le_rpow h1 γ.coe_nonneg
  have hcoarse : edist (f x) (f y) ≤ 2 * (S_ser + 1) * ((K : ℝ≥0∞) + K₀) := by
    calc edist (f x) (f y)
        ≤ edist (f x) (f x₀) + edist (f x₀) (f y₀) + edist (f y₀) (f y) :=
          edist_triangle4 (f x) (f x₀) (f y₀) (f y)
      _ ≤ (K : ℝ≥0∞) * S_ser * 1 + K₀ + (K : ℝ≥0∞) * S_ser * 1 := by
          rw [edist_comm (f y₀)]
          exact add_le_add (add_le_add (by simpa using hx₀_f) (hf_V0 x₀ hx₀V y₀ hy₀V))
            (by simpa using hy₀_f)
      _ ≤ (2 * S_ser + 2) * (K : ℝ≥0∞) + (2 * S_ser + 2) * K₀ := by
          rw [show (K : ℝ≥0∞) * S_ser * 1 + K₀ + (K : ℝ≥0∞) * S_ser * 1 =
            2 * S_ser * (K : ℝ≥0∞) + 1 * K₀ by ring]
          exact add_le_add (mul_le_mul' le_self_add le_rfl)
            (mul_le_mul' (le_add_of_nonneg_of_le zero_le one_le_two) le_rfl)
      _ = 2 * (S_ser + 1) * ((K : ℝ≥0∞) + K₀) := by ring
  exact (hcoarse.trans_eq (mul_one _).symm).trans
    ((mul_le_mul' le_rfl hone_le).trans_eq (by ring))

/-- Given nested covers `V`, parent projections `π`, and two-hop star covers on each `V n`, edge
bounds of order `K · 2^{-n γ}` together with a coarse bound `K₀` on `V 0 × V 0` imply `HolderOnWith`
on `D = ⋃ n, V n`. -/
private lemma holderOnWith_iUnion_of_parent_and_star {T E : Type*} [PseudoEMetricSpace T]
    [PseudoEMetricSpace E] {V : ℕ → Finset T} (hV_mono : Monotone V) {π : ℕ → T → T} {L : ℕ}
    (hπ_mem : ∀ n z, z ∈ V (n + 1) → π n z ∈ V n)
    (hπ_edist : ∀ n z, z ∈ V (n + 1) → edist z (π n z) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + L))
    {m_star : ℕ → ℕ} {u_star v_star : (n : ℕ) → Fin (m_star n) → T}
    (hstar_chain : ∀ n, ∀ x ∈ V n, ∀ y ∈ V n, edist x y ≤ 5 * (2⁻¹ : ℝ≥0∞) ^ (n + L) →
      ∃ i j, u_star n i = x ∧ u_star n j = y ∧ v_star n i = v_star n j)
    {γ : ℝ≥0} (hγ : 0 < γ) {f : T → E} {K K₀ : ℝ≥0}
    (hparent_f : ∀ n z, z ∈ V (n + 1) →
      edist (f z) (f (π n z)) ≤ (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ))
    (hstar_f : ∀ n i,
      edist (f (u_star n i)) (f (v_star n i)) ≤ (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ))
    (hf_V0 : ∀ x ∈ V 0, ∀ y ∈ V 0, edist (f x) (f y) ≤ K₀) :
    HolderOnWith
      (2 * (((1 - (2⁻¹ : ℝ≥0∞) ^ (γ : ℝ))⁻¹).toNNReal + 1) *
        (2 : ℝ≥0) ^ (((L + 1 : ℕ) : ℝ) * γ) * (K + K₀))
      γ f (⋃ n, (V n : Set T)) := by
  let S_ser : ℝ≥0∞ := (1 - (2⁻¹ : ℝ≥0∞) ^ (γ : ℝ))⁻¹
  let M_H : ℝ≥0 := 2 * (S_ser.toNNReal + 1) * (2 : ℝ≥0) ^ (((L + 1 : ℕ) : ℝ) * γ)
  have h2γ_lt : (2⁻¹ : ℝ≥0∞) ^ (γ : ℝ) < 1 :=
    ENNReal.rpow_lt_one (by norm_num) (by exact_mod_cast hγ)
  have hS_ne_top : S_ser ≠ ∞ := ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr h2γ_lt).ne'
  have hMH_coe : ((M_H * (K + K₀) : ℝ≥0) : ℝ≥0∞) =
      2 * (S_ser + 1) * ((2 : ℝ≥0∞) ^ (L + 1)) ^ (γ : ℝ) * ((K : ℝ≥0∞) + K₀) := by
    simp only [M_H, ENNReal.coe_mul, ENNReal.coe_ofNat, ENNReal.coe_add, ENNReal.coe_one,
      ENNReal.coe_toNNReal hS_ne_top, ENNReal.coe_rpow_of_ne_zero two_ne_zero]
    rw [ENNReal.rpow_mul, ENNReal.rpow_natCast]
  intro x hx y hy
  have hscale := edist_le_of_parent_and_star_scale hV_mono hπ_mem hπ_edist hstar_chain
    hparent_f hstar_f hx hy
  rcases eq_or_ne (edist x y) 0 with hxy0 | hxy_pos
  · have hlim : Tendsto
        (fun m : ℕ ↦ 2 * (S_ser + 1) * (K : ℝ≥0∞) * (((2⁻¹ : ℝ≥0∞) ^ (γ : ℝ)) ^ m))
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one h2γ_lt)
        (Or.inr (by finiteness))
    exact (ge_of_tendsto' hlim fun m ↦ by
      simpa [ENNReal.pow_rpow_comm] using hscale m (by simp [hxy0])).trans zero_le
  · rw [hMH_coe]
    by_cases hxyL : edist x y ≤ (2⁻¹ : ℝ≥0∞) ^ L
    · exact edist_le_mul_rpow_of_fine hxy_pos hxyL hscale
    · exact edist_le_mul_rpow_of_coarse hπ_mem hπ_edist hparent_f hf_V0 hx hy (not_le.mp hxyL).le

private lemma card_minimalCover_dyadic_le {T : Type*} [PseudoEMetricSpace T]
    {A : Set T} {c : ℝ≥0} {d d₁ : ℝ} (hA : HasCoveringExponent A c d) (hd : 0 ≤ d)
    (hdd₁ : d ≤ d₁) (hd₁_pos : 0 < d₁) (L n : ℕ) :
    let ε : ℝ≥0 := (2⁻¹ : ℝ≥0) ^ (n + L)
    (((finite_minimalCover (ε := ε) (A := A)).toFinset.card : ℕ) : ℝ) ≤
      ((1 + (c : ℝ)) * ((2 : ℝ) ^ d₁) ^ L) * ((2 : ℝ) ^ d₁) ^ n := by
  let ε : ℝ≥0 := (2⁻¹ : ℝ≥0) ^ (n + L)
  have hcov_ne : coveringNumber ε A ≠ ⊤ :=
    hA.coveringNumber_ne_top (pow_ne_zero _ (by norm_num)) ENNReal.coe_ne_top hd
  let U : Finset T := (finite_minimalCover (ε := ε) (A := A)).toFinset
  have hencard : (U.card : ℝ≥0∞) = (coveringNumber ε A : ℝ≥0∞) := by
    have h1 : ((U : Set T).encard : ℝ≥0∞) = (coveringNumber ε A : ℝ≥0∞) := by
      simpa [U] using congrArg (fun x : ℕ∞ ↦ (x : ℝ≥0∞)) (encard_minimalCover hcov_ne)
    simpa using h1
  have hcard_enn : (U.card : ℝ≥0∞) ≤ (1 + (c : ℝ≥0∞)) * ((2 : ℝ≥0∞) ^ d₁) ^ (n + L) := by
    have hpow_ge_one : (1 : ℝ≥0∞) ≤ ((2 : ℝ≥0∞) ^ d₁) ^ (n + L) :=
      one_le_pow₀ (ENNReal.one_le_rpow one_le_two hd₁_pos)
    by_cases hle : (ε : ℝ≥0∞) ≤ ediam A
    · have hinv : ((ε : ℝ≥0∞)⁻¹) = (2 : ℝ≥0∞) ^ (n + L) := by simp [ε, ENNReal.inv_pow]
      calc (U.card : ℝ≥0∞)
          ≤ (c : ℝ≥0∞) * (ε : ℝ≥0∞)⁻¹ ^ d := hencard.le.trans (hA.coveringNumber_le ε hle)
        _ = (c : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (n + L)) ^ d := by rw [hinv]
        _ ≤ (c : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (n + L)) ^ d₁ := by
            gcongr
            exact one_le_pow₀ one_le_two
        _ ≤ (1 + (c : ℝ≥0∞)) * ((2 : ℝ≥0∞) ^ d₁) ^ (n + L) := by
            rw [ENNReal.pow_rpow_comm]
            gcongr
            exact le_add_self
    · have hcov1 : (U.card : ℝ≥0∞) ≤ 1 :=
        hencard.le.trans (mod_cast coveringNumber_le_one_of_ediam_le (not_le.mp hle).le)
      exact (hcov1.trans_eq (mul_one 1).symm).trans (mul_le_mul' le_self_add hpow_ge_one)
  have htoR := ENNReal.toReal_mono (by finiteness) hcard_enn
  simp only [ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_add ENNReal.one_ne_top
    ENNReal.coe_ne_top, ENNReal.toReal_one, ENNReal.coe_toReal, ENNReal.toReal_pow,
    ← ENNReal.toReal_rpow, ENNReal.toReal_ofNat] at htoR
  exact htoR.trans_eq (by simp [pow_add]; ring)

/-- Construct cumulative nested covers `V n = ⋃_{j ≤ n} U j` of `A` from minimal `2^{-(n+L)}`-covers
`U n`, together with geometric cardinality bounds `|V n| ≤ C₁ · (2 ^ d₁) ^ n`. -/
private lemma exists_nested_covers_of_hasCoveringExponent {T : Type*} [PseudoEMetricSpace T]
    {A : Set T} {c : ℝ≥0} {d d₁ : ℝ} (hA : HasCoveringExponent A c d) (hd : 0 ≤ d)
    (hdd₁ : d ≤ d₁) (hd₁_pos : 0 < d₁) (L : ℕ) :
    ∃ (U V : ℕ → Finset T) (C₁ : ℝ),
      0 < C₁ ∧ Monotone V ∧
      (∀ n, (V n : Set T) ⊆ A) ∧
      (∀ {j n}, j ≤ n → U j ⊆ V n) ∧
      (∀ n, IsCover ((2⁻¹ : ℝ≥0) ^ (n + L)) A (U n : Set T)) ∧
      (∀ n, ((V n).card : ℝ) ≤ C₁ * ((2 : ℝ) ^ d₁) ^ n) := by
  classical
  let ε : ℕ → ℝ≥0 := fun n ↦ (2⁻¹ : ℝ≥0) ^ (n + L)
  have hcov_ne : ∀ n, coveringNumber (ε n) A ≠ ⊤ :=
    fun n ↦ hA.coveringNumber_ne_top (pow_ne_zero _ (by norm_num)) ENNReal.coe_ne_top hd
  let U : ℕ → Finset T := fun n ↦ (finite_minimalCover (ε := ε n) (A := A)).toFinset
  have hUA : ∀ n, (U n : Set T) ⊆ A := fun n ↦ by simpa [U] using minimalCover_subset
  have hUcov : ∀ n, IsCover (ε n) A (U n : Set T) :=
    fun n ↦ by simpa [U] using isCover_minimalCover (hcov_ne n)
  let q₁ : ℝ := (2 : ℝ) ^ d₁
  have hq₁_gt : 1 < q₁ := Real.one_lt_rpow one_lt_two hd₁_pos
  let V : ℕ → Finset T := fun n ↦ (Finset.range (n + 1)).biUnion U
  have hUV : ∀ {j n}, j ≤ n → U j ⊆ V n := fun {j n} hjn ↦
    Finset.subset_biUnion_of_mem U (Finset.mem_range.mpr (Nat.lt_succ_of_le hjn))
  have hV_mono : Monotone V := fun m n hmn ↦
    Finset.biUnion_subset_biUnion_of_subset_left U (Finset.range_mono (Nat.add_le_add_right hmn 1))
  have hVA : ∀ n, (V n : Set T) ⊆ A := fun n x hx ↦ by
    simp only [V, Finset.coe_biUnion, Finset.mem_coe, mem_iUnion] at hx
    obtain ⟨j, _, hxj⟩ := hx
    exact hUA j hxj
  let C₁ : ℝ := max 1 (((1 + (c : ℝ)) * q₁ ^ L) * (q₁ / (q₁ - 1)))
  refine ⟨U, V, C₁, lt_of_lt_of_le zero_lt_one (le_max_left _ _), hV_mono, hVA, hUV, hUcov,
    fun n ↦ ?_⟩
  have hbi : ((V n).card : ℝ) ≤ ∑ j ∈ Finset.range (n + 1), ((U j).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  calc ((V n).card : ℝ)
      ≤ ∑ j ∈ Finset.range (n + 1), ((1 + (c : ℝ)) * q₁ ^ L) * q₁ ^ j :=
        hbi.trans (Finset.sum_le_sum fun j _ ↦
          card_minimalCover_dyadic_le hA hd hdd₁ hd₁_pos L j)
    _ = ((1 + (c : ℝ)) * q₁ ^ L) * ((q₁ ^ (n + 1) - 1) / (q₁ - 1)) := by
        rw [← Finset.mul_sum, geom_sum_eq hq₁_gt.ne']
    _ ≤ ((1 + (c : ℝ)) * q₁ ^ L) * (q₁ / (q₁ - 1) * q₁ ^ n) := by
        gcongr
        rw [div_mul_eq_mul_div, pow_succ']
        gcongr
        linarith
    _ ≤ C₁ * q₁ ^ n := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

private lemma card_parent_add_star_le {C₁ d₁ d' : ℝ} {t n v_succ v_cur m_star : ℕ}
    (hC₁_pos : 0 < C₁) (hd₁d' : d₁ < d')
    (ht_exp : d₁ * (1 + (t : ℝ)⁻¹) ≤ d')
    (hv_succ : (v_succ : ℝ) ≤ C₁ * ((2 : ℝ) ^ d₁) ^ (n + 1))
    (hv_cur : (v_cur : ℝ) ≤ C₁ * ((2 : ℝ) ^ d₁) ^ n)
    (hm_star : (m_star : ℝ) ≤ (C₁ * ((2 : ℝ) ^ d₁) ^ n) ^ (t : ℝ)⁻¹ * v_cur) :
    ((v_succ + m_star : ℕ) : ℝ≥0) ≤
      (C₁ * (2 : ℝ) ^ d₁ + C₁ ^ (1 + (t : ℝ)⁻¹)).toNNReal * ((2⁻¹ : ℝ≥0) ^ (-d')) ^ n := by
  let q₁ : ℝ := (2 : ℝ) ^ d₁
  rw [← NNReal.coe_le_coe, NNReal.coe_mul, Real.coe_toNNReal _ (by positivity)]
  push_cast
  have h2inv : (2⁻¹ : ℝ) ^ (-d') = (2 : ℝ) ^ d' := by
    rw [Real.inv_rpow zero_le_two, ← Real.rpow_neg zero_le_two, neg_neg]
  rw [h2inv]
  have hp1 : (v_succ : ℝ) ≤ (C₁ * q₁) * ((2 : ℝ) ^ d') ^ n := by
    calc (v_succ : ℝ)
        ≤ C₁ * q₁ ^ (n + 1) := hv_succ
      _ = (C₁ * q₁) * q₁ ^ n := by ring
      _ ≤ (C₁ * q₁) * ((2 : ℝ) ^ d') ^ n := by
          gcongr
          exact Real.rpow_le_rpow_of_exponent_le one_le_two hd₁d'.le
  have hp2 : (m_star : ℝ) ≤ C₁ ^ (1 + (t : ℝ)⁻¹) * ((2 : ℝ) ^ d') ^ n := by
    have hpos : 0 < C₁ * q₁ ^ n := by positivity
    calc (m_star : ℝ)
        ≤ (C₁ * q₁ ^ n) ^ (t : ℝ)⁻¹ * (C₁ * q₁ ^ n) :=
          hm_star.trans (mul_le_mul_of_nonneg_left hv_cur (by positivity))
      _ = (C₁ * q₁ ^ n) ^ ((t : ℝ)⁻¹ + 1) := (Real.rpow_add_one hpos.ne' _).symm
      _ = C₁ ^ (1 + (t : ℝ)⁻¹) * (q₁ ^ (1 + (t : ℝ)⁻¹)) ^ n := by
          rw [add_comm, Real.mul_rpow (by positivity) (by positivity),
            ← Real.rpow_natCast q₁, ← Real.rpow_mul (by positivity), mul_comm (n : ℝ),
            Real.rpow_mul (by positivity), Real.rpow_natCast]
      _ ≤ C₁ ^ (1 + (t : ℝ)⁻¹) * ((2 : ℝ) ^ d') ^ n := by
          gcongr
          calc q₁ ^ (1 + (t : ℝ)⁻¹)
              = (2 : ℝ) ^ (d₁ * (1 + (t : ℝ)⁻¹)) := (Real.rpow_mul zero_le_two _ _).symm
            _ ≤ (2 : ℝ) ^ d' := Real.rpow_le_rpow_of_exponent_le one_le_two ht_exp
  linarith

private lemma packed_chaining_edges_spec.{u, v} {T : Type v} [PseudoEMetricSpace T]
    {A : Set T} {U V : ℕ → Finset T} {π : ℕ → T → T} {t : ℕ}
    (hV_mono : Monotone V) (hVA : ∀ n, (V n : Set T) ⊆ A) (hUV : ∀ {j n}, j ≤ n → U j ⊆ V n)
    (hπ_memU : ∀ n x, π n x ∈ U n)
    (hπ_edist : ∀ n {x}, x ∈ A → edist x (π n x) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 5 * t))
    {m_star : ℕ → ℕ} {u_star v_star : (n : ℕ) → Fin (m_star n) → T}
    (hstar_mem : ∀ n i, u_star n i ∈ V n ∧ v_star n i ∈ V n)
    (hstar_edist : ∀ n i, edist (u_star n i) (v_star n i) ≤ t * (5 * (2⁻¹ : ℝ≥0∞) ^ (n + 5 * t)))
    (hstar_chain : ∀ n, ∀ x ∈ V n, ∀ y ∈ V n, edist x y ≤ 5 * (2⁻¹ : ℝ≥0∞) ^ (n + 5 * t) →
      ∃ i j, u_star n i = x ∧ u_star n j = y ∧ v_star n i = v_star n j) :
    let D : Set T := ⋃ n, (V n : Set T)
    let P_list : ℕ → List (T × T) := fun n ↦
      ((V (n + 1)).toList.map fun z ↦ (z, π n z)) ++
        (List.ofFn fun i : Fin (m_star n) ↦ (u_star n i, v_star n i))
    let k : ℕ → ℕ := fun n ↦ (P_list n).length
    let s : (n : ℕ) → Fin (k n) → T := fun n i ↦ (P_list n)[i.1].1
    let t_edge : (n : ℕ) → Fin (k n) → T := fun n i ↦ (P_list n)[i.1].2
    let M_H : ℝ≥0 → ℝ≥0 := fun γ ↦ 2 * (((1 - (2⁻¹ : ℝ≥0∞) ^ (γ : ℝ))⁻¹).toNNReal + 1) *
      (2 : ℝ≥0) ^ (((5 * t + 1 : ℕ) : ℝ) * γ)
    (∀ n i, s n i ∈ D ∧ t_edge n i ∈ D) ∧
    (∀ n i, edist (s n i) (t_edge n i) ≤ (2⁻¹ : ℝ≥0∞) ^ n) ∧
    (∀ {E : Type u} [PseudoEMetricSpace E] {γ : ℝ≥0}, 0 < γ →
      ∀ (f : T → E) (K K₀ : ℝ≥0),
        (∀ n i, edist (f (s n i)) (f (t_edge n i)) ≤ (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ)) →
        (∀ x ∈ V 0, ∀ y ∈ V 0, edist (f x) (f y) ≤ K₀) →
        HolderOnWith (M_H γ * (K + K₀)) γ f D) := by
  intro D P_list k s t_edge M_H
  have hVD : ∀ n, (V n : Set T) ⊆ D := fun n ↦ subset_iUnion (fun m ↦ (V m : Set T)) n
  refine ⟨fun n i ↦ ?_, fun n i ↦ ?_, fun hγ f K K₀ hf_edge hf_V0 ↦ ?_⟩
  · have hmem : (P_list n)[i.1] ∈ P_list n := List.getElem_mem i.2
    simp only [P_list, List.mem_append, List.mem_map, Finset.mem_toList, List.mem_ofFn] at hmem
    rcases hmem with ⟨z, hz, hpair⟩ | ⟨j, hpair⟩
    · dsimp only [s, t_edge]
      rw [← congrArg Prod.fst hpair, ← congrArg Prod.snd hpair]
      exact ⟨hVD (n + 1) hz, hVD n (hUV le_rfl (hπ_memU n z))⟩
    · dsimp only [s, t_edge]
      rw [← congrArg Prod.fst hpair, ← congrArg Prod.snd hpair]
      exact ⟨hVD n (hstar_mem n j).1, hVD n (hstar_mem n j).2⟩
  · have hmem : (P_list n)[i.1] ∈ P_list n := List.getElem_mem i.2
    simp only [P_list, List.mem_append, List.mem_map, Finset.mem_toList, List.mem_ofFn] at hmem
    rcases hmem with ⟨z, hz, hpair⟩ | ⟨j, hpair⟩
    · dsimp only [s, t_edge]
      rw [← congrArg Prod.fst hpair, ← congrArg Prod.snd hpair]
      exact (hπ_edist n (hVA (n + 1) hz)).trans
        (pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_add_right n (5 * t)))
    · dsimp only [s, t_edge]
      rw [← congrArg Prod.fst hpair, ← congrArg Prod.snd hpair]
      calc edist (u_star n j) (v_star n j)
          ≤ (t : ℝ≥0∞) * (5 * (2⁻¹ : ℝ≥0∞) ^ (n + 5 * t)) := hstar_edist n j
        _ = ((5 * t : ℕ) : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ (5 * t) * (2⁻¹ : ℝ≥0∞) ^ n := by
            simp [pow_add]; ring
        _ ≤ (2 ^ (5 * t) : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ (5 * t) * (2⁻¹ : ℝ≥0∞) ^ n := by
            gcongr; exact_mod_cast Nat.lt_two_pow_self.le
        _ = (2⁻¹ : ℝ≥0∞) ^ n := by
            rw [← mul_pow, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_pow, one_mul]
  · refine holderOnWith_iUnion_of_parent_and_star hV_mono
      (fun n w _ ↦ hUV le_rfl (hπ_memU n w)) (fun n w hw ↦ hπ_edist n (hVA (n + 1) hw))
      hstar_chain hγ (fun n z hz ↦ ?_) (fun n j ↦ ?_) hf_V0
    · obtain ⟨i, hi_lt, hi⟩ := List.mem_iff_getElem.mp
        (List.mem_append_left _ (List.mem_map.mpr ⟨z, Finset.mem_toList.mpr hz, rfl⟩) :
          (z, π n z) ∈ P_list n)
      have h := hf_edge n ⟨i, hi_lt⟩
      dsimp only [s, t_edge] at h
      rwa [congrArg Prod.fst hi, congrArg Prod.snd hi] at h
    · obtain ⟨i, hi_lt, hi⟩ := List.mem_iff_getElem.mp
        (List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, rfl⟩) :
          (u_star n j, v_star n j) ∈ P_list n)
      have h := hf_edge n ⟨i, hi_lt⟩
      dsimp only [s, t_edge] at h
      rwa [congrArg Prod.fst hi, congrArg Prod.snd hi] at h

/-- **Multiscale chaining system for sets with bounded covering exponent.**
If `A` has covering exponent `d` with finite constant `c` and `d < d'`, then `A` contains a
countable subset `D`, a finite base set `V₀ ⊆ D`, a `2⁻ⁿ`-approximation map `u : ℕ → T → T` into
`D`, and edge families `(s n, t n)` in `D` of count `≤ C · ((2⁻¹) ^ (-d')) ^ n` and length `≤ 2⁻ⁿ`
such that edge-level `γ`-Hölder bounds together with a finite bound on `V₀ × V₀` imply
`HolderOnWith` on `D`. -/
theorem HasCoveringExponent.exists_countable_dense_edges.{u, v}
    {T : Type v} [PseudoEMetricSpace T] {A : Set T} {c : ℝ≥0∞} {d d' : ℝ}
    (hA : HasCoveringExponent A c d) (hc : c ≠ ∞) (hdd' : d < d') :
    ∃ (V₀ : Finset T) (D : Set T) (u : ℕ → T → T) (C : ℝ≥0) (k : ℕ → ℕ)
      (s t : (n : ℕ) → Fin (k n) → T) (M_H : ℝ≥0 → ℝ≥0),
      D.Countable ∧ D ⊆ A ∧ (V₀ : Set T) ⊆ D ∧
      (∀ a ∈ A, ∀ n, u n a ∈ D ∧ edist a (u n a) ≤ (2⁻¹ : ℝ≥0∞) ^ n) ∧
      (∀ n i, s n i ∈ D ∧ t n i ∈ D) ∧
      (∀ n, (k n : ℝ≥0) ≤ C * ((2⁻¹ : ℝ≥0) ^ (-d')) ^ n) ∧
      (∀ n i, edist (s n i) (t n i) ≤ (2⁻¹ : ℝ≥0∞) ^ n) ∧
      (∀ {E : Type u} [PseudoEMetricSpace E] {γ : ℝ≥0}, 0 < γ →
        ∀ (f : T → E) (K K₀ : ℝ≥0),
          (∀ n i, edist (f (s n i)) (f (t n i)) ≤ (K : ℝ≥0∞) * ((2⁻¹ : ℝ≥0∞) ^ n) ^ (γ : ℝ)) →
          (∀ x ∈ V₀, ∀ y ∈ V₀, edist (f x) (f y) ≤ K₀) →
          HolderOnWith (M_H γ * (K + K₀)) γ f D) := by
  classical
  rcases A.eq_empty_or_nonempty with rfl | hAne
  · refine ⟨∅, ∅, fun _ x ↦ x, 0, fun _ ↦ 0, fun _ i ↦ Fin.elim0 i, fun _ i ↦ Fin.elim0 i,
      fun _ ↦ 0, countable_empty, Subset.rfl, by simp, by simp, fun _ i ↦ Fin.elim0 i,
      by simp, fun _ i ↦ Fin.elim0 i, fun _ _ _ _ _ _ ↦ by simp [HolderOnWith]⟩
  have hd : 0 ≤ d := hA.nonneg_of_nonempty hAne
  lift c to ℝ≥0 using hc
  let d₁ : ℝ := (d + d') / 2
  have hd₁_pos : 0 < d₁ := by dsimp [d₁]; linarith
  have hd₁d' : d₁ < d' := by dsimp [d₁]; linarith
  obtain ⟨t, ht_gt⟩ := exists_nat_gt (d₁ / (d' - d₁))
  have ht_pos_R : (0 : ℝ) < t := lt_trans (div_pos hd₁_pos (sub_pos.mpr hd₁d')) ht_gt
  have ht : t ≠ 0 := by exact_mod_cast ht_pos_R.ne'
  have ht_exp : d₁ * (1 + (t : ℝ)⁻¹) ≤ d' := by
    have h1 : d₁ * (t : ℝ)⁻¹ < d' - d₁ :=
      (div_eq_mul_inv d₁ (t : ℝ)) ▸ (div_lt_iff₀ ht_pos_R).mpr
        (by linarith [(div_lt_iff₀ (sub_pos.mpr hd₁d')).mp ht_gt])
    linarith
  obtain ⟨U, V, C₁, hC₁_pos, hV_mono, hVA, hUV, hUcov, hV_card⟩ :=
    exists_nested_covers_of_hasCoveringExponent hA hd (by dsimp [d₁]; linarith) hd₁_pos (5 * t)
  obtain ⟨a₀, ha₀⟩ := hAne
  let π : ℕ → T → T := fun n x ↦ if hx : x ∈ A then (hUcov n hx).choose else (hUcov n ha₀).choose
  have hπ_memU (n : ℕ) (x : T) : π n x ∈ U n := by
    dsimp only [π]; split_ifs with hx
    exacts [(hUcov n hx).choose_spec.1, (hUcov n ha₀).choose_spec.1]
  have hπ_edist (n : ℕ) {x : T} (hx : x ∈ A) : edist x (π n x) ≤ (2⁻¹ : ℝ≥0∞) ^ (n + 5 * t) := by
    have hspec : edist x (π n x) ≤ (((2⁻¹ : ℝ≥0) ^ (n + 5 * t) : ℝ≥0) : ℝ≥0∞) := by
      simp only [π, hx, ↓reduceDIte]; exact (hUcov n hx).choose_spec.2
    simpa only [ENNReal.coe_pow, ENNReal.coe_inv two_ne_zero, ENNReal.coe_ofNat] using hspec
  let q₁ : ℝ := (2 : ℝ) ^ d₁
  have hb_pow (n : ℕ) : ((V n).card : ℝ) ≤ ((C₁ * q₁ ^ n) ^ (t : ℝ)⁻¹) ^ t := by
    have hpos : 0 ≤ C₁ * q₁ ^ n := by positivity
    rw [← Real.rpow_natCast, ← Real.rpow_mul hpos, inv_mul_cancel₀ ht_pos_R.ne', Real.rpow_one]
    exact hV_card n
  choose m_star u_star v_star hstar_mem hstar_card hstar_edist hstar_chain using fun n ↦
    Finset.exists_star_edges_of_card_le_pow (V n) (5 * (2⁻¹ : ℝ≥0∞) ^ (n + 5 * t)) ht
      (by positivity) (hb_pow n)
  obtain ⟨hmemD, hedge_le, hhold⟩ := packed_chaining_edges_spec.{u, v} hV_mono hVA hUV hπ_memU
    hπ_edist hstar_mem hstar_edist hstar_chain
  refine ⟨V 0, ⋃ n, (V n : Set T), π, (C₁ * q₁ + C₁ ^ (1 + (t : ℝ)⁻¹)).toNNReal, _, _, _, _,
    countable_iUnion fun n ↦ (V n).countable_toSet, iUnion_subset hVA,
    subset_iUnion (fun m ↦ (V m : Set T)) 0, fun a ha n ↦ ?_, hmemD, fun n ↦ ?_, hedge_le, hhold⟩
  · exact ⟨subset_iUnion (fun m ↦ (V m : Set T)) n (hUV le_rfl (hπ_memU n a)),
      (hπ_edist n ha).trans (pow_le_pow_right_of_le_one' (by norm_num) (Nat.le_add_right n _))⟩
  · simpa using card_parent_add_star_le hC₁_pos hd₁d' ht_exp (hV_card (n + 1))
      (hV_card n) (hstar_card n)

end Metric
