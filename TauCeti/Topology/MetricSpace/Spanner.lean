/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
-- Private: floor estimates are used only in the real-exponent corollary proof.
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Sparse multiplicative spanners on finite sets

Given a finite vertex set `s : Finset α`, a symmetric relation `R : α → α → Prop`, and a branching
bound `s.card < m ^ k`, Awerbuch's ball-carving algorithm extracts a subset `E ⊆ s ×ˢ s` of pairs
satisfying `R`, of size `E.card ≤ m * s.card`, with stretch at most `2 * k - 1`: for every
symmetric subadditive weight `w : α → α → ℝ≥0∞` vanishing on the diagonal, if `w e.1 e.2 ≤ D` for
all `e ∈ E`, then `w x y ≤ (2 * k - 1) * D` for all `x, y ∈ s` with `R x y`.

Choosing `m = ⌊(max 1 B) ^ (1 / k)⌋₊ + 1` when `(s.card : ℝ≥0) ≤ B` and `k ≠ 0` bounds the number
of selected edges by `2 * (max 1 B) ^ (1 + 1 / k)`, replacing the quadratic `B ^ 2` count of all
`R`-pairs by an exponent arbitrarily close to `1` at the cost of the constant stretch factor
`2 * k - 1`.

## Main results

* `Finset.exists_spanner`: discrete ball-carving `(2 * k - 1)`-spanner with at most `m * s.card`
  edges whenever `s.card < m ^ k`.
* `Finset.exists_spanner_rpow`: quantitative version with edge count bounded by
  `2 * (max 1 B) ^ (1 + (k : ℝ)⁻¹)` whenever `(s.card : ℝ≥0) ≤ B` and `k ≠ 0`.

## References

* Baruch Awerbuch, *Complexity of network synchronization*, J. ACM 32 (1985), 804–823.
* David Peleg and Alejandro A. Schäffer, *Graph spanners*, J. Graph Theory 13 (1989), 99–116.
* Volker Krätschmer and Mikhail Urusov, *A general Kolmogorov–Chentsov type theorem on general
  metric spaces*, Bernoulli 29 (2023), 2960–2986, arXiv:2107.13837v2.
-/

public section

open scoped ENNReal NNReal

namespace Finset

/-- **Ball-carving `(2 * k - 1)`-spanner.** For any finite set `s : Finset α`, symmetric relation
`R` on `α`, and `k m : ℕ` with `s.card < m ^ k`, there is a set `E : Finset (α × α)` of at most
`m * s.card` pairs `(u, v) ∈ s ×ˢ s` satisfying `R u v` such that every `R`-related pair in `s`
has distance at most `(2 * k - 1) * D` under any symmetric triangle weight bounded by `D` on `E`. -/
theorem exists_spanner {α : Type*} (s : Finset α) {R : α → α → Prop}
    (hR : ∀ ⦃x y⦄, R x y → R y x) {k m : ℕ} (hcard : s.card < m ^ k) :
    ∃ E : Finset (α × α),
      (∀ e ∈ E, e.1 ∈ s ∧ e.2 ∈ s ∧ R e.1 e.2) ∧
      E.card ≤ m * s.card ∧
      ∀ (w : α → α → ℝ≥0∞),
        (∀ a, w a a = 0) →
        (∀ a b, w a b = w b a) →
        (∀ a b c, w a c ≤ w a b + w b c) →
        ∀ {D : ℝ≥0∞}, (∀ e ∈ E, w e.1 e.2 ≤ D) →
        ∀ x ∈ s, ∀ y ∈ s, R x y → w x y ≤ (2 * k - 1 : ℕ) * D := by
  -- Strong induction on the cardinality of `s`.
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    classical
    subst hn
    rcases s.eq_empty_or_nonempty with rfl | ⟨v, hv⟩
    · exact ⟨∅, by simp, by simp, fun _ _ _ _ _ _ _ hx ↦ (notMem_empty _ hx).elim⟩
    -- Grow combinatorial balls `B 0 = {v}`, `B (i + 1) = B i ∪ {y ∈ s | ∃ x ∈ B i, R x y}`.
    let B : ℕ → Finset α := fun i ↦
      Nat.rec {v} (fun _ Bi ↦ Bi ∪ s.filter fun y ↦ ∃ x ∈ Bi, R x y) i
    have hB_zero : B 0 = {v} := rfl
    have hB_succ (i : ℕ) : B (i + 1) = B i ∪ s.filter fun y ↦ ∃ x ∈ B i, R x y := rfl
    have hB_sub : ∀ i, B i ⊆ s := by
      intro i
      induction i with
      | zero => exact singleton_subset_iff.mpr hv
      | succ i hi => exact union_subset hi (filter_subset _ s)
    have hB_step (i : ℕ) : B i ⊆ B (i + 1) := by
      rw [hB_succ]
      exact subset_union_left
    have hB_mono {i₁ i₂ : ℕ} (hle : i₁ ≤ i₂) : B i₁ ⊆ B i₂ :=
      Nat.le_induction Subset.rfl (fun _ _ hsub ↦ hsub.trans (hB_step _)) i₂ hle
    have hvB (i : ℕ) : v ∈ B i := hB_mono (Nat.zero_le i) (mem_singleton_self v)
    -- Since `s.card < m ^ k`, some step `j < k` expands by a factor at most `m`.
    obtain ⟨j, hjk, hj_card⟩ : ∃ j < k, (B (j + 1)).card ≤ m * (B j).card := by
      by_contra! hgt
      have hpow : ∀ i ≤ k, m ^ i ≤ (B i).card := by
        intro i hi
        induction i with
        | zero => simp [hB_zero]
        | succ i hi_ih =>
          calc m ^ (i + 1)
            _ = m * m ^ i := pow_succ' m i
            _ ≤ m * (B i).card := Nat.mul_le_mul_left m (hi_ih (Nat.le_of_succ_le hi))
            _ ≤ (B (i + 1)).card := (hgt i (Nat.lt_of_succ_le hi)).le
      exact hcard.not_ge ((hpow k le_rfl).trans (card_le_card (hB_sub k)))
    -- Assign each `y ∈ B (j + 1) \ {v}` a parent in the first layer before `y` appears.
    have hex_layer {y : α} (hy : y ∈ (B (j + 1)).erase v) : ∃ i, y ∈ B (i + 1) :=
      ⟨j, mem_of_mem_erase hy⟩
    let layer (y : α) : ℕ := if hy : y ∈ (B (j + 1)).erase v then Nat.find (hex_layer hy) else 0
    have hlayer_eq {y : α} (hy : y ∈ (B (j + 1)).erase v) : layer y = Nat.find (hex_layer hy) := by
      simp only [layer, hy, ↓reduceDIte]
    have hparent {y : α} (hy : y ∈ (B (j + 1)).erase v) : ∃ x ∈ B (layer y), R x y := by
      have hmem : y ∈ B (layer y + 1) := by
        rw [hlayer_eq hy]
        exact Nat.find_spec (hex_layer hy)
      have hnotMem : y ∉ B (layer y) := by
        rcases eq_or_ne (layer y) 0 with h0 | hpos
        · rw [h0, hB_zero, mem_singleton]
          exact ne_of_mem_erase hy
        · obtain ⟨i', hi'⟩ := Nat.exists_eq_succ_of_ne_zero hpos
          have hlt : i' < Nat.find (hex_layer hy) := by
            have := hlayer_eq hy
            omega
          simpa only [hi'] using Nat.find_min (hex_layer hy) hlt
      rw [hB_succ, mem_union, mem_filter] at hmem
      exact (hmem.resolve_left hnotMem).2
    let parent (y : α) : α :=
      if hy : y ∈ (B (j + 1)).erase v then (hparent hy).choose else y
    have hparent_spec {y : α} (hy : y ∈ (B (j + 1)).erase v) :
        parent y ∈ B (layer y) ∧ R (parent y) y := by
      have hp_eq : parent y = (hparent hy).choose := by simp only [parent, hy, ↓reduceDIte]
      rw [hp_eq]
      exact (hparent hy).choose_spec
    let Estep : Finset (α × α) := ((B (j + 1)).erase v).image fun y ↦ (parent y, y)
    have hEstep_mem : ∀ e ∈ Estep, e.1 ∈ s ∧ e.2 ∈ s ∧ R e.1 e.2 := by
      intro e he
      obtain ⟨y, hy, rfl⟩ := mem_image.mp he
      obtain ⟨hpy1, hpy2⟩ := hparent_spec hy
      exact ⟨hB_sub (layer y) hpy1, hB_sub (j + 1) (mem_of_mem_erase hy), hpy2⟩
    have hEstep_card : Estep.card ≤ m * (B j).card :=
      card_image_le.trans (card_erase_le.trans hj_card)
    -- Carve out `B j` and recurse on `s \ B j`.
    have hsdiff_lt : (s \ B j).card < s.card := by
      refine card_lt_card ⟨sdiff_subset, fun hsub ↦ ?_⟩
      exact (mem_sdiff.mp (hsub hv)).2 (hvB j)
    obtain ⟨Erec, hErec_mem, hErec_card, hErec_stretch⟩ :=
      ih (s \ B j).card hsdiff_lt (s \ B j) (hsdiff_lt.trans hcard) rfl
    refine ⟨Estep ∪ Erec, ?_, ?_, ?_⟩
    · intro e he
      rcases mem_union.mp he with he1 | he2
      · exact hEstep_mem e he1
      · obtain ⟨h1, h2, h3⟩ := hErec_mem e he2
        exact ⟨sdiff_subset h1, sdiff_subset h2, h3⟩
    · calc (Estep ∪ Erec).card
        _ ≤ Estep.card + Erec.card := card_union_le _ _
        _ ≤ m * (B j).card + m * (s \ B j).card := add_le_add hEstep_card hErec_card
        _ = m * ((s \ B j).card + (B j).card) := by ring
        _ = m * s.card := by rw [card_sdiff_add_card_eq_card (hB_sub j)]
    · intro w hw_refl hw_symm hw_tri D hD x hx y hy hxy
      -- Every vertex in `B n` (`n ≤ j + 1`) is within `n * D` of the center `v`.
      have hrad : ∀ n ≤ j + 1, ∀ z ∈ B n, w z v ≤ (n : ℝ≥0∞) * D := by
        intro n hn
        induction n with
        | zero =>
          intro z hz
          rw [hB_zero, mem_singleton] at hz
          simp [hz, hw_refl]
        | succ n hn_ih =>
          intro z hz
          rcases eq_or_ne z v with rfl | hzv
          · simp [hw_refl]
          · have hz_erase : z ∈ (B (j + 1)).erase v :=
              mem_erase.mpr ⟨hzv, hB_mono hn hz⟩
            have hlay_le : layer z ≤ n := by
              rw [hlayer_eq hz_erase]
              exact Nat.find_le (h := hex_layer hz_erase) hz
            have hpy_mem : parent z ∈ B n := hB_mono hlay_le (hparent_spec hz_erase).1
            have hedge : (parent z, z) ∈ Estep ∪ Erec :=
              mem_union_left _ (mem_image_of_mem _ hz_erase)
            calc w z v
              _ ≤ w z (parent z) + w (parent z) v := hw_tri z (parent z) v
              _ = w (parent z) z + w (parent z) v := by rw [hw_symm z (parent z)]
              _ ≤ D + (n : ℝ≥0∞) * D :=
                add_le_add (hD _ hedge) (hn_ih (Nat.le_of_succ_le hn) _ hpy_mem)
              _ = ((n + 1 : ℕ) : ℝ≥0∞) * D := by push_cast; ring
      -- Pairs with an endpoint in `B j` route through `v`; remaining pairs use `Erec`.
      by_cases hboth : x ∈ s \ B j ∧ y ∈ s \ B j
      · exact hErec_stretch w hw_refl hw_symm hw_tri
          (fun e he ↦ hD e (mem_union_right _ he)) x hboth.1 y hboth.2 hxy
      · have hor : x ∈ B j ∨ y ∈ B j := by
          rcases em (x ∈ B j) with hxj | hxj
          · exact Or.inl hxj
          · refine Or.inr (by_contra fun hyj ↦ ?_)
            exact hboth ⟨mem_sdiff.mpr ⟨hx, hxj⟩, mem_sdiff.mpr ⟨hy, hyj⟩⟩
        have hclose : ∀ u ∈ B j, ∀ z ∈ s, R u z → w u z ≤ (2 * k - 1 : ℕ) * D := by
          intro u hu z hz huz
          have hz_next : z ∈ B (j + 1) := by
            rw [hB_succ]
            exact mem_union_right _ (mem_filter.mpr ⟨hz, u, hu, huz⟩)
          have h2j : 2 * j + 1 ≤ 2 * k - 1 := by omega
          calc w u z
            _ ≤ w u v + w v z := hw_tri u v z
            _ = w u v + w z v := by rw [hw_symm v z]
            _ ≤ (j : ℝ≥0∞) * D + ((j + 1 : ℕ) : ℝ≥0∞) * D :=
              add_le_add (hrad j (Nat.le_succ j) u hu) (hrad (j + 1) le_rfl z hz_next)
            _ = ((2 * j + 1 : ℕ) : ℝ≥0∞) * D := by push_cast; ring
            _ ≤ ((2 * k - 1 : ℕ) : ℝ≥0∞) * D := by gcongr
        rcases hor with hxj | hyj
        · exact hclose x hxj y hy hxy
        · rw [hw_symm x y]
          exact hclose y hyj x hx (hR hxy)

/-- **Quantitative `(2 * k - 1)`-spanner bound.** If `(s.card : ℝ≥0) ≤ B` and `k ≠ 0`, there is a
`(2 * k - 1)`-spanner `E` of `(s, R)` with `(E.card : ℝ≥0) ≤ 2 * (max 1 B) ^ (1 + (k : ℝ)⁻¹)`. -/
theorem exists_spanner_rpow {α : Type*} (s : Finset α) {R : α → α → Prop}
    (hR : ∀ ⦃x y⦄, R x y → R y x) {B : ℝ≥0} (hB : (s.card : ℝ≥0) ≤ B) {k : ℕ} (hk : k ≠ 0) :
    ∃ E : Finset (α × α),
      (∀ e ∈ E, e.1 ∈ s ∧ e.2 ∈ s ∧ R e.1 e.2) ∧
      (E.card : ℝ≥0) ≤ 2 * (max 1 B) ^ (1 + (k : ℝ)⁻¹) ∧
      ∀ (w : α → α → ℝ≥0∞),
        (∀ a, w a a = 0) →
        (∀ a b, w a b = w b a) →
        (∀ a b c, w a c ≤ w a b + w b c) →
        ∀ {D : ℝ≥0∞}, (∀ e ∈ E, w e.1 e.2 ≤ D) →
        ∀ x ∈ s, ∀ y ∈ s, R x y → w x y ≤ (2 * k - 1 : ℕ) * D := by
  let B₁ : ℝ≥0 := max 1 B
  have hB₁_one : (1 : ℝ≥0) ≤ B₁ := le_max_left 1 B
  have hB₁_pos : (0 : ℝ≥0) < B₁ := zero_lt_one.trans_le hB₁_one
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hsB₁ : (s.card : ℝ≥0) ≤ B₁ := hB.trans (le_max_right 1 B)
  let m : ℕ := ⌊B₁ ^ (k : ℝ)⁻¹⌋₊ + 1
  have hcard_lt : s.card < m ^ k := by
    have hlt_m : B₁ ^ (k : ℝ)⁻¹ < (m : ℝ≥0) := by
      simpa [m] using Nat.lt_floor_add_one (B₁ ^ (k : ℝ)⁻¹)
    have hlt_pow : B₁ < ((m ^ k : ℕ) : ℝ≥0) := by
      calc B₁
        _ = (B₁ ^ (k : ℝ)⁻¹) ^ (k : ℝ) := by
          rw [← NNReal.rpow_mul, inv_mul_cancel₀ hk_pos.ne', NNReal.rpow_one]
        _ < (m : ℝ≥0) ^ (k : ℝ) := NNReal.rpow_lt_rpow hlt_m hk_pos
        _ = ((m ^ k : ℕ) : ℝ≥0) := by rw [NNReal.rpow_natCast]; norm_cast
    exact_mod_cast hsB₁.trans_lt hlt_pow
  obtain ⟨E, hE_mem, hE_card, hE_stretch⟩ := s.exists_spanner hR hcard_lt
  refine ⟨E, hE_mem, ?_, hE_stretch⟩
  have hm_le : (m : ℝ≥0) ≤ 2 * B₁ ^ (k : ℝ)⁻¹ := by
    have hfloor : (⌊B₁ ^ (k : ℝ)⁻¹⌋₊ : ℝ≥0) ≤ B₁ ^ (k : ℝ)⁻¹ := Nat.floor_le zero_le
    have hone : (1 : ℝ≥0) ≤ B₁ ^ (k : ℝ)⁻¹ := NNReal.one_le_rpow hB₁_one (inv_nonneg.mpr hk_pos.le)
    calc (m : ℝ≥0)
      _ = (⌊B₁ ^ (k : ℝ)⁻¹⌋₊ : ℝ≥0) + 1 := by simp [m]
      _ ≤ B₁ ^ (k : ℝ)⁻¹ + B₁ ^ (k : ℝ)⁻¹ := add_le_add hfloor hone
      _ = 2 * B₁ ^ (k : ℝ)⁻¹ := (two_mul _).symm
  calc (E.card : ℝ≥0)
    _ ≤ ((m * s.card : ℕ) : ℝ≥0) := by exact_mod_cast hE_card
    _ = (m : ℝ≥0) * (s.card : ℝ≥0) := by push_cast; rfl
    _ ≤ (2 * B₁ ^ (k : ℝ)⁻¹) * B₁ := mul_le_mul' hm_le hsB₁
    _ = 2 * (B₁ ^ (1 : ℝ) * B₁ ^ (k : ℝ)⁻¹) := by rw [NNReal.rpow_one]; ring
    _ = 2 * B₁ ^ (1 + (k : ℝ)⁻¹) := by rw [← NNReal.rpow_add hB₁_pos.ne']

end Finset
