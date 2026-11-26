/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.LinearAlgebra.Dimension.Submodule

/-!
# Spreading families of linear maps

A family `(B s)_{s ∈ Θ}` of linear maps `V → W` *spreads with error `η`* if for every subspace
`F ⊆ W`, of share `α = dim F / dim W` (with `α = 0` when `W = 0`), the preimage of `F` under some
`B s` has dimension at most `((1 + α) / 2 + η) dim V`. A spreading family is a supply of maps whose
images keep adding new directions: a greedy choice of logarithmically many of them spans almost
all of `W`. This is the linear algebra behind the "few translates" step of second-moment
arguments, where the family consists of the translates of one map by a finite group.

Throughout, `dim` is `Module.finrank`, which is `0` on an infinite-dimensional space; the notions
and bounds are meant for finite-dimensional `V` and `W`.

## Main definitions and results

* `TauCeti.IsSpread B η`: the family `B` spreads with error `η`.
* `TauCeti.IsSpread.exists_card_mul_finrank_le_and_le_finrank_biSup_range`: if `V` is
  finite-dimensional and nonzero (`0 < dim V`) and `B` spreads with error `3ε/2`, where
  `0 < ε < 1/16`, then the images of a set `t` of maps with
  `#t dim V ≤ (5/2) (1 + log (1 / (16 ε))) dim W` together span at least `(1 - 16 ε) dim W`
  dimensions.

## References

The greedy covering with a logarithmic loss is that of L. A. Wolsey, *An analysis of the greedy
algorithm for the submodular set covering problem*, Combinatorica 2 (1982), 385–393, here for the
dimension of a sum of images.

These results are adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0,
Copyright 2026 Anthropic PBC), file `src/New/Spanning/SecondMoment/FewTranslates.lean`
(`New.IsSpread`, `New.IsSpread.exists_codim_le`, `New.IsSpread.exists_codim_le_max`,
`New.IsSpread.exists_few_le_finrank_iSup_range`), where they are stated for complex vector
spaces; here they hold over any division ring.
-/

public section

open Module Finset Submodule LinearMap

namespace TauCeti


variable {K V W Θ : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- A family `(B s)_{s ∈ Θ}` of linear maps *spreads with error `η`* if for every subspace `F` of
the target, of share `α = dim F / dim W` (with `α = 0` when `dim W = 0`), the preimage of `F`
under some `B s` has dimension at most `((1 + α) / 2 + η) dim V`. Here `dim` is
`Module.finrank`, which is `0` on an infinite-dimensional space, so the notion is meant for
finite-dimensional `V` and `W`. -/
def IsSpread (B : Θ → V →ₗ[K] W) (η : ℝ) : Prop :=
  ∀ F : Submodule K W, ∃ s : Θ,
    (finrank K (F.comap (B s)) : ℝ) ≤ ((1 + finrank K F / finrank K W) / 2 + η) * finrank K V

theorem isSpread_iff {B : Θ → V →ₗ[K] W} {η : ℝ} :
    IsSpread B η ↔ ∀ F : Submodule K W, ∃ s : Θ,
      (finrank K (F.comap (B s)) : ℝ) ≤ ((1 + finrank K F / finrank K W) / 2 + η) * finrank K V :=
  Iff.rfl

/-- A family that spreads with some error spreads with any larger error. -/
theorem IsSpread.mono {B : Θ → V →ₗ[K] W} {η η' : ℝ} (hB : IsSpread B η) (h : η ≤ η') :
    IsSpread B η' := fun F ↦ (hB F).imp fun _ hs ↦ hs.trans (by gcongr)

variable {B : Θ → V →ₗ[K] W} {ε : ℝ}

/-- One step of the greedy choice. If the maps `B s` spread with error `3ε/2` and `F` misses more
than a share `16 ε` of the dimensions of `W`, then adding some image `range (B s)` to `F`
multiplies the codimension by at most `1 - 2 dim V / (5 dim W)`. -/
theorem IsSpread.exists_codim_sup_range_le [FiniteDimensional K V] [FiniteDimensional K W]
    (h_spread : IsSpread B (3 / 2 * ε)) (F : Submodule K W) (hW : 0 < finrank K W)
    (hF : 16 * ε * finrank K W < (finrank K W - finrank K F : ℝ)) :
    ∃ s : Θ, (finrank K W - finrank K ↥(F ⊔ range (B s)) : ℝ) ≤
      (1 - 2 * finrank K V / (5 * finrank K W)) * (finrank K W - finrank K F) := by
  obtain ⟨s, hs⟩ := h_spread F
  refine ⟨s, ?_⟩
  have hW' : (0 : ℝ) < finrank K W := by exact_mod_cast hW
  set α : ℝ := finrank K F / finrank K W
  have hα : (finrank K F : ℝ) = α * finrank K W := (div_mul_cancel₀ _ hW'.ne').symm
  have hα_le : α ≤ 1 := (div_le_one hW').2 (by exact_mod_cast F.finrank_le)
  have h_share : 16 * ε < 1 - α := lt_of_mul_lt_mul_right (by linarith) hW'.le
  have h_added : (finrank K ↥(F ⊔ range (B s)) : ℝ) + finrank K (F.comap (B s)) =
      finrank K F + finrank K V := by exact_mod_cast (B s).finrank_sup_range_add_finrank_comap F
  -- The image adds at least `(1/2 - 3/32) (1 - α) dim V ≥ (2/5) (1 - α) dim V` dimensions.
  have h_gain : ((1 + α) / 2 + 3 / 2 * ε) * finrank K V ≤ (1 - 2 / 5 * (1 - α)) * finrank K V := by
    gcongr
    linarith
  have h_factor : (1 - 2 * finrank K V / (5 * finrank K W)) * (finrank K W - finrank K F : ℝ) =
      finrank K W - finrank K F - 2 / 5 * (1 - α) * finrank K V := by
    rw [hα]
    field_simp
  rw [h_factor]
  linarith

/-- The greedy choice after `l` steps. If the maps `B s : V → W` spread with error `3ε/2`, then the
span of the images of at most `l` of them misses at most a share
`max (16 ε) (exp (-l · rate))` of the dimensions of `W`, where `rate = 2 dim V / (5 dim W)`. -/
theorem IsSpread.exists_card_le_and_codim_le_max [FiniteDimensional K V] [FiniteDimensional K W]
    (h_spread : IsSpread B (3 / 2 * ε)) (hW : 0 < finrank K W) (l : ℕ) :
    ∃ t : Finset Θ, #t ≤ l ∧ (finrank K W - finrank K ↥(⨆ s ∈ t, range (B s)) : ℝ) ≤
      max (16 * ε) (Real.exp (-(l * (2 * finrank K V / (5 * finrank K W))))) * finrank K W := by
  classical
  have hW' : (0 : ℝ) < finrank K W := by exact_mod_cast hW
  set rate : ℝ := 2 * finrank K V / (5 * finrank K W)
  let codim (t : Finset Θ) : ℝ := finrank K W - finrank K ↥(⨆ s ∈ t, range (B s))
  -- Restate the goal through `codim` (the `let` unfolds definitionally), so that the induction
  -- hypothesis and each step speak about the one quantity `codim t`.
  change ∃ t : Finset Θ, #t ≤ l ∧ codim t ≤ max (16 * ε) (Real.exp (-(l * rate))) * finrank K W
  induction l with
  | zero =>
    refine ⟨∅, le_rfl, ?_⟩
    calc codim ∅ ≤ finrank K W := sub_le_self _ (Nat.cast_nonneg _)
      _ ≤ max (16 * ε) (Real.exp (-((0 : ℕ) * rate))) * finrank K W :=
          le_mul_of_one_le_left hW'.le (le_max_of_le_right (by simp))
  | succ l ih =>
    obtain ⟨t, h_card, h_codim⟩ := ih
    obtain h_done | h_more := le_or_gt (codim t) (16 * ε * finrank K W)
    · exact ⟨t, h_card.trans l.le_succ,
        h_done.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hW'.le)⟩
    obtain ⟨s, h_step⟩ := h_spread.exists_codim_sup_range_le _ hW h_more
    have h_exp : codim t ≤ Real.exp (-(l * rate)) * finrank K W := by
      rw [max_mul_of_nonneg _ _ hW'.le, le_max_iff] at h_codim
      exact h_codim.resolve_left h_more.not_ge
    refine ⟨insert s t, (card_insert_le s t).trans (by omega), ?_⟩
    have h_insert : ⨆ i ∈ insert s t, range (B i) = (⨆ i ∈ t, range (B i)) ⊔ range (B s) := by
      rw [Finset.iSup_insert, sup_comm]
    calc codim (insert s t)
        ≤ (1 - rate) * codim t := by rwa [← h_insert] at h_step
      _ ≤ Real.exp (-rate) * (Real.exp (-(l * rate)) * finrank K W) := by
          gcongr
          · exact sub_nonneg.2 (by exact_mod_cast Submodule.finrank_le _)
          · exact Real.one_sub_le_exp_neg rate
      _ = Real.exp (-((l + 1 : ℕ) * rate)) * finrank K W := by
          rw [← mul_assoc, ← Real.exp_add]
          push_cast
          ring_nf
      _ ≤ max (16 * ε) (Real.exp (-((l + 1 : ℕ) * rate))) * finrank K W :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hW'.le

/-- The first greedy step shows that a spreading family into a nonzero space has
`2 dim V ≤ 5 dim W`. -/
private theorem IsSpread.two_mul_finrank_le [FiniteDimensional K V] [FiniteDimensional K W]
    (h_spread : IsSpread B (3 / 2 * ε)) (hW : 0 < finrank K W) (hε_lt : ε < 1 / 16) :
    2 * finrank K V / (5 * finrank K W) ≤ (1 : ℝ) := by
  have hW' : (0 : ℝ) < finrank K W := by exact_mod_cast hW
  have h_start : 16 * ε * finrank K W < finrank K W - finrank K (⊥ : Submodule K W) := by
    simpa using mul_lt_of_lt_one_left hW' (by linarith : 16 * ε < 1)
  obtain ⟨s, h_step⟩ := h_spread.exists_codim_sup_range_le ⊥ hW h_start
  have h_codim_nonneg : (0 : ℝ) ≤ finrank K W - finrank K ↥(⊥ ⊔ range (B s)) :=
    sub_nonneg.2 (by exact_mod_cast Submodule.finrank_le _)
  have h_nonneg : (0 : ℝ) ≤ (1 - 2 * finrank K V / (5 * finrank K W)) * finrank K W := by
    simpa using h_codim_nonneg.trans h_step
  exact sub_nonneg.1 (nonneg_of_mul_nonneg_left h_nonneg hW')

/-- **Few maps span almost everything** (the case of a nonzero target). -/
private theorem IsSpread.exists_card_mul_finrank_le_and_le_finrank_biSup_range_of_pos
    [FiniteDimensional K V] [FiniteDimensional K W] (h_spread : IsSpread B (3 / 2 * ε))
    (hV : 0 < finrank K V) (hW : 0 < finrank K W) (hε : 0 < ε) (hε_lt : ε < 1 / 16) :
    ∃ t : Finset Θ,
      #t * finrank K V ≤ 5 / 2 * (1 + Real.log (16 * ε)⁻¹) * finrank K W ∧
      (1 - 16 * ε) * finrank K W ≤ finrank K ↥(⨆ s ∈ t, range (B s)) := by
  -- While more than a share `16 ε` is missing, each step multiplies the missing share by at most
  -- `1 - rate ≤ exp (-rate)`; stop at the least `l` with `l rate ≥ log (1 / (16 ε))`.
  set rate : ℝ := 2 * finrank K V / (5 * finrank K W) with h_rate
  have h_rate_pos : 0 < rate := by positivity
  have h_rate_le : rate ≤ 1 := h_spread.two_mul_finrank_le hW hε_lt
  have h_log : 0 ≤ Real.log (16 * ε)⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ (by positivity)).2 (by linarith))
  set l : ℕ := ⌈Real.log (16 * ε)⁻¹ / rate⌉₊
  have hl_ge : Real.log (16 * ε)⁻¹ ≤ l * rate := (div_le_iff₀ h_rate_pos).1 (Nat.le_ceil _)
  have hl_le : l * rate ≤ 1 + Real.log (16 * ε)⁻¹ :=
    calc l * rate ≤ (Real.log (16 * ε)⁻¹ / rate + 1) * rate := by
          gcongr
          exact (Nat.ceil_lt_add_one (by positivity)).le
      _ = rate + Real.log (16 * ε)⁻¹ := by field_simp; ring
      _ ≤ 1 + Real.log (16 * ε)⁻¹ := by gcongr
  obtain ⟨t, h_card, h_codim⟩ := h_spread.exists_card_le_and_codim_le_max hW l
  have h_exp : Real.exp (-(l * rate)) ≤ 16 * ε := by
    rwa [← Real.le_log_iff_exp_le (by positivity), _root_.neg_le, ← Real.log_inv]
  rw [max_eq_left h_exp] at h_codim
  refine ⟨t, ?_, by linarith⟩
  calc (#t * finrank K V : ℝ) ≤ l * finrank K V := by gcongr
    _ = 5 / 2 * (l * rate) * finrank K W := by rw [h_rate]; field_simp
    _ ≤ 5 / 2 * (1 + Real.log (16 * ε)⁻¹) * finrank K W := by gcongr

/-- **Few maps of a spreading family span almost everything.** Let `V` be finite-dimensional and
nonzero (`0 < finrank K V`), let `0 < ε < 1/16`, and let the maps `B s : V → W` spread with error
`3ε/2`. Then there is a finite set `t` of indices with
`#t dim V ≤ (5/2) (1 + log (1 / (16 ε))) dim W` whose images together span at least
`(1 - 16 ε) dim W` dimensions. Here `dim W` is `finrank K W`, which is `0` for an
infinite-dimensional `W`, so the bound says something only for finite-dimensional `W`. -/
theorem IsSpread.exists_card_mul_finrank_le_and_le_finrank_biSup_range
    (h_spread : IsSpread B (3 / 2 * ε)) (hV : 0 < finrank K V) (hε : 0 < ε)
    (hε_lt : ε < 1 / 16) :
    ∃ t : Finset Θ,
      #t * finrank K V ≤ 5 / 2 * (1 + Real.log (16 * ε)⁻¹) * finrank K W ∧
      (1 - 16 * ε) * finrank K W ≤ finrank K ↥(⨆ s ∈ t, range (B s)) := by
  obtain hW | hW := (Nat.zero_le (finrank K W)).eq_or_lt
  · -- For `dim W = 0` the empty set does.
    refine ⟨∅, ?_, ?_⟩ <;> simp [← hW]
  have := Module.finite_of_finrank_pos hV
  have := Module.finite_of_finrank_pos hW
  exact h_spread.exists_card_mul_finrank_le_and_le_finrank_biSup_range_of_pos hV hW hε hε_lt

end TauCeti
