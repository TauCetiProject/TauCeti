/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.L1Space.HasFiniteIntegral
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Disjoint subsets of sets of small measure

If `μ (s n) → 0`, a subsequence of the measurable sets `s n` can be shrunk to pairwise disjoint
measurable sets while losing at most `η` from the lower integrals of given functions of finite
lower integral: remove from each chosen set all later chosen sets, choosing the subsequence so that
the later sets carry lower integral at most `η * 2⁻¹ ^ l` for all earlier functions. Such disjoint
sets feed the gliding hump arguments behind the Dunford–Pettis weak compactness criterion in `L¹`.

## Main statements

* `MeasureTheory.exists_strictMono_pairwise_disjoint_lintegral_le`: shrinking a subsequence of
  sets of measure tending to zero to pairwise disjoint sets.
* `MeasureTheory.half_lt_lintegral_enorm_sub`: if `g` has mass more than `ε` on `S` and `f` at
  most `ε / 2`, then `g - f` has mass more than `ε / 2` on `S`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §5.2, for the role of this
  statement in the Dunford–Pettis theorem.
-/

public section

open Filter Function Set Topology
open scoped ENNReal

namespace MeasureTheory

variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α}

/-- If `μ (s n) → 0`, a subsequence of the measurable sets `s n` can be shrunk to pairwise
disjoint measurable sets `B j ⊆ s (σ j)` such that the lower integral of `f (σ j)` over `B j`
falls short of its lower integral over `s (σ j)` by at most `η`, for given functions `f n` of
finite lower integral. -/
theorem exists_strictMono_pairwise_disjoint_lintegral_le {f : ℕ → α → ℝ≥0∞}
    (hf : ∀ n, ∫⁻ x, f n x ∂μ ≠ ∞) {s : ℕ → Set α} (hsm : ∀ n, MeasurableSet (s n))
    (hs : Tendsto (fun n ↦ μ (s n)) atTop (𝓝 0)) {η : ℝ≥0∞} (hη : η ≠ 0) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ B : ℕ → Set α, (∀ j, MeasurableSet (B j)) ∧
      Pairwise (Disjoint on B) ∧ (∀ j, B j ⊆ s (σ j)) ∧
      ∀ j, ∫⁻ x in s (σ j), f (σ j) x ∂μ ≤ ∫⁻ x in B j, f (σ j) x ∂μ + η := by
  set δ : ℕ → ℝ≥0∞ := fun l ↦ η * 2⁻¹ ^ l
  have hδ (l : ℕ) : 0 < δ l := by
    simp only [δ]
    exact ENNReal.mul_pos hη (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top))
  -- The next index: a set on which all earlier functions have lower integral at most `δ l`.
  have key (N l K : ℕ) : ∃ n, K ≤ n ∧ ∀ m ≤ N, ∫⁻ x in s n, f m x ∂μ ≤ δ l := by
    have hev : ∀ᶠ n in atTop, ∀ m ∈ Finset.range (N + 1), ∫⁻ x in s n, f m x ∂μ ≤ δ l := by
      rw [eventually_all_finset]
      exact fun m _ ↦ ENNReal.tendsto_nhds_zero.1 (tendsto_setLIntegral_zero (hf m) hs) _ (hδ l)
    obtain ⟨n, hn, hK⟩ := (hev.and (eventually_ge_atTop K)).exists
    exact ⟨n, hK, fun m hm ↦ hn m (Finset.mem_range.2 (Nat.lt_succ_of_le hm))⟩
  choose g hg_ge hg_small using key
  let σ : ℕ → ℕ := fun l ↦ Nat.rec 0 (fun l k ↦ g k (l + 1) (k + 1)) l
  have hσ_succ (l : ℕ) : σ (l + 1) = g (σ l) (l + 1) (σ l + 1) := rfl
  have hσ : StrictMono σ := strictMono_nat_of_lt_succ fun l ↦ by
    rw [hσ_succ, Nat.lt_iff_add_one_le]
    exact hg_ge _ _ _
  have hsmall (j l : ℕ) (hjl : j < l) : ∫⁻ x in s (σ l), f (σ j) x ∂μ ≤ δ l := by
    obtain ⟨l, rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
    rw [hσ_succ]
    exact hg_small _ _ _ _ (hσ.monotone (by omega))
  -- Remove from each chosen set all later chosen sets.
  set U : ℕ → Set α := fun j ↦ ⋃ i, s (σ (j + 1 + i))
  have hUm (j : ℕ) : MeasurableSet (U j) := .iUnion fun i ↦ hsm _
  refine ⟨σ, hσ, fun j ↦ s (σ j) \ U j, fun j ↦ (hsm _).diff (hUm j), ?_, fun j ↦ sdiff_subset, ?_⟩
  · refine (pairwise_disjoint_on _).2 fun a b hab ↦ disjoint_left.2 fun x hxa hxb ↦ hxa.2 ?_
    exact mem_iUnion.2 ⟨b - (a + 1), by rw [show a + 1 + (b - (a + 1)) = b by omega]; exact hxb.1⟩
  · intro j
    -- The later chosen sets carry lower integral of `f (σ j)` at most `∑ δ (j + 1 + i) ≤ η`.
    have hU : ∫⁻ x in U j, f (σ j) x ∂μ ≤ η :=
      calc ∫⁻ x in U j, f (σ j) x ∂μ ≤ ∑' i, ∫⁻ x in s (σ (j + 1 + i)), f (σ j) x ∂μ :=
            lintegral_iUnion_le _ _
        _ ≤ ∑' i, η * 2⁻¹ ^ (i + 1) := by
          refine tsum_le_tsum fun i ↦ (hsmall j _ (by omega)).trans ?_
          exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one zero_le
            (ENNReal.inv_le_one.2 one_le_two) (show i + 1 ≤ j + 1 + i by omega)) zero_le
        _ = η := by
          rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one, ENNReal.one_sub_inv_two,
            inv_inv, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, mul_one]
    rw [← lintegral_inter_add_sdiff _ (s (σ j)) (hUm j), add_comm]
    gcongr
    exact (lintegral_mono_set inter_subset_right).trans hU

/-- If `g` has `L¹` mass more than `ε` on a set `S` and `f` has mass at most `ε / 2` there, then
`g - f` has mass more than `ε / 2` on `S`. -/
theorem half_lt_lintegral_enorm_sub {E : Type*} [NormedAddCommGroup E] {f g : α → E}
    (hf : AEStronglyMeasurable f μ) {S : Set α} {ε : ℝ≥0∞}
    (hg : ε < ∫⁻ x in S, ‖g x‖ₑ ∂μ) (hfS : ∫⁻ x in S, ‖f x‖ₑ ∂μ ≤ ε / 2) :
    ε / 2 < ∫⁻ x in S, ‖g x - f x‖ₑ ∂μ := by
  by_contra! hle
  have hsplit := lintegral_edist_triangle (μ := μ.restrict S) (f := fun _ : α ↦ (0 : E)) (g := g)
    (h := f) aestronglyMeasurable_zero hf.restrict
  simp only [edist_eq_enorm_sub, zero_sub, enorm_neg] at hsplit
  have := hg.trans_le (hsplit.trans (add_le_add hfS hle))
  rw [ENNReal.add_halves] at this
  exact lt_irrefl _ this

end MeasureTheory
