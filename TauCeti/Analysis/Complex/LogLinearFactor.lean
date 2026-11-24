/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import TauCeti.Topology.FilledHull

/-!
# Holomorphic logarithms of linear factors near a closed set

This file builds holomorphic logarithms of linear factors and of their quotients on an open
neighbourhood of a closed set `K ⊆ ℂ`, depending on where their roots lie in `Kᶜ`.

## Main results

* `TauCeti.exists_eqOn_sub_mul_exp_of_mem_connectedComponentIn`: if `a` and `b` lie in one
  connected component of the complement of a closed set `K`, then `(z - b) / (z - a)` has a
  holomorphic logarithm on an open neighbourhood of `K`.
* `TauCeti.exists_eqOn_sub_exp_of_notMem_filledHull`: if `b` lies in an unbounded component of
  the complement of a compact set `K`, then `z - b` has a holomorphic logarithm near `K`.

## Implementation notes

The logarithms are built along a chain of small discs in the complementary component: if
`‖a - a'‖ < ‖z - a'‖` then `(z - a) / (z - a')` lies in the disc of radius one about `1`, where the
principal logarithm is holomorphic. These are holomorphic counterparts of the continuous logarithm
`TauCeti.hasContinuousLogOn_sub_div_sub`.

## References

* A. Rainer, *Advanced Complex Analysis*, lecture notes, Lemma 15.1.
-/

public section

open Complex Metric Set

namespace TauCeti

variable {K : Set ℂ}

/-- One link of a disc chain: off the closed disc of radius `‖a - a'‖` about `a'`, the quotient
`(z - a) / (z - a')` lies in the disc of radius one about `1`, so it has a principal logarithm. -/
private theorem exists_eqOn_sub_mul_exp_of_norm_sub_lt (a a' : ℂ) :
    ∃ ℓ : ℂ → ℂ, DifferentiableOn ℂ ℓ {z | ‖a - a'‖ < ‖z - a'‖} ∧
      EqOn (fun z ↦ z - a) (fun z ↦ (z - a') * exp (ℓ z)) {z | ‖a - a'‖ < ‖z - a'‖} := by
  have hne {z : ℂ} (hz : ‖a - a'‖ < ‖z - a'‖) : z - a' ≠ 0 :=
    norm_pos_iff.mp ((norm_nonneg _).trans_lt hz)
  have hslit {z : ℂ} (hz : ‖a - a'‖ < ‖z - a'‖) : 1 + -((a - a') / (z - a')) ∈ slitPlane := by
    apply mem_slitPlane_of_norm_lt_one
    rwa [norm_neg, norm_div, div_lt_one ((norm_nonneg _).trans_lt hz)]
  refine ⟨fun z ↦ log (1 + -((a - a') / (z - a'))), DifferentiableOn.clog ?_ fun z hz ↦ hslit hz,
    fun z hz ↦ ?_⟩
  · exact (differentiableOn_const _).add
      ((differentiableOn_const _).div (differentiableOn_id.sub_const _) fun z hz ↦ hne hz).neg
  · have h := hne hz
    simp only [exp_log (slitPlane_ne_zero (hslit hz))]
    field_simp
    ring

/-- **Logarithms of quotients of linear factors.** If `b` lies in the connected component of `a`
in the complement of a closed set `K ⊆ ℂ`, then `z - b = (z - a) * exp (ℓ z)` on an open
neighbourhood of `K`, for some `ℓ` holomorphic there. That is, `(z - b) / (z - a)` has a
holomorphic logarithm near `K`. -/
theorem exists_eqOn_sub_mul_exp_of_mem_connectedComponentIn (hK : IsClosed K) {a b : ℂ}
    (hb : b ∈ connectedComponentIn Kᶜ a) :
    ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ ∃ ℓ : ℂ → ℂ, DifferentiableOn ℂ ℓ W ∧
      EqOn (fun z ↦ z - b) (fun z ↦ (z - a) * exp (ℓ z)) W := by
  -- The conclusion is a transitive relation between `a` and `b` which holds between any two
  -- nearby points of `Kᶜ`, so it holds throughout each connected component of `Kᶜ`.
  let R : ℂ → ℂ → Prop := fun a b ↦ ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ ∃ ℓ : ℂ → ℂ,
    DifferentiableOn ℂ ℓ W ∧ EqOn (fun z ↦ z - b) (fun z ↦ (z - a) * exp (ℓ z)) W
  have hstep (x y : ℂ) (hxy : ∀ z ∈ K, ‖y - x‖ < ‖z - x‖) : R x y := by
    obtain ⟨ℓ, hℓ, heq⟩ := exists_eqOn_sub_mul_exp_of_norm_sub_lt y x
    exact ⟨_, isOpen_lt continuous_const (continuous_id.sub continuous_const).norm, hxy, ℓ, hℓ,
      heq⟩
  have ha : a ∈ Kᶜ := connectedComponentIn_nonempty_iff.mp ⟨b, hb⟩
  refine isPreconnected_connectedComponentIn.induction₂' R (fun x hx ↦ ?_) ?_
    (mem_connectedComponentIn ha) hb
  · obtain ⟨r, hr, hball⟩ :=
      Metric.isOpen_iff.mp hK.isOpen_compl x (connectedComponentIn_subset _ _ hx)
    have hfar (z : ℂ) (hz : z ∈ K) : r ≤ ‖z - x‖ :=
      not_lt.mp fun h ↦ hball (mem_ball_iff_norm.mpr h) hz
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds x (half_pos hr))] with y hy
    rw [mem_ball_iff_norm] at hy
    refine ⟨hstep x y fun z hz ↦ by linarith [hfar z hz], hstep y x fun z hz ↦ ?_⟩
    have := norm_sub_le_norm_sub_add_norm_sub z y x
    rw [norm_sub_rev x y]
    linarith [hfar z hz]
  · rintro x y z - - - ⟨W₁, hW₁, hKW₁, ℓ₁, hℓ₁, h₁⟩ ⟨W₂, hW₂, hKW₂, ℓ₂, hℓ₂, h₂⟩
    refine ⟨W₁ ∩ W₂, hW₁.inter hW₂, subset_inter hKW₁ hKW₂, fun w ↦ ℓ₁ w + ℓ₂ w,
      (hℓ₁.mono inter_subset_left).add (hℓ₂.mono inter_subset_right), fun w hw ↦ ?_⟩
    have e₁ := h₁ hw.1
    have e₂ := h₂ hw.2
    simp only at e₁ e₂ ⊢
    rw [e₂, e₁, exp_add]
    ring

/-- **Logarithms of linear factors with root in the unbounded component.** If `b` lies outside
the filled hull of a compact set `K ⊆ ℂ`, i.e. in an unbounded component of `Kᶜ`, then
`z - b = exp (ℓ z)` on an open neighbourhood of `K`, for some `ℓ` holomorphic there. -/
theorem exists_eqOn_sub_exp_of_notMem_filledHull (hK : IsCompact K) {b : ℂ}
    (hb : b ∉ filledHull K) :
    ∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ ∃ ℓ : ℂ → ℂ, DifferentiableOn ℂ ℓ W ∧
      EqOn (fun z ↦ z - b) (fun z ↦ exp (ℓ z)) W := by
  -- Move the root to a point `a` of the same component outside a disc containing `K`; there
  -- `z - a = -a * (1 - z / a)` has a principal logarithm.
  have hbK : b ∈ Kᶜ := fun h ↦ hb (subset_filledHull h)
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  rw [mem_filledHull_iff, isBounded_iff_subset_closedBall 0] at hb
  obtain ⟨a, ha, haR⟩ := not_subset.mp (not_exists.mp hb (max R 0))
  rw [mem_closedBall_zero_iff, not_le, max_lt_iff] at haR
  have ha0 : a ≠ 0 := norm_pos_iff.mp haR.2
  have hba : b ∈ connectedComponentIn Kᶜ a := by
    rw [← connectedComponentIn_eq ha]
    exact mem_connectedComponentIn hbK
  obtain ⟨W, hW, hKW, ℓ, hℓ, heq⟩ :=
    exists_eqOn_sub_mul_exp_of_mem_connectedComponentIn hK.isClosed hba
  have hslit {z : ℂ} (hz : z ∈ ball (0 : ℂ) ‖a‖) : 1 + -(z / a) ∈ slitPlane := by
    apply mem_slitPlane_of_norm_lt_one
    rwa [norm_neg, norm_div, div_lt_one (norm_pos_iff.mpr ha0), ← mem_ball_zero_iff]
  refine ⟨W ∩ ball 0 ‖a‖, hW.inter isOpen_ball,
    subset_inter hKW fun z hz ↦ mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp (hR hz)).trans_lt
      haR.1),
    fun z ↦ ℓ z + (log (-a) + log (1 + -(z / a))),
    (hℓ.mono inter_subset_left).add ((differentiableOn_const _).add
      (DifferentiableOn.clog ((differentiableOn_const _).add (differentiableOn_id.div_const _).neg)
        fun z hz ↦ hslit hz.2)), fun z hz ↦ ?_⟩
  have e := heq hz.1
  simp only at e ⊢
  rw [e, exp_add, exp_add, exp_log (neg_ne_zero.mpr ha0), exp_log (slitPlane_ne_zero (hslit hz.2))]
  field_simp
  ring


end TauCeti
