/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Exhausting a convex open set from inside

A convex open subset `Ω` of a *proper* real seminormed space — a finite-dimensional normed space,
say — is the increasing union of convex open subsets `U n` whose closures are compact subsets of
`Ω`, with the closure of each `U n` inside `U (n + 1)`.  Intersecting the shrunken copies
`c + r⁻¹ • (Ω - c)` about a point `c ∈ Ω`, for ratios `r > 1` decreasing to `1`, with expanding
balls gives the subsets: convexity puts the closure of each copy inside the next, the balls make
them bounded, and properness makes their closures compact.  Properness cannot be dropped: in an
infinite-dimensional normed space the unit ball is exhausted by no sequence of relatively compact
open subsets.

Convexity of the pieces is the point of the construction.  A general open set is exhausted by the
relatively compact open sets `{x | dist x Ωᶜ > 1 / n} ∩ ball 0 n`, but those are not convex, and an
estimate whose constant depends on convexity of the domain — a Poincaré-type inequality, say —
cannot be transported along them.

## Main declaration

* `TauCeti.exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq`: the exhaustion.
-/

public section

namespace TauCeti

open AffineMap Filter Set Topology

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] {Ω : Set E}

/-- **A convex open set is exhausted from inside by convex open sets.**  In a proper real
seminormed space, if `Ω` is open and convex, there is an increasing sequence of convex open sets
`U n` whose closures are compact subsets of `Ω`, each contained in the next set `U (n + 1)`, and
whose union is `Ω`. -/
theorem exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) :
    ∃ U : ℕ → Set E, Monotone U ∧ (∀ n, IsOpen (U n)) ∧ (∀ n, Convex ℝ (U n)) ∧
      (∀ n, IsCompact (closure (U n))) ∧ (∀ n, closure (U n) ⊆ U (n + 1)) ∧
      (∀ n, closure (U n) ⊆ Ω) ∧ ⋃ n, U n = Ω := by
  rcases eq_empty_or_nonempty Ω with rfl | ⟨c, hc⟩
  · exact ⟨fun _ => ∅, monotone_const, fun _ => isOpen_empty, fun _ => convex_empty,
      by simp, by simp, by simp, by simp⟩
  -- Fix `c ∈ Ω`.  For a ratio `r > 1`, the preimage of an open convex set `s ∋ c` under the
  -- homothety of ratio `r` about `c` is a shrunken copy of `s` whose closure lies in `s`.
  have key : ∀ {s : Set E}, IsOpen s → Convex ℝ s → c ∈ s → ∀ {r : ℝ}, 1 < r →
      closure (homothety c r ⁻¹' s) ⊆ s := by
    intro s hs hsc hcs r hr x hx
    obtain ⟨y, hy, hyx⟩ := hsc.closure_subset_image_homothety_interior_of_one_lt
      (hs.interior_eq.symm ▸ hcs) r hr ((homothety_continuous c r).closure_preimage_subset s hx)
    rwa [← homothety_injective c (one_pos.trans hr).ne' hyx, ← hs.interior_eq]
  -- The shrunken copies `V r` of `Ω` are open and convex, and their closures are nested.
  set V : ℝ → Set E := fun r => homothety c r ⁻¹' Ω with hV
  have hV_open : ∀ r, IsOpen (V r) := fun r => hΩ.preimage (homothety_continuous c r)
  have hV_convex : ∀ r, Convex ℝ (V r) := fun r => hconv.affine_preimage _
  have hV_closure : ∀ {r r' : ℝ}, 1 ≤ r' → r' < r → closure (V r) ⊆ V r' := by
    intro r r' hr' hr
    have hr'0 : 0 < r' := zero_lt_one.trans_le hr'
    have hrw : V r = homothety c (r / r') ⁻¹' V r' := by
      ext x; simp [hV, ← homothety_mul_apply, mul_div_cancel₀ _ hr'0.ne']
    rw [hrw]
    exact key (hV_open r') (hV_convex r') (by simpa [hV] using hc) ((one_lt_div hr'0).2 hr)
  -- The ratios `r n = 1 + 1 / (n + 1)` decrease strictly to `1`; the exhausting sequence
  -- intersects `V (r n)` with balls of radius `n` about `c`.
  set r : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1) with hr
  have hr_one : ∀ n, 1 < r n := fun n => lt_add_of_pos_right 1 Nat.one_div_pos_of_nat
  have hr_succ : ∀ n, r (n + 1) < r n := fun n => by
    simpa [hr] using Nat.one_div_lt_one_div (α := ℝ) n.lt_succ_self
  have hr_tendsto : Tendsto r atTop (𝓝 1) := by
    simpa [hr] using (tendsto_const_nhds (x := (1 : ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hVr_mono : Monotone fun n => V (r n) :=
    monotone_nat_of_le_succ fun n => subset_closure.trans (hV_closure (hr_one _).le (hr_succ n))
  set U : ℕ → Set E := fun n => V (r n) ∩ Metric.ball c n
  have hU_closure : ∀ n, closure (U n) ⊆ U (n + 1) := fun n =>
    (closure_inter_subset_inter_closure _ _).trans <| inter_subset_inter
      (hV_closure (hr_one _).le (hr_succ n))
      (Metric.closure_ball_subset_closedBall.trans (Metric.closedBall_subset_ball (by simp)))
  have hU_subset : ∀ n, closure (U n) ⊆ Ω := fun n =>
    (closure_mono inter_subset_left).trans (key hΩ hconv hc (hr_one n))
  refine ⟨U, monotone_nat_of_le_succ fun n => subset_closure.trans (hU_closure n),
    fun n => (hV_open _).inter Metric.isOpen_ball,
    fun n => (hV_convex _).inter (convex_ball c n),
    fun n => (Metric.isBounded_ball.subset inter_subset_right).isCompact_closure, hU_closure,
    hU_subset, subset_antisymm (iUnion_subset fun n => subset_closure.trans (hU_subset n))
      fun x hx => ?_⟩
  -- For `x ∈ Ω` the ratio `1` lies in the open set of ratios keeping `x` inside `Ω`.
  have hcont : Continuous fun s : ℝ => homothety c s x := by
    simp only [homothety_apply, vsub_eq_sub, vadd_eq_add]
    fun_prop
  obtain ⟨n, hn⟩ :=
    (hr_tendsto.eventually ((hΩ.preimage hcont).mem_nhds (by simpa using hx))).exists
  obtain ⟨m : ℕ, hm⟩ := exists_nat_gt (dist x c)
  exact mem_iUnion.2 ⟨max n m, hVr_mono (le_max_left n m) hn,
    Metric.mem_ball.2 (hm.trans_le (by exact_mod_cast le_max_right n m))⟩

end TauCeti
