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

A convex open subset `Ω` of a *proper* real normed space — a finite-dimensional one, say — is the
increasing union of convex open subsets whose closures are compact subsets of `Ω`.  Intersecting
the homothetic copies `c + t • (Ω - c)` about a point `c ∈ Ω`, for `0 < t < 1`, with expanding
balls gives the subsets: convexity keeps their closures inside `Ω`, the balls make them bounded,
and properness makes their closures compact.  Properness cannot be dropped: in an
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

open Filter Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] {Ω : Set E}

/-- **A convex open set is exhausted from inside by convex open sets.**  In a proper real normed
space, if `Ω` is open and convex, there is an increasing sequence of convex open sets `U n` whose
closures are compact subsets of `Ω` and whose union is `Ω`. -/
theorem exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq
    (hΩ : IsOpen Ω) (hconv : Convex ℝ Ω) :
    ∃ U : ℕ → Set E, Monotone U ∧ (∀ n, IsOpen (U n)) ∧ (∀ n, Convex ℝ (U n)) ∧
      (∀ n, IsCompact (closure (U n))) ∧ (∀ n, closure (U n) ⊆ Ω) ∧ ⋃ n, U n = Ω := by
  rcases eq_empty_or_nonempty Ω with rfl | ⟨c, hc⟩
  · exact ⟨fun _ => ∅, monotone_const, fun _ => isOpen_empty, fun _ => convex_empty,
      by simp, by simp, by simp⟩
  -- Fix `c ∈ Ω`.  The shrunken copy `V s` of `Ω` is cut out as the preimage of `Ω` under the
  -- homothety `h s` of ratio `s⁻¹` about `c`, so that openness and convexity are inherited from
  -- `Ω` for free.  The exhausting sequence intersects `V (t n)`, for ratios `t n` increasing to
  -- `1`, with balls of radius `n` about `c`.
  set h : ℝ → E → E := fun s x => s⁻¹ • (x - c) + c with hh
  set V : ℝ → Set E := fun s => h s ⁻¹' Ω with hV
  have hcont : ∀ s : ℝ, Continuous (h s) := by fun_prop
  have hV_open : ∀ s, IsOpen (V s) := fun s => hΩ.preimage (hcont s)
  have hV_convex : ∀ s : ℝ, Convex ℝ (V s) := by
    intro s
    have hrw : V s = (AffineMap.homothety c s⁻¹ : E →ᵃ[ℝ] E) ⁻¹' Ω := by
      ext x; simp [hV, hh, AffineMap.homothety_apply]
    rw [hrw]
    exact hconv.affine_preimage _
  have hV_one : V 1 = Ω := by ext x; simp [hV, hh]
  have hV_mono : ∀ {s s' : ℝ}, 0 < s → s ≤ s' → V s ⊆ V s' := by
    intro s s' hs hss' x hx
    have hs' : (0 : ℝ) < s' := hs.trans_le hss'
    have hcombo : h s' x = (s / s') • h s x + (1 - s / s') • c := by
      simp only [hh]
      match_scalars <;> (field_simp [hs.ne', hs'.ne']; try ring)
    rw [hV, mem_preimage, hcombo]
    exact hconv hx hc (by positivity) (by rw [sub_nonneg]; exact (div_le_one hs').2 hss')
      (by ring)
  have hV_subset : ∀ {s : ℝ}, 0 < s → s ≤ 1 → V s ⊆ Ω := fun hs hs1 =>
    hV_one ▸ hV_mono hs hs1
  have hV_closure : ∀ {s : ℝ}, 0 < s → s < 1 → closure (V s) ⊆ Ω := by
    intro s hs hs1 x hx
    have hpre : closure (V s) ⊆ h s ⁻¹' closure Ω :=
      closure_minimal (preimage_mono subset_closure) (isClosed_closure.preimage (hcont s))
    have hy : h s x ∈ closure Ω := hpre hx
    have hxc : x = (1 - s) • c + s • h s x := by
      simp only [hh]
      match_scalars <;> (field_simp [hs.ne']; try ring)
    rw [← hΩ.interior_eq, hxc]
    exact hconv.combo_interior_closure_mem_interior (by rwa [hΩ.interior_eq]) hy (by linarith)
      hs.le (by ring)
  -- The ratios `1 - (n + 2)⁻¹` increase to `1`.
  set t : ℕ → ℝ := fun n => 1 - ((n : ℝ) + 2)⁻¹ with ht
  have ht_pos : ∀ n, 0 < t n := by
    intro n
    have : ((n : ℝ) + 2)⁻¹ ≤ 2⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (by norm_num)]
      simp
    simp only [ht]
    linarith
  have ht_lt : ∀ n, t n < 1 := by
    intro n
    have : (0 : ℝ) < ((n : ℝ) + 2)⁻¹ := by positivity
    simp only [ht]; linarith
  have ht_mono : Monotone t := by
    intro m n hmn
    have : ((n : ℝ) + 2)⁻¹ ≤ ((m : ℝ) + 2)⁻¹ := by
      rw [inv_le_inv₀ (by positivity) (by positivity)]
      have : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      linarith
    simp only [ht]; linarith
  have ht_tendsto : Tendsto (fun n => (t n)⁻¹) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have h2 : Tendsto t atTop (𝓝 1) := by
      simpa [ht] using tendsto_const_nhds.sub h1
    simpa using h2.inv₀ one_ne_zero
  refine ⟨fun n => V (t n) ∩ Metric.ball c n, fun m n hmn => inter_subset_inter
      (hV_mono (ht_pos m) (ht_mono hmn)) (Metric.ball_subset_ball (by exact_mod_cast hmn)),
    fun n => (hV_open _).inter Metric.isOpen_ball,
    fun n => (hV_convex _).inter (convex_ball c n),
    fun n => (Metric.isBounded_ball.subset inter_subset_right).isCompact_closure,
    fun n => (closure_mono inter_subset_left).trans (hV_closure (ht_pos n) (ht_lt n)), ?_⟩
  refine subset_antisymm (iUnion_subset fun n => inter_subset_left.trans
    (hV_subset (ht_pos n) (ht_lt n).le)) fun x hx => ?_
  -- For `x ∈ Ω` the ray parameter `1` lies in the open set of ratios keeping `x` inside `Ω`.
  have hopen : IsOpen {r : ℝ | r • (x - c) + c ∈ Ω} :=
    hΩ.preimage (by fun_prop)
  have hone : (1 : ℝ) ∈ {r : ℝ | r • (x - c) + c ∈ Ω} := by simpa using hx
  obtain ⟨n, hn⟩ := (ht_tendsto.eventually (hopen.mem_nhds hone)).exists
  obtain ⟨m : ℕ, hm⟩ := exists_nat_gt (dist x c)
  refine mem_iUnion.2 ⟨max n m, hV_mono (ht_pos n) (ht_mono (Nat.le_max_left n m)) hn, ?_⟩
  rw [Metric.mem_ball]
  exact hm.trans_le (by exact_mod_cast Nat.le_max_right n m)

end TauCeti
