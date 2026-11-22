/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.AbsMax
import TauCeti.Analysis.Complex.Runge.Rational.SimpleFraction
import TauCeti.Topology.ConnectedComponents

/-!
# Runge approximation of simple fractions

If a compact set `K` is filled in a subset `Ω` of the complex plane (without requiring `Ω` to be
open), every simple fraction with pole outside `K` is uniformly approximable on `K` by functions
holomorphic on `Ω`. Neither `K` nor `Ω` needs to be connected. Conversely, if `Ω` is open and every
simple fraction `(z - a)⁻¹` with `a ∈ Ω \ K` is uniformly approximable on `K` by functions
holomorphic on `Ω` (without requiring `K` to be compact or closed), then `K` is filled in `Ω`.

The forward proof delegates to `IsCompact.exists_rational_norm_inv_sub_lt` with poles in `Ωᶜ`,
converting filledness into the pole-set condition via
`TauCeti.IsFilledIn.compl_inter_connectedComponentIn_nonempty`.

## Main results

* `TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`: uniform approximation of `(z - a)⁻¹`
  on a compact set `K` filled in an arbitrary `Ω ⊆ ℂ`.
* `IsOpen.isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt`: converse for open `Ω` and
  arbitrary `K`.
* `IsOpen.isFilledIn_iff_forall_exists_differentiableOn_norm_inv_sub_lt`: equivalence for open `Ω`
  and compact `K ⊆ Ω`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1.
-/

public section

open Metric Set
open scoped Topology

namespace TauCeti

/-- **Runge approximation for a simple fraction.** On a compact set `K` filled in `Ω ⊆ ℂ`
(without requiring `Ω` to be open), a simple fraction whose pole avoids `K` is uniformly
approximable on `K` by functions holomorphic on all of `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_inv_sub_lt {K Ω : Set ℂ} (hfill : IsFilledIn K Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {a : ℂ} (ha : a ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖(z - a)⁻¹ - g z‖ < ε := by
  obtain ⟨p, q, -, hqΩ, hlt⟩ := hK.exists_rational_norm_inv_sub_lt ha
    (fun haH => hfill.compl_inter_connectedComponentIn_nonempty hKΩ ⟨haH, ha⟩) hε
  refine ⟨fun z => p.eval z / q.eval z, ?_, hlt⟩
  exact p.differentiable.differentiableOn.div q.differentiable.differentiableOn
    fun z hz h0 => (hqΩ z h0).1 hz

/-- **Converse of Runge's theorem.** If `Ω ⊆ ℂ` is open and every simple fraction `(z - a)⁻¹` with
`a ∈ Ω \ K` can be uniformly approximated on `K` by functions holomorphic on `Ω`, then `K` is
filled in `Ω`. No compactness or closedness of `K` is needed. -/
theorem _root_.IsOpen.isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt {K Ω : Set ℂ}
    (hΩ : IsOpen Ω)
    (h : ∀ a ∈ Ω \ K, ∀ ε > 0,
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖(z - a)⁻¹ - g z‖ < ε) :
    IsFilledIn K Ω := by
  rw [isFilledIn_iff]
  rintro a ha ⟨hcpt, hsub⟩
  set C := connectedComponentIn (Ω \ K) a
  have hfr : frontier C ⊆ closure K := hΩ.frontier_connectedComponentIn_sdiff_subset_closure hsub
  obtain ⟨R, hR⟩ := hcpt.isBounded.subset_closedBall a
  set M : ℝ := max R 1
  have hM : 0 < M := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨g, hg, hga⟩ := h a ha (2 * M)⁻¹ (by positivity)
  set f : ℂ → ℂ := fun z ↦ 1 - (z - a) * g z
  have hf_diff : DifferentiableOn ℂ f Ω :=
    (differentiableOn_const 1).sub ((differentiableOn_id.sub (differentiableOn_const a)).mul hg)
  have hf_cl : DiffContOnCl ℂ f C :=
    ⟨hf_diff.mono ((connectedComponentIn_subset _ _).trans sdiff_subset),
      hf_diff.continuousOn.mono hsub⟩
  have hle_K : ∀ z ∈ K, ‖f z‖ ≤ ‖z - a‖ * (2 * M)⁻¹ := by
    intro z hz
    have hza : z - a ≠ 0 := sub_ne_zero.mpr fun hza ↦ ha.2 (hza ▸ hz)
    have hfz : f z = (z - a) * ((z - a)⁻¹ - g z) := by
      simp only [f]; field_simp [hza]
    rw [hfz, norm_mul]
    exact mul_le_mul_of_nonneg_left (hga z hz).le (norm_nonneg (z - a))
  have hf_fr : ∀ y ∈ frontier C, ‖f y‖ ≤ 1 / 2 := by
    intro y hy
    have hy_le : ‖f y‖ ≤ ‖y - a‖ * (2 * M)⁻¹ :=
      ContinuousWithinAt.closure_le (hfr hy)
        (hf_diff.continuousOn.continuousAt (hΩ.mem_nhds (hsub hy.1))).norm.continuousWithinAt
        ((continuous_id.sub continuous_const).norm.mul_const (2 * M)⁻¹).continuousWithinAt
        hle_K
    have hyM : ‖y - a‖ ≤ M :=
      (dist_eq_norm y a ▸ mem_closedBall.mp (hR hy.1)).trans (le_max_left _ _)
    calc ‖f y‖ ≤ ‖y - a‖ * (2 * M)⁻¹ := hy_le
      _ ≤ M * (2 * M)⁻¹ := mul_le_mul_of_nonneg_right hyM (by positivity)
      _ = 1 / 2 := by field_simp [hM.ne']
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le
    (hcpt.isBounded.subset subset_closure) hf_cl hf_fr
    (subset_closure (mem_connectedComponentIn ha))
  simp only [f, sub_self, zero_mul, sub_zero, norm_one] at hmax
  norm_num at hmax

/-- **Runge's theorem (equivalence with simple-fraction approximation).** A compact subset `K` of
an open set `Ω ⊆ ℂ` is filled in `Ω` if and only if every simple fraction `(z - a)⁻¹` with
`a ∈ Ω \ K` is uniformly approximable on `K` by functions holomorphic on `Ω`. -/
theorem _root_.IsOpen.isFilledIn_iff_forall_exists_differentiableOn_norm_inv_sub_lt {K Ω : Set ℂ}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔
      ∀ a ∈ Ω \ K, ∀ ε > 0,
        ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖(z - a)⁻¹ - g z‖ < ε :=
  ⟨fun hfill _ ha _ hε ↦ hfill.exists_differentiableOn_norm_inv_sub_lt hK hKΩ ha.2 hε,
    hΩ.isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt⟩

end TauCeti
