/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Analysis.Complex.AbsMax
import TauCeti.Analysis.Calculus.Deriv.Polynomial
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

Conversely, if a component `C` of `Ω \ K` is relatively compact in `Ω`, its frontier lies in `K`.
For `a ∈ C`, an approximation `g` of `(z - a)⁻¹` on `K` makes `(z - a) g(z) - 1` small on `K`,
hence on `C` by the maximum modulus principle, which fails at `z = a`.

## Main results

* `TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`: uniform approximation of `(z - a)⁻¹`
  on a compact set `K` filled in an arbitrary `Ω ⊆ ℂ`.
* `TauCeti.isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt`: conversely, if the
  simple fractions with poles in `Ω \ K` are so approximable, then `K` is filled in `Ω`.
* `TauCeti.isFilledIn_iff_forall_exists_differentiableOn_norm_inv_sub_lt`: the resulting
  characterisation of compact sets filled in `Ω`.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 13.9.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

variable {K Ω : Set ℂ}

/-- **Runge approximation for a simple fraction.** On a compact set `K` filled in `Ω ⊆ ℂ`
(without requiring `Ω` to be open), a simple fraction whose pole avoids `K` is uniformly
approximable on `K` by functions holomorphic on all of `Ω`. -/
theorem IsFilledIn.exists_differentiableOn_norm_inv_sub_lt (hfill : IsFilledIn K Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) {a : ℂ} (ha : a ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧ ∀ z ∈ K, ‖(z - a)⁻¹ - g z‖ < ε := by
  obtain ⟨p, q, -, hqΩ, hlt⟩ := hK.exists_rational_norm_inv_sub_lt ha
    (fun haH => hfill.compl_inter_connectedComponentIn_nonempty hKΩ ⟨haH, ha⟩) hε
  refine ⟨fun z => p.eval z / q.eval z, ?_, hlt⟩
  exact Polynomial.differentiableOn_eval_div_eval fun z hz h0 => (hqΩ z h0).1 hz

/-- **The converse of Runge's theorem for simple fractions.** Let `K ⊆ ℂ` be any set and `Ω ⊆ ℂ`
open. If for every `a ∈ Ω \ K` the simple fraction `z ↦ (z - a)⁻¹` is a uniform limit on `K` of
functions holomorphic on `Ω`, then `K` is filled in `Ω`. -/
theorem isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt (hΩ : IsOpen Ω)
    (h : ∀ a ∈ Ω \ K, ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ K, ‖(z - a)⁻¹ - g z‖ < ε) :
    IsFilledIn K Ω := by
  -- `Ω \ K` is open: a pole `a ∈ Ω \ K` lies off `closure K`, since near `a` the simple fraction
  -- is unbounded on `K` while its holomorphic approximant stays bounded.
  have hΩK : IsOpen (Ω \ K) := by
    suffices Ω \ K = Ω \ closure K from this ▸ hΩ.sdiff isClosed_closure
    refine (sdiff_subset_sdiff_right subset_closure).antisymm' fun a ha ↦ ⟨ha.1, fun haK ↦ ?_⟩
    obtain ⟨g, hg, hgK⟩ := h a ha 1 one_pos
    have := mem_closure_iff_nhdsWithin_neBot.1 haK
    have hsub : Tendsto (· - a) (𝓝[K] a) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_nhdsWithin_of_tendsto_nhds
        (by simpa using (continuous_sub_right a).tendsto a),
        eventually_mem_nhdsWithin.mono fun z hz ↦ sub_ne_zero.2 fun hza ↦ ha.2 (hza ▸ hz)⟩
    have hg' : Tendsto (fun z ↦ -‖g z‖) (𝓝[K] a) (𝓝 (-‖g a‖)) :=
      ((hg.differentiableAt (hΩ.mem_nhds ha.1)).continuousAt.norm.neg).mono_left
        nhdsWithin_le_nhds
    have hlim := tendsto_atTop_mono
      (fun z ↦ (sub_eq_add_neg _ _).symm.trans_le (norm_sub_norm_le _ _))
      ((tendsto_norm_inv_nhdsNE_zero_atTop.comp hsub).atTop_add hg')
    obtain ⟨z, hz, hzK⟩ := ((hlim.eventually_ge_atTop 1).and self_mem_nhdsWithin).exists
    exact (hgK z hzK).not_ge hz
  rw [isFilledIn_iff]
  rintro a ha ⟨hCc, hCΩ⟩
  set C := connectedComponentIn (Ω \ K) a
  -- The frontier of the component `C` lies in `K`.
  have hfr : frontier C ⊆ K := frontier_connectedComponentIn_sdiff_subset hΩK hCΩ
  obtain ⟨R, hR⟩ := hCc.isBounded.subset_closedBall a
  set R' := max R 0
  obtain ⟨g, hg, hgK⟩ := h a ha (R' + 1)⁻¹ (by positivity)
  -- `F z = (z - a) g z - 1` is small on the frontier of `C`, but `F a = -1`.
  set F : ℂ → ℂ := fun z ↦ (z - a) * g z - 1
  have hFK (z : ℂ) (hz : z ∈ frontier C) : ‖F z‖ ≤ R' / (R' + 1) := by
    have hza : z - a ≠ 0 := sub_ne_zero.2 fun hza ↦ ha.2 (hza ▸ hfr hz)
    have hF : F z = -((z - a) * ((z - a)⁻¹ - g z)) := by
      simp only [F, mul_sub, mul_inv_cancel₀ hza]
      ring
    rw [hF, norm_neg, norm_mul, div_eq_mul_inv]
    refine mul_le_mul ?_ (hgK z (hfr hz)).le (norm_nonneg _) (le_max_right R 0)
    exact (mem_closedBall_iff_norm.1 (hR (frontier_subset_closure hz))).trans (le_max_left R 0)
  have hFd : DifferentiableOn ℂ F (closure C) :=
    (((differentiableOn_id.sub_const a).mul hg).sub_const 1).mono hCΩ
  have hFa := Complex.norm_le_of_forall_mem_frontier_norm_le
    (hCc.isBounded.subset subset_closure) hFd.diffContOnCl hFK
    (subset_closure (mem_connectedComponentIn ha))
  have hF1 : ‖F a‖ = 1 := by simp only [F, sub_self, zero_mul, zero_sub, norm_neg, norm_one]
  have hR'1 : R' / (R' + 1) < 1 := (div_lt_one (by positivity)).2 (lt_add_one R')
  linarith

/-- **Runge's theorem for simple fractions, characterisation.** A compact subset `K` of an open set
`Ω ⊆ ℂ` is filled in `Ω` if and only if, for every `a ∈ Ω \ K`, the simple fraction
`z ↦ (z - a)⁻¹` is a uniform limit on `K` of functions holomorphic on `Ω`. -/
theorem isFilledIn_iff_forall_exists_differentiableOn_norm_inv_sub_lt (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    IsFilledIn K Ω ↔ ∀ a ∈ Ω \ K, ∀ ε > 0, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g Ω ∧
      ∀ z ∈ K, ‖(z - a)⁻¹ - g z‖ < ε :=
  ⟨fun hfill _ ha _ hε ↦ hfill.exists_differentiableOn_norm_inv_sub_lt hK hKΩ ha.2 hε,
    isFilledIn_of_forall_exists_differentiableOn_norm_inv_sub_lt hΩ⟩

end TauCeti
