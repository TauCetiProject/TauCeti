/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Topology.FilledIn
import Mathlib.Topology.Separation.Regular
import TauCeti.Analysis.Complex.Pompeiu.Discretization
import TauCeti.Analysis.Complex.Runge.SimpleFraction

/-!
# Runge's approximation theorem for normed-space-valued holomorphic functions

Let `K` be a compact subset filled in an open set `Ω ⊆ ℂ`, with no connectivity assumption on
either `K` or `Ω`. Every function `g : ℂ → W` holomorphic on an open neighbourhood `V` of `K`,
with values in an arbitrary complex normed space `W` (not necessarily complete), is uniformly
approximable on `K` by functions holomorphic on all of `Ω`
(`TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`).

The proof shrinks `V` to a precompact open neighbourhood `V'` of `K` so that `g` is bounded on
`V'`, discretizes the Cauchy–Pompeiu representation on `K` into finitely many simple fractions
with poles outside `K` (`IsCompact.exists_norm_sub_sum_mul_sub_inv_smul_le`), and replaces each
simple fraction by a scalar function holomorphic on `Ω` via simple-fraction Runge approximation
(`TauCeti.IsFilledIn.exists_differentiableOn_norm_inv_sub_lt`).

## Main results

* `TauCeti.IsFilledIn.exists_differentiableOn_norm_sub_lt`: uniform approximation on a filled-in
  compact set by functions holomorphic on the ambient open set, with values in any complex normed
  space.

## References

* A. Rainer, *Advanced Complex Analysis*, Theorem 11.1.
* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, 3rd ed.,
  North-Holland, 1990, Theorem 1.3.1.
-/

public section

open Set

namespace TauCeti

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- **Runge's approximation theorem (normed-space valued).** On a compact set `K` filled in an
open set `Ω ⊆ ℂ`, every function holomorphic on an open neighbourhood `V` of `K` with values in a
complex normed space `W` is uniformly approximable on `K` by functions holomorphic on `Ω`. Neither
`K` nor `Ω` needs to be connected, and `W` need not be complete. -/
theorem IsFilledIn.exists_differentiableOn_norm_sub_lt {K V Ω : Set ℂ}
    (hfill : IsFilledIn K Ω) (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hV : IsOpen V) (hKV : K ⊆ V) {g : ℂ → W} (hg : DifferentiableOn ℂ g V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℂ → W, DifferentiableOn ℂ P Ω ∧ ∀ z ∈ K, ‖g z - P z‖ < ε := by
  -- Shrink `V` to a relatively compact open neighbourhood `V'` of `K` so `g` is bounded on `V'`.
  obtain ⟨V', hV'_open, hKV', hV'_cl, hV'_cpt⟩ :=
    exists_open_between_and_isCompact_closure hK hV hKV
  obtain ⟨M, hM⟩ := hV'_cpt.exists_bound_of_continuousOn (hg.continuousOn.mono hV'_cl)
  set M' : ℝ := max M 1
  have hM'_pos : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  have hM' : ∀ z ∈ V', ‖g z‖ ≤ M' := fun z hz ↦
    (hM z (subset_closure hz)).trans (le_max_left M 1)
  -- Discretize Cauchy–Pompeiu on `K` into finitely many simple fractions with poles outside `K`.
  obtain ⟨N, ζ, c, hζ, hdisc⟩ :=
    hK.exists_norm_sub_sum_mul_sub_inv_smul_le hV'_open hKV' (ε := ε / (2 * M')) (by positivity)
  have hdisc' (w : ℂ) (hw : w ∈ K) :
      ‖g w - ∑ i, (c i * (w - ζ i)⁻¹) • g (ζ i)‖ ≤ ε / 2 := by
    have h := hdisc g M' (hg.mono (subset_closure.trans hV'_cl)) hM' w hw
    have hmul : ε / (2 * M') * M' = ε / 2 := by field_simp
    rwa [hmul] at h
  -- Approximate each simple fraction `(w - ζ i)⁻¹` on `K` by a holomorphic function on `Ω`.
  have hrunge (i : Fin N) : ∃ q : ℂ → ℂ, DifferentiableOn ℂ q Ω ∧
      ∀ w ∈ K, ‖(w - ζ i)⁻¹ - q w‖ <
        ε / (2 * ((N : ℝ) + 1) * (‖c i‖ * ‖g (ζ i)‖ + 1)) :=
    hfill.exists_differentiableOn_norm_inv_sub_lt hΩ hK hKΩ (hζ i).2 (by positivity)
  choose q hq hq_lt using hrunge
  refine ⟨fun w ↦ ∑ i, (c i * q i w) • g (ζ i),
    DifferentiableOn.fun_sum fun i _ ↦ ((differentiableOn_const _).mul (hq i)).smul_const _,
    fun w hw ↦ ?_⟩
  have hsplit : g w - ∑ i, (c i * q i w) • g (ζ i) =
      (g w - ∑ i, (c i * (w - ζ i)⁻¹) • g (ζ i)) +
        ∑ i, (c i * ((w - ζ i)⁻¹ - q i w)) • g (ζ i) := by
    simp only [mul_sub, sub_smul, Finset.sum_sub_distrib]
    abel
  have hterm (i : Fin N) :
      ‖(c i * ((w - ζ i)⁻¹ - q i w)) • g (ζ i)‖ ≤ ε / (2 * ((N : ℝ) + 1)) := by
    rw [norm_smul, norm_mul]
    have hcoeff : ‖c i‖ * ‖g (ζ i)‖ ≤ ‖c i‖ * ‖g (ζ i)‖ + 1 :=
      le_add_of_nonneg_right zero_le_one
    have hden : (0 : ℝ) < ‖c i‖ * ‖g (ζ i)‖ + 1 := by positivity
    calc ‖c i‖ * ‖(w - ζ i)⁻¹ - q i w‖ * ‖g (ζ i)‖
        = (‖c i‖ * ‖g (ζ i)‖) * ‖(w - ζ i)⁻¹ - q i w‖ := by ring
      _ ≤ (‖c i‖ * ‖g (ζ i)‖ + 1) *
            (ε / (2 * ((N : ℝ) + 1) * (‖c i‖ * ‖g (ζ i)‖ + 1))) :=
          mul_le_mul hcoeff (hq_lt i w hw).le (norm_nonneg _) hden.le
      _ = ε / (2 * ((N : ℝ) + 1)) := by field_simp
  have hsum_lt : ∑ i : Fin N, ‖(c i * ((w - ζ i)⁻¹ - q i w)) • g (ζ i)‖ < ε / 2 := by
    calc ∑ i : Fin N, ‖(c i * ((w - ζ i)⁻¹ - q i w)) • g (ζ i)‖
        ≤ ∑ _i : Fin N, ε / (2 * ((N : ℝ) + 1)) := Finset.sum_le_sum fun i _ ↦ hterm i
      _ = (N : ℝ) * (ε / (2 * ((N : ℝ) + 1))) := by simp
      _ < ((N : ℝ) + 1) * (ε / (2 * ((N : ℝ) + 1))) :=
          mul_lt_mul_of_pos_right (lt_add_one _) (by positivity)
      _ = ε / 2 := by field_simp
  calc ‖g w - ∑ i, (c i * q i w) • g (ζ i)‖
      ≤ ‖g w - ∑ i, (c i * (w - ζ i)⁻¹) • g (ζ i)‖ +
          ‖∑ i, (c i * ((w - ζ i)⁻¹ - q i w)) • g (ζ i)‖ := by
        rw [hsplit]; exact norm_add_le _ _
    _ ≤ ε / 2 + ∑ i, ‖(c i * ((w - ζ i)⁻¹ - q i w)) • g (ζ i)‖ :=
        add_le_add (hdisc' w hw) (norm_sum_le _ _)
    _ < ε / 2 + ε / 2 := add_lt_add_right hsum_lt _
    _ = ε := add_halves ε

end TauCeti
