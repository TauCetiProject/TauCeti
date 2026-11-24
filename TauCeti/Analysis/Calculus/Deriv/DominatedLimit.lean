/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Derivatives of limits under dominated convergence of the derivatives

Let `f i : ℝ → F` be differentiable curves in a Banach space with continuous derivatives `f' i`,
converging pointwise to `y` along a countably generated filter. If the derivatives converge
pointwise to a continuous `g` and are eventually bounded on each interval `[-T, T]`, then `y` is
differentiable with derivative `g` (`TauCeti.hasDerivAt_of_tendsto_of_norm_le`).

Each curve is the integral of its derivative, `f i t - f i 0 = ∫₀ᵗ f' i`. By dominated convergence
these integrals converge to `∫₀ᵗ g`, so `y t - y 0 = ∫₀ᵗ g`, and the fundamental theorem of
calculus differentiates the right side. Unlike Mathlib's `hasDerivAt_of_tendstoUniformly` and its
variants, the derivatives need not converge uniformly on any set. This is the form in which the
derivative passes to the limit along a subsequence of solutions of `x' = X_n(t, x)` extracted by
the Arzelà–Ascoli theorem: the fields along the solutions converge pointwise, and boundedly, to
the limit field along the limit curve.
-/

public section

open Set Filter Topology MeasureTheory

namespace TauCeti

variable {ι F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {l : Filter ι} [l.IsCountablyGenerated] [l.NeBot] {f f' : ι → ℝ → F} {y g : ℝ → F}

/-- **A pointwise limit of curves whose derivatives converge boundedly.** Let `f i` be curves with
continuous derivatives `f' i`, converging pointwise to `y`. If the derivatives converge pointwise
to a continuous `g`, and are eventually bounded on each interval `[-T, T]` by a constant, then `y`
has derivative `g`. -/
theorem hasDerivAt_of_tendsto_of_norm_le (hf : ∀ i t, HasDerivAt (f i) (f' i t) t)
    (hf' : ∀ i, Continuous (f' i)) (hfy : ∀ t, Tendsto (fun i ↦ f i t) l (𝓝 (y t)))
    (hf'g : ∀ t, Tendsto (fun i ↦ f' i t) l (𝓝 (g t)))
    (hbound : ∀ T, ∃ B, ∀ᶠ i in l, ∀ t ∈ Icc (-T) T, ‖f' i t‖ ≤ B) (hg : Continuous g)
    (t : ℝ) : HasDerivAt y (g t) t := by
  -- The limit is the integral of `g`: pass to the limit in `f i s - f i 0 = ∫₀ˢ f' i`.
  have hint (s : ℝ) : y s - y 0 = ∫ τ in (0 : ℝ)..s, g τ := by
    obtain ⟨B, hB⟩ := hbound |s|
    have h₁ : Tendsto (fun i ↦ ∫ τ in (0 : ℝ)..s, f' i τ) l (𝓝 (∫ τ in (0 : ℝ)..s, g τ)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ ↦ B)
        (Eventually.of_forall fun i ↦ (hf' i).aestronglyMeasurable)
        (hB.mono fun i hi ↦ ae_of_all _ fun τ hτ ↦ hi τ ?_) intervalIntegrable_const
        (ae_of_all _ fun τ _ ↦ hf'g τ)
      -- A time between `0` and `s` lies in `[-|s|, |s|]`.
      rcases mem_uIcc.1 (uIoc_subset_uIcc hτ) with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
        exact ⟨by linarith [neg_abs_le s, abs_nonneg s], by linarith [le_abs_self s, abs_nonneg s]⟩
    refine tendsto_nhds_unique (((hfy s).sub (hfy 0)).congr fun i ↦ ?_) h₁
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ ↦ hf i τ)
      ((hf' i).intervalIntegrable _ _)).symm
  -- Differentiate `y s = y 0 + ∫₀ˢ g`.
  exact (((hg.integral_hasStrictDerivAt 0 t).hasDerivAt).const_add (y 0)).congr_of_eventuallyEq
    (Eventually.of_forall fun s ↦ eq_add_of_sub_eq' (hint s))

end TauCeti
