/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.VectorMeasure.FiniteHorizon
public import TauCeti.MeasureTheory.VectorMeasure.RiemannSums
public import TauCeti.Analysis.Calculus.MeanValue

/-!
# Change of variables along continuous finite-variation paths

For a continuous real path `g` of bounded variation and a continuously differentiable
function `f` on its range, the Stieltjes integral of `f' ∘ g` equals the increment of
`f ∘ g`. The measure is constructed once on the full horizon and can be used on any
closed subinterval. No absolute continuity of `g` is assumed: singular continuous
finite-variation paths are included.

This is the finite-variation chain rule used for the continuous drift coordinates in
change-of-variables formulas. Continuity of `f` and `f'` is required only on the image
of the integration subinterval, and differentiability only in the interior of that image.

The proof uses the tagged vector-measure sums and Mathlib's mean value theorem.

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition,
  Chapter I, finite-variation integration, and Chapter II, change of variables.
-/

public section

open MeasureTheory Set Filter Topology
open scoped BigOperators

namespace BoundedVariationOn

/-- The continuous finite-variation chain rule, on a subinterval of one fixed horizon.
The derivative measure excludes the initial atom and the path need not be absolutely
continuous. On `g '' Icc c d`, assume continuity of `f` and `f'`, and require the
specified derivative only in the interior. No hypotheses on `f` outside this image
are needed, even when the measure is constructed on a larger horizon. -/
theorem setIntegral_deriv_comp_vectorMeasureIcc {g f f' : ℝ → ℝ} {a b c d : ℝ}
    (hg : BoundedVariationOn g (Icc a b)) (hab : a ≤ b)
    (hgc : ContinuousOn g (Icc a b))
    (hfc : ContinuousOn f (g '' Icc c d))
    (hf : ∀ x ∈ interior (g '' Icc c d), HasDerivAt f (f' x) x)
    (hf' : ContinuousOn f' (g '' Icc c d))
    (hc : c ∈ Icc a b) (hd : d ∈ Icc a b) (hcd : c ≤ d) :
    (∫ᵛ t in Ioc c d, f' (g t)
      ∂[ContinuousLinearMap.mul ℝ ℝ; hg.vectorMeasureIcc hab]) = f (g d) - f (g c) := by
  classical
  -- Uniform grids allow the identity to follow from the tagged-sum convergence theorem.
  let τ (k i : ℕ) : ℝ := c + (i : ℝ) * ((d - c) / (k + 1))
  have hτ (k : ℕ) : Monotone (τ k) := by
    intro i j hij
    dsimp [τ]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij)
      (div_nonneg (sub_nonneg.mpr hcd) (by positivity)))
  have h₀ (k : ℕ) : τ k 0 = c := by simp [τ]
  have hn (k : ℕ) : τ k (k + 1) = d := by
    dsimp [τ]
    push_cast
    field_simp
    ring
  have hcell_cd (k i : ℕ) (hi : i ≤ k + 1) : τ k i ∈ Icc c d := by
    simpa only [h₀, hn] using (hτ k).mapsTo_Icc ⟨Nat.zero_le i, hi⟩
  have hsub : Icc c d ⊆ Icc a b := Icc_subset_Icc hc.1 hd.2
  have hcell (k i : ℕ) (hi : i ≤ k + 1) : τ k i ∈ Icc a b :=
    hsub (hcell_cd k i hi)
  -- The scalar mean value theorem supplies a derivative value between the two states.
  -- Continuity of the path realizes that value at an actual time in the same cell.
  have htag (k i : ℕ) (hi : i < k + 1) : ∃ t ∈ Icc (τ k i) (τ k (i + 1)),
      f' (g t) * (g (τ k (i + 1)) - g (τ k i)) =
        f (g (τ k (i + 1))) - f (g (τ k i)) := by
    have hcell_sub : Icc (τ k i) (τ k (i + 1)) ⊆ Icc c d :=
      Icc_subset_Icc (hcell_cd k i hi.le).1 (hcell_cd k (i + 1) hi).2
    have himage := image_mono (f := g) hcell_sub
    exact (hgc.mono (hcell_sub.trans hsub)).exists_deriv_comp_mul_sub_eq
      (hτ k (Nat.le_succ i)) (hfc.mono himage)
      (fun x hx ↦ hf x (interior_mono himage hx))
  choose ξ hξ heq using htag
  let tag (k i : ℕ) : ℝ := if hi : i < k + 1 then ξ k i hi else τ k i
  have htag_mem (k i : ℕ) (hi : i < k + 1) :
      tag k i ∈ Icc (τ k i) (τ k (i + 1)) := by
    simpa only [tag, dite_eq_left hi] using hξ k i hi
  -- The derivative along the path is continuous, so the selected tagged sums converge.
  have hlim := VectorMeasure.tendsto_sum_tagged_Ioc
    (μ := hg.vectorMeasureIcc hab) (B := ContinuousLinearMap.mul ℝ ℝ)
    (hf'.comp (hgc.mono hsub) (mapsTo_image g (Icc c d)))
    hτ h₀ hn htag_mem
    (δ := fun k : ℕ ↦ (d - c) / (k + 1))
    (fun k i _ ↦ le_of_eq (by dsimp [τ]; push_cast; ring))
    (by simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun k : ℕ ↦ (d - c) * (1 / ((k : ℝ) + 1))) atTop (𝓝 ((d - c) * 0))))
  -- Each of these sums already telescopes exactly to the endpoint increment.
  have hsum (k : ℕ) :
      (∑ i ∈ Finset.range (k + 1), (ContinuousLinearMap.mul ℝ ℝ)
        (f' (g (tag k i))) ((hg.vectorMeasureIcc hab) (Ioc (τ k i) (τ k (i + 1))))) =
      f (g d) - f (g c) := by
    calc
      _ = ∑ i ∈ Finset.range (k + 1),
          (f (g (τ k (i + 1))) - f (g (τ k i))) := by
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        have hi := Finset.mem_range.mp hi
        rw [hg.vectorMeasureIcc_Ioc hab
          ((hgc _ (hcell k i hi.le)).mono (Icc_subset_Icc_left (hcell k i hi.le).1))
          ((hgc _ (hcell k (i + 1) hi)).mono (Icc_subset_Icc_left (hcell k (i + 1) hi).1))
          (hcell k i hi.le) (hcell k (i + 1) hi) (hτ k (Nat.le_succ i))]
        simpa only [tag, dite_eq_left hi, ContinuousLinearMap.mul_apply'] using heq k i hi
      _ = _ := by rw [Finset.sum_range_sub (fun i ↦ f (g (τ k i))), hn, h₀]
  simp only [Function.comp_apply] at hlim
  simp only [hsum] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

end BoundedVariationOn
