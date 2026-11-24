/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MetricSpace.Length
import TauCeti.Topology.MetricSpace.Arclength.Basic

/-!
# Lipschitz paths in length spaces

In a length space, two points at distance less than `r` are joined by a path on the unit interval
that is `r`-Lipschitz (`TauCeti.IsLengthSpace.exists_lipschitz_path`). The length space provides a
joining curve of length `L < r`, and its arclength factorization
`BoundedVariationOn.exists_arclength_factorization` reparametrizes it at constant speed `L`
on `[0, 1]`.

Such uniformly Lipschitz paths form compact families in a proper space, which is how minimizing
paths are obtained as limits of nearly minimizing ones.

## References

* D. Burago, Y. Burago, and S. Ivanov, *A Course in Metric Geometry*, AMS, 2001, Section 2.5.
* Riccardo Brasca, *ColdingMinicozziTheory*,
  [complete-ball proof](https://github.com/riccardobrasca/ColdingMinicozziTheory/commit/afd6c6c8).
-/

public section

open Set
open scoped ENNReal NNReal unitInterval

namespace TauCeti

variable {X : Type*} [MetricSpace X]

/-- In a length space, two points at distance less than `r` are joined by an `r`-Lipschitz path on
the unit interval. -/
theorem IsLengthSpace.exists_lipschitz_path [IsLengthSpace X] {x y : X} {r : ℝ}
    (hr : dist x y < r) :
    ∃ f : C(I, X), f 0 = x ∧ f 1 = y ∧ LipschitzWith r.toNNReal f := by
  obtain ⟨γ, hγ, hlen⟩ := IsLengthSpace.exists_eVariationOn_lt_ofReal hr
  have hBV : BoundedVariationOn γ (Icc 0 1) := (hlen.trans_le le_top).ne
  set L := (eVariationOn γ (Icc 0 1)).toReal
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  have hLr : L ≤ r := by
    calc
      _ ≤ (ENNReal.ofReal r).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlen.le
      _ = r := ENNReal.toReal_ofReal (dist_nonneg.trans_lt hr).le
  obtain ⟨g, hg, hfactor, -⟩ := hBV.exists_arclength_factorization hγ.continuousOn zero_le_one
  have harg (t : I) : L * (t : ℝ) ∈ Icc 0 L :=
    ⟨mul_nonneg hL t.property.1, mul_le_of_le_one_right hL t.property.2⟩
  have hLip : LipschitzWith r.toNNReal (fun t : I ↦ g (L * (t : ℝ))) := by
    refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
    have hd := hg.dist_le_mul _ (harg s) _ (harg t)
    rw [NNReal.coe_one, one_mul, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hL] at hd
    rw [Real.coe_toNNReal r (dist_nonneg.trans_lt hr).le]
    exact hd.trans (mul_le_mul_of_nonneg_right hLr (abs_nonneg _))
  refine ⟨⟨fun t ↦ g (L * (t : ℝ)), hLip.continuous⟩, ?_, ?_, hLip⟩
  · simpa only [ContinuousMap.coe_mk, Icc.coe_zero, Function.comp_apply, variationOnFromTo.self,
      hγ.source, mul_zero] using hfactor (left_mem_Icc.2 zero_le_one)
  · simpa only [ContinuousMap.coe_mk, Icc.coe_one, Function.comp_apply,
      variationOnFromTo.eq_of_le _ _ zero_le_one, inter_self, hγ.target, mul_one] using
      hfactor (right_mem_Icc.2 zero_le_one)

/-- In a length space, a point at distance at most `s + t` from `p` lies within `t + ε` of a
point at distance at most `s` from `p`. -/
theorem IsLengthSpace.exists_dist_le_of_dist_le_add [IsLengthSpace X] {p x : X} {s t ε : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hε : 0 < ε) (hx : dist p x ≤ s + t) :
    ∃ y, dist p y ≤ s ∧ dist y x ≤ t + ε := by
  by_cases hxs : dist p x ≤ s
  · exact ⟨x, hxs, by rw [dist_self]; positivity⟩
  rw [not_le] at hxs
  set r := dist p x + ε with _hr_def
  have hr : 0 < r := by positivity
  obtain ⟨f, hf0, hf1, hf⟩ := IsLengthSpace.exists_lipschitz_path (x := p) (y := x)
    (r := r) (by linarith)
  have hsr : s / r ≤ 1 := (div_le_one hr).2 (by linarith)
  let τ : unitInterval := ⟨s / r, div_nonneg hs hr.le, hsr⟩
  have hK : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal _ hr.le
  refine ⟨f τ, ?_, ?_⟩
  · have h := hf.dist_le_mul 0 τ
    rw [hf0, hK, Subtype.dist_eq, Real.dist_eq] at h
    have hτ : |((0 : unitInterval) : ℝ) - (τ : ℝ)| = s / r := by
      simp only [Icc.coe_zero, zero_sub, abs_neg, τ]
      exact abs_of_nonneg (div_nonneg hs hr.le)
    rw [hτ, mul_div_cancel₀ _ hr.ne'] at h
    exact h
  · have h := hf.dist_le_mul τ 1
    rw [hf1, hK, Subtype.dist_eq, Real.dist_eq] at h
    have hτ : |(τ : ℝ) - ((1 : unitInterval) : ℝ)| = 1 - s / r := by
      simp only [Icc.coe_one, τ]
      rw [abs_of_nonpos (by linarith)]
      ring
    rw [hτ, mul_sub, mul_one, mul_div_cancel₀ _ hr.ne'] at h
    linarith

end TauCeti
