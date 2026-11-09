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
-/

public section

open Set
open scoped ENNReal unitInterval

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
    ⟨mul_nonneg hL t.2.1, mul_le_of_le_one_right hL t.2.2⟩
  have hLip : LipschitzWith r.toNNReal (fun t : I ↦ g (L * (t : ℝ))) := by
    refine LipschitzWith.of_dist_le_mul fun s t ↦ ?_
    have hd := hg.dist_le_mul _ (harg s) _ (harg t)
    rw [NNReal.coe_one, one_mul, Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg hL] at hd
    rw [Real.coe_toNNReal r (dist_nonneg.trans_lt hr).le]
    exact hd.trans (mul_le_mul_of_nonneg_right hLr (abs_nonneg _))
  refine ⟨⟨fun t ↦ g (L * (t : ℝ)), hLip.continuous⟩, ?_, ?_, hLip⟩
  · change g (L * 0) = x
    simpa only [Function.comp_apply, variationOnFromTo.self, hγ.source, mul_zero] using
      hfactor (left_mem_Icc.2 zero_le_one)
  · change g (L * 1) = y
    simpa only [Function.comp_apply, variationOnFromTo.eq_of_le _ _ zero_le_one, inter_self,
      hγ.target, mul_one] using hfactor (right_mem_Icc.2 zero_le_one)

end TauCeti
