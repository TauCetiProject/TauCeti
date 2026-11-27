/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.Representative
import TauCeti.Analysis.Holder.Examples
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.Analysis.Sobolev.W1p.NormRpow
import TauCeti.Topology.MetricSpace.Holder

/-!
# Morrey's embedding on `(-1, 1)` for the cusps `|x|^{3/4}` and `|x|^{1/4}`

In dimension one Morrey's embedding for `p = 2` says that the continuous representative of
`u ∈ W^{1,2}(a, b)` is Hölder continuous of exponent `1 - 1/2 = 1/2`, with constant `‖u'‖_{L²}`
(`TauCeti.W1p.abs_intervalRepresentativeL_sub_le`). On `(-1, 1)` the two cusps of this file show
both sides of the statement.

* `|x|^{3/4}` has derivative `(3/4) |x|^{-1/4}`, whose square `(9/16) |x|^{-1/2}` is integrable,
  so it lies in `W^{1,2}(-1, 1)`
  (`TauCeti.Examples.AbsRpowMorrey.exists_value_ae_eq_abs_rpow_three_quarters`), and Morrey makes it
  `1/2`-Hölder on `[-1, 1]` with constant `‖u'‖`
  (`TauCeti.Examples.AbsRpowMorrey.holderOnWith_abs_rpow_three_quarters`). This is consistent with
  its actual regularity: it is `3/4`-Hölder (`TauCeti.holderOnWith_abs_rpow_Ioo_iff`).
* `|x|^{1/4}` is `1/4`-Hölder but not `1/2`-Hölder (`TauCeti.not_holderOnWith_abs_rpow_Ioo`), and
  consistently its derivative squared, `(1/16) |x|^{-3/2}`, is not integrable: it does not lie in
  `W^{1,2}(-1, 1)` (`TauCeti.Examples.AbsRpowMorrey.not_exists_value_ae_eq_abs_rpow_one_quarter`),
  so Morrey makes no claim about it. The proof reads this off Morrey's embedding itself: a class
  of `W^{1,2}(-1, 1)` with value `|x|^{1/4}` would make `|x|^{1/4}` `1/2`-Hölder.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 8.8 and Remark 8.10.
-/

public section

open MeasureTheory Set
open scoped NNReal

namespace TauCeti.Examples.AbsRpowMorrey

open W1p

/-- **Morrey's embedding on `(-1, 1)` for `p = 2`.** If the value of `u ∈ W^{1,2}(-1, 1)` agrees
almost everywhere with a function `f` continuous on `[-1, 1]`, then `f` is `1/2`-Hölder on `[-1, 1]`
with constant `‖u'‖_{L²}`. -/
private theorem holderOnWith_of_value_ae_eq {u : W1p volume ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ 2}
    {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1))
    (hu : value u =ᵐ[volume.restrict (Ioo (-1) 1)] f) :
    HolderOnWith ‖gradient u‖₊ (1 / 2) f (Icc (-1) 1) := by
  have hab : (-1 : ℝ) < 1 := by norm_num
  refine HolderOnWith.of_dist_le fun x hx y hy => ?_
  have h := abs_intervalRepresentativeL_sub_le hab u ⟨y, hy⟩ ⟨x, hx⟩
  rw [intervalRepresentativeL_apply_of_value_ae_eq hab hf hu,
    intervalRepresentativeL_apply_of_value_ae_eq hab hf hu] at h
  rw [Real.dist_eq, Real.dist_eq, coe_nnNorm, mul_comm]
  convert h using 3
  norm_num

/-- `|x|^{3/4}` lies in `W^{1,2}(-1, 1)`: its derivative `(3/4) |x|^{-1/4}` is square integrable
near `0`. -/
theorem exists_value_ae_eq_abs_rpow_three_quarters :
    ∃ u : W1p volume ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ 2,
      value u =ᵐ[volume.restrict (Ioo (-1) 1)] fun x => |x| ^ (3 / 4 : ℝ) := by
  simpa only [Real.norm_eq_abs, TopologicalSpace.Opens.coe_mk] using
    (exists_w1p_value_ae_eq_norm_rpow_iff (μ := volume) (Ω := ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩)
      (p := 2) (s := 3 / 4) ENNReal.ofNat_ne_top (Metric.isBounded_Ioo _ _)
      (Ioo_mem_nhds (by norm_num) (by norm_num)) (by norm_num)).2 (by norm_num)

/-- **Morrey's embedding for `|x|^{3/4}`.** If `u ∈ W^{1,2}(-1, 1)` has value `|x|^{3/4}`, then
`|x|^{3/4}` is `1/2`-Hölder on `[-1, 1]` with constant `‖u'‖_{L²}`. -/
theorem holderOnWith_abs_rpow_three_quarters {u : W1p volume ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ 2}
    (hu : value u =ᵐ[volume.restrict (Ioo (-1) 1)] fun x => |x| ^ (3 / 4 : ℝ)) :
    HolderOnWith ‖gradient u‖₊ (1 / 2) (fun x : ℝ => |x| ^ (3 / 4 : ℝ)) (Icc (-1) 1) :=
  holderOnWith_of_value_ae_eq
    (continuous_abs.rpow_const fun _ => Or.inr (by norm_num)).continuousOn hu

/-- `|x|^{1/4}` does not lie in `W^{1,2}(-1, 1)`: otherwise Morrey's embedding would make it
`1/2`-Hölder on `(-1, 1)`, which it is not. -/
theorem not_exists_value_ae_eq_abs_rpow_one_quarter :
    ¬ ∃ u : W1p volume ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ 2,
      value u =ᵐ[volume.restrict (Ioo (-1) 1)] fun x => |x| ^ (1 / 4 : ℝ) := by
  rintro ⟨u, hu⟩
  have h := (holderOnWith_of_value_ae_eq
    (continuous_abs.rpow_const fun _ => Or.inr (by norm_num)).continuousOn hu).mono
    Ioo_subset_Icc_self
  exact not_holderOnWith_abs_rpow_Ioo (α := 1 / 4) (β := 1 / 2) (by norm_num) (by norm_num)
    (by simpa using h)

end TauCeti.Examples.AbsRpowMorrey
