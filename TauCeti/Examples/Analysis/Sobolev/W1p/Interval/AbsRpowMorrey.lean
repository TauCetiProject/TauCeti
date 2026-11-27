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

/-!
# Morrey's embedding on `(-1, 1)` for the cusps `|x|^{3/4}` and `|x|^{1/4}`

In dimension one Morrey's embedding for `p = 2` says that the continuous representative of
`u ∈ W^{1,2}(a, b)` is Hölder continuous of exponent `1 - 1/2 = 1/2`, with constant `‖u'‖_{L²}`
(`TauCeti.W1p.holderOnWith_of_value_ae_eq`). On `(-1, 1)` the two cusps of this file show
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
open scoped ENNReal NNReal

namespace TauCeti.Examples.AbsRpowMorrey

open W1p

/-- The Hölder exponent `1 - 1/p` of Morrey's embedding at `p = 2`. -/
private theorem holderExponent_two : (1 - 1 / (2 : ℝ≥0∞).toReal).toNNReal = 1 / 2 := by
  rw [← NNReal.coe_inj, Real.coe_toNNReal _ (by norm_num)]
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
  holderExponent_two ▸ holderOnWith_of_value_ae_eq (by norm_num)
    (continuous_abs.rpow_const fun _ => Or.inr (by norm_num)).continuousOn hu

/-- `|x|^{1/4}` does not lie in `W^{1,2}(-1, 1)`: otherwise Morrey's embedding would make it
`1/2`-Hölder on `(-1, 1)`, which it is not. -/
theorem not_exists_value_ae_eq_abs_rpow_one_quarter :
    ¬ ∃ u : W1p volume ⟨Ioo (-1 : ℝ) 1, isOpen_Ioo⟩ 2,
      value u =ᵐ[volume.restrict (Ioo (-1) 1)] fun x => |x| ^ (1 / 4 : ℝ) := by
  rintro ⟨u, hu⟩
  have h := (holderOnWith_of_value_ae_eq (by norm_num)
    (continuous_abs.rpow_const fun _ => Or.inr (by norm_num)).continuousOn hu).mono
    Ioo_subset_Icc_self
  rw [holderExponent_two] at h
  exact not_holderOnWith_abs_rpow_Ioo (α := 1 / 4) (β := 1 / 2) (by norm_num) (by norm_num)
    (by simpa using h)

end TauCeti.Examples.AbsRpowMorrey
