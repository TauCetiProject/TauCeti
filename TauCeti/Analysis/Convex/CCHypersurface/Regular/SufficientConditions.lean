/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import TauCeti.Analysis.Convex.CCHypersurface.Regular.Basic
import TauCeti.Analysis.Convex.CCHypersurface.Measure
import TauCeti.Analysis.InnerProductSpace.OrthogonalLine.HausdorffDimension

/-!
# Sufficient conditions for `c - c`-regular measures

In finite dimensions, a measure is `c - c`-regular (`TauCeti.IsCCRegular`) whenever it vanishes on
all measurable sets of Hausdorff codimension at least `1` (`TauCeti.isCCRegular_of_dimH_add_one_le`,
and `TauCeti.isCCRegular_of_dimH_le`), or whenever it is an additive Haar measure or absolutely
continuous with respect to one (`TauCeti.isCCRegular_of_isAddHaarMeasure`,
`TauCeti.isCCRegular_of_absolutelyContinuous`).

## Main statements

* `TauCeti.isCCRegular_of_dimH_add_one_le` — vanishing on measurable sets with `dimH A + 1 ≤ dim E`
  implies `IsCCRegular`;
* `TauCeti.isCCRegular_of_dimH_le` — vanishing on measurable sets with `dimH A ≤ dim E - 1` implies
  `IsCCRegular`;
* `TauCeti.isCCRegular_of_isAddHaarMeasure` — every additive Haar measure is `c - c`-regular;
* `TauCeti.isCCRegular_of_absolutelyContinuous` — every measure absolutely continuous with respect
  to an additive Haar measure is `c - c`-regular.

## References

* L. Zajíček, *On the differentiation of convex functions in finite and infinite dimensional
  spaces*, Czechoslovak Math. J. 29 (1979), 340–348.
* W. Gangbo and R. J. McCann, *The geometry of optimal transportation*, Acta Math. 177 (1996),
  113–161.
* L. Ambrosio and N. Gigli, *A user's guide to optimal transport*, LNM 2062, Springer, 2013,
  Definition 1.25.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

section SufficientConditions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E]

/-- **Measures vanishing on sets of Hausdorff codimension at least `1` are `c - c`-regular.** If
`μ` vanishes on every measurable set `A` with `dimH A + 1 ≤ finrank ℝ E`, then `μ` is
`c - c`-regular. -/
theorem isCCRegular_of_dimH_add_one_le [OpensMeasurableSpace E] {μ : Measure E}
    (h : ∀ A : Set E, MeasurableSet A →
      dimH A + 1 ≤ (Module.finrank ℝ E : ℝ≥0∞) → μ A = 0) : IsCCRegular μ :=
  isCCRegular_of_null_lipschitz_graphs fun _ hv _ _ hg =>
    measure_range_add_smul_eq_zero_of_dimH_add_one_le h hv hg

/-- **Measures vanishing on small-Hausdorff-dimension sets are `c - c`-regular.** If `μ` vanishes
on every measurable set `A` with `dimH A ≤ finrank ℝ E - 1`, then `μ` is `c - c`-regular. -/
theorem isCCRegular_of_dimH_le [OpensMeasurableSpace E] {μ : Measure E}
    (h : ∀ A : Set E, MeasurableSet A →
      dimH A ≤ ((Module.finrank ℝ E - 1 : ℕ) : ℝ≥0∞) → μ A = 0) : IsCCRegular μ :=
  isCCRegular_of_dimH_add_one_le fun _ hA hdim =>
    h _ hA (by
      simpa only [ENNReal.natCast_sub, Nat.cast_one] using
        ENNReal.le_sub_of_add_le_right ENNReal.one_ne_top hdim)

/-- **Every additive Haar measure is `c - c`-regular.** -/
theorem isCCRegular_of_isAddHaarMeasure [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] :
    IsCCRegular μ := (isCCRegular_def μ).2 fun _ hs => hs.addHaar_eq_zero μ

/-- **Every measure absolutely continuous with respect to an additive Haar measure is
`c - c`-regular.** -/
theorem isCCRegular_of_absolutelyContinuous [BorelSpace E] {μ ρ : Measure E} [ρ.IsAddHaarMeasure]
    (h : μ ≪ ρ) : IsCCRegular μ := (isCCRegular_of_isAddHaarMeasure ρ).mono_ac h

end SufficientConditions

end TauCeti
