/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import TauCeti.Analysis.InnerProductSpace.OrthogonalLine.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Hausdorff dimension of Lipschitz graphs over orthogonal hyperplanes

In a finite-dimensional real inner product space `E`, the orthogonal complement `(ℝ ∙ v)ᗮ` of a
unit vector `v` has dimension `finrank ℝ E - 1`. Since the graph parametrization
`w ↦ (w : E) + g w • v` of a globally Lipschitz function `g : (ℝ ∙ v)ᗮ → ℝ` is Lipschitz
(`TauCeti.lipschitzWith_coe_add_smul`), its range has Hausdorff codimension at least `1`:
`dimH (range (fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v)) + 1 ≤ finrank ℝ E`, and hence
`dimH ≤ finrank ℝ E - 1`. Because such a graph is also closed
(`TauCeti.isClosed_range_add_smul_of_lipschitzWith`), any measure on `E` (with open sets
measurable) that vanishes on measurable sets satisfying `dimH A + 1 ≤ finrank ℝ E` vanishes on
every globally Lipschitz graph over `(ℝ ∙ v)ᗮ`.

## Main statements

* `TauCeti.dimH_range_add_smul_add_one_le` and `TauCeti.dimH_range_add_smul_le` — Hausdorff
  codimension and dimension bounds for a globally Lipschitz graph over `(ℝ ∙ v)ᗮ` (`‖v‖ = 1`);
* `TauCeti.measure_range_add_smul_eq_zero_of_dimH_add_one_le` — any measure vanishing on measurable
  sets with `dimH A + 1 ≤ finrank ℝ E` gives mass `0` to every globally Lipschitz graph over
  `(ℝ ∙ v)ᗮ`.
-/

public section

open MeasureTheory Module Set
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- On a finite-dimensional real inner product space `E`, a Lipschitz graph over `(ℝ ∙ v)ᗮ`
(`‖v‖ = 1`) has Hausdorff dimension satisfying `dimH + 1 ≤ finrank ℝ E`. -/
theorem dimH_range_add_smul_add_one_le {v : E} (hv : ‖v‖ = 1)
    {K : ℝ≥0} {g : (ℝ ∙ v)ᗮ → ℝ} (hg : LipschitzWith K g) :
    dimH (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) + 1 ≤ (finrank ℝ E : ℝ≥0∞) := by
  have hv0 : v ≠ 0 := fun h => by simp [h] at hv
  have hfin : finrank ℝ (ℝ ∙ v)ᗮ + 1 = finrank ℝ E := by
    have h := Submodule.finrank_add_finrank_orthogonal (𝕜 := ℝ) (E := E) (ℝ ∙ v)
    rwa [finrank_span_singleton hv0, add_comm] at h
  calc
    dimH (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) + 1
      ≤ dimH (univ : Set (ℝ ∙ v)ᗮ) + 1 :=
        add_le_add_left (lipschitzWith_coe_add_smul hv hg).dimH_range_le 1
    _ = (finrank ℝ (ℝ ∙ v)ᗮ : ℝ≥0∞) + 1 := by rw [Real.dimH_univ_eq_finrank]
    _ = (finrank ℝ E : ℝ≥0∞) := by exact_mod_cast hfin

/-- On a finite-dimensional real inner product space `E`, a Lipschitz graph over `(ℝ ∙ v)ᗮ`
(`‖v‖ = 1`) has Hausdorff dimension at most `finrank ℝ E - 1`. -/
theorem dimH_range_add_smul_le {v : E} (hv : ‖v‖ = 1)
    {K : ℝ≥0} {g : (ℝ ∙ v)ᗮ → ℝ} (hg : LipschitzWith K g) :
    dimH (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) ≤ ((finrank ℝ E - 1 : ℕ) : ℝ≥0∞) := by
  simpa only [ENNReal.natCast_sub, Nat.cast_one] using
    ENNReal.le_sub_of_add_le_right ENNReal.one_ne_top (dimH_range_add_smul_add_one_le hv hg)

/-- On a finite-dimensional real inner product space with open sets measurable, a measure that
vanishes on measurable sets `A` satisfying `dimH A + 1 ≤ finrank ℝ E` vanishes on every globally
Lipschitz graph over the orthogonal complement of a unit vector. -/
theorem measure_range_add_smul_eq_zero_of_dimH_add_one_le [MeasurableSpace E]
    [OpensMeasurableSpace E] {μ : Measure E}
    (hμ : ∀ A, MeasurableSet A → dimH A + 1 ≤ (finrank ℝ E : ℝ≥0∞) → μ A = 0)
    {v : E} (hv : ‖v‖ = 1) {K : ℝ≥0} {g : (ℝ ∙ v)ᗮ → ℝ} (hg : LipschitzWith K g) :
    μ (range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) = 0 :=
  hμ _ (isClosed_range_add_smul_of_lipschitzWith hv hg).measurableSet
    (dimH_range_add_smul_add_one_le hv hg)

end TauCeti
