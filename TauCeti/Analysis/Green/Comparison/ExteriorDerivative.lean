/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Comparison.Area.Basic
public import TauCeti.Analysis.Green.DifferentialForm
import TauCeti.Analysis.Green.FlatDifferentialForm

/-!
# The planar exterior derivative as an actual area form

The exterior derivative of the circulation form is the curl times the canonical manifold area
form, by transport from the flat exterior derivative in the canonical chart.
-/

public section

noncomputable section

open Set
open scoped Manifold

namespace TauCeti.Green

attribute [local instance] Complex.finrank_real_complex_fact

/-- The actual planar manifold exterior derivative is curl times the normalized area form. -/
theorem _root_.DifferentiableAt.mextDeriv_manifoldOneForm_eq_smul_area {P Q : ℂ → ℝ} {z : ℂ}
    (hP : DifferentiableAt ℝ P z) (hQ : DifferentiableAt ℝ Q z) :
    mextDeriv (manifoldOneForm P Q) z = curl P Q z • manifoldAreaForm z := by
  have hω := differentiableAt_manifoldOneForm_inChartAt z hP hQ
  rw [manifoldOneForm_inChartAt] at hω
  rw [mextDeriv_def, ← RoughForm.inChartAt_extChartAt_self manifoldAreaForm z,
    manifoldAreaForm_inChartAt, extChartAt_model_space_eq_id]
  simp only [modelWithCornersSelf_coe, range_id, PartialEquiv.refl_coe, id_eq,
    extDerivWithin_univ, manifoldOneForm_inChartAt]
  exact hω.extDeriv_oneForm_eq_smul_volumeFormL

end TauCeti.Green
