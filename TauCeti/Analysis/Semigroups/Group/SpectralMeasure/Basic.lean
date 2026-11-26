/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import TauCeti.Analysis.PositiveDefinite.AddGroup
public import TauCeti.Analysis.Semigroups.Group.Unitary
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import TauCeti.Analysis.Bochner.CharFun.Bochner

/-!
# Spectral measure of a unitary C₀-group

For a unitary C₀-group `U` on a complex inner product space `H` and any vector `v : H`, the
correlation function `t ↦ ⟪v, U t v⟫_ℂ` is continuous and positive definite
(`IsUnitary.isPositiveDefiniteSub_inner`), so Bochner's theorem supplies a unique finite Borel
spectral measure `σ` on `ℝ` with `⟪v, U t v⟫_ℂ = charFun σ t`
(`IsUnitary.existsUnique_spectralMeasure`).

For the identification of `σ.real {ω}` with the squared norm of the eigenprojection onto
`U.eigenspace hU.isComplexLinear ω`, see
`TauCeti.Analysis.Semigroups.Group.SpectralMeasure.Atoms`.

## Main results

* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.isPositiveDefiniteSub_inner`: positive
  definiteness of `t ↦ ⟪v, U t v⟫_ℂ`.
* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.existsUnique_spectralMeasure`: existence and
  uniqueness of the Bochner spectral measure `σ` representing `t ↦ ⟪v, U t v⟫_ℂ`.
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace

namespace TauCeti.Semigroups.StronglyContinuousGroup

namespace IsUnitary

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {U : StronglyContinuousGroup H}

/-- The correlation function `t ↦ ⟪v, U t v⟫_ℂ` of a unitary C₀-group is positive definite. -/
theorem isPositiveDefiniteSub_inner (hU : U.IsUnitary) (v : H) :
    TauCeti.IsPositiveDefiniteSub fun t : ℝ ↦ ⟪v, U t v⟫_ℂ := by
  refine TauCeti.IsPositiveDefiniteSub.of_posSemidef ?_
  have hgram : (fun a b : ℝ ↦ ⟪v, U (a - b) v⟫_ℂ) =
      Matrix.gram ℂ (fun t : ℝ ↦ U (-t) v) := by
    ext a b
    rw [Matrix.gram_apply]
    calc ⟪v, U (a - b) v⟫_ℂ
        = ⟪U (-a) v, U (-a) (U (a - b) v)⟫_ℂ := (hU.inner_map_map (-a) _ _).symm
      _ = ⟪U (-a) v, U (-b) v⟫_ℂ := by
          rw [← U.map_add_apply, ← add_sub_assoc, neg_add_cancel, zero_sub]
  rw [hgram]
  exact Matrix.posSemidef_gram ℂ (fun t : ℝ ↦ U (-t) v)

/-- **Spectral measure of a unitary C₀-group.** For every vector `v` in a complex inner product
space and every unitary C₀-group `U`, there is a unique finite Borel measure `σ` on `ℝ` whose
characteristic function is `t ↦ ⟪v, U t v⟫_ℂ`. -/
theorem existsUnique_spectralMeasure (hU : U.IsUnitary) (v : H) :
    ∃! σ : Measure ℝ, IsFiniteMeasure σ ∧ ∀ t : ℝ, ⟪v, U t v⟫_ℂ = charFun σ t := by
  have hboch := (TauCeti.bochner_charFun fun t : ℝ ↦ ⟪v, U t v⟫_ℂ).mp
    ⟨continuous_const.inner (U.continuous_orbit v), hU.isPositiveDefiniteSub_inner v⟩
  simpa only [funext_iff, eq_comm (a := ⟪v, U _ v⟫_ℂ)] using hboch

end IsUnitary

end TauCeti.Semigroups.StronglyContinuousGroup

end
