/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import TauCeti.MeasureTheory.Function.StronglyMeasurable.ScalarTests

/-!
# Weak and norm-Borel structures on separable normed spaces

On a separable real or complex normed space, the weak and norm topologies generate the
same Borel σ-algebra. Thus passage to the weak topology preserves measurability in both
directions, even though the inverse of `toWeakSpace` need not be continuous.

`TauCeti.comap_borel_toWeakSpace` states the equality on the original space, and
`TauCeti.toWeakSpaceMeasurableEquiv` bundles it as a measurable equivalence. The Borel
structures remain explicit; this file installs no measurable-space instances on weak spaces.
Completeness is not required.

The comparison uses the scalar-test Borel criterion and Mathlib's continuity of weak
evaluations, rather than identifying the Borel structure of an uncountable product with
its product σ-algebra.

## References

* T. Hytönen, J. van Neerven, M. Veraar, L. Weis, *Analysis in Banach Spaces*, Volume I,
  §1.1.a, Proposition 1.1.1 and Corollary 1.1.2.
-/

public section

open MeasureTheory MeasurableSpace TopologicalSpace

namespace TauCeti

variable {𝕜 X : Type*} [RCLike 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [SeparableSpace X]

/-- On a separable normed space, pulling back the weak Borel σ-algebra gives the
norm-Borel σ-algebra. No completeness assumption is needed. -/
theorem comap_borel_toWeakSpace :
    (borel (WeakSpace 𝕜 X)).comap (toWeakSpace 𝕜 X) = borel X := by
  refine le_antisymm (toWeakSpaceCLM 𝕜 X).continuous.borel_measurable.comap_le ?_
  rw [← evalMeasurableSpace_univ_eq_borel (𝕜 := 𝕜) (X := X)]
  refine evalMeasurableSpace_le_iff.2 fun φ _ ↦ ?_
  borelize (WeakSpace 𝕜 X)
  have hφ : Continuous fun y : WeakSpace 𝕜 X ↦ φ ((toWeakSpace 𝕜 X).symm y) :=
    WeakBilin.eval_continuous (topDualPairing 𝕜 X).flip φ
  simpa only [Function.comp_def, LinearEquiv.symm_apply_apply] using
    hφ.measurable.comp (comap_measurable (toWeakSpace 𝕜 X))

variable (𝕜 X) [MeasurableSpace X] [BorelSpace X]
  [MeasurableSpace (WeakSpace 𝕜 X)] [BorelSpace (WeakSpace 𝕜 X)]

/-- The canonical measurable equivalence between a separable normed space and its weak
space, with their Borel measurable structures. -/
noncomputable def toWeakSpaceMeasurableEquiv : X ≃ᵐ WeakSpace 𝕜 X where
  toEquiv := (toWeakSpace 𝕜 X).toEquiv
  measurable_toFun := (toWeakSpaceCLM 𝕜 X).continuous.measurable
  measurable_invFun := by
    rw [measurable_iff_comap_le, BorelSpace.measurable_eq (α := X),
      BorelSpace.measurable_eq (α := WeakSpace 𝕜 X),
      ← comap_borel_toWeakSpace (𝕜 := 𝕜) (X := X), MeasurableSpace.comap_comp]
    simp only [← LinearEquiv.coe_toEquiv, Function.comp_def, Equiv.apply_symm_apply]
    exact measurable_id.comap_le

@[simp]
theorem coe_toWeakSpaceMeasurableEquiv :
    ⇑(toWeakSpaceMeasurableEquiv 𝕜 X) = toWeakSpace 𝕜 X := (rfl)

@[simp]
theorem coe_toWeakSpaceMeasurableEquiv_symm :
    ⇑(toWeakSpaceMeasurableEquiv 𝕜 X).symm = (toWeakSpace 𝕜 X).symm := (rfl)

end TauCeti
