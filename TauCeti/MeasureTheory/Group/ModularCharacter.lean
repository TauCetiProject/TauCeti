/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.ModularCharacter
public import TauCeti.MeasureTheory.Group.Integral

/-!
# Continuity of the modular character

The modular character of a locally compact group is continuous. Its real value can be
computed as the ratio of the integrals of a compactly supported continuous test function
and its right translate. This supplies the continuous weight used in convolution involutions.

We use Mathlib's convention: right translation of the argument multiplies an integral by
`Measure.modularCharacter g`. This is the inverse of the modular function in Dana Williams,
*Crossed Products of C*-Algebras*, Lemma 1.61.
-/

public section

open MeasureTheory
open scoped NNReal

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- The bundled modular character evaluates to the modular character function. -/
theorem modularCharacter_apply (g : G) :
    Measure.modularCharacter g = Measure.modularCharacterFun g := rfl

/-- A nonzero test integral computes the modular character by right translation.
No regularity assumption on the Haar measure is needed. -/
theorem modularCharacter_eq_integral_div [MeasurableSpace G] [BorelSpace G]
    {μ : Measure G} [μ.IsHaarMeasure] {f : G → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (hfi : ∫ x, f x ∂μ ≠ 0) (g : G) :
    (Measure.modularCharacter g : ℝ) = (∫ x, f (x * g) ∂μ) / ∫ x, f x ∂μ := by
  rw [modularCharacter_apply, Measure.modularCharacterFun_eq_haarScalarFactor μ g,
    Measure.haarScalarFactor_eq_integral_div _ _ hf hfc hfi,
    integral_map (by fun_prop) hf.aestronglyMeasurable]

/-- The modular character is continuous, without countability or separation assumptions. -/
@[fun_prop]
theorem continuous_modularCharacter : Continuous (Measure.modularCharacter : G → ℝ≥0) := by
  borelize G
  obtain ⟨f, hfc, hfn, hf1⟩ := exists_continuous_nonneg_pos (1 : G)
  have hfi : ∫ x, f x ∂(Measure.haar : Measure G) ≠ 0 :=
    (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hfn hf1).ne'
  have hc : Continuous (fun g : G => ∫ x, f (x * g) ∂(Measure.haar : Measure G)) := by
    have h := continuous_integral_apply_inv_mul (μ := (Measure.haar : Measure G).inv)
      f.continuous hfc
    simpa only [integral_inv_measure, inv_inv] using h
  exact continuous_induced_rng.mpr <| (hc.div_const _).congr fun g =>
    (modularCharacter_eq_integral_div f.continuous hfc hfi g).symm

end TauCeti
