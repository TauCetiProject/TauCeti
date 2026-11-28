/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import TauCeti.MeasureTheory.Function.StronglyMeasurable.OperatorField
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-!
# The `eLpNorm` of an operator field through measurable unit vector fields

Over a densely normed field, the extended seminorm `eLpNorm G r μ` of an almost everywhere
strongly measurable operator field `G : S → E →L[𝕜] F` is the supremum of the extended
seminorms `eLpNorm (fun s ↦ G s (x s)) r μ` over strongly measurable, countably valued fields
`x` of vectors of norm at most one
(`MeasureTheory.AEStronglyMeasurable.eLpNorm_le_of_forall_eLpNorm_apply_le`).

Taking `F` to be the scalar field, this tests a strongly measurable family of functionals
against measurable unit vector fields. Through the isometric embedding of a normed space into
its bidual, it also tests a vector-valued function against measurable fields of functionals.
These are the pointwise test functions used to compute the norm of the integral pairing between
Bochner spaces `Lᵖ(μ; X)` and `L^q(μ; X⋆)`.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Proposition 1.3.1.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {S 𝕜 E F : Type*} [MeasurableSpace S] {μ : Measure S}
  [DenselyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Norming an operator field by measurable unit vector fields.** If the extended seminorm
`eLpNorm (fun s ↦ G s (x s)) r μ` is at most `C` for every strongly measurable, countably valued
`x : S → E` with `‖x s‖ ≤ 1`, then `eLpNorm G r μ ≤ C` for the almost everywhere strongly
measurable operator field `G`. -/
theorem AEStronglyMeasurable.eLpNorm_le_of_forall_eLpNorm_apply_le {G : S → E →L[𝕜] F}
    (hG : AEStronglyMeasurable G μ) {r C : ℝ≥0∞}
    (hC : ∀ x : S → E, StronglyMeasurable x → (range x).Countable → (∀ s, ‖x s‖ ≤ 1) →
      eLpNorm (fun s ↦ G s (x s)) r μ ≤ C) :
    eLpNorm G r μ ≤ C := by
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha ↦ ?_
  obtain ⟨x, hx, hxc, hx1, hGx⟩ := hG.exists_stronglyMeasurable_norming
    (ENNReal.toReal_lt_of_lt_ofReal (by simpa using ha))
  calc a * eLpNorm G r μ = eLpNorm (fun s ↦ a * ‖G s‖ₑ) r μ := by
        rw [eLpNorm_const_mul_ennreal hG.eNorm.aestronglyMeasurable, eLpNorm_eNorm G hG]
    _ ≤ eLpNorm (fun s ↦ G s (x s)) r μ := eLpNorm_mono_eNorm_ae
        (hG.eNorm.const_mul a).aestronglyMeasurable <| hGx.mono fun s hs ↦ by
        simpa only [eNorm_eq_self, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ofReal_norm,
          ENNReal.ofReal_toReal ha.ne_top] using ENNReal.ofReal_le_ofReal hs
    _ ≤ C := hC x hx hxc hx1

end MeasureTheory
