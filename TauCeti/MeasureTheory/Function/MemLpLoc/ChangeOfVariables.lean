/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Jacobian
public import TauCeti.MeasureTheory.Function.MemLpLoc

/-!
# Local `Lᵖ` classes under `C¹` changes of variables

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`, and let `Φ`
be `C¹` on an open set `Ω ⊆ E`, with invertible derivative at every point of a set `U ⊆ Ω` and
mapping `U` into `V`. Precomposition with `Φ` maps the local `Lᵖ` class of `V` into that of `U`
(`TauCeti.MemLpLoc.comp_contDiffOn_diffeo`). The same holds for the transformed derivative field
`x ↦ D (Φ x) ∘ DΦ(x)` of a locally `Lᵖ` operator field `D`
(`TauCeti.MemLpLoc.comp_fderiv_contDiffOn_diffeo`). These are the two `Lᵖ` conditions in the
change of variables for local Sobolev classes, where `D` is a weak derivative of `u`.

No bound on `DΦ` or on its inverse is assumed, and `Φ` need not be injective. On each compact
subset of `U` the derivative is bounded and the Jacobian is bounded below, and `Φ` is injective
near each point by the inverse function theorem (`MeasureTheory.MemLp.comp_restrict_of_isCompact`).
So `x ↦ eˣ` from `ℝ` to `(0, ∞)`, whose derivative is unbounded, and the covering `z ↦ z²` of
`ℂ ∖ {0}`, which identifies `z` and `-z`, are both admissible. The sets `U` and `V` need not be
open: compact subsets of `U` may reach its boundary, as for half-discs in the plane.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] {p : ℝ≥0∞} {Φ : E → E} {Ω U V : Set E}

/-- **Change of variables in local `Lᵖ` classes.** If `Φ` is `C¹` on an open set `Ω ⊇ U`, with
invertible derivative on `U`, and maps `U` into `V`, then precomposition with `Φ` maps
`MemLpLoc p V` into `MemLpLoc p U`. Neither injectivity of `Φ` nor a bound on its derivative or
on the inverse of its derivative is needed. -/
theorem MemLpLoc.comp_contDiffOn_diffeo {u : E → F} (hu : MemLpLoc p V u μ) (hΩ : IsOpen Ω)
    (hΦ : ContDiffOn ℝ 1 Φ Ω) (hdet : ∀ x ∈ U, (fderiv ℝ Φ x).det ≠ 0) (hUΩ : U ⊆ Ω)
    (hmaps : MapsTo Φ U V) : MemLpLoc p U (fun x => u (Φ x)) μ :=
  memLpLoc_iff.2 fun _ hKU hK => MemLp.comp_restrict_of_isCompact
    (memLpLoc_iff.1 hu _ ((image_mono hKU).trans hmaps.image_subset)
      (hK.image_of_continuousOn (hΦ.continuousOn.mono (hKU.trans hUΩ))))
    hΩ hΦ (fun x hx => hdet x (hKU hx)) hK (hKU.trans hUΩ)

/-- The transformed derivative `x ↦ D (Φ x) ∘ DΦ(x)` of a locally `Lᵖ` operator field `D` is
locally `Lᵖ`, under the hypotheses of `TauCeti.MemLpLoc.comp_contDiffOn_diffeo`. -/
theorem MemLpLoc.comp_fderiv_contDiffOn_diffeo [NormedSpace ℝ F] {D : E → E →L[ℝ] F}
    (hD : MemLpLoc p V D μ) (hΩ : IsOpen Ω) (hΦ : ContDiffOn ℝ 1 Φ Ω)
    (hdet : ∀ x ∈ U, (fderiv ℝ Φ x).det ≠ 0) (hUΩ : U ⊆ Ω) (hmaps : MapsTo Φ U V) :
    MemLpLoc p U (fun x => (D (Φ x)).comp (fderiv ℝ Φ x)) μ :=
  memLpLoc_iff.2 fun _ hKU hK => MemLp.comp_fderiv_restrict_of_isCompact
    (memLpLoc_iff.1 hD _ ((image_mono hKU).trans hmaps.image_subset)
      (hK.image_of_continuousOn (hΦ.continuousOn.mono (hKU.trans hUΩ))))
    hΩ hΦ (fun x hx => hdet x (hKU hx)) hK (hKU.trans hUΩ)

end TauCeti
