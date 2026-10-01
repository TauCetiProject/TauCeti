/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import TauCeti.Analysis.Complex.RiemannSurface.LocalMultiplicity

/-!
# Local multiplicities of complex-valued functions on the upper half-plane

The upper half-plane is an open subset of `ℂ`, and its complex-manifold structure has the single
chart given by the inclusion, with inverse `UpperHalfPlane.ofComplex`
(`TauCeti.UpperHalfPlane.chartAt_eq_ofComplex_symm`). So the local multiplicity of a function
`f : ℍ → ℂ` at `z` is the order of vanishing of `f ∘ ofComplex - f z` at `z`
(`TauCeti.UpperHalfPlane.localMultiplicity_eq_analyticOrderNatAt_comp_ofComplex_sub`). This is the
form in which orders of modular forms and modular functions are computed, and the form in which
they enter the ramification theory of the orbit projection.
`TauCeti.UpperHalfPlane.localMultiplicity_eq_toNat_analyticOrderAt_comp_ofComplex` reads off the
local multiplicity from the order of any function agreeing with `f - f z`, such as `j - 1728`.
-/

public section

open UpperHalfPlane TauCeti.RiemannSurface Topology

namespace TauCeti.UpperHalfPlane

/-- The chart of the upper half-plane at every point is the inclusion into `ℂ`, the inverse of
`UpperHalfPlane.ofComplex`. -/
theorem chartAt_eq_ofComplex_symm (z : ℍ) : chartAt ℂ z = ofComplex.symm := by
  rw [OpenPartialHomeomorph.singletonChartedSpace_chartAt_eq _
    (IsOpenEmbedding.toOpenPartialHomeomorph_source _ _), ofComplex,
    OpenPartialHomeomorph.symm_symm]

/-- On the upper half-plane, the local multiplicity of `f : ℍ → ℂ` at `z` is the order of vanishing
of `f ∘ ofComplex - f z` at `z`. -/
@[simp]
theorem localMultiplicity_eq_analyticOrderNatAt_comp_ofComplex_sub (f : ℍ → ℂ) (z : ℍ) :
    localMultiplicity f z = analyticOrderNatAt (fun w ↦ f (ofComplex w) - f z) z := by
  rw [localMultiplicity_def, isOpenEmbedding_coe.singletonChartedSpace_chartAt_eq,
    chartAt_eq_ofComplex_symm, OpenPartialHomeomorph.symm_symm, chartAt_self_eq]
  simp only [OpenPartialHomeomorph.refl_apply, id_eq]

/-- On the upper half-plane, if `g` agrees with `f - f z`, then the local multiplicity of `f` at
`z` is the order of vanishing of `g ∘ ofComplex` at `z`. -/
theorem localMultiplicity_eq_toNat_analyticOrderAt_comp_ofComplex {f g : ℍ → ℂ} {z : ℍ}
    (hg : ∀ w, f w - f z = g w) :
    localMultiplicity f z = (analyticOrderAt (g ∘ ofComplex) z).toNat := by
  rw [localMultiplicity_eq_analyticOrderNatAt_comp_ofComplex_sub, analyticOrderNatAt]
  congr 2
  exact funext fun w ↦ hg (ofComplex w)

end TauCeti.UpperHalfPlane
