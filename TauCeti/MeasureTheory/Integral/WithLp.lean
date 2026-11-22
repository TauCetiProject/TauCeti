/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.Calculus.FDeriv.WithLp

/-!
# Energy of a map into a Euclidean product

For maps `f` and `g`, the derivative of `w ↦ (f w, g w)` into the Euclidean product
`WithLp 2 (F × E)` in a direction `v` has squared length `‖df v‖² + ‖dg v‖²`
(`TauCeti.norm_fderiv_toLp_prodMk_apply_sq`). Integrating over a set, the energy of the pair in
the direction `v` is the sum of the energies of `f` and `g`
(`TauCeti.setIntegral_norm_fderiv_toLp_prodMk_apply_sq`). For the graph `w ↦ (w, u w)` of a map
`u` and a unit vector `v`, this says that the energy of the graph is the measure of the set plus
the energy of `u`, the energy identity of Gromov's graph construction.
-/

public section

open MeasureTheory

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [MeasurableSpace G] {μ : Measure G}

/-- On a measurable set where `f` and `g` are differentiable, the energy in the direction `v` of
the map `w ↦ (f w, g w)` into the Euclidean product is the sum of the energies of `f` and `g`. -/
theorem setIntegral_norm_fderiv_toLp_prodMk_apply_sq {f : G → F} {g : G → E} {S : Set G}
    (hS : MeasurableSet S) (hf : ∀ y ∈ S, DifferentiableAt 𝕜 f y)
    (hg : ∀ y ∈ S, DifferentiableAt 𝕜 g y) (v : G)
    (hfi : IntegrableOn (fun y ↦ ‖fderiv 𝕜 f y v‖ ^ 2) S μ)
    (hgi : IntegrableOn (fun y ↦ ‖fderiv 𝕜 g y v‖ ^ 2) S μ) :
    ∫ y in S, ‖fderiv 𝕜 (fun w ↦ WithLp.toLp 2 (f w, g w)) y v‖ ^ 2 ∂μ =
      ∫ y in S, ‖fderiv 𝕜 f y v‖ ^ 2 ∂μ + ∫ y in S, ‖fderiv 𝕜 g y v‖ ^ 2 ∂μ := by
  rw [setIntegral_congr_fun hS fun y hy ↦ norm_fderiv_toLp_prodMk_apply_sq (hf y hy) (hg y hy) v,
    integral_add hfi hgi]

end TauCeti
