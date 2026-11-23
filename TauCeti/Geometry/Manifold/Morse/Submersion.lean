/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Hessian

/-!
# Critical points along a submersion

Let `π : Z → B` be a map whose derivative is onto at `z` and let `f : B → ℝ`. By the chain rule,
`z` is a critical point of `f ∘ π` exactly when `π z` is a critical point of `f`, and there the
critical Hessian of `f ∘ π` is the critical Hessian of `f` read through `dπ`:

`Hess (f ∘ π) z (u, w) = Hess f (π z) (dπ u, dπ w)`.

Since `dπ` is onto, the kernel of the Hessian of `f ∘ π` at `z` is the preimage under `dπ` of the
kernel of the Hessian of `f` at `π z`, and the two Morse indices agree. These are the pointwise
facts behind the Morse–Bott property of the pullback of a Morse function along a submersion
(`TauCeti.IsMorse.isMorseBottFamily_comp`).

## Main results

* `TauCeti.IsRegularPoint.mem_criticalPoints_comp_iff`: at a point where `dπ` is onto, `z` is a
  critical point of `f ∘ π` exactly when `π z` is a critical point of `f`.
* `TauCeti.IsRegularPoint.ker_criticalHessian_comp`: there the kernel of the Hessian of `f ∘ π` is
  the preimage under `dπ` of the kernel of the Hessian of `f`.
* `TauCeti.IsRegularPoint.manifoldMorseIndex_comp`: the Morse index of `f ∘ π` at `z` is that of
  `f` at `π z`.

## References

* A. Banyaga and D. E. Hurtubise, *Lectures on Morse Homology*, Kluwer, 2004, Section 3.5.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E H B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace B] [ChartedSpace H B]
  {E' H' Z : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace Z] [ChartedSpace H' Z]
  {π : Z → B} {f : B → ℝ} {z : Z}

namespace IsRegularPoint

/-- **Critical points along a submersion.** At a point `z` where the derivative of `π` is onto,
`z` is a critical point of `f ∘ π` exactly when `π z` is a critical point of `f`: the differential
of `f ∘ π` is `df ∘ dπ`, which vanishes exactly when `df` does. -/
theorem mem_criticalPoints_comp_iff (hπ : IsRegularPoint I' I π z)
    (hπd : MDifferentiableAt I' I π z) (hf : MDifferentiableAt I 𝓘(ℝ) f (π z)) :
    z ∈ criticalPoints I' (f ∘ π) ↔ π z ∈ criticalPoints I f := by
  simp only [mem_criticalPoints_iff_mfderiv_eq_zero, mfderiv_comp z hf hπd]
  refine ⟨fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_,
    fun h ↦ by rw [h, ContinuousLinearMap.zero_comp]⟩
  obtain ⟨u, rfl⟩ := isRegularPoint_iff.1 hπ v
  exact congr($h u)

variable [I.Boundaryless] [I'.Boundaryless]

/-- **The kernel of the Hessian along a submersion.** If `π z` is a critical point of a function
`f` which is `C²` there, `π` is `C²` at `z` and its derivative there is onto, then the kernel of the
critical Hessian of `f ∘ π` at `z` is the preimage under `dπ` of the kernel of the critical Hessian
of `f` at `π z`. -/
theorem ker_criticalHessian_comp (hπ : IsRegularPoint I' I π z)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f (π z)) (hπ₂ : ContMDiffAt I' I 2 π z)
    (hcrit : π z ∈ criticalPoints I f) :
    (criticalHessian I' (f ∘ π) z).ker =
      (criticalHessian I f (π z)).ker.comap (mfderiv I' I π z).toLinearMap := by
  ext u
  simp only [Submodule.mem_comap, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  refine ⟨fun hu ↦ ContinuousLinearMap.ext fun v ↦ ?_, fun hu ↦ ContinuousLinearMap.ext fun w ↦ ?_⟩
  · obtain ⟨w, rfl⟩ := isRegularPoint_iff.1 hπ v
    have := congr($hu w)
    rwa [criticalHessian_comp_apply rfl hf hπ₂ hcrit] at this
  · rw [criticalHessian_comp_apply rfl hf hπ₂ hcrit, hu, zero_apply, zero_apply]

/-- **The Morse index along a submersion.** If `π z` is a critical point of a function `f` which
is `C²` there, `π` is `C²` at `z` and its derivative there is onto, then the Morse index of
`f ∘ π` at `z` is the Morse index of `f` at `π z`: the quadratic form of the Hessian of `f ∘ π` is
that of `f` pulled back along the surjection `dπ`, which does not change its negative index. -/
theorem manifoldMorseIndex_comp [FiniteDimensional ℝ E'] (hπ : IsRegularPoint I' I π z)
    (hf : ContMDiffAt I 𝓘(ℝ) 2 f (π z)) (hπ₂ : ContMDiffAt I' I 2 π z)
    (hcrit : π z ∈ criticalPoints I f) :
    manifoldMorseIndex I' (f ∘ π) z = manifoldMorseIndex I f (π z) := by
  -- Tangent spaces are their model spaces.
  have : FiniteDimensional ℝ (TangentSpace I' z) := inferInstanceAs (FiniteDimensional ℝ E')
  rw [manifoldMorseIndex_eq_sigNeg_criticalHessian, manifoldMorseIndex_eq_sigNeg_criticalHessian,
    toQuadraticMap_toBilinForm_criticalHessian_comp hf hπ₂ hcrit,
    QuadraticForm.sigNeg_comp_of_surjective _ (isRegularPoint_iff.1 hπ)]

end IsRegularPoint

end TauCeti
