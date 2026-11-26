/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle.Basic

import TauCeti.Geometry.Manifold.Submersion.Split

/-!
# Regular values of functions of the actions on `T*Tⁿ`

Let `p > 0`, let `Tⁿ = ι → AddCircle p` be the torus and `I = (I_j)` the actions of its cotangent
bundle `T*Tⁿ` (`TauCeti.CotangentBundle.torusActions`). The action map is a submersion
(`TauCeti.CotangentBundle.surjective_mfderiv_torusActions`) and every vector of actions is the
actions of some covector, so for a profile `h : ℝⁿ → ℝ` the regular points and values of the
function of the actions `h ∘ I` are read off from those of `h`.

## Main results

In the namespace `TauCeti.CotangentBundle`:

* `isRegularPoint_comp_torusActions_iff`: `h ∘ I` is regular at a covector exactly when the
  derivative of `h` is surjective at its actions.
* `isRegularValue_comp_torusActions_iff`: the regular values of `h ∘ I` are those of `h`.
-/

public section

noncomputable section

open Bundle Function
open scoped Manifold

namespace TauCeti

namespace CotangentBundle

variable (p : ℝ) [Fact (0 < p)] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A function of the actions is regular at a covector exactly when its profile is regular at the
actions of the covector: the action map is a submersion. Where the profile is not differentiable
neither holds. -/
theorem isRegularPoint_comp_torusActions_iff {h : (ι → ℝ) → ℝ}
    {z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)} :
    IsRegularPoint ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) 𝓘(ℝ)
        (h ∘ torusActions p) z ↔
      Surjective (fderiv ℝ h (torusActions p z)) := by
  by_cases hh : DifferentiableAt ℝ h (torusActions p z)
  · rw [← isRegularPoint_iff_surjective_fderiv]
    exact ⟨fun hz ↦ hz.of_comp hh.mdifferentiableAt
        ((contMDiff_torusActions p z).mdifferentiableAt (by simp)),
      fun hz ↦ hz.comp (isRegularPoint_iff.2 (surjective_mfderiv_torusActions p z))⟩
  · -- Differentiability descends along the submersion `I`, so `h ∘ I` is not differentiable.
    have hI := ((contMDiff_torusActions (ι := ι) p).isSubmersionOfComplement_of_surjective_mfderiv
      (by simp) (surjective_mfderiv_torusActions p)).isSubmersion.isSubmersionAt z
    refine iff_of_false (fun hz ↦ hh (mdifferentiableAt_iff_differentiableAt.1
      ((hI.mdifferentiableAt_comp_iff (by simp)).1 hz.mdifferentiableAt))) ?_
    rw [fderiv_zero_of_not_differentiableAt hh]
    intro h0
    obtain ⟨v, hv⟩ := h0 1
    simp at hv

/-- **The regular values of a function of the actions are those of its profile.** Every vector of
actions is the actions of some covector, so `c` is a regular value of `h ∘ I` exactly when the
derivative of `h` is surjective at every point of `h⁻¹(c)`. -/
theorem isRegularValue_comp_torusActions_iff {h : (ι → ℝ) → ℝ} {c : ℝ} :
    IsRegularValue ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) 𝓘(ℝ)
        (h ∘ torusActions p) c ↔
      ∀ a, h a = c → Surjective (fderiv ℝ h a) := by
  rw [isRegularValue_iff]
  refine ⟨fun hc a ha ↦ ?_,
    fun hc z hz ↦ (isRegularPoint_comp_torusActions_iff p).2 (hc _ hz)⟩
  -- The covector `κ(0, a)` has the actions `a`.
  have hz := hc (actionAngleCover p (0, a)) (by simp [ha])
  rwa [isRegularPoint_comp_torusActions_iff p, torusActions_actionAngleCover] at hz

end CotangentBundle

end TauCeti
