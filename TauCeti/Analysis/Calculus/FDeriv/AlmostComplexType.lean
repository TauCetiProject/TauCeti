/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Alternating.Uncurry.AlmostComplexType
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Derivatives of families of forms of type `(p,q)`

Let `J` be a fixed continuous real-linear endomorphism of a real normed space `E`. A form has type
`(p,q)` for `J` when its derivation along `J` is multiplication by `(p - q) * I`. Since this
derivation is continuous linear on forms, differentiating the type equation of a family of forms
of type `(p,q)` shows that its derivative consists of forms of type `(p,q)` again.

## Main declarations

* `ContinuousAlternatingMap.isOfType_fderivWithin`: derivatives of families of forms of type
  `(p,q)` have type `(p,q)`.
-/

public section

open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] {k : ℕ}

namespace ContinuousAlternatingMap

/-- For a fixed endomorphism `J`, the derivative within `s` of a family of forms which have type
`(p,q)` near `z` within `s` consists of forms of type `(p,q)`. -/
theorem isOfType_fderivWithin {J : E →L[ℝ] E} {p q : ℕ} {Θ : E → E [⋀^Fin k]→L[ℝ] F}
    {s : Set E} {z : E} (hs : UniqueDiffWithinAt ℝ s z) (hz : z ∈ s)
    (hΘ : ∀ᶠ y in 𝓝[s] z, (Θ y).IsOfType J p q) (v : E) :
    (fderivWithin ℝ Θ s z v).IsOfType J p q := by
  have hk := (hΘ.self_of_nhdsWithin hz).add_eq
  by_cases hd : DifferentiableWithinAt ℝ Θ s z
  swap
  · simp [fderivWithin_zero_of_not_differentiableWithinAt hd, hk]
  -- The derivation of `J` is continuous linear on forms, so the derivative of the type
  -- equation `D_J Θ = c • Θ` is the type equation of the derivative.
  set c : ℂ := ((p : ℂ) - q) * Complex.I
  let T := (fderivCompContinuousLinearMapCLM F (ContinuousLinearMap.id ℝ E) (ι := Fin k)).flip J
  have hT (β : E [⋀^Fin k]→L[ℝ] F) : T β = J.alternatingDerivation β := by
    simp only [T, ContinuousLinearMap.flip_apply, fderivCompContinuousLinearMapCLM_apply,
      ← ContinuousLinearMap.alternatingDerivation_eq_fderivCompContinuousLinearMap]
  have heq : (fun y ↦ T (Θ y)) =ᶠ[𝓝[s] z] fun y ↦ c • Θ y := by
    filter_upwards [hΘ] with y hy
    rw [hT]
    exact hy.alternatingDerivation_eq
  have hD := hs.eq ((T.hasFDerivAt.comp_hasFDerivWithinAt z
    hd.hasFDerivWithinAt).congr_of_eventuallyEq heq.symm (heq.symm.eq_of_nhdsWithin hz))
    (hd.hasFDerivWithinAt.const_smul c)
  refine isOfType_iff.2 ⟨hk, ?_⟩
  rw [← hT]
  exact congrArg (fun A ↦ A v) hD

end ContinuousAlternatingMap
