/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Restricting bounded actions to invariant submodules

A bounded bilinear action preserving a submodule restricts to a bounded action on that
submodule, with operator norm at most that of the original action.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 B E : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup B] [NormedSpace 𝕜 B]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Restrict a bounded bilinear action to a submodule that it preserves. -/
noncomputable def restrictAction (M : B →L[𝕜] E →L[𝕜] E) (p : Submodule 𝕜 E)
    (hM : ∀ a x, x ∈ p → M a x ∈ p) : B →L[𝕜] p →L[𝕜] p :=
  LinearMap.mkContinuous
    { toFun a := (M a).restrict (hM a)
      map_add' a b := by ext x; exact congrArg (fun f ↦ f x.1) (map_add M a b)
      map_smul' c a := by
        ext x
        exact congrArg (fun f ↦ f x.1) (map_smul M c a) }
    ‖M‖ fun a ↦ by
      apply opNorm_le_bound _ (by positivity)
      intro x
      exact M.le_opNorm₂ a x.1

/-- The restricted action agrees with the original action after inclusion. -/
@[simp]
theorem coe_restrictAction_apply (M : B →L[𝕜] E →L[𝕜] E) (p : Submodule 𝕜 E)
    (hM : ∀ a x, x ∈ p → M a x ∈ p) (a : B) (x : p) :
    (M.restrictAction p hM a x : E) = M a x := (rfl)

/-- Restricting a bounded action to an invariant submodule does not increase its norm. -/
theorem norm_restrictAction_le (M : B →L[𝕜] E →L[𝕜] E) (p : Submodule 𝕜 E)
    (hM : ∀ a x, x ∈ p → M a x ∈ p) : ‖M.restrictAction p hM‖ ≤ ‖M‖ := by
  apply opNorm_le_bound₂ _ (norm_nonneg _)
  intro a x
  exact M.le_opNorm₂ a x.1

end ContinuousLinearMap
