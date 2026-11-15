/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import TauCeti.Analysis.Normed.Module.Dual.Functoriality

/-!
# The dual of a Banach bimodule

Let `A` be a normed algebra over `𝕜` and `E` a normed space. A bounded bimodule structure on `E`
is given by two bounded bilinear maps `L R : A →L[𝕜] E →L[𝕜] E`, with `a · x = L a x` and
`x · a = R a x`, satisfying `L (a * b) x = L a (L b x)`, `R (a * b) x = R b (R a x)` and
`L a (R b x) = R b (L a x)`. The actions need not be contractive or unital.

The continuous dual `E*` is again a bounded bimodule, with the *dual actions*

`(a · φ) x = φ (x · a)` and `(φ · a) x = φ (a · x)`.

Both are instances of one construction: for a bounded bilinear action
`M : A →L[𝕜] E →L[𝕜] E`, the bounded bilinear map `ContinuousLinearMap.dualAction M` sends `a` to
the adjoint `φ ↦ φ ∘ M a` of `M a`. The left action of `A` on `E*` is `dualAction R` and the
right action is `dualAction L`. Dual bimodules are the coefficient modules in the definition of
amenability, where derivations into duals of Banach bimodules are required to be inner, and in
the bounded Hochschild cohomology `Hⁿ(A, E*)`.

This file proves the bimodule laws of the dual actions, the weak-star continuity of each dual
action in the dual variable, and that adjoints of bounded module maps are module maps for the dual
actions. Since `dualAction M a` is the adjoint `precomp 𝕜 (M a)` of `M a`
(`ContinuousLinearMap.dualAction_apply`), the adjoint API applies directly after rewriting:
`ContinuousLinearMap.norm_precomp_le` gives the bound `‖dualAction M a‖ ≤ ‖M a‖`,
`ContinuousLinearMap.norm_precomp` gives equality over `ℝ` or `ℂ`, and
`ContinuousLinearMap.precomp_precomp_inclusionInDoubleDual` shows that the canonical map of `E` into
its bidual `E**` is a bimodule map when `E**` carries the dual actions of `E*`. Likewise, the
correspondence between invariant subspaces and their annihilators in
`TauCeti.Analysis.Normed.Module.Dual.Invariant` identifies the closed submodules of `E` with the
weak-star closed submodules of `E*`.

## Main definitions

* `ContinuousLinearMap.dualAction`: the dual action `a ↦ (φ ↦ φ ∘ M a)` of a bounded bilinear
  action `M`.

## Main results

* `ContinuousLinearMap.dualAction_apply`: the dual action of `a` is the adjoint of the action of
  `a`.
* `ContinuousLinearMap.dualAction_mul_apply_of_right`,
  `ContinuousLinearMap.dualAction_mul_apply_of_left`,
  `ContinuousLinearMap.dualAction_apply_dualAction_apply_comm`: the dual actions of a bounded
  bimodule satisfy the bimodule laws.
* `ContinuousLinearMap.continuous_toWeakDual_dualAction`: each dual action is weak-star
  continuous in the dual variable.
* `ContinuousLinearMap.precomp_dualAction_apply`: the adjoint of a module map intertwines the
  dual actions.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.6, dual modules.
* V. Runde, *Lectures on Amenability*, §2.1, dual Banach bimodules.
-/

public section

noncomputable section

namespace ContinuousLinearMap

variable {𝕜 A E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup A] [NormedSpace 𝕜 A]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The dual action of a bounded bilinear action `M : A →L[𝕜] E →L[𝕜] E` on the continuous dual
of `E`: `dualAction M a φ = φ ∘ M a`. For a bounded bimodule with left action `L` and right action
`R`, the dual bimodule has left action `dualAction R`, `(a · φ) x = φ (x · a)`, and right action
`dualAction L`, `(φ · a) x = φ (a · x)`. -/
def dualAction (M : A →L[𝕜] E →L[𝕜] E) :
    A →L[𝕜] StrongDual 𝕜 E →L[𝕜] StrongDual 𝕜 E :=
  (compL 𝕜 E E 𝕜).flip ∘L M

/-- The dual action evaluates as `(dualAction M a φ) x = φ (M a x)`. -/
@[simp]
theorem dualAction_apply_apply (M : A →L[𝕜] E →L[𝕜] E) (a : A) (φ : StrongDual 𝕜 E) (x : E) :
    dualAction M a φ x = φ (M a x) := (rfl)

/-- The dual action of `a` is the adjoint of the action of `a`. -/
theorem dualAction_apply (M : A →L[𝕜] E →L[𝕜] E) (a : A) :
    dualAction M a = precomp 𝕜 (M a) := by
  ext φ x
  simp

section Laws

variable [Mul A]

/-- The dual of a right action is a left action: if `R (a * b) x = R b (R a x)`, then
`a * b` acts on functionals as `a` after `b`. -/
theorem dualAction_mul_apply_of_right {R : A →L[𝕜] E →L[𝕜] E}
    (hR : ∀ a b x, R (a * b) x = R b (R a x)) (a b : A) (φ : StrongDual 𝕜 E) :
    dualAction R (a * b) φ = dualAction R a (dualAction R b φ) := by
  ext x
  simp [hR]

/-- The dual of a left action is a right action: if `L (a * b) x = L a (L b x)`, then
`a * b` acts on functionals as `b` after `a`. -/
theorem dualAction_mul_apply_of_left {L : A →L[𝕜] E →L[𝕜] E}
    (hL : ∀ a b x, L (a * b) x = L a (L b x)) (a b : A) (φ : StrongDual 𝕜 E) :
    dualAction L (a * b) φ = dualAction L b (dualAction L a φ) := by
  ext x
  simp [hL]

end Laws

/-- The dual actions of commuting actions commute: if `L a (R b x) = R b (L a x)`, then the dual
left action `dualAction R` commutes with the dual right action `dualAction L`. -/
theorem dualAction_apply_dualAction_apply_comm {L R : A →L[𝕜] E →L[𝕜] E}
    (hLR : ∀ a b x, L a (R b x) = R b (L a x)) (a b : A) (φ : StrongDual 𝕜 E) :
    dualAction R a (dualAction L b φ) = dualAction L b (dualAction R a φ) := by
  ext x
  simp [hLR]

/-- Each dual action is continuous for the weak-star topology in the dual variable. -/
theorem continuous_toWeakDual_dualAction (M : A →L[𝕜] E →L[𝕜] E) (a : A) :
    Continuous fun φ : WeakDual 𝕜 E ↦
      StrongDual.toWeakDual (dualAction M a (WeakDual.toStrongDual φ)) :=
  WeakDual.continuous_of_continuous_eval fun x ↦ WeakDual.eval_continuous (M a x)

/-- The adjoint of a bounded module map intertwines the dual actions: if `T (M a x) = N a (T x)`,
then `T* (dualAction N a ψ) = dualAction M a (T* ψ)`. -/
theorem precomp_dualAction_apply {M : A →L[𝕜] E →L[𝕜] E} {N : A →L[𝕜] F →L[𝕜] F}
    {T : E →L[𝕜] F} (hT : ∀ a x, T (M a x) = N a (T x)) (a : A) (ψ : StrongDual 𝕜 F) :
    precomp 𝕜 T (dualAction N a ψ) = dualAction M a (precomp 𝕜 T ψ) := by
  ext x
  simp [hT]

end ContinuousLinearMap
