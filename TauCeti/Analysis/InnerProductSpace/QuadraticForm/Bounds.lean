/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Quadratic-form bounds on subspaces

Scalar-generic lower and upper bounds for the real part of the quadratic form
of a bounded operator, restricted to a subspace.  These predicates are useful
well beyond Davis--Kahan perturbation theory.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/Analysis/InnerProductSpace/QuadraticFormBounds.lean`
  in the DKPS formalization at commit `df036cd`.
* Authors: Jon Crall and GPT 5.6 High; Copyright (c) 2026 Kitware, Inc.;
  released under Apache 2.0.
-/

public section


open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-! Form-bound predicates extend the `ContinuousLinearMap` API and support
dot notation on bounded operators. -/
namespace ContinuousLinearMap

/-- Lower quadratic-form bound on a subspace. -/
def LowerFormBoundOn (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (c : ℝ) : Prop :=
  ∀ x ∈ U, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜

/-- Upper quadratic-form bound on a subspace. -/
def UpperFormBoundOn (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (c : ℝ) : Prop :=
  ∀ x ∈ U, RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2

/-- The characteristic inequality defining a lower form bound. -/
theorem lowerFormBoundOn_iff (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (c : ℝ) :
    A.LowerFormBoundOn U c ↔
      ∀ x ∈ U, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜 := Iff.rfl

/-- The characteristic inequality defining an upper form bound. -/
theorem upperFormBoundOn_iff (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (c : ℝ) :
    A.UpperFormBoundOn U c ↔
      ∀ x ∈ U, RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2 := Iff.rfl

/-! ### Basic theory

The two ways a form bound weakens -- in the constant and in the subspace -- and the
identification of the degenerate case with Mathlib's `IsPositive`.  A consumer holding a
bound on `U` at constant `c` and needing one on a subspace of `U`, or at a worse constant,
should not have to reprove it from the definition. -/

/-- A lower form bound weakens as the constant decreases. -/
theorem LowerFormBoundOn.mono_const {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {c c' : ℝ}
    (h : A.LowerFormBoundOn U c) (hc : c' ≤ c) : A.LowerFormBoundOn U c' :=
  (lowerFormBoundOn_iff A U c').2 fun x hx =>
    (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖)).trans
      ((lowerFormBoundOn_iff A U c).1 h x hx)

/-- A lower form bound restricts to a smaller subspace. -/
theorem LowerFormBoundOn.mono_subspace {A : E →L[𝕜] E} {U U' : Submodule 𝕜 E} {c : ℝ}
    (h : A.LowerFormBoundOn U c) (hU : U' ≤ U) : A.LowerFormBoundOn U' c :=
  (lowerFormBoundOn_iff A U' c).2 fun x hx =>
    (lowerFormBoundOn_iff A U c).1 h x (hU hx)

/-- An upper form bound weakens as the constant increases. -/
theorem UpperFormBoundOn.mono_const {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {c c' : ℝ}
    (h : A.UpperFormBoundOn U c) (hc : c ≤ c') : A.UpperFormBoundOn U c' :=
  (upperFormBoundOn_iff A U c').2 fun x hx =>
    ((upperFormBoundOn_iff A U c).1 h x hx).trans
      (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖))

/-- An upper form bound restricts to a smaller subspace. -/
theorem UpperFormBoundOn.mono_subspace {A : E →L[𝕜] E} {U U' : Submodule 𝕜 E} {c : ℝ}
    (h : A.UpperFormBoundOn U c) (hU : U' ≤ U) : A.UpperFormBoundOn U' c :=
  (upperFormBoundOn_iff A U' c).2 fun x hx =>
    (upperFormBoundOn_iff A U c).1 h x (hU hx)

/-- Positivity implies the zero lower form bound on the whole space. -/
theorem IsPositive.lowerFormBoundOn_top {A : E →L[𝕜] E} (hA : A.IsPositive) :
    A.LowerFormBoundOn ⊤ 0 :=
  (lowerFormBoundOn_iff A ⊤ 0).2 fun x _ => by
    simpa [ContinuousLinearMap.reApplyInnerSelf] using hA.2 x

/-- The converse: symmetry plus the zero lower bound on `⊤` is positivity.  Together with
`IsPositive.lowerFormBoundOn_top` this pins `LowerFormBoundOn _ ⊤ 0` as a generalization of
Mathlib's predicate rather than a competitor to it. -/
theorem isPositive_of_lowerFormBoundOn_top {A : E →L[𝕜] E} (hsym : A.IsSymmetric)
    (h : A.LowerFormBoundOn ⊤ 0) : A.IsPositive :=
  ⟨hsym, fun x => by
    simpa [ContinuousLinearMap.reApplyInnerSelf] using
      (lowerFormBoundOn_iff A ⊤ 0).1 h x Submodule.mem_top⟩

end ContinuousLinearMap
