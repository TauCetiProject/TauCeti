/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.RealAlgebra

/-!
# Quadratic-form bounds on subspaces

Scalar-generic lower and upper bounds for the real part of the quadratic form
of a bounded operator, restricted to a subspace.  These predicates are useful
well beyond Davis--Kahan perturbation theory.

The predicates, their monotonicity and the form of a real scalar operator only need a
seminormed inner product space; the comparison with Mathlib's `IsPositive` uses the normed
setting in which that predicate is defined.

A single-vector perturbation estimate complements them: the form stays nonnegative at a vector
close, relative to its norm, to one at which it is coercive
(`ContinuousLinearMap.re_inner_apply_nonneg_of_norm_sub_le`).

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

/-! Form-bound predicates extend the `ContinuousLinearMap` API and support
dot notation on bounded operators. -/
namespace ContinuousLinearMap

section Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

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

end Seminormed

section Normed

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

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

end Normed

section RealScalar

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

attribute [local instance] realAlgebra realIsScalarTower

/-- The real quadratic form of a real scalar operator is the scalar times the squared norm. -/
@[simp] theorem re_inner_algebraMap_apply (c : ℝ) (x : E) :
    RCLike.re ⟪(algebraMap ℝ (E →L[𝕜] E) c) x, x⟫_𝕜 = c * ‖x‖ ^ 2 := by
  rw [Algebra.algebraMap_eq_smul_one, ← IsScalarTower.algebraMap_smul 𝕜]
  simp only [smul_apply, one_apply_eq_self]
  simp [inner_smul_left, RCLike.algebraMap_eq_ofReal]

end RealScalar

section Perturbation

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The form `re ⟪B v, v⟫` stays nonnegative under a small relative perturbation of a vector `u`
on which it is coercive: if `c ‖u‖ ^ 2 ≤ re ⟪B u, u⟫` and `‖u - v‖ ≤ δ ‖v‖` with `δ ≤ 1 / 2` and
`‖B‖ δ ≤ c / 12`, then `0 ≤ re ⟪B v, v⟫`. -/
theorem re_inner_apply_nonneg_of_norm_sub_le {B : E →L[𝕜] E} {c δ : ℝ} (hc : 0 ≤ c)
    (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1 / 2) (hδ₂ : ‖B‖ * δ ≤ c / 12) {u v : E}
    (hu : c * ‖u‖ ^ 2 ≤ RCLike.re ⟪B u, u⟫_𝕜) (huv : ‖u - v‖ ≤ δ * ‖v‖) :
    0 ≤ RCLike.re ⟪B v, v⟫_𝕜 := by
  have hexp : RCLike.re ⟪B v, v⟫_𝕜 =
      RCLike.re ⟪B u, u⟫_𝕜 - RCLike.re ⟪B (u - v), u⟫_𝕜 - RCLike.re ⟪B v, u - v⟫_𝕜 := by
    simp only [map_sub, inner_sub_left, inner_sub_right]
    ring
  have h₁ : RCLike.re ⟪B (u - v), u⟫_𝕜 ≤ ‖B‖ * ‖u - v‖ * ‖u‖ :=
    (re_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _))
  have h₂ : RCLike.re ⟪B v, u - v⟫_𝕜 ≤ ‖B‖ * ‖v‖ * ‖u - v‖ :=
    (re_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (B.le_opNorm _) (norm_nonneg _))
  have hun : ‖v‖ / 2 ≤ ‖u‖ := by
    have := norm_sub_norm_le v u
    rw [norm_sub_rev] at this
    nlinarith [norm_nonneg v]
  have hun' : ‖u‖ ≤ 3 / 2 * ‖v‖ := by
    have := norm_le_norm_add_norm_sub' u v
    nlinarith [norm_nonneg v]
  have h₃ : ‖B‖ * ‖u - v‖ * ‖u‖ ≤ ‖B‖ * (δ * ‖v‖) * (3 / 2 * ‖v‖) :=
    mul_le_mul (mul_le_mul_of_nonneg_left huv (norm_nonneg _)) hun' (norm_nonneg _)
      (by positivity)
  have h₄ : ‖B‖ * ‖v‖ * ‖u - v‖ ≤ ‖B‖ * ‖v‖ * (δ * ‖v‖) :=
    mul_le_mul_of_nonneg_left huv (by positivity)
  have h₅ : c * (‖v‖ / 2) ^ 2 ≤ c * ‖u‖ ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hun 2) hc
  have h₆ := mul_le_mul_of_nonneg_right hδ₂ (sq_nonneg ‖v‖)
  nlinarith

end Perturbation

end ContinuousLinearMap
