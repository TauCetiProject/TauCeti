/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Quadratic-form bounds on subspaces

Scalar-generic lower and upper bounds for the real part of the quadratic form
of a bounded operator, restricted to a subspace.  These predicates are useful
well beyond Davis--Kahan perturbation theory.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `df036cd`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Original authors / copyright: Jon Crall, GPT 5.6 High; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (enforced by `scripts/check_dependency_layers.py`).
-/

public section


open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace TauCeti

/-! The Mathlib type namespace is mirrored *inside* `TauCeti`, matching the destination
library (Tau Ceti, e.g. `Analysis/Fredholm/Basic.lean` and
`LinearAlgebra/TotallyReal.lean`).  Root `ContinuousLinearMap` is deliberately not extended:
this repository cannot upstream to Mathlib, so a name taken there is a bet that can never be
settled by coordination.  Consumers get `A.LowerFormBoundOn U c` from `open TauCeti` --
being inside `namespace TauCeti` is *not* sufficient, as dot notation resolves through
`open`, not through the enclosing namespace. -/
namespace ContinuousLinearMap

open TauCeti

/-- Lower quadratic-form bound on a subspace. -/
@[expose]
def LowerFormBoundOn (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (c : ℝ) : Prop :=
  ∀ x ∈ U, c * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜

/-- Upper quadratic-form bound on a subspace. -/
@[expose]
def UpperFormBoundOn (A : E →L[𝕜] E) (U : Submodule 𝕜 E) (c : ℝ) : Prop :=
  ∀ x ∈ U, RCLike.re ⟪A x, x⟫_𝕜 ≤ c * ‖x‖ ^ 2

/-! ### Basic theory

The two ways a form bound weakens -- in the constant and in the subspace -- and the
identification of the degenerate case with Mathlib's `IsPositive`.  A consumer holding a
bound on `U` at constant `c` and needing one on a subspace of `U`, or at a worse constant,
should not have to reprove it from the definition. -/

/-- A lower form bound weakens as the constant decreases. -/
theorem LowerFormBoundOn.mono_const {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {c c' : ℝ}
    (h : A.LowerFormBoundOn U c) (hc : c' ≤ c) : A.LowerFormBoundOn U c' :=
  fun x hx => (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖)).trans (h x hx)

/-- A lower form bound restricts to a smaller subspace. -/
theorem LowerFormBoundOn.mono_subspace {A : E →L[𝕜] E} {U U' : Submodule 𝕜 E} {c : ℝ}
    (h : A.LowerFormBoundOn U c) (hU : U' ≤ U) : A.LowerFormBoundOn U' c :=
  fun x hx => h x (hU hx)

/-- An upper form bound weakens as the constant increases. -/
theorem UpperFormBoundOn.mono_const {A : E →L[𝕜] E} {U : Submodule 𝕜 E} {c c' : ℝ}
    (h : A.UpperFormBoundOn U c) (hc : c ≤ c') : A.UpperFormBoundOn U c' :=
  fun x hx => (h x hx).trans (mul_le_mul_of_nonneg_right hc (sq_nonneg ‖x‖))

/-- An upper form bound restricts to a smaller subspace. -/
theorem UpperFormBoundOn.mono_subspace {A : E →L[𝕜] E} {U U' : Submodule 𝕜 E} {c : ℝ}
    (h : A.UpperFormBoundOn U c) (hU : U' ≤ U) : A.UpperFormBoundOn U' c :=
  fun x hx => h x (hU hx)

/-- **The grounding to Mathlib.**  A positive operator is exactly one with the zero lower
form bound on the whole space; this is the direction that makes Mathlib's positivity API
usable wherever a form bound is held. -/
theorem IsPositive.lowerFormBoundOn_top {A : E →L[𝕜] E} (hA : A.IsPositive) :
    A.LowerFormBoundOn ⊤ 0 :=
  fun x _ => by simpa [ContinuousLinearMap.reApplyInnerSelf] using hA.2 x

/-- The converse: symmetry plus the zero lower bound on `⊤` is positivity.  Together with
`IsPositive.lowerFormBoundOn_top` this pins `LowerFormBoundOn _ ⊤ 0` as a generalization of
Mathlib's predicate rather than a competitor to it. -/
theorem isPositive_of_lowerFormBoundOn_top {A : E →L[𝕜] E} (hsym : A.IsSymmetric)
    (h : A.LowerFormBoundOn ⊤ 0) : A.IsPositive :=
  ⟨hsym, fun x => by
    simpa [ContinuousLinearMap.reApplyInnerSelf] using h x Submodule.mem_top⟩

end ContinuousLinearMap

end TauCeti
