module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Small `RCLike` inner-product lemmas

This file records scalar inner-product facts for `RCLike` fields that are used by multiple
`L²` packaging developments.
-/

public section

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The inner product of two real scalars, cast into any `RCLike` field, is the cast of their
product. -/
lemma inner_algebraMap_algebraMap (a b : ℝ) :
    inner 𝕜 ((algebraMap ℝ 𝕜) a) ((algebraMap ℝ 𝕜) b) =
      (algebraMap ℝ 𝕜) (a * b) := by
  simp [RCLike.inner_apply, RCLike.conj_ofReal, map_mul, mul_comm]

end TauCeti
