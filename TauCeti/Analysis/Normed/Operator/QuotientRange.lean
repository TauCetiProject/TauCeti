/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.ContinuousInverse
public import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Fixed complements to nearby operator ranges

A continuous family of split injections with a complete ambient space has a single closed
complement to its ranges near each parameter. The complement parametrizes all nearby
quotients through `ContinuousLinearMap.quotientRangeEquiv`. This is the local
linear input for quotient bundles, such as the intrinsic normal bundle of an immersion.

The proof uses Mathlib's `ContinuousLinearEquiv.equivOfRightInverse` and openness of
invertibility.

Reference: J. M. Lee, *Introduction to Smooth Manifolds*, second edition,
the normal-bundle construction preceding Theorem 6.24.
-/

public section

open Set Filter Topology

variable {𝕜 X E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A fixed complement to a split injection still parametrizes the quotient by every
sufficiently nearby range. The source and ambient spaces may be infinite dimensional. -/
theorem ContinuousAt.exists_isInvertible_coprod_subtypeL
    [TopologicalSpace X] [CompleteSpace F]
    {A : X → E →L[𝕜] F} {x₀ : X} (hA : ContinuousAt A x₀)
    (h₀ : (A x₀).HasLeftInverse) :
    ∃ Q : Submodule 𝕜 F, IsClosed (Q : Set F) ∧
      ∃ U : Set X, IsOpen U ∧ x₀ ∈ U ∧
        ∀ x ∈ U, ((A x).coprod Q.subtypeL).IsInvertible := by
  let Q := h₀.leftInverse.ker
  have hQ : IsClosed (Q : Set F) := h₀.leftInverse.isClosed_ker
  let e := ContinuousLinearEquiv.equivOfRightInverse h₀.leftInverse (A x₀)
    h₀.leftInverse_leftInverse
  have : CompleteSpace (E × Q) :=
    (e.isUniformEmbedding.completeSpace_congr e.surjective).mp inferInstance
  have he : ((A x₀).coprod Q.subtypeL).IsInvertible := by
    refine ⟨e.symm, ?_⟩
    apply ContinuousLinearMap.ext
    intro p
    exact ContinuousLinearEquiv.equivOfRightInverse_symm_apply _ _ _ p
  have hnear : ∀ᶠ x in 𝓝 x₀, ((A x).coprod Q.subtypeL).IsInvertible :=
    (hA.continuousLinearMapCoprod continuousAt_const).eventually he.eventually_nhds
  obtain ⟨U, hUsub, hU, hx₀⟩ := mem_nhds_iff.mp hnear
  exact ⟨Q, hQ, U, hU, hx₀, fun x hx => hUsub hx⟩
