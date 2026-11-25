/-
Copyright (c) 2026 The Tau Ceti contributors and Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Jon Crall, GPT 5.6 High, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded
public import TauCeti.Analysis.InnerProductSpace.Projection.Acute.Basic

/-!
# Acute pairs of subspaces are unitarily equivalent

The two subspaces of an acute pair (`Submodule.IsAcute`) of complete subspaces are unitarily
equivalent, in any dimension: the compression `P_V|_U : U → V` is injective with dense range, so
its polar factor is a surjective isometry `U ≃ₗᵢ V`. This is the Hilbert-space comparison behind
the constancy of the deficiency subspaces of a symmetric operator on each open half-plane; the
algebraic rank, which `Submodule.rank_eq_of_projectionGap_lt_one` compares, is the wrong invariant
in infinite dimension.

## Main results

* `Submodule.IsAcute.nonempty_linearIsometryEquiv`: the subspaces of an acute pair of complete
  subspaces are linearly isometrically equivalent.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Springer (1995), §I.4.6.
-/

public section

noncomputable section

namespace Submodule

open ContinuousLinearMap
open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {U V : Submodule 𝕜 E} [CompleteSpace U] [CompleteSpace V]

/-- **Acute pairs are unitarily equivalent.** The two subspaces of an acute pair of complete
subspaces are linearly isometrically equivalent, with no dimension hypothesis and no completeness
of the ambient space. An equivalence is the polar factor of the compression `P_V|_U : U → V`. -/
theorem IsAcute.nonempty_linearIsometryEquiv (h : U.IsAcute V) : Nonempty (U ≃ₗᵢ[𝕜] V) := by
  obtain ⟨hUV, hVU⟩ := isAcute_iff_disjoint.1 h
  set T : U →L[𝕜] V := V.orthogonalProjectionOnto ∘L U.subtypeL
  have hinj : Function.Injective T := by
    refine (injective_iff_map_eq_zero T).2 fun u hu ↦ Subtype.ext ?_
    exact disjoint_def.1 hUV _ u.property (orthogonalProjectionOnto_eq_zero_iff.1 hu)
  -- A vector of `V` orthogonal to the range of `T` is orthogonal to `U`, hence zero.
  have hdense : T.range.topologicalClosure = ⊤ := by
    refine topologicalClosure_eq_top_iff.2 (eq_bot_iff.2 fun v hv ↦ ?_)
    have hvU : (v : E) ∈ Uᗮ := (U.mem_orthogonal (v : E)).2 fun u hu ↦ by
      simpa only [T, coe_coe, comp_apply, subtypeL_apply,
        inner_orthogonalProjectionOnto_eq_of_mem_right] using
        inner_right_of_mem_orthogonal (LinearMap.mem_range_self (T : U →ₗ[𝕜] V) ⟨u, hu⟩) hv
    exact (mem_bot 𝕜).2 (Subtype.ext (disjoint_def.1 hVU _ v.property hvU))
  have hsurj : Function.Surjective T.polarFactor :=
    LinearMap.range_eq_top.1 (by rw [range_polarFactor, hdense])
  exact ⟨LinearIsometryEquiv.ofSurjective (T.polarIsometry hinj)
    (by rwa [coe_polarIsometry])⟩

end Submodule
