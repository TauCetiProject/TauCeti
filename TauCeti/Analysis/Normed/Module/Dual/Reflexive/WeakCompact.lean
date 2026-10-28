/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.Dual.Goldstine
import Mathlib.Analysis.LocallyConvex.WeakSpace
import TauCeti.Analysis.Normed.Module.DoubleDual

/-!
# Reflexivity and weak compactness

A real or complex seminormed space is reflexive if and only if its closed unit ball is
weakly compact. More generally, every bounded set in a reflexive space has weakly
compact closure, and every norm-closed bounded real-convex set is weakly compact.

Reflexivity means surjectivity of `NormedSpace.inclusionInDoubleDual`. No completeness,
separability or separation hypothesis is needed for the equivalence. For normed spaces,
either condition also implies completeness. The topology changes are explicit, using
`toWeakSpace` and `NormedSpace.inclusionInDoubleDualWeak`.

The forward direction transports Banach–Alaoglu along the inducing bidual map;
the reverse direction uses Goldstine's theorem.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.6.
-/

public section

open Bornology Function Metric Set Topology
open NormedSpace

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A seminormed space whose closed unit ball is weakly compact is reflexive. -/
theorem surjective_inclusionInDoubleDual_of_isCompact_toWeakSpace_closedBall
    (hball : IsCompact (toWeakSpace 𝕜 E '' closedBall 0 1)) :
    Surjective (inclusionInDoubleDual 𝕜 E) := by
  have hclosed := (hball.image (inclusionInDoubleDualWeak 𝕜 E).continuous).isClosed
  have hgold := closure_image_inclusionInDoubleDualWeak_closedBall_zero_one 𝕜 E
  rw [hclosed.closure_eq] at hgold
  apply (closedBall_subset_range_iff_surjective (𝕜 := 𝕜) (𝕜₂ := 𝕜)
    (E := E) (F := StrongDual 𝕜 (StrongDual 𝕜 E)) (σ₁₂ := RingHom.id 𝕜)
    (f := (inclusionInDoubleDual 𝕜 E).toLinearMap) 0
    zero_lt_one).1
  intro φ hφ
  have hmem : StrongDual.toWeakDual φ ∈
      inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' closedBall 0 1) := by
    rw [hgold]
    simpa only [mem_preimage, StrongDual.toStrongDual_toWeakDual] using hφ
  obtain ⟨_, ⟨x, _, rfl⟩, hx⟩ := hmem
  refine ⟨x, ?_⟩
  simpa only [inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply,
    StrongDual.toStrongDual_toWeakDual, ContinuousLinearMap.coe_coe] using
      congrArg WeakDual.toStrongDual hx

/-- In a reflexive seminormed space, every norm-bounded set has weakly compact closure. -/
theorem isCompact_closure_toWeakSpace
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) {s : Set E} (hs : IsBounded s) :
    IsCompact (closure (toWeakSpace 𝕜 E '' s)) := by
  apply NormedSpace.isCompact_closure_weakSpace_of_isBounded 𝕜 E
  · simpa only [preimage_image_eq _ (toWeakSpace 𝕜 E).injective] using hs
  · intro φ _
    obtain ⟨x, hx⟩ := hE (WeakDual.toStrongDual φ)
    refine ⟨toWeakSpace 𝕜 E x, ?_⟩
    apply WeakDual.toStrongDual.injective
    simpa only [inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply,
      StrongDual.toStrongDual_toWeakDual] using hx

/-- Norm-closed bounded real-convex subsets of a reflexive seminormed space are weakly compact.
Convexity over real scalars also covers complex seminormed spaces. -/
theorem isCompact_toWeakSpace_of_isClosed_of_convex_of_isBounded
    (hE : Surjective (inclusionInDoubleDual 𝕜 E))
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] {s : Set E}
    (hclosed : IsClosed s) (hconv : Convex ℝ s) (hbound : IsBounded s) :
    IsCompact (toWeakSpace 𝕜 E '' s) := by
  have : LocallyConvexSpace ℝ E := NormedSpace.toLocallyConvexSpace' 𝕜
  rw [← hclosed.closure_eq, hconv.toWeakSpace_closure 𝕜]
  exact isCompact_closure_toWeakSpace hE hbound

/-- Every closed ball in a reflexive seminormed space is weakly compact, including balls
of zero or negative radius. -/
theorem isCompact_toWeakSpace_closedBall
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) (x : E) (r : ℝ) :
    IsCompact (toWeakSpace 𝕜 E '' closedBall x r) := by
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := .of_algebraMap_smul fun _ _ ↦ rfl
  exact isCompact_toWeakSpace_of_isClosed_of_convex_of_isBounded hE
    isClosed_closedBall (convex_closedBall x r) isBounded_closedBall

/-- A real or complex seminormed space is reflexive exactly when its closed unit ball is
weakly compact. No completeness or separation assumption is needed. -/
theorem surjective_inclusionInDoubleDual_iff_isCompact_toWeakSpace_closedBall :
    Surjective (inclusionInDoubleDual 𝕜 E) ↔
      IsCompact (toWeakSpace 𝕜 E '' closedBall 0 1) :=
  ⟨fun hE ↦ isCompact_toWeakSpace_closedBall hE 0 1,
    surjective_inclusionInDoubleDual_of_isCompact_toWeakSpace_closedBall⟩

end TauCeti
