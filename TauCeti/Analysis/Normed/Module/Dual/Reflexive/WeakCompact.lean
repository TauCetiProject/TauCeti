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
weakly compact. More generally, every norm-closed bounded real-convex set in a reflexive space is
weakly compact, and so a real function whose sublevel sets on a nonempty set are norm-closed,
convex and bounded attains its infimum there (the direct method of the calculus of variations,
`TauCeti.exists_isMinOn_of_isClosed_of_convex_of_isBounded`). This rests on
`TauCeti.isCompact_closure_toWeakSpace` from `TauCeti.Analysis.Normed.Module.DoubleDual`: over
any proper nontrivially normed field, every bounded set in a reflexive space has weakly compact
closure.

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

/-- **Direct method of the calculus of variations.** In a reflexive seminormed space, a real
function `f` attains its infimum on a nonempty set `D` when every sublevel set
`{u ∈ D | f u ≤ t}` is norm-closed, real-convex and bounded. These sublevel sets are weakly
compact, and a common point of those at the levels `f v` for `v ∈ D` is a minimizer. -/
theorem exists_isMinOn_of_isClosed_of_convex_of_isBounded
    (hE : Surjective (inclusionInDoubleDual 𝕜 E))
    [Module ℝ E] [IsScalarTower ℝ 𝕜 E] {f : E → ℝ} {D : Set E} (hD : D.Nonempty)
    (hclosed : ∀ t, IsClosed {u ∈ D | f u ≤ t}) (hconv : ∀ t, Convex ℝ {u ∈ D | f u ≤ t})
    (hbound : ∀ t, IsBounded {u ∈ D | f u ≤ t}) :
    ∃ u ∈ D, IsMinOn f D u := by
  have : LocallyConvexSpace ℝ E := NormedSpace.toLocallyConvexSpace' 𝕜
  have : Nonempty D := hD.to_subtype
  let K : D → Set (WeakSpace 𝕜 E) := fun v ↦ toWeakSpace 𝕜 E '' {u ∈ D | f u ≤ f v}
  have hdir : Directed (· ⊇ ·) K := fun v w ↦ by
    rcases le_total (f v) (f w) with h | h
    · exact ⟨v, subset_rfl, image_mono fun u hu ↦ ⟨hu.1, hu.2.trans h⟩⟩
    · exact ⟨w, image_mono fun u hu ↦ ⟨hu.1, hu.2.trans h⟩, subset_rfl⟩
  have hKcl (v : D) : IsClosed (K v) := by
    have h := (hconv (f v)).toWeakSpace_closure 𝕜
    rw [(hclosed _).closure_eq] at h
    simp only [K]
    rw [h]
    exact isClosed_closure
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed K hdir
    (fun v ↦ ⟨_, v, ⟨v.2, le_rfl⟩, rfl⟩)
    (fun v ↦ isCompact_toWeakSpace_of_isClosed_of_convex_of_isBounded hE (hclosed _) (hconv _)
      (hbound _)) hKcl
  have hmem (v : D) : (toWeakSpace 𝕜 E).symm x ∈ {u ∈ D | f u ≤ f v} := by
    obtain ⟨u, hu, hux⟩ := mem_iInter.1 hx v
    rwa [← hux, LinearEquiv.symm_apply_apply]
  exact ⟨_, (hmem ⟨_, hD.some_mem⟩).1, isMinOn_iff.2 fun v hv ↦ (hmem ⟨v, hv⟩).2⟩

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
