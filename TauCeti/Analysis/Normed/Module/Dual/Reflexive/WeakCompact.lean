/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.WeakSpace
import TauCeti.Analysis.Normed.Module.Dual.Goldstine
import TauCeti.Analysis.Normed.Module.DoubleDual
import TauCeti.Analysis.Normed.Module.WeakSpace.SeqCompact
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Reflexivity and weak compactness

A real or complex seminormed space is reflexive if and only if its closed unit ball is
weakly compact. More generally, every norm-closed bounded real-convex set in a reflexive space is
weakly compact. This rests on `TauCeti.isCompact_closure_toWeakSpace_of_isBounded` from
`TauCeti.Analysis.Normed.Module.DoubleDual`: over any proper nontrivially normed field, every
bounded set in a reflexive space has weakly compact closure.

Reflexivity means surjectivity of `NormedSpace.inclusionInDoubleDual`. No completeness,
separability or separation hypothesis is needed for the equivalence. Either condition also implies
completeness (`TauCeti.completeSpace_of_surjective_inclusionInDoubleDual`). The topology changes
are explicit, using `toWeakSpace` and `NormedSpace.inclusionInDoubleDualWeak`.

The forward direction transports Banach–Alaoglu along the inducing bidual map;
the reverse direction uses Goldstine's theorem.

With Šmulian's theorem (`TauCeti.tendsto_subseq_toWeakSpace_of_isCompact_closure`), every bounded
sequence in a reflexive real or complex normed space has a weakly convergent subsequence
(`TauCeti.tendsto_subseq_toWeakSpace_of_isBounded`). Consequently a bounded operator from a
reflexive normed space maps closed balls to norm-closed sets
(`ContinuousLinearMap.isClosed_image_closedBall`).

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.6.
-/

public section

open Bornology Filter Function Metric Set Topology
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
  exact isCompact_closure_toWeakSpace_of_isBounded hE hbound

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

section Normed

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- In a reflexive real or complex normed space, every norm-bounded sequence has a weakly
convergent subsequence. -/
theorem tendsto_subseq_toWeakSpace_of_isBounded (hF : Surjective (inclusionInDoubleDual 𝕜 F))
    {u : ℕ → F} (hu : IsBounded (range u)) :
    ∃ x : F, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace 𝕜 F (u (φ n))) atTop (𝓝 (toWeakSpace 𝕜 F x)) :=
  tendsto_subseq_toWeakSpace_of_isCompact_closure (isCompact_closure_toWeakSpace_of_isBounded hF hu)
    mem_range_self

/-- **A bounded operator on a reflexive space maps closed balls to closed sets.** If `F` is a
reflexive real or complex normed space and `T : F →L[𝕜] G` is bounded, then `T '' closedBall x r`
is closed in `G`. A sequence `T vₙ → y` with `vₙ` in the ball has a weakly convergent subsequence
`vₙ ⇀ z`; the ball is weakly closed, and `T z = y` because every functional on `G` composed with `T`
is a functional on `F`. -/
theorem _root_.ContinuousLinearMap.isClosed_image_closedBall
    (hF : Surjective (inclusionInDoubleDual 𝕜 F)) {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] (T : F →L[𝕜] G) (x : F) (r : ℝ) :
    IsClosed (T '' closedBall x r) := by
  refine isSeqClosed_iff_isClosed.1 fun y p hy hyp ↦ ?_
  choose v hv hTv using hy
  obtain ⟨z, φ, hφ, hz⟩ := tendsto_subseq_toWeakSpace_of_isBounded hF
    (isBounded_closedBall.subset (range_subset_iff.2 hv))
  rw [tendsto_toWeakSpace_iff_forall_eval_tendsto] at hz
  refine ⟨z, ?_, ?_⟩
  · -- The ball is weakly closed: test `z - x` against a norming functional.
    obtain ⟨g, hg, hgz⟩ := exists_dual_vector'' 𝕜 (z - x)
    have hlim : Tendsto (fun n ↦ ‖g (v (φ n) - x)‖) atTop (𝓝 ‖g (z - x)‖) := by
      simpa only [map_sub] using ((hz g).sub_const (g x)).norm
    have hle (n : ℕ) : ‖g (v (φ n) - x)‖ ≤ r :=
      (g.le_opNorm _).trans ((mul_le_of_le_one_left (norm_nonneg _) hg).trans
        (mem_closedBall_iff_norm.1 (hv _)))
    have hr := le_of_tendsto' hlim hle
    rwa [hgz, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg _), ← mem_closedBall_iff_norm] at hr
  · -- Weak limits are unique, since the functionals on `G` separate points.
    rw [← sub_eq_zero]
    refine SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := 𝕜) fun f ↦ ?_
    have hlim : Tendsto (fun n ↦ (f.comp T) (v (φ n))) atTop (𝓝 (f p)) := by
      simp only [ContinuousLinearMap.comp_apply, hTv]
      exact ((f.continuous.tendsto p).comp hyp).comp hφ.tendsto_atTop
    rw [map_sub, ← ContinuousLinearMap.comp_apply, tendsto_nhds_unique (hz (f.comp T)) hlim,
      sub_self]

end Normed

end TauCeti
