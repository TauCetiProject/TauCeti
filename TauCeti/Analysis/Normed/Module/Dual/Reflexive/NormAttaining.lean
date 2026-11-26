/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import Mathlib.Analysis.Normed.Module.WeakDual
import TauCeti.Analysis.Normed.Module.Dual.JamesBoundary
import TauCeti.Analysis.Normed.Module.Dual.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.Normed.Module.WeakSpace.EberleinSmulian

/-!
# Norm-attaining functionals and reflexivity

A continuous linear functional `f` on a normed space *attains its norm* if `‖f x‖ = ‖f‖` for
some `x` in the closed unit ball. Every functional on a reflexive space attains its norm, since
the closed unit ball is weakly compact. James's theorem is the converse for Banach spaces. This
file proves it for separable Banach spaces.

If every functional attains its norm, the canonical image of the closed unit ball in the bidual
is a James boundary of the dual. The Rainwater–Simons theorem for James boundaries
(`TauCeti.tendsto_toWeakSpace_of_forall_mem_tendsto`, a consequence of Simons' inequality) then
shows that a bounded sequence of functionals which converges weak-star also converges weakly,
that is, against every element of the bidual
(`TauCeti.tendsto_toWeakSpace_of_forall_exists_norm_apply_eq_norm`).

For a separable space the dual closed unit ball is weak-star sequentially compact, so it is then
weakly sequentially compact, and by Eberlein–Šmulian weakly compact. The dual is therefore
reflexive, and so is the space when it is complete
(`TauCeti.surjective_inclusionInDoubleDual_iff_forall_exists_norm_apply_eq_norm`).

## Main statements

* `TauCeti.exists_norm_apply_eq_norm_of_surjective_inclusionInDoubleDual`: on a reflexive space
  every functional attains its norm.
* `TauCeti.tendsto_toWeakSpace_of_forall_exists_norm_apply_eq_norm`: the Rainwater–Simons
  theorem.
* `TauCeti.surjective_inclusionInDoubleDual_iff_forall_exists_norm_apply_eq_norm`: James's
  theorem for separable Banach spaces.

## References

* R. C. James, *Reflexivity and the supremum of linear functionals*, Ann. of Math. **66**
  (1957), 159–169.
* J. Rainwater, *Weak convergence of bounded sequences*, Proc. Amer. Math. Soc. **14** (1963),
  999.
* S. Simons, *A convergence theorem with boundary*, Pacific J. Math. **40** (1972), 703–708.
-/

public section

open Bornology Filter Function Metric NormedSpace RCLike Set Topology

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜]

section Seminormed

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Every continuous linear functional on a reflexive space attains its norm on the closed unit
ball. -/
theorem exists_norm_apply_eq_norm_of_surjective_inclusionInDoubleDual
    (hE : Surjective (inclusionInDoubleDual 𝕜 E)) (f : StrongDual 𝕜 E) :
    ∃ x, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖ := by
  -- `f` is weakly continuous, so `‖f‖` has a maximum on the weakly compact closed unit ball.
  have hcont : Continuous fun z : WeakSpace 𝕜 E ↦ ‖f ((toWeakSpace 𝕜 E).symm z)‖ :=
    (WeakBilin.eval_continuous (topDualPairing 𝕜 E).flip f).norm
  obtain ⟨_, ⟨x, hx, rfl⟩, hmax⟩ := (isCompact_toWeakSpace_closedBall hE 0 1).exists_isMaxOn
    ⟨_, 0, mem_closedBall_self zero_le_one, rfl⟩ hcont.continuousOn
  rw [mem_closedBall_zero_iff] at hx
  refine ⟨x, hx, le_antisymm (f.unit_le_opNorm x hx)
    (f.opNorm_le_of_unit_norm (norm_nonneg _) fun y hy ↦ ?_)⟩
  have := hmax ⟨y, mem_closedBall_zero_iff.2 hy.le, rfl⟩
  simpa using this

/-- **The Rainwater–Simons theorem.** If every continuous linear functional on `E` attains its
norm on the closed unit ball, then every bounded sequence in the dual which converges weak-star
converges weakly, that is, against every element of the bidual.

The canonical image of the closed unit ball of `E` in the bidual is then a James boundary of the
dual, so this is `TauCeti.tendsto_toWeakSpace_of_forall_mem_tendsto` for that boundary. -/
theorem tendsto_toWeakSpace_of_forall_exists_norm_apply_eq_norm
    (hE : ∀ f : StrongDual 𝕜 E, ∃ x, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖) {f : ℕ → StrongDual 𝕜 E}
    {g : StrongDual 𝕜 E} (hbdd : IsBounded (range f))
    (hlim : ∀ x, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n ↦ toWeakSpace 𝕜 (StrongDual 𝕜 E) (f n)) atTop
      (𝓝 (toWeakSpace 𝕜 (StrongDual 𝕜 E) g)) := by
  refine tendsto_toWeakSpace_of_forall_mem_tendsto
    (B := inclusionInDoubleDual 𝕜 E '' closedBall 0 1) ?_ ?_ hbdd ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact (double_dual_bound 𝕜 E x).trans (mem_closedBall_zero_iff.1 hx)
  · intro φ
    obtain ⟨x, hx, hφx⟩ := StrongDual.exists_norm_le_one_re_apply_eq_norm_iff.2 (hE φ)
    exact ⟨_, mem_image_of_mem _ (mem_closedBall_zero_iff.2 hx), by simpa [dual_def] using hφx⟩
  · rintro _ ⟨x, -, rfl⟩
    simpa only [dual_def] using hlim x

end Seminormed

section Normed

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- **James's theorem for separable spaces.** A separable Banach space on which every continuous
linear functional attains its norm on the closed unit ball is reflexive. -/
theorem surjective_inclusionInDoubleDual_of_forall_exists_norm_apply_eq_norm [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    (hE : ∀ f : StrongDual 𝕜 E, ∃ x, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖) :
    Surjective (inclusionInDoubleDual 𝕜 E) := by
  -- The dual closed unit ball is weakly sequentially compact: extract a weak-star convergent
  -- subsequence by separability, which converges weakly by the Rainwater–Simons theorem.
  refine surjective_inclusionInDoubleDual_of_strongDual
    (surjective_inclusionInDoubleDual_of_isCompact_toWeakSpace_closedBall
      (isCompact_toWeakSpace_iff_isSeqCompact.2 ?_))
  rintro u hu
  choose v hv hvu using hu
  obtain ⟨φ, hφ, ψ, hψ, hlim⟩ := WeakDual.isSeqCompact_closedBall (𝕜 := 𝕜) (E := E) 0 1
    (x := fun n ↦ StrongDual.toWeakDual (v n)) fun n ↦ by simpa using hv n
  refine ⟨toWeakSpace 𝕜 _ (WeakDual.toStrongDual φ), ⟨_, hφ, rfl⟩, ψ, hψ, ?_⟩
  have := tendsto_toWeakSpace_of_forall_exists_norm_apply_eq_norm hE (f := fun n ↦ v (ψ n))
    (g := WeakDual.toStrongDual φ)
    (isBounded_closedBall.subset (range_subset_iff.2 fun n ↦ hv (ψ n))) fun x ↦ by
      simpa [comp_def] using ((WeakDual.eval_continuous x).tendsto φ).comp hlim
  simpa [comp_def, ← hvu] using this

/-- **James's theorem for separable spaces.** A separable Banach space is reflexive exactly when
every continuous linear functional attains its norm on the closed unit ball. -/
theorem surjective_inclusionInDoubleDual_iff_forall_exists_norm_apply_eq_norm [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] :
    Surjective (inclusionInDoubleDual 𝕜 E) ↔
      ∀ f : StrongDual 𝕜 E, ∃ x, ‖x‖ ≤ 1 ∧ ‖f x‖ = ‖f‖ :=
  ⟨exists_norm_apply_eq_norm_of_surjective_inclusionInDoubleDual,
    surjective_inclusionInDoubleDual_of_forall_exists_norm_apply_eq_norm⟩

end Normed

end TauCeti
