/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import TauCeti.Analysis.Normed.Module.Dual.Adjoint
import TauCeti.Topology.MetricSpace.SimultaneousApproximation

/-!
# Norm approximation from the bidual

Combined with the bipolar closed-ball criterion
(`ContinuousLinearMap.mem_closure_image_closedBall_iff`), exact operator identities solved in a
bidual ball yield norm-bounded approximate solutions in the original space: if `Φ ∈ E**` has
`‖Φ‖ ≤ r` and `T** Φ = J_F y`, then `y ∈ closure (T '' closedBall 0 r)`. Applied to a finite
product, finitely many equations `Sᵢ** Φ = J (zᵢ)` can be approximately solved simultaneously in
norm by a single vector of norm at most `r`, and for an arbitrary family of equations this yields a
proper filter eventually bounded in norm by `r` along which every `Sₖ x → zₖ` (used to construct
bounded approximate identities and bounded approximate diagonals from bidual witnesses).

## Main results

* `ContinuousLinearMap.mem_closure_image_closedBall_of_precomp_precomp_eq`: if `‖Φ‖ ≤ r` and
  `T** Φ = J_F y`, then `y ∈ closure (T '' closedBall 0 r)`.
* `ContinuousLinearMap.mem_closure_image_closedBall_of_forall_apply_comp_eq`: pointwise form of
  `mem_closure_image_closedBall_of_precomp_precomp_eq`.
* `StrongDual.exists_norm_le_and_forall_norm_sub_lt`: simultaneous norm approximation on a closed
  ball for finitely many operators whose bidual adjoints send `Φ` into canonical images.
* `StrongDual.exists_neBot_eventually_norm_le_and_forall_tendsto`: proper filter on a closed ball
  approximating an arbitrary family of operators whose bidual adjoints send `Φ` into canonical
  images.
-/

public section

open Filter Metric NormedSpace Set
open scoped Topology

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace ContinuousLinearMap

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If `Φ ∈ E**` has `‖Φ‖ ≤ r` and the bidual adjoint of `T : E →L[𝕜] F` sends `Φ` to the canonical
image of `y ∈ F`, then `y` lies in the norm closure of `T '' closedBall 0 r`. -/
theorem mem_closure_image_closedBall_of_precomp_precomp_eq (T : E →L[𝕜] F)
    {Φ : StrongDual 𝕜 (StrongDual 𝕜 E)} {r : ℝ} (hr : ‖Φ‖ ≤ r) {y : F}
    (hy : precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) Φ =
      inclusionInDoubleDual 𝕜 F y) :
    y ∈ closure (T '' closedBall 0 r) :=
  (T.mem_closure_image_closedBall_iff ((norm_nonneg Φ).trans hr)).2 fun g ↦ by
    have hg : g y = Φ (g.comp T) := by
      simpa only [precomp_apply, comp_apply, dual_def] using congr($(hy.symm) g)
    rw [hg]
    exact (Φ.le_opNorm (g.comp T)).trans (mul_le_mul_of_nonneg_right hr (norm_nonneg _))

/-- Pointwise form of `mem_closure_image_closedBall_of_precomp_precomp_eq`: if `‖Φ‖ ≤ r` and
`Φ (f ∘ T) = f y` for every `f ∈ F*`, then `y ∈ closure (T '' closedBall 0 r)`. -/
theorem mem_closure_image_closedBall_of_forall_apply_comp_eq (T : E →L[𝕜] F)
    {Φ : StrongDual 𝕜 (StrongDual 𝕜 E)} {r : ℝ} (hr : ‖Φ‖ ≤ r) {y : F}
    (hy : ∀ f : StrongDual 𝕜 F, Φ (f.comp T) = f y) :
    y ∈ closure (T '' closedBall 0 r) :=
  T.mem_closure_image_closedBall_of_precomp_precomp_eq hr <|
    ext fun f ↦ by simpa only [precomp_apply, comp_apply, dual_def] using hy f

end ContinuousLinearMap

namespace StrongDual

/-- Simultaneous norm approximation from a bidual element: if `Φ ∈ E**` satisfies `‖Φ‖ ≤ r` and
`Φ (f ∘ S i) = f (z i)` for every `i` in a finite index type and every `f ∈ (Z i)*`, then for every
`ε > 0` there is `x : E` with `‖x‖ ≤ r` and `‖S i x - z i‖ < ε` for all `i`. -/
theorem exists_norm_le_and_forall_norm_sub_lt
    (Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) {ι : Type*} [Finite ι] {Z : ι → Type*}
    [∀ i, SeminormedAddCommGroup (Z i)] [∀ i, NormedSpace 𝕜 (Z i)]
    (S : ∀ i, E →L[𝕜] Z i) (z : ∀ i, Z i)
    (hz : ∀ i (f : StrongDual 𝕜 (Z i)), Φ (f.comp (S i)) = f (z i))
    {r : ℝ} (hr : ‖Φ‖ ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : E, ‖x‖ ≤ r ∧ ∀ i, ‖S i x - z i‖ < ε := by
  cases nonempty_fintype ι
  classical
  have hmem : z ∈ closure ((ContinuousLinearMap.pi S) '' closedBall 0 r) := by
    refine (ContinuousLinearMap.pi S).mem_closure_image_closedBall_of_forall_apply_comp_eq hr
      fun F ↦ ?_
    have hF : F.comp (ContinuousLinearMap.pi S) =
        ∑ i, (F.comp (.single 𝕜 Z i)).comp (S i) := by
      ext x
      rw [ContinuousLinearMap.comp_apply,
        ← ContinuousLinearMap.sum_comp_single (L := F) (v := ContinuousLinearMap.pi S x)]
      simp
    rw [hF, map_sum]
    simpa only [hz] using ContinuousLinearMap.sum_comp_single (L := F) (v := z)
  obtain ⟨_, ⟨x, hx, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1 hmem ε hε
  rw [dist_comm, dist_eq_norm] at hdist
  exact ⟨x, mem_closedBall_zero_iff.1 hx, fun i ↦ by
    simpa only [Pi.sub_apply, ContinuousLinearMap.pi_apply] using (pi_norm_lt_iff hε).1 hdist i⟩

/-- Simultaneous filter approximation from a bidual element: if `Φ ∈ E**` satisfies `‖Φ‖ ≤ r` and
`Φ (f ∘ S k) = f (z k)` for every `k` in an arbitrary index type and every `f ∈ (Z k)*`, then there
is a proper filter on `E` eventually bounded in norm by `r` along which `S k x → z k` for every
`k`. -/
theorem exists_neBot_eventually_norm_le_and_forall_tendsto
    (Φ : StrongDual 𝕜 (StrongDual 𝕜 E)) {κ : Type*} {Z : κ → Type*}
    [∀ k, SeminormedAddCommGroup (Z k)] [∀ k, NormedSpace 𝕜 (Z k)]
    (S : ∀ k, E →L[𝕜] Z k) (z : ∀ k, Z k)
    (hz : ∀ k (f : StrongDual 𝕜 (Z k)), Φ (f.comp (S k)) = f (z k))
    {r : ℝ} (hr : ‖Φ‖ ≤ r) :
    ∃ l : Filter E, l.NeBot ∧ (∀ᶠ x in l, ‖x‖ ≤ r) ∧ ∀ k, Tendsto (S k) l (𝓝 (z k)) := by
  obtain ⟨l, hl, hle, ht⟩ :=
    (TauCeti.exists_neBot_tendsto_iff_forall_finset_dist_lt (p := fun x : E ↦ ‖x‖ ≤ r)
      (F := fun k x ↦ ‖S k x - z k‖) (x := fun _ ↦ (0 : ℝ))).2 fun s ε hε ↦ by
    obtain ⟨x, hx, happrox⟩ := Φ.exists_norm_le_and_forall_norm_sub_lt
      (fun k : s ↦ S k.val) (fun k : s ↦ z k.val) (fun k ↦ hz k.val) hr hε
    exact ⟨x, hx, fun k hk ↦ by
      simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)] using happrox ⟨k, hk⟩⟩
  exact ⟨l, hl, hle, fun k ↦ tendsto_iff_norm_sub_tendsto_zero.2 (ht k)⟩

end StrongDual
