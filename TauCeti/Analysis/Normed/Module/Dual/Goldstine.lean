/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.DoubleDual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakSpace
import TauCeti.Analysis.LocallyConvex.WeakDual.Basic
import TauCeti.Analysis.Normed.Module.DoubleDual
import TauCeti.Analysis.Normed.Module.Dual.Basic
import TauCeti.Analysis.Normed.Module.Dual.Functoriality
import TauCeti.Topology.MetricSpace.SimultaneousApproximation

/-!
# Goldstine's theorem

**Goldstine's theorem** says that the canonical embedding of a normed space `E` into its bidual
maps the closed unit ball of `E` onto a weak-star dense subset of the closed unit ball of the
bidual. We prove it for every closed ball: the weak-star closure of the image of
`closedBall x r` under `NormedSpace.inclusionInDoubleDualWeak` is the closed ball of radius `r`
about the image of `x`. In particular `E` is weak-star dense in its bidual.

No completeness or separability is assumed, and seminormed spaces are allowed. Together with
Banach–Alaoglu (`WeakDual.isCompact_closedBall`), Goldstine's theorem relates weak compactness
of the unit ball of `E` to reflexivity of `E`. Combined with Mazur's theorem that weak and norm
closures of convex sets agree (`Convex.toWeakSpace_closure`), it converts bidual operator
equations `T** M = J y` with `‖M‖ ≤ C` into norm approximation inside `T '' closedBall 0 C`,
simultaneously across any family of bounded operators.

## Main results

* `NormedSpace.closure_image_inclusionInDoubleDualWeak_closedBall`: Goldstine's theorem.
* `NormedSpace.closure_image_inclusionInDoubleDualWeak_closedBall_zero_one`: its unit-ball form.
* `NormedSpace.denseRange_inclusionInDoubleDualWeak`: `E` is weak-star dense in its bidual.
* `ContinuousLinearMap.mem_closure_image_closedBall_of_precomp_precomp_eq`: if `T** M = J y`
  with `‖M‖ ≤ C`, then `y ∈ closure (T '' closedBall 0 C)`.
* `StrongDual.exists_neBot_tendsto_of_forall_precomp_precomp_eq`: simultaneous norm
  approximation along a bounded proper filter for any family of operators with `T_k** M = J y_k`.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, Theorem 2.6.26.
-/

public section

open Metric RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

namespace NormedSpace

variable (𝕜 E)

/-- **Goldstine's theorem.** The weak-star closure of the image of the closed ball `closedBall x r`
under the canonical embedding into the bidual is the closed ball of radius `r` about the image
of `x`. -/
theorem closure_image_inclusionInDoubleDualWeak_closedBall (x : E) (r : ℝ) :
    closure (inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' closedBall x r)) =
      WeakDual.toStrongDual ⁻¹' closedBall (inclusionInDoubleDual 𝕜 E x) r := by
  -- The real structure on `E` gives convexity of balls.
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := .of_algebraMap_smul fun _ _ ↦ rfl
  set S := inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' closedBall x r)
  have hS : S ⊆ WeakDual.toStrongDual ⁻¹' closedBall (inclusionInDoubleDual 𝕜 E x) r := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    -- The bidual's metric is not reducibly the one of its normed group, so name the type.
    rw [Set.mem_preimage, inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply,
      StrongDual.toStrongDual_toWeakDual,
      mem_closedBall_iff_norm (E := StrongDual 𝕜 (StrongDual 𝕜 E)),
      ← map_sub (inclusionInDoubleDual 𝕜 E) y x]
    exact (double_dual_bound 𝕜 E _).trans (mem_closedBall_iff_norm.1 hy)
  refine (closure_minimal hS (WeakDual.isClosed_closedBall _ _)).antisymm fun φ hφ ↦ ?_
  -- A point `φ` of the bidual ball outside the weak-star closure is separated from it by
  -- Hahn–Banach, through a weak-star continuous functional, which is evaluation at some `f` in
  -- the dual. `StrongDual.re_apply_add_mul_norm_le` bounds `re (f x) + r * ‖f‖` by the separating
  -- constant, while `φ` lying in the ball bounds `re (φ f)` by `re (f x) + r * ‖f‖`, which
  -- contradicts the separation.
  by_contra hφS
  have hconv : Convex ℝ S := by
    simp only [S, Set.image_image]
    exact (convex_closedBall x r).linear_image
      (((inclusionInDoubleDualWeak 𝕜 E).toLinearMap ∘ₗ
        (toWeakSpace 𝕜 E).toLinearMap).restrictScalars ℝ)
  obtain ⟨l, u, hl, hlφ⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := 𝕜) hconv.closure isClosed_closure hφS
  -- Every weak-star continuous functional on the bidual is evaluation at a point of the dual.
  obtain ⟨f, hf⟩ := WeakDual.exists_forall_apply_eq_apply l
  have hfu : ∀ y ∈ closedBall x r, re (f y) ≤ u := fun y hy ↦ by
    have := (hl _ (subset_closure ⟨_, ⟨y, hy, rfl⟩, rfl⟩)).le
    rwa [hf, inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply,
      StrongDual.toWeakDual_apply, dual_def] at this
  have hfx := StrongDual.re_apply_add_mul_norm_le (dist_nonneg.trans hφ) hfu
  -- On the other hand `re (φ f) ≤ re (f x) + ‖φ - J x‖ * ‖f‖ ≤ re (f x) + r * ‖f‖`.
  have hφf : re (φ f) ≤ re (f x) + r * ‖f‖ := by
    have hφ' := (mem_closedBall_iff_norm (E := StrongDual 𝕜 (StrongDual 𝕜 E))).1 hφ
    have key := (re_le_norm _).trans
      (((WeakDual.toStrongDual φ - inclusionInDoubleDual 𝕜 E x).le_opNorm f).trans
        (mul_le_mul_of_nonneg_right hφ' (norm_nonneg f)))
    rw [sub_apply, dual_def, WeakDual.toStrongDual_apply, map_sub] at key
    linarith
  rw [hf] at hlφ
  exact (hlφ.trans_le hφf).not_ge hfx

/-- **Goldstine's theorem**, unit-ball form: the closed unit ball of `E` has weak-star dense
image in the closed unit ball of its bidual. -/
theorem closure_image_inclusionInDoubleDualWeak_closedBall_zero_one :
    closure (inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' closedBall 0 1)) =
      WeakDual.toStrongDual ⁻¹' closedBall 0 1 := by
  simpa using closure_image_inclusionInDoubleDualWeak_closedBall 𝕜 E 0 1

/-- A normed space is weak-star dense in its bidual. -/
theorem denseRange_inclusionInDoubleDualWeak : DenseRange (inclusionInDoubleDualWeak 𝕜 E) := by
  intro φ
  refine closure_mono (Set.image_subset_range _ (toWeakSpace 𝕜 E '' closedBall 0
    ‖WeakDual.toStrongDual φ‖)) ?_
  rw [closure_image_inclusionInDoubleDualWeak_closedBall, map_zero]
  exact (mem_closedBall_zero_iff (E := StrongDual 𝕜 (StrongDual 𝕜 E))).2 le_rfl

end NormedSpace

namespace ContinuousLinearMap

variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- If the bidual adjoint `T**` of `T : E →L[𝕜] F` sends an element `M` of the bidual of `E` with
`‖M‖ ≤ C` to the canonical bidual image of `y : F`, then `y` belongs to the norm closure of
`T '' closedBall 0 C`: Goldstine's theorem places `y` in the weak closure of that convex image,
which coincides with its norm closure. -/
theorem mem_closure_image_closedBall_of_precomp_precomp_eq
    (T : E →L[𝕜] F) {M : StrongDual 𝕜 (StrongDual 𝕜 E)} {C : ℝ} (hM : ‖M‖ ≤ C) {y : F}
    (hy : precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) M =
      NormedSpace.inclusionInDoubleDual 𝕜 F y) :
    y ∈ closure (T '' closedBall 0 C) := by
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  let : IsScalarTower ℝ 𝕜 E := .of_algebraMap_smul fun _ _ ↦ rfl
  let : IsScalarTower ℝ 𝕜 F := .of_algebraMap_smul fun _ _ ↦ rfl
  -- Goldstine places `M` in the weak-star closure of the ball of radius `C`.
  have hMcl : StrongDual.toWeakDual M ∈ closure
      (NormedSpace.inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' closedBall 0 C)) := by
    rw [NormedSpace.closure_image_inclusionInDoubleDualWeak_closedBall, map_zero,
      Set.mem_preimage, StrongDual.toStrongDual_toWeakDual]
    exact (mem_closedBall_zero_iff (E := StrongDual 𝕜 (StrongDual 𝕜 E))).2 hM
  -- Push forward along the weak-star continuous bidual adjoint `T**`.
  let f : WeakDual 𝕜 (StrongDual 𝕜 E) → WeakDual 𝕜 (StrongDual 𝕜 F) := fun Φ ↦
    StrongDual.toWeakDual
      (precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) (WeakDual.toStrongDual Φ))
  have hfM : f (StrongDual.toWeakDual M) ∈ closure (f ''
      (NormedSpace.inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' closedBall 0 C))) :=
    T.continuous_toWeakDual_precomp_precomp.continuousOn.image_closure ⟨_, hMcl, rfl⟩
  have hfim : f '' (NormedSpace.inclusionInDoubleDualWeak 𝕜 E ''
      (toWeakSpace 𝕜 E '' closedBall 0 C)) =
      NormedSpace.inclusionInDoubleDualWeak 𝕜 F ''
        (toWeakSpace 𝕜 F '' (T '' closedBall 0 C)) := by
    ext ψ
    simp only [Set.mem_image, f]
    constructor
    · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨T x, ⟨x, hx, rfl⟩, rfl⟩,
        (T.toWeakDual_precomp_precomp_inclusionInDoubleDualWeak x).symm⟩
    · rintro ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩,
        T.toWeakDual_precomp_precomp_inclusionInDoubleDualWeak x⟩
  have hfy : f (StrongDual.toWeakDual M) =
      NormedSpace.inclusionInDoubleDualWeak 𝕜 F (toWeakSpace 𝕜 F y) := by
    dsimp [f]
    rw [hy, NormedSpace.inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply]
  rw [hfim, hfy] at hfM
  -- Pull back to the weak topology of `F`, where weak and norm closures agree on convex sets.
  have hweak : toWeakSpace 𝕜 F y ∈ closure (toWeakSpace 𝕜 F '' (T '' closedBall 0 C)) := by
    rw [(NormedSpace.isInducing_inclusionInDoubleDualWeak 𝕜 F).closure_eq_preimage_closure_image]
    exact hfM
  have hconv : Convex ℝ (T '' closedBall (0 : E) C) :=
    (convex_closedBall 0 C).linear_image ((T : E →ₗ[𝕜] F).restrictScalars ℝ)
  rw [← hconv.toWeakSpace_closure 𝕜] at hweak
  exact (toWeakSpace 𝕜 F).injective.mem_set_image.1 hweak

end ContinuousLinearMap

namespace StrongDual

/-- If an element `M` of the bidual of `E` with `‖M‖ ≤ C` is sent by the bidual adjoint of every
operator `T k : E →L[𝕜] Y k` to the canonical bidual image of `y k`, then there is a proper filter
on `E`, eventually bounded in norm by `C`, along which `T k` tends in norm to `y k` for all `k`. -/
theorem exists_neBot_tendsto_of_forall_precomp_precomp_eq {κ : Type*} {Y : κ → Type*}
    [∀ k, SeminormedAddCommGroup (Y k)] [∀ k, NormedSpace 𝕜 (Y k)]
    (M : StrongDual 𝕜 (StrongDual 𝕜 E)) {C : ℝ} (hM : ‖M‖ ≤ C)
    (T : ∀ k, E →L[𝕜] Y k) (y : ∀ k, Y k)
    (hT : ∀ k, ContinuousLinearMap.precomp 𝕜
        (ContinuousLinearMap.precomp 𝕜 (T k) : StrongDual 𝕜 (Y k) →L[𝕜] StrongDual 𝕜 E) M =
      NormedSpace.inclusionInDoubleDual 𝕜 (Y k) (y k)) :
    ∃ l : Filter E, l.NeBot ∧ (∀ᶠ x in l, ‖x‖ ≤ C) ∧ ∀ k, Filter.Tendsto (T k) l (nhds (y k)) := by
  suffices ∃ l : Filter E, l.NeBot ∧ (∀ᶠ x in l, ‖x‖ ≤ C) ∧
      ∀ k, Filter.Tendsto (fun x ↦ ‖T k x - y k‖) l (nhds 0) by
    simpa only [← tendsto_iff_norm_sub_tendsto_zero] using this
  rw [TauCeti.exists_neBot_tendsto_iff_forall_finset_dist_lt]
  intro s ε hε
  classical
  let Φ : E →L[𝕜] ∀ k : s, Y k.1 := ContinuousLinearMap.pi fun k : s ↦ T k.1
  let z : ∀ k : s, Y k.1 := fun k ↦ y k.1
  have hΦ : ContinuousLinearMap.precomp 𝕜
      (ContinuousLinearMap.precomp 𝕜 Φ : StrongDual 𝕜 (∀ k : s, Y k.1) →L[𝕜] StrongDual 𝕜 E) M =
      NormedSpace.inclusionInDoubleDual 𝕜 (∀ k : s, Y k.1) z := by
    ext g
    have hg : g.comp Φ = ∑ k : s, (g.comp (.single 𝕜 (fun k : s ↦ Y k.1) k)).comp (T k.1) := by
      ext x
      simpa [Φ] using (ContinuousLinearMap.sum_comp_single (L := g) (v := Φ x)).symm
    have hkey (k : s) : M ((g.comp (.single 𝕜 (fun k : s ↦ Y k.1) k)).comp (T k.1)) =
        g.comp (.single 𝕜 (fun k : s ↦ Y k.1) k) (y k.1) :=
      congr($(hT k.1) (g.comp (.single 𝕜 (fun k : s ↦ Y k.1) k)))
    rw [ContinuousLinearMap.precomp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.precomp_apply, hg, map_sum, NormedSpace.dual_def]
    simp only [hkey]
    exact ContinuousLinearMap.sum_comp_single (L := g) (v := z)
  obtain ⟨_, ⟨x, hx, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1
    (Φ.mem_closure_image_closedBall_of_precomp_precomp_eq hM hΦ) ε hε
  refine ⟨x, mem_closedBall_zero_iff.1 hx, fun k hk ↦ ?_⟩
  rw [Real.dist_0_eq_abs, abs_norm, norm_sub_rev]
  rw [dist_eq_norm] at hdist
  exact (norm_le_pi_norm (z - Φ x) ⟨k, hk⟩).trans_lt hdist

end StrongDual
