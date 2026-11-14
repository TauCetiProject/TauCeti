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

/-!
# Goldstine's theorem and norm approximation from the bidual

**Goldstine's theorem** says that the canonical embedding of a normed space `E` into its bidual
maps the closed unit ball of `E` onto a weak-star dense subset of the closed unit ball of the
bidual. We prove it for every closed ball: the weak-star closure of the image of
`closedBall x r` under `NormedSpace.inclusionInDoubleDualWeak` is the closed ball of radius `r`
about the image of `x`. In particular `E` is weak-star dense in its bidual.

No completeness or separability is assumed, and seminormed spaces are allowed. Together with
Banach–Alaoglu (`WeakDual.isCompact_closedBall`), Goldstine's theorem relates weak compactness
of the unit ball of `E` to reflexivity of `E`.

Combined with weak-star continuity of bidual adjoints and convex weak-norm closure
(`Convex.toWeakSpace_closure`), Goldstine's theorem turns exact operator identities solved in a
bidual ball into norm-bounded approximate solutions in the original space: if `Φ ∈ E**` has
`‖Φ‖ ≤ r` and `T** Φ = J_F y`, then `y ∈ closure (T '' closedBall 0 r)`. Applied to a finite
product, finitely many equations `Sᵢ** Φ = J (zᵢ)` can be approximately solved simultaneously in
norm by a single vector of norm at most `r` (used to construct bounded approximate identities and
bounded approximate diagonals from bidual witnesses).

## Main results

* `NormedSpace.closure_image_inclusionInDoubleDualWeak_closedBall`: Goldstine's theorem.
* `NormedSpace.closure_image_inclusionInDoubleDualWeak_closedBall_zero_one`: its unit-ball form.
* `NormedSpace.denseRange_inclusionInDoubleDualWeak`: `E` is weak-star dense in its bidual.
* `ContinuousLinearMap.mem_closure_image_closedBall_of_precomp_precomp_eq`: if `‖Φ‖ ≤ r` and
  `T** Φ = J_F y`, then `y ∈ closure (T '' closedBall 0 r)`.
* `StrongDual.exists_norm_le_and_forall_norm_sub_lt`: simultaneous norm approximation on a closed
  ball for finitely many operators whose bidual adjoints send `Φ` into canonical images.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.6, Theorem 2.6.26.
-/

public section

open Metric NormedSpace RCLike Set

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

/-- If `Φ ∈ E**` has `‖Φ‖ ≤ r` and the bidual adjoint of `T : E →L[𝕜] F` sends `Φ` to the canonical
image of `y ∈ F`, then `y` lies in the norm closure of `T '' closedBall 0 r`. -/
theorem mem_closure_image_closedBall_of_precomp_precomp_eq (T : E →L[𝕜] F)
    {Φ : StrongDual 𝕜 (StrongDual 𝕜 E)} {r : ℝ} (hr : ‖Φ‖ ≤ r) {y : F}
    (hy : precomp 𝕜 (precomp 𝕜 T : StrongDual 𝕜 F →L[𝕜] StrongDual 𝕜 E) Φ =
      inclusionInDoubleDual 𝕜 F y) :
    y ∈ closure (T '' closedBall 0 r) := by
  let : NormedSpace ℝ E := .restrictScalars ℝ 𝕜 E
  let : IsScalarTower ℝ 𝕜 E := .restrictScalars ℝ 𝕜 E
  let : NormedSpace ℝ F := .restrictScalars ℝ 𝕜 F
  let : IsScalarTower ℝ 𝕜 F := .restrictScalars ℝ 𝕜 F
  -- Goldstine places `Φ` in the weak-star closure of the `r`-ball of `E`; `T**` pushes this to
  -- the weak-star bidual of `F`.
  have hΦ : StrongDual.toWeakDual Φ ∈
      closure (inclusionInDoubleDualWeak 𝕜 E '' (toWeakSpace 𝕜 E '' closedBall 0 r)) := by
    rw [closure_image_inclusionInDoubleDualWeak_closedBall, map_zero, mem_preimage,
      StrongDual.toStrongDual_toWeakDual]
    exact (mem_closedBall_zero_iff (E := StrongDual 𝕜 (StrongDual 𝕜 E))).2 hr
  have himg := image_closure_subset_closure_image T.continuous_toWeakDual_precomp_precomp
    (mem_image_of_mem _ hΦ)
  simp only [StrongDual.toStrongDual_toWeakDual, hy, image_image,
    T.toWeakDual_precomp_precomp_inclusionInDoubleDualWeak] at himg
  have hy' : inclusionInDoubleDualWeak 𝕜 F (toWeakSpace 𝕜 F y) ∈
      closure (inclusionInDoubleDualWeak 𝕜 F '' (toWeakSpace 𝕜 F '' (T '' closedBall 0 r))) := by
    simpa only [inclusionInDoubleDualWeak_apply, LinearEquiv.symm_apply_apply, image_image]
      using himg
  -- Pull back along the inducing canonical map into `F**`, then upgrade weak closure to norm
  -- closure by convexity of `T '' closedBall 0 r`.
  rw [← mem_preimage,
    ← (isInducing_inclusionInDoubleDualWeak 𝕜 F).closure_eq_preimage_closure_image] at hy'
  have hconv : Convex ℝ (T '' closedBall 0 r) :=
    (convex_closedBall 0 r).linear_image ((T : E →ₗ[𝕜] F).restrictScalars ℝ)
  rw [← hconv.toWeakSpace_closure 𝕜] at hy'
  exact (toWeakSpace 𝕜 F).injective.mem_set_image.1 hy'

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
  exact ⟨x, mem_closedBall_zero_iff.1 hx, (pi_norm_lt_iff hε).1 hdist⟩

end StrongDual
