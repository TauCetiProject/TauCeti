/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pompeiu.Holder.Beurling
public import TauCeti.Analysis.Holder.Localization
public import TauCeti.Analysis.Holder.Product
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.MetricSpace.Contracting
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Normed.Ring.Units
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Beltrami equation with small `C^{k,α}` coefficient

Let `k : ℕ`, `0 < α < 1`, and let `μ` be a bounded `C^{k,α}` function on `ℂ` vanishing off the
closed disc `closedBall c r`. This file solves the Beltrami equation `\bar∂ψ = μ ∂ψ` when the
`C^{k,α}` norm of `μ` is small, with a solution `ψ` of class `C^{k+1,α}` on the disc that is
`C^{k+1}`-close to the identity there.

As in the case `k = 0` (`TauCeti.exists_conjWirtingerDeriv_eq_mul_wirtingerDeriv`), the solution
is `ψ = z + T h`, where `T` is the Cauchy transform and the source `h` is the fixed point of
`h = μ (1 + B h)`, with `B = ∂ T` the Beurling operator. Here the contraction runs on the Banach
space of `C^{k,α}` data supported in the disc (`TauCeti.isClosed_supportedCkHolderSubmodule`).
The Beurling operator `TauCeti.beurlingCkCLM` takes such data to the `C^{k,α}` fields of `B h`
on a larger disc. Multiplying by a fixed smooth cutoff turns them into an element of the global
space `CkHolderSpace k α ℂ ℂ` (`TauCeti.Beltrami.cutoffBeurlingCkCLM`), and multiplying by `μ`
with `ContinuousLinearMap.compCkHolder₂` gives the linear part of the fixed-point map,
`TauCeti.Beltrami.beltramiCkOperator`, whose operator norm is a fixed multiple of `‖μ‖`.

## Main results

* `TauCeti.isClosed_supportedCkHolderSubmodule`: the supported `C^{k,α}` subspace is closed, so it
  is a Banach space.
* `TauCeti.Beltrami.cutoffBeurlingCkCLM`: `h ↦ χ B h` as a bounded operator from `C^{k,α}` data
  supported in `closedBall c r` to `CkHolderSpace k α ℂ ℂ`, equal to `B h` on
  `closedBall c (r + 1)`.
* `TauCeti.Beltrami.beltramiCkOperator`: `h ↦ μ χ B h` on the supported space, with operator norm
  at most a fixed multiple of `‖μ‖`.
* `TauCeti.exists_ckHolder_conjWirtingerDeriv_eq_mul_wirtingerDeriv`: for `‖μ‖` below a threshold
  depending only on `k`, `α`, `c` and `r`, there is a supported source `h` with `‖h‖ ≤ 2 ‖μ‖`
  such that `ψ = z + T h` is globally `C^{k+1}`, solves `\bar∂ψ = μ ∂ψ` on `ℂ`, has derivatives of
  `T h` through order `k + 1` bounded by `C ‖μ‖` on the disc, has `D^{k+1} ψ` `α`-Hölder with
  constant `C ‖μ‖` there, and has an invertible strict derivative at every point of the disc.

## References

* L. V. Ahlfors, *Lectures on Quasiconformal Mappings*, 2nd ed., AMS University Lecture Series
  **38**, 2006, Chapter V.
* I. N. Vekua, *Generalized Analytic Functions*, Pergamon, 1962, Chapters I–II.
-/

public noncomputable section

open Complex Metric Set
open scoped NNReal ContDiff BoundedContinuousFunction

namespace TauCeti

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `ℂ`, as in
`TauCeti.beurlingCkCLM`. It is local, and no public statement mentions it. -/
private local instance instNormedAddCommGroupBoundedContinuousFunction {X : Type*}
    [TopologicalSpace X] (n : ℕ) : NormedAddCommGroup (X →ᵇ (ℂ [×n]→L[ℝ] ℂ)) :=
  inferInstance

/-- Shortcut instance for bounded continuous fields of `n`-multilinear maps on `ℂ`. It is local
for the same reason. -/
private local instance instNormedSpaceBoundedContinuousFunction {X : Type*} [TopologicalSpace X]
    (n : ℕ) : NormedSpace ℝ (X →ᵇ (ℂ [×n]→L[ℝ] ℂ)) :=
  inferInstance

section Closed

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The supported `C^{k,α}` subspace is closed, as an intersection of kernels of evaluations. -/
theorem isClosed_supportedCkHolderSubmodule (k : ℕ) (α : ℝ≥0) (s : Set E) :
    IsClosed (supportedCkHolderSubmodule (F := F) k α s : Set (CkHolderSpace k α E F)) := by
  have h : (supportedCkHolderSubmodule (F := F) k α s : Set (CkHolderSpace k α E F)) =
      ⋂ x ∈ sᶜ, (fun f ↦ CkHolderSpace.toBoundedContinuousFunctionCLM f x) ⁻¹' {0} := by
    ext f
    simp
  rw [h]
  exact isClosed_biInter fun x _ ↦ isClosed_singleton.preimage
    ((continuous_eval_const x).comp (ContinuousLinearMap.continuous _))

/-- The supported `C^{k,α}` subspace is a Banach space when the codomain is. -/
instance instCompleteSpaceSupportedCkHolderSubmodule [CompleteSpace F] (k : ℕ) (α : ℝ≥0)
    (s : Set E) : CompleteSpace (supportedCkHolderSubmodule (F := F) k α s) :=
  (isClosed_supportedCkHolderSubmodule k α s).completeSpace_coe

end Closed

namespace Beltrami

variable {k : ℕ} {α : ℝ≥0} {c : ℂ} {r : ℝ}

/-- The fixed cutoff: a smooth bump equal to one on `closedBall c (r + 1)` and vanishing off
`ball c (r + 2)`. -/
private def bump (c : ℂ) (hr : 0 ≤ r) : ContDiffBump c :=
  ⟨r + 1, r + 2, by linarith, by linarith⟩

private theorem exists_bound_bump (c : ℂ) (hr : 0 ≤ r) (n : ℕ) :
    ∃ N : ℝ≥0, ∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i (bump c hr) x‖ ≤ N := by
  obtain ⟨C, hC0, hC⟩ :=
    (bump c hr).hasCompactSupport.exists_bound_iteratedFDeriv (bump c hr).contDiff n
  exact ⟨⟨C, hC0⟩, hC⟩

/-- A common bound for the derivatives of the cutoff through order `n`. -/
private def bumpBound (c : ℂ) (hr : 0 ≤ r) (n : ℕ) : ℝ≥0 :=
  (exists_bound_bump c hr n).choose

private theorem norm_iteratedFDeriv_bump_le (hr : 0 ≤ r) {n i : ℕ} (hi : i ≤ n) (x : ℂ) :
    ‖iteratedFDeriv ℝ i (bump c hr) x‖ ≤ bumpBound c hr n :=
  (exists_bound_bump c hr n).choose_spec i hi x

private theorem tsupport_bump_subset (hr : 0 ≤ r) :
    tsupport (bump c hr) ⊆ ball c (r + 3) := by
  rw [ContDiffBump.tsupport_eq]
  exact closedBall_subset_ball (by simp only [bump]; linarith)

private theorem r3_nonneg (hr : 0 ≤ r) : 0 ≤ r + 3 := by linarith

private theorem hasCompactSupport_coe
    (h : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) :
    HasCompactSupport (h : CkHolderSpace k α ℂ ℂ) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r)
    (support_subset_of_mem_supportedCkHolderSubmodule h.property)

variable (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)

private theorem norm_iteratedFDeriv_beurling_le
    (h : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) {i : ℕ} (hi : i ≤ k)
    {x : ℂ} (hx : x ∈ closedBall c (r + 3)) :
    ‖iteratedFDeriv ℝ i
        (fun w ↦ wirtingerDeriv (cauchyTransform (h : CkHolderSpace k α ℂ ℂ)) w 1) x‖ ≤
      ‖beurlingCkCLM k hα hα1 hr (r3_nonneg hr) h‖ := by
  rw [← beurlingCkCLM_apply_fst k hα hα1 hr (r3_nonneg hr) h ⟨i, by omega⟩ ⟨x, hx⟩]
  set b := beurlingCkCLM k hα hα1 hr (r3_nonneg hr) h
  calc ‖b.1 ⟨i, by omega⟩ ⟨x, hx⟩‖ ≤ ‖b.1 ⟨i, by omega⟩‖ :=
        BoundedContinuousFunction.norm_coe_le_norm _ _
    _ ≤ ‖b.1‖ := norm_le_pi_norm b.1 _
    _ ≤ ‖b‖ := norm_fst_le b

private theorem holderOnWith_iteratedFDeriv_beurling
    (h : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) :
    HolderOnWith ‖beurlingCkCLM k hα hα1 hr (r3_nonneg hr) h‖₊ α
      (iteratedFDeriv ℝ k
        (fun w ↦ wirtingerDeriv (cauchyTransform (h : CkHolderSpace k α ℂ ℂ)) w 1))
      (closedBall c (r + 3)) := by
  rw [← HolderWith.restrict_iff]
  have he : (closedBall c (r + 3)).domRestrict (iteratedFDeriv ℝ k
      (fun w ↦ wirtingerDeriv (cauchyTransform (h : CkHolderSpace k α ℂ ℂ)) w 1)) =
      ⇑(beurlingCkCLM k hα hα1 hr (r3_nonneg hr) h).2 :=
    funext fun x ↦ (beurlingCkCLM_apply_snd k hα hα1 hr (r3_nonneg hr) h x).symm
  rw [he]
  exact (HolderSpace.holderWith_nnnorm _).mono (by
    rw [← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm]
    exact norm_snd_le _)

/-- The cut-off Beurling transform of a supported source, as an element of the global space. -/
private def cutoffBeurling
    (h : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) :
    CkHolderSpace k α ℂ ℂ :=
  CkHolderSpace.cutoff
    (f := fun w ↦ wirtingerDeriv (cauchyTransform (h : CkHolderSpace k α ℂ ℂ)) w 1)
    (M := ‖beurlingCkCLM k hα hα1 hr (r3_nonneg hr) h‖₊)
    (H := ‖beurlingCkCLM k hα hα1 hr (r3_nonneg hr) h‖₊)
    (N := bumpBound c hr (k + 1))
    ((hasCompactSupport_coe h).contDiff_wirtingerDeriv_cauchyTransform_of_holderWith hα hα1
      (h : CkHolderSpace k α ℂ ℂ).contDiff
      (h : CkHolderSpace k α ℂ ℂ).memHolder_iteratedFDeriv.holderWith).contDiffOn
    (bump c hr).contDiff isOpen_ball (convex_ball c (r + 3)) (tsupport_bump_subset hr) hα1.le
    (fun _ hi _ hx ↦ norm_iteratedFDeriv_beurling_le hα hα1 hr h hi (ball_subset_closedBall hx))
    (fun _ hi x ↦ norm_iteratedFDeriv_bump_le hr hi x)
    ((holderOnWith_iteratedFDeriv_beurling hα hα1 hr h).mono ball_subset_closedBall)

private theorem cutoffBeurling_apply
    (h : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) (x : ℂ) :
    cutoffBeurling hα hα1 hr h x =
      bump c hr x • wirtingerDeriv (cauchyTransform (h : CkHolderSpace k α ℂ ℂ)) x 1 :=
  CkHolderSpace.cutoff_apply _ _ _ _ _ _ _ _ _ x

private theorem norm_cutoffBeurling_le
    (h : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) :
    ‖cutoffBeurling hα hα1 hr h‖ ≤
      (2 : ℝ) ^ k * bumpBound c hr (k + 1) * (k + 8) *
        ‖beurlingCkCLM (F := ℂ) (c := c) k hα hα1 hr (r3_nonneg hr)‖ * ‖h‖ := by
  refine (CkHolderSpace.norm_cutoff_le _ _ _ _ _ _ _ _ _).trans ?_
  simp only [coe_nnNorm]
  have hb := (beurlingCkCLM (F := ℂ) (c := c) k hα hα1 hr (r3_nonneg hr)).le_opNorm h
  calc
    _ = (2 : ℝ) ^ k * bumpBound c hr (k + 1) * (k + 8) *
        ‖beurlingCkCLM (F := ℂ) (c := c) k hα hα1 hr (r3_nonneg hr) h‖ := by ring
    _ ≤ _ := by
      rw [mul_assoc _ _ ‖h‖]
      gcongr

private theorem cutoffBeurling_apply_of_mem
    (f : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) {x : ℂ}
    (hx : x ∈ closedBall c (r + 3)) :
    cutoffBeurling hα hα1 hr f x =
      bump c hr x • (beurlingCkCLM k hα hα1 hr (r3_nonneg hr) f).1 0 ⟨x, hx⟩ 0 := by
  rw [cutoffBeurling_apply]
  exact congrArg _ (beurlingCkCLM_apply_fst_zero k hα hα1 hr (r3_nonneg hr) f ⟨x, hx⟩ 0).symm

private theorem cutoffBeurling_apply_of_notMem
    (f : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) {x : ℂ}
    (hx : x ∉ closedBall c (r + 3)) : cutoffBeurling hα hα1 hr f x = 0 := by
  rw [cutoffBeurling_apply, (bump c hr).zero_of_le_dist (by
    simp only [bump, mem_closedBall, not_le] at hx ⊢
    linarith), zero_smul]

/-- **The cut-off Beurling operator on supported `C^{k,α}` data.** For `0 < α < 1` and `0 ≤ r`,
it sends `C^{k,α}` data `h` supported in `closedBall c r` to `χ B h ∈ C^{k,α}(ℂ)`, where
`B h = ∂ (T h)` is the Beurling transform and `χ` is a fixed smooth cutoff, equal to one on
`closedBall c (r + 1)` and vanishing off `ball c (r + 2)`. It is real linear and bounded. -/
def cutoffBeurlingCkCLM (k : ℕ) (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r) :
    supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r) →L[ℝ]
      CkHolderSpace k α ℂ ℂ :=
  LinearMap.mkContinuous
    { toFun := cutoffBeurling hα hα1 hr
      map_add' := fun f g ↦ CkHolderSpace.ext fun x ↦ by
        by_cases hx : x ∈ closedBall c (r + 3)
        · simp only [cutoffBeurling_apply_of_mem hα hα1 hr _ hx, map_add, Prod.fst_add,
            Pi.add_apply, CkHolderSpace.coe_add, ← smul_add]
          rfl
        · simp [cutoffBeurling_apply_of_notMem hα hα1 hr _ hx]
      map_smul' := fun a f ↦ CkHolderSpace.ext fun x ↦ by
        by_cases hx : x ∈ closedBall c (r + 3)
        · simp only [cutoffBeurling_apply_of_mem hα hα1 hr _ hx, map_smul, Prod.smul_fst,
            Pi.smul_apply, CkHolderSpace.coe_smul, RingHom.id_apply, smul_comm a]
          rfl
        · simp [cutoffBeurling_apply_of_notMem hα hα1 hr _ hx] }
    ((2 : ℝ) ^ k * bumpBound c hr (k + 1) * (k + 8) *
      ‖beurlingCkCLM (F := ℂ) (c := c) k hα hα1 hr (r3_nonneg hr)‖)
    (norm_cutoffBeurling_le hα hα1 hr)

/-- On `closedBall c (r + 1)` the cut-off Beurling operator is the Beurling transform. -/
theorem cutoffBeurlingCkCLM_apply_of_mem
    (h : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) {z : ℂ}
    (hz : z ∈ closedBall c (r + 1)) :
    cutoffBeurlingCkCLM k hα hα1 hr h z =
      wirtingerDeriv (cauchyTransform (h : CkHolderSpace k α ℂ ℂ)) z 1 := by
  change cutoffBeurling hα hα1 hr h z = _
  rw [cutoffBeurling_apply, (bump c hr).one_of_mem_closedBall hz, one_smul]

/-- On `ball c (r + 1)` every derivative of the cut-off Beurling operator is that of the
Beurling transform. -/
theorem iteratedFDeriv_cutoffBeurlingCkCLM_of_mem
    (h : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) {z : ℂ}
    (hz : z ∈ ball c (r + 1)) (j : ℕ) :
    iteratedFDeriv ℝ j (cutoffBeurlingCkCLM k hα hα1 hr h) z =
      iteratedFDeriv ℝ j
        (fun w ↦ wirtingerDeriv (cauchyTransform (h : CkHolderSpace k α ℂ ℂ)) w 1) z :=
  CkHolderSpace.iteratedFDeriv_cutoff_eq _ _ _ _ _ _ _ _ _
    ((bump c hr).eventuallyEq_one_of_mem_ball hz) j

/-- The cut-off Beurling operator vanishes off `ball c (r + 2)`. -/
theorem cutoffBeurlingCkCLM_apply_eq_zero
    (h : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) {z : ℂ}
    (hz : r + 2 ≤ dist z c) : cutoffBeurlingCkCLM k hα hα1 hr h z = 0 := by
  change cutoffBeurling hα hα1 hr h z = _
  rw [cutoffBeurling_apply, (bump c hr).zero_of_le_dist hz, zero_smul]

/-- **The linear part of the Beltrami fixed-point map on `C^{k,α}` data.** For a coefficient
`μ` in the supported space, it is `h ↦ μ χ B h`, the product of `μ` with the cut-off Beurling
operator `TauCeti.Beltrami.cutoffBeurlingCkCLM`. It stays in the space of data supported in
`closedBall c r` because `μ` vanishes off that disc. -/
def beltramiCkOperator (k : ℕ) (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (μ : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) :
    supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r) →L[ℝ]
      supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r) :=
  (((ContinuousLinearMap.mul ℝ ℂ).compCkHolder₂ hα1.le (μ : CkHolderSpace k α ℂ ℂ)).comp
    (cutoffBeurlingCkCLM k hα hα1 hr)).codRestrict _ fun h ↦ by
      rw [mem_supportedCkHolderSubmodule_iff]
      intro x hx
      simp [mem_supportedCkHolderSubmodule_iff.mp μ.property x hx]

/-- The Beltrami operator is pointwise `μ` times the cut-off Beurling operator. -/
theorem beltramiCkOperator_apply
    (μ h : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) (z : ℂ) :
    (beltramiCkOperator k hα hα1 hr μ h : CkHolderSpace k α ℂ ℂ) z =
      (μ : CkHolderSpace k α ℂ ℂ) z * cutoffBeurlingCkCLM k hα hα1 hr h z := by
  simp [beltramiCkOperator]

/-- On the disc the Beltrami operator is `μ ∂ (T h)`. -/
theorem beltramiCkOperator_apply_of_mem
    (μ h : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) {z : ℂ}
    (hz : z ∈ closedBall c r) :
    (beltramiCkOperator k hα hα1 hr μ h : CkHolderSpace k α ℂ ℂ) z =
      (μ : CkHolderSpace k α ℂ ℂ) z *
        wirtingerDeriv (cauchyTransform (h : CkHolderSpace k α ℂ ℂ)) z 1 := by
  rw [beltramiCkOperator_apply, cutoffBeurlingCkCLM_apply_of_mem hα hα1 hr h
    (closedBall_subset_closedBall (by linarith) hz)]

/-- The operator norm of the Beltrami operator is at most a fixed multiple of `‖μ‖`. -/
theorem norm_beltramiCkOperator_le
    (μ : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) :
    ‖beltramiCkOperator k hα hα1 hr μ‖ ≤
      (k + 7) * 2 ^ k * ‖cutoffBeurlingCkCLM (c := c) k hα hα1 hr‖ * ‖μ‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h ↦ ?_
  rw [← Submodule.norm_coe]
  change ‖(ContinuousLinearMap.mul ℝ ℂ).compCkHolder₂ hα1.le (μ : CkHolderSpace k α ℂ ℂ)
    (cutoffBeurlingCkCLM k hα hα1 hr h)‖ ≤ _
  refine ((ContinuousLinearMap.mul ℝ ℂ).norm_compCkHolder₂_apply_le hα1.le _ _).trans ?_
  have hm : ‖ContinuousLinearMap.mul ℝ ℂ‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le _ _
  have hb := (cutoffBeurlingCkCLM (c := c) k hα hα1 hr).le_opNorm h
  rw [Submodule.norm_coe]
  calc
    _ ≤ (k + 7) * 2 ^ k * 1 * ‖μ‖ * (‖cutoffBeurlingCkCLM (c := c) k hα hα1 hr‖ * ‖h‖) := by
      gcongr
    _ = _ := by ring

end Beltrami

/-- The solution of `v + A k = k` for a linear part of norm at most `1 / 4` is the Neumann series
`(1 - A)⁻¹ v`, with `‖k‖ ≤ 2 ‖v‖`. -/
private theorem exists_add_apply_eq {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (v : X) (A : X →L[ℝ] X) (hA : ‖A‖ ≤ 4⁻¹) :
    ∃ k, v + A k = k ∧ ‖k‖ ≤ 2 * ‖v‖ := by
  have hA1 : ‖A‖ < 1 := by linarith
  refine ⟨Ring.inverse (1 - A) v, ?_, ?_⟩
  · have h := congrArg (fun L : X →L[ℝ] X ↦ L v)
      (Ring.mul_inverse_cancel (1 - A) ⟨Units.oneSub A hA1, rfl⟩)
    change Ring.inverse (1 - A) v - A (Ring.inverse (1 - A) v) = v at h
    nth_rewrite 1 [← h]
    rw [sub_add_cancel]
  · have hinv := NormedRing.norm_inverse_one_sub_le hA1
    have h1 : ‖(1 : X →L[ℝ] X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h2 : (1 - ‖A‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) two_pos]
      linarith
    calc ‖Ring.inverse (1 - A) v‖ ≤ ‖Ring.inverse (1 - A)‖ * ‖v‖ :=
          (Ring.inverse (1 - A)).le_opNorm v
      _ ≤ 2 * ‖v‖ := by gcongr; linarith

/-- A bounded `C^{k,α}` map is itself `α`-Hölder, with constant `3 ‖f‖`, for `α ≤ 1`. -/
private theorem holderWith_coe {k : ℕ} {α : ℝ≥0} (f : CkHolderSpace k α ℂ ℂ) (hα : α ≤ 1) :
    HolderWith (3 * ‖f‖₊) α f := by
  have h := f.holderWith_iteratedFDeriv_of_le hα (Nat.zero_le k)
  rw [iteratedFDeriv_zero_eq_comp] at h
  exact (Isometry.holderWith_comp_iff
    (continuousMultilinearCurryFin0 ℝ ℂ ℂ).symm.isometry).mp h

/-- The derivative of order `n + 1` of the identity is constant. -/
private theorem iteratedFDeriv_succ_id_eq (n : ℕ) (x y : ℂ) :
    iteratedFDeriv ℝ (n + 1) (id : ℂ → ℂ) x = iteratedFDeriv ℝ (n + 1) (id : ℂ → ℂ) y := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right, Function.comp_apply,
    Function.comp_apply]
  simp only [fderiv_id]
  rcases n with _ | n
  · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
  · rw [iteratedFDeriv_succ_const, Pi.zero_apply, Pi.zero_apply]

variable {k : ℕ} {α : ℝ≥0} {c : ℂ} {r : ℝ}

/-- The source of the Beltrami solution: a supported `h` with `‖h‖ ≤ 2 ‖μ‖` and
`h = μ (1 + ∂ (T h))` on `ℂ`, when the Beltrami operator of `μ` has norm at most `1 / 4`. -/
private theorem exists_source (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (μ : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r))
    (hA : ‖Beltrami.beltramiCkOperator k hα hα1 hr μ‖ ≤ 4⁻¹) :
    ∃ h : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r), ‖h‖ ≤ 2 * ‖μ‖ ∧
      ∀ z, (h : CkHolderSpace k α ℂ ℂ) z = (μ : CkHolderSpace k α ℂ ℂ) z *
        (1 + wirtingerDeriv (cauchyTransform (h : CkHolderSpace k α ℂ ℂ)) z 1) := by
  obtain ⟨h, hfix, hh⟩ := exists_add_apply_eq μ _ hA
  refine ⟨h, hh, fun z ↦ ?_⟩
  by_cases hz : z ∈ closedBall c r
  · have := congrArg (fun g : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r) ↦
      (g : CkHolderSpace k α ℂ ℂ) z) hfix
    simp only [Submodule.coe_add, CkHolderSpace.coe_add, Pi.add_apply,
      Beltrami.beltramiCkOperator_apply_of_mem hα hα1 hr _ _ hz] at this
    rw [← this]
    ring
  · rw [mem_supportedCkHolderSubmodule_iff.mp h.property z hz,
      mem_supportedCkHolderSubmodule_iff.mp μ.property z hz, zero_mul]

/-- Regularity of `T h` for a supported `C^{k,α}` source: it is globally `C^{k+1}` with
`\bar∂ T h = h`, and on the disc its derivatives through order `k + 1` and the Hölder constant of
its derivative of order `k + 1` are bounded by the norm of `TauCeti.cauchyTransformCkCLM h`. -/
private theorem cauchyTransform_regularity (hα : 0 < α) (hα1 : α < 1) (hr : 0 ≤ r)
    (h : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r)) :
    let T := cauchyTransform (h : CkHolderSpace k α ℂ ℂ)
    let D := cauchyTransformCkCLM (F := ℂ) (c := c) k hα hα1 hr hr
    ContDiff ℝ (k + 1 : ℕ) T ∧ (∀ z, conjWirtingerDeriv T z 1 = (h : CkHolderSpace k α ℂ ℂ) z) ∧
      (∀ i ≤ k + 1, ∀ z ∈ closedBall c r, ‖iteratedFDeriv ℝ i T z‖ ≤ ‖D h‖) ∧
      HolderOnWith ‖D h‖₊ α (iteratedFDeriv ℝ (k + 1) T) (closedBall c r) := by
  intro T D
  have hhs := support_subset_of_mem_supportedCkHolderSubmodule h.property
  refine ⟨(HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c r)
      hhs).contDiff_cauchyTransform_of_holderWith_iteratedFDeriv hα hα1
      (h : CkHolderSpace k α ℂ ℂ).contDiff
      (h : CkHolderSpace k α ℂ ℂ).memHolder_iteratedFDeriv.holderWith, fun z ↦ ?_,
    fun i hi z hz ↦ ?_, ?_⟩
  · -- `\bar∂ T h = h`, by the one-derivative Hölder gain on a disc containing `z`.
    obtain ⟨C₀, hC₀⟩ := exists_contDiffOn_holderOnWith_fderiv_pi_inv_smul_integral_sub_inv_smul
      (F := ℂ) hα hα1 c hr (dist_nonneg (x := z) (y := c))
    rw [show T = _ from funext (cauchyTransform_apply _)]
    exact (hC₀ (M := ‖(h : CkHolderSpace k α ℂ ℂ)‖₊) hhs (holderWith_coe _ hα1.le)
      (fun x ↦ (h : CkHolderSpace k α ℂ ℂ).norm_apply_le x)).2.2.2 z
      (mem_ball.mpr (lt_add_one _))
  · rw [← cauchyTransformCkCLM_apply_fst k hα hα1 hr hr h ⟨i, by omega⟩ ⟨z, hz⟩]
    calc ‖(D h).1 ⟨i, by omega⟩ ⟨z, hz⟩‖ ≤ ‖(D h).1 ⟨i, by omega⟩‖ :=
          BoundedContinuousFunction.norm_coe_le_norm _ _
      _ ≤ ‖(D h).1‖ := norm_le_pi_norm (D h).1 _
      _ ≤ ‖D h‖ := norm_fst_le (D h)
  · rw [← HolderWith.restrict_iff]
    have he : (closedBall c r).domRestrict (iteratedFDeriv ℝ (k + 1) T) = ⇑(D h).2 :=
      funext fun x ↦ (cauchyTransformCkCLM_apply_snd k hα hα1 hr hr h x).symm
    rw [he]
    exact (HolderSpace.holderWith_nnnorm _).mono (by
      rw [← NNReal.coe_le_coe, coe_nnNorm, coe_nnNorm]
      exact norm_snd_le _)

/-- Adding the identity does not change the Hölder constant of a derivative of order `n + 1`. -/
private theorem holderOnWith_iteratedFDeriv_id_add {n : ℕ} {T : ℂ → ℂ} {C : ℝ≥0} {s : Set ℂ}
    (hT : ContDiff ℝ (n + 1 : ℕ) T) (hH : HolderOnWith C α (iteratedFDeriv ℝ (n + 1) T) s) :
    HolderOnWith C α (iteratedFDeriv ℝ (n + 1) (fun w ↦ w + T w)) s := by
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  rw [show (fun w ↦ w + T w) = id + T from rfl,
    iteratedFDeriv_add_apply contDiff_id.contDiffAt hT.contDiffAt,
    iteratedFDeriv_add_apply contDiff_id.contDiffAt hT.contDiffAt,
    iteratedFDeriv_succ_id_eq n x y, dist_add_left]
  exact hH.dist_le hx hy

/-- If `T` is differentiable at `z` with `‖D T(z)‖ < 1`, then `w ↦ w + T w` has an invertible
strict derivative at `z`. -/
private theorem exists_hasStrictFDerivAt_id_add {T : ℂ → ℂ} {z : ℂ} (hT : ContDiffAt ℝ 1 T z)
    (hlt : ‖fderiv ℝ T z‖ < 1) :
    ∃ L : ℂ ≃L[ℝ] ℂ, HasStrictFDerivAt (fun w ↦ w + T w) (L : ℂ →L[ℝ] ℂ) z := by
  have hlt' : ‖fderiv ℝ T z‖₊ < ‖((ContinuousLinearEquiv.refl ℝ ℂ).symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
    rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl,
      ContinuousLinearMap.nnNorm_id, inv_one, ← NNReal.coe_lt_coe, coe_nnNorm, NNReal.coe_one]
    exact hlt
  obtain ⟨L, hL⟩ := ContinuousLinearMap.isInvertible_of_norm_sub_lt
    (ContinuousLinearEquiv.refl ℝ ℂ) (A := ContinuousLinearMap.id ℝ ℂ + fderiv ℝ T z)
    (by rwa [ContinuousLinearEquiv.coe_refl, add_sub_cancel_left])
  refine ⟨L, ?_⟩
  rw [hL]
  exact (contDiffAt_id.add hT).hasStrictFDerivAt
    ((hasFDerivAt_id z).add (hT.differentiableAt one_ne_zero).hasFDerivAt) one_ne_zero

/-- The Wirtinger derivatives of `w ↦ w + T w` at a point where `T` is differentiable. -/
private theorem wirtingerDeriv_id_add {T : ℂ → ℂ} {z : ℂ} (hT : DifferentiableAt ℝ T z) :
    conjWirtingerDeriv (fun w ↦ w + T w) z 1 = conjWirtingerDeriv T z 1 ∧
      wirtingerDeriv (fun w ↦ w + T w) z 1 = 1 + wirtingerDeriv T z 1 := by
  rw [show (fun w ↦ w + T w) = id + T from rfl, conjWirtingerDeriv_add differentiableAt_id hT,
    wirtingerDeriv_add differentiableAt_id hT, conjWirtingerDeriv_id, wirtingerDeriv_id]
  simp

/-- **The Beltrami equation with small `C^{k,α}` coefficient.** Let `k : ℕ` and `0 < α < 1`.
There are `δ > 0` and `C` such that every bounded `C^{k,α}` function `μ` vanishing off
`closedBall c r` with `‖μ‖ < δ` admits a source `h`, `C^{k,α}` and vanishing off the disc with
`‖h‖ ≤ 2 ‖μ‖`, for which `ψ(w) = w + T h(w)`, with `T` the Cauchy transform,

* is globally `C^{k+1}`, with `\bar∂ψ = h`;
* solves the Beltrami equation `\bar∂ψ = μ ∂ψ` on `ℂ`;
* differs from the identity by `T h`, whose derivatives of orders through `k + 1` are bounded by
  `C ‖μ‖` on the disc; in particular its real derivative is within `C ‖μ‖` of the identity there;
* has `α`-Hölder derivative of order `k + 1` on the disc, with constant `C ‖μ‖`;
* has an invertible strict derivative at every point of the disc.

For `k = 0` this is the analogue of `TauCeti.exists_conjWirtingerDeriv_eq_mul_wirtingerDeriv` on
the carrier `supportedCkHolderSubmodule 0` in place of `supportedHolderSubmodule`. -/
theorem exists_ckHolder_conjWirtingerDeriv_eq_mul_wirtingerDeriv (k : ℕ) (hα : 0 < α)
    (hα1 : α < 1) (c : ℂ) (r : ℝ) :
    ∃ δ > 0, ∃ C : ℝ≥0, ∀ μ ∈ supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r),
      ‖μ‖ < δ →
      ∃ h ∈ supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c r), ‖h‖ ≤ 2 * ‖μ‖ ∧
        let ψ : ℂ → ℂ := fun w ↦ w + cauchyTransform h w
        ContDiff ℝ (k + 1 : ℕ) ψ ∧
        (∀ z, conjWirtingerDeriv ψ z 1 = h z) ∧
        (∀ z, conjWirtingerDeriv ψ z 1 = μ z * wirtingerDeriv ψ z 1) ∧
        (∀ i ≤ k + 1, ∀ z ∈ closedBall c r,
          ‖iteratedFDeriv ℝ i (cauchyTransform h) z‖ ≤ C * ‖μ‖) ∧
        (∀ z ∈ closedBall c r, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ C * ‖μ‖) ∧
        HolderOnWith (C * ‖μ‖₊) α (iteratedFDeriv ℝ (k + 1) ψ) (closedBall c r) ∧
        ∀ z ∈ closedBall c r, ∃ L : ℂ ≃L[ℝ] ℂ, HasStrictFDerivAt ψ (L : ℂ →L[ℝ] ℂ) z := by
  -- Work on the disc of radius `max r 0`; the source then vanishes wherever `μ` does.
  set ρ := max r 0
  have hρ : 0 ≤ ρ := le_max_right r 0
  have hsub : closedBall c r ⊆ closedBall c ρ := closedBall_subset_closedBall (le_max_left r 0)
  set D := cauchyTransformCkCLM (F := ℂ) (c := c) k hα hα1 hρ hρ
  set K : ℝ := (k + 7) * 2 ^ k * ‖Beltrami.cutoffBeurlingCkCLM (c := c) k hα hα1 hρ‖
  have hK : 0 ≤ K := by positivity
  have hD : 0 ≤ ‖D‖ := D.opNorm_nonneg
  refine ⟨(4 * (K + ‖D‖ + 1))⁻¹, by positivity, 2 * ‖D‖₊, fun μ hμ hμδ ↦ ?_⟩
  have hδ : 4 * (K + ‖D‖ + 1) * ‖μ‖ < 1 := by
    rwa [← lt_inv_mul_iff₀ (by positivity), mul_one]
  set μ' : supportedCkHolderSubmodule (E := ℂ) (F := ℂ) k α (closedBall c ρ) :=
    ⟨μ, mem_supportedCkHolderSubmodule_iff.mpr fun z hz ↦
      mem_supportedCkHolderSubmodule_iff.mp hμ z fun h ↦ hz (hsub h)⟩
  have hμ' : ‖μ'‖ = ‖μ‖ := (Submodule.norm_coe μ').symm
  obtain ⟨h, hh, hpt⟩ := exists_source hα hα1 hρ μ' <| by
    refine (Beltrami.norm_beltramiCkOperator_le hα hα1 hρ μ').trans ?_
    rw [hμ']
    nlinarith [norm_nonneg μ, mul_nonneg hD (norm_nonneg μ)]
  rw [hμ'] at hh
  obtain ⟨hT, hTbar, hTi, hTH⟩ := cauchyTransform_regularity hα hα1 hρ h
  set T := cauchyTransform (h : CkHolderSpace k α ℂ ℂ)
  have hTd : ∀ z, DifferentiableAt ℝ T z := fun z ↦
    (hT.differentiable (by simp)).differentiableAt
  have hDh : ‖D h‖ ≤ 2 * ‖D‖ * ‖μ‖ := (D.le_opNorm h).trans (by nlinarith)
  have hfd : ∀ z ∈ closedBall c r, ‖fderiv ℝ T z‖ ≤ 2 * ‖D‖ * ‖μ‖ := fun z hz ↦ by
    simpa only [norm_iteratedFDeriv_one] using (hTi 1 (by omega) z (hsub hz)).trans hDh
  have hψbar : ∀ z, conjWirtingerDeriv (fun w ↦ w + T w) z 1 = (h : CkHolderSpace k α ℂ ℂ) z :=
    fun z ↦ (wirtingerDeriv_id_add (hTd z)).1.trans (hTbar z)
  refine ⟨h, mem_supportedCkHolderSubmodule_iff.mpr fun z hz ↦ by
      rw [hpt z, mem_supportedCkHolderSubmodule_iff.mp hμ z hz, zero_mul],
    hh, contDiff_id.add hT, hψbar, fun z ↦ ?_, fun i hi z hz ↦ ?_, fun z hz ↦ ?_, ?_,
    fun z hz ↦ ?_⟩
  · rw [hψbar z, (wirtingerDeriv_id_add (hTd z)).2]
    exact hpt z
  · push_cast
    exact (hTi i hi z (hsub hz)).trans hDh
  · rw [show (fun w ↦ w + T w) = id + T from rfl,
      ((hasFDerivAt_id z).add (hTd z).hasFDerivAt).fderiv, add_sub_cancel_left]
    push_cast
    exact hfd z hz
  · refine ((holderOnWith_iteratedFDeriv_id_add hT hTH).mono hsub).mono_const ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    exact hDh
  · exact exists_hasStrictFDerivAt_id_add (hT.contDiffAt.of_le (by simp))
      ((hfd z hz).trans_lt (by nlinarith [norm_nonneg μ, mul_nonneg hK (norm_nonneg μ)]))

end TauCeti
