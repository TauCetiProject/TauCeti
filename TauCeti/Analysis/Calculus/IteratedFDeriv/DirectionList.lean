/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Iterated directional derivatives along a list of directions

For a list of directions `[v₁, …, vₖ]` in a normed space `E` and a map `f : E → F`, the iterated
directional derivative `iteratedDirDeriv 𝕜 [v₁, …, vₖ] f` differentiates `f` first in the
direction `vₖ` and last in the direction `v₁`:

`iteratedDirDeriv 𝕜 (v :: vs) f x = Df'(x) v`, where `f' = iteratedDirDeriv 𝕜 vs f`.

Mixed partial derivatives `∂_x^α ∂_ξ^β`, indexed by lists of coordinate directions, are the
main example: symbol estimates in microlocal analysis bound them one multi-index at a time.
For smooth maps the operation is linear, commutes with affine changes of variables, is local, and
does not depend on the order of the directions (by the symmetry of second derivatives), and it
agrees with Mathlib's `iteratedFDeriv` evaluated on the directions.

## Main declarations

* `TauCeti.iteratedDirDeriv`: the iterated directional derivative along a list of directions.
* `ContDiff.iteratedDirDeriv`: iterated directional derivatives of smooth maps are smooth.
* `TauCeti.iteratedDirDeriv_comp_of_hasFDerivAt`: the chain rule for an affine change of
  variables.
* `List.Perm.iteratedDirDeriv_eq`: for smooth maps over `ℝ` or `ℂ`, reordering the directions does
  not change the iterated directional derivative.
* `TauCeti.iteratedDirDeriv_eq_iteratedFDeriv`: the comparison with `iteratedFDeriv`.
-/

public section

noncomputable section

open Filter Topology
open scoped ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable (𝕜) in
/-- The iterated directional derivative of `f` along the list of directions `vs`: the derivative
in the direction of the head of the list is taken last, so
`iteratedDirDeriv 𝕜 (v :: vs) f x = fderiv 𝕜 (iteratedDirDeriv 𝕜 vs f) x v`. -/
def iteratedDirDeriv : List E → (E → F) → E → F
  | [], f => f
  | v :: vs, f => fun x => fderiv 𝕜 (iteratedDirDeriv vs f) x v

@[simp]
theorem iteratedDirDeriv_nil (f : E → F) : iteratedDirDeriv 𝕜 [] f = f :=
  (rfl)

@[simp]
theorem iteratedDirDeriv_cons_apply (v : E) (vs : List E) (f : E → F) (x : E) :
    iteratedDirDeriv 𝕜 (v :: vs) f x = fderiv 𝕜 (iteratedDirDeriv 𝕜 vs f) x v :=
  (rfl)

theorem iteratedDirDeriv_cons (v : E) (vs : List E) (f : E → F) :
    iteratedDirDeriv 𝕜 (v :: vs) f = fun x => fderiv 𝕜 (iteratedDirDeriv 𝕜 vs f) x v :=
  (rfl)

/-- Differentiating along `vs ++ ws` differentiates along `ws` first, then along `vs`. -/
theorem iteratedDirDeriv_append (vs ws : List E) (f : E → F) :
    iteratedDirDeriv 𝕜 (vs ++ ws) f = iteratedDirDeriv 𝕜 vs (iteratedDirDeriv 𝕜 ws f) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [List.cons_append, iteratedDirDeriv_cons, ih, iteratedDirDeriv_cons]

/-- Every nonempty iterated directional derivative of a constant map vanishes. -/
@[simp]
theorem iteratedDirDeriv_cons_const (v : E) (vs : List E) (c : F) :
    iteratedDirDeriv 𝕜 (v :: vs) (fun _ : E => c) = 0 := by
  induction vs generalizing v with
  | nil => funext x; simp
  | cons w ws ih =>
    rw [iteratedDirDeriv_cons, ih w]
    funext x
    simp

@[simp]
theorem iteratedDirDeriv_zero (vs : List E) : iteratedDirDeriv 𝕜 vs (0 : E → F) = 0 := by
  cases vs with
  | nil => rfl
  | cons v vs => exact iteratedDirDeriv_cons_const v vs 0

/-- Iterated directional derivatives are local: maps which agree near `x` have iterated
directional derivatives which agree near `x`. -/
theorem _root_.Filter.EventuallyEq.iteratedDirDeriv {f g : E → F} {x : E} (h : f =ᶠ[𝓝 x] g)
    (vs : List E) : iteratedDirDeriv 𝕜 vs f =ᶠ[𝓝 x] iteratedDirDeriv 𝕜 vs g := by
  induction vs with
  | nil => exact h
  | cons v vs ih =>
    filter_upwards [ih.eventuallyEq_nhds] with y hy
    rw [iteratedDirDeriv_cons_apply, iteratedDirDeriv_cons_apply, (hy.fderiv (𝕜 := 𝕜)).eq_of_nhds]

/-- Every iterated directional derivative of a map vanishing near `x` vanishes at `x`. -/
theorem iteratedDirDeriv_eq_zero_of_eventuallyEq_zero {f : E → F} {x : E}
    (h : f =ᶠ[𝓝 x] 0) (vs : List E) : iteratedDirDeriv 𝕜 vs f x = 0 := by
  simpa using (h.iteratedDirDeriv (𝕜 := 𝕜) vs).eq_of_nhds

/-- Iterated directional derivatives of smooth maps are smooth. -/
theorem _root_.ContDiff.iteratedDirDeriv {f : E → F} (hf : ContDiff 𝕜 ∞ f) (vs : List E) :
    ContDiff 𝕜 ∞ (iteratedDirDeriv 𝕜 vs f) := by
  induction vs with
  | nil => exact hf
  | cons v vs ih => exact (ih.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

theorem _root_.ContDiff.differentiable_iteratedDirDeriv {f : E → F} (hf : ContDiff 𝕜 ∞ f)
    (vs : List E) : Differentiable 𝕜 (iteratedDirDeriv 𝕜 vs f) :=
  (hf.iteratedDirDeriv vs).differentiable (by simp)

theorem iteratedDirDeriv_add {f g : E → F} (hf : ContDiff 𝕜 ∞ f) (hg : ContDiff 𝕜 ∞ g)
    (vs : List E) :
    iteratedDirDeriv 𝕜 vs (f + g) = iteratedDirDeriv 𝕜 vs f + iteratedDirDeriv 𝕜 vs g := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    rw [iteratedDirDeriv_cons_apply, ih, fderiv_add (hf.differentiable_iteratedDirDeriv vs x)
      (hg.differentiable_iteratedDirDeriv vs x)]
    rfl

theorem iteratedDirDeriv_neg (f : E → F) (vs : List E) :
    iteratedDirDeriv 𝕜 vs (-f) = -iteratedDirDeriv 𝕜 vs f := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    rw [iteratedDirDeriv_cons_apply, ih]
    exact congrArg (· v) (fderiv_neg (𝕜 := 𝕜) (f := iteratedDirDeriv 𝕜 vs f) (x := x))

theorem iteratedDirDeriv_sub {f g : E → F} (hf : ContDiff 𝕜 ∞ f) (hg : ContDiff 𝕜 ∞ g)
    (vs : List E) :
    iteratedDirDeriv 𝕜 vs (f - g) = iteratedDirDeriv 𝕜 vs f - iteratedDirDeriv 𝕜 vs g := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    rw [iteratedDirDeriv_cons_apply, ih, fderiv_sub (hf.differentiable_iteratedDirDeriv vs x)
      (hg.differentiable_iteratedDirDeriv vs x)]
    rfl

theorem iteratedDirDeriv_const_smul {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F]
    [ContinuousConstSMul R F] {f : E → F} (hf : ContDiff 𝕜 ∞ f) (c : R) (vs : List E) :
    iteratedDirDeriv 𝕜 vs (c • f) = c • iteratedDirDeriv 𝕜 vs f := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    rw [iteratedDirDeriv_cons_apply, ih,
      fderiv_const_smul (hf.differentiable_iteratedDirDeriv vs x)]
    rfl

/-- Iterated directional derivatives commute with postcomposition by a continuous linear map. -/
theorem _root_.ContinuousLinearMap.iteratedDirDeriv_comp_left (L : F →L[𝕜] G) {f : E → F}
    (hf : ContDiff 𝕜 ∞ f) (vs : List E) :
    iteratedDirDeriv 𝕜 vs (fun x => L (f x)) = fun x => L (iteratedDirDeriv 𝕜 vs f x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    have h : HasFDerivAt (fun y => L (iteratedDirDeriv 𝕜 vs f y))
        (L.comp (fderiv 𝕜 (iteratedDirDeriv 𝕜 vs f) x)) x :=
      L.hasFDerivAt.comp x (hf.differentiable_iteratedDirDeriv vs x).hasFDerivAt
    rw [iteratedDirDeriv_cons_apply, ih, h.fderiv]
    rfl

/-- The derivative of a continuous linear map in the direction `v` is the constant `L v`. -/
@[simp]
theorem _root_.ContinuousLinearMap.iteratedDirDeriv_singleton (L : E →L[𝕜] F) (v : E) :
    iteratedDirDeriv 𝕜 [v] L = fun _ => L v := by
  funext x
  simp

/-- Every iterated directional derivative of order at least two of a continuous linear map
vanishes. -/
@[simp]
theorem _root_.ContinuousLinearMap.iteratedDirDeriv_cons_cons (L : E →L[𝕜] F) (u v : E)
    (vs : List E) : iteratedDirDeriv 𝕜 (u :: v :: vs) L = 0 := by
  induction vs generalizing u v with
  | nil => rw [iteratedDirDeriv_cons, L.iteratedDirDeriv_singleton]; funext x; simp
  | cons w ws ih => rw [iteratedDirDeriv_cons, ih v w]; funext x; simp

/-- **Chain rule for an affine change of variables.** If `φ` has the constant derivative `L`,
the iterated directional derivative of `f ∘ φ` along `vs` is that of `f` along the image of `vs`
under `L`, evaluated at `φ z`. -/
theorem iteratedDirDeriv_comp_of_hasFDerivAt {φ : G → E} {L : G →L[𝕜] E}
    (hφ : ∀ z, HasFDerivAt φ L z) {f : E → F} (hf : ContDiff 𝕜 ∞ f) (vs : List G) (z : G) :
    iteratedDirDeriv 𝕜 vs (fun z => f (φ z)) z = iteratedDirDeriv 𝕜 (vs.map L) f (φ z) := by
  induction vs generalizing z with
  | nil => rfl
  | cons v vs ih =>
    have h : HasFDerivAt (fun y => iteratedDirDeriv 𝕜 (vs.map L) f (φ y))
        ((fderiv 𝕜 (iteratedDirDeriv 𝕜 (vs.map L) f) (φ z)).comp L) z :=
      ((hf.differentiable_iteratedDirDeriv _) (φ z)).hasFDerivAt.comp z (hφ z)
    rw [iteratedDirDeriv_cons_apply, funext ih, List.map_cons, iteratedDirDeriv_cons_apply,
      h.fderiv]
    rfl

/-- The derivative of an iterated directional derivative, in the direction `v`, followed by the
direction `w`, is the second derivative applied to `v` and `w`. -/
theorem iteratedDirDeriv_cons_cons_apply {f : E → F} (hf : ContDiff 𝕜 ∞ f) (v w : E)
    (vs : List E) (x : E) :
    iteratedDirDeriv 𝕜 (v :: w :: vs) f x =
      fderiv 𝕜 (fderiv 𝕜 (iteratedDirDeriv 𝕜 vs f)) x v w := by
  have hd : Differentiable 𝕜 (fderiv 𝕜 (iteratedDirDeriv 𝕜 vs f)) :=
    ((hf.iteratedDirDeriv vs).fderiv_right (m := ∞) le_rfl).differentiable (by simp)
  rw [iteratedDirDeriv_cons_apply, iteratedDirDeriv_cons,
    fderiv_clm_apply (hd x) (differentiableAt_const w)]
  simp

/-- Over `ℝ` or `ℂ`, two consecutive directions of a smooth map can be exchanged. -/
theorem iteratedDirDeriv_swap [IsRCLikeNormedField 𝕜] {f : E → F} (hf : ContDiff 𝕜 ∞ f)
    (v w : E) (vs : List E) :
    iteratedDirDeriv 𝕜 (v :: w :: vs) f = iteratedDirDeriv 𝕜 (w :: v :: vs) f := by
  funext x
  rw [iteratedDirDeriv_cons_cons_apply hf, iteratedDirDeriv_cons_cons_apply hf]
  exact ((hf.iteratedDirDeriv vs).contDiffAt.isSymmSndFDerivAt (by simp)) v w

/-- Over `ℝ` or `ℂ`, the iterated directional derivative of a smooth map does not depend on the
order of the directions. -/
theorem _root_.List.Perm.iteratedDirDeriv_eq [IsRCLikeNormedField 𝕜] {vs ws : List E}
    (h : vs.Perm ws) {f : E → F} (hf : ContDiff 𝕜 ∞ f) :
    iteratedDirDeriv 𝕜 vs f = iteratedDirDeriv 𝕜 ws f := by
  induction h with
  | nil => rfl
  | cons v _ ih => rw [iteratedDirDeriv_cons, ih, iteratedDirDeriv_cons]
  | swap v w vs => exact iteratedDirDeriv_swap hf w v vs
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The iterated directional derivative along the directions `m 0, …, m (k - 1)` is the `k`-th
iterated derivative evaluated on them. -/
theorem iteratedDirDeriv_ofFn_eq_iteratedFDeriv {f : E → F} (hf : ContDiff 𝕜 ∞ f) {k : ℕ}
    (m : Fin k → E) (x : E) :
    iteratedDirDeriv 𝕜 (List.ofFn m) f x = iteratedFDeriv 𝕜 k f x m := by
  induction k generalizing x with
  | zero => simp [Subsingleton.elim m Fin.elim0]
  | succ k ih =>
    rw [List.ofFn_succ, iteratedDirDeriv_cons_apply, funext (ih fun i => m i.succ),
      fderiv_continuousMultilinear_apply_const_apply
        ((hf.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast ENat.natCast_lt_top k)) x),
      iteratedFDeriv_succ_apply_left]
    rfl

end TauCeti
