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
directional derivative `iteratedFDerivAlong 𝕜 [v₁, …, vₖ] f` differentiates `f` first in the
direction `vₖ` and last in the direction `v₁`:

`iteratedFDerivAlong 𝕜 (v :: vs) f x = Df'(x) v`, where `f' = iteratedFDerivAlong 𝕜 vs f`.

Mixed partial derivatives `∂_x^α ∂_ξ^β`, indexed by lists of coordinate directions, are the
main example: symbol estimates in microlocal analysis bound them one multi-index at a time.
Each step uses the Fréchet derivative `fderiv`, so for a map which has directional derivatives
but is not differentiable this can differ from iterating Mathlib's `lineDeriv`.

The operation is local. For maps which are `C^k` along a list of `k` directions, it is linear,
commutes with affine changes of variables, over `ℝ` or `ℂ` does not depend on the order of the
directions (by the symmetry of second derivatives), and agrees with Mathlib's `iteratedFDeriv`
evaluated on the directions.

## Main declarations

* `TauCeti.iteratedFDerivAlong`: the iterated directional derivative along a list of directions.
* `ContDiff.iteratedFDerivAlong`: differentiating a `C^n` map along `k` directions gives a map
  which is `C^m` whenever `m + k ≤ n`.
* `ContDiffOn.iteratedFDerivAlong`, `TauCeti.iteratedFDerivAlong_add_apply_of_isOpen`: the
  same smoothness, and additivity, for maps which are only `C^n` on an open set.
* `TauCeti.iteratedFDerivAlong_comp_of_hasFDerivAt`: the chain rule for an affine change of
  variables.
* `List.Perm.iteratedFDerivAlong_eq`: over `ℝ` or `ℂ`, reordering the directions does not change
  the iterated directional derivative.
* `TauCeti.iteratedFDerivAlong_ofFn_eq_iteratedFDeriv`: the comparison with `iteratedFDeriv`.
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
/-- The iterated directional derivative of `f` along the list of directions `vs`, computed with
Fréchet derivatives: the derivative in the direction of the head of the list is taken last, so
`iteratedFDerivAlong 𝕜 (v :: vs) f x = fderiv 𝕜 (iteratedFDerivAlong 𝕜 vs f) x v`. -/
def iteratedFDerivAlong : List E → (E → F) → E → F
  | [], f => f
  | v :: vs, f => fun x => fderiv 𝕜 (iteratedFDerivAlong vs f) x v

@[simp]
theorem iteratedFDerivAlong_nil (f : E → F) : iteratedFDerivAlong 𝕜 [] f = f :=
  (rfl)

@[simp]
theorem iteratedFDerivAlong_cons_apply (v : E) (vs : List E) (f : E → F) (x : E) :
    iteratedFDerivAlong 𝕜 (v :: vs) f x = fderiv 𝕜 (iteratedFDerivAlong 𝕜 vs f) x v :=
  (rfl)

theorem iteratedFDerivAlong_cons (v : E) (vs : List E) (f : E → F) :
    iteratedFDerivAlong 𝕜 (v :: vs) f = fun x => fderiv 𝕜 (iteratedFDerivAlong 𝕜 vs f) x v :=
  (rfl)

/-- Differentiating along `vs ++ ws` differentiates along `ws` first, then along `vs`. -/
theorem iteratedFDerivAlong_append (vs ws : List E) (f : E → F) :
    iteratedFDerivAlong 𝕜 (vs ++ ws) f = iteratedFDerivAlong 𝕜 vs (iteratedFDerivAlong 𝕜 ws f) := by
  induction vs with
  | nil => rfl
  | cons v vs ih => rw [List.cons_append, iteratedFDerivAlong_cons, ih, iteratedFDerivAlong_cons]

/-- Every nonempty iterated directional derivative of a constant map vanishes. -/
@[simp]
theorem iteratedFDerivAlong_cons_const (v : E) (vs : List E) (c : F) :
    iteratedFDerivAlong 𝕜 (v :: vs) (fun _ : E => c) = 0 := by
  induction vs generalizing v with
  | nil => funext x; simp
  | cons w ws ih =>
    rw [iteratedFDerivAlong_cons, ih w]
    funext x
    simp

@[simp]
theorem iteratedFDerivAlong_zero (vs : List E) : iteratedFDerivAlong 𝕜 vs (0 : E → F) = 0 := by
  cases vs with
  | nil => rfl
  | cons v vs => exact iteratedFDerivAlong_cons_const v vs 0

/-- Iterated directional derivatives are local: maps which agree near `x` have iterated
directional derivatives which agree near `x`. -/
theorem _root_.Filter.EventuallyEq.iteratedFDerivAlong {f g : E → F} {x : E} (h : f =ᶠ[𝓝 x] g)
    (vs : List E) : iteratedFDerivAlong 𝕜 vs f =ᶠ[𝓝 x] iteratedFDerivAlong 𝕜 vs g := by
  induction vs with
  | nil => exact h
  | cons v vs ih =>
    filter_upwards [ih.eventuallyEq_nhds] with y hy
    rw [iteratedFDerivAlong_cons_apply, iteratedFDerivAlong_cons_apply,
      (hy.fderiv (𝕜 := 𝕜)).eq_of_nhds]

/-- Every iterated directional derivative of a map vanishing near `x` vanishes at `x`. -/
theorem iteratedFDerivAlong_eq_zero_of_eventuallyEq_zero {f : E → F} {x : E}
    (h : f =ᶠ[𝓝 x] 0) (vs : List E) : iteratedFDerivAlong 𝕜 vs f x = 0 := by
  simpa using (h.iteratedFDerivAlong (𝕜 := 𝕜) vs).eq_of_nhds

variable {n : ℕ∞ω}

/-- Differentiating a `C^n` map along `k` directions gives a `C^m` map whenever `m + k ≤ n`. -/
theorem _root_.ContDiff.iteratedFDerivAlong {m : ℕ∞ω} {f : E → F} (hf : ContDiff 𝕜 n f)
    (vs : List E) (hvs : m + vs.length ≤ n) : ContDiff 𝕜 m (iteratedFDerivAlong 𝕜 vs f) := by
  induction vs generalizing m with
  | nil => exact hf.of_le (by simpa using hvs)
  | cons v vs ih =>
    refine ((ih (m := m + 1) ?_).fderiv_right le_rfl).clm_apply contDiff_const
    rwa [List.length_cons, Nat.cast_succ, add_comm (vs.length : ℕ∞ω), ← add_assoc] at hvs

theorem _root_.ContDiff.differentiable_iteratedFDerivAlong {f : E → F} (hf : ContDiff 𝕜 n f)
    (vs : List E) (hvs : vs.length < n) : Differentiable 𝕜 (iteratedFDerivAlong 𝕜 vs f) :=
  (hf.iteratedFDerivAlong (m := 1) vs (by
    rw [add_comm]
    exact_mod_cast ENat.add_one_natCast_le_withTop_of_lt hvs)).differentiable one_ne_zero

theorem iteratedFDerivAlong_add {f g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g)
    (vs : List E) (hvs : vs.length ≤ n) :
    iteratedFDerivAlong 𝕜 vs (f + g) = iteratedFDerivAlong 𝕜 vs f + iteratedFDerivAlong 𝕜 vs g := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hlt : (vs.length : ℕ∞ω) < n :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) hvs
    funext x
    rw [iteratedFDerivAlong_cons_apply, ih hlt.le,
      fderiv_add (hf.differentiable_iteratedFDerivAlong vs hlt x)
        (hg.differentiable_iteratedFDerivAlong vs hlt x)]
    rfl

/-- Differentiating a map which is `C^n` on an open set `s` along `k` directions gives a map which
is `C^m` on `s` whenever `m + k ≤ n`. -/
theorem _root_.ContDiffOn.iteratedFDerivAlong {m : ℕ∞ω} {f : E → F} {s : Set E}
    (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (vs : List E) (hvs : m + vs.length ≤ n) :
    ContDiffOn 𝕜 m (iteratedFDerivAlong 𝕜 vs f) s := by
  induction vs generalizing m with
  | nil => exact hf.of_le (by simpa using hvs)
  | cons v vs ih =>
    refine ((ih (m := m + 1) ?_).fderiv_of_isOpen hs le_rfl).clm_apply contDiffOn_const
    rwa [List.length_cons, Nat.cast_succ, add_comm (vs.length : ℕ∞ω), ← add_assoc] at hvs

theorem _root_.ContDiffOn.differentiableOn_iteratedFDerivAlong {f : E → F} {s : Set E}
    (hf : ContDiffOn 𝕜 n f s) (hs : IsOpen s) (vs : List E) (hvs : vs.length < n) :
    DifferentiableOn 𝕜 (iteratedFDerivAlong 𝕜 vs f) s :=
  (hf.iteratedFDerivAlong (m := 1) hs vs (by
    rw [add_comm]
    exact_mod_cast ENat.add_one_natCast_le_withTop_of_lt hvs)).differentiableOn one_ne_zero

/-- Iterated directional derivatives are additive at the points of an open set on which both maps
are `C^k`, for a list of `k` directions. -/
theorem iteratedFDerivAlong_add_apply_of_isOpen {f g : E → F} {s : Set E}
    (hf : ContDiffOn 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) (hs : IsOpen s) (vs : List E)
    (hvs : vs.length ≤ n) {x : E} (hx : x ∈ s) :
    iteratedFDerivAlong 𝕜 vs (f + g) x =
      iteratedFDerivAlong 𝕜 vs f x + iteratedFDerivAlong 𝕜 vs g x := by
  induction vs generalizing x with
  | nil => rfl
  | cons v vs ih =>
    have hlt : (vs.length : ℕ∞ω) < n :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) hvs
    have hev : iteratedFDerivAlong 𝕜 vs (f + g) =ᶠ[𝓝 x]
        iteratedFDerivAlong 𝕜 vs f + iteratedFDerivAlong 𝕜 vs g := by
      filter_upwards [hs.mem_nhds hx] with y hy
      exact ih hlt.le hy
    rw [iteratedFDerivAlong_cons_apply, hev.fderiv_eq,
      fderiv_add ((hf.differentiableOn_iteratedFDerivAlong hs vs hlt).differentiableAt
        (hs.mem_nhds hx)) ((hg.differentiableOn_iteratedFDerivAlong hs vs hlt).differentiableAt
        (hs.mem_nhds hx))]
    rfl

theorem iteratedFDerivAlong_neg (f : E → F) (vs : List E) :
    iteratedFDerivAlong 𝕜 vs (-f) = -iteratedFDerivAlong 𝕜 vs f := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    funext x
    rw [iteratedFDerivAlong_cons_apply, ih]
    exact congrArg (· v) (fderiv_neg (𝕜 := 𝕜) (f := iteratedFDerivAlong 𝕜 vs f) (x := x))

theorem iteratedFDerivAlong_sub {f g : E → F} (hf : ContDiff 𝕜 n f) (hg : ContDiff 𝕜 n g)
    (vs : List E) (hvs : vs.length ≤ n) :
    iteratedFDerivAlong 𝕜 vs (f - g) = iteratedFDerivAlong 𝕜 vs f - iteratedFDerivAlong 𝕜 vs g := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hlt : (vs.length : ℕ∞ω) < n :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) hvs
    funext x
    rw [iteratedFDerivAlong_cons_apply, ih hlt.le,
      fderiv_sub (hf.differentiable_iteratedFDerivAlong vs hlt x)
        (hg.differentiable_iteratedFDerivAlong vs hlt x)]
    rfl

theorem iteratedFDerivAlong_const_smul {R : Type*} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F]
    [ContinuousConstSMul R F] {f : E → F} (hf : ContDiff 𝕜 n f) (c : R) (vs : List E)
    (hvs : vs.length ≤ n) : iteratedFDerivAlong 𝕜 vs (c • f) = c • iteratedFDerivAlong 𝕜 vs f := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hlt : (vs.length : ℕ∞ω) < n :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) hvs
    funext x
    rw [iteratedFDerivAlong_cons_apply, ih hlt.le,
      fderiv_const_smul (hf.differentiable_iteratedFDerivAlong vs hlt x)]
    rfl

/-- Iterated directional derivatives commute with postcomposition by a continuous linear map. -/
theorem _root_.ContinuousLinearMap.iteratedFDerivAlong_comp_left (L : F →L[𝕜] G) {f : E → F}
    (hf : ContDiff 𝕜 n f) (vs : List E) (hvs : vs.length ≤ n) :
    iteratedFDerivAlong 𝕜 vs (fun x => L (f x)) = fun x => L (iteratedFDerivAlong 𝕜 vs f x) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    have hlt : (vs.length : ℕ∞ω) < n :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) hvs
    funext x
    have h : HasFDerivAt (fun y => L (iteratedFDerivAlong 𝕜 vs f y))
        (L.comp (fderiv 𝕜 (iteratedFDerivAlong 𝕜 vs f) x)) x :=
      L.hasFDerivAt.comp x (hf.differentiable_iteratedFDerivAlong vs hlt x).hasFDerivAt
    rw [iteratedFDerivAlong_cons_apply, ih hlt.le, h.fderiv]
    rfl

/-- The derivative of a continuous linear map in the direction `v` is the constant `L v`. -/
@[simp]
theorem _root_.ContinuousLinearMap.iteratedFDerivAlong_singleton (L : E →L[𝕜] F) (v : E) :
    iteratedFDerivAlong 𝕜 [v] L = fun _ => L v := by
  funext x
  simp

/-- Every iterated directional derivative of order at least two of a continuous linear map
vanishes. -/
@[simp]
theorem _root_.ContinuousLinearMap.iteratedFDerivAlong_cons_cons (L : E →L[𝕜] F) (u v : E)
    (vs : List E) : iteratedFDerivAlong 𝕜 (u :: v :: vs) L = 0 := by
  induction vs generalizing u v with
  | nil => rw [iteratedFDerivAlong_cons, L.iteratedFDerivAlong_singleton]; funext x; simp
  | cons w ws ih => rw [iteratedFDerivAlong_cons, ih v w]; funext x; simp

/-- **Chain rule for an affine change of variables.** If `φ` has the constant derivative `L`,
the iterated directional derivative of `f ∘ φ` along `vs` is that of `f` along the image of `vs`
under `L`, evaluated at `φ z`. -/
theorem iteratedFDerivAlong_comp_of_hasFDerivAt {φ : G → E} {L : G →L[𝕜] E}
    (hφ : ∀ z, HasFDerivAt φ L z) {f : E → F} (hf : ContDiff 𝕜 n f) (vs : List G)
    (hvs : vs.length ≤ n) (z : G) :
    iteratedFDerivAlong 𝕜 vs (fun z => f (φ z)) z = iteratedFDerivAlong 𝕜 (vs.map L) f (φ z) := by
  induction vs generalizing z with
  | nil => rfl
  | cons v vs ih =>
    have hlt : ((vs.map L).length : ℕ∞ω) < n := by
      rw [List.length_map]
      exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) hvs
    have h : HasFDerivAt (fun y => iteratedFDerivAlong 𝕜 (vs.map L) f (φ y))
        ((fderiv 𝕜 (iteratedFDerivAlong 𝕜 (vs.map L) f) (φ z)).comp L) z :=
      ((hf.differentiable_iteratedFDerivAlong _ hlt) (φ z)).hasFDerivAt.comp z (hφ z)
    rw [List.length_map] at hlt
    rw [iteratedFDerivAlong_cons_apply, funext (ih hlt.le), List.map_cons,
      iteratedFDerivAlong_cons_apply, h.fderiv]
    rfl

/-- The derivative of an iterated directional derivative, in the direction `v`, followed by the
direction `w`, is the second derivative applied to `v` and `w`. -/
theorem iteratedFDerivAlong_cons_cons_apply {f : E → F} (hf : ContDiff 𝕜 n f) (v w : E)
    (vs : List E) (hvs : (v :: w :: vs).length ≤ n) (x : E) :
    iteratedFDerivAlong 𝕜 (v :: w :: vs) f x =
      fderiv 𝕜 (fderiv 𝕜 (iteratedFDerivAlong 𝕜 vs f)) x v w := by
  have h2 : ContDiff 𝕜 2 (iteratedFDerivAlong 𝕜 vs f) :=
    hf.iteratedFDerivAlong vs
      (le_of_eq_of_le (by simp only [List.length_cons]; push_cast; ring) hvs)
  have hd : Differentiable 𝕜 (fderiv 𝕜 (iteratedFDerivAlong 𝕜 vs f)) :=
    (h2.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  rw [iteratedFDerivAlong_cons_apply, iteratedFDerivAlong_cons,
    fderiv_clm_apply (hd x) (differentiableAt_const w)]
  simp

/-- Over `ℝ` or `ℂ`, the first two directions of a `C^k` map, for a list of `k` directions, can
be exchanged. See `List.Perm.iteratedFDerivAlong_eq` for arbitrary reorderings. -/
theorem iteratedFDerivAlong_swap [IsRCLikeNormedField 𝕜] {f : E → F} (hf : ContDiff 𝕜 n f)
    (v w : E) (vs : List E) (hvs : (v :: w :: vs).length ≤ n) :
    iteratedFDerivAlong 𝕜 (v :: w :: vs) f = iteratedFDerivAlong 𝕜 (w :: v :: vs) f := by
  funext x
  rw [iteratedFDerivAlong_cons_cons_apply hf _ _ _ hvs,
    iteratedFDerivAlong_cons_cons_apply hf _ _ _ (by simpa using hvs)]
  have h2 : ContDiff 𝕜 2 (iteratedFDerivAlong 𝕜 vs f) :=
    hf.iteratedFDerivAlong vs
      (le_of_eq_of_le (by simp only [List.length_cons]; push_cast; ring) hvs)
  exact (h2.contDiffAt.isSymmSndFDerivAt (by simp)) v w

/-- Over `ℝ` or `ℂ`, the iterated directional derivative of a `C^k` map along `k` directions does
not depend on the order of the directions. -/
theorem _root_.List.Perm.iteratedFDerivAlong_eq [IsRCLikeNormedField 𝕜] {vs ws : List E}
    (h : vs.Perm ws) {f : E → F} (hf : ContDiff 𝕜 n f) (hvs : vs.length ≤ n) :
    iteratedFDerivAlong 𝕜 vs f = iteratedFDerivAlong 𝕜 ws f := by
  induction h with
  | nil => rfl
  | cons v _ ih =>
    rw [iteratedFDerivAlong_cons, ih (le_trans (by exact_mod_cast Nat.le_succ _) hvs),
      iteratedFDerivAlong_cons]
  | swap v w vs => exact iteratedFDerivAlong_swap hf w v vs hvs
  | trans h₁₂ _ ih₁ ih₂ => exact (ih₁ hvs).trans (ih₂ (h₁₂.length_eq ▸ hvs))

/-- The iterated directional derivative of a `C^k` map along the directions `m 0, …, m (k - 1)` is
the `k`-th iterated derivative evaluated on them. -/
theorem iteratedFDerivAlong_ofFn_eq_iteratedFDeriv {f : E → F} {k : ℕ} (hf : ContDiff 𝕜 k f)
    (m : Fin k → E) (x : E) :
    iteratedFDerivAlong 𝕜 (List.ofFn m) f x = iteratedFDeriv 𝕜 k f x m := by
  induction k generalizing x with
  | zero => simp [Subsingleton.elim m Fin.elim0]
  | succ k ih =>
    rw [List.ofFn_succ, iteratedFDerivAlong_cons_apply,
      funext (ih (hf.of_le (by exact_mod_cast Nat.le_succ k)) fun i => m i.succ),
      fderiv_continuousMultilinear_apply_const_apply
        ((hf.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast Nat.lt_succ_self k)) x),
      iteratedFDeriv_succ_apply_left]
    rfl

end TauCeti
