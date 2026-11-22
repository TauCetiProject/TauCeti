/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Distribution.Comul

/-!
# Stage-level right convolution on analytic stages

Let `K` be a complete nontrivially normed field with contractive `ℤ_p`-action. Postcomposing the
curried stage comultiplication `TauCeti.AnalyticStage.comulCurried K` coordinatewise with a
continuous linear functional `φ : LA_h(K) →L[K] K` produces the stage-level right convolution
operator
`TauCeti.LocallyAnalyticDistribution.convolveFunRightStage φ : LA_h(K) →L[K] LA_h(K)`, sending
`c` to the coefficient vector of `x ↦ φ (translate K x c)`.

This file develops the stage-only theory of `convolveFunRightStage` over
`TauCeti.NumberTheory.Padics.Distribution.Comul`, without importing the locally analytic direct
limit, the distribution space, or measure convolution.

## Main definitions

* `TauCeti.LocallyAnalyticDistribution.convolveFunRightStage`: stage-level right convolution
  `(LA_h(K) →L[K] K) →ₗ[K] (LA_h(K) →L[K] LA_h(K))`.

## Main results

* `TauCeti.LocallyAnalyticDistribution.opNorm_convolveFunRightStage_le`: operator norm bound
  `‖convolveFunRightStage φ‖ ≤ ‖φ‖`.
* `TauCeti.LocallyAnalyticDistribution.eval_convolveFunRightStage`: evaluation gives
  `φ (AnalyticStage.translate K x c)`.
* `TauCeti.LocallyAnalyticDistribution.eval_convolveFunRightStage_zero`,
  `TauCeti.LocallyAnalyticDistribution.convolveFunRightStage_injective`: zero-evaluation recovery
  and faithfulness of `convolveFunRightStage`.
* `TauCeti.LocallyAnalyticDistribution.convolveFunRightStage_transition`,
  `TauCeti.LocallyAnalyticDistribution.convolveFunRightStage_transitionLE`: compatibility with
  stage transitions.
* `TauCeti.LocallyAnalyticDistribution.convolveFunRightStage_comp`,
  `TauCeti.LocallyAnalyticDistribution.convolveFunRightStage_evalCLM_zero`: associativity and
  unit law.

## References

* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4 and §II.2.
* P. Schneider and J. Teitelbaum, *p-adic Fourier theory*, Documenta Math. 6 (2001), 447–481.
-/

public section

open scoped ZeroAtInfty
open ZeroAtInftyContinuousMap

namespace TauCeti.LocallyAnalyticDistribution

variable {p : ℕ} [Fact p.Prime] {K : Type*} [NontriviallyNormedField K] [Algebra ℤ_[p] K]
  [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K] [CompleteSpace K]

open AnalyticStage

/-- The stage-level right convolution operator of a continuous functional `φ : LA_h(K) →L[K] K`:
postcomposing `AnalyticStage.comulCurried K` coordinatewise with `φ` sends `c` to the
coefficient vector of `x ↦ φ (y ↦ c (x + y))`. -/
noncomputable def convolveFunRightStage {h : ℕ} :
    (AnalyticStage p h K →L[K] K) →ₗ[K] (AnalyticStage p h K →L[K] AnalyticStage p h K) where
  toFun φ := (compLeft φ (φ.bound.imp fun _ hb ↦ hb.2)).comp (comulCurried K)
  map_add' φ ψ := by
    rw [compLeft_add φ ψ (φ.bound.imp fun _ hb ↦ hb.2) (ψ.bound.imp fun _ hb ↦ hb.2),
      ContinuousLinearMap.add_comp]
  map_smul' a φ := by
    rw [compLeft_smul a φ (φ.bound.imp fun _ hb ↦ hb.2), ContinuousLinearMap.smul_comp,
      RingHom.id_apply]

private theorem convolveFunRightStage_def {h : ℕ} (φ : AnalyticStage p h K →L[K] K) :
    convolveFunRightStage φ =
      (compLeft φ (φ.bound.imp fun _ hb ↦ hb.2)).comp (comulCurried K) :=
  (rfl)

/-- Coordinatewise formula for `convolveFunRightStage φ`. -/
@[simp]
theorem convolveFunRightStage_apply {h : ℕ} (φ : AnalyticStage p h K →L[K] K)
    (c : AnalyticStage p h K) (i : ZMod (p ^ h) × ℕ) :
    convolveFunRightStage φ c i = φ (comulCurried K c i) := by
  simp [convolveFunRightStage]

private theorem convolveFunRightStage_apply_eq {h : ℕ} (φ : AnalyticStage p h K →L[K] K)
    (c : AnalyticStage p h K) :
    convolveFunRightStage φ c =
      compLeft φ (φ.bound.imp fun _ hb ↦ hb.2) (comulCurried K c) :=
  (rfl)

omit [Fact p.Prime] [Algebra ℤ_[p] K] [IsBoundedSMul ℤ_[p] K] [IsUltrametricDist K]
  [CompleteSpace K] in
private theorem compLeft_comp_clm {h : ℕ} {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace K E]
    [NormedAddCommGroup F] [NormedSpace K F]
    [NormedAddCommGroup G] [NormedSpace K G]
    (v : F →L[K] G) (u : E →L[K] F) (f : AnalyticStage p h E) :
    compLeft (v.comp u) ((v.comp u).bound.imp fun _ hb ↦ hb.2) f =
      compLeft v (v.bound.imp fun _ hb ↦ hb.2)
        (compLeft u (u.bound.imp fun _ hb ↦ hb.2) f) := by
  rw [compLeft_comp v u (v.bound.imp fun _ hb ↦ hb.2) (u.bound.imp fun _ hb ↦ hb.2)
    ((v.comp u).bound.imp fun _ hb ↦ hb.2), ContinuousLinearMap.comp_apply]

/-- `convolveFunRightStage φ` is bounded by `‖φ‖`. -/
theorem norm_convolveFunRightStage_apply_le {h : ℕ} (φ : AnalyticStage p h K →L[K] K)
    (c : AnalyticStage p h K) :
    ‖convolveFunRightStage φ c‖ ≤ ‖φ‖ * ‖c‖ := by
  rw [convolveFunRightStage_apply_eq]
  exact (norm_compLeft_apply_le φ φ.le_opNorm _).trans (by rw [norm_comulCurried])

/-- The operator norm of `convolveFunRightStage φ` is at most `‖φ‖`. -/
theorem opNorm_convolveFunRightStage_le {h : ℕ} (φ : AnalyticStage p h K →L[K] K) :
    ‖convolveFunRightStage φ‖ ≤ ‖φ‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg φ) (norm_convolveFunRightStage_apply_le φ)

/-- Evaluating `convolveFunRightStage φ c` at `x` applies `φ` to the translate of `c` by `x`. -/
@[simp]
theorem eval_convolveFunRightStage {h : ℕ} (φ : AnalyticStage p h K →L[K] K)
    (c : AnalyticStage p h K) (x : ℤ_[p]) :
    AnalyticStage.eval K (convolveFunRightStage φ c) x = φ (AnalyticStage.translate K x c) := by
  rw [convolveFunRightStage_apply_eq, eval_compLeft K, translate_eq_eval_comulCurried]

/-- Evaluating `convolveFunRightStage φ c` at `0` recovers `φ c`. -/
theorem eval_convolveFunRightStage_zero {h : ℕ} (φ : AnalyticStage p h K →L[K] K)
    (c : AnalyticStage p h K) :
    AnalyticStage.eval K (convolveFunRightStage φ c) 0 = φ c := by
  simp

/-- The stage-level right convolution action `convolveFunRightStage` is injective. -/
theorem convolveFunRightStage_injective {h : ℕ} :
    Function.Injective (convolveFunRightStage (p := p) (K := K) (h := h)) := by
  intro φ ψ hφψ
  ext c
  simpa only [eval_convolveFunRightStage_zero] using
    congrArg (fun T ↦ AnalyticStage.eval K (T c) 0) hφψ

/-- Stage-level right convolution commutes with adjacent stage transitions: applying `ψ` after
refining equals refining after applying `ψ ∘ transition`. -/
theorem convolveFunRightStage_transition {h : ℕ} (ψ : AnalyticStage p (h + 1) K →L[K] K)
    (c : AnalyticStage p h K) :
    convolveFunRightStage ψ (transition K c) =
      transition K (convolveFunRightStage (ψ.comp (transition K)) c) := by
  rw [convolveFunRightStage_apply_eq, convolveFunRightStage_apply_eq,
    ← transition_compLeft_transition_comulCurried K c, ← transition_compLeft K,
    compLeft_comp_clm]

/-- Stage-level right convolution commutes with multi-level stage transitions. -/
theorem convolveFunRightStage_transitionLE {h k : ℕ} (hhk : h ≤ k)
    (ψ : AnalyticStage p k K →L[K] K) (c : AnalyticStage p h K) :
    convolveFunRightStage ψ (transitionLE K hhk c) =
      transitionLE K hhk (convolveFunRightStage (ψ.comp (transitionLE K hhk)) c) := by
  induction k, hhk using Nat.le_induction with
  | base => simp
  | succ k hhk ih =>
    rw [transitionLE_succ K hhk, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      convolveFunRightStage_transition, ih, ← ContinuousLinearMap.comp_assoc]

/-- Stage-level right convolution is associative with respect to composition of stage
functionals. -/
theorem convolveFunRightStage_comp {h : ℕ} (φ ψ : AnalyticStage p h K →L[K] K) :
    convolveFunRightStage (φ.comp (convolveFunRightStage ψ)) =
      (convolveFunRightStage φ).comp (convolveFunRightStage ψ) := by
  refine ContinuousLinearMap.ext fun c ↦ ?_
  have hinner : compLeft (convolveFunRightStage ψ)
        ((convolveFunRightStage ψ).bound.imp fun _ hb ↦ hb.2) (comulCurried K c) =
      comulCurried K (convolveFunRightStage ψ c) := by
    conv_lhs => simp only [convolveFunRightStage_def]
    rw [compLeft_comp_clm, ← comulCurried_comulCurried, ← comulCurried_compLeft,
      ← convolveFunRightStage_apply_eq]
  rw [ContinuousLinearMap.comp_apply, convolveFunRightStage_apply_eq, compLeft_comp_clm, hinner,
    ← convolveFunRightStage_apply_eq]

/-- Stage-level right convolution with coordinate evaluation at `(0, 0)` is the identity
operator. -/
@[simp]
theorem convolveFunRightStage_evalCLM_zero (h : ℕ) :
    convolveFunRightStage (evalCLM K (0, 0) : AnalyticStage p h K →L[K] K) =
      ContinuousLinearMap.id K _ := by
  ext c i
  simp

end TauCeti.LocallyAnalyticDistribution
