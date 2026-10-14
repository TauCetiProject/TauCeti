/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import TauCeti.Analysis.Calculus.FDeriv.Submodule
public import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Smoothness through a closed linear isometric inclusion

For finite orders and `∞`, smoothness can be checked after composing with a linear
isometry whose range is closed. Derivatives remain in the closed range and hence lift,
with their norms and continuity preserved. This gives the smooth alternating-map
pullback needed for differential-form coordinate changes without a characteristic
restriction. The analytic order `ω` is not covered by this criterion.
-/

public section

open Filter Set
open scoped Topology ContDiff
noncomputable section
variable {𝕜 D E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- For finite orders and `∞`, a closed linear isometric inclusion reflects smoothness.
No completeness assumption is needed. -/
theorem LinearIsometry.contDiff_comp_iff (i : E →ₗᵢ[𝕜] F)
    (hi : IsClosed (range i)) {f : D → E} {n : ℕ∞} :
    ContDiff 𝕜 n (i ∘ f) ↔ ContDiff 𝕜 n f := by
  constructor
  · intro h
    classical
    obtain ⟨q, hq⟩ := h
    let R (m : ℕ) : Submodule 𝕜 (D [×m]→L[𝕜] F) :=
      { carrier := {a | ∀ v, a v ∈ i.toLinearMap.range}
        zero_mem' := fun _ ↦ ⟨0, i.map_zero⟩
        add_mem' := fun ha hb v ↦ i.toLinearMap.range.add_mem (ha v) (hb v)
        smul_mem' := fun c _ ha v ↦ i.toLinearMap.range.smul_mem c (ha v) }
    have hR (m : ℕ) : IsClosed (R m : Set (D [×m]→L[𝕜] F)) := by
      -- Unfold the carrier of R and the linear-map range to expose the pointwise
      -- conditions whose closedness follows from continuous evaluation.
      change IsClosed {a : D [×m]→L[𝕜] F | ∀ v, a v ∈ range i}
      simp only [ofPred_forall]
      exact isClosed_iInter fun v ↦ hi.preimage (continuous_eval_const v)
    have hQ : ∀ m : ℕ, m ≤ (n : WithTop ℕ∞) → ∀ x v, q x m v ∈ i.toLinearMap.range := by
      intro m
      induction m with
      | zero =>
        intro _ x v
        rw [hq.zero_eq']
        exact ⟨f x, rfl⟩
      | succ m ih =>
        intro hm x v
        have hmn : (m : WithTop ℕ∞) < n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) hm
        have hv := (hq.fderiv m hmn x).apply_mem_of_eventually_sub_mem (hR m)
          (Eventually.of_forall fun y ↦
            (R m).sub_mem (ih (le_of_lt hmn) y) (ih (le_of_lt hmn) x)) (v 0)
        simpa only [ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail]
          using hv (Fin.tail v)
    let J (m : ℕ) : (D [×m]→L[𝕜] E) →ₗᵢ[𝕜] (D [×m]→L[𝕜] F) :=
      { toLinearMap := (ContinuousLinearMap.compContinuousMultilinearMapL
          𝕜 (fun _ : Fin m ↦ D) E F i.toContinuousLinearMap).toLinearMap
        norm_map' := i.norm_compContinuousMultilinearMap }
    let p : D → FormalMultilinearSeries 𝕜 D E := fun x m ↦
      if hm : (m : WithTop ℕ∞) ≤ n then
        i.equivRange.symm.toContinuousLinearEquiv.toContinuousLinearMap.compContinuousMultilinearMap
          ((q x m).codRestrict i.toLinearMap.range (hQ m hm x))
      else 0
    have hJp (m : ℕ) (hm : (m : WithTop ℕ∞) ≤ n) (x : D) : J m (p x m) = q x m := by
      ext v
      -- J is postcomposition by i, so its evaluation is definitionally i (p x m v).
      -- Exposing this expression lets the range-equivalence cancellation below apply.
      change i (p x m v) = q x m v
      simp only [p, dite_eq_left hm, ContinuousLinearMap.compContinuousMultilinearMap_coe,
        Function.comp_apply]
      exact congrArg Subtype.val (i.equivRange.apply_symm_apply ⟨q x m v, hQ m hm x v⟩)
    refine ⟨p, ?_⟩
    constructor
    · intro x
      apply i.injective
      rw [ContinuousMultilinearMap.curry0_apply]
      -- Postcomposition by i at the unique zero-arity tuple is evaluation of J 0.
      -- This definitional conversion puts the goal in the form established by hJp.
      change J 0 (p x 0) 0 = i (f x)
      rw [hJp 0 (by simp)]
      exact hq.zero_eq x
    · intro m hm x
      have hm' : (m : WithTop ℕ∞) ≤ n := le_of_lt hm
      have hs : ((m + 1 : ℕ) : WithTop ℕ∞) ≤ n := ENat.add_one_natCast_le_withTop_of_lt hm
      have hc : Continuous (fun y ↦ p y m) :=
        (J m).comp_continuous_iff.mp
          (by simpa only [Function.comp_def, hJp m hm'] using hq.cont m hm')
      have hd : (J m).toContinuousLinearMap.comp (p x (m + 1)).curryLeft =
          (q x (m + 1)).curryLeft := by
        ext v w
        exact congrArg (fun a : D [×(m + 1)]→L[𝕜] F ↦ a (Fin.cons v w)) (hJp (m + 1) hs x)
      exact HasFDerivAt.of_comp_of_isEmbedding hc.continuousAt
        (J m).toContinuousLinearMap.hasFDerivAt (J m).isEmbedding
        (by simpa only [hd] using hq.fderiv m hm x)
        (Eventually.of_forall fun y ↦ hJp m hm' y)
    · intro m hm
      exact (J m).comp_continuous_iff.mp
        (by simpa only [Function.comp_def, hJp m hm] using hq.cont m hm)
  · intro h
    exact i.contDiff.comp h
