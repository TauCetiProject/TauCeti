/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import TauCeti.Analysis.Calculus.FDeriv.Submodule
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Taylor derivatives in subspaces and through isometries

For `HasFTaylorSeriesUpTo n f q`, if `f` takes values in a closed subspace,
then the Taylor coefficients `q x m` take values there at every order `m ≤ n`. The proof uses
the closed-subspace derivative criterion at each successive order.

A linear isometry lifts a Taylor derivative series when its coefficients lie in the
isometry’s range; this lifting does not require the range to be closed.
-/

public section

open Filter Set
open scoped ContDiff

variable {𝕜 D F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup D] [NormedSpace 𝕜 D]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : WithTop ℕ∞} {f : D → F} {q : D → FormalMultilinearSeries 𝕜 D F}
  {S : Submodule 𝕜 F}

/-- For a Taylor derivative series up to order `n` of a function valued in a closed subspace,
the coefficients of every order `m ≤ n` take values in that subspace. -/
theorem HasFTaylorSeriesUpTo.apply_mem_of_range_subset
    (hq : HasFTaylorSeriesUpTo n f q) (hS : IsClosed (S : Set F))
    (hf : range f ⊆ S) (m : ℕ) (hm : m ≤ n) (x : D) (v : Fin m → D) : q x m v ∈ S := by
  let R (m : ℕ) : Submodule 𝕜 (D [×m]→L[𝕜] F) :=
    { carrier := {a | ∀ v, a v ∈ S}
      zero_mem' := fun _ ↦ S.zero_mem
      add_mem' := fun ha hb v ↦ S.add_mem (ha v) (hb v)
      smul_mem' := fun c _ ha v ↦ S.smul_mem c (ha v) }
  have hR (m : ℕ) : IsClosed (R m : Set (D [×m]→L[𝕜] F)) := by
    -- Unfold the carrier so closedness follows from the evaluation preimages.
    change IsClosed {a : D [×m]→L[𝕜] F | ∀ v, a v ∈ S}
    simp only [ofPred_forall]
    exact isClosed_iInter fun v ↦ hS.preimage (continuous_eval_const v)
  induction m generalizing x with
  | zero =>
    rw [hq.zero_eq']
    exact hf ⟨x, rfl⟩
  | succ m ih =>
    have hmn : (m : WithTop ℕ∞) < n := lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self m) hm
    have hv := (hq.fderiv m hmn x).apply_mem_of_eventually_sub_mem (hR m)
      (Eventually.of_forall fun y ↦ (R m).sub_mem
        (ih (le_of_lt hmn) y) (ih (le_of_lt hmn) x)) (v 0)
    simpa only [ContinuousMultilinearMap.curryLeft_apply, Fin.cons_self_tail]
      using hv (Fin.tail v)
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A Taylor derivative series of `i ∘ f` lifts through the linear isometry `i` when its
coefficients of orders `m ≤ n` lie in the range of `i`. No closed-range assumption is needed. -/
theorem LinearIsometry.exists_hasFTaylorSeriesUpTo_of_comp (i : E →ₗᵢ[𝕜] F)
    {f : D → E} {n : WithTop ℕ∞} {q : D → FormalMultilinearSeries 𝕜 D F}
    (hq : HasFTaylorSeriesUpTo n (i ∘ f) q)
    (hQ : ∀ m : ℕ, m ≤ n → ∀ x v, q x m v ∈ i.toLinearMap.range) :
    ∃ p : D → FormalMultilinearSeries 𝕜 D E, HasFTaylorSeriesUpTo n f p := by
  classical
  -- Lift each coefficient through the range equivalence. Isometric postcomposition
  -- then reflects the continuity and derivative relations required by the series.
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
