/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import TauCeti.Analysis.Normed.Operator.DunfordPettis.Basic
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basic
import Mathlib.Analysis.Normed.Module.DoubleDual
import TauCeti.Analysis.Normed.Lp.Schur
import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Dual
import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Reflexive

/-!
# The Dunford–Pettis property through the dual, and `c₀`

This file derives the Dunford–Pettis property of a normed space from properties of its dual,
using the sequence criterion `TauCeti.hasDunfordPettisProperty_iff`, and applies this to `c₀`.

* If every weakly null sequence in the dual of `E` is norm null, then `E` has the Dunford–Pettis
  property: a weakly null sequence in `E` is bounded.
* If the dual of `E` has the Dunford–Pettis property, so does `E`: the canonical embedding into
  the bidual carries weakly null sequences in `E` to weakly null sequences in the dual of
  `StrongDual 𝕜 E`.
* By the duality `C₀(ι, 𝕜)* = ℓ¹` and Schur's theorem for `ℓ¹`, the space `C₀(ι, 𝕜)` has the
  Dunford–Pettis property.

The space `c₀` also shows that weakly null sequences of functionals cannot be replaced by weak-star
null ones in the sequence criterion: the unit vectors are weakly null, the coordinate functionals
are weak-star null, and they pair to `1`.

## Main results

* `TauCeti.hasDunfordPettisProperty_of_tendsto_dual`: weakly null sequences in the dual being norm
  null implies the Dunford–Pettis property.
* `TauCeti.HasDunfordPettisProperty.of_dual`: the Dunford–Pettis property passes from the dual to
  the space.
* `ZeroAtInftyContinuousMap.hasDunfordPettisProperty`: `c₀` has the Dunford–Pettis property.
* `ZeroAtInftyContinuousMap.tendsto_toWeakDual_evalCLM_cofinite`: the coordinate functionals of
  `c₀` are weak-star null.
* `ZeroAtInftyContinuousMap.not_forall_tendsto_apply_of_tendsto_toWeakDual`: the sequence
  criterion fails for weak-star null sequences of functionals on `c₀`.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, §5.4.
-/

public section

open Filter Function NormedSpace Topology
open scoped ZeroAtInfty

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- If every weakly null sequence in the dual of `E` is norm null (the dual has the Schur
property), then `E` has the Dunford–Pettis property. -/
theorem hasDunfordPettisProperty_of_tendsto_dual
    (h : ∀ ⦃f : ℕ → StrongDual 𝕜 E⦄,
      Tendsto (fun n ↦ toWeakSpace 𝕜 (StrongDual 𝕜 E) (f n)) atTop (𝓝 0) →
        Tendsto f atTop (𝓝 0)) :
    HasDunfordPettisProperty 𝕜 E := by
  refine hasDunfordPettisProperty_iff.2 fun x f hx hf ↦ ?_
  -- A weakly null sequence is bounded, and `‖f n (x n)‖ ≤ ‖f n‖ ‖x n‖`.
  rw [← map_zero (toWeakSpace 𝕜 E)] at hx
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hx.isBounded_range_of_toWeakSpace
  refine squeeze_zero_norm (fun n ↦ (f n).le_opNorm (x n) |>.trans ?_)
    (by simpa using (h hf).norm.mul_const C)
  exact mul_le_mul_of_nonneg_left (hC _ ⟨n, rfl⟩) (norm_nonneg _)

/-- If the dual of `E` has the Dunford–Pettis property, then so does `E`. -/
theorem HasDunfordPettisProperty.of_dual (h : HasDunfordPettisProperty 𝕜 (StrongDual 𝕜 E)) :
    HasDunfordPettisProperty 𝕜 E := by
  refine hasDunfordPettisProperty_iff.2 fun x f hx hf ↦ ?_
  -- The canonical embedding `J` into the bidual is weakly continuous, so `J ∘ x` is weakly null;
  -- `WeakSpace.map J` acts as `J` on `WeakSpace 𝕜 E = E` (`WeakSpace.map_apply`).
  rw [← map_zero (toWeakSpace 𝕜 E)] at hx
  have hJx : Tendsto
      (fun n ↦ toWeakSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 E)) (inclusionInDoubleDual 𝕜 E (x n)))
      atTop (𝓝 (toWeakSpace 𝕜 _ (inclusionInDoubleDual 𝕜 E 0))) :=
    ((WeakSpace.map (inclusionInDoubleDual 𝕜 E)).continuous.tendsto _).comp hx
  rw [map_zero, map_zero] at hJx
  simpa using h.tendsto_apply hf hJx

end TauCeti

namespace ZeroAtInftyContinuousMap

variable {𝕜 ι : Type*} [RCLike 𝕜] [TopologicalSpace ι] [DiscreteTopology ι]

variable (𝕜 ι) in
/-- **The Dunford–Pettis property of `c₀`.** On a discrete index type, `C₀(ι, 𝕜)` has the
Dunford–Pettis property. -/
theorem hasDunfordPettisProperty : TauCeti.HasDunfordPettisProperty 𝕜 C₀(ι, 𝕜) := by
  refine TauCeti.hasDunfordPettisProperty_of_tendsto_dual fun f hf ↦ ?_
  -- Under `C₀(ι, 𝕜)* = ℓ¹` the sequence is weakly null in `ℓ¹`, hence norm null by Schur;
  -- `WeakSpace.map` acts as the underlying map (`WeakSpace.map_apply`).
  let e := (dualEquiv 𝕜 ι).toContinuousLinearEquiv
  rw [← map_zero (toWeakSpace 𝕜 (StrongDual 𝕜 C₀(ι, 𝕜)))] at hf
  have hf' : Tendsto (fun n ↦ toWeakSpace 𝕜 (lp (fun _ : ι ↦ 𝕜) 1) (e.symm (f n))) atTop
      (𝓝 (toWeakSpace 𝕜 (lp (fun _ : ι ↦ 𝕜) 1) (e.symm 0))) :=
    ((WeakSpace.map e.symm.toContinuousLinearMap).continuous.tendsto _).comp hf
  rw [map_zero] at hf'
  simpa [Function.comp_def] using
    (e.continuous.tendsto 0).comp (lp.tendsto_of_tendsto_toWeakSpace_one hf')

variable (𝕜) in
/-- The coordinate functionals of `C₀(ι, 𝕜)` tend to zero in the weak-star topology along the
cofinite filter. -/
theorem tendsto_toWeakDual_evalCLM_cofinite :
    Tendsto (fun i : ι ↦ StrongDual.toWeakDual (evalCLM 𝕜 i : StrongDual 𝕜 C₀(ι, 𝕜))) cofinite
      (𝓝 0) :=
  tendsto_iff_forall_eval_tendsto_topDualPairing.2 fun f ↦ by
    have : Tendsto (fun i ↦ evalCLM 𝕜 i f) cofinite (𝓝 0) := by simpa using f.tendsto_cofinite
    -- `topDualPairing 𝕜 _ (StrongDual.toWeakDual g) f` is `g f` by definition of the pairing.
    exact this

variable (𝕜 ι) in
/-- Weak-star null sequences of functionals cannot replace weakly null ones in the sequence
criterion for the Dunford–Pettis property (`TauCeti.hasDunfordPettisProperty_iff`): on an infinite
discrete index type, a sequence of distinct unit vectors of `C₀(ι, 𝕜)` is weakly null, the
corresponding coordinate functionals are weak-star null, and every pairing equals `1`. -/
theorem not_forall_tendsto_apply_of_tendsto_toWeakDual [Infinite ι] :
    ¬ ∀ ⦃x : ℕ → C₀(ι, 𝕜)⦄ ⦃f : ℕ → StrongDual 𝕜 C₀(ι, 𝕜)⦄,
        Tendsto (fun n ↦ toWeakSpace 𝕜 C₀(ι, 𝕜) (x n)) atTop (𝓝 0) →
          Tendsto (fun n ↦ StrongDual.toWeakDual (f n)) atTop (𝓝 0) →
            Tendsto (fun n ↦ f n (x n)) atTop (𝓝 0) := by
  classical
  intro h
  let u := Infinite.natEmbedding ι
  have hu : Tendsto u atTop cofinite := Nat.cofinite_eq_atTop ▸ u.injective.tendsto_cofinite
  have h₁ := h (x := fun n ↦ single (u n) 1) (f := fun n ↦ evalCLM 𝕜 (u n))
    (by simpa [Function.comp_def] using (tendsto_toWeakSpace_single_one_cofinite (𝕜 := 𝕜)).comp hu)
    ((tendsto_toWeakDual_evalCLM_cofinite 𝕜).comp hu)
  simp only [evalCLM_apply, single_eq_same] at h₁
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h₁)

end ZeroAtInftyContinuousMap
