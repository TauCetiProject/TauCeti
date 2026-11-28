/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.InwardSemiflow.Smooth
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smoothness of quadratic inward semiflow deformations

Proves joint `C^m` smoothness (`1 ≤ m`, including `m = ∞`) on `univ ×ˢ (U ∩ C)` (in the globally
forward-complete case) and on `Icc 0 1 ×ˢ (U ∩ C)` (in the finite-time case) for the quadratic
time-reparametrized inward deformation
`p ↦ TauCeti.forwardSemiflow X (U ∩ C) (T * (1 - p.1) ^ 2) p.2`.
-/

public section

open Set
open scoped ContDiff

section QuadraticDeformationSmooth

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Global real-time `C^m` smoothness of the quadratic inward deformation.** Given a `C^m`
(`1 ≤ m`, including `m = ∞`) vector field `X` on `U ∩ C` (`U` open, `C` convex) that is strictly
inward to `C` on `U ∩ C` and globally forward complete on `U ∩ C`
(`forwardSemiflowInterval X (U ∩ C) x = Ici 0`), and `0 ≤ T`, the reparametrized semiflow
`fun p : ℝ × E ↦ forwardSemiflow X (U ∩ C) (T * (1 - p.1) ^ 2) p.2` is `C^m` on
`univ ×ˢ (U ∩ C)`, agreeing with `forwardSemiflow X (U ∩ C) T` at `p.1 = 0` and the identity at
`p.1 = 1`. -/
theorem Convex.contDiffOn_forwardSemiflow_mul_one_sub_sq_univ_prod
    {C U : Set E} (hC : Convex ℝ C) (hU : IsOpen U)
    {m : ℕ∞} (hm : 1 ≤ m) {X : E → E} (hX : ContDiffOn ℝ m X (U ∩ C))
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ TauCeti.strictInwardCone C x)
    (hglob : ∀ x ∈ U ∩ C, TauCeti.forwardSemiflowInterval X (U ∩ C) x = Ici 0)
    {T : ℝ} (hT_nonneg : 0 ≤ T) :
    ContDiffOn ℝ m
      (fun p : ℝ × E ↦ TauCeti.forwardSemiflow X (U ∩ C) (T * (1 - p.1) ^ 2) p.2)
      (univ ×ˢ (U ∩ C)) :=
  hC.contDiffOn_forwardSemiflow_comp hU hm hX hX_in
    (contDiffOn_const.mul ((contDiffOn_const.sub contDiffOn_id).pow 2))
    fun _ _ x hx ↦ hglob x hx ▸ mul_nonneg hT_nonneg (sq_nonneg _)

/-- **Finite-time `C^m` smoothness of the quadratic inward deformation.** Given a `C^m` (`1 ≤ m`,
including `m = ∞`) vector field `X` on `U ∩ C` (`U` open, `C` convex) that is strictly inward
to `C` on `U ∩ C` and defined through time `T ≥ 0` for every `x ∈ U ∩ C`, the reparametrized
semiflow `fun p : ℝ × E ↦ forwardSemiflow X (U ∩ C) (T * (1 - p.1) ^ 2) p.2` is `C^m` on
`Icc 0 1 ×ˢ (U ∩ C)`. -/
theorem Convex.contDiffOn_forwardSemiflow_mul_one_sub_sq_Icc_prod {C U : Set E} (hC : Convex ℝ C)
    (hU : IsOpen U) {m : ℕ∞} (hm : 1 ≤ m) {X : E → E} (hX : ContDiffOn ℝ m X (U ∩ C))
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ TauCeti.strictInwardCone C x)
    {T : ℝ} (hT_nonneg : 0 ≤ T)
    (hT : ∀ x ∈ U ∩ C, T ∈ TauCeti.forwardSemiflowInterval X (U ∩ C) x) :
    ContDiffOn ℝ m
      (fun p : ℝ × E ↦ TauCeti.forwardSemiflow X (U ∩ C) (T * (1 - p.1) ^ 2) p.2)
      (Icc 0 1 ×ˢ (U ∩ C)) :=
  hC.contDiffOn_forwardSemiflow_comp hU hm hX hX_in
    (contDiffOn_const.mul ((contDiffOn_const.sub contDiffOn_id).pow 2))
    fun _ ht _ hx ↦ TauCeti.Icc_subset_forwardSemiflowInterval_of_mem (hT _ hx)
      ⟨mul_nonneg hT_nonneg (sq_nonneg _),
        mul_le_of_le_one_right hT_nonneg (by dsimp only [id_eq]; nlinarith [ht.1, ht.2])⟩

end QuadraticDeformationSmooth
