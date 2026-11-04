/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Strict tangent inequalities on the closure of a convex domain

A differentiable strictly convex function on an open set has a strict tangent inequality
even at other points of its closure where the function remains convex.

The proof follows the [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/e60bc39b18ef691263c66e2dba8d64726f18060d/formalization/FunctionalInequalities/Analysis/Convex/ContactMeasure.lean#L993).
-/

public section

open Set

/-- An injective affine change of variables preserves strict convexity on the preimage. -/
theorem StrictConvexOn.comp_affineMap_of_injective
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    {S : Set E} {v : E → ℝ} (hv : StrictConvexOn ℝ S v) (A : F →ᵃ[ℝ] E)
    (hA : Function.Injective A) : StrictConvexOn ℝ (A ⁻¹' S) (v ∘ A) := by
  refine ⟨hv.1.affine_preimage A, fun a ha b hb hab p q hp hq hpq => ?_⟩
  simp only [Function.comp_apply, Convex.combo_affine_apply hpq]
  exact hv.2 ha hb (fun h => hab (hA h)) hp hq hpq

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The tangent at an interior point of a strictly convex function lies strictly below every
other point of its graph on the closure, provided the function is convex there. -/
theorem StrictConvexOn.fderiv_lt_sub_of_mem_closure {S : Set E} {v : E → ℝ}
    (hvs : StrictConvexOn ℝ S v) (hSo : IsOpen S) (hv : ConvexOn ℝ (closure S) v)
    {z y : E} (hz : z ∈ S) (hy : y ∈ closure S) (hzy : z ≠ y)
    (hd : DifferentiableAt ℝ v z) : fderiv ℝ v z (y - z) < v y - v z := by
  let A : ℝ →ᵃ[ℝ] E := AffineMap.lineMap z y
  have hA : Function.Injective A := AffineMap.lineMap_injective ℝ hzy
  have hs := hvs.comp_affineMap_of_injective A hA
  have h0 : (0 : ℝ) ∈ A ⁻¹' S := by simpa [A] using hz
  have hAhalf : A (1 / 2) = (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • y := by
    dsimp only [A]
    rw [AffineMap.lineMap_apply_module, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  have hmidseg : A (1 / 2) ∈ openSegment ℝ z y := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, ?_⟩
    exact hAhalf.symm
  have hmid : (1 / 2 : ℝ) ∈ A ⁻¹' S := by
    rw [mem_preimage]
    have hz' : z ∈ interior S := by simpa only [hSo.interior_eq] using hz
    simpa only [hSo.interior_eq] using
      hvs.1.openSegment_interior_closure_subset_interior hz' hy hmidseg
  have hD : HasDerivAt (v ∘ A) (fderiv ℝ v z (y - z)) 0 := by
    have hL : HasDerivAt A (y - z) 0 := AffineMap.hasDerivAt_lineMap
    have hA0 : A 0 = z := AffineMap.lineMap_apply_zero _ _
    have hvA : HasFDerivAt v (fderiv ℝ v z) (A 0) := by simpa only [hA0] using hd.hasFDerivAt
    exact hvA.comp_hasDerivAt 0 hL
  have hstrict := hs.lt_slope_of_hasDerivAt h0 hmid (by norm_num) hD
  have hchord : v (A (1 / 2)) ≤ (1 / 2 : ℝ) * v z + (1 / 2 : ℝ) * v y := by
    have h := hv.2 (subset_closure hz) hy (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
    simpa only [hAhalf, smul_eq_mul] using h
  simp only [slope_def_field, Function.comp_apply, sub_zero, A,
    AffineMap.lineMap_apply_zero] at hstrict
  dsimp only [A] at hchord
  linarith
