/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Hessian upper bounds from semiconcavity

Concavity after subtracting a quadratic bounds the diagonal second derivative on an open set.
Only twice continuous differentiability is needed.

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public section

open Set Filter
open scoped Topology ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A smooth semiconcave function has the corresponding actual Hessian bound
at every point of its open domain. -/
theorem fderiv_fderiv_le_of_concaveOn_sub_norm_sq
    {f : E → ℝ} {U : Set E} {C : ℝ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U)
    (hconc : ConcaveOn ℝ U (fun y ↦ f y - C * ‖y‖ ^ 2 / 2))
    {x : E} (hx : x ∈ U) (v : E) :
    fderiv ℝ (fderiv ℝ f) x v v ≤ C * ‖v‖ ^ 2 := by
  let A : ℝ → E := fun t ↦ x + t • v
  let q : ℝ → ℝ := fun t ↦ f (A t) - C * ‖A t‖ ^ 2 / 2
  let q' : ℝ → ℝ := fun t ↦ fderiv ℝ f (A t) v - C * inner ℝ (A t) v
  have hA (t : ℝ) : HasDerivAt A v t := by
    simpa [A] using ((hasDerivAt_id t).smul_const v).const_add x
  have hAo : IsOpen (A ⁻¹' U) := hU.preimage (by fun_prop)
  have hA0 : (0 : ℝ) ∈ A ⁻¹' U := by simpa [A] using hx
  have hq : ConcaveOn ℝ (A ⁻¹' U) q := by
    simpa [A, q, Function.comp_def, AffineMap.coe_lineMap, add_comm] using
      hconc.comp_affineMap (AffineMap.lineMap x (x + v))
  have hd (t : ℝ) (ht : t ∈ A ⁻¹' U) : HasDerivAt q (q' t) t := by
    have hft := (hf.contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp)
    change HasDerivAt (fun t ↦ f (A t) - C * ‖A t‖ ^ 2 / 2)
      (fderiv ℝ f (A t) v - C * inner ℝ (A t) v) t
    convert (hft.hasFDerivAt.comp_hasDerivAt t (hA t)).sub
      (((hA t).norm_sq.const_mul C).div_const 2) using 1 <;> first | rfl | ring
  have hant : AntitoneOn (deriv q) (A ⁻¹' U) :=
    hq.antitoneOn_deriv (fun t ht ↦ (hd t ht).differentiableAt)
  have hn : deriv (deriv q) 0 ≤ 0 := by
    rw [← derivWithin_of_mem_nhds (hAo.mem_nhds hA0)]
    exact hant.derivWithin_nonpos
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_of_isOpen hU (m := 1) (by norm_num)).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by simp)
  have hlinear : HasDerivAt (fun t ↦ fderiv ℝ f (A t) v)
      (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
    have hfd' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) (A 0) := by
      simpa [A] using hfd.hasFDerivAt
    have h := (hfd'.comp_hasDerivAt 0 (hA 0)).clm_apply (hasDerivAt_const 0 v)
    simpa [A] using h
  have hinner : HasDerivAt (fun t ↦ inner ℝ (A t) v) (‖v‖ ^ 2) 0 := by
    simpa using (hA 0).inner ℝ (hasDerivAt_const 0 v)
  have hsecond : HasDerivAt (deriv q)
      (fderiv ℝ (fderiv ℝ f) x v v - C * ‖v‖ ^ 2) 0 := by
    apply (hlinear.sub (hinner.const_mul C)).congr_of_eventuallyEq
    filter_upwards [hAo.mem_nhds hA0] with t ht
    exact (hd t ht).deriv
  rw [hsecond.deriv] at hn
  linarith

/-- Translating a function preserves its quadratic concavity bound. -/
theorem concaveOn_sub_norm_sq_translate {f : E → ℝ} {C : ℝ} {s T : Set E}
    (hf : ConcaveOn ℝ T (fun x ↦ f x - C * ‖x‖ ^ 2 / 2))
    (hs : Convex ℝ s) (t : E) (hsub : ∀ x ∈ s, x - t ∈ T) :
    ConcaveOn ℝ s (fun x ↦ f (x - t) - C * ‖x‖ ^ 2 / 2) := by
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have h := hf.2 (hsub x hx) (hsub y hy) ha hb hab
  have ht : a • (x - t) + b • (y - t) = (a • x + b • y) - t := by
    rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul]
  rw [ht] at h
  simp only [norm_sub_sq_real, inner_add_left, real_inner_smul_left,
    smul_eq_mul] at h ⊢
  have hb' : b = 1 - a := by linarith
  rw [hb'] at h ⊢
  nlinarith [h]

end TauCeti
