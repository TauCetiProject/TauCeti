/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Secants of a differentiable map on an open set

The difference of a continuously differentiable real-valued map at the ends of a segment is
the integral of its derivative along that segment. The whole segment must lie in the open
domain of differentiability.
-/

public noncomputable section

open Set
open scoped Convex Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The exact secant formula for a `C¹` function on an open neighborhood of a segment. -/
theorem integral_fderiv_lineMap_eq_sub {U : Set V} (hU : IsOpen U)
    {F : V → ℝ} (hF : ContDiffOn ℝ 1 F U) {a b : V}
    (hseg : [a -[ℝ] b] ⊆ U) :
    (∫ t in (0 : ℝ)..1, fderiv ℝ F (a + t • (b - a)) (b - a)) = F b - F a := by
  let γ : ℝ → V := fun t ↦ a + t • (b - a)
  have hγ : Continuous γ := by
    dsimp [γ]
    fun_prop
  have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t ∈ U := by
    have hline : γ t = (1 - t) • a + t • b := by
      dsimp [γ]
      module
    rw [hline]
    exact hseg (by simpa only [AffineMap.lineMap_apply_module] using
      lineMap_mem_segment ℝ a b ht)
  have hcont : ContinuousOn (fun t : ℝ ↦ fderiv ℝ F (γ t) (b - a))
      (Icc (0 : ℝ) 1) :=
    ((hF.continuousOn_fderiv_of_isOpen hU (by norm_num)).comp
      hγ.continuousOn hmem).clm_apply continuousOn_const
  have hpath : ContinuousOn (F ∘ γ) (Icc (0 : ℝ) 1) :=
    hF.continuousOn.comp hγ.continuousOn hmem
  have hderiv (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (F ∘ γ) (fderiv ℝ F (γ t) (b - a)) t := by
    have hγderiv : HasDerivAt γ (b - a) t := by
      simpa only [id_eq, one_smul] using
        (hasDerivAt_id t).smul_const (b - a) |>.const_add a
    have hFderiv : HasFDerivAt F (fderiv ℝ F (γ t)) (γ t) :=
      ((hF.contDiffAt (hU.mem_nhds (hmem t (Ioo_subset_Icc_self ht)))).differentiableAt
        (by norm_num)).hasFDerivAt
    exact hFderiv.comp_hasDerivAt t hγderiv
  have hint : IntervalIntegrable
      (fun t : ℝ ↦ fderiv ℝ F (γ t) (b - a)) MeasureTheory.volume 0 1 :=
    hcont.intervalIntegrable_of_Icc zero_le_one
  simpa [γ] using
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hpath hderiv hint

end TauCeti
