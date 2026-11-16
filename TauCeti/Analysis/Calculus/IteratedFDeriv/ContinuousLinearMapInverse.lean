/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
import TauCeti.Analysis.Calculus.IteratedFDeriv.Bilinear

/-!
# Derivative bounds for inverse families of continuous linear maps

Let `H` be a smooth family of invertible complex-linear maps on an open subset of a
finite-dimensional real normed space. If at a point `x` the derivatives of `H` of order at most `k`
are of size `s` and the inverse `(H x)⁻¹` is of size `1 / s`, then the derivatives of `y ↦ (H y)⁻¹`
of order at most `k` at `x` are of size `1 / s`, with a constant independent of `H`, `x` and `s`
(`TauCeti.exists_norm_iteratedFDeriv_clm_inverse_le`). The proof is an induction on `k` from
`∂ᵤ(H⁻¹) = -H⁻¹ (∂ᵤ H) H⁻¹` and the uniform Leibniz bound
`TauCeti.exists_norm_iteratedFDeriv_bilinear_le`.
-/

public section

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace TauCeti

/-- Bounds on the derivatives of an inverse family at one point, from bounds on the derivatives
of the family at that point and on its inverse there. The bounds are homogeneous in the scale `s`:
the derivatives of the family are of size `s` and its inverse of size `1 / s`. -/
theorem exists_norm_iteratedFDeriv_clm_inverse_le {E V W : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    [CompleteSpace V] [NormedAddCommGroup W] [NormedSpace ℂ W] (k : ℕ) (A B : ℝ) :
    ∃ c, ∀ (H : E → V →L[ℂ] W) (U : Set E) (x : E) (s : ℝ), 0 < s → IsOpen U → x ∈ U →
      ContDiffOn ℝ ∞ H U → (∀ y ∈ U, (H y).IsInvertible) →
      (∀ j ≤ k, ‖iteratedFDeriv ℝ j H x‖ ≤ A * s) → ‖(H x).inverse‖ ≤ B / s →
      ∀ j ≤ k, ‖iteratedFDeriv ℝ j (fun y => (H y).inverse) x‖ ≤ c / s := by
  induction k with
  | zero =>
    refine ⟨B, fun H U x s _ _ _ _ _ _ hB j hj => ?_⟩
    obtain rfl := Nat.le_zero.1 hj
    simpa using hB
  | succ k ih =>
    obtain ⟨c, hc⟩ := ih
    obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_iteratedFDeriv_bilinear_le E
      ((ContinuousLinearMap.compL ℂ W V W).bilinearRestrictScalars ℝ) k
    obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_iteratedFDeriv_bilinear_le E
      ((ContinuousLinearMap.compL ℂ W W V).bilinearRestrictScalars ℝ) k
    refine ⟨max c (C₂ * (c * (C₁ * (A * c)))), ?_⟩
    intro H U x s hs hU hx hH hinv hA hB j hj
    have hc' := hc H U x s hs hU hx hH hinv (fun j hj => hA j (hj.trans k.le_succ)) hB
    rcases Nat.lt_or_eq_of_le hj with hj | rfl
    · exact (hc' j (Nat.lt_succ_iff.1 hj)).trans
        (div_le_div_of_nonneg_right (le_max_left _ _) hs.le)
    have hc0 : 0 ≤ c / s := (norm_nonneg _).trans (hc' 0 (Nat.zero_le _))
    have hA0 : 0 ≤ A * s := (norm_nonneg _).trans (hA 0 (Nat.zero_le _))
    -- Replace `H` and `H⁻¹` by globally smooth functions agreeing with them near `x`.
    have hF : ContDiffOn ℝ ∞ (fun y => (H y).inverse) U := hH.clm_inverse hinv
    obtain ⟨H', hH', -, hHH'⟩ :=
      hH.exists_contDiff_eventuallyEq_of_finiteDimensional (hU.mem_nhds hx)
    obtain ⟨F', hF', -, hFF'⟩ :=
      hF.exists_contDiff_eventuallyEq_of_finiteDimensional (hU.mem_nhds hx)
    have hDH' : ContDiff ℝ ∞ (fderiv ℝ H') := hH'.fderiv_right (by simp)
    have hDF' : ContDiff ℝ ∞ (fderiv ℝ F') := hF'.fderiv_right (by simp)
    have hH'x : ∀ i, iteratedFDeriv ℝ i H' x = iteratedFDeriv ℝ i H x :=
      fun i => (hHH'.iteratedFDeriv (𝕜 := ℝ) i).eq_of_nhds
    have hF'x : ∀ i, iteratedFDeriv ℝ i F' x = iteratedFDeriv ℝ i (fun y => (H y).inverse) x :=
      fun i => (hFF'.iteratedFDeriv (𝕜 := ℝ) i).eq_of_nhds
    -- `∂ᵤ(H⁻¹) = -H⁻¹ (∂ᵤ H) H⁻¹` near `x`.
    have heq (u : E) : (fun y => fderiv ℝ F' y u) =ᶠ[𝓝 x]
        fun y => -(F' y).comp ((fderiv ℝ H' y u).comp (F' y)) := by
      filter_upwards [hU.mem_nhds hx, hHH'.eventuallyEq_nhds, hFF'.eventuallyEq_nhds]
        with y hy hHy hFy
      have hdiff : DifferentiableAt ℝ H y :=
        (hH.differentiableOn (by simp) y hy).differentiableAt (hU.mem_nhds hy)
      rw [hFy.fderiv_eq, hHy.fderiv_eq, hdiff.fderiv_clm_inverse (hinv y hy), hFy.eq_of_nhds]
    -- Bounds on the derivatives of `∂ᵤ(H⁻¹)` at `x`, for every direction `u`.
    have hdir (u : E) : ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ F' y u) x‖ ≤
        C₂ * (c * (C₁ * (A * c))) / s * ‖u‖ := by
      have hDHu : ∀ i ≤ k, ‖iteratedFDeriv ℝ i (fun y => fderiv ℝ H' y u) x‖ ≤ ‖u‖ * (A * s) :=
        fun i hi => (norm_iteratedFDeriv_clm_apply_const hDH'.contDiffAt
          (by exact_mod_cast le_top)).trans (by
            rw [norm_iteratedFDeriv_fderiv, hH'x]
            exact mul_le_mul_of_nonneg_left (hA (i + 1) (Nat.succ_le_succ hi)) (norm_nonneg u))
      have hF'k : ∀ i ≤ k, ‖iteratedFDeriv ℝ i F' x‖ ≤ c / s := fun i hi => by
        rw [hF'x]
        exact hc' i hi
      have hk : ((k : ℕ∞ω)) ≤ ∞ := by exact_mod_cast le_top
      have hG := h₁ (fun y => fderiv ℝ H' y u) F' univ x isOpen_univ (mem_univ x)
        ((hDH'.clm_apply contDiff_const).of_le hk).contDiffOn (hF'.of_le hk).contDiffOn _ _ hDHu
        hF'k
      have hG' := h₂ F' (fun y => (fderiv ℝ H' y u).comp (F' y)) univ x isOpen_univ
        (mem_univ x) (hF'.of_le hk).contDiffOn
        (((((ContinuousLinearMap.compL ℂ W V W).bilinearRestrictScalars ℝ).isBoundedBilinearMap
          |>.contDiff (n := ∞)).comp ((hDH'.clm_apply contDiff_const).prodMk hF')).of_le
            hk).contDiffOn _ _ hF'k hG k le_rfl
      have hneg : iteratedFDeriv ℝ k (fun y => -(F' y).comp ((fderiv ℝ H' y u).comp (F' y))) x =
          -iteratedFDeriv ℝ k (fun y => (F' y).comp ((fderiv ℝ H' y u).comp (F' y))) x :=
        iteratedFDeriv_neg_apply
      rw [((heq u).iteratedFDeriv (𝕜 := ℝ) k).eq_of_nhds, hneg, norm_neg]
      refine hG'.trans (le_of_eq ?_)
      field_simp
    -- Assemble the bound on the derivative of order `k + 1` from the directional ones.
    have hK : 0 ≤ C₂ * (c * (C₁ * (A * c))) / s := by
      have hc'0 : 0 ≤ c := by
        have := mul_nonneg hc0 hs.le
        rwa [div_mul_cancel₀ c hs.ne'] at this
      have hA'0 : 0 ≤ A := nonneg_of_mul_nonneg_left hA0 hs
      positivity
    rw [← hF'x]
    refine (ContinuousMultilinearMap.opNorm_le_bound hK fun m => ?_).trans
      (div_le_div_of_nonneg_right (le_max_right _ _) hs.le)
    rw [iteratedFDeriv_succ_apply_right, ← iteratedFDeriv_clm_apply_const_apply hDF'
      (by exact_mod_cast le_top), Fin.prod_univ_castSucc]
    calc ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ F' y (m (Fin.last k))) x (Fin.init m)‖
        ≤ ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ F' y (m (Fin.last k))) x‖ *
            ∏ i, ‖Fin.init m i‖ := ContinuousMultilinearMap.le_opNorm _ _
      _ ≤ C₂ * (c * (C₁ * (A * c))) / s * ‖m (Fin.last k)‖ * ∏ i, ‖Fin.init m i‖ := by
          gcongr
          exact hdir _
      _ = _ := by
          simp only [Fin.init]
          ring

end TauCeti
