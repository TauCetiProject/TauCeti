/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Lipschitz-small perturbations of the identity are diffeomorphisms

If `u : E → E` is `C^n`, `1 ≤ n`, and `K`-Lipschitz with `K < 1`, on a Banach space `E` over a
nontrivially normed field, then `x ↦ x + u x` is a `C^n` diffeomorphism of `E`
(`ContDiff.exists_diffeomorph_apply_eq_add_of_lipschitzWith`). It is a homeomorphism because it
approximates the identity (`ApproximatesLinearOn.toHomeomorph`), and its derivative `1 + Du` is
invertible everywhere, so its inverse is `C^n` (`Homeomorph.contDiff_symm`).

Cutting off a translation in this way gives the standard local motions of a finite-dimensional
real normed space `E`: for a ball `B(c, r)`, the maps `p ↦ p + ρ(p) • d`, with `ρ` a bump function
supported in `B(c, r)` and equal to `1` near `c`, are `C^n` diffeomorphisms of `E` for `d` small,
fix every point outside `B(c, r)` and carry `c` to `c + d`. After a further cut-off in `d`, they
form a family of diffeomorphisms indexed by all of `E`, depending jointly smoothly on `d` and the
point (`TauCeti.exists_diffeomorph_family_apply_eq_add`). Read in a chart, these are the local
motions that move a point of a manifold continuously to every nearby point.

## Main results

* `ContDiff.exists_diffeomorph_apply_eq_add_of_lipschitzWith`: a `C^n` map `u` which is
  `K`-Lipschitz with `K < 1` makes `x ↦ x + u x` a `C^n` diffeomorphism.
* `TauCeti.exists_diffeomorph_family_apply_eq_add`: a jointly smooth family of diffeomorphisms of
  `E` supported in a ball `B(c, r)` and carrying `c` to `c + d` for every small `d`.
-/

public section

noncomputable section

open Set Metric
open scoped Manifold ContDiff NNReal

namespace ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [CompleteSpace E]

/-- **A Lipschitz-small perturbation of the identity is a diffeomorphism.** If `u : E → E` is
`C^n`, `1 ≤ n`, and `K`-Lipschitz with `K < 1`, on a Banach space `E`, then `x ↦ x + u x` is a
`C^n` diffeomorphism of `E`. -/
theorem exists_diffeomorph_apply_eq_add_of_lipschitzWith {n : WithTop ℕ∞} {u : E → E}
    (hu : ContDiff 𝕜 n u) (hn : 1 ≤ n) {K : ℝ≥0} (hlip : LipschitzWith K u) (hK : K < 1) :
    ∃ φ : E ≃ₘ^n⟮𝓘(𝕜, E), 𝓘(𝕜, E)⟯ E, ∀ x, φ x = x + u x := by
  have hf : ApproximatesLinearOn (fun x ↦ x + u x)
      ((ContinuousLinearEquiv.refl 𝕜 E : E ≃L[𝕜] E) : E →L[𝕜] E) univ K := by
    rw [ApproximatesLinearOn.approximatesLinearOn_iff_lipschitzOnWith]
    convert hlip.lipschitzOnWith (s := univ) using 1
    ext x
    simp
  have hc : Subsingleton E ∨
      K < ‖(((ContinuousLinearEquiv.refl 𝕜 E).symm : E ≃L[𝕜] E) : E →L[𝕜] E)‖₊⁻¹ := by
    rcases subsingleton_or_nontrivial E with hE | hE
    · exact Or.inl hE
    · right
      simpa using hK
  -- The derivative `1 + Du a = 1 - (-Du a)` is a unit, since `‖Du a‖ ≤ K < 1`.
  have hnorm (a : E) : ‖-fderiv 𝕜 u a‖ < 1 := by
    rw [norm_neg]
    exact (norm_fderiv_le_of_lipschitz 𝕜 hlip).trans_lt (by exact_mod_cast hK)
  have hf' (a : E) : HasFDerivAt (fun x ↦ x + u x)
      ((ContinuousLinearEquiv.unitsEquiv 𝕜 E (Units.oneSub _ (hnorm a)) : E ≃L[𝕜] E) :
        E →L[𝕜] E) a := by
    refine ((hasFDerivAt_id a).add
      (hu.differentiable (zero_lt_one.trans_le hn).ne' a).hasFDerivAt).congr_fderiv ?_
    ext v
    simp [sub_eq_add_neg]
  have hfd : ContDiff 𝕜 n (fun x ↦ x + u x) := contDiff_id.add hu
  let H := hf.toHomeomorph _ hc
  exact ⟨{ toEquiv := H.toEquiv
           contMDiff_toFun := contMDiff_iff_contDiff.2 hfd
           contMDiff_invFun := contMDiff_iff_contDiff.2 (H.contDiff_symm hf' hfd) },
    fun _ ↦ rfl⟩

end ContDiff

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Compactly supported translations.** Let `c` be a point of a finite-dimensional real normed
space `E` and `r > 0`. There are `δ > 0` and a family `τ d`, `d ∈ E`, of `C^n` diffeomorphisms of
`E`, `1 ≤ n`, such that `(d, p) ↦ τ d p` is `C^n`, every `τ d` fixes each point outside the ball
`B(c, r)`, `τ 0` is the identity, and `τ d c = c + d` whenever `‖d‖ < δ`.

The diffeomorphism `τ d` is `p ↦ p + ρ(p) • κ(d)`, where `ρ` is a bump function supported in
`B(c, r)` and equal to `1` at `c`, and `κ(d) = χ(d) • d` for a bump function `χ` at `0` so narrow
that `ρ(p) • κ(d)` is a Lipschitz-small perturbation of the identity. -/
theorem exists_diffeomorph_family_apply_eq_add (c : E) {r : ℝ} (hr : 0 < r) {n : ℕ∞}
    (hn : 1 ≤ n) :
    ∃ δ > 0, ∃ τ : E → E ≃ₘ^n⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯ E,
      ContDiff ℝ n (fun q : E × E ↦ τ q.1 q.2) ∧ (∀ d, ∀ p ∉ ball c r, τ d p = p) ∧
        τ 0 = Diffeomorph.refl 𝓘(ℝ, E) E n ∧ ∀ d, ‖d‖ < δ → τ d c = c + d := by
  -- The bump `ρ` in the point, supported in `B(c, r)`, and its Lipschitz constant `L`.
  let ρ : ContDiffBump c := ⟨r / 2, r, by positivity, by linarith⟩
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport ρ.hasCompactSupport
    (ρ.contDiff (n := 1)) one_ne_zero
  -- The bump `χ` in the parameter, of radius `B` with `L * B < 1`.
  set B : ℝ := 1 / (2 * (L + 1)) with hB
  have hB0 : 0 < B := by positivity
  have hLB : (L : ℝ) * B < 1 := by
    rw [hB, mul_one_div, div_lt_one (by positivity)]
    linarith [L.coe_nonneg]
  let χ : ContDiffBump (0 : E) := ⟨B / 2, B, by positivity, by linarith⟩
  let κ : E → E := fun d ↦ χ d • d
  have hκ (d : E) : ‖κ d‖ < B ∨ κ d = 0 := by
    by_cases hd : ‖d‖ < B
    · left
      calc ‖κ d‖ = χ d * ‖d‖ := by rw [norm_smul, Real.norm_of_nonneg χ.nonneg]
        _ ≤ 1 * ‖d‖ := mul_le_mul_of_nonneg_right χ.le_one (norm_nonneg d)
        _ < B := by rwa [one_mul]
    · right
      simp [κ, χ.zero_of_le_dist (by simpa using hd)]
  -- Each `p ↦ p + ρ p • κ d` is a perturbation of the identity of Lipschitz constant below `1`.
  have hlip (d : E) : LipschitzWith (L * ‖κ d‖₊) fun p ↦ ρ p • κ d := by
    refine LipschitzWith.of_dist_le_mul fun p q ↦ ?_
    rw [dist_eq_norm, ← sub_smul, norm_smul, ← dist_eq_norm, NNReal.coe_mul, coe_nnnorm,
      mul_right_comm]
    exact mul_le_mul_of_nonneg_right (hL.dist_le_mul p q) (norm_nonneg _)
  have hlt (d : E) : L * ‖κ d‖₊ < 1 := by
    rcases hκ d with h | h
    · rw [← NNReal.coe_lt_coe, NNReal.coe_mul, coe_nnnorm, NNReal.coe_one]
      exact (mul_le_mul_of_nonneg_left h.le L.coe_nonneg).trans_lt hLB
    · simp [h]
  have hτ (d : E) := ContDiff.exists_diffeomorph_apply_eq_add_of_lipschitzWith
    (u := fun p ↦ ρ p • κ d) (n := n) (ρ.contDiff.smul contDiff_const) (by exact_mod_cast hn)
    (hlip d) (hlt d)
  choose τ hτ using hτ
  refine ⟨B / 2, by positivity, τ, ?_, fun d p hp ↦ ?_, ?_, fun d hd ↦ ?_⟩
  · simp only [hτ]
    exact contDiff_snd.add ((ρ.contDiff.comp contDiff_snd).smul
      ((χ.contDiff.smul contDiff_id).comp contDiff_fst))
  · rw [hτ, ρ.zero_of_le_dist (by simpa [mem_ball] using hp), zero_smul, add_zero]
  · ext p
    simp [hτ, κ]
  · rw [hτ, ρ.one_of_mem_closedBall (mem_closedBall_self (by positivity)), one_smul]
    simp only [κ, χ.one_of_mem_closedBall (show d ∈ closedBall 0 (B / 2) by
      rw [mem_closedBall_zero_iff]; exact hd.le), one_smul]

end TauCeti
