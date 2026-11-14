/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import TauCeti.LinearAlgebra.Matrix.Rank.Pencil
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The Lefschetz–Whitehead rank estimate

Let `g, h : E → F` be maps into a finite-dimensional space and consider the swept map
`(y, t) ↦ g y + t • h y`, which moves the point `g y` along the line through it in the direction
`h y`. Its derivative at `(x, t)` sends `(e, s)` to `g' e + t • h' e + s • h x`, so its range is
`range (g' + t • h') ⊔ 𝕜 ∙ h x`: a pencil in `t`, together with the fixed line spanned by
`h x`. If the swept map has rank at most `p` at `(x, t)` for infinitely many `t`, for instance
for all `t` near `0`, then the rank bound passes to the direction of the pencil
(`LinearMap.finrank_range_sup_le_of_infinite`). When `h x` is transverse to the range of `h'`,
the line `𝕜 ∙ h x` contributes one more dimension, so `h` has rank at most `p - 1` at `x`.

This is Lemma 2 of Łojasiewicz's triangulation of semianalytic sets, where `h` takes values in an
`(m - 1)`-dimensional submanifold `S` of an `m`-dimensional space with `u ∉ T_u S` for `u ∈ S`.
The range of `h'` lies in the tangent space of `S` at `h x`, so the transversality hypothesis
`h x ∉ range h'` used here is implied by the one in the source. In Łojasiewicz's Lemma 3,
directions are represented by unit vectors and `S` is the unit sphere; then transversality holds
because the derivative of a map of constant nonzero norm is orthogonal to its value.

## Main results

* `HasFDerivAt.finrank_range_lt_of_infinite`: the Lefschetz–Whitehead rank estimate for a
  direction field `h` with `h x ∉ range h'`.
* `HasFDerivAt.finrank_range_lt_of_infinite_of_isLocalExtr_norm`: the same for a nonzero
  direction field whose norm has a local extremum at `x`, such as a map into the unit sphere.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Ann. Scuola Norm. Sup. Pisa (3) 18
  (1964), 449–474, §2, Lemma 2.
-/

public section

open Asymptotics Module

namespace HasFDerivAt

section NontriviallyNormedField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {g h : E → F} {g' h' : E →L[𝕜] F} {x : E}

/-- The derivative of the swept map `(y, t) ↦ g y + t • h y` at `(x, t)` sends `(e, s)` to
`g' e + t • h' e + s • h x`. -/
private theorem sweep (hg : HasFDerivAt g g' x) (hh : HasFDerivAt h h' x) (t : 𝕜) :
    HasFDerivAt (fun q : E × 𝕜 ↦ g q.1 + q.2 • h q.1)
      ((g' + t • h').coprod (ContinuousLinearMap.toSpanSingleton 𝕜 (h x))) (x, t) := by
  have hg₁ := hg.comp (x, t) (hasFDerivAt_fst (𝕜 := 𝕜) (p := (x, t)))
  have hh₁ := hh.comp (x, t) (hasFDerivAt_fst (𝕜 := 𝕜) (p := (x, t)))
  refine (hg₁.add ((hasFDerivAt_snd (𝕜 := 𝕜) (p := (x, t))).smul hh₁)).congr_fderiv ?_
  ext <;> simp

variable [FiniteDimensional 𝕜 F]

/-- **The Lefschetz–Whitehead rank estimate.** Let `g` and `h` be differentiable at `x`, with
`h x` outside the range of the derivative `h'` of `h`. If the swept map
`(y, t) ↦ g y + t • h y` has rank at most `p` at `(x, t)` for infinitely many `t`, for instance
for every `t` near `0`, then `h` has rank less than `p` at `x`. -/
theorem finrank_range_lt_of_infinite (hh : HasFDerivAt h h' x) (hg : HasFDerivAt g g' x)
    (hx : h x ∉ LinearMap.range (h' : E →ₗ[𝕜] F)) {p : ℕ}
    (hp : {t : 𝕜 | finrank 𝕜 (LinearMap.range
      (fderiv 𝕜 (fun q : E × 𝕜 ↦ g q.1 + q.2 • h q.1) (x, t) : E × 𝕜 →ₗ[𝕜] F)) ≤ p}.Infinite) :
    finrank 𝕜 (LinearMap.range (h' : E →ₗ[𝕜] F)) < p := by
  refine LinearMap.finrank_range_lt_of_infinite (f := (g' : E →ₗ[𝕜] F)) hx (hp.mono fun t ht ↦ ?_)
  -- The range of the derivative of the swept map is `range (g' + t • h') ⊔ 𝕜 ∙ h x`.
  rw [Set.mem_ofPred_eq, (sweep hg hh t).fderiv, ContinuousLinearMap.coe_coprod,
    LinearMap.range_coprod, ContinuousLinearMap.toLinearMap_toSpanSingleton,
    LinearMap.range_toSpanSingleton] at ht
  simpa using ht

end NontriviallyNormedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {g h : E → F} {g' h' : E →L[ℝ] F} {x : E}

/-- **The Lefschetz–Whitehead rank estimate for unit directions.** Let `g` and `h` be
differentiable at `x`, where `h x ≠ 0` and `‖h‖` has a local extremum at `x`, for instance when
`h` is a map into the unit sphere. If the swept map `(y, t) ↦ g y + t • h y` has rank at most
`p` at `(x, t)` for infinitely many `t`, then `h` has rank less than `p` at `x`. The norm on `F`
need not come from an inner product. -/
theorem finrank_range_lt_of_infinite_of_isLocalExtr_norm (hh : HasFDerivAt h h' x)
    (hg : HasFDerivAt g g' x) (hn : IsLocalExtr (fun y ↦ ‖h y‖) x) (h0 : h x ≠ 0) {p : ℕ}
    (hp : {t : ℝ | finrank ℝ (LinearMap.range
      (fderiv ℝ (fun q : E × ℝ ↦ g q.1 + q.2 • h q.1) (x, t) : E × ℝ →ₗ[ℝ] F)) ≤ p}.Infinite) :
    finrank ℝ (LinearMap.range (h' : E →ₗ[ℝ] F)) < p := by
  refine hh.finrank_range_lt_of_infinite hg ?_ hp
  rintro ⟨e, he⟩
  rw [ContinuousLinearMap.coe_coe] at he
  -- If `h' e = h x`, then along the line `t ↦ x + t • e` the map `h` moves as
  -- `(1 + t) • h x + o(t)`.
  have hψ : HasDerivAt (fun t : ℝ ↦ h (x + t • e)) (h x) 0 := by
    have hl : HasDerivAt (fun t : ℝ ↦ x + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
    simpa [he, Function.comp_def] using hh.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  -- So `‖h (x + t • e)‖ = (1 + t) * ‖h x‖ + o(t)`: the norm of `h` has derivative `‖h x‖ ≠ 0`
  -- along the line, which is impossible at a local extremum.
  have hφ : HasDerivAt (fun t : ℝ ↦ ‖h (x + t • e)‖) ‖h x‖ 0 := by
    rw [hasDerivAt_iff_isLittleO] at hψ ⊢
    refine (IsBigO.of_bound' ?_).trans_isLittleO hψ
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with t (ht : -1 < t)
    calc ‖‖h (x + t • e)‖ - ‖h (x + (0 : ℝ) • e)‖ - (t - 0) • ‖h x‖‖
        = |‖h (x + t • e)‖ - ‖(1 + t) • h x‖| := by
          rw [Real.norm_eq_abs, norm_smul, Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + t)]
          simp only [zero_smul, add_zero, sub_zero, smul_eq_mul]
          congr 1
          ring
      _ ≤ ‖h (x + t • e) - (1 + t) • h x‖ := abs_norm_sub_norm_le _ _
      _ = ‖h (x + t • e) - h (x + (0 : ℝ) • e) - (t - 0) • h x‖ := by
          rw [zero_smul, add_zero, sub_zero, add_smul, one_smul, sub_add_eq_sub_sub]
  have hext : IsLocalExtr (fun t : ℝ ↦ ‖h (x + t • e)‖) 0 :=
    IsLocalExtr.comp_continuous (f := fun y ↦ ‖h y‖) (g := fun t : ℝ ↦ x + t • e) (b := 0)
      (by simpa using hn) (by fun_prop)
  exact h0 (norm_eq_zero.mp (hext.hasDerivAt_eq_zero hφ))

end HasFDerivAt
