/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.FDeriv.Norm
public import TauCeti.LinearAlgebra.Matrix.Rank.Pencil

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
* `HasFDerivAt.finrank_range_lt_of_infinite_of_norm_eq`: the same for a direction field of
  locally constant nonzero norm, such as a map into the unit sphere.

## References

* S. Łojasiewicz, *Triangulation of semi-analytic sets*, Ann. Scuola Norm. Sup. Pisa (3) 18
  (1964), 449–474, §2, Lemma 2.
-/

public section

open Module
open scoped Topology RealInnerProductSpace

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
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {g h : E → F} {g' h' : E →L[ℝ] F} {x : E}

/-- **The Lefschetz–Whitehead rank estimate for unit directions.** Let `g` and `h` be
differentiable at `x`, where `h x ≠ 0` and `‖h‖` is constant near `x`, for instance a map into the
unit sphere. If the swept map `(y, t) ↦ g y + t • h y` has rank at most `p` at `(x, t)` for
infinitely many `t`, then `h` has rank less than `p` at `x`. -/
theorem finrank_range_lt_of_infinite_of_norm_eq (hh : HasFDerivAt h h' x)
    (hg : HasFDerivAt g g' x) (hn : ∀ᶠ y in 𝓝 x, ‖h y‖ = ‖h x‖) (h0 : h x ≠ 0) {p : ℕ}
    (hp : {t : ℝ | finrank ℝ (LinearMap.range
      (fderiv ℝ (fun q : E × ℝ ↦ g q.1 + q.2 • h q.1) (x, t) : E × ℝ →ₗ[ℝ] F)) ≤ p}.Infinite) :
    finrank ℝ (LinearMap.range (h' : E →ₗ[ℝ] F)) < p := by
  refine hh.finrank_range_lt_of_infinite hg ?_ hp
  -- The derivative of a map of constant norm is orthogonal to its value.
  rintro ⟨e, he⟩
  have := TauCeti.inner_fderiv_eq_zero_of_eventually_norm_eq hn e
  rw [ContinuousLinearMap.coe_coe] at he
  rw [hh.fderiv, he, inner_self_eq_zero] at this
  exact h0 this

end HasFDerivAt
