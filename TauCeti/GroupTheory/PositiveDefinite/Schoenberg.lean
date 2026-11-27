/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
import TauCeti.Analysis.PositiveDefinite.Kernel.Schoenberg

/-!
# Schoenberg's theorem for positive-definite functions on groups

This file applies Schoenberg's theorem (`Matrix.CondNegSemidef.posSemidef_cexp_neg_mul`) to
positive-definite functions on discrete groups. Given a family of positive-definite functions
`φ k : G → ℂ` and nonnegative weights `w k`, each `(a, b) ↦ w k * (1 - φ k (a⁻¹ * b))` is
conditionally negative semidefinite, so whenever the weighted series converges pointwise, the
exponentiated function `g ↦ exp (-t * ∑' k, w k * (1 - φ k g))` is positive definite for every
`t ≥ 0`.

## Main declarations

* `TauCeti.posSemidef_cexp_neg_tsum_mul`: positive semidefiniteness of
  `g ↦ exp (-t * ∑' k, w k * (1 - φ k g))` for nonnegative weights `w` and positive-definite
  functions `φ k`.

## References

* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Proposition 14.1.2.
* P. Jolissaint, *On property (T) for pairs of topological groups*, Enseign. Math. (2) 51 (2005),
  31–45.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Appendix C.
-/

public section

open scoped ComplexOrder

namespace TauCeti

/-- **Weighted Schoenberg series.** For nonnegative weights `w`, positive-definite functions `φ k`
on a group `G`, and `t ≥ 0`, the function `g ↦ exp (-t * ∑' k, w k * (1 - φ k g))` is positive
definite whenever the series converges pointwise. -/
theorem posSemidef_cexp_neg_tsum_mul {ι G : Type*} [Group G] {φ : ι → G → ℂ}
    (hpd : ∀ k, (Matrix.of fun a b : G ↦ φ k (a⁻¹ * b)).PosSemidef)
    {w : ι → ℝ} (hw : ∀ k, 0 ≤ w k)
    {L : SummationFilter ι} [L.NeBot]
    (hsumm : ∀ g, Summable (fun k ↦ (w k : ℂ) * (1 - φ k g)) L)
    {t : ℝ} (ht : 0 ≤ t) :
    (Matrix.of fun a b : G ↦
      Complex.exp (-(t : ℂ) * ∑'[L] k, (w k : ℂ) * (1 - φ k (a⁻¹ * b)))).PosSemidef := by
  let Ψ : Matrix G G ℂ :=
    Matrix.of fun a b : G ↦ ∑'[L] k, (w k : ℂ) * (1 - φ k (a⁻¹ * b))
  have hΨ : Ψ.CondNegSemidef := by
    refine Matrix.CondNegSemidef.tsum_of_summable
      (f := fun (k : ι) (a b : G) ↦ (w k : ℂ) * (1 - φ k (a⁻¹ * b)))
      (fun a b ↦ hsumm (a⁻¹ * b)) fun k ↦ ?_
    convert ((hpd k).const_sub_condNegSemidef (star_one ℂ)).smul
      (a := (w k : ℂ)) (by exact_mod_cast hw k) using 1
    ext a b
    simp
  simpa [Ψ] using hΨ.posSemidef_cexp_neg_mul ht

end TauCeti
