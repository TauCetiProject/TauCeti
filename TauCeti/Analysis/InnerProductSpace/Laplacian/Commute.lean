/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.IteratedFDeriv.DirectionList
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

/-!
# The Laplacian commutes with derivatives

On a finite-dimensional real inner product space the Laplacian is a constant-coefficient operator,
so it commutes with differentiation of smooth functions. In an orthonormal basis `b`, the
Laplacian is the sum of the iterated directional derivatives along `[bᵢ, bᵢ]`. Differentiating
along a list of directions `vs` and then taking the Laplacian differentiates along `[bᵢ, bᵢ] ++ vs`,
while the other order differentiates along `vs ++ [bᵢ, bᵢ]`; these agree because iterated
directional derivatives of a smooth function do not depend on the order of the directions
(`List.Perm.iteratedFDerivAlong_eq`). Hence

`Δ (∂_vs f) = ∂_vs (Δ f)`

(`ContDiff.laplacian_iteratedFDerivAlong`), and in terms of the iterated Fréchet derivative,
`Δ (y ↦ Dᵏf(y) m) = y ↦ Dᵏ(Δf)(y) m` (`ContDiff.laplacian_iteratedFDeriv_apply`).

These identities let a semilinear elliptic equation `Δ u = G(u)` be differentiated: every
derivative of `u` solves the equation whose right side is the corresponding derivative of `G(u)`.

## Main results

* `OrthonormalBasis.laplacian_eq_sum_iteratedFDerivAlong`: `Δ g = ∑ᵢ ∂_[bᵢ, bᵢ] g` for an
  orthonormal basis `b`.
* `ContDiff.laplacian_iteratedFDerivAlong`: `Δ (iteratedFDerivAlong ℝ vs f) =
  iteratedFDerivAlong ℝ vs (Δ f)` for `f` of class `C^(k + 2)`, `k` the length of `vs`.
* `ContDiff.laplacian_iteratedFDeriv_apply`: for `f` of class `C^(k + 2)`,
  `Δ (fun y ↦ iteratedFDeriv ℝ k f y m) = fun y ↦ iteratedFDeriv ℝ k (Δ f) y m`.
-/

public section

namespace TauCeti

open InnerProductSpace Laplacian
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The Laplacian of a `C²` function is the sum of its second directional derivatives
`∂_[bᵢ, bᵢ]` along an orthonormal basis `b`. -/
theorem _root_.OrthonormalBasis.laplacian_eq_sum_iteratedFDerivAlong {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) {g : E → F} (hg : ContDiff ℝ 2 g) :
    Δ g = fun y ↦ ∑ i, iteratedFDerivAlong ℝ [b i, b i] g y := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis g b]
  funext y
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← iteratedFDerivAlong_ofFn_eq_iteratedFDeriv hg]
  simp

/-- **The Laplacian commutes with iterated directional derivatives.** For a function `f` of class
`C^(k + 2)` and a list `vs` of `k` directions, `Δ (∂_vs f) = ∂_vs (Δ f)`. -/
theorem _root_.ContDiff.laplacian_iteratedFDerivAlong {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    (vs : List E) (hvs : (vs.length : ℕ∞ω) + 2 ≤ n) :
    Δ (iteratedFDerivAlong ℝ vs f) = iteratedFDerivAlong ℝ vs (Δ f) := by
  set b := stdOrthonormalBasis ℝ E
  have h2 : (2 : ℕ∞ω) ≤ n := le_trans (by simp) hvs
  rw [b.laplacian_eq_sum_iteratedFDerivAlong (hf.iteratedFDerivAlong vs (by rwa [add_comm])),
    b.laplacian_eq_sum_iteratedFDerivAlong (hf.of_le h2),
    iteratedFDerivAlong_sum (fun i _ ↦ hf.iteratedFDerivAlong (m := vs.length) [b i, b i]
      (by simpa using hvs)) vs le_rfl]
  funext y
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [← iteratedFDerivAlong_append, ← iteratedFDerivAlong_append,
    List.perm_append_comm.iteratedFDerivAlong_eq hf (le_of_eq_of_le (by simp; ring) hvs)]

/-- **The Laplacian commutes with iterated derivatives.** For a function `f` of class
`C^(k + 2)`, the Laplacian of its `k`-th iterated derivative, evaluated on fixed vectors `m`, is
the `k`-th iterated derivative of `Δ f` evaluated on `m`. -/
theorem _root_.ContDiff.laplacian_iteratedFDeriv_apply {n : ℕ∞ω} {f : E → F} (hf : ContDiff ℝ n f)
    {k : ℕ} (hk : (k : ℕ∞ω) + 2 ≤ n) (m : Fin k → E) :
    Δ (fun y ↦ iteratedFDeriv ℝ k f y m) = fun y ↦ iteratedFDeriv ℝ k (Δ f) y m := by
  have hΔf : ContDiff ℝ k (Δ f) := hf.laplacian hk
  have h₁ : (fun y ↦ iteratedFDeriv ℝ k f y m) = iteratedFDerivAlong ℝ (List.ofFn m) f :=
    funext fun y ↦ (iteratedFDerivAlong_ofFn_eq_iteratedFDeriv
      (hf.of_le (le_trans (by simp) hk)) m y).symm
  have h₂ : (fun y ↦ iteratedFDeriv ℝ k (Δ f) y m) = iteratedFDerivAlong ℝ (List.ofFn m) (Δ f) :=
    funext fun y ↦ (iteratedFDerivAlong_ofFn_eq_iteratedFDeriv hΔf m y).symm
  rw [h₁, h₂, hf.laplacian_iteratedFDerivAlong _ (by simpa using hk)]

end TauCeti
