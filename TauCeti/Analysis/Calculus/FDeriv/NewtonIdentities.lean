/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# The derivative of the Newton coefficients of a family of moments

Let `M₁, M₂, … : E → 𝔸` be differentiable functions, for instance the moments `M_k(z) = ∫ Wᵏ dμ_z`
of a smooth family of measures, and let `b₀ = 1, b₁, b₂, …` be their Newton coefficients, defined
pointwise by Newton's recursion

`j b_j = ∑_{k=1}^{j} (-1)^(k-1) b_{j-k} M_k`.

When the `M_k` are the power sums of a multiset of points, the `b_j` are its elementary symmetric
functions, the coefficients of the monic polynomial with those points as roots. This file shows
that the `b_j` are differentiable and computes their derivative:

`D b_j = ∑_{k=1}^{j} (-1)^(k-1) (b_{j-k} / k) D M_k`.

The algebra is `TauCeti.newton_variation_eq_sum`, applied to the derivatives at a point, which
live in the torsion-free `𝔸`-module `E →L[𝕜] 𝔸`. Only a neighbourhood of the point matters, so
the recursion is assumed near it.

## Main results

* `TauCeti.differentiableAt_of_newton`: the Newton coefficients of differentiable functions are
  differentiable.
* `TauCeti.hasFDerivAt_of_newton`: their derivative.

## References

* C. H. Taubes, *SW ⇒ Gr: from the Seiberg–Witten equations to pseudo-holomorphic curves*,
  J. Amer. Math. Soc. 9 (1996), 845–918.
-/

public section

open Finset Filter Topology

namespace TauCeti

variable {𝕜 𝔸 E : Type*} [NontriviallyNormedField 𝕜] [NormedField 𝔸] [CharZero 𝔸]
  [NormedAlgebra 𝕜 𝔸] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {b M : ℕ → E → 𝔸} {x : E}
  {j : ℕ}

/-- The Newton coefficients `b_j` of functions `M_k` differentiable at `x`, defined near `x` by
`b₀ = 1` and `i b_i = ∑_{k=1}^{i} (-1)^(k-1) b_{i-k} M_k`, are differentiable at `x`. -/
theorem differentiableAt_of_newton (hb₀ : b 0 =ᶠ[𝓝 x] 1)
    (hb : ∀ i ≤ j, ∀ᶠ y in 𝓝 x,
      (i : 𝔸) * b i y = ∑ k ∈ Icc 1 i, (-1) ^ (k - 1) * b (i - k) y * M k y)
    (hM : ∀ k ∈ Icc 1 j, DifferentiableAt 𝕜 (M k) x) :
    DifferentiableAt 𝕜 (b j) x := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact (differentiableAt_const 1).congr_of_eventuallyEq hb₀
  have hj' : (j : 𝔸) ≠ 0 := Nat.cast_ne_zero.2 hj.ne'
  -- Near `x`, `b_j` is `j⁻¹` times a polynomial in the lower `b_i` and the `M_k`.
  have hd : DifferentiableAt 𝕜
      (fun y ↦ (j : 𝔸)⁻¹ * ∑ k ∈ Icc 1 j, (-1) ^ (k - 1) * b (j - k) y * M k y) x := by
    refine (DifferentiableAt.fun_sum fun k hk ↦ ?_).const_mul _
    rw [mem_Icc] at hk
    exact ((differentiableAt_const _).mul (ih (j - k) (by omega)
      (fun i hi ↦ hb i (by omega)) (fun i hi ↦ hM i (by simp only [mem_Icc] at hi ⊢; omega)))).mul
      (hM k (mem_Icc.2 hk))
  refine hd.congr_of_eventuallyEq ((hb j le_rfl).mono fun y hy ↦ ?_)
  dsimp only
  rw [← hy, inv_mul_cancel_left₀ hj']

/-- **The derivative of the Newton coefficients.** If `M_k` is differentiable at `x` for
`1 ≤ k ≤ j`, and near `x` the functions `b_i` satisfy `b₀ = 1` and Newton's recursion
`i b_i = ∑_{k=1}^{i} (-1)^(k-1) b_{i-k} M_k` for `i ≤ j`, then

`D b_j(x) = ∑_{k=1}^{j} (-1)^(k-1) (b_{j-k}(x) / k) D M_k(x)`. -/
theorem hasFDerivAt_of_newton (hb₀ : b 0 =ᶠ[𝓝 x] 1)
    (hb : ∀ i ≤ j, ∀ᶠ y in 𝓝 x,
      (i : 𝔸) * b i y = ∑ k ∈ Icc 1 i, (-1) ^ (k - 1) * b (i - k) y * M k y)
    (hM : ∀ k ∈ Icc 1 j, DifferentiableAt 𝕜 (M k) x) :
    HasFDerivAt (b j)
      (∑ k ∈ Icc 1 j, ((-1) ^ (k - 1) * b (j - k) x / k) • fderiv 𝕜 (M k) x) x := by
  have hd : ∀ i ≤ j, DifferentiableAt 𝕜 (b i) x := fun i hi ↦
    differentiableAt_of_newton hb₀ (fun i' hi' ↦ hb i' (by omega))
      (fun k hk ↦ hM k (by simp only [mem_Icc] at hk ⊢; omega))
  -- Differentiating Newton's recursion at `x` gives the recursion for the derivatives of the
  -- `b_i` that `TauCeti.newton_variation_eq_sum` solves.
  have hc : ∀ i ≤ j, (i : 𝔸) • fderiv 𝕜 (b i) x = ∑ k ∈ Icc 1 i, (-1 : 𝔸) ^ (k - 1) •
      (M k x • fderiv 𝕜 (b (i - k)) x +
        (k : 𝔸) • b (i - k) x • ((k : 𝔸)⁻¹ • fderiv 𝕜 (M k) x)) := fun i hi ↦ by
    have hsum := HasFDerivAt.fun_sum (u := Icc 1 i) fun k hk ↦
      (((hd (i - k) (by omega)).hasFDerivAt.const_mul ((-1 : 𝔸) ^ (k - 1))).mul
        (hM k (by simp only [mem_Icc] at hk ⊢; omega)).hasFDerivAt)
    refine ((hd i hi).hasFDerivAt.const_mul (i : 𝔸)).unique
      (hsum.congr_of_eventuallyEq (hb i hi)) |>.trans (sum_congr rfl fun k hk ↦ ?_)
    have hk : (k : 𝔸) ≠ 0 := Nat.cast_ne_zero.2 (by simp only [mem_Icc] at hk; omega)
    rw [smul_comm (k : 𝔸) (b (i - k) x), smul_smul (k : 𝔸), mul_inv_cancel₀ hk, one_smul]
    module
  have h₀ : fderiv 𝕜 (b 0) x = 0 := by
    rw [hb₀.fderiv_eq, fderiv_one, Pi.zero_apply]
  have := HasUniqueDiv.of_isTorsionFree 𝔸 (E →L[𝕜] 𝔸)
  convert (hd j le_rfl).hasFDerivAt using 1
  rw [newton_variation_eq_sum (c := fun i ↦ fderiv 𝕜 (b i) x)
    (e := fun k ↦ (k : 𝔸)⁻¹ • fderiv 𝕜 (M k) x) (fun i hi ↦ (hb i hi.le).self_of_nhds) h₀ hc]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [smul_smul, div_eq_mul_inv]

end TauCeti
