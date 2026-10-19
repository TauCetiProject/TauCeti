/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Parseval's identity in norm-square form

Mathlib states Parseval's identity in polarized, `𝕜`-valued form:
`HilbertBasis.hasSum_inner_mul_inner` gives `∑' i, ⟪x, b i⟫ * ⟪b i, y⟫ = ⟪x, y⟫`. This file states
the diagonal, real-valued form `‖x‖² = ∑' i, ‖⟪b i, x⟫‖²`. The two differ in the type of their
summands, so the real-valued form is not a substitution instance of the polarized one.

The real-valued form is the shape consumers state coefficient decay in, and it is the
`OrthogonalL2Bases` roadmap's Part A3 acceptance criterion `‖f‖² = ∑' n, ‖⟪ψₙ, f⟫‖²`; its instance
for the Hermite basis is `TauCeti.tsum_norm_sq_inner_hermiteFunctionLp`.

## Main declarations

* `HilbertBasis.hasSum_norm_sq_inner` — Parseval in norm-square form, as a `HasSum` statement.
* `HilbertBasis.tsum_norm_sq_inner` — the same identity as an equation between a `tsum` and `‖x‖²`.
* `HilbertBasis.tsum_enorm_sq_inner` — the same identity in `ℝ≥0∞`, where it needs no summability
  bookkeeping and can be reordered freely against other unconditional sums.
* `OrthonormalBasis.sum_sq_norm_apply_eq_norm_sq` — the squared values of a continuous linear
  functional on a finite orthonormal basis sum to the square of its operator norm.
-/

public section

namespace TauCeti

variable {ι : Type*} {𝕜 : Type*} {E : Type*}
variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Parseval's identity, norm-square form.** The squared coordinates of `x` in a Hilbert basis
sum to `‖x‖²`, as a convergent series of real numbers. -/
theorem _root_.HilbertBasis.hasSum_norm_sq_inner (b : _root_.HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i => ‖inner 𝕜 (b i) x‖ ^ 2) (‖x‖ ^ 2) := by
  have h := lp.hasSum_norm (p := 2) (by norm_num) (b.repr x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, b.repr_apply_apply, b.repr.norm_map] using h

/-- **Parseval's identity, norm-square form** (`tsum` version of
`HilbertBasis.hasSum_norm_sq_inner`). -/
theorem _root_.HilbertBasis.tsum_norm_sq_inner (b : _root_.HilbertBasis ι 𝕜 E) (x : E) :
    ∑' i : ι, ‖inner 𝕜 (b i) x‖ ^ 2 = ‖x‖ ^ 2 :=
  (b.hasSum_norm_sq_inner x).tsum_eq

/-- The squared coordinate family of a vector is summable. -/
theorem _root_.HilbertBasis.summable_norm_sq_inner (b : _root_.HilbertBasis ι 𝕜 E) (x : E) :
    Summable fun i => ‖inner 𝕜 (b i) x‖ ^ 2 :=
  (b.hasSum_norm_sq_inner x).summable

/-- **Parseval's identity, extended-nonnegative form.** The squared extended norms of the
coordinates of `x` in a Hilbert basis sum to `‖x‖ₑ²`. -/
theorem _root_.HilbertBasis.tsum_enorm_sq_inner (b : _root_.HilbertBasis ι 𝕜 E) (x : E) :
    ∑' i : ι, ‖inner 𝕜 (b i) x‖ₑ ^ 2 = ‖x‖ₑ ^ 2 := by
  simp_rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) (b.summable_norm_sq_inner x),
    b.tsum_norm_sq_inner]

/-- **Parseval's identity for a functional.** The squared values of a continuous linear functional
on a finite orthonormal basis sum to the square of its operator norm: by the Riesz representation,
they are the squared coordinates of the representing vector. -/
theorem _root_.OrthonormalBasis.sum_sq_norm_apply_eq_norm_sq [Fintype ι]
    (b : OrthonormalBasis ι 𝕜 E) (A : E →L[𝕜] 𝕜) :
    ∑ i, ‖A (b i)‖ ^ 2 = ‖A‖ ^ 2 := by
  have : FiniteDimensional 𝕜 E := Module.Finite.of_basis b.toBasis
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  rw [← (InnerProductSpace.toDual 𝕜 E).symm.norm_map A, ← b.sum_sq_norm_inner_left]
  simp_rw [InnerProductSpace.toDual_symm_apply]

end TauCeti
