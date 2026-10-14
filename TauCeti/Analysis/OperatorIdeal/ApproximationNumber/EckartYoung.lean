/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.SingularValues
public import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax

/-!
# The Eckart–Young theorem: approximation numbers are singular values

For a bounded linear map `T : E →L[𝕜] F` between finite-dimensional inner product spaces over `ℝ`
or `ℂ`, the approximation number `aₙ(T)`, the distance from `T` to the maps of rank at most `n`,
is the `n`-th singular value `σₙ(T) = (T : E →ₗ[𝕜] F).singularValues n`, including the zero tail
from the dimension of `E` on. This identifies the approximation numbers, which make sense for
operators between arbitrary normed spaces, with the singular values of finite-dimensional linear
algebra, so estimates proved for either sequence transfer to the other.

Let `(vᵢ)` be the right singular basis of `T`, the orthonormal eigenbasis of `T† T` in which
`T† T vᵢ = σᵢ² vᵢ`. Projecting away from the span of the `vᵢ` with `i < n` gives an approximant of
rank at most `n` whose error is `T` restricted to the span of the `vᵢ` with `i ≥ n`, of norm at most
`σₙ`; this is the orthogonal-tail bound
`ContinuousLinearMap.singularValue_le_nnnorm_comp_orthogonal`.
Conversely `T` stretches every vector of the `(n + 1)`-dimensional span of the `vᵢ` with `i ≤ n`
by at least `σₙ`, so `σₙ ≤ aₙ(T)` by the coercive-subspace bound
`ContinuousLinearMap.le_singularValue_of_lt_rank`.

Two consequences are recorded for linear maps: the operator norm is the largest singular value,
and singular values are `1`-Lipschitz in the operator norm (Weyl's perturbation bound for singular
values), transferred from the corresponding facts `a₀(T) = ‖T‖` and `|aₙ(S) - aₙ(T)| ≤ ‖S - T‖`.

## Main declarations

* `ContinuousLinearMap.singularValue_eq_linearMap_singularValues`: **Eckart–Young**,
  `aₙ(T) = σₙ(T)` in finite dimension.
* `LinearMap.norm_toContinuousLinearMap_eq_singularValues_zero`: `‖A‖ = σ₀(A)`.
* `LinearMap.abs_singularValues_sub_singularValues_le`: `|σₙ(A) - σₙ(B)| ≤ ‖A - B‖`.

## References

* C. Eckart, G. Young, *The approximation of one matrix by another of lower rank*,
  Psychometrika 1 (1936), 211–218.
* R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press (2013),
  Chapter 7 (the singular value decomposition and its consequences).
* A. Pietsch, *Eigenvalues and s-Numbers*, Cambridge Studies in Advanced Mathematics 13,
  Cambridge University Press (1987), Chapter 2.
-/

public section

open Module
open scoped NNReal

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

namespace ContinuousLinearMap

/-- **Eckart–Young.** Between finite-dimensional inner product spaces, the approximation numbers
of a bounded linear map are its singular values: `aₙ(T) = σₙ(T)` for every `n`, both sides
vanishing from the dimension of the source on. -/
theorem singularValue_eq_linearMap_singularValues (T : E →L[𝕜] F) (n : ℕ) :
    (T.singularValue n : ℝ) = (T : E →ₗ[𝕜] F).singularValues n := by
  set A : E →ₗ[𝕜] F := (T : E →ₗ[𝕜] F)
  set v := A.rightSingularBasis
  refine le_antisymm ?_ ?_
  · -- Upper bound: `T` on the orthogonal complement of the first `n` right singular vectors.
    set V := v.spanIndices ↑({i | (i : ℕ) < n} : Finset (Fin (finrank 𝕜 E)))
    refine (NNReal.coe_le_coe.mpr
      (T.singularValue_le_nnnorm_comp_orthogonal (v.rank_spanIndices_val_lt_le n))).trans ?_
    rw [coe_nnnorm]
    exact T.norm_comp_orthogonal_spanIndices_le_of_adjoint_comp_self_eigenbasis v
      (A.sq_singularValues_antitone.comp_monotone (Fin.valOrderEmb _).monotone)
      A.adjoint_comp_self_rightSingularBasis n
  · -- Lower bound: `T` is `σₙ`-coercive on the span of the first `n + 1` right singular vectors.
    rcases lt_or_ge n (finrank 𝕜 E) with hn | hn
    · set V := v.spanIndices ↑({i | (i : ℕ) < n + 1} : Finset (Fin (finrank 𝕜 E)))
      have hV : (n : Cardinal) < Module.rank 𝕜 V := by
        rw [← finrank_eq_rank, v.finrank_spanIndices, Fin.card_filter_val_lt,
          min_eq_right (Nat.succ_le_of_lt hn)]
        exact_mod_cast n.lt_succ_self
      refine T.le_singularValue_of_lt_rank hV fun x hx ↦ ?_
      have hx' : x ∈ v.spanIndices {i | (i : ℕ) ≤ n} :=
        v.spanIndices_mono (fun i hi ↦ by simpa [Nat.lt_succ_iff] using hi) hx
      simpa [A] using A.singularValues_mul_norm_le_norm_apply hx'
    · rw [A.singularValues_of_finrank_le hn]
      exact NNReal.coe_nonneg _

end ContinuousLinearMap

namespace LinearMap

/-- The operator norm of a linear map between finite-dimensional inner product spaces is its
largest singular value: `‖A‖ = σ₀(A)`. -/
theorem norm_toContinuousLinearMap_eq_singularValues_zero (A : E →ₗ[𝕜] F) :
    ‖LinearMap.toContinuousLinearMap A‖ = A.singularValues 0 := by
  rw [← coe_nnnorm, ← ContinuousLinearMap.singularValue_zero,
    ContinuousLinearMap.singularValue_eq_linearMap_singularValues, coe_toContinuousLinearMap]

/-- **Weyl's perturbation bound for singular values.** Each singular value of a linear map between
finite-dimensional inner product spaces is `1`-Lipschitz in the operator norm:
`|σₙ(A) - σₙ(B)| ≤ ‖A - B‖`. -/
theorem abs_singularValues_sub_singularValues_le (A B : E →ₗ[𝕜] F) (n : ℕ) :
    |A.singularValues n - B.singularValues n| ≤ ‖LinearMap.toContinuousLinearMap (A - B)‖ := by
  simpa [ContinuousLinearMap.singularValue_eq_linearMap_singularValues] using
    ContinuousLinearMap.abs_singularValue_sub_singularValue_le
      (LinearMap.toContinuousLinearMap A) (LinearMap.toContinuousLinearMap B) n

end LinearMap
