/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Analysis.InnerProductSpace.Positive
public import TauCeti.Analysis.Normed.Operator.Banach

/-!
# The Laplacian of two composable operators

Let `A : U → V` and `B : V → W` be bounded operators between Hilbert spaces. The *Laplacian* of
the pair at the middle space is the positive operator

`Δ = A A† + B† B : V → V` (`ContinuousLinearMap.hodgeLaplacian`),

the finite-dimensional model of the Hodge Laplacian `d d* + d* d` of an elliptic complex. Since
`⟪Δ v, v⟫ = ‖A† v‖² + ‖B v‖²` (`ContinuousLinearMap.inner_hodgeLaplacian_apply_self`), the kernel
of `Δ` is `ker A† ⊓ ker B` (`ContinuousLinearMap.ker_hodgeLaplacian`).

When `B A = 0`, so that `U → V → W` is a complex, `Δ` detects exactness at `V`: as `ker A†` is the
orthogonal complement of `range A`, a vector killed by `Δ` lies in `ker B ⊓ (range A)ᗮ`, and this
is zero exactly when `ker B = range A`, provided `range A` is closed. Hence

* `ContinuousLinearMap.injective_hodgeLaplacian`: if the complex is exact at `V`, then `Δ` is
  injective;
* `ContinuousLinearMap.exact_iff_injective_hodgeLaplacian`: for a complex whose first operator
  has closed range, exactness at `V` is equivalent to injectivity of `Δ`;
* `ContinuousLinearMap.exact_iff_isInvertible_hodgeLaplacian`: when `V` is finite-dimensional,
  exactness at `V` is equivalent to invertibility of `Δ`.

Applied fibrewise to the principal symbols of a complex of differential operators, the last
statement says that a complex is elliptic, that is its symbol sequence is exact at every nonzero
covector, exactly when its Laplacians are elliptic.

The Laplacian of the adjoint complex `W → V → U` is the same operator
(`ContinuousLinearMap.hodgeLaplacian_adjoint_adjoint`).

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §7.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 U V W : Type*} [RCLike 𝕜]
  [NormedAddCommGroup U] [InnerProductSpace 𝕜 U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [CompleteSpace W]
  (A : U →L[𝕜] V) (B : V →L[𝕜] W)

/-- The Laplacian `A A† + B† B` of two composable operators `A : U → V` and `B : V → W`, an
operator on the middle space `V`. -/
noncomputable def hodgeLaplacian : V →L[𝕜] V :=
  A ∘L adjoint A + adjoint B ∘L B

theorem hodgeLaplacian_def : A.hodgeLaplacian B = A ∘L adjoint A + adjoint B ∘L B :=
  (rfl)

@[simp]
theorem hodgeLaplacian_apply (v : V) :
    A.hodgeLaplacian B v = A (adjoint A v) + adjoint B (B v) :=
  (rfl)

/-- The adjoint complex `B† : W → V`, `A† : V → U` has the same Laplacian. -/
@[simp]
theorem hodgeLaplacian_adjoint_adjoint :
    (adjoint B).hodgeLaplacian (adjoint A) = A.hodgeLaplacian B := by
  rw [hodgeLaplacian_def, hodgeLaplacian_def, adjoint_adjoint, adjoint_adjoint, add_comm]

/-- The Laplacian is a positive operator. -/
theorem isPositive_hodgeLaplacian : (A.hodgeLaplacian B).IsPositive :=
  (isPositive_self_comp_adjoint A).add (isPositive_adjoint_comp_self B)

/-- The Laplacian is self-adjoint. -/
theorem isSelfAdjoint_hodgeLaplacian : IsSelfAdjoint (A.hodgeLaplacian B) :=
  (A.isPositive_hodgeLaplacian B).isSelfAdjoint

/-- The quadratic form of the Laplacian: `⟪Δ v, v⟫ = ‖A† v‖² + ‖B v‖²`. -/
theorem inner_hodgeLaplacian_apply_self (v : V) :
    ⟪A.hodgeLaplacian B v, v⟫_𝕜 = ((‖adjoint A v‖ ^ 2 + ‖B v‖ ^ 2 : ℝ) : 𝕜) := by
  rw [hodgeLaplacian_apply, inner_add_left, ← adjoint_inner_right A, adjoint_inner_left B,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  push_cast
  ring

/-- The kernel of the Laplacian is `ker A† ⊓ ker B`. -/
theorem ker_hodgeLaplacian : (A.hodgeLaplacian B).ker = (adjoint A).ker ⊓ B.ker := by
  ext v
  simp only [Submodule.mem_inf, LinearMap.mem_ker, coe_coe]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h.1, h.2]⟩
  have h0 := A.inner_hodgeLaplacian_apply_self B v
  rw [h, inner_zero_left, eq_comm, RCLike.ofReal_eq_zero,
    add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)] at h0
  simpa using h0

/-- If `U → V → W` is exact at `V`, the Laplacian at `V` is injective. -/
theorem injective_hodgeLaplacian (h : Function.Exact A B) :
    Function.Injective (A.hodgeLaplacian B) := by
  rw [← coe_coe, ← LinearMap.ker_eq_bot, ker_hodgeLaplacian, ← orthogonal_range,
    ← (LinearMap.exact_iff.1 h : B.ker = A.range), inf_comm]
  exact Submodule.inf_orthogonal_eq_bot _

/-- For a complex `U → V → W` whose first operator has closed range, injectivity of the
Laplacian at `V` implies exactness at `V`. -/
theorem exact_of_injective_hodgeLaplacian (hBA : B ∘L A = 0)
    (hA : IsClosed (A.range : Set V)) (h : Function.Injective (A.hodgeLaplacian B)) :
    Function.Exact A B := by
  have : CompleteSpace A.range := hA.completeSpace_coe
  rw [← coe_coe, ← LinearMap.ker_eq_bot, ker_hodgeLaplacian, ← orthogonal_range] at h
  refine LinearMap.exact_of_comp_of_mem_range (by simpa using congrArg toLinearMap hBA)
    fun v hv ↦ ?_
  -- Split `v` into its components in `range A` and `(range A)ᗮ`; the second is killed by `B`.
  have hp := A.range.starProjection_apply_mem v
  have hBp : B (A.range.starProjection v) = 0 := by
    obtain ⟨u, hu⟩ := LinearMap.mem_range.1 hp
    rw [← hu, coe_coe, ← comp_apply, hBA, zero_apply]
  have hq : v - A.range.starProjection v ∈ (A.rangeᗮ ⊓ B.ker : Submodule 𝕜 V) :=
    ⟨A.range.sub_starProjection_mem_orthogonal v, LinearMap.mem_ker.2 (by simpa [hBp] using hv)⟩
  rw [h, Submodule.mem_bot, sub_eq_zero] at hq
  exact hq ▸ hp

/-- For a complex `U → V → W` whose first operator has closed range, exactness at `V` is
equivalent to injectivity of the Laplacian at `V`. -/
theorem exact_iff_injective_hodgeLaplacian (hBA : B ∘L A = 0)
    (hA : IsClosed (A.range : Set V)) :
    Function.Exact A B ↔ Function.Injective (A.hodgeLaplacian B) :=
  ⟨A.injective_hodgeLaplacian B, A.exact_of_injective_hodgeLaplacian B hBA hA⟩

/-- For a complex `U → V → W` with finite-dimensional middle space, exactness at `V` is equivalent
to invertibility of the Laplacian at `V`. -/
theorem exact_iff_isInvertible_hodgeLaplacian [FiniteDimensional 𝕜 V] (hBA : B ∘L A = 0) :
    Function.Exact A B ↔ (A.hodgeLaplacian B).IsInvertible := by
  rw [A.exact_iff_injective_hodgeLaplacian B hBA (Submodule.isClosed_of_finiteDimensional _),
    isInvertible_iff_bijective, Function.Bijective, ← coe_coe,
    ← LinearMap.injective_iff_surjective, and_self]

end ContinuousLinearMap
