/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Gram.Factor
public import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Right inverses of formal adjoints from a lower bound

Let `T, ι : Φ →ₗ[𝕜] _` be linear maps from a vector space `Φ`, which carries no topology, into
Hilbert spaces `H` and `F`. In applications `Φ` is a space of test functions, `T` is a
differential operator `P*` on test functions with values in `L²`, and `ι` is the inclusion of
test functions into `L²`. A vector `u ∈ H` with

`⟪u, T φ⟫ = ⟪f, ι φ⟫` for every `φ ∈ Φ`

is a weak solution of `T* u = ι* f`; in the application, of `P u = f` in the sense of
distributions. Suppose that `T` is bounded below relative to `ι`: `‖ι φ‖ ≤ C ‖T φ‖`. Then
`T φ ↦ ι φ` is a well-defined bounded map on the range of `T`. It extends to a bounded operator
`S : H → F` that vanishes on the orthogonal complement of that range: the factor of this map
through the inclusion of the range (`ContinuousLinearMap.factorThru`). Its Hilbert
adjoint `S† : F → H` solves the weak equation (`LinearMap.inner_adjointRightInverse_apply`).
Thus `LinearMap.adjointRightInverse T ι = S†` is a bounded right inverse of the weak operator `T*`,
of norm at most `C` (`LinearMap.norm_adjointRightInverse_le`). For a differential operator `P`
whose formal adjoint satisfies an `L²` lower bound on test functions, this is the statement
that the maximal `L²` realization of `P` is onto, with a bounded right inverse.

Two weak solutions differ by a vector orthogonal to the range of `T`, while `S† f` lies in its
closure (`LinearMap.adjointRightInverse_apply_mem_topologicalClosure`). So `S† f` is the unique
weak solution in that closure: the orthogonal projection onto it of any weak solution
(`LinearMap.adjointRightInverse_apply_eq_starProjection`). Hence it is the weak solution of least
norm: every weak solution `u` satisfies `‖u‖² = ‖S† f‖² + ‖u - S† f‖²`
(`LinearMap.norm_sq_eq_norm_adjointRightInverse_apply_sq_add`).
When `T` is the formal adjoint `P*`, this is, formally, the minimal-norm right inverse
`P* (P P*)⁻¹`.

Existence of a weak solution for a single `f` is also a special case of Lions' representation
theorem (`LinearMap.exists_forall_apply_eq_and_norm_le_of_coercive`, with the test map `T`).
The point here is the bounded linear operator and its characterization by least norm.

## Main declarations

* `LinearMap.adjointRightInverse T ι`: the minimal-norm right inverse of the weak adjoint.
* `LinearMap.inner_adjointRightInverse_apply`: it solves the weak equation.
* `LinearMap.norm_adjointRightInverse_le`: the norm bound `C`.
* `LinearMap.adjointRightInverse_apply_eq_starProjection`: it is the orthogonal projection of any
  weak solution onto the closure of the range of `T`.
* `LinearMap.adjointRightInverse_apply_eq_iff`: it is the unique weak solution of least norm.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Universitext, Springer, 2011, Theorem 2.20.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace LinearMap

variable {𝕜 Φ H F : Type*} [RCLike 𝕜] [AddCommGroup Φ] [Module 𝕜 Φ]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]
  (T : Φ →ₗ[𝕜] H) (ι : Φ →ₗ[𝕜] F)

/-- **The minimal-norm right inverse of the weak adjoint.** For linear maps `T : Φ → H` and
`ι : Φ → F` with `‖ι φ‖ ≤ C ‖T φ‖`, this is the bounded operator `F → H` sending `f` to the
unique `u` in the closure of the range of `T` with `⟪u, T φ⟫ = ⟪f, ι φ⟫` for every `φ`
(`LinearMap.inner_adjointRightInverse_apply`, `LinearMap.adjointRightInverse_apply_eq_iff`).
It is the adjoint of the factor (`ContinuousLinearMap.factorThru`) of the bounded map
`T φ ↦ ι φ` on the range of `T` through the inclusion of that range into `H`. Without a lower
bound its value is unspecified. -/
def adjointRightInverse : F →L[𝕜] H :=
  ContinuousLinearMap.adjoint ((ι.compLeftInverse T).factorThru (range T).subtypeL)

/-- The right inverse takes values in the closure of the range of `T`. -/
theorem adjointRightInverse_apply_mem_topologicalClosure (f : F) :
    adjointRightInverse T ι f ∈ (range T).topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure, Submodule.mem_orthogonal]
  intro y hy
  have hA : ((range T).subtypeL : range T →ₗ[𝕜] H).range = range T := by simp
  rw [← hA] at hy
  rw [adjointRightInverse, ContinuousLinearMap.adjoint_inner_right,
    ContinuousLinearMap.factorThru_apply_of_mem_orthogonal hy, inner_zero_left]

variable {T ι}

/-- **The weak equation.** If `‖ι φ‖ ≤ C ‖T φ‖` for every `φ`, then `u = adjointRightInverse T ι f`
satisfies `⟪u, T φ⟫ = ⟪f, ι φ⟫` for every `φ`, that is, `T* u = ι* f` weakly. -/
theorem inner_adjointRightInverse_apply (h : ∃ C, ∀ φ, ‖ι φ‖ ≤ C * ‖T φ‖) (f : F) (φ : Φ) :
    ⟪adjointRightInverse T ι f, T φ⟫_𝕜 = ⟪f, ι φ⟫_𝕜 := by
  rw [adjointRightInverse, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.factorThru_compLeftInverse_apply h]

/-- **The norm bound.** If `‖ι φ‖ ≤ C ‖T φ‖` for every `φ`, with `C ≥ 0`, the right inverse has
norm at most `C`. -/
theorem norm_adjointRightInverse_le {C : ℝ} (hC : 0 ≤ C) (h : ∀ φ, ‖ι φ‖ ≤ C * ‖T φ‖) :
    ‖adjointRightInverse T ι‖ ≤ C := by
  rw [adjointRightInverse, LinearIsometryEquiv.norm_map]
  exact ContinuousLinearMap.norm_factorThru_le hC (norm_compLeftInverse_apply_le h)

/-- A weak solution differs from the right inverse by a vector orthogonal to the range
of `T`. -/
theorem sub_adjointRightInverse_apply_mem_orthogonal (h : ∃ C, ∀ φ, ‖ι φ‖ ≤ C * ‖T φ‖) {f : F}
    {u : H} (hu : ∀ φ, ⟪u, T φ⟫_𝕜 = ⟪f, ι φ⟫_𝕜) :
    u - adjointRightInverse T ι f ∈ (range T)ᗮ := by
  rw [Submodule.mem_orthogonal']
  rintro _ ⟨φ, rfl⟩
  rw [inner_sub_left, hu, inner_adjointRightInverse_apply h, sub_self]

/-- **Orthogonal projection.** If `‖ι φ‖ ≤ C ‖T φ‖` for every `φ`, the right inverse sends `f` to
the orthogonal projection of any weak solution `u` of `T* u = ι* f` onto the closure of the range
of `T`. -/
theorem adjointRightInverse_apply_eq_starProjection (h : ∃ C, ∀ φ, ‖ι φ‖ ≤ C * ‖T φ‖) {f : F}
    {u : H} (hu : ∀ φ, ⟪u, T φ⟫_𝕜 = ⟪f, ι φ⟫_𝕜) :
    adjointRightInverse T ι f = (range T).topologicalClosure.starProjection u := by
  refine (Submodule.eq_starProjection_of_mem_orthogonal
    (adjointRightInverse_apply_mem_topologicalClosure T ι f) ?_).symm
  rw [Submodule.orthogonal_closure]
  exact sub_adjointRightInverse_apply_mem_orthogonal h hu

/-- **Pythagoras for weak solutions.** Every weak solution `u` of `T* u = ι* f` satisfies
`‖u‖² = ‖adjointRightInverse T ι f‖² + ‖u - adjointRightInverse T ι f‖²`. -/
theorem norm_sq_eq_norm_adjointRightInverse_apply_sq_add
    (h : ∃ C, ∀ φ, ‖ι φ‖ ≤ C * ‖T φ‖) {f : F} {u : H} (hu : ∀ φ, ⟪u, T φ⟫_𝕜 = ⟪f, ι φ⟫_𝕜) :
    ‖u‖ ^ 2 = ‖adjointRightInverse T ι f‖ ^ 2 + ‖u - adjointRightInverse T ι f‖ ^ 2 := by
  rw [adjointRightInverse_apply_eq_starProjection h hu, ← Submodule.starProjection_orthogonal_val]
  exact Submodule.norm_sq_eq_add_norm_sq_starProjection u _

/-- **Least norm.** The right inverse has norm at most that of any weak solution. -/
theorem norm_adjointRightInverse_apply_le (h : ∃ C, ∀ φ, ‖ι φ‖ ≤ C * ‖T φ‖) {f : F} {u : H}
    (hu : ∀ φ, ⟪u, T φ⟫_𝕜 = ⟪f, ι φ⟫_𝕜) :
    ‖adjointRightInverse T ι f‖ ≤ ‖u‖ := by
  rw [adjointRightInverse_apply_eq_starProjection h hu]
  exact Submodule.norm_starProjection_apply_le _ u

/-- **Characterization.** If `‖ι φ‖ ≤ C ‖T φ‖` for every `φ`, then `adjointRightInverse T ι f` is
the unique weak solution of `T* u = ι* f` of least norm. -/
theorem adjointRightInverse_apply_eq_iff (h : ∃ C, ∀ φ, ‖ι φ‖ ≤ C * ‖T φ‖) {f : F} {u : H} :
    adjointRightInverse T ι f = u ↔ (∀ φ, ⟪u, T φ⟫_𝕜 = ⟪f, ι φ⟫_𝕜) ∧
      ∀ v : H, (∀ φ, ⟪v, T φ⟫_𝕜 = ⟪f, ι φ⟫_𝕜) → ‖u‖ ≤ ‖v‖ := by
  constructor
  · rintro rfl
    exact ⟨inner_adjointRightInverse_apply h f, fun v hv ↦ norm_adjointRightInverse_apply_le h hv⟩
  · rintro ⟨hu, hmin⟩
    have hle := hmin _ (inner_adjointRightInverse_apply h f)
    rw [adjointRightInverse_apply_eq_starProjection h hu] at hle ⊢
    exact (Submodule.eq_starProjection_of_norm_le _ hle).symm

end LinearMap
