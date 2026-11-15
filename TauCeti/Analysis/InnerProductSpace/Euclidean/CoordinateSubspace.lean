/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import TauCeti.Algebra.Group.Action.Pi
public import TauCeti.Analysis.InnerProductSpace.BasisSpan

/-!
# Coordinate subspaces and the diagonal torus

A coordinate subspace of `𝕜^ι` is the span of the standard basis vectors `eᵢ` with `i` in a set
`s` of indices, `(EuclideanSpace.basisFun ι 𝕜).spanIndices s`. A permutation `σ` of the
coordinates carries it to the coordinate subspace of `σ '' s`
(`TauCeti.map_piLpCongrLeft_spanIndices_basisFun`).

The diagonal torus `T = ι → Circle` acts on `ℂ^ι` coordinatewise, `(t • v)ᵢ = tᵢ vᵢ`, and hence on
its complex subspaces (`Submodule.pointwiseDistribMulAction`, in the `Pointwise` scope). This file
proves that the subspaces fixed by `T` are exactly the coordinate subspaces
(`TauCeti.mem_fixedPoints_iff_exists_eq_spanIndices`). If a subspace `V` is invariant under `T`
and contains `v`, then it contains `v + t • v = 2 vᵢ eᵢ` for the sign vector `t` with `tᵢ = 1` and
`tⱼ = -1` for `j ≠ i`, so `vᵢ ≠ 0` forces `eᵢ ∈ V`
(`TauCeti.single_apply_mem_of_forall_smul_mem`). Hence `V` is spanned by the basis vectors it
contains (`TauCeti.eq_spanIndices_of_forall_smul_mem`). Only the finite subgroup `{±1}^ι` of the
torus is used.

This is the linear algebra behind the fixed points of torus actions on Grassmannians and flag
manifolds: a point of a Grassmannian of `ℂ^ι` is fixed by the diagonal torus exactly when it is a
coordinate subspace, and a flag is fixed exactly when each of its members is.

## Main results

* `TauCeti.eq_spanIndices_of_forall_smul_mem`: a torus-invariant subspace is spanned by the
  standard basis vectors it contains.
* `TauCeti.smul_spanIndices`: coordinate subspaces are fixed by the torus.
* `TauCeti.mem_fixedPoints_iff_exists_eq_spanIndices`: the torus-fixed subspaces are exactly the
  coordinate subspaces.
* `TauCeti.map_piLpCongrLeft_spanIndices_basisFun`: permuting the coordinates permutes the
  coordinate subspaces.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bulletin of the London Mathematical
  Society 14 (1982), 1–15, Section 3 (fixed points of the diagonal torus on Grassmannians and
  flag manifolds).
-/

public section

open scoped Pointwise

namespace TauCeti

variable {ι : Type*}

/-- A complex subspace of `ℂ^ι` invariant under the diagonal torus contains the coordinate
projection `vᵢ eᵢ` of each of its vectors `v`. -/
theorem single_apply_mem_of_forall_smul_mem [DecidableEq ι] {V : Submodule ℂ (EuclideanSpace ℂ ι)}
    (hV : ∀ t : ι → Circle, ∀ v ∈ V, t • v ∈ V) {v : EuclideanSpace ℂ ι} (hv : v ∈ V) (i : ι) :
    EuclideanSpace.single i (v i) ∈ V := by
  -- `t` is the sign vector with `tᵢ = 1` and `tⱼ = -1` for `j ≠ i`.
  let t : ι → Circle := fun j ↦ if j = i then 1 else -1
  have h2 : v + t • v = (2 : ℂ) • EuclideanSpace.single i (v i) := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [t, two_smul]
    · simp [t, hj, Circle.smul_def]
  have := V.smul_mem (2 : ℂ)⁻¹ (h2 ▸ V.add_mem hv (hV t v hv))
  rwa [smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul] at this

variable [Fintype ι]

/-- A complex subspace of `ℂ^ι` invariant under the diagonal torus is the coordinate subspace
spanned by the standard basis vectors it contains. -/
theorem eq_spanIndices_of_forall_smul_mem {V : Submodule ℂ (EuclideanSpace ℂ ι)}
    (hV : ∀ t : ι → Circle, ∀ v ∈ V, t • v ∈ V) :
    V = (EuclideanSpace.basisFun ι ℂ).spanIndices {i | EuclideanSpace.basisFun ι ℂ i ∈ V} := by
  classical
  refine le_antisymm (fun v hv ↦ ?_) ?_
  · rw [OrthonormalBasis.mem_spanIndices_iff]
    intro i hi
    rw [EuclideanSpace.basisFun_repr]
    by_contra hvi
    apply hi
    have h : (v i)⁻¹ • EuclideanSpace.single i (v i) = EuclideanSpace.basisFun ι ℂ i := by
      ext j
      by_cases hj : j = i <;> simp [hj, hvi]
    rw [Set.mem_ofPred_eq, ← h]
    exact V.smul_mem _ (single_apply_mem_of_forall_smul_mem hV hv i)
  · rw [OrthonormalBasis.spanIndices_eq_span, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hi

/-- The diagonal torus maps each coordinate subspace of `ℂ^ι` into itself. -/
theorem smul_mem_spanIndices {s : Set ι} (t : ι → Circle) {v : EuclideanSpace ℂ ι}
    (hv : v ∈ (EuclideanSpace.basisFun ι ℂ).spanIndices s) :
    t • v ∈ (EuclideanSpace.basisFun ι ℂ).spanIndices s := by
  simp only [OrthonormalBasis.mem_spanIndices_iff, EuclideanSpace.basisFun_repr] at hv ⊢
  intro i hi
  simp [hv i hi]

/-- Coordinate subspaces of `ℂ^ι` are fixed by the diagonal torus. -/
@[simp]
theorem smul_spanIndices (t : ι → Circle) (s : Set ι) :
    t • (EuclideanSpace.basisFun ι ℂ).spanIndices s =
      (EuclideanSpace.basisFun ι ℂ).spanIndices s := by
  ext v
  rw [Submodule.mem_smul_pointwise_iff_exists]
  refine ⟨?_, fun hv ↦ ⟨t⁻¹ • v, smul_mem_spanIndices t⁻¹ hv, smul_inv_smul t v⟩⟩
  rintro ⟨w, hw, rfl⟩
  exact smul_mem_spanIndices t hw

/-- The complex subspaces of `ℂ^ι` fixed by the diagonal torus are exactly the coordinate
subspaces. -/
theorem mem_fixedPoints_iff_exists_eq_spanIndices {V : Submodule ℂ (EuclideanSpace ℂ ι)} :
    V ∈ MulAction.fixedPoints (ι → Circle) (Submodule ℂ (EuclideanSpace ℂ ι)) ↔
      ∃ s : Finset ι, V = (EuclideanSpace.basisFun ι ℂ).spanIndices s := by
  refine ⟨fun hV ↦ ⟨(Set.toFinite {i | EuclideanSpace.basisFun ι ℂ i ∈ V}).toFinset, ?_⟩, ?_⟩
  · rw [Set.Finite.coe_toFinset]
    refine eq_spanIndices_of_forall_smul_mem fun t v hv ↦ ?_
    rw [← hV t]
    exact Submodule.smul_mem_pointwise_smul v t V hv
  · rintro ⟨s, rfl⟩ t
    exact smul_spanIndices t s

/-- Permuting the coordinates of `𝕜^ι` by `σ` carries the coordinate subspace of `s` to that of
`σ '' s`. -/
theorem map_piLpCongrLeft_spanIndices_basisFun {𝕜 ι' : Type*} [RCLike 𝕜] [Fintype ι']
    (σ : ι ≃ ι') (s : Set ι) :
    ((EuclideanSpace.basisFun ι 𝕜).spanIndices s).map
        (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 σ : EuclideanSpace 𝕜 ι →ₗ[𝕜] EuclideanSpace 𝕜 ι') =
      (EuclideanSpace.basisFun ι' 𝕜).spanIndices (σ '' s) := by
  classical
  simp only [OrthonormalBasis.spanIndices_eq_span, Submodule.map_span, Set.image_image,
    EuclideanSpace.basisFun_apply]
  exact congrArg _ (Set.image_congr fun i _ ↦ EuclideanSpace.piLpCongrLeft_single σ i 1)

end TauCeti
