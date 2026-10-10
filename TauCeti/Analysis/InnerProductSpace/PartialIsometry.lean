/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Algebra.Star.PartialIsometry

/-!
# Partial isometries between Hilbert spaces

A map `u : E → F` between inner product spaces is a *partial isometry* when `u u† u = u`. This
file defines the predicate for bounded operators between complete spaces
(`ContinuousLinearMap.IsPartialIsometry`) and for linear maps between finite-dimensional spaces
(`LinearMap.IsPartialIsometry`). Unlike the star-monoid predicate `TauCeti.IsPartialIsometry`,
these allow different source and target spaces, as needed for the polar factor of a rectangular
operator; on endomorphisms the three notions agree.

The main result is the geometric characterization: `u` is a partial isometry exactly when it is
isometric on the orthogonal complement `(ker u)ᗮ` of its kernel, its *initial space*. Equivalently,
the *initial projection* `u† u` is the orthogonal projection onto `(ker u)ᗮ`, and it suffices that
`u† u` be idempotent. The proof uses that every operator factors through the projection onto
`(ker u)ᗮ`: `u ∘L (ker u)ᗮ.starProjection = u`.

## Main declarations

* `ContinuousLinearMap.IsPartialIsometry`, `LinearMap.IsPartialIsometry`: the predicate
  `u ∘ u† ∘ u = u`.
* `ContinuousLinearMap.isPartialIsometry_iff_starMul`, `LinearMap.isPartialIsometry_iff_starMul`:
  for endomorphisms, agreement with the star-monoid predicate.
* `ContinuousLinearMap.isPartialIsometry_iff_norm_map`, `LinearMap.isPartialIsometry_iff_norm_map`:
  `u` is a partial isometry iff `‖u x‖ = ‖x‖` for every `x ∈ (ker u)ᗮ`.
* `ContinuousLinearMap.isPartialIsometry_iff_adjoint_comp_self`,
  `LinearMap.isPartialIsometry_iff_adjoint_comp_self`: `u` is a partial isometry iff
  `u† u = (ker u)ᗮ.starProjection`.
* `ContinuousLinearMap.isPartialIsometry_iff_isIdempotentElem_adjoint_comp_self`,
  `LinearMap.isPartialIsometry_iff_isIdempotentElem_adjoint_comp_self`: `u` is a partial
  isometry iff `u† u` is idempotent.
* `ContinuousLinearMap.IsPartialIsometry.isStarProjection_adjoint_comp_self`,
  `ContinuousLinearMap.IsPartialIsometry.isStarProjection_self_comp_adjoint` (and their
  `LinearMap` versions): the initial projection `u† u` and the final projection `u u†` of a
  partial isometry are star projections.
* `ContinuousLinearMap.IsPartialIsometry.adjoint`: the adjoint of a partial isometry is a partial
  isometry.
* `LinearIsometry.isPartialIsometry_toContinuousLinearMap`: linear isometries are partial
  isometries.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), the section on
  the polar decomposition.
-/

public section

open scoped InnerProduct InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace ContinuousLinearMap

variable [CompleteSpace E]

/-- Every bounded operator factors through the orthogonal projection onto the orthogonal
complement of its kernel. -/
@[simp]
theorem comp_starProjection_orthogonal_ker (u : E →L[𝕜] F) :
    u ∘L u.kerᗮ.starProjection = u := by
  have : CompleteSpace u.ker := u.isClosed_ker.completeSpace_coe
  ext x
  have hx : x - u.kerᗮ.starProjection x ∈ u.ker := by
    simpa only [Submodule.orthogonal_orthogonal] using
      u.kerᗮ.sub_starProjection_mem_orthogonal x
  rw [LinearMap.mem_ker, coe_coe, map_sub, sub_eq_zero] at hx
  exact hx.symm

variable [CompleteSpace F]

/-- A bounded operator `u : E →L[𝕜] F` between Hilbert spaces is a *partial isometry* when
`u ∘L u† ∘L u = u`. -/
def IsPartialIsometry (u : E →L[𝕜] F) : Prop :=
  u ∘L u† ∘L u = u

variable {u : E →L[𝕜] F}

theorem isPartialIsometry_iff : u.IsPartialIsometry ↔ u ∘L u† ∘L u = u :=
  Iff.rfl

/-- On bounded endomorphisms, the rectangular predicate agrees with the star-monoid predicate
`TauCeti.IsPartialIsometry`. -/
theorem isPartialIsometry_iff_starMul {u : E →L[𝕜] E} :
    u.IsPartialIsometry ↔ TauCeti.IsPartialIsometry u := by
  rw [isPartialIsometry_iff, TauCeti.isPartialIsometry_iff, star_eq_adjoint, mul_assoc, mul_def,
    mul_def]

/-- A bounded operator is a partial isometry iff its initial projection `u† ∘L u` is the
orthogonal projection onto the orthogonal complement of its kernel. -/
theorem isPartialIsometry_iff_adjoint_comp_self :
    u.IsPartialIsometry ↔ u† ∘L u = u.kerᗮ.starProjection := by
  refine ⟨fun hu ↦ ?_, fun h ↦ by
    rw [isPartialIsometry_iff, h, comp_starProjection_orthogonal_ker]⟩
  -- `u† (u x)` lies in `(ker u)ᗮ`, and `x - u† (u x)` lies in `ker u` because `u u† u = u`.
  ext x
  have hP : adjoint u (u x) ∈ u.kerᗮ :=
    u.orthogonal_ker ▸ Submodule.le_topologicalClosure _ ⟨u x, rfl⟩
  have hK : x - adjoint u (u x) ∈ u.ker := by
    simpa [sub_eq_zero] using (DFunLike.congr_fun hu x).symm
  have := u.kerᗮ.starProjection.map_add (adjoint u (u x)) (x - adjoint u (u x))
  rw [add_sub_cancel, Submodule.starProjection_eq_self_iff.mpr hP,
    Submodule.starProjection_orthogonal_apply_eq_zero hK, add_zero] at this
  simpa using this.symm

/-- A bounded operator is a partial isometry iff its initial projection `u† ∘L u` is
idempotent. -/
theorem isPartialIsometry_iff_isIdempotentElem_adjoint_comp_self :
    u.IsPartialIsometry ↔ IsIdempotentElem (u† ∘L u) := by
  refine ⟨fun hu ↦ ?_, fun h ↦ ?_⟩
  · rw [IsIdempotentElem, mul_def, comp_assoc, isPartialIsometry_iff.mp hu]
  · -- `x - u† (u x)` is killed by `u† ∘L u`, hence lies in `ker (u† ∘L u) = ker u`.
    ext x
    have hK : x - adjoint u (u x) ∈ (u† ∘L u).ker := by
      simpa [sub_eq_zero] using (DFunLike.congr_fun h x).symm
    rw [ker_adjoint_comp_self, LinearMap.mem_ker, coe_coe, map_sub, sub_eq_zero] at hK
    exact hK.symm

/-- The initial projection `u† ∘L u` of a partial isometry is a star projection. -/
theorem IsPartialIsometry.isStarProjection_adjoint_comp_self (hu : u.IsPartialIsometry) :
    IsStarProjection (u† ∘L u) :=
  isPartialIsometry_iff_adjoint_comp_self.mp hu ▸ isStarProjection_starProjection

/-- The adjoint of a partial isometry is a partial isometry. -/
protected theorem IsPartialIsometry.adjoint (hu : u.IsPartialIsometry) :
    u†.IsPartialIsometry := by
  simpa [isPartialIsometry_iff, comp_assoc] using congr_arg adjoint hu

@[simp]
theorem isPartialIsometry_adjoint_iff : u†.IsPartialIsometry ↔ u.IsPartialIsometry :=
  ⟨fun hu ↦ adjoint_adjoint u ▸ hu.adjoint, IsPartialIsometry.adjoint⟩

/-- The final projection `u ∘L u†` of a partial isometry is a star projection. -/
theorem IsPartialIsometry.isStarProjection_self_comp_adjoint (hu : u.IsPartialIsometry) :
    IsStarProjection (u ∘L u†) := by
  simpa using hu.adjoint.isStarProjection_adjoint_comp_self

/-- **Geometric characterization of partial isometries.** A bounded operator is a partial
isometry iff it preserves norms on the orthogonal complement of its kernel. -/
theorem isPartialIsometry_iff_norm_map :
    u.IsPartialIsometry ↔ ∀ x ∈ u.kerᗮ, ‖u x‖ = ‖x‖ := by
  rw [isPartialIsometry_iff_adjoint_comp_self]
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · have : ⟪u x, u x⟫_𝕜 = ⟪x, x⟫_𝕜 := by
      rw [← adjoint_inner_left, ← comp_apply, h, Submodule.starProjection_eq_self_iff.mpr hx]
    rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜), norm_eq_sqrt_re_inner (𝕜 := 𝕜) x, this]
  · -- `u` preserves inner products on `(ker u)ᗮ`, and factors through the projection onto it.
    set Q := u.kerᗮ.starProjection
    have hinner : ∀ x y : u.kerᗮ, ⟪u x, u y⟫_𝕜 = ⟪(x : E), y⟫_𝕜 :=
      (LinearMap.norm_map_iff_inner_map_map (u.toLinearMap ∘ₗ u.kerᗮ.subtype)).mp
        fun x ↦ h x x.2
    ext x
    refine ext_inner_left 𝕜 fun z ↦ ?_
    have hQ : ∀ y, u (Q y) = u y := fun y ↦ congr($(comp_starProjection_orthogonal_ker u) y)
    rw [comp_apply, adjoint_inner_right, ← hQ z, ← hQ x,
      hinner ⟨Q z, Submodule.starProjection_apply_mem _ z⟩
        ⟨Q x, Submodule.starProjection_apply_mem _ x⟩,
      Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem _ x)]

@[simp]
theorem isPartialIsometry_zero : (0 : E →L[𝕜] F).IsPartialIsometry := by
  simp [isPartialIsometry_iff]

end ContinuousLinearMap

/-- A linear isometry between Hilbert spaces is a partial isometry. -/
theorem LinearIsometry.isPartialIsometry_toContinuousLinearMap [CompleteSpace E] [CompleteSpace F]
    (f : E →ₗᵢ[𝕜] F) : f.toContinuousLinearMap.IsPartialIsometry := by
  rw [ContinuousLinearMap.isPartialIsometry_iff, f.adjoint_comp_self,
    ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]

namespace LinearMap

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- A linear map `u : E →ₗ[𝕜] F` between finite-dimensional inner product spaces is a *partial
isometry* when `u ∘ₗ u† ∘ₗ u = u`. -/
def IsPartialIsometry (u : E →ₗ[𝕜] F) : Prop :=
  u ∘ₗ u.adjoint ∘ₗ u = u

variable {u : E →ₗ[𝕜] F}

theorem isPartialIsometry_iff : u.IsPartialIsometry ↔ u ∘ₗ u.adjoint ∘ₗ u = u :=
  Iff.rfl

/-- A linear map between finite-dimensional spaces is a partial isometry iff the corresponding
bounded operator is. -/
theorem isPartialIsometry_toContinuousLinearMap_iff :
    have := FiniteDimensional.complete 𝕜 E
    have := FiniteDimensional.complete 𝕜 F
    (toContinuousLinearMap u).IsPartialIsometry ↔ u.IsPartialIsometry := by
  intro _ _
  rw [ContinuousLinearMap.isPartialIsometry_iff, isPartialIsometry_iff,
    ← adjoint_toContinuousLinearMap, ← ContinuousLinearMap.coe_inj]
  simp

/-- On endomorphisms, the rectangular predicate agrees with the star-monoid predicate
`TauCeti.IsPartialIsometry`. -/
theorem isPartialIsometry_iff_starMul {u : E →ₗ[𝕜] E} :
    u.IsPartialIsometry ↔ TauCeti.IsPartialIsometry u := by
  rw [isPartialIsometry_iff, TauCeti.isPartialIsometry_iff, star_eq_adjoint, mul_assoc,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp]

/-- **Geometric characterization of partial isometries.** A linear map between
finite-dimensional inner product spaces is a partial isometry iff it preserves norms on the
orthogonal complement of its kernel. -/
theorem isPartialIsometry_iff_norm_map :
    u.IsPartialIsometry ↔ ∀ x ∈ (ker u)ᗮ, ‖u x‖ = ‖x‖ := by
  have := FiniteDimensional.complete 𝕜 E
  simp [← isPartialIsometry_toContinuousLinearMap_iff,
    ContinuousLinearMap.isPartialIsometry_iff_norm_map]

/-- A linear map between finite-dimensional spaces is a partial isometry iff its initial
projection `u† ∘ₗ u` is the orthogonal projection onto the orthogonal complement of its kernel. -/
theorem isPartialIsometry_iff_adjoint_comp_self :
    u.IsPartialIsometry ↔ u.adjoint ∘ₗ u = (ker u)ᗮ.starProjection := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  rw [← show _ ↔ u.IsPartialIsometry from isPartialIsometry_toContinuousLinearMap_iff,
    ContinuousLinearMap.isPartialIsometry_iff_adjoint_comp_self, ← adjoint_toContinuousLinearMap,
    ← ContinuousLinearMap.coe_inj]
  rfl

/-- A linear map between finite-dimensional spaces is a partial isometry iff its initial
projection `u† ∘ₗ u` is idempotent. -/
theorem isPartialIsometry_iff_isIdempotentElem_adjoint_comp_self :
    u.IsPartialIsometry ↔ IsIdempotentElem (u.adjoint ∘ₗ u) := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  rw [← show _ ↔ u.IsPartialIsometry from isPartialIsometry_toContinuousLinearMap_iff,
    ContinuousLinearMap.isPartialIsometry_iff_isIdempotentElem_adjoint_comp_self,
    ← adjoint_toContinuousLinearMap, IsIdempotentElem, IsIdempotentElem,
    ← ContinuousLinearMap.coe_inj]
  rfl

/-- The initial projection `u† ∘ₗ u` of a partial isometry is a star projection. -/
theorem IsPartialIsometry.isStarProjection_adjoint_comp_self (hu : u.IsPartialIsometry) :
    IsStarProjection (u.adjoint ∘ₗ u) where
  isIdempotentElem := by
    rw [IsIdempotentElem, Module.End.mul_eq_comp, comp_assoc, isPartialIsometry_iff.mp hu]
  isSelfAdjoint := by rw [isSelfAdjoint_iff', adjoint_comp, adjoint_adjoint]

/-- The adjoint of a partial isometry is a partial isometry. -/
protected theorem IsPartialIsometry.adjoint (hu : u.IsPartialIsometry) :
    u.adjoint.IsPartialIsometry := by
  simpa [isPartialIsometry_iff, comp_assoc] using congr_arg adjoint hu

@[simp]
theorem isPartialIsometry_adjoint_iff : u.adjoint.IsPartialIsometry ↔ u.IsPartialIsometry :=
  ⟨fun hu ↦ adjoint_adjoint u ▸ hu.adjoint, IsPartialIsometry.adjoint⟩

/-- The final projection `u ∘ₗ u†` of a partial isometry is a star projection. -/
theorem IsPartialIsometry.isStarProjection_self_comp_adjoint (hu : u.IsPartialIsometry) :
    IsStarProjection (u ∘ₗ u.adjoint) := by
  simpa using hu.adjoint.isStarProjection_adjoint_comp_self

@[simp]
theorem isPartialIsometry_zero : (0 : E →ₗ[𝕜] F).IsPartialIsometry := by
  simp [isPartialIsometry_iff]

end LinearMap

/-- A linear isometry between finite-dimensional inner product spaces is a partial isometry. -/
theorem LinearIsometry.isPartialIsometry_toLinearMap [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (f : E →ₗᵢ[𝕜] F) : f.toLinearMap.IsPartialIsometry := by
  rw [LinearMap.isPartialIsometry_iff, f.adjoint_comp_self', LinearMap.comp_id]
