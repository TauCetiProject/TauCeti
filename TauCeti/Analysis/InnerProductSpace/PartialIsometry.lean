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

A map `u : E → F` between Hilbert spaces is a *partial isometry* when `u u† u = u`, where
`u†` is the adjoint. Unlike the star-monoid predicate `IsPartialIsometry`, this makes sense for maps
between *different* spaces, which is the generality needed for the polar decomposition
`T = U |T|` of a rectangular operator.

The main result is the geometric characterization: `u` is a partial isometry if and only if it
preserves norms on the orthogonal complement of its kernel, and then `u† u` is the orthogonal
projection onto that complement (the *initial space* of `u`). The adjoint of a partial isometry
is a partial isometry, so `u u†` is the orthogonal projection onto `(ker u†)ᗮ`, the closure of
the range of `u` (the *final space* of `u`).

The predicate is developed for bounded operators between complete spaces, and for linear maps
between finite-dimensional spaces, where `LinearMap.adjoint` is available. On endomorphisms both
agree with the star-monoid predicate.

## Main definitions

* `ContinuousLinearMap.IsPartialIsometry u`: `u ∘L u† ∘L u = u`, for `u : E →L[𝕜] F`
  between complete inner product spaces.
* `LinearMap.IsPartialIsometry u`: `u ∘ₗ u.adjoint ∘ₗ u = u`, for `u : E →ₗ[𝕜] F`
  between finite-dimensional inner product spaces.

## Main statements

* `ContinuousLinearMap.isPartialIsometry_iff_adjoint_comp_self_eq_starProjection`: `u` is a
  partial isometry if and only if `u† u` is the orthogonal projection onto `(ker u)ᗮ`.
* `ContinuousLinearMap.isPartialIsometry_iff_norm_map`,
  `LinearMap.isPartialIsometry_iff_norm_map`: `u` is a partial isometry if and only if
  `‖u x‖ = ‖x‖` for every `x ∈ (ker u)ᗮ`.
* `ContinuousLinearMap.isPartialIsometry_adjoint_iff`, `LinearMap.isPartialIsometry_adjoint_iff`:
  the adjoint of a partial isometry is a partial isometry.
* `ContinuousLinearMap.isPartialIsometry_iff_starMul`, `LinearMap.isPartialIsometry_iff_starMul`:
  on endomorphisms the rectangular predicate is the star-monoid predicate.
* `LinearIsometry.isPartialIsometry_toContinuousLinearMap`,
  `LinearIsometry.isPartialIsometry_toLinearMap`, `Submodule.isPartialIsometry_starProjection`:
  linear isometries and orthogonal projections are partial isometries.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Graduate Texts in Mathematics 96,
  Springer (1990): partial isometries and the polar decomposition.
-/

public section

open scoped InnerProduct InnerProductSpace
open RCLike

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace ContinuousLinearMap

variable [CompleteSpace E] [CompleteSpace F]

/-- A bounded operator `u : E →L[𝕜] F` between complete inner product spaces is a *partial
isometry* when `u u† u = u`. Equivalently (`isPartialIsometry_iff_norm_map`), `u` preserves norms
on the orthogonal complement of its kernel. -/
@[mk_iff]
structure IsPartialIsometry (u : E →L[𝕜] F) : Prop where
  /-- The defining identity `u u† u = u` of a partial isometry. -/
  comp_adjoint_comp_self : u ∘L u† ∘L u = u

variable {u : E →L[𝕜] F}

/-- Pointwise form of the identity `u u† u = u`. -/
theorem IsPartialIsometry.apply_adjoint_apply_apply (hu : u.IsPartialIsometry) (x : E) :
    u ((u†) (u x)) = u x :=
  congr($(hu.comp_adjoint_comp_self) x)

omit [CompleteSpace F] in
/-- A bounded operator does not see the projection onto the orthogonal complement of its kernel:
`u (P x) = u x` where `P` is the orthogonal projection onto `(ker u)ᗮ`. -/
theorem apply_starProjection_orthogonal_ker (u : E →L[𝕜] F) (x : E) :
    u (u.kerᗮ.starProjection x) = u x := by
  have h : u (u.ker.starProjection x) = 0 := u.ker.starProjection_apply_mem x
  simp [h]

/-- A bounded operator is a partial isometry if and only if `u† u` is the orthogonal projection
onto the orthogonal complement of its kernel. -/
theorem isPartialIsometry_iff_adjoint_comp_self_eq_starProjection :
    u.IsPartialIsometry ↔ u† ∘L u = u.kerᗮ.starProjection := by
  refine ⟨fun hu ↦ ?_, fun h ↦ ⟨?_⟩⟩
  · ext x
    have hmem : (u†) (u x) ∈ u.kerᗮ :=
      u.orthogonal_ker ▸ (u†).range.le_topologicalClosure (LinearMap.mem_range_self _ _)
    refine (Submodule.eq_starProjection_of_mem_orthogonal hmem
      (Submodule.le_orthogonal_orthogonal _ ?_)).symm
    simp [hu.apply_adjoint_apply_apply]
  · ext x
    simpa [h] using u.apply_starProjection_orthogonal_ker x

/-- For a partial isometry `u`, `u† u` is the orthogonal projection onto the initial space
`(ker u)ᗮ`. -/
theorem IsPartialIsometry.adjoint_comp_self_eq_starProjection (hu : u.IsPartialIsometry) :
    u† ∘L u = u.kerᗮ.starProjection :=
  isPartialIsometry_iff_adjoint_comp_self_eq_starProjection.mp hu

/-- The initial projection `u† u` of a partial isometry is a star projection. -/
theorem IsPartialIsometry.isStarProjection_adjoint_comp_self (hu : u.IsPartialIsometry) :
    IsStarProjection (u† ∘L u) := by
  rw [hu.adjoint_comp_self_eq_starProjection]
  exact isStarProjection_starProjection

/-- The adjoint of a partial isometry is a partial isometry. -/
theorem IsPartialIsometry.adjoint (hu : u.IsPartialIsometry) : (u†).IsPartialIsometry :=
  ⟨by simpa [adjoint_comp, comp_assoc] using
    congr(ContinuousLinearMap.adjoint $(hu.comp_adjoint_comp_self))⟩

/-- The adjoint of a bounded operator is a partial isometry if and only if the operator is. -/
@[simp]
theorem isPartialIsometry_adjoint_iff : (u†).IsPartialIsometry ↔ u.IsPartialIsometry :=
  ⟨fun h ↦ by simpa using h.adjoint, .adjoint⟩

/-- For a partial isometry `u`, `u u†` is the orthogonal projection onto the final space
`(ker u†)ᗮ`, the closure of the range of `u`. -/
theorem IsPartialIsometry.comp_adjoint_eq_starProjection (hu : u.IsPartialIsometry) :
    u ∘L u† = (u†).kerᗮ.starProjection := by
  simpa using hu.adjoint.adjoint_comp_self_eq_starProjection

/-- The final projection `u u†` of a partial isometry is a star projection. -/
theorem IsPartialIsometry.isStarProjection_comp_adjoint (hu : u.IsPartialIsometry) :
    IsStarProjection (u ∘L u†) := by
  simpa using hu.adjoint.isStarProjection_adjoint_comp_self

/-- **Geometric characterization of partial isometries.** A bounded operator is a partial
isometry if and only if it preserves norms on the orthogonal complement of its kernel. -/
theorem isPartialIsometry_iff_norm_map :
    u.IsPartialIsometry ↔ ∀ x ∈ u.kerᗮ, ‖u x‖ = ‖x‖ := by
  rw [isPartialIsometry_iff_adjoint_comp_self_eq_starProjection]
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ?_⟩
  · have := congr(re ⟪$h x, x⟫_𝕜)
    simp only [comp_apply, adjoint_inner_left, inner_self_eq_norm_sq,
      Submodule.starProjection_eq_self_iff.mpr hx] at this
    simpa using this
  -- By polarization, `u` preserves inner products on `(ker u)ᗮ`.
  have hinner : ∀ x ∈ u.kerᗮ, ∀ y ∈ u.kerᗮ, ⟪u x, u y⟫_𝕜 = ⟪x, y⟫_𝕜 := fun x hx y hy ↦
    (LinearMap.norm_map_iff_inner_map_map (u.toLinearMap ∘ₗ u.kerᗮ.subtype)).mp
      (fun z ↦ h z z.2) ⟨x, hx⟩ ⟨y, hy⟩
  ext x
  refine ext_inner_right 𝕜 fun y ↦ ?_
  have hPx := u.kerᗮ.starProjection_apply_mem x
  calc ⟪(u† ∘L u) x, y⟫_𝕜
      = ⟪u (u.kerᗮ.starProjection x), u (u.kerᗮ.starProjection y)⟫_𝕜 := by
        rw [comp_apply, adjoint_inner_left, u.apply_starProjection_orthogonal_ker,
          u.apply_starProjection_orthogonal_ker]
    _ = ⟪u.kerᗮ.starProjection x, u.kerᗮ.starProjection y⟫_𝕜 :=
        hinner _ hPx _ (u.kerᗮ.starProjection_apply_mem y)
    _ = ⟪u.kerᗮ.starProjection x, y⟫_𝕜 := by
      rw [← Submodule.inner_starProjection_left_eq_right,
        Submodule.starProjection_eq_self_iff.mpr hPx]

/-- A bounded operator that preserves all norms is a partial isometry. -/
theorem IsPartialIsometry.of_norm_map (h : ∀ x, ‖u x‖ = ‖x‖) : u.IsPartialIsometry :=
  ⟨by rw [(norm_map_iff_adjoint_comp_self u).mp h, one_def, comp_id]⟩

variable (𝕜 E F) in
/-- The zero operator is a partial isometry. -/
@[simp]
theorem isPartialIsometry_zero : (0 : E →L[𝕜] F).IsPartialIsometry :=
  ⟨by simp⟩

/-- On endomorphisms, the rectangular partial-isometry predicate agrees with the star-monoid
predicate `IsPartialIsometry`. -/
theorem isPartialIsometry_iff_starMul {u : E →L[𝕜] E} :
    u.IsPartialIsometry ↔ _root_.IsPartialIsometry u := by
  rw [isPartialIsometry_iff, _root_.isPartialIsometry_iff, star_eq_adjoint, mul_def, mul_def,
    comp_assoc]

end ContinuousLinearMap

/-- An orthogonal projection is a partial isometry, with initial and final space its range. -/
theorem Submodule.isPartialIsometry_starProjection [CompleteSpace E] (K : Submodule 𝕜 E)
    [K.HasOrthogonalProjection] : K.starProjection.IsPartialIsometry :=
  ContinuousLinearMap.isPartialIsometry_iff_starMul.mpr
    isStarProjection_starProjection.isPartialIsometry

/-- A linear isometry between complete inner product spaces is a partial isometry. -/
theorem LinearIsometry.isPartialIsometry_toContinuousLinearMap [CompleteSpace E] [CompleteSpace F]
    (f : E →ₗᵢ[𝕜] F) : f.toContinuousLinearMap.IsPartialIsometry :=
  .of_norm_map f.norm_map

namespace LinearMap

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- A linear map `u : E →ₗ[𝕜] F` between finite-dimensional inner product spaces is a *partial
isometry* when `u u† u = u`. Equivalently (`isPartialIsometry_iff_norm_map`), `u` preserves norms
on the orthogonal complement of its kernel. -/
@[mk_iff]
structure IsPartialIsometry (u : E →ₗ[𝕜] F) : Prop where
  /-- The defining identity `u u† u = u` of a partial isometry. -/
  comp_adjoint_comp_self : u ∘ₗ u.adjoint ∘ₗ u = u

variable {u : E →ₗ[𝕜] F}

/-- A finite-dimensional linear map is a partial isometry if and only if the corresponding
bounded operator is. -/
theorem isPartialIsometry_toContinuousLinearMap_iff :
    have := FiniteDimensional.complete 𝕜 E
    have := FiniteDimensional.complete 𝕜 F
    (toContinuousLinearMap u).IsPartialIsometry ↔ u.IsPartialIsometry := by
  intro _ _
  simp only [ContinuousLinearMap.isPartialIsometry_iff, isPartialIsometry_iff,
    ← adjoint_toContinuousLinearMap, ← ContinuousLinearMap.coe_inj,
    ContinuousLinearMap.toLinearMap_comp, coe_toContinuousLinearMap]

/-- **Geometric characterization of partial isometries.** A linear map between finite-dimensional
inner product spaces is a partial isometry if and only if it preserves norms on the orthogonal
complement of its kernel. -/
theorem isPartialIsometry_iff_norm_map :
    u.IsPartialIsometry ↔ ∀ x ∈ (ker u)ᗮ, ‖u x‖ = ‖x‖ := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simpa using (isPartialIsometry_toContinuousLinearMap_iff (u := u)).symm.trans
    ContinuousLinearMap.isPartialIsometry_iff_norm_map

/-- For a partial isometry `u`, `u† u` is the orthogonal projection onto the initial space
`(ker u)ᗮ`. -/
theorem IsPartialIsometry.adjoint_comp_self_eq_starProjection (hu : u.IsPartialIsometry) :
    u.adjoint ∘ₗ u = (ker u)ᗮ.starProjection := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  have h := (isPartialIsometry_toContinuousLinearMap_iff.mpr hu)
    |>.adjoint_comp_self_eq_starProjection
  rw [← adjoint_toContinuousLinearMap] at h
  exact congr(($h : E →ₗ[𝕜] E))

/-- The initial projection `u† u` of a partial isometry is a symmetric projection. -/
theorem IsPartialIsometry.isSymmetricProjection_adjoint_comp_self (hu : u.IsPartialIsometry) :
    (u.adjoint ∘ₗ u).IsSymmetricProjection := by
  rw [hu.adjoint_comp_self_eq_starProjection]
  exact Submodule.isSymmetricProjection_starProjection _

/-- The adjoint of a partial isometry is a partial isometry. -/
theorem IsPartialIsometry.adjoint (hu : u.IsPartialIsometry) : u.adjoint.IsPartialIsometry :=
  ⟨by simpa [adjoint_comp, comp_assoc] using
    congr(LinearMap.adjoint $(hu.comp_adjoint_comp_self))⟩

/-- The adjoint of a linear map is a partial isometry if and only if the map is. -/
@[simp]
theorem isPartialIsometry_adjoint_iff : u.adjoint.IsPartialIsometry ↔ u.IsPartialIsometry :=
  ⟨fun h ↦ by simpa using h.adjoint, .adjoint⟩

/-- For a partial isometry `u`, `u u†` is the orthogonal projection onto the final space
`(ker u†)ᗮ = range u`. -/
theorem IsPartialIsometry.comp_adjoint_eq_starProjection (hu : u.IsPartialIsometry) :
    u ∘ₗ u.adjoint = (ker u.adjoint)ᗮ.starProjection := by
  simpa using hu.adjoint.adjoint_comp_self_eq_starProjection

/-- The final projection `u u†` of a partial isometry is a symmetric projection. -/
theorem IsPartialIsometry.isSymmetricProjection_comp_adjoint (hu : u.IsPartialIsometry) :
    (u ∘ₗ u.adjoint).IsSymmetricProjection := by
  simpa using hu.adjoint.isSymmetricProjection_adjoint_comp_self

/-- A linear map that preserves all norms is a partial isometry. -/
theorem IsPartialIsometry.of_norm_map (h : ∀ x, ‖u x‖ = ‖x‖) : u.IsPartialIsometry :=
  isPartialIsometry_iff_norm_map.mpr fun x _ ↦ h x

variable (𝕜 E F) in
/-- The zero map is a partial isometry. -/
@[simp]
theorem isPartialIsometry_zero : (0 : E →ₗ[𝕜] F).IsPartialIsometry :=
  ⟨by simp⟩

/-- On endomorphisms, the rectangular partial-isometry predicate agrees with the star-monoid
predicate `IsPartialIsometry`. -/
theorem isPartialIsometry_iff_starMul {u : E →ₗ[𝕜] E} :
    u.IsPartialIsometry ↔ _root_.IsPartialIsometry u := by
  rw [isPartialIsometry_iff, _root_.isPartialIsometry_iff, star_eq_adjoint,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp, comp_assoc]

end LinearMap

/-- A linear isometry between finite-dimensional inner product spaces is a partial isometry. -/
theorem LinearIsometry.isPartialIsometry_toLinearMap [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (f : E →ₗᵢ[𝕜] F) : f.toLinearMap.IsPartialIsometry :=
  .of_norm_map f.norm_map
