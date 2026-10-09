/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.PartialIsometry
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Partial isometries between Hilbert spaces

A map `u : E → F` between Hilbert spaces is a *partial isometry* when `u u† u = u`. Unlike the
star-monoid predicate `TauCeti.IsPartialIsometry`, this makes sense for maps between two different
spaces, as needed for the polar factor of a rectangular operator. This file develops the predicate
for bounded operators between complete inner product spaces and for linear maps between
finite-dimensional ones, and proves its geometric characterization: `u` is a partial isometry
exactly when it preserves norms on its initial space `(ker u)ᗮ`. Equivalently, `u† u` is the
orthogonal projection onto `(ker u)ᗮ`, or merely some star projection.

## Main definitions

* `ContinuousLinearMap.IsPartialIsometry u`: the bounded operator `u` satisfies `u u† u = u`.
* `LinearMap.IsPartialIsometry u`: the finite-dimensional linear map `u` satisfies `u u† u = u`.

## Main statements

* `ContinuousLinearMap.isPartialIsometry_iff_norm_map`,
  `LinearMap.isPartialIsometry_iff_norm_map`: a map is a partial isometry iff it preserves norms on
  the orthogonal complement of its kernel.
* `ContinuousLinearMap.IsPartialIsometry.adjoint_comp_self_eq_starProjection`: the initial
  projection `u† u` of a bounded partial isometry is the orthogonal projection onto `(ker u)ᗮ`.
* `ContinuousLinearMap.isPartialIsometry_iff_isStarProjection_adjoint_comp_self`,
  `LinearMap.isPartialIsometry_iff_isStarProjection_adjoint_comp_self`: a map is a partial isometry
  iff `u† u` is a star projection.
* `ContinuousLinearMap.isPartialIsometry_adjoint_iff`, `LinearMap.isPartialIsometry_adjoint_iff`:
  the adjoint of a partial isometry is a partial isometry.
* `ContinuousLinearMap.isPartialIsometry_iff_starMul`, `LinearMap.isPartialIsometry_iff_starMul`:
  on endomorphisms the rectangular predicate agrees with the star-monoid predicate.
* `LinearIsometry.isPartialIsometry_toContinuousLinearMap`,
  `LinearIsometry.isPartialIsometry_toLinearMap`: linear isometries are partial isometries.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer (1990), the treatment of
  partial isometries and the polar decomposition.
-/

public section

open scoped InnerProduct InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace ContinuousLinearMap

section Complete

variable [CompleteSpace E] {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- A bounded operator does not see the component of a vector in its kernel: it agrees with its
composition with the orthogonal projection onto the orthogonal complement of its kernel. -/
@[simp]
theorem apply_starProjection_orthogonal_ker (u : E →L[𝕜] G) (x : E) :
    u (u.kerᗮ.starProjection x) = u x := by
  have hx : x - u.kerᗮ.starProjection x ∈ u.ker :=
    (Submodule.orthogonal_orthogonal u.ker).le (Submodule.sub_starProjection_mem_orthogonal x)
  rw [LinearMap.mem_ker, coe_coe, map_sub, sub_eq_zero] at hx
  exact hx.symm

/-- Composing a bounded operator with the orthogonal projection onto the orthogonal complement of
its kernel does not change it. -/
@[simp]
theorem comp_starProjection_orthogonal_ker (u : E →L[𝕜] G) :
    u ∘L u.kerᗮ.starProjection = u :=
  ext (apply_starProjection_orthogonal_ker u)

variable [CompleteSpace F] {u : E →L[𝕜] F}

/-- The adjoint of a bounded operator takes values in the orthogonal complement of its kernel. -/
theorem adjoint_apply_mem_orthogonal_ker (u : E →L[𝕜] F) (y : F) : (u†) y ∈ u.kerᗮ := by
  rw [orthogonal_ker]
  exact Submodule.le_topologicalClosure _ ⟨y, rfl⟩

/-- A bounded operator `u : E →L[𝕜] F` is a **partial isometry** when `u u† u = u`. -/
def IsPartialIsometry (u : E →L[𝕜] F) : Prop :=
  u ∘L u† ∘L u = u

/-- Unfold the definition of a bounded partial isometry. -/
theorem isPartialIsometry_iff : u.IsPartialIsometry ↔ u ∘L u† ∘L u = u :=
  Iff.rfl

/-- The defining equation `u u† u = u` of a bounded partial isometry. -/
theorem IsPartialIsometry.comp_adjoint_comp (hu : u.IsPartialIsometry) : u ∘L u† ∘L u = u :=
  hu

/-- The defining equation `u u† u = u` of a bounded partial isometry, applied to a vector. -/
@[simp]
theorem IsPartialIsometry.apply_adjoint_apply (hu : u.IsPartialIsometry) (x : E) :
    u ((u†) (u x)) = u x :=
  congr($hu x)

/-- A bounded partial isometry is a partial isometry in the star monoid of endomorphisms. -/
theorem isPartialIsometry_iff_starMul {u : E →L[𝕜] E} :
    u.IsPartialIsometry ↔ TauCeti.IsPartialIsometry u := by
  rw [isPartialIsometry_iff, TauCeti.isPartialIsometry_iff, star_eq_adjoint, mul_def, mul_def,
    comp_assoc]

/-- The adjoint of a bounded partial isometry is a partial isometry. -/
theorem IsPartialIsometry.adjoint (hu : u.IsPartialIsometry) : (u†).IsPartialIsometry := by
  rw [isPartialIsometry_iff, adjoint_adjoint, ← comp_assoc]
  simpa only [adjoint_comp, adjoint_adjoint, comp_assoc] using
    congrArg ContinuousLinearMap.adjoint hu.comp_adjoint_comp

/-- A bounded operator is a partial isometry iff its adjoint is. -/
@[simp]
theorem isPartialIsometry_adjoint_iff : (u†).IsPartialIsometry ↔ u.IsPartialIsometry :=
  ⟨fun h => by simpa only [adjoint_adjoint] using h.adjoint, IsPartialIsometry.adjoint⟩

/-- A bounded operator is a partial isometry iff `u† u` restricts to the identity on the initial
space `(ker u)ᗮ`. -/
theorem isPartialIsometry_iff_adjoint_apply_apply :
    u.IsPartialIsometry ↔ ∀ x ∈ u.kerᗮ, (u†) (u x) = x := by
  refine ⟨fun hu x hx => ?_, fun h => ?_⟩
  · -- `(u†) (u x) - x` lies both in `(ker u)ᗮ` and in `ker u`.
    have hmem : (u†) (u x) - x ∈ u.kerᗮ :=
      sub_mem (adjoint_apply_mem_orthogonal_ker u _) hx
    have hker : (u†) (u x) - x ∈ u.ker := by
      rw [LinearMap.mem_ker, coe_coe, map_sub, hu.apply_adjoint_apply, sub_self]
    exact sub_eq_zero.mp <| (Submodule.mem_bot 𝕜).mp <|
      u.ker.inf_orthogonal_eq_bot ▸ ⟨hker, hmem⟩
  · ext x
    rw [comp_apply, comp_apply, ← u.apply_starProjection_orthogonal_ker x,
      h _ (Submodule.starProjection_apply_mem _ x)]

/-- A bounded partial isometry `u` satisfies `u† u x = x` on its initial space `(ker u)ᗮ`. -/
theorem IsPartialIsometry.adjoint_apply_apply (hu : u.IsPartialIsometry) {x : E}
    (hx : x ∈ u.kerᗮ) : (u†) (u x) = x :=
  isPartialIsometry_iff_adjoint_apply_apply.mp hu x hx

/-- The initial projection `u† u` of a bounded partial isometry is the orthogonal projection onto
its initial space `(ker u)ᗮ`. -/
theorem IsPartialIsometry.adjoint_comp_self_eq_starProjection (hu : u.IsPartialIsometry) :
    u† ∘L u = u.kerᗮ.starProjection := by
  ext x
  rw [comp_apply, ← u.apply_starProjection_orthogonal_ker x,
    hu.adjoint_apply_apply (Submodule.starProjection_apply_mem _ x)]

/-- A bounded operator is a partial isometry iff `u† u` is a star projection. -/
theorem isPartialIsometry_iff_isStarProjection_adjoint_comp_self :
    u.IsPartialIsometry ↔ IsStarProjection (u† ∘L u) := by
  refine ⟨fun hu => hu.adjoint_comp_self_eq_starProjection ▸ isStarProjection_starProjection,
    fun hp => ?_⟩
  -- For every `x`, the vector `y = u† u x - x` satisfies `u† u y = 0`, hence `u y = 0`.
  ext x
  set y := (u†) (u x) - x with hy
  have hPy : (u†) (u y) = 0 := by
    have := congr($hp.isIdempotentElem.eq x)
    simp only [mul_def, comp_apply] at this
    rw [hy, map_sub, map_sub, this, sub_self]
  have huy : u y = 0 := by
    rw [← inner_self_eq_zero (𝕜 := 𝕜), ← adjoint_inner_right, hPy, inner_zero_right]
  rw [hy, map_sub, sub_eq_zero] at huy
  simpa only [comp_apply] using huy

/-- The initial projection `u† u` of a bounded partial isometry is a star projection. -/
theorem IsPartialIsometry.isStarProjection_adjoint_comp_self (hu : u.IsPartialIsometry) :
    IsStarProjection (u† ∘L u) :=
  isPartialIsometry_iff_isStarProjection_adjoint_comp_self.mp hu

/-- The final projection `u u†` of a bounded partial isometry is a star projection. -/
theorem IsPartialIsometry.isStarProjection_comp_adjoint (hu : u.IsPartialIsometry) :
    IsStarProjection (u ∘L u†) := by
  simpa only [adjoint_adjoint] using hu.adjoint.isStarProjection_adjoint_comp_self

/-- **Geometric characterization of partial isometries.** A bounded operator is a partial
isometry iff it preserves norms on the orthogonal complement of its kernel. -/
theorem isPartialIsometry_iff_norm_map :
    u.IsPartialIsometry ↔ ∀ x ∈ u.kerᗮ, ‖u x‖ = ‖x‖ := by
  rw [isPartialIsometry_iff_adjoint_apply_apply]
  refine ⟨fun h x hx => ?_, fun h x hx => ?_⟩
  · rw [norm_eq_sqrt_re_inner (𝕜 := 𝕜), norm_eq_sqrt_re_inner (𝕜 := 𝕜) x,
      ← adjoint_inner_right, h x hx]
  · -- Polarization on `(ker u)ᗮ` shows that `u† u x - x` is orthogonal to `(ker u)ᗮ`.
    have hinner : ∀ y ∈ u.kerᗮ, ⟪u y, u x⟫_𝕜 = ⟪y, x⟫_𝕜 := fun y hy =>
      (LinearMap.norm_map_iff_inner_map_map (u ∘L u.kerᗮ.subtypeL)).mp
        (fun z => h z z.2) ⟨y, hy⟩ ⟨x, hx⟩
    have hperp : (u†) (u x) - x ∈ u.kerᗮᗮ := fun y hy => by
      rw [inner_sub_right, adjoint_inner_right, hinner y hy, sub_self]
    exact sub_eq_zero.mp <| (Submodule.mem_bot 𝕜).mp <|
      u.kerᗮ.inf_orthogonal_eq_bot ▸
        ⟨sub_mem (adjoint_apply_mem_orthogonal_ker u _) hx, hperp⟩

/-- A bounded partial isometry preserves norms on its initial space `(ker u)ᗮ`. -/
theorem IsPartialIsometry.norm_map (hu : u.IsPartialIsometry) {x : E} (hx : x ∈ u.kerᗮ) :
    ‖u x‖ = ‖x‖ :=
  isPartialIsometry_iff_norm_map.mp hu x hx

end Complete

end ContinuousLinearMap

/-- A linear isometry between complete inner product spaces is a bounded partial isometry. -/
theorem LinearIsometry.isPartialIsometry_toContinuousLinearMap [CompleteSpace E] [CompleteSpace F]
    (f : E →ₗᵢ[𝕜] F) : f.toContinuousLinearMap.IsPartialIsometry := by
  rw [ContinuousLinearMap.isPartialIsometry_iff, f.adjoint_comp_self,
    ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]

namespace LinearMap

section FiniteDimensional

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] {u : E →ₗ[𝕜] F}

/-- A linear map `u : E →ₗ[𝕜] F` between finite-dimensional inner product spaces is a
**partial isometry** when `u u† u = u`. -/
def IsPartialIsometry (u : E →ₗ[𝕜] F) : Prop :=
  u ∘ₗ u.adjoint ∘ₗ u = u

/-- Unfold the definition of a finite-dimensional partial isometry. -/
theorem isPartialIsometry_iff : u.IsPartialIsometry ↔ u ∘ₗ u.adjoint ∘ₗ u = u :=
  Iff.rfl

/-- The defining equation `u u† u = u` of a finite-dimensional partial isometry. -/
theorem IsPartialIsometry.comp_adjoint_comp (hu : u.IsPartialIsometry) :
    u ∘ₗ u.adjoint ∘ₗ u = u :=
  hu

/-- A finite-dimensional linear map is a partial isometry iff the corresponding bounded operator
is one. -/
theorem isPartialIsometry_toContinuousLinearMap_iff :
    have := FiniteDimensional.complete 𝕜 E
    have := FiniteDimensional.complete 𝕜 F
    (toContinuousLinearMap u).IsPartialIsometry ↔ u.IsPartialIsometry := by
  intro _ _
  rw [ContinuousLinearMap.isPartialIsometry_iff, isPartialIsometry_iff,
    ← ContinuousLinearMap.coe_inj]
  simp [adjoint_eq_toCLM_adjoint]

/-- A finite-dimensional partial isometry is a partial isometry in the star monoid of
endomorphisms. -/
theorem isPartialIsometry_iff_starMul {u : E →ₗ[𝕜] E} :
    u.IsPartialIsometry ↔ TauCeti.IsPartialIsometry u := by
  rw [isPartialIsometry_iff, TauCeti.isPartialIsometry_iff, star_eq_adjoint,
    Module.End.mul_eq_comp, Module.End.mul_eq_comp, comp_assoc]

/-- The adjoint of a finite-dimensional partial isometry is a partial isometry. -/
theorem IsPartialIsometry.adjoint (hu : u.IsPartialIsometry) : u.adjoint.IsPartialIsometry := by
  rw [isPartialIsometry_iff, adjoint_adjoint, ← comp_assoc]
  simpa only [adjoint_comp, adjoint_adjoint, comp_assoc] using
    congrArg LinearMap.adjoint hu.comp_adjoint_comp

/-- A finite-dimensional linear map is a partial isometry iff its adjoint is. -/
@[simp]
theorem isPartialIsometry_adjoint_iff : u.adjoint.IsPartialIsometry ↔ u.IsPartialIsometry :=
  ⟨fun h => by simpa only [adjoint_adjoint] using h.adjoint, IsPartialIsometry.adjoint⟩

/-- A finite-dimensional linear map is a partial isometry iff `u† u` is a star projection. -/
theorem isPartialIsometry_iff_isStarProjection_adjoint_comp_self :
    u.IsPartialIsometry ↔ IsStarProjection (u.adjoint ∘ₗ u) := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  have h : toContinuousLinearMap (u.adjoint ∘ₗ u) =
      (toContinuousLinearMap u)† ∘L toContinuousLinearMap u := by
    rw [← ContinuousLinearMap.coe_inj]
    simp [adjoint_eq_toCLM_adjoint]
  simp only [← isPartialIsometry_toContinuousLinearMap_iff,
    ContinuousLinearMap.isPartialIsometry_iff_isStarProjection_adjoint_comp_self, h,
    ← isStarProjection_toContinuousLinearMap_iff]

/-- The initial projection `u† u` of a finite-dimensional partial isometry is a star
projection. -/
theorem IsPartialIsometry.isStarProjection_adjoint_comp_self (hu : u.IsPartialIsometry) :
    IsStarProjection (u.adjoint ∘ₗ u) :=
  isPartialIsometry_iff_isStarProjection_adjoint_comp_self.mp hu

/-- **Geometric characterization of partial isometries.** A linear map between
finite-dimensional inner product spaces is a partial isometry iff it preserves norms on the
orthogonal complement of its kernel. -/
theorem isPartialIsometry_iff_norm_map :
    u.IsPartialIsometry ↔ ∀ x ∈ u.kerᗮ, ‖u x‖ = ‖x‖ := by
  have := FiniteDimensional.complete 𝕜 E
  have := FiniteDimensional.complete 𝕜 F
  simp [← isPartialIsometry_toContinuousLinearMap_iff,
    ContinuousLinearMap.isPartialIsometry_iff_norm_map]

end FiniteDimensional

end LinearMap

/-- A linear isometry between finite-dimensional inner product spaces is a partial isometry. -/
theorem LinearIsometry.isPartialIsometry_toLinearMap [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] (f : E →ₗᵢ[𝕜] F) : f.toLinearMap.IsPartialIsometry := by
  rw [LinearMap.isPartialIsometry_iff, f.adjoint_comp_self', LinearMap.comp_id]
