/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.BasisSpan
public import TauCeti.Analysis.InnerProductSpace.Projection.PrincipalAngle
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Schatten
public import Mathlib.Data.Finsupp.Order

/-!
# Directed Frobenius sine between subspaces

For subspaces `U` and `V` of a finite-dimensional inner product space, the Frobenius sine
`U.sinThetaFrobenius V` is the Frobenius seminorm of the directed sine map `P_{Vᗮ} P_U`.
It packages the quantity used in Frobenius subspace perturbation inequalities without
selecting bases. The quantity is not generally symmetric and vanishes exactly when
`U ≤ V`, so it is not a distance on arbitrary subspaces.

The Frobenius sine is the square root of the sum of the squared principal sines.
The operator norm of the directed sine map sees only the largest principal sine;
the Frobenius quantity accounts for all of them.

For a finite orthonormal family spanning `U`, the squared Frobenius sine from
`U` to `V` equals the sum of squared norms of projections onto `Vᗮ`.

## Main results

* `OrthonormalBasis.sq_sinThetaFrobenius_spanIndices_eq_sum_projection`: the
  squared Frobenius sine from a selected basis block to an arbitrary subspace.
* `Submodule.sq_sinThetaFrobenius_eq_sum_projection_of_orthonormal`: the squared
  Frobenius sine expressed through any orthonormal spanning family.

## Source

* AIQ-Kitware DKPS formalization (Kitware, Inc.; Apache-2.0):
  https://github.com/AIQ-Kitware/aiq-dkps-formalization
* Source file: `ForTauCeti/Analysis/InnerProductSpace/SinTheta/Frobenius.lean`.
-/

public section

namespace Submodule

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The Frobenius seminorm of the directed sine map between two subspaces. -/
noncomputable def sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] : ℝ :=
  TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E
    (U.sinThetaMap V : E →ₗ[𝕜] E)

/-- The Frobenius sine is the Frobenius seminorm of the directed sine map `P_{Vᗮ} P_U`. -/
theorem sinThetaFrobenius_def (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.sinThetaFrobenius V =
      TauCeti.UnitarilyInvariantSeminorm.frobenius 𝕜 E E
        (U.sinThetaMap V : E →ₗ[𝕜] E) :=
  (rfl)

/-- The Frobenius sine is nonnegative. -/
theorem sinThetaFrobenius_nonneg (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    0 ≤ U.sinThetaFrobenius V := by
  rw [sinThetaFrobenius_def]
  exact apply_nonneg _ _

/-- The Frobenius sine is the Euclidean norm of the principal-sine list. -/
theorem sinThetaFrobenius_eq_sqrt_sum_sq_principalSines (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.sinThetaFrobenius V = √((U.principalSines V).sum fun _ s => s ^ 2) := by
  rw [sinThetaFrobenius_def,
    TauCeti.UnitarilyInvariantSeminorm.frobenius_apply_eq_sqrt_sum_sq_singularValues,
    ← principalSines_def]

/-- The squared Frobenius sine equals the sum of the squared principal sines. -/
theorem sq_sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    (U.sinThetaFrobenius V) ^ 2 = (U.principalSines V).sum fun _ s => s ^ 2 := by
  have hs : 0 ≤ (U.principalSines V).sum (fun _ s => s ^ 2) := by
    exact Finsupp.sum_nonneg (fun _ _ => sq_nonneg _)
  rw [sinThetaFrobenius_eq_sqrt_sum_sq_principalSines, Real.sq_sqrt hs]

/-- The Frobenius sine is symmetric for subspaces of equal finite dimension. -/
theorem sinThetaFrobenius_comm (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection]
    (h : Module.finrank 𝕜 U = Module.finrank 𝕜 V) :
    U.sinThetaFrobenius V = V.sinThetaFrobenius U := by
  rw [U.sinThetaFrobenius_eq_sqrt_sum_sq_principalSines V,
    V.sinThetaFrobenius_eq_sqrt_sum_sq_principalSines U,
    U.principalSines_comm V h]

/-- The directed projection gap is bounded by the Frobenius sine. -/
theorem directedProjectionGap_le_sinThetaFrobenius (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.directedProjectionGap V ≤ U.sinThetaFrobenius V := by
  have h := TauCeti.UnitarilyInvariantSeminorm.opNorm_apply_le_schatten_apply 2
    (U.sinThetaMap V : E →ₗ[𝕜] E)
  rw [TauCeti.UnitarilyInvariantSeminorm.opNorm_apply,
    TauCeti.UnitarilyInvariantSeminorm.schatten_two] at h
  have hcont : LinearMap.toContinuousLinearMap
      (U.sinThetaMap V : E →ₗ[𝕜] E) = U.sinThetaMap V :=
    (LinearMap.toContinuousLinearMap_eq_iff_eq_toLinearMap _ _).2 rfl
  simpa only [hcont, U.norm_sinThetaMap V, sinThetaFrobenius_def] using h

/-- The Frobenius sine vanishes precisely when the first subspace is contained in the second. -/
@[simp]
theorem sinThetaFrobenius_eq_zero_iff (U V : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    U.sinThetaFrobenius V = 0 ↔ U ≤ V := by
  constructor
  · intro h
    exact (U.directedProjectionGap_eq_zero_iff V).mp <|
      le_antisymm (h ▸ U.directedProjectionGap_le_sinThetaFrobenius V)
        (U.directedProjectionGap_nonneg V)
  · intro h
    rw [sinThetaFrobenius_def, (U.sinThetaMap_eq_zero_iff V).mpr h]
    simp

/-- The Frobenius sine from a subspace to itself is zero. -/
@[simp]
theorem sinThetaFrobenius_self (U : Submodule 𝕜 E)
    [U.HasOrthogonalProjection] : U.sinThetaFrobenius U = 0 :=
  (U.sinThetaFrobenius_eq_zero_iff U).mpr le_rfl

end Submodule

/-! ### Projection formula for the squared Frobenius sine -/

open scoped InnerProductSpace

namespace OrthonormalBasis

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι]

/-- For an arbitrary target subspace `U`, the squared Frobenius sine from a
coordinate block of an orthonormal basis `b` to `U` is the total squared
orthogonal projection of the selected vectors onto `Uᗮ`. -/
theorem sq_sinThetaFrobenius_spanIndices_eq_sum_projection (b : OrthonormalBasis ι 𝕜 E)
    (s : Finset ι) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    letI : FiniteDimensional 𝕜 E := Module.Finite.of_basis b.toBasis
    (b.spanIndices (↑s : Set ι)).sinThetaFrobenius U ^ 2 =
      ∑ j ∈ s, ‖Uᗮ.starProjection (b j)‖ ^ 2 := by
  classical
  have : FiniteDimensional 𝕜 E := Module.Finite.of_basis b.toBasis
  set V := b.spanIndices (↑s : Set ι) with hV
  have hb (j : ι) :
      (V.sinThetaMap U) (b j) =
        if j ∈ s then Uᗮ.starProjection (b j) else 0 := by
    by_cases hj : j ∈ s
    · simp [hj, Submodule.sinThetaMap_apply,
        V.starProjection_eq_self_iff.mpr (b.mem_spanIndices_of_mem hj)]
    · have horth : b j ∈ Vᗮ := by
        rw [b.orthogonal_spanIndices]
        exact b.mem_spanIndices_of_mem (by simpa using hj)
      simp [hj, Submodule.sinThetaMap_apply,
        V.starProjection_apply_eq_zero_iff.mpr horth]
  calc
    V.sinThetaFrobenius U ^ 2 =
        ∑ j, ‖(V.sinThetaMap U) (b j)‖ ^ 2 := by
          rw [Submodule.sinThetaFrobenius_def]
          exact TauCeti.UnitarilyInvariantSeminorm.sq_frobenius_apply b _
    _ = ∑ j ∈ s, ‖(V.sinThetaMap U) (b j)‖ ^ 2 := by
          exact (Finset.sum_subset (Finset.subset_univ s)
            (by
              intro j _ hj
              rw [hb j]
              simp [hj])).symm
    _ = ∑ j ∈ s, ‖Uᗮ.starProjection (b j)‖ ^ 2 := by
          exact Finset.sum_congr rfl fun j hj ↦ by
            rw [hb j]
            simp [hj]

end OrthonormalBasis

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- For any finite orthonormal family spanning `V`, the squared Frobenius sine
from `V` to `U` is the sum of the squared orthogonal projections of its vectors
onto `Uᗮ`. In particular, the value does not depend on the chosen family. -/
theorem sq_sinThetaFrobenius_eq_sum_projection_of_orthonormal
    (V U : Submodule 𝕜 E) [V.HasOrthogonalProjection] [U.HasOrthogonalProjection]
    {κ : Type*} [Fintype κ] {v : κ → E} (hv : Orthonormal 𝕜 v)
    (hV : Submodule.span 𝕜 (Set.range v) = V) :
    V.sinThetaFrobenius U ^ 2 = ∑ j, ‖Uᗮ.starProjection (v j)‖ ^ 2 := by
  classical
  have hvinj : Function.Injective v := hv.linearIndependent.injective
  have hvRange : Orthonormal 𝕜 ((↑) : Set.range v → E) :=
    (orthonormal_subtype_range hvinj).mpr hv
  obtain ⟨t, b, hsubset, hb⟩ := hvRange.exists_orthonormalBasis_extension
  let e : κ ↪ t :=
    ⟨fun j => ⟨v j, hsubset (Set.mem_range_self j)⟩,
      fun i j hij => hvinj (congrArg Subtype.val hij)⟩
  set s : Finset t := Finset.univ.image e with hs
  have hbe (j : κ) : b (e j) = v j := by
    calc
      b (e j) = (e j : E) := congrFun hb (e j)
      _ = v j := rfl
  have hset : b '' (↑s : Set t) = Set.range v := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hi)
      exact ⟨j, (hbe j).symm⟩
    · rintro ⟨j, rfl⟩
      refine ⟨e j, ?_, hbe j⟩
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨j, Finset.mem_univ _, rfl⟩)
  have hsV : b.spanIndices (↑s : Set t) = V := by
    rw [b.spanIndices_eq_span, hset, hV]
  have hproj := b.sq_sinThetaFrobenius_spanIndices_eq_sum_projection s U
  rw [hsV] at hproj
  calc
    V.sinThetaFrobenius U ^ 2 =
        ∑ i ∈ s, ‖Uᗮ.starProjection (b i)‖ ^ 2 := hproj
    _ = ∑ j : κ, ‖Uᗮ.starProjection (v j)‖ ^ 2 := by
      rw [hs, Finset.sum_image (fun i _ j _ hij => e.injective hij)]
      exact Finset.sum_congr rfl fun j _ => by rw [hbe j]

end Submodule
