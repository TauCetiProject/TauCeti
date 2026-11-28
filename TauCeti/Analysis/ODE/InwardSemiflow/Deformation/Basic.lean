/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.InwardSemiflow.Basic

/-!
# Interior entry and persistence of quadratic inward semiflow deformations

Proves `MapsTo` properties on `U ∩ C` and `U ∩ interior C` for the quadratic time-reparametrized
inward semiflow deformation `x ↦ TauCeti.forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x`.
Smoothness of this deformation is proved in
`TauCeti.Analysis.ODE.InwardSemiflow.Deformation.Smooth`.
-/

public section

open Set

section QuadraticDeformationGeometry

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Interior entry of the global quadratic inward deformation.** Under global forward completeness
on `U ∩ C`, for `T > 0` and any `t ≠ 1`, the map
`x ↦ forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x` sends `U ∩ C` into `U ∩ interior C`. -/
theorem Convex.mapsTo_forwardSemiflow_mul_one_sub_sq_inter_interior {C U : Set E}
    (hC : Convex ℝ C) {X : E → E} (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x)
    (hglob : ∀ x ∈ U ∩ C, forwardSemiflowInterval X (U ∩ C) x = Ici 0)
    {T t : ℝ} (hT_pos : 0 < T) (ht : t ≠ 1) :
    MapsTo (fun x ↦ forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x)
      (U ∩ C) (U ∩ interior C) :=
  hC.mapsTo_forwardSemiflow_inter_interior hX_in
    (mul_pos hT_pos (sq_pos_iff.mpr (sub_ne_zero.mpr ht.symm)))
    fun x hx ↦ hglob x hx ▸ mul_nonneg hT_pos.le (sq_nonneg _)

/-- **Interior entry of the finite-time quadratic inward deformation.** If
`forwardSemiflow X (U ∩ C)` is defined through time `T > 0` on `U ∩ C`, then for every
`t ∈ Ico 0 1`, the map `x ↦ forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x` sends `U ∩ C` into
`U ∩ interior C`. -/
theorem Convex.mapsTo_forwardSemiflow_mul_one_sub_sq_inter_interior_of_mem_Ico {C U : Set E}
    (hC : Convex ℝ C) {X : E → E}
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x)
    {T t : ℝ} (hT_pos : 0 < T)
    (hT : ∀ x ∈ U ∩ C, T ∈ forwardSemiflowInterval X (U ∩ C) x)
    (ht : t ∈ Ico (0 : ℝ) 1) :
    MapsTo (fun x ↦ forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x)
      (U ∩ C) (U ∩ interior C) :=
  hC.mapsTo_forwardSemiflow_inter_interior hX_in
    (mul_pos hT_pos (sq_pos_iff.mpr (sub_ne_zero.mpr ht.2.ne.symm)))
    fun x hx ↦ Icc_subset_forwardSemiflowInterval_of_mem (hT x hx)
      ⟨mul_nonneg hT_pos.le (sq_nonneg _),
        mul_le_of_le_one_right hT_pos.le (by nlinarith [ht.1, ht.2])⟩

/-- **Interior preservation of the global quadratic inward deformation.** Under global forward
completeness on `U ∩ C`, for any `T ≥ 0` and `t : ℝ`, the map
`x ↦ forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x` maps `U ∩ interior C` into itself. -/
theorem Convex.mapsTo_forwardSemiflow_mul_one_sub_sq_inter_interior_of_mem_interior {C U : Set E}
    (hC : Convex ℝ C) {X : E → E}
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x)
    (hglob : ∀ x ∈ U ∩ C, forwardSemiflowInterval X (U ∩ C) x = Ici 0)
    {T : ℝ} (hT_nonneg : 0 ≤ T) (t : ℝ) :
    MapsTo (fun x ↦ forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x)
      (U ∩ interior C) (U ∩ interior C) :=
  hC.mapsTo_forwardSemiflow_inter_interior_of_mem_interior hX_in
    fun x hx ↦ hglob x ⟨hx.1, interior_subset hx.2⟩ ▸ mul_nonneg hT_nonneg (sq_nonneg _)

/-- **Interior preservation of the finite-time quadratic inward deformation.** If
`forwardSemiflow X (U ∩ C)` is defined through time `T ≥ 0` on `U ∩ interior C`, then for
every `t ∈ Icc 0 1`, the map `x ↦ forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x` maps
`U ∩ interior C` into itself. -/
theorem Convex.mapsTo_forwardSemiflow_mul_one_sub_sq_inter_interior_of_mem_Icc_of_mem_interior
    {C U : Set E} (hC : Convex ℝ C) {X : E → E}
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x)
    {T t : ℝ} (hT_nonneg : 0 ≤ T)
    (hT : ∀ x ∈ U ∩ interior C, T ∈ forwardSemiflowInterval X (U ∩ C) x)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    MapsTo (fun x ↦ forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x)
      (U ∩ interior C) (U ∩ interior C) :=
  hC.mapsTo_forwardSemiflow_inter_interior_of_mem_interior hX_in
    fun x hx ↦ Icc_subset_forwardSemiflowInterval_of_mem (hT x hx)
      ⟨mul_nonneg hT_nonneg (sq_nonneg _),
        mul_le_of_le_one_right hT_nonneg (by nlinarith [ht.1, ht.2])⟩

end QuadraticDeformationGeometry
