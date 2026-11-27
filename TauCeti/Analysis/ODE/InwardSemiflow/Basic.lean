/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.ForwardSemiflow.Basic
public import TauCeti.Analysis.Convex.Cone.StrictInward

/-!
# Interior entry and persistence of inward forward semiflows

Proves that the maximal forward semiflow `TauCeti.forwardSemiflow` of a strictly inward vector
field in a convex set `C` immediately enters and remains in `interior C`
(`Convex.forwardSemiflow_mem_interior`, `Convex.forwardSemiflow_mem_interior_of_mem_interior`,
and the `MapsTo` lemmas on `U ∩ C` and `U ∩ interior C` for time-`T` maps and inward
deformations). Local existence/continuity and `C^m` regularity appear in `Existence.lean` and
`Smooth.lean`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer, 2012, Chapter 9,
  Theorems 9.12 and 9.24–9.26.
* H. Brezis, *On a characterization of flow-invariant sets*, Comm. Pure Appl. Math. 23 (1970),
  261–263.
-/

public section

open Set

section ForwardSemiflowGeometry

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {C S : Set E} {X : E → E} {x : E}

/-- **Interior entry and persistence of `forwardSemiflow`.** When `S ⊆ C` for a convex set `C` and
`X` is strictly inward to `C` on `S`, `forwardSemiflow X S` lies in `interior C` at every strictly
positive time in its forward interval. -/
theorem Convex.forwardSemiflow_mem_interior (hC : Convex ℝ C) (hSC : S ⊆ C)
    (hX_in : ∀ y ∈ S, X y ∈ strictInwardCone C y)
    {t : ℝ} (ht : t ∈ forwardSemiflowInterval X S x) (ht_pos : 0 < t) :
    forwardSemiflow X S t x ∈ interior C := by
  obtain ⟨_, _, _, htI, hγt, _, hS, hγ'⟩ := exists_integralCurve_apply_eq_forwardSemiflow ht
  rw [← hγt]
  exact hC.mapsTo_Ioo_interior_of_hasDerivWithinAt_Ico_of_mem_strictInwardCone (hS.mono_right hSC)
    (fun _ hs ↦ hγ' _ (Ioo_subset_Ico_self hs))
    (fun _ hs ↦ hX_in _ (hS (Ioo_subset_Ico_self hs))) ⟨ht_pos, htI.2⟩

/-- If `x ∈ interior C`, then `forwardSemiflow X S t x ∈ interior C` for all times `t` in its
forward interval (including `t = 0`). -/
theorem Convex.forwardSemiflow_mem_interior_of_mem_interior (hC : Convex ℝ C) (hSC : S ⊆ C)
    (hX_in : ∀ y ∈ S, X y ∈ strictInwardCone C y)
    (hx : x ∈ interior C) {t : ℝ} (ht : t ∈ forwardSemiflowInterval X S x) :
    forwardSemiflow X S t x ∈ interior C := by
  rcases (nonneg_of_mem_forwardSemiflowInterval ht).eq_or_lt with rfl | ht_pos
  exacts [by simpa using hx, hC.forwardSemiflow_mem_interior hSC hX_in ht ht_pos]

/-- **Interior entry of the time-`T` inward semiflow map.** When `X` is strictly inward to the
convex set `C` on `U ∩ C`, `0 < T`, and `T` lies in `forwardSemiflowInterval X (U ∩ C) x` for
every `x ∈ U ∩ C`, the time-`T` map `forwardSemiflow X (U ∩ C) T` sends `U ∩ C` into
`U ∩ interior C`. -/
theorem Convex.mapsTo_forwardSemiflow_inter_interior {C U : Set E} (hC : Convex ℝ C)
    {X : E → E} (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x) {T : ℝ}
    (hT_pos : 0 < T) (hT : ∀ x ∈ U ∩ C, T ∈ forwardSemiflowInterval X (U ∩ C) x) :
    MapsTo (forwardSemiflow X (U ∩ C) T) (U ∩ C) (U ∩ interior C) :=
  fun x hx ↦ ⟨(forwardSemiflow_mem (hT x hx)).1,
    hC.forwardSemiflow_mem_interior inter_subset_right hX_in (hT x hx) hT_pos⟩

/-- **Interior preservation of the time-`T` inward semiflow map.** When `X` is strictly inward
to the convex set `C` on `U ∩ C` and `T` lies in `forwardSemiflowInterval X (U ∩ C) x` for
every `x ∈ U ∩ interior C`, `forwardSemiflow X (U ∩ C) T` maps `U ∩ interior C` into itself. -/
theorem Convex.mapsTo_forwardSemiflow_inter_interior_of_mem_interior {C U : Set E}
    (hC : Convex ℝ C) {X : E → E}
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x) {T : ℝ}
    (hT : ∀ x ∈ U ∩ interior C, T ∈ forwardSemiflowInterval X (U ∩ C) x) :
    MapsTo (forwardSemiflow X (U ∩ C) T) (U ∩ interior C) (U ∩ interior C) :=
  fun x hx ↦ ⟨(forwardSemiflow_mem (hT x hx)).1,
    hC.forwardSemiflow_mem_interior_of_mem_interior inter_subset_right hX_in hx.2 (hT x hx)⟩

/-- **Interior entry of the global inward deformation.** Under global forward completeness on
`U ∩ C`, for `T > 0` and any `t ≠ 1`, the inward deformation sends `U ∩ C` into
`U ∩ interior C`. -/
theorem Convex.mapsTo_inward_deformation_inter_interior {C U : Set E} (hC : Convex ℝ C)
    {X : E → E} (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x)
    (hglob : ∀ x ∈ U ∩ C, forwardSemiflowInterval X (U ∩ C) x = Ici 0)
    {T t : ℝ} (hT_pos : 0 < T) (ht : t ≠ 1) :
    MapsTo (fun x ↦ forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x)
      (U ∩ C) (U ∩ interior C) :=
  hC.mapsTo_forwardSemiflow_inter_interior hX_in
    (mul_pos hT_pos (sq_pos_iff.mpr (sub_ne_zero.mpr ht.symm)))
    fun x hx ↦ hglob x hx ▸ mul_nonneg hT_pos.le (sq_nonneg _)

/-- **Interior entry of the finite-time inward deformation.** If `forwardSemiflow X (U ∩ C)`
is defined through time `T > 0` on `U ∩ C`, then for every `t ∈ Ico 0 1`, the inward
deformation sends `U ∩ C` into `U ∩ interior C`. -/
theorem Convex.mapsTo_inward_deformation_inter_interior_of_mem_Ico {C U : Set E}
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

/-- **Interior preservation of the global inward deformation.** Under global forward
completeness on `U ∩ C`, for any `T ≥ 0` and `t : ℝ`, the inward deformation maps
`U ∩ interior C` into itself. -/
theorem Convex.mapsTo_inward_deformation_inter_interior_of_mem_interior {C U : Set E}
    (hC : Convex ℝ C) {X : E → E}
    (hX_in : ∀ x ∈ U ∩ C, X x ∈ strictInwardCone C x)
    (hglob : ∀ x ∈ U ∩ C, forwardSemiflowInterval X (U ∩ C) x = Ici 0)
    {T : ℝ} (hT_nonneg : 0 ≤ T) (t : ℝ) :
    MapsTo (fun x ↦ forwardSemiflow X (U ∩ C) (T * (1 - t) ^ 2) x)
      (U ∩ interior C) (U ∩ interior C) :=
  hC.mapsTo_forwardSemiflow_inter_interior_of_mem_interior hX_in
    fun x hx ↦ hglob x ⟨hx.1, interior_subset hx.2⟩ ▸ mul_nonneg hT_nonneg (sq_nonneg _)

/-- **Interior preservation of the finite-time inward deformation.** If
`forwardSemiflow X (U ∩ C)` is defined through time `T ≥ 0` on `U ∩ interior C`, then for
every `t ∈ Icc 0 1`, the inward deformation maps `U ∩ interior C` into itself. -/
theorem Convex.mapsTo_inward_deformation_inter_interior_of_mem_Icc_of_mem_interior
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

end ForwardSemiflowGeometry
