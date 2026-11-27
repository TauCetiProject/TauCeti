/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Grassmannian.ImagePlane

/-!
# Grassmannians under linear equivalences

A continuous linear equivalence `L : E ≃L[ℝ] F` of finite-dimensional real inner product spaces,
not necessarily isometric, carries each `k`-plane `S` of `E` to the `k`-plane `L S` of `F`. In the
projection form of the Grassmannian (`Euclidean.grassmannian ℝ E k`), where a plane is recorded by
its orthogonal projection, this is the map `P ↦ P_{L (range P)}`
(`ContinuousLinearEquiv.grassmannianMap`), the image-plane map
`Euclidean.grassmannian.imagePlane` at `(L, P)`. Its value depends on the inner product of `F`, not
only on `L`: the orthogonal projection onto `L S` is in general not `L P L⁻¹`.

The map is functorial (`ContinuousLinearEquiv.grassmannianMap_refl`,
`ContinuousLinearEquiv.grassmannianMap_trans`), so it is a homeomorphism `G(E, k) ≃ₜ G(F, k)`
(`ContinuousLinearEquiv.grassmannianCongr`). It depends continuously on `L` and `P` jointly
(`ContinuousAt.grassmannianMap`). For a linear isometry equivalence it is conjugation
`P ↦ U P U⁻¹` (`LinearIsometryEquiv.grassmannianMap_toContinuousLinearEquiv`), and more generally,
when `L` multiplies inner products by a constant `c²`, the projection onto `L (range P)` is
`L P L⁻¹` (`ContinuousLinearEquiv.coe_grassmannianMap_of_inner_map_map`).

These are the fibres of the canonical homeomorphism between the Grassmann bundles of a vector
bundle for two fibre metrics (W. K. Allard, *On the first variation of a varifold*, Section 3).

## Main definitions

* `ContinuousLinearEquiv.grassmannianMap`: the map `P ↦ P_{L (range P)}` of Grassmannians.
* `ContinuousLinearEquiv.grassmannianCongr`: the same map, as a homeomorphism.

## Main results

* `ContinuousLinearEquiv.range_coe_grassmannianMap_apply`: the plane of the image is `L (range P)`.
* `ContinuousLinearEquiv.grassmannianMap_trans`: functoriality.
* `ContinuousAt.grassmannianMap`: joint continuity in the equivalence and the plane.
* `ContinuousLinearEquiv.coe_grassmannianMap_of_inner_map_map`: for a conformal equivalence with
  constant factor the image of `P` is `L P L⁻¹`.
-/

public section

open Module ContinuousLinearMap Euclidean
open scoped InnerProductSpace

namespace Euclidean.grassmannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {k : ℕ}

/-- Two points of the Grassmannian with the same plane are equal: each is the orthogonal
projection onto its range. -/
theorem ext_range {P Q : grassmannian ℝ E k}
    (h : (P : E →L[ℝ] E).range = (Q : E →L[ℝ] E).range) : P = Q := by
  obtain ⟨_, hP⟩ := eq_starProjection_range P.property
  obtain ⟨_, hQ⟩ := eq_starProjection_range Q.property
  refine Subtype.ext ?_
  rw [hP, hQ]
  simp_rw [h]

end Euclidean.grassmannian

namespace ContinuousLinearEquiv

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G] {k : ℕ}

variable (L : E ≃L[ℝ] F)

variable (k) in
/-- The map of Grassmannians induced by a continuous linear equivalence `L : E ≃L[ℝ] F`: a point
`P` of `G(E, k)` goes to the orthogonal projection onto the `k`-plane `L (range P)` of `F`. -/
noncomputable def grassmannianMap (P : grassmannian ℝ E k) : grassmannian ℝ F k :=
  ⟨((L : E →L[ℝ] F) ∘L (P : E →L[ℝ] E)).range.starProjection,
    grassmannian.starProjection_range_comp_mem P.property L.injective.injOn⟩

/-- The image of `P` is the orthogonal projection onto the range of `L ∘L P`. -/
theorem coe_grassmannianMap_apply (P : grassmannian ℝ E k) :
    (L.grassmannianMap k P : F →L[ℝ] F) =
      ((L : E →L[ℝ] F) ∘L (P : E →L[ℝ] E)).range.starProjection :=
  (rfl)

/-- `ContinuousLinearEquiv.grassmannianMap` is the image-plane map at `(L, P)`. -/
theorem grassmannianMap_eq_imagePlane (P : grassmannian ℝ E k) :
    L.grassmannianMap k P =
      grassmannian.imagePlane E F k ⟨((L : E →L[ℝ] F), P), L.injective.injOn⟩ :=
  Subtype.ext (by rw [grassmannian.coe_imagePlane_apply, coe_grassmannianMap_apply])

/-- The plane of the image of `P` is `L (range P)`. -/
theorem range_coe_grassmannianMap_apply (P : grassmannian ℝ E k) :
    (L.grassmannianMap k P : F →L[ℝ] F).range =
      (P : E →L[ℝ] E).range.map (L : E →ₗ[ℝ] F) := by
  rw [grassmannianMap_eq_imagePlane]
  exact grassmannian.range_coe_imagePlane_apply _

/-- The identity induces the identity of the Grassmannian. -/
@[simp]
theorem grassmannianMap_refl (P : grassmannian ℝ E k) :
    (ContinuousLinearEquiv.refl ℝ E).grassmannianMap k P = P := by
  refine grassmannian.ext_range ?_
  rw [range_coe_grassmannianMap_apply]
  exact Submodule.map_id _

/-- **Functoriality.** The map induced by a composite is the composite of the induced maps. -/
theorem grassmannianMap_trans (L' : F ≃L[ℝ] G) (P : grassmannian ℝ E k) :
    (L.trans L').grassmannianMap k P = L'.grassmannianMap k (L.grassmannianMap k P) := by
  refine grassmannian.ext_range ?_
  rw [range_coe_grassmannianMap_apply, range_coe_grassmannianMap_apply,
    range_coe_grassmannianMap_apply, ← Submodule.map_comp]
  rfl

/-- The inverse equivalence undoes the induced map. -/
@[simp]
theorem symm_grassmannianMap_grassmannianMap (P : grassmannian ℝ E k) :
    L.symm.grassmannianMap k (L.grassmannianMap k P) = P := by
  rw [← grassmannianMap_trans, self_trans_symm, grassmannianMap_refl]

/-- The induced map undoes the map induced by the inverse equivalence. -/
@[simp]
theorem grassmannianMap_symm_grassmannianMap (Q : grassmannian ℝ F k) :
    L.grassmannianMap k (L.symm.grassmannianMap k Q) = Q := by
  simpa using L.symm.symm_grassmannianMap_grassmannianMap Q

/-- The induced map depends only on the plane `L (range P)`: two equivalences with the same image
of `range P` send `P` to the same point. -/
theorem grassmannianMap_eq_of_map_eq {L' : E ≃L[ℝ] F} {P : grassmannian ℝ E k}
    (h : (P : E →L[ℝ] E).range.map (L : E →ₗ[ℝ] F) =
      (P : E →L[ℝ] E).range.map (L' : E →ₗ[ℝ] F)) :
    L.grassmannianMap k P = L'.grassmannianMap k P := by
  refine grassmannian.ext_range ?_
  rw [range_coe_grassmannianMap_apply, range_coe_grassmannianMap_apply, h]

variable (k) in
/-- The **homeomorphism of Grassmannians induced by a continuous linear equivalence**
`L : E ≃L[ℝ] F`: `P ↦ P_{L (range P)}`, with inverse induced by `L⁻¹`. -/
noncomputable def grassmannianCongr : grassmannian ℝ E k ≃ₜ grassmannian ℝ F k where
  toFun := L.grassmannianMap k
  invFun := L.symm.grassmannianMap k
  left_inv := L.symm_grassmannianMap_grassmannianMap
  right_inv := L.grassmannianMap_symm_grassmannianMap
  continuous_toFun := ((grassmannian.imagePlane E F k).continuous.comp
    ((continuous_const.prodMk continuous_id).subtype_mk _)).congr
    fun P ↦ (L.grassmannianMap_eq_imagePlane P).symm
  continuous_invFun := ((grassmannian.imagePlane F E k).continuous.comp
    ((continuous_const.prodMk continuous_id).subtype_mk _)).congr
    fun Q ↦ (L.symm.grassmannianMap_eq_imagePlane Q).symm

@[simp]
theorem coe_grassmannianCongr :
    (L.grassmannianCongr k : grassmannian ℝ E k → grassmannian ℝ F k) = L.grassmannianMap k :=
  (rfl)

@[simp]
theorem grassmannianCongr_symm : (L.grassmannianCongr k).symm = L.symm.grassmannianCongr k :=
  (rfl)

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {k : ℕ}

/-- For a linear isometry equivalence `U`, the map of Grassmannians induced by `U` as a continuous
linear equivalence is conjugation `P ↦ U P U⁻¹`. -/
theorem grassmannianMap_toContinuousLinearEquiv (U : E ≃ₗᵢ[ℝ] F) (P : grassmannian ℝ E k) :
    U.toContinuousLinearEquiv.grassmannianMap k P = U.grassmannianCongr k P := by
  refine grassmannian.ext_range ?_
  rw [ContinuousLinearEquiv.range_coe_grassmannianMap_apply, range_coe_grassmannianCongr_apply]
  rfl

end LinearIsometryEquiv

namespace ContinuousLinearEquiv

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {k : ℕ}
  (L : E ≃L[ℝ] F)

/-- For a continuous linear equivalence `L` that multiplies inner products by the constant `c²`,
the orthogonal projection onto `L (range P)` is `L P L⁻¹`: for `c ≠ 0`, `c⁻¹ L` is a linear
isometry equivalence, under which orthogonal projections correspond, and for `c = 0` the space
`F` is zero. -/
theorem coe_grassmannianMap_of_inner_map_map {c : ℝ}
    (h : ∀ u v, ⟪L u, L v⟫_ℝ = c ^ 2 * ⟪u, v⟫_ℝ) (P : grassmannian ℝ E k) :
    (L.grassmannianMap k P : F →L[ℝ] F) =
      (L : E →L[ℝ] F) ∘L (P : E →L[ℝ] E) ∘L (L.symm : F →L[ℝ] E) := by
  rcases eq_or_ne c 0 with rfl | hc
  · -- For `c = 0` every vector `L u` of `F` has `⟪L u, L u⟫ = 0`.
    have hF (w : F) : w = 0 := by
      rw [← L.apply_symm_apply w]
      exact inner_self_eq_zero.1 (by rw [h, zero_pow two_ne_zero, zero_mul])
    exact ContinuousLinearMap.ext fun w ↦ (hF _).trans (hF _).symm
  -- The rescaled equivalence `c⁻¹ L` is isometric.
  let U : E ≃ₗᵢ[ℝ] F :=
    { L.toLinearEquiv.trans (LinearEquiv.smulOfNeZero ℝ F c⁻¹ (inv_ne_zero hc)) with
      norm_map' := fun u ↦ by
        have h2 : ‖L u‖ ^ 2 = (|c| * ‖u‖) ^ 2 := by
          rw [← real_inner_self_eq_norm_sq, h, real_inner_self_eq_norm_sq, mul_pow, sq_abs]
        have h3 : ‖L u‖ = |c| * ‖u‖ :=
          (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h2
        simp [norm_smul, h3, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.2 hc)] }
  have hU (u : E) : U u = c⁻¹ • L u := rfl
  have hUs (v : F) : U.symm v = c • L.symm v := by
    apply U.injective
    rw [U.apply_symm_apply, hU, map_smul, L.apply_symm_apply, smul_smul,
      inv_mul_cancel₀ hc, one_smul]
  have hmap : (P : E →L[ℝ] E).range.map (L : E →ₗ[ℝ] F) =
      (P : E →L[ℝ] E).range.map (U.toContinuousLinearEquiv : E →ₗ[ℝ] F) := by
    ext v
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨c • u, Submodule.smul_mem _ _ hu, by
        simp [hU, smul_smul, mul_inv_cancel₀ hc]⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨c⁻¹ • u, Submodule.smul_mem _ _ hu, by simp [hU]⟩
  rw [grassmannianMap_eq_of_map_eq L hmap,
    LinearIsometryEquiv.grassmannianMap_toContinuousLinearEquiv,
    LinearIsometryEquiv.coe_grassmannianCongr_apply]
  ext v
  simp [LinearIsometryEquiv.conjStarAlgEquiv_apply, hU, hUs, smul_smul, mul_inv_cancel₀ hc]

end ContinuousLinearEquiv

section Continuity

variable {X E F : Type*} [TopologicalSpace X]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {k : ℕ}
  {L : X → E ≃L[ℝ] F} {P : X → grassmannian ℝ E k} {x : X}

/-- **Joint continuity of the induced maps of Grassmannians**: if the equivalences `L x`, seen as
operators, and the planes `P x` depend continuously on `x` at `x₀`, so does the projection onto
`L x (range (P x))`. -/
theorem ContinuousAt.grassmannianMap (hL : ContinuousAt (fun x ↦ (L x : E →L[ℝ] F)) x)
    (hP : ContinuousAt P x) : ContinuousAt (fun x ↦ (L x).grassmannianMap k (P x)) x := by
  let g : X → {x : (E →L[ℝ] F) × grassmannian ℝ E k //
      Set.InjOn x.1 ((x.2 : E →L[ℝ] E).range : Set E)} :=
    fun x ↦ ⟨((L x : E →L[ℝ] F), P x), (L x).injective.injOn⟩
  have hg : ContinuousAt g x :=
    tendsto_subtype_rng.2 (hL.prodMk hP)
  exact ((grassmannian.imagePlane E F k).continuous.continuousAt.comp hg).congr
    (Filter.Eventually.of_forall fun x ↦ ((L x).grassmannianMap_eq_imagePlane (P x)).symm)

/-- **Joint continuity of the induced maps of Grassmannians**, global form. -/
theorem Continuous.grassmannianMap (hL : Continuous fun x ↦ (L x : E →L[ℝ] F))
    (hP : Continuous P) : Continuous fun x ↦ (L x).grassmannianMap k (P x) :=
  continuous_iff_continuousAt.2 fun _ ↦ hL.continuousAt.grassmannianMap hP.continuousAt

end Continuity
