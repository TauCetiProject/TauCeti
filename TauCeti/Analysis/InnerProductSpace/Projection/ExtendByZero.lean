/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Zero-extension star-algebra homomorphisms from closed subspaces

Let `U` be a complete subspace of a Hilbert space `E` over `𝕜`. Every bounded operator
`S : U →L[𝕜] U` extends by zero on `Uᗮ` to the bounded operator
`U.subtypeL ∘L S ∘L U.orthogonalProjectionOnto : E →L[𝕜] E`.

Because `U.orthogonalProjectionOnto ∘L U.subtypeL = id` and the adjoint of `U.subtypeL` is
`U.orthogonalProjectionOnto`, this extension is an isometric nonunital star-algebra homomorphism
`U.extendByZero : (U →L[𝕜] U) →⋆ₙₐ[𝕜] (E →L[𝕜] E)` sending the identity operator on `U` to the
orthogonal projection `U.starProjection`. Conversely, any bounded operator `T : E →L[𝕜] E` mapping
`E` into `U` and vanishing on `Uᗮ` is recovered from its compression
`U.orthogonalProjectionOnto ∘L T ∘L U.subtypeL` via `U.extendByZero`.

## Main definitions and results

* `Submodule.extendByZero`: the isometric nonunital star-algebra homomorphism
  `(U →L[𝕜] U) →⋆ₙₐ[𝕜] (E →L[𝕜] E)` extending operators on `U` by zero on `Uᗮ`.
* `Submodule.extendByZero_one`: `U.extendByZero 1 = U.starProjection`.
* `Submodule.norm_extendByZero` and `Submodule.isometry_extendByZero`: `U.extendByZero` preserves
  operator norms.
* `Submodule.extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL` and
  `Submodule.mem_range_extendByZero_iff`: operators with range in `U` and kernel containing `Uᗮ`
  are recovered by compressing to `U` and extending by zero.
* `Submodule.starProjection_mul_extendByZero`, `Submodule.extendByZero_mul_starProjection`,
  `Submodule.IsOrtho.extendByZero_mul_extendByZero`, and
  `Submodule.extendByZero_mul_extendByZero_orthogonal`: `U.starProjection` acts as a two-sided
  identity on `Set.range U.extendByZero`, and extensions from orthogonal subspaces annihilate each
  other.
* `Submodule.starProjection_mul_mul_starProjection_eq_extendByZero`,
  `Submodule.extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL_eq_mul_starProjection`,
  `Submodule.extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL_eq_starProjection_mul`,
  `Submodule.mul_extendByZero_of_mapsTo`, `Submodule.extendByZero_mul_of_mapsTo_orthogonal`,
  `Submodule.commute_extendByZero_iff_of_commute`, and
  `Submodule.eq_extendByZero_add_extendByZero_orthogonal_of_commute`: zero-extended compressions
  equal `U.starProjection * y * U.starProjection`, simplify under one-sided invariance of `U` or
  `Uᗮ`, and split operators commuting with `U.starProjection` across `U` and `Uᗮ`.
-/

public section

noncomputable section

namespace Submodule

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E] (U : Submodule 𝕜 E) [CompleteSpace U]

/-- Extend bounded operators on a complete subspace `U` of a Hilbert space `E` by zero on `Uᗮ`,
bundled as a nonunital star-algebra homomorphism `(U →L[𝕜] U) →⋆ₙₐ[𝕜] (E →L[𝕜] E)`. -/
def extendByZero : (U →L[𝕜] U) →⋆ₙₐ[𝕜] (E →L[𝕜] E) where
  toFun S := U.subtypeL ∘L S ∘L U.orthogonalProjectionOnto
  map_smul' c S := by
    ext x
    simp
  map_zero' := by
    ext x
    simp
  map_add' S T := by
    ext x
    simp
  map_mul' S T := by
    simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.comp_assoc U.orthogonalProjectionOnto U.subtypeL,
      U.orthogonalProjectionOnto_comp_subtypeL, ContinuousLinearMap.id_comp]
  map_star' S := by
    simp only [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_comp,
      U.adjoint_subtypeL, U.adjoint_orthogonalProjectionOnto, ContinuousLinearMap.comp_assoc]

/-- Operator-composition unfolding of `Submodule.extendByZero`. -/
theorem extendByZero_def (S : U →L[𝕜] U) :
    U.extendByZero S = U.subtypeL ∘L S ∘L U.orthogonalProjectionOnto :=
  (rfl)

/-- Pointwise formula for `Submodule.extendByZero`. -/
@[simp]
theorem extendByZero_apply (S : U →L[𝕜] U) (x : E) :
    U.extendByZero S x = S (U.orthogonalProjectionOnto x) :=
  (rfl)

variable {U}

/-- On elements of `U`, `U.extendByZero S` agrees with `S`. -/
theorem extendByZero_apply_coe (S : U →L[𝕜] U) (u : U) :
    U.extendByZero S u = S u := by
  simp

/-- On vectors belonging to `U`, `U.extendByZero S` agrees with `S`. -/
theorem extendByZero_apply_of_mem (S : U →L[𝕜] U) {x : E} (hx : x ∈ U) :
    U.extendByZero S x = S ⟨x, hx⟩ :=
  U.extendByZero_apply_coe S ⟨x, hx⟩

/-- `U.extendByZero S` vanishes on the orthogonal complement `Uᗮ`. -/
theorem extendByZero_apply_of_mem_orthogonal (S : U →L[𝕜] U) {x : E} (hx : x ∈ Uᗮ) :
    U.extendByZero S x = 0 := by
  simp [U.orthogonalProjectionOnto_eq_zero_iff.2 hx]

/-- Every image vector of `U.extendByZero S` lies in `U`. -/
theorem extendByZero_apply_mem (S : U →L[𝕜] U) (x : E) :
    U.extendByZero S x ∈ U :=
  (S (U.orthogonalProjectionOnto x)).property

/-- Compressing `U.extendByZero S` back to `U` recovers `S`. -/
@[simp]
theorem orthogonalProjectionOnto_comp_extendByZero_comp_subtypeL (S : U →L[𝕜] U) :
    U.orthogonalProjectionOnto ∘L U.extendByZero S ∘L U.subtypeL = S := by
  simp only [extendByZero_def, ContinuousLinearMap.comp_assoc,
    U.orthogonalProjectionOnto_comp_subtypeL, ContinuousLinearMap.comp_id]
  rw [← ContinuousLinearMap.comp_assoc, U.orthogonalProjectionOnto_comp_subtypeL,
    ContinuousLinearMap.id_comp]

/-- Extending the identity operator on `U` by zero on `Uᗮ` gives `U.starProjection`. -/
@[simp]
theorem extendByZero_one : U.extendByZero 1 = U.starProjection := by
  ext x
  simp

/-- Extending a bounded operator on `U` by zero on `Uᗮ` preserves its operator norm. -/
@[simp]
theorem norm_extendByZero (S : U →L[𝕜] U) : ‖U.extendByZero S‖ = ‖S‖ := by
  refine le_antisymm
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S) fun x => ?_)
    (ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg (U.extendByZero S)) fun u => ?_)
  · calc ‖U.extendByZero S x‖ = ‖S (U.orthogonalProjectionOnto x)‖ := by simp
      _ ≤ ‖S‖ * ‖U.orthogonalProjectionOnto x‖ := S.le_opNorm _
      _ ≤ ‖S‖ * ‖x‖ :=
        mul_le_mul_of_nonneg_left (U.norm_orthogonalProjectionOnto_apply_le x) (norm_nonneg S)
  · simpa only [extendByZero_apply_coe, norm_coe] using
      (U.extendByZero S).le_opNorm (u : E)

variable (U) in
/-- `Submodule.extendByZero` is an isometry for the operator norms. -/
theorem isometry_extendByZero : Isometry U.extendByZero :=
  AddMonoidHomClass.isometry_of_norm U.extendByZero norm_extendByZero

variable (U) in
/-- `Submodule.extendByZero` is continuous for the operator-norm topologies. -/
@[fun_prop]
theorem continuous_extendByZero : Continuous U.extendByZero :=
  U.isometry_extendByZero.continuous

variable (U) in
/-- `Submodule.extendByZero` is injective. -/
theorem extendByZero_injective : Function.Injective U.extendByZero :=
  U.isometry_extendByZero.injective

/-- Any bounded operator `T : E →L[𝕜] E` mapping `E` into `U` and vanishing on `Uᗮ` is the
extension by zero of its compression to `U`. -/
theorem extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL {T : E →L[𝕜] E}
    (hrange : ∀ x, T x ∈ U) (hker : ∀ x ∈ Uᗮ, T x = 0) :
    U.extendByZero (U.orthogonalProjectionOnto ∘L T ∘L U.subtypeL) = T := by
  ext x
  calc U.extendByZero (U.orthogonalProjectionOnto ∘L T ∘L U.subtypeL) x
      = U.starProjection (T (U.starProjection x)) := by simp
    _ = T (U.starProjection x) := U.starProjection_eq_self_iff.2 (hrange _)
    _ = T x := U.apply_starProjection_eq_of_forall_mem_orthogonal hker x

/-- Left multiplication by `U.starProjection` fixes every operator extended from `U` by zero. -/
@[simp]
theorem starProjection_mul_extendByZero (S : U →L[𝕜] U) :
    U.starProjection * U.extendByZero S = U.extendByZero S := by
  rw [← extendByZero_one, ← map_mul, one_mul]

/-- Right multiplication by `U.starProjection` fixes every operator extended from `U` by zero. -/
@[simp]
theorem extendByZero_mul_starProjection (S : U →L[𝕜] U) :
    U.extendByZero S * U.starProjection = U.extendByZero S := by
  rw [← extendByZero_one, ← map_mul, mul_one]

/-- Operators extended by zero from orthogonal complete subspaces have zero product. -/
theorem IsOrtho.extendByZero_mul_extendByZero {V : Submodule 𝕜 E} [CompleteSpace V] (h : U ⟂ V)
    (S : U →L[𝕜] U) (T : V →L[𝕜] V) :
    U.extendByZero S * V.extendByZero T = 0 := by
  ext x
  exact U.extendByZero_apply_of_mem_orthogonal S (h.ge (V.extendByZero_apply_mem T x))

/-- Operators extended by zero from orthogonal complete subspaces commute. -/
theorem IsOrtho.commute_extendByZero {V : Submodule 𝕜 E} [CompleteSpace V] (h : U ⟂ V)
    (S : U →L[𝕜] U) (T : V →L[𝕜] V) :
    Commute (U.extendByZero S) (V.extendByZero T) :=
  (h.extendByZero_mul_extendByZero S T).trans (h.symm.extendByZero_mul_extendByZero T S).symm

/-- Operators extended by zero from `U` and from `Uᗮ` have zero product. -/
@[simp]
theorem extendByZero_mul_extendByZero_orthogonal (S : U →L[𝕜] U) (T : Uᗮ →L[𝕜] Uᗮ) :
    U.extendByZero S * Uᗮ.extendByZero T = 0 :=
  U.isOrtho_orthogonal_right.extendByZero_mul_extendByZero S T

/-- Operators extended by zero from `Uᗮ` and from `U` have zero product. -/
@[simp]
theorem extendByZero_orthogonal_mul_extendByZero (T : Uᗮ →L[𝕜] Uᗮ) (S : U →L[𝕜] U) :
    Uᗮ.extendByZero T * U.extendByZero S = 0 :=
  U.isOrtho_orthogonal_left.extendByZero_mul_extendByZero T S

/-- Every operator extended by zero from `U` commutes with every operator extended by zero from
`Uᗮ`. -/
theorem commute_extendByZero_extendByZero_orthogonal (S : U →L[𝕜] U) (T : Uᗮ →L[𝕜] Uᗮ) :
    Commute (U.extendByZero S) (Uᗮ.extendByZero T) :=
  U.isOrtho_orthogonal_right.commute_extendByZero S T

/-- A bounded operator on `E` belongs to `Set.range U.extendByZero` if and only if its range lies
in `U` and its kernel contains `Uᗮ`. -/
theorem mem_range_extendByZero_iff {T : E →L[𝕜] E} :
    T ∈ Set.range U.extendByZero ↔ (∀ x, T x ∈ U) ∧ (∀ x ∈ Uᗮ, T x = 0) :=
  ⟨by
      rintro ⟨S, rfl⟩
      exact ⟨U.extendByZero_apply_mem S, fun _ hx => U.extendByZero_apply_of_mem_orthogonal S hx⟩,
    fun ⟨hrange, hker⟩ => ⟨U.orthogonalProjectionOnto ∘L T ∘L U.subtypeL,
      U.extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL hrange hker⟩⟩

/-- `U.starProjection * y * U.starProjection` is the zero extension of the compression
`U.orthogonalProjectionOnto ∘L y ∘L U.subtypeL`. -/
theorem starProjection_mul_mul_starProjection_eq_extendByZero (y : E →L[𝕜] E) :
    U.starProjection * y * U.starProjection =
      U.extendByZero (U.orthogonalProjectionOnto ∘L y ∘L U.subtypeL) := by
  simp only [extendByZero_def, Submodule.starProjection, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc]

/-- If `y` leaves `U` invariant, extending its compression to `U` by zero on `Uᗮ` gives
`y * U.starProjection`. -/
theorem extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL_eq_mul_starProjection
    {y : E →L[𝕜] E} (hy : ∀ x ∈ U, y x ∈ U) :
    U.extendByZero (U.orthogonalProjectionOnto ∘L y ∘L U.subtypeL) = y * U.starProjection := by
  rw [← starProjection_mul_mul_starProjection_eq_extendByZero]
  ext x
  exact U.starProjection_eq_self_iff.2 (hy _ (U.starProjection_apply_mem x))

/-- If `y` leaves `Uᗮ` invariant, extending its compression to `U` by zero on `Uᗮ` gives
`U.starProjection * y`. -/
theorem extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL_eq_starProjection_mul
    {y : E →L[𝕜] E} (hy : ∀ x ∈ Uᗮ, y x ∈ Uᗮ) :
    U.extendByZero (U.orthogonalProjectionOnto ∘L y ∘L U.subtypeL) = U.starProjection * y := by
  rw [← starProjection_mul_mul_starProjection_eq_extendByZero]
  exact U.mul_starProjection_eq_self fun x hx =>
    U.starProjection_apply_eq_zero_iff.2 (hy x hx)

/-- If `y` commutes with `U.starProjection`, extending its compression to `U` by zero on `Uᗮ` gives
`y * U.starProjection`. -/
theorem extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL_eq_mul_starProjection_of_commute
    {y : E →L[𝕜] E} (hy : Commute U.starProjection y) :
    U.extendByZero (U.orthogonalProjectionOnto ∘L y ∘L U.subtypeL) = y * U.starProjection :=
  extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL_eq_mul_starProjection
    fun _ => apply_mem_of_commute_starProjection hy

/-- Left multiplication of `U.extendByZero S` by an operator `y` leaving `U` invariant acts inside
`U.extendByZero` by the compression of `y` to `U`. -/
theorem mul_extendByZero_of_mapsTo {y : E →L[𝕜] E} (hy : ∀ x ∈ U, y x ∈ U) (S : U →L[𝕜] U) :
    y * U.extendByZero S =
      U.extendByZero ((U.orthogonalProjectionOnto ∘L y ∘L U.subtypeL) * S) := by
  rw [map_mul, extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL_eq_mul_starProjection hy,
    mul_assoc, starProjection_mul_extendByZero]

/-- Right multiplication of `U.extendByZero S` by an operator `y` leaving `Uᗮ` invariant acts inside
`U.extendByZero` by the compression of `y` to `U`. -/
theorem extendByZero_mul_of_mapsTo_orthogonal {y : E →L[𝕜] E} (hy : ∀ x ∈ Uᗮ, y x ∈ Uᗮ)
    (S : U →L[𝕜] U) :
    U.extendByZero S * y =
      U.extendByZero (S * (U.orthogonalProjectionOnto ∘L y ∘L U.subtypeL)) := by
  rw [map_mul, extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL_eq_starProjection_mul hy,
    ← mul_assoc, extendByZero_mul_starProjection]

/-- Left multiplication of `U.extendByZero S` by an operator `y` commuting with `U.starProjection`
acts inside `U.extendByZero` by the compression of `y` to `U`. -/
theorem mul_extendByZero_of_commute {y : E →L[𝕜] E} (hy : Commute U.starProjection y)
    (S : U →L[𝕜] U) :
    y * U.extendByZero S =
      U.extendByZero ((U.orthogonalProjectionOnto ∘L y ∘L U.subtypeL) * S) :=
  mul_extendByZero_of_mapsTo (fun _ => apply_mem_of_commute_starProjection hy) S

/-- Right multiplication of `U.extendByZero S` by an operator `y` commuting with `U.starProjection`
acts inside `U.extendByZero` by the compression of `y` to `U`. -/
theorem extendByZero_mul_of_commute {y : E →L[𝕜] E} (hy : Commute U.starProjection y)
    (S : U →L[𝕜] U) :
    U.extendByZero S * y =
      U.extendByZero (S * (U.orthogonalProjectionOnto ∘L y ∘L U.subtypeL)) :=
  extendByZero_mul_of_mapsTo_orthogonal
    (fun _ => apply_mem_of_commute_starProjection (commute_starProjection_orthogonal_iff.2 hy)) S

/-- When `y` commutes with `U.starProjection`, `U.extendByZero S` commutes with `y` if and only if
`S` commutes with the compression of `y` to `U`. -/
theorem commute_extendByZero_iff_of_commute {y : E →L[𝕜] E} (hy : Commute U.starProjection y)
    (S : U →L[𝕜] U) :
    Commute (U.extendByZero S) y ↔ Commute S (U.orthogonalProjectionOnto ∘L y ∘L U.subtypeL) := by
  simp only [Commute, SemiconjBy, extendByZero_mul_of_commute hy, mul_extendByZero_of_commute hy,
    U.extendByZero_injective.eq_iff]

/-- Every bounded operator commuting with `U.starProjection` is the sum of the zero extensions of
its compressions to `U` and `Uᗮ`. -/
theorem eq_extendByZero_add_extendByZero_orthogonal_of_commute {y : E →L[𝕜] E}
    (hy : Commute U.starProjection y) :
    y = U.extendByZero (U.orthogonalProjectionOnto ∘L y ∘L U.subtypeL) +
      Uᗮ.extendByZero (Uᗮ.orthogonalProjectionOnto ∘L y ∘L Uᗮ.subtypeL) := by
  rw [extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL_eq_mul_starProjection_of_commute hy,
    extendByZero_comp_orthogonalProjectionOnto_comp_subtypeL_eq_mul_starProjection_of_commute
      (commute_starProjection_orthogonal_iff.2 hy), ← mul_add, U.starProjection_orthogonal',
    add_sub_cancel, mul_one]

end Submodule
