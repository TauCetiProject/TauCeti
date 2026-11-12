/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.Isometry

/-!
# Extending isometries of a nondegenerate subspace by the identity

Let `ι : W → V` be an isometric embedding of a finite-dimensional bilinear space `(W, B')` into
a bilinear space `(V, B)`, and suppose that `B'` is nondegenerate. Then `V` is the orthogonal sum
of the image of `ι` and its orthogonal complement. The projection onto the first summand, read
in `W`, is `ι.orthogonalProjection`: the vector `π v` is characterized by `B' (π v) w = B v (ι w)`
for every `w`.

If moreover `B` is symmetric, every isometry `g` of `B'` extends to the isometry
`v ↦ v + ι (g (π v) - π v)` of `B`, which acts as `g` on the image of `ι` and as the identity on
its orthogonal complement. The extensions form an injective group homomorphism
`ι.isometryGroupExtend : Aut(W, B') →* Aut(V, B)`.

For an integral lattice this is how isometries of a sublattice spanning a nondegenerate rational
subspace become rational isometries of the whole lattice; a congruence condition then makes them
preserve the lattice itself.

## Main definitions

* `LinearMap.BilinForm.Isometry.orthogonalProjection`: the projection `π : V → W`.
* `LinearMap.BilinForm.Isometry.isometryGroupExtend`: the extension homomorphism.

## Main results

* `LinearMap.BilinForm.Isometry.apply_orthogonalProjection`: `B' (π v) w = B v (ι w)`.
* `LinearMap.BilinForm.Isometry.orthogonalProjection_apply_left`: `π (ι w) = w`.
* `LinearMap.BilinForm.Isometry.isometryGroupExtend_apply`: the formula for the extension.
* `LinearMap.BilinForm.Isometry.isometryGroupExtend_apply_left` and
  `LinearMap.BilinForm.Isometry.isometryGroupExtend_apply_of_forall_eq_zero`: the extension acts
  as `g` on the image of `ι` and fixes its orthogonal complement.
* `LinearMap.BilinForm.Isometry.isometryGroupExtend_injective`: the extension is injective.
-/

public section

open Module TauCeti.BilinForm
open LinearMap (BilinForm)

namespace LinearMap.BilinForm.Isometry

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {B : BilinForm K V} {B' : BilinForm K W}

/-! ## The orthogonal projection -/

/-- The orthogonal projection onto the image of an isometric embedding `ι` of a nondegenerate
finite-dimensional bilinear space, read in the source: `π v` is the unique vector with
`B' (π v) w = B v (ι w)` for every `w`. -/
noncomputable def orthogonalProjection (ι : B' →bᵢ B) (hB' : B'.Nondegenerate) : V →ₗ[K] W :=
  (B'.toDual hB').symm.toLinearMap ∘ₗ ι.toLinearMap.dualMap ∘ₗ B

/-- The defining property of the orthogonal projection. -/
@[simp]
theorem apply_orthogonalProjection (ι : B' →bᵢ B) (hB' : B'.Nondegenerate) (v : V) (w : W) :
    B' (ι.orthogonalProjection hB' v) w = B v (ι w) := by
  simp [orthogonalProjection]

/-- The orthogonal projection is the unique map with its defining property. -/
theorem eq_orthogonalProjection_iff (ι : B' →bᵢ B) (hB' : B'.Nondegenerate) (v : V) (x : W) :
    x = ι.orthogonalProjection hB' v ↔ ∀ w, B' x w = B v (ι w) := by
  refine ⟨fun h w ↦ h ▸ apply_orthogonalProjection ι hB' v w, fun h ↦ ?_⟩
  rw [← sub_eq_zero]
  exact hB'.1 _ fun w ↦ by simp [h]

/-- The orthogonal projection is a left inverse of the embedding. -/
@[simp]
theorem orthogonalProjection_apply_left (ι : B' →bᵢ B) (hB' : B'.Nondegenerate) (w : W) :
    ι.orthogonalProjection hB' (ι w) = w :=
  ((ι.eq_orthogonalProjection_iff hB' (ι w) w).mpr fun _ ↦ (ι.map_app _ _).symm).symm

/-- The orthogonal projection vanishes exactly on the orthogonal complement of the image. -/
theorem orthogonalProjection_eq_zero_iff (ι : B' →bᵢ B) (hB' : B'.Nondegenerate) (v : V) :
    ι.orthogonalProjection hB' v = 0 ↔ ∀ w, B v (ι w) = 0 := by
  rw [eq_comm, eq_orthogonalProjection_iff]
  exact ⟨fun h w ↦ by simpa using (h w).symm, fun h w ↦ by simp [h w]⟩

/-! ## The extension -/

/-- The linear map `v ↦ v + ι (g (π v) - π v)` extending an endomorphism `g` of `W` by the
identity on the orthogonal complement of the image of `ι`. -/
private noncomputable def extendAux (ι : B' →bᵢ B) (hB' : B'.Nondegenerate) (g : W →ₗ[K] W) :
    V →ₗ[K] V :=
  LinearMap.id + ι.toLinearMap ∘ₗ (g - LinearMap.id) ∘ₗ ι.orthogonalProjection hB'

private theorem extendAux_apply (ι : B' →bᵢ B) (hB' : B'.Nondegenerate) (g : W →ₗ[K] W)
    (v : V) :
    extendAux ι hB' g v = v + ι (g (ι.orthogonalProjection hB' v) - ι.orthogonalProjection hB' v) :=
  by simp [extendAux]

private theorem orthogonalProjection_extendAux (ι : B' →bᵢ B) (hB' : B'.Nondegenerate)
    (g : W →ₗ[K] W) (v : V) :
    ι.orthogonalProjection hB' (extendAux ι hB' g v) = g (ι.orthogonalProjection hB' v) := by
  rw [extendAux_apply, map_add, orthogonalProjection_apply_left, add_sub_cancel]

private theorem extendAux_comp (ι : B' →bᵢ B) (hB' : B'.Nondegenerate) (f g : W →ₗ[K] W) :
    extendAux ι hB' f ∘ₗ extendAux ι hB' g = extendAux ι hB' (f ∘ₗ g) := by
  ext v
  simp only [LinearMap.comp_apply, extendAux_apply _ _ _ (extendAux ι hB' g v),
    orthogonalProjection_extendAux]
  rw [extendAux_apply, extendAux_apply, add_assoc, ← map_add]
  congr 2
  abel

private theorem extendAux_id (ι : B' →bᵢ B) (hB' : B'.Nondegenerate) :
    extendAux ι hB' LinearMap.id = LinearMap.id := by
  ext v
  simp [extendAux_apply]

/-- If `B` is symmetric, the extension of an isometry of `B'` is an isometry of `B`. -/
private theorem isIsometry_extendAux (ι : B' →bᵢ B) (hB : B.IsSymm) (hB' : B'.Nondegenerate)
    {g : W →ₗ[K] W} (hg : IsIsometry B' g) : IsIsometry B (extendAux ι hB' g) := by
  have hB's : ∀ x y, B' x y = B' y x := fun x y ↦ by
    rw [← ι.map_app, ← ι.map_app, hB.eq]
  refine isIsometry_iff.mpr fun v u ↦ ?_
  have hv (z : W) : B v (ι z) = B' (ι.orthogonalProjection hB' v) z :=
    (apply_orthogonalProjection ι hB' v z).symm
  have hu (z : W) : B (ι z) u = B' z (ι.orthogonalProjection hB' u) := by
    rw [hB.eq, ← apply_orthogonalProjection ι hB' u z, hB's]
  rw [extendAux_apply, extendAux_apply]
  simp only [map_add, LinearMap.add_apply, hv, hu, ι.map_app, map_sub, LinearMap.sub_apply,
    hg.apply]
  ring

private theorem extendAux_mul (ι : B' →bᵢ B) (hB' : B'.Nondegenerate) (g h : isometryGroup B') :
    extendAux ι hB' ((g * h : isometryGroup B') : W ≃ₗ[K] W) =
      extendAux ι hB' (g : W ≃ₗ[K] W) ∘ₗ extendAux ι hB' (h : W ≃ₗ[K] W) := by
  rw [extendAux_comp, Subgroup.coe_mul, LinearEquiv.mul_eq_trans, LinearEquiv.coe_trans]

private theorem extendAux_one (ι : B' →bᵢ B) (hB' : B'.Nondegenerate) :
    extendAux ι hB' ((1 : isometryGroup B') : W ≃ₗ[K] W) = LinearMap.id :=
  extendAux_id ι hB'

/-- **Extension of isometries by the identity.** For an isometric embedding `ι` of a
nondegenerate finite-dimensional bilinear space `(W, B')` into a symmetric bilinear space
`(V, B)`, the isometry `g` of `B'` extends to the isometry of `B` acting as `g` on the image of
`ι` and as the identity on its orthogonal complement. -/
noncomputable def isometryGroupExtend (ι : B' →bᵢ B) (hB : B.IsSymm) (hB' : B'.Nondegenerate) :
    isometryGroup B' →* isometryGroup B where
  toFun g := ⟨LinearEquiv.ofLinearMap (extendAux ι hB' (g : W ≃ₗ[K] W))
      (extendAux ι hB' ((g⁻¹ : isometryGroup B') : W ≃ₗ[K] W))
      (by rw [← extendAux_mul, mul_inv_cancel, extendAux_one])
      (by rw [← extendAux_mul, inv_mul_cancel, extendAux_one]),
    mem_isometryGroup_iff.mpr (isIsometry_extendAux ι hB hB' (mem_isometryGroup.mp g.2)).apply⟩
  map_one' := by
    ext v
    exact LinearMap.congr_fun (extendAux_one ι hB') v
  map_mul' g h := by
    ext v
    exact LinearMap.congr_fun (extendAux_mul ι hB' g h) v

/-- The extension acts by `v ↦ v + ι (g (π v) - π v)`. -/
theorem isometryGroupExtend_apply (ι : B' →bᵢ B) (hB : B.IsSymm) (hB' : B'.Nondegenerate)
    (g : isometryGroup B') (v : V) :
    (ι.isometryGroupExtend hB hB' g : V ≃ₗ[K] V) v =
      v + ι ((g : W ≃ₗ[K] W) (ι.orthogonalProjection hB' v) - ι.orthogonalProjection hB' v) :=
  extendAux_apply ι hB' _ v

/-- On the image of `ι`, the extension of `g` acts as `g`. -/
@[simp]
theorem isometryGroupExtend_apply_left (ι : B' →bᵢ B) (hB : B.IsSymm) (hB' : B'.Nondegenerate)
    (g : isometryGroup B') (w : W) :
    (ι.isometryGroupExtend hB hB' g : V ≃ₗ[K] V) (ι w) = ι ((g : W ≃ₗ[K] W) w) := by
  rw [isometryGroupExtend_apply, orthogonalProjection_apply_left, map_sub, add_sub_cancel]

/-- On the orthogonal complement of the image of `ι`, the extension of `g` is the identity. -/
theorem isometryGroupExtend_apply_of_forall_eq_zero (ι : B' →bᵢ B) (hB : B.IsSymm)
    (hB' : B'.Nondegenerate) (g : isometryGroup B') {v : V} (hv : ∀ w, B v (ι w) = 0) :
    (ι.isometryGroupExtend hB hB' g : V ≃ₗ[K] V) v = v := by
  rw [isometryGroupExtend_apply, (ι.orthogonalProjection_eq_zero_iff hB' v).mpr hv, map_zero,
    sub_zero, map_zero, add_zero]

/-- Distinct isometries of `B'` have distinct extensions. -/
theorem isometryGroupExtend_injective (ι : B' →bᵢ B) (hB : B.IsSymm) (hB' : B'.Nondegenerate) :
    Function.Injective (ι.isometryGroupExtend hB hB') := by
  intro g h hgh
  ext w
  apply ι.injective hB'.1
  rw [← isometryGroupExtend_apply_left ι hB hB', hgh, isometryGroupExtend_apply_left]

end LinearMap.BilinForm.Isometry
