/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Star.StarRingHom
public import TauCeti.LinearAlgebra.Matrix.ProjectionMonoid.KZero

/-!
# The projection monoid and `K₀` of a product

A matrix over `R × S` is a pair of matrices over `R` and over `S`, and a matrix projection over
`R × S` is the orthogonal sum of its two components, embedded through `R → R × S` and
`S → R × S` (`TauCeti.ProjectionMonoid.map_inl_map_fst_add_map_inr_map_snd`). Since orthogonal
projections have additive classes (`TauCeti.ProjectionMonoid.mk_add_of_mul_eq_zero`), the
projections `R × S → R` and `R × S → S` induce isomorphisms `V(R × S) ≃+ V(R) × V(S)`
(`TauCeti.ProjectionMonoid.prodEquiv`) and `K₀(R × S) ≃+ K₀(R) × K₀(S)`
(`TauCeti.ProjectionKZero.prodEquiv`), with inverses induced by the inclusions.

## Main statements

* `TauCeti.ProjectionMonoid.map_inl_map_fst_add_map_inr_map_snd`: every class in `V(R × S)` is
  the sum of the images under the inclusions of its images under the two projections.
* `TauCeti.ProjectionMonoid.prodEquiv`: `V(R × S) ≃+ V(R) × V(S)`.
* `TauCeti.ProjectionKZero.prodEquiv`: `K₀(R × S) ≃+ K₀(R) × K₀(S)`.
* `TauCeti.ProjectionKZero.map_inl_map_fst_add_map_inr_map_snd`: the same decomposition of a
  class in `K₀(R × S)`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  §5.2.
-/

public section

open Matrix Algebra

namespace TauCeti

variable {R S : Type*} [NonUnitalSemiring R] [StarRing R] [NonUnitalSemiring S] [StarRing S]

namespace ProjectionMonoid

variable {m : Type*} [Fintype m]

/-- The first projection undoes the first inclusion on `V`. -/
@[simp]
theorem map_fst_map_inl (x : ProjectionMonoid R) :
    map (NonUnitalStarRingHom.fst R S) (map (NonUnitalStarRingHom.inl R S) x) = x := by
  rw [map_map, NonUnitalStarRingHom.fst_comp_inl, map_id, AddMonoidHom.id_apply]

/-- The second projection undoes the second inclusion on `V`. -/
@[simp]
theorem map_snd_map_inr (y : ProjectionMonoid S) :
    map (NonUnitalStarRingHom.snd R S) (map (NonUnitalStarRingHom.inr R S) y) = y := by
  rw [map_map, NonUnitalStarRingHom.snd_comp_inr, map_id, AddMonoidHom.id_apply]

/-- The first projection kills the image of the second inclusion on `V`. -/
@[simp]
theorem map_fst_map_inr (y : ProjectionMonoid S) :
    map (NonUnitalStarRingHom.fst R S) (map (NonUnitalStarRingHom.inr R S) y) = 0 := by
  rw [map_map, NonUnitalStarRingHom.fst_comp_inr]
  exact map_eq_zero_of_forall_eq_zero NonUnitalStarRingHom.zero_apply y

/-- The second projection kills the image of the first inclusion on `V`. -/
@[simp]
theorem map_snd_map_inl (x : ProjectionMonoid R) :
    map (NonUnitalStarRingHom.snd R S) (map (NonUnitalStarRingHom.inl R S) x) = 0 := by
  rw [map_map, NonUnitalStarRingHom.snd_comp_inl]
  exact map_eq_zero_of_forall_eq_zero NonUnitalStarRingHom.zero_apply x

/-- Every class in `V(R × S)` is the sum of the images under the inclusions of its images under
the two projections. -/
theorem map_inl_map_fst_add_map_inr_map_snd (x : ProjectionMonoid (R × S)) :
    map (NonUnitalStarRingHom.inl R S) (map (NonUnitalStarRingHom.fst R S) x) +
      map (NonUnitalStarRingHom.inr R S) (map (NonUnitalStarRingHom.snd R S) x) = x := by
  induction x using ind with
  | mk _ p hp =>
    simp only [map_mk, Matrix.map_map]
    rw [← mk_add_of_mul_eq_zero _ _ (by
      ext i j <;> simp [Matrix.mul_apply])]
    congr 1
    ext i j <;> simp

variable (R S) in
/-- **The projection monoid of a product**: `V(R × S) ≃+ V(R) × V(S)`, induced by the two
projections, with inverse induced by the two inclusions. -/
noncomputable def prodEquiv : ProjectionMonoid (R × S) ≃+ ProjectionMonoid R × ProjectionMonoid S
    where
  toFun x := (map (NonUnitalStarRingHom.fst R S) x, map (NonUnitalStarRingHom.snd R S) x)
  invFun y := map (NonUnitalStarRingHom.inl R S) y.1 + map (NonUnitalStarRingHom.inr R S) y.2
  left_inv := map_inl_map_fst_add_map_inr_map_snd
  right_inv y := by simp
  map_add' x y := by simp

/-- The isomorphism `V(R × S) ≃+ V(R) × V(S)` is induced by the two projections. -/
@[simp]
theorem prodEquiv_apply (x : ProjectionMonoid (R × S)) :
    prodEquiv R S x =
      (map (NonUnitalStarRingHom.fst R S) x, map (NonUnitalStarRingHom.snd R S) x) :=
  (rfl)

/-- The class in `V(R) × V(S)` of a matrix projection over `R × S` is the pair of the classes of
its components. -/
theorem prodEquiv_mk {p : Matrix m m (R × S)} (hp : IsStarProjection p) :
    prodEquiv R S (mk p hp) =
      (mk (p.map (NonUnitalStarRingHom.fst R S)) (hp.matrix_map _),
        mk (p.map (NonUnitalStarRingHom.snd R S)) (hp.matrix_map _)) :=
  Prod.ext (map_mk _ hp) (map_mk _ hp)

/-- The inverse of `V(R × S) ≃+ V(R) × V(S)` is induced by the two inclusions. -/
@[simp]
theorem prodEquiv_symm_apply (y : ProjectionMonoid R × ProjectionMonoid S) :
    (prodEquiv R S).symm y =
      map (NonUnitalStarRingHom.inl R S) y.1 + map (NonUnitalStarRingHom.inr R S) y.2 :=
  (rfl)

end ProjectionMonoid

namespace ProjectionKZero

open ProjectionMonoid

/-- The first projection undoes the first inclusion on `K₀`. -/
@[simp]
theorem map_fst_map_inl (x : ProjectionKZero R) :
    map (NonUnitalStarRingHom.fst R S) (map (NonUnitalStarRingHom.inl R S) x) = x := by
  rw [map_map, NonUnitalStarRingHom.fst_comp_inl, map_id, AddMonoidHom.id_apply]

/-- The second projection undoes the second inclusion on `K₀`. -/
@[simp]
theorem map_snd_map_inr (y : ProjectionKZero S) :
    map (NonUnitalStarRingHom.snd R S) (map (NonUnitalStarRingHom.inr R S) y) = y := by
  rw [map_map, NonUnitalStarRingHom.snd_comp_inr, map_id, AddMonoidHom.id_apply]

/-- The first projection kills the image of the second inclusion on `K₀`. -/
@[simp]
theorem map_fst_map_inr (y : ProjectionKZero S) :
    map (NonUnitalStarRingHom.fst R S) (map (NonUnitalStarRingHom.inr R S) y) = 0 := by
  rw [map_map, NonUnitalStarRingHom.fst_comp_inr,
    map_eq_zero_of_forall_eq_zero NonUnitalStarRingHom.zero_apply, AddMonoidHom.zero_apply]

/-- The second projection kills the image of the first inclusion on `K₀`. -/
@[simp]
theorem map_snd_map_inl (x : ProjectionKZero R) :
    map (NonUnitalStarRingHom.snd R S) (map (NonUnitalStarRingHom.inl R S) x) = 0 := by
  rw [map_map, NonUnitalStarRingHom.snd_comp_inl,
    map_eq_zero_of_forall_eq_zero NonUnitalStarRingHom.zero_apply, AddMonoidHom.zero_apply]

variable (R S) in
/-- **`K₀` of a product**: `K₀(R × S) ≃+ K₀(R) × K₀(S)`, induced by the two projections, with
inverse induced by the two inclusions. -/
noncomputable def prodEquiv : ProjectionKZero (R × S) ≃+ ProjectionKZero R × ProjectionKZero S :=
  AddMonoidHom.toAddEquiv
    ((map (NonUnitalStarRingHom.fst R S)).prod (map (NonUnitalStarRingHom.snd R S)))
    ((map (NonUnitalStarRingHom.inl R S)).coprod (map (NonUnitalStarRingHom.inr R S)))
    (GrothendieckAddGroup.addHom_ext fun x ↦ by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.prod_apply, AddMonoidHom.coprod_apply,
        map_of, ← map_add, map_inl_map_fst_add_map_inr_map_snd, AddMonoidHom.id_apply])
    (AddMonoidHom.ext fun y ↦ by simp)

/-- The isomorphism `K₀(R × S) ≃+ K₀(R) × K₀(S)` is induced by the two projections. -/
@[simp]
theorem prodEquiv_apply (x : ProjectionKZero (R × S)) :
    prodEquiv R S x =
      (map (NonUnitalStarRingHom.fst R S) x, map (NonUnitalStarRingHom.snd R S) x) :=
  (rfl)

/-- The inverse of `K₀(R × S) ≃+ K₀(R) × K₀(S)` is induced by the two inclusions. -/
@[simp]
theorem prodEquiv_symm_apply (y : ProjectionKZero R × ProjectionKZero S) :
    (prodEquiv R S).symm y =
      map (NonUnitalStarRingHom.inl R S) y.1 + map (NonUnitalStarRingHom.inr R S) y.2 :=
  (rfl)

/-- Every class in `K₀(R × S)` is the sum of the images under the inclusions of its images under
the two projections. -/
theorem map_inl_map_fst_add_map_inr_map_snd (x : ProjectionKZero (R × S)) :
    map (NonUnitalStarRingHom.inl R S) (map (NonUnitalStarRingHom.fst R S) x) +
      map (NonUnitalStarRingHom.inr R S) (map (NonUnitalStarRingHom.snd R S) x) = x :=
  (prodEquiv R S).symm_apply_apply x

-- Not `@[simp]`: the simp normal form of `Algebra.GrothendieckAddGroup.of x` is
-- `AddLocalization.addMonoidOf ⊤ x`, as for `TauCeti.ProjectionKZero.map_of_mk`.
/-- The class in `K₀(R) × K₀(S)` of a matrix projection over `R × S` is the pair of the classes
of its components. -/
theorem prodEquiv_of_mk {m : Type*} [Fintype m] {p : Matrix m m (R × S)}
    (hp : IsStarProjection p) :
    prodEquiv R S (GrothendieckAddGroup.of (mk p hp)) =
      (GrothendieckAddGroup.of (mk (p.map (NonUnitalStarRingHom.fst R S)) (hp.matrix_map _)),
        GrothendieckAddGroup.of
          (mk (p.map (NonUnitalStarRingHom.snd R S)) (hp.matrix_map _))) :=
  Prod.ext (map_of_mk _ hp) (map_of_mk _ hp)

end ProjectionKZero

end TauCeti
