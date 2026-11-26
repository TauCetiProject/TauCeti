/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Algebra.Star.MonoidHom
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Tactic.NoncommRing

/-!
# Functoriality of the forced unitization

A nonunital algebra `A` is a left ideal of its forced unitization: `(r, a) * a'` is
`r • a' + a * a'` in `A`.

A homomorphism of nonunital algebras `f : A →ₙₐ[R] B` induces a unital algebra homomorphism
`Unitization R A →ₐ[R] Unitization R B`, sending `(r, a)` to `(r, f a)`. This is the non-star
counterpart of Mathlib's `Unitization.starMap`, and it is functorial.

For a unital algebra `B`, the forced unitization is the product algebra `B × R`, through
`(r, b) ↦ (r • 1 + b, r)`: forcing a new unit onto `B` adds a copy of the scalars.

For a unital algebra `B`, the map `x ↦ 1 + (x - 1_B)` is a unital multiplicative map
`B → Unitization R B` (a star monoid homomorphism when `B` is a star algebra). It acts on
`B ⊆ Unitization R B` by multiplication as `x` does, so it carries unitaries of `B` to unitaries
of the unitization implementing the same conjugation on `B`.

Star projections of a non-unital star algebra `A` that are conjugate by a unitary `u` of its
unitization are Murray–von Neumann equivalent in `A`, through the partial isometry `u * p ∈ A`.

## Main declarations

* `Unitization.mul_inr`: `A` is a left ideal of `Unitization R A`.
* `Unitization.map`: the unital algebra homomorphism induced on forced unitizations.
* `Unitization.map_id`, `Unitization.map_comp`: functoriality.
* `Unitization.fstHom_comp_map`: the induced map preserves the augmentation.
* `Unitization.map_surjective`: the induced map of a surjective homomorphism is surjective.
* `Unitization.mapScalars`: for an algebra `R → S` and an `S`-algebra `A`, the map
  `Unitization R A → Unitization S A`, `(r, a) ↦ (algebraMap R S r, a)`.
* `Unitization.fstHom_comp_mapScalars`, `Unitization.mapScalars_map`: change of scalars lies over
  `algebraMap R S` on the augmentations and commutes with `Unitization.map`.
* `Unitization.fstStarAlgHom`: the augmentation `(r, a) ↦ r` as a star algebra homomorphism.
* `Unitization.fstAlgEquivOfSubsingleton`, `Unitization.fstStarAlgEquivOfSubsingleton`: when `A`
  is a subsingleton, the augmentation `Unitization.fstHom` upgrades to an algebra (or `⋆`-algebra)
  equivalence onto `R`.
* `Unitization.prodAlgEquiv`: for a unital algebra `A`, the splitting
  `Unitization R A ≃ₐ[R] A × R`, `(r, a) ↦ (r • 1 + a, r)`, whose components are the lift of the
  identity and the augmentation (`Unitization.fst_comp_prodAlgEquiv`,
  `Unitization.snd_comp_prodAlgEquiv`).
* `Unitization.starLift_comp_inr`: the lift of a star homomorphism restricts to it on `A`.
* `Unitization.oneAddInrSubOne`: for unital `B`, the star monoid homomorphism
  `x ↦ 1 + (x - 1_B)` from `B` to its unitization.
* `IsStarProjection.exists_star_mul_self_eq_of_mem_unitary_unitization`: projections of a
  non-unital star algebra that are conjugate by a unitary of its unitization are Murray–von
  Neumann equivalent.
-/

public section

namespace Unitization

/-- A nonunital algebra `A` is a left ideal of its unitization: `x * a` lies in `A`, with value
`x.fst • a + x.snd * a`. -/
theorem mul_inr {R A : Type*} [MulZeroClass R] [NonUnitalNonAssocSemiring A]
    [SMulWithZero R A] (x : Unitization R A) (a : A) : x * inr a = inr (x.fst • a + x.snd * a) :=
  Unitization.ext (by simp) (by simp)

section Map

variable {R A B C : Type*} [CommSemiring R]
  [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
  [NonUnitalSemiring C] [Module R C] [IsScalarTower R C C] [SMulCommClass R C C]

/-- The unital algebra homomorphism between forced unitizations induced by a homomorphism of
nonunital algebras. -/
def map (f : A →ₙₐ[R] B) : Unitization R A →ₐ[R] Unitization R B :=
  lift ((inrNonUnitalAlgHom R B).comp f)

/-- The induced map of unitizations restricts to the original nonunital algebra homomorphism. -/
@[simp]
theorem map_inr (f : A →ₙₐ[R] B) (a : A) : map f (inr a) = inr (f a) := by simp [map]

/-- The induced map of unitizations is the identity on scalars. -/
@[simp]
theorem map_inl (f : A →ₙₐ[R] B) (r : R) :
    map f (inl r : Unitization R A) = algebraMap R (Unitization R B) r := by simp [map]

/-- The scalar component of the induced map of unitizations is unchanged. -/
@[simp]
theorem fst_map (f : A →ₙₐ[R] B) (x : Unitization R A) : (map f x).fst = x.fst := by
  simp [map, algebraMap_eq_inl]

/-- The nonunital-algebra component of the induced map of unitizations is obtained by applying the
original homomorphism. -/
@[simp]
theorem snd_map (f : A →ₙₐ[R] B) (x : Unitization R A) : (map f x).snd = f x.snd := by
  simp [map, algebraMap_eq_inl]

/-- The induced map of forced unitizations preserves the augmentation `(r, a) ↦ r`. -/
@[simp]
theorem fstHom_comp_map (f : A →ₙₐ[R] B) : (fstHom R B).comp (map f) = fstHom R A :=
  AlgHom.ext fun x ↦ by simp

/-- A surjective homomorphism of nonunital algebras induces a surjective homomorphism of forced
unitizations: `(r, b)` is the image of `(r, a)` for any preimage `a` of `b`. -/
theorem map_surjective {f : A →ₙₐ[R] B} (hf : Function.Surjective f) :
    Function.Surjective (map f) := fun y ↦ by
  obtain ⟨a, ha⟩ := hf y.snd
  exact ⟨inl y.fst + inr a,
    Unitization.ext (by rw [fst_map]; simp) (by rw [snd_map]; simp [ha])⟩

/-- The identity homomorphism induces the identity homomorphism of forced unitizations. -/
@[simp]
theorem map_id : map (NonUnitalAlgHom.id R A) = AlgHom.id R (Unitization R A) :=
  algHom_ext'' fun _ ↦ by simp

/-- Unitization preserves composition of nonunital algebra homomorphisms. -/
theorem map_comp (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) : map (g.comp f) = (map g).comp (map f) :=
  algHom_ext'' fun _ ↦ by simp

end Map

section MapScalars

variable (R S A : Type*) {B : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  [NonUnitalSemiring A] [Module S A] [IsScalarTower S A A] [SMulCommClass S A A] [Module R A]
  [IsScalarTower R S A] [IsScalarTower R A A] [SMulCommClass R A A]

/-- Change of the scalar ring of a forced unitization: for an algebra `R → S` and an `S`-algebra
`A`, the unital `R`-algebra homomorphism `Unitization R A → Unitization S A` sending `(r, a)` to
`(algebraMap R S r, a)`. -/
def mapScalars : Unitization R A →ₐ[R] Unitization S A :=
  lift ((inrNonUnitalAlgHom S A).restrictScalars R)

variable {R S A}

/-- Change of scalars of forced unitizations is the identity on `A`. -/
@[simp]
theorem mapScalars_inr (a : A) : mapScalars R S A (inr a : Unitization R A) = inr a := by
  simp [mapScalars]

/-- Change of scalars of forced unitizations applies `algebraMap R S` to the scalar component. -/
@[simp]
theorem fst_mapScalars (x : Unitization R A) :
    (mapScalars R S A x).fst = algebraMap R S x.fst := by
  simp [mapScalars, Algebra.algebraMap_eq_smul_one]

/-- Change of scalars of forced unitizations leaves the component in `A` unchanged. -/
@[simp]
theorem snd_mapScalars (x : Unitization R A) : (mapScalars R S A x).snd = x.snd := by
  simp [mapScalars, Algebra.algebraMap_eq_smul_one]

/-- Change of scalars of forced unitizations lies over `algebraMap R S` on the augmentations. -/
@[simp]
theorem fstHom_comp_mapScalars :
    (fstHom S A : Unitization S A →+* S).comp
        (mapScalars R S A : Unitization R A →+* Unitization S A) =
      (algebraMap R S).comp (fstHom R A : Unitization R A →+* R) :=
  RingHom.ext fun x ↦ by simp

/-- Change of scalars of forced unitizations commutes with the maps induced by homomorphisms of
nonunital `S`-algebras. -/
theorem mapScalars_map [NonUnitalSemiring B] [Module S B] [IsScalarTower S B B]
    [SMulCommClass S B B] [Module R B] [IsScalarTower R S B] [IsScalarTower R B B]
    [SMulCommClass R B B] (f : A →ₙₐ[S] B) (x : Unitization R A) :
    mapScalars R S B (map (f.restrictScalars R) x) = map f (mapScalars R S A x) :=
  Unitization.ext (by simp) (by simp)

end MapScalars

section Augmentation

variable (R A : Type*) [CommSemiring R] [Star R] [NonUnitalSemiring A] [Star A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- The augmentation `Unitization R A → R`, `(r, a) ↦ r`, as a star algebra homomorphism. -/
def fstStarAlgHom : Unitization R A →⋆ₐ[R] R where
  toAlgHom := fstHom R A
  map_star' := fst_star

/-- The augmentation sends `(r, a)` to `r`. -/
@[simp]
theorem fstStarAlgHom_apply (x : Unitization R A) : fstStarAlgHom R A x = x.fst :=
  (rfl)

end Augmentation

section Subsingleton

variable {R A : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [Subsingleton A]

variable (R A) in
/-- When `A` is a subsingleton, the augmentation `Unitization.fstHom` upgrades to an algebra
equivalence `Unitization R A ≃ₐ[R] R` with inverse `Unitization.inl`. -/
def fstAlgEquivOfSubsingleton : Unitization R A ≃ₐ[R] R :=
  { fstHom R A with
    invFun := inl
    left_inv := fun _ ↦ Unitization.ext (by simp) (Subsingleton.elim _ _)
    right_inv := fst_inl A }

@[simp]
theorem fstAlgEquivOfSubsingleton_apply (u : Unitization R A) :
    fstAlgEquivOfSubsingleton R A u = u.fst := (rfl)

@[simp]
theorem fstAlgEquivOfSubsingleton_symm_apply (r : R) :
    (fstAlgEquivOfSubsingleton R A).symm r = inl r := (rfl)

variable (R A) in
/-- When `A` is a subsingleton, the augmentation `Unitization.fstHom` upgrades to a `⋆`-algebra
equivalence `Unitization R A ≃⋆ₐ[R] R` with inverse `Unitization.inl`. -/
def fstStarAlgEquivOfSubsingleton [Star R] [Star A] : Unitization R A ≃⋆ₐ[R] R :=
  { fstAlgEquivOfSubsingleton R A with
    map_smul' := map_smul (fstHom R A)
    map_star' := fun _ ↦ by simp }

@[simp]
theorem fstStarAlgEquivOfSubsingleton_apply [Star R] [Star A] (u : Unitization R A) :
    fstStarAlgEquivOfSubsingleton R A u = u.fst := (rfl)

@[simp]
theorem fstStarAlgEquivOfSubsingleton_symm_apply [Star R] [Star A] (r : R) :
    (fstStarAlgEquivOfSubsingleton R A).symm r = inl r := (rfl)

end Subsingleton

section Unital

variable (R A : Type*) [CommSemiring R] [Ring A] [Algebra R A]

/-- For a unital algebra `A`, the forced unitization splits as a product:
`Unitization R A ≃ₐ[R] A × R`, `(r, a) ↦ (r • 1 + a, r)`, with inverse
`(b, r) ↦ (r, b - r • 1)`. Its components are `Unitization.lift` of the identity and the
augmentation `Unitization.fstHom`. -/
def prodAlgEquiv : Unitization R A ≃ₐ[R] A × R where
  toFun x := (lift (NonUnitalAlgHom.id R A) x, x.fst)
  invFun y := inl y.2 + inr (y.1 - algebraMap R A y.2)
  left_inv x := by ext <;> simp
  right_inv y := by ext <;> simp
  map_mul' x y := Prod.ext (map_mul (lift (NonUnitalAlgHom.id R A)) x y) (fst_mul x y)
  map_add' x y := Prod.ext (map_add (lift (NonUnitalAlgHom.id R A)) x y) (fst_add x y)
  commutes' r := Prod.ext (by simp) (by simp)

variable {R A}

/-- The splitting `Unitization R A ≃ₐ[R] A × R` sends `(r, a)` to `(r • 1 + a, r)`. -/
@[simp]
theorem prodAlgEquiv_apply (x : Unitization R A) :
    prodAlgEquiv R A x = (algebraMap R A x.fst + x.snd, x.fst) := by
  simp [prodAlgEquiv]

/-- The inverse of the splitting `Unitization R A ≃ₐ[R] A × R` sends `(b, r)` to
`(r, b - r • 1)`. -/
@[simp]
theorem prodAlgEquiv_symm_apply (y : A × R) :
    (prodAlgEquiv R A).symm y = inl y.2 + inr (y.1 - algebraMap R A y.2) :=
  (rfl)

/-- The first component of the splitting `Unitization R A ≃ₐ[R] A × R` is the map
`(r, a) ↦ r • 1 + a`, the lift of the identity of `A`. -/
@[simp]
theorem fst_comp_prodAlgEquiv :
    (RingHom.fst A R).comp (prodAlgEquiv R A : Unitization R A →+* A × R) =
      (lift (NonUnitalAlgHom.id R A) : Unitization R A →+* A) :=
  RingHom.ext fun x ↦ by simp

/-- The second component of the splitting `Unitization R A ≃ₐ[R] A × R` is the augmentation. -/
@[simp]
theorem snd_comp_prodAlgEquiv :
    (RingHom.snd A R).comp (prodAlgEquiv R A : Unitization R A →+* A × R) =
      (fstHom R A : Unitization R A →+* R) :=
  RingHom.ext fun x ↦ by simp

/-- Through the splitting `Unitization R A ≃ₐ[R] A × R`, the lift of the identity of `A` is the
first projection. -/
-- Not `@[simp]`: `Unitization.lift_apply` rewrites the left-hand side.
theorem lift_comp_prodAlgEquiv_symm :
    (lift (NonUnitalAlgHom.id R A) : Unitization R A →+* A).comp
        ((prodAlgEquiv R A).symm : A × R →+* Unitization R A) = RingHom.fst A R :=
  RingHom.ext fun y ↦ by simp

/-- Through the splitting `Unitization R A ≃ₐ[R] A × R`, the augmentation is the second
projection. -/
@[simp]
theorem fstHom_comp_prodAlgEquiv_symm :
    (fstHom R A : Unitization R A →+* R).comp
        ((prodAlgEquiv R A).symm : A × R →+* Unitization R A) = RingHom.snd A R :=
  RingHom.ext fun y ↦ by simp

end Unital

end Unitization

namespace Unitization

variable {R A C : Type*} [CommSemiring R] [StarRing R]
  [NonUnitalSemiring A] [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [Semiring C] [Algebra R C] [StarRing C] [StarModule R C]

/-- The lift of a star homomorphism to the unitization restricts to it on the nonunital
algebra. -/
theorem starLift_comp_inr (φ : A →⋆ₙₐ[R] C) :
    (starLift φ).toNonUnitalStarAlgHom.comp (inrNonUnitalStarAlgHom R A) = φ := by
  rw [← starLift_symm_apply, Equiv.symm_apply_apply]

end Unitization

namespace Unitization

variable {R B : Type*} [CommRing R] [StarRing R] [Ring B] [StarRing B] [Module R B]
  [IsScalarTower R B B] [SMulCommClass R B B] [StarModule R B]

/-- For a unital algebra `B`, the unital multiplicative map `B → Unitization R B` sending `x` to
`1 + (x - 1_B)`. It maps unitaries of `B` to unitaries of the unitization acting on `B` by the
same conjugation. -/
noncomputable def oneAddInrSubOne : B →⋆* Unitization R B where
  toFun x := 1 + inr (x - 1)
  map_one' := by simp
  map_mul' x y := by
    ext
    · simp
    · simp only [snd_mul, fst_add, snd_add, fst_one, snd_one, fst_inr, snd_inr]
      simp only [add_zero, zero_add, one_smul]
      noncomm_ring
  map_star' x := by simp [← inr_star]

/-- `Unitization.oneAddInrSubOne` sends `x` to `1 + (x - 1_B)`. -/
@[simp]
theorem oneAddInrSubOne_apply (x : B) :
    oneAddInrSubOne x = (1 + inr (x - 1) : Unitization R B) := by
  rfl

/-- Left multiplication by `oneAddInrSubOne x` acts on `B` as left multiplication by `x`. -/
theorem oneAddInrSubOne_mul_inr (x c : B) :
    (oneAddInrSubOne x : Unitization R B) * inr c = inr (x * c) := by
  simp [add_mul, sub_mul, ← inr_mul]

/-- Right multiplication by `oneAddInrSubOne x` acts on `B` as right multiplication by `x`. -/
theorem inr_mul_oneAddInrSubOne (c x : B) :
    (inr c : Unitization R B) * oneAddInrSubOne x = inr (c * x) := by
  simp [mul_add, mul_sub, ← inr_mul]

end Unitization

namespace IsStarProjection

/-- Star projections `p` and `q` of a non-unital star algebra `A` that are conjugate by a unitary
of its unitization are Murray–von Neumann equivalent in `A`: `v = u * p` lies in `A`, with
`star v * v = p` and `v * star v = q`. -/
theorem exists_star_mul_self_eq_of_mem_unitary_unitization {R A : Type*} [CommSemiring R]
    [StarRing R] [NonUnitalSemiring A] [StarRing A] [Module R A] [IsScalarTower R A A]
    [SMulCommClass R A A] [StarModule R A] {p q : A} (hp : IsStarProjection p)
    {u : Unitization R A} (hu : u ∈ unitary (Unitization R A))
    (hupq : u * (p : Unitization R A) * star u = q) :
    ∃ v : A, star v * v = p ∧ v * star v = q := by
  have hv : ((u * (p : Unitization R A)).snd : Unitization R A) = u * p := by
    ext
    · rw [Unitization.fst_inr, Unitization.fst_mul, Unitization.fst_inr, mul_zero]
    · rw [Unitization.snd_inr]
  refine ⟨(u * (p : Unitization R A)).snd, Unitization.inr_injective (R := R) ?_,
    Unitization.inr_injective (R := R) ?_⟩
  · rw [Unitization.inr_mul, Unitization.inr_star, hv, star_mul, mul_assoc, ← mul_assoc (star u),
      Unitary.star_mul_self_of_mem hu, one_mul, ← Unitization.inr_star, ← Unitization.inr_mul,
      hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  · rw [Unitization.inr_mul, Unitization.inr_star, hv, star_mul, mul_assoc, ← mul_assoc _ (star _),
      ← Unitization.inr_star, ← Unitization.inr_mul, hp.isSelfAdjoint.star_eq,
      hp.isIdempotentElem.eq, ← mul_assoc, hupq]

end IsStarProjection
