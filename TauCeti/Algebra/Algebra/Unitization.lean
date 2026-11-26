/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Star.MonoidHom
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Tactic.NoncommRing

/-!
# Functoriality of the forced unitization

A nonunital algebra `A` is a two-sided ideal of its forced unitization: `(r, a) * a'` is
`r • a' + a * a'` in `A`, and `a' * (r, a)` is `r • a' + a' * a`.

A homomorphism of nonunital algebras `f : A →ₙₐ[R] B` induces a unital algebra homomorphism
`Unitization R A →ₐ[R] Unitization R B`, sending `(r, a)` to `(r, f a)`. This is the non-star
counterpart of Mathlib's `Unitization.starMap`, and it is functorial.

For a unital algebra `B`, the map `x ↦ 1 + (x - 1_B)` is a unital multiplicative map
`B → Unitization R B` (a star monoid homomorphism when `B` is a star algebra). It acts on
`B ⊆ Unitization R B` by multiplication as `x` does, so it carries unitaries of `B` to unitaries
of the unitization implementing the same conjugation on `B`.

Star projections of a non-unital star algebra `A` that are conjugate by a unitary `u` of its
unitization are Murray–von Neumann equivalent in `A`, through the partial isometry `u * p ∈ A`.

## Main declarations

* `Unitization.mul_inr`, `Unitization.inr_mul_eq_inr`: `A` is a two-sided ideal of
  `Unitization R A`.
* `Unitization.inr_snd_of_fst_eq_zero`: an element with scalar part `0` lies in `A`.
* `Unitization.conjStar`: the element `u * x * star u` of `A`, for `u` in the unitization and
  `x : A`, with `Unitization.inr_conjStar`, `Unitization.conjStar_mul`,
  `Unitization.conjStar_smul`, `Unitization.star_conjStar`, `IsSelfAdjoint.conjStar` and
  `Unitization.conjStar_nonneg`.
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
* `Unitization.traceExtension`: the extension `(r, a) ↦ g r + f a` of an additive map `f` on `A`
  to the unitization, tracial when `f` is (`Unitization.traceExtension_mul_comm`).
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

/-- A nonunital algebra `A` is a right ideal of its unitization: `a * x` lies in `A`, with value
`x.fst • a + a * x.snd`. This mirrors `Unitization.mul_inr`; the name `Unitization.inr_mul` is
Mathlib's statement that `inr` is multiplicative. -/
theorem inr_mul_eq_inr {R A : Type*} [MulZeroClass R] [NonUnitalNonAssocSemiring A]
    [SMulWithZero R A] (a : A) (x : Unitization R A) :
    (inr a : Unitization R A) * x = inr (x.fst • a + a * x.snd) :=
  Unitization.ext (by simp) (by simp)

/-- An element of the unitization with scalar part `0` is the image of its `A`-part. -/
theorem inr_snd_of_fst_eq_zero {R A : Type*} [Zero R] {w : Unitization R A} (h : w.fst = 0) :
    (inr w.snd : Unitization R A) = w :=
  Unitization.ext (by simp [h]) rfl

section ConjStar

variable {R A : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
  [Module R A]

/-- The element `u * x * star u` of `A`, for `u` in the unitization `Unitization R A` and `x : A`:
the `A`-part of the product computed in the unitization, which lies in the ideal `A`. -/
def conjStar (u : Unitization R A) (x : A) : A :=
  (u * (x : Unitization R A) * star u).snd

/-- `u * x * star u` computed in the unitization is the image of `u.conjStar x`. -/
@[simp]
theorem inr_conjStar (u : Unitization R A) (x : A) :
    (inr (u.conjStar x) : Unitization R A) = u * (x : Unitization R A) * star u :=
  inr_snd_of_fst_eq_zero (by simp)

/-- Conjugation by `1` is the identity. -/
@[simp]
theorem conjStar_one [StarModule R A] (x : A) : (1 : Unitization R A).conjStar x = x :=
  inr_injective (R := R) (by simp)

variable [IsScalarTower R A A] [SMulCommClass R A A]

/-- Conjugation sends `0` to `0`. -/
@[simp]
theorem conjStar_zero (u : Unitization R A) : u.conjStar 0 = 0 :=
  inr_injective (R := R) (by simp)

/-- Conjugation is additive. -/
@[simp]
theorem conjStar_add (u : Unitization R A) (x y : A) :
    u.conjStar (x + y) = u.conjStar x + u.conjStar y :=
  inr_injective (R := R) (by simp [mul_add, add_mul])

/-- Conjugation commutes with scalar multiplication. -/
@[simp]
theorem conjStar_smul (u : Unitization R A) (r : R) (x : A) :
    u.conjStar (r • x) = r • u.conjStar x :=
  inr_injective (R := R) (by simp [inr_smul])

variable [StarModule R A]

/-- Conjugation commutes with `star`. -/
theorem star_conjStar (u : Unitization R A) (x : A) :
    star (u.conjStar x) = u.conjStar (star x) :=
  inr_injective (R := R) (by simp [inr_star, mul_assoc])

/-- Conjugation by an element of the unitization preserves self-adjointness. -/
theorem _root_.IsSelfAdjoint.conjStar {x : A} (hx : IsSelfAdjoint x) (u : Unitization R A) :
    IsSelfAdjoint (u.conjStar x) := by
  rw [IsSelfAdjoint, star_conjStar, hx.star_eq]

/-- Conjugation by a product is the composite of the conjugations. -/
theorem conjStar_mul (u v : Unitization R A) (x : A) :
    (u * v).conjStar x = u.conjStar (v.conjStar x) :=
  inr_injective (R := R) (by simp [mul_assoc])

/-- Conjugation by an element of the unitization preserves nonnegativity in a star-ordered `A`:
it sends `star s * s` to `star w * w` for `w = s * star u ∈ A`. -/
theorem conjStar_nonneg [PartialOrder A] [StarOrderedRing A] (u : Unitization R A) {x : A}
    (hx : 0 ≤ x) : 0 ≤ u.conjStar x := by
  induction hx using StarOrderedRing.induction_on with
  | star_mul_self s =>
    obtain ⟨w, hw⟩ : ∃ w : A, (w : Unitization R A) = s * star u :=
      ⟨_, (inr_mul_eq_inr s (star u)).symm⟩
    convert star_mul_self_nonneg w using 1
    exact inr_injective (R := R) (by simp [hw, mul_assoc])
  | zero => simp
  | add x y _ _ hx hy => simpa using add_nonneg hx hy

end ConjStar

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

section TraceExtension

variable {R A M : Type*} [AddCommMonoid R] [AddCommMonoid A] [AddCommMonoid M]

/-- The extension `f⁺ (r, a) = g r + f a` of an additive map `f : A →+ M` to the unitization,
with value `g` on the scalars. -/
def traceExtension (g : R →+ M) (f : A →+ M) : Unitization R A →+ M :=
  (g.coprod f).comp (addEquiv R A).toAddMonoidHom

@[simp]
theorem traceExtension_apply (g : R →+ M) (f : A →+ M) (x : Unitization R A) :
    traceExtension g f x = g x.fst + f x.snd :=
  (rfl)

end TraceExtension

section TraceExtensionMul

variable {R A M : Type*} [CommSemiring R] [NonUnitalSemiring A] [Module R A] [AddCommMonoid M]

/-- The extension of a tracial map to the unitization is tracial. -/
theorem traceExtension_mul_comm (g : R →+ M) {f : A →+ M}
    (hf : ∀ a b, f (a * b) = f (b * a)) (x y : Unitization R A) :
    traceExtension g f (x * y) = traceExtension g f (y * x) := by
  simp only [traceExtension_apply, fst_mul, snd_mul, map_add, hf x.snd y.snd, mul_comm x.fst y.fst]
  abel

end TraceExtensionMul

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
  have hv := (Unitization.mul_inr u p).symm
  refine ⟨u.fst • p + u.snd * p, Unitization.inr_injective (R := R) ?_,
    Unitization.inr_injective (R := R) ?_⟩
  · rw [Unitization.inr_mul, Unitization.inr_star, hv, star_mul, mul_assoc, ← mul_assoc (star u),
      Unitary.star_mul_self_of_mem hu, one_mul, ← Unitization.inr_star, ← Unitization.inr_mul,
      hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  · rw [Unitization.inr_mul, Unitization.inr_star, hv, star_mul, mul_assoc, ← mul_assoc _ (star _),
      ← Unitization.inr_star, ← Unitization.inr_mul, hp.isSelfAdjoint.star_eq,
      hp.isIdempotentElem.eq, ← mul_assoc, hupq]

end IsStarProjection
