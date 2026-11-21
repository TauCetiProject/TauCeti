/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.Algebra.Star.MonoidHom
public import Mathlib.Tactic.NoncommRing

/-!
# Functoriality of the forced unitization

A homomorphism of nonunital algebras `f : A →ₙₐ[R] B` induces a unital algebra homomorphism
`Unitization R A →ₐ[R] Unitization R B`, sending `(r, a)` to `(r, f a)`. This is the non-star
counterpart of Mathlib's `Unitization.starMap`, and it is functorial.

For a unital algebra `B`, the map `x ↦ 1 + (x - 1_B)` is a unital multiplicative map
`B → Unitization R B` (a star monoid homomorphism when `B` is a star algebra). It acts on
`B ⊆ Unitization R B` by multiplication as `x` does, so it carries unitaries of `B` to unitaries
of the unitization implementing the same conjugation on `B`.

## Main declarations

* `Unitization.mul_inr_eq_inr`, `Unitization.inr_mul_eq_inr`: multiplying an embedded element
  `(a : Unitization R A)` on the left or right by an arbitrary element of `Unitization R A`
  stays in the embedded copy of `A`.
* `Unitization.map`: the unital algebra homomorphism induced on forced unitizations.
* `Unitization.map_id`, `Unitization.map_comp`: functoriality.
* `Unitization.fstHom_comp_map`: the induced map preserves the augmentation.
* `Unitization.map_surjective`: the induced map of a surjective homomorphism is surjective.
* `Unitization.fstAlgEquivOfSubsingleton`, `Unitization.fstStarAlgEquivOfSubsingleton`: when `A`
  is a subsingleton, the augmentation `Unitization.fstHom` upgrades to an algebra (or `⋆`-algebra)
  equivalence onto `R`.
* `Unitization.starLift_comp_inr`: the lift of a star homomorphism restricts to it on `A`.
* `Unitization.fst_smul_one_add_inr_snd`: decomposition of elements of `Unitization R A` as
  `x.fst • 1 + (x.snd : Unitization R A)`.
* `Unitization.oneAddInrSubOne`: for unital `B`, the star monoid homomorphism
  `x ↦ 1 + (x - 1_B)` from `B` to its unitization.
-/

public section

namespace Unitization

section MulInr

variable {R A : Type*} [MulZeroClass R] [AddZeroClass A] [Mul A] [SMulWithZero R A]

/-- Left-multiplying an embedded element `a : A` by `x : Unitization R A` yields the embedded
element `x.fst • a + x.snd * a`. -/
theorem mul_inr_eq_inr (x : Unitization R A) (a : A) :
    x * (a : Unitization R A) = ↑(x.fst • a + x.snd * a) :=
  Unitization.ext (mul_zero x.fst) <| by simp

/-- Right-multiplying an embedded element `a : A` by `x : Unitization R A` yields the embedded
element `x.fst • a + a * x.snd`. -/
theorem inr_mul_eq_inr (a : A) (x : Unitization R A) :
    (a : Unitization R A) * x = ↑(x.fst • a + a * x.snd) :=
  Unitization.ext (zero_mul x.fst) <| by simp

end MulInr

section Decomposition

/-- Every element of `Unitization R A` decomposes as `x.fst • 1 + (x.snd : Unitization R A)`. -/
theorem fst_smul_one_add_inr_snd {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A]
    (x : Unitization R A) :
    x.fst • (1 : Unitization R A) + (x.snd : Unitization R A) = x :=
  Unitization.ext (by simp) (by simp)

end Decomposition

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
