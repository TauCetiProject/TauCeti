/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Unitization
public import Mathlib.RingTheory.Ideal.Maps

/-!
# Functoriality and splitting of the forced unitization

A homomorphism of nonunital algebras `f : A →ₙₐ[R] B` induces a unital algebra homomorphism
`Unitization R A →ₐ[R] Unitization R B`, sending `(r, a)` to `(r, f a)`. This is the non-star
counterpart of Mathlib's `Unitization.starMap`, and it is functorial.

The augmentation `Unitization.fstHom` (upgraded to `Unitization.fstStarAlgHom` in the star
setting) has kernel equal to the image of `Unitization.inr`. When `A` already has a multiplicative
identity, the forced unitization `Unitization R A` splits canonically as the direct product
`R × A` via `(r, a) ↦ (r, algebraMap R A r + a)`.

## Main declarations

* `Unitization.map`: the unital algebra homomorphism induced on forced unitizations.
* `Unitization.map_id`, `Unitization.map_comp`: functoriality.
* `Unitization.fstHom_comp_map`: the induced map preserves the augmentation.
* `Unitization.map_surjective`: the induced map of a surjective homomorphism is surjective.
* `Unitization.mem_range_inr_iff`, `Unitization.range_inr_eq_ker_fstHom`: the image of `inr` is
  the kernel `{x | x.fst = 0}` of the augmentation.
* `Unitization.fstStarAlgHom`: the augmentation `Unitization R A →⋆ₐ[R] R` as a unital
  `⋆`-algebra homomorphism.
* `Unitization.algEquivProd`, `Unitization.starAlgEquivProd`: the canonical algebra and
  `⋆`-algebra equivalences `Unitization R A ≃ₐ[R] R × A` and `Unitization R A ≃⋆ₐ[R] R × A`
  when `A` is unital.
-/

public section

namespace Unitization

section Map

variable {R A B : Type*} [CommSemiring R]
  [NonUnitalSemiring A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
  [NonUnitalSemiring B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]

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
theorem map_comp {C : Type*} [NonUnitalSemiring C] [Module R C] [IsScalarTower R C C]
    [SMulCommClass R C C] (f : A →ₙₐ[R] B) (g : B →ₙₐ[R] C) :
    map (g.comp f) = (map g).comp (map f) :=
  algHom_ext'' fun _ ↦ by simp

end Map

section AugmentationKernel

/-- An element of `Unitization R A` lies in the range of `inr` if and only if its scalar
coordinate vanishes. -/
theorem mem_range_inr_iff {R A : Type*} [Zero R] {x : Unitization R A} :
    x ∈ Set.range ((↑) : A → Unitization R A) ↔ x.fst = 0 :=
  ⟨by rintro ⟨a, rfl⟩; exact fst_inr R a,
    fun hx ↦ ⟨x.snd, Unitization.ext (hx.symm ▸ fst_inr R x.snd) (snd_inr R x.snd)⟩⟩

/-- An element of `Unitization R A` is the image of an element of `A` if and only if its scalar
coordinate vanishes. -/
@[simp]
theorem exists_inr_eq_iff {R A : Type*} [Zero R] {x : Unitization R A} :
    (∃ a : A, (a : Unitization R A) = x) ↔ x.fst = 0 :=
  mem_range_inr_iff

/-- Membership in the range of `inrNonUnitalStarAlgHom R A` is equivalent to vanishing of the
scalar coordinate. -/
theorem mem_range_inrNonUnitalStarAlgHom_iff {R A : Type*} [CommSemiring R] [StarAddMonoid R]
    [NonUnitalSemiring A] [Star A] [Module R A] {x : Unitization R A} :
    x ∈ NonUnitalStarAlgHom.range (inrNonUnitalStarAlgHom R A) ↔ x.fst = 0 := by
  simp

variable (R A : Type*) [CommRing R] [NonUnitalRing A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A]

/-- The image of `A` in `Unitization R A` is the kernel of the augmentation `fstHom R A`. -/
theorem range_inr_eq_ker_fstHom :
    Set.range ((↑) : A → Unitization R A) = (RingHom.ker (fstHom R A) : Set (Unitization R A)) := by
  ext x
  simp [RingHom.mem_ker]

/-- The nonunital subalgebra range of `inrNonUnitalAlgHom R A` has carrier equal to the kernel of
`fstHom R A`. -/
theorem coe_range_inrNonUnitalAlgHom :
    (NonUnitalAlgHom.range (inrNonUnitalAlgHom R A) : Set (Unitization R A)) =
      (RingHom.ker (fstHom R A) : Set (Unitization R A)) := by
  ext x
  simp [RingHom.mem_ker]

/-- The nonunital `⋆`-subalgebra range of `inrNonUnitalStarAlgHom R A` has carrier equal to the
kernel of `fstHom R A`. -/
theorem coe_range_inrNonUnitalStarAlgHom [StarAddMonoid R] [Star A] :
    (NonUnitalStarAlgHom.range (inrNonUnitalStarAlgHom R A) : Set (Unitization R A)) =
      (RingHom.ker (fstHom R A) : Set (Unitization R A)) := by
  ext x
  simp [RingHom.mem_ker]

end AugmentationKernel

section StarAugmentation

variable (R A : Type*) [CommSemiring R] [Star R] [NonUnitalSemiring A] [Star A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]

/-- The canonical augmentation `Unitization R A →⋆ₐ[R] R` projecting onto the scalar coordinate,
bundled as a unital `⋆`-algebra homomorphism. -/
def fstStarAlgHom : Unitization R A →⋆ₐ[R] R where
  toAlgHom := fstHom R A
  map_star' := fst_star

/-- `fstStarAlgHom R A` extracts the scalar coordinate. -/
@[simp]
theorem fstStarAlgHom_apply (x : Unitization R A) : fstStarAlgHom R A x = x.fst := by rfl

/-- Forgetting the star structure on `fstStarAlgHom R A` recovers `fstHom R A`. -/
@[simp]
theorem toAlgHom_fstStarAlgHom : (fstStarAlgHom R A).toAlgHom = fstHom R A := by rfl

/-- The `⋆`-map induced on unitizations preserves the `⋆`-augmentation. -/
@[simp]
theorem fstStarAlgHom_comp_starMap {R A B : Type*} [CommSemiring R] [StarRing R]
    [NonUnitalSemiring A] [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [NonUnitalSemiring B] [StarRing B] [Module R B] [IsScalarTower R B B] [SMulCommClass R B B]
    [StarModule R B] (f : A →⋆ₙₐ[R] B) :
    (fstStarAlgHom R B).comp (starMap f) = fstStarAlgHom R A :=
  StarAlgHom.ext fun x ↦ by simp [algebraMap_eq_inl]

end StarAugmentation

section SplitProd

variable (R A : Type*) [CommRing R] [Ring A] [Algebra R A]

/-- When `A` is already a unital `R`-algebra, its forced unitization `Unitization R A` splits
canonically as the product algebra `R × A` via `(r, a) ↦ (r, algebraMap R A r + a)`, with inverse
`(r, b) ↦ inl r + inr (b - algebraMap R A r)`. -/
def algEquivProd : Unitization R A ≃ₐ[R] R × A :=
  { (fstHom R A).prod (lift (AlgHom.id R A).toNonUnitalAlgHom) with
    toFun x := (x.fst, algebraMap R A x.fst + x.snd)
    invFun p := inl p.1 + inr (p.2 - algebraMap R A p.1)
    left_inv x := by ext <;> simp
    right_inv p := by ext <;> simp }

/-- `algEquivProd R A` sends `x` to `(x.fst, algebraMap R A x.fst + x.snd)`. -/
@[simp]
theorem algEquivProd_apply (x : Unitization R A) :
    algEquivProd R A x = (x.fst, algebraMap R A x.fst + x.snd) := by rfl

/-- `algEquivProd R A` sends a scalar `inl r` to `(r, algebraMap R A r)`. -/
theorem algEquivProd_inl (r : R) :
    algEquivProd R A (inl r) = (r, algebraMap R A r) := by
  simp [algEquivProd_apply]

/-- `algEquivProd R A` embeds `a : A` into the second factor `(0, a)`. -/
theorem algEquivProd_inr (a : A) :
    algEquivProd R A a = (0, a) := by
  simp [algEquivProd_apply]

/-- The inverse of `algEquivProd R A` sends `(r, b)` to `inl r + inr (b - algebraMap R A r)`. -/
@[simp]
theorem algEquivProd_symm_apply (p : R × A) :
    (algEquivProd R A).symm p = inl p.1 + inr (p.2 - algebraMap R A p.1) := by rfl

/-- Projecting onto the first factor after `algEquivProd R A` recovers `fstHom R A`. -/
@[simp]
theorem fst_comp_algEquivProd :
    (AlgHom.fst R R A).comp (algEquivProd R A).toAlgHom = fstHom R A :=
  AlgHom.ext fun _ ↦ by rfl

/-- When `A` is a unital `⋆`-algebra over a commutative `⋆`-ring `R`, the product splitting
`Unitization.algEquivProd R A` upgrades to a `⋆`-algebra equivalence
`Unitization R A ≃⋆ₐ[R] R × A`. -/
def starAlgEquivProd [StarRing R] [StarRing A] [StarModule R A] :
    Unitization R A ≃⋆ₐ[R] R × A where
  __ := algEquivProd R A
  map_smul' := map_smul (algEquivProd R A)
  map_star' x := by
    ext
    · simp
    · simp [Algebra.algebraMap_eq_smul_one]

/-- Forgetting the star structure on `starAlgEquivProd R A` recovers `algEquivProd R A`. -/
@[simp]
theorem toAlgEquiv_starAlgEquivProd [StarRing R] [StarRing A] [StarModule R A] :
    (starAlgEquivProd R A).toAlgEquiv = algEquivProd R A := by rfl

/-- `starAlgEquivProd R A` sends `x` to `(x.fst, algebraMap R A x.fst + x.snd)`. -/
@[simp]
theorem starAlgEquivProd_apply [StarRing R] [StarRing A] [StarModule R A]
    (x : Unitization R A) :
    starAlgEquivProd R A x = (x.fst, algebraMap R A x.fst + x.snd) := by rfl

/-- `starAlgEquivProd R A` sends a scalar `inl r` to `(r, algebraMap R A r)`. -/
theorem starAlgEquivProd_inl [StarRing R] [StarRing A] [StarModule R A] (r : R) :
    starAlgEquivProd R A (inl r) = (r, algebraMap R A r) :=
  algEquivProd_inl R A r

/-- `starAlgEquivProd R A` embeds `a : A` into the second factor `(0, a)`. -/
theorem starAlgEquivProd_inr [StarRing R] [StarRing A] [StarModule R A] (a : A) :
    starAlgEquivProd R A a = (0, a) :=
  algEquivProd_inr R A a

/-- The inverse of `starAlgEquivProd R A` sends `(r, b)` to
`inl r + inr (b - algebraMap R A r)`. -/
@[simp]
theorem starAlgEquivProd_symm_apply [StarRing R] [StarRing A] [StarModule R A] (p : R × A) :
    (starAlgEquivProd R A).symm p = inl p.1 + inr (p.2 - algebraMap R A p.1) := by rfl

/-- Projecting onto the first factor after `starAlgEquivProd R A` recovers `fstStarAlgHom R A`. -/
@[simp]
theorem fst_comp_starAlgEquivProd [StarRing R] [StarRing A] [StarModule R A] :
    (StarAlgHom.fst R R A).comp (starAlgEquivProd R A).toStarAlgHom = fstStarAlgHom R A :=
  StarAlgHom.ext fun _ ↦ by rfl

end SplitProd

end Unitization
