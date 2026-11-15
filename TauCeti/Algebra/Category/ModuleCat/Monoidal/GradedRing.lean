/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.DirectSum.Algebra

/-!
# Graded rings from homogeneous multiplications of modules

Let `M : ι → ModuleCat R` be a family of `R`-modules indexed by an additive monoid, equipped
with a unit `one : R ⟶ M 0` and homogeneous multiplications `mul i j : M i ⊗ M j ⟶ M (i + j)`
satisfying the graded unit and associativity laws, stated up to the identifications of degrees
`0 + n = n`, `n + 0 = n` and `i + j + k = i + (j + k)`. These are the laws of a monoid object in
graded `R`-modules, written degree by degree. This file turns such data into Mathlib's graded
ring structure on the family of carriers:

* `TauCeti.ModuleCat.gRingOfHomogeneous`: the `DirectSum.GRing` structure whose homogeneous
  product of `a : M i` and `b : M j` is `mul i j (a ⊗ₜ b)` and whose unit is `one 1`;
* `TauCeti.ModuleCat.gCommRingOfHomogeneous`: the `DirectSum.GCommRing` structure, when the
  homogeneous multiplications are moreover graded commutative;
* `TauCeti.ModuleCat.gAlgebraOfHomogeneous`: the `DirectSum.GAlgebra R` structure whose
  structure map is `one`.

Through Mathlib's instances on direct sums these make `⨁ i, M i` a (commutative) `R`-algebra in
which `DirectSum.of _ i a * DirectSum.of _ j b = DirectSum.of _ (i + j) (mul i j (a ⊗ₜ b))`.
This is the graded analogue of `ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toRing`, which
makes a monoid object of `ModuleCat R` a ring. Its main use is to give rings of sections of a
graded algebra of sheaves of modules their graded multiplication.

None of these structures is an instance, since the homogeneous multiplication is data that is
not determined by the family `M`.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti.ModuleCat

universe u v

variable {R : Type u} {ι : Type*}

/-- Transporting an element along an identification of degrees does not change the element of
the graded monoid. -/
lemma gradedMonoid_mk_eqToHom_hom [Ring R] (M : ι → ModuleCat.{v} R) {n m : ι}
    (h : n = m) (x : M n) :
    GradedMonoid.mk (A := fun i ↦ M i) m ((eqToHom (congrArg M h)).hom x) =
      GradedMonoid.mk n x := by
  subst h
  rfl

variable [CommRing R]

section AddZeroClass

variable [AddZeroClass ι] {M : ι → ModuleCat.{u} R} {one : 𝟙_ (ModuleCat.{u} R) ⟶ M 0}
  {mul : ∀ i j, M i ⊗ M j ⟶ M (i + j)}

/-- The left unit law, applied to `r ⊗ₜ a`: multiplying by the image of `r` in degree zero is
scalar multiplication by `r`, as elements of the graded monoid. -/
lemma gradedMonoid_mk_mul_one_hom_tmul
    (one_mul : ∀ n, (one ▷ M n) ≫ mul 0 n =
      (λ_ (M n)).hom ≫ eqToHom (congrArg M (zero_add n).symm))
    (r : R) {n : ι} (a : M n) :
    GradedMonoid.mk (A := fun i ↦ M i) (0 + n) ((mul 0 n).hom (one.hom r ⊗ₜ a)) =
      GradedMonoid.mk n (r • a) :=
  (congrArg (GradedMonoid.mk (A := fun i ↦ M i) _)
    congr($(ModuleCat.hom_ext_iff.mp (one_mul n)) (r ⊗ₜ a))).trans
    (gradedMonoid_mk_eqToHom_hom M (zero_add n).symm _)

/-- The right unit law, applied to `a ⊗ₜ r`: multiplying by the image of `r` in degree zero is
scalar multiplication by `r`, as elements of the graded monoid. -/
lemma gradedMonoid_mk_mul_tmul_one_hom
    (mul_one : ∀ n, (M n ◁ one) ≫ mul n 0 =
      (ρ_ (M n)).hom ≫ eqToHom (congrArg M (add_zero n).symm))
    (r : R) {n : ι} (a : M n) :
    GradedMonoid.mk (A := fun i ↦ M i) (n + 0) ((mul n 0).hom (a ⊗ₜ one.hom r)) =
      GradedMonoid.mk n (r • a) :=
  (congrArg (GradedMonoid.mk (A := fun i ↦ M i) _)
    congr($(ModuleCat.hom_ext_iff.mp (mul_one n)) (a ⊗ₜ r))).trans
    (gradedMonoid_mk_eqToHom_hom M (add_zero n).symm _)

end AddZeroClass

section AddMonoid

variable [AddMonoid ι] (M : ι → ModuleCat.{u} R) (one : 𝟙_ (ModuleCat.{u} R) ⟶ M 0)
  (mul : ∀ i j, M i ⊗ M j ⟶ M (i + j))
  (one_mul : ∀ n, (one ▷ M n) ≫ mul 0 n =
    (λ_ (M n)).hom ≫ eqToHom (congrArg M (zero_add n).symm))
  (mul_one : ∀ n, (M n ◁ one) ≫ mul n 0 =
    (ρ_ (M n)).hom ≫ eqToHom (congrArg M (add_zero n).symm))
  (mul_assoc : ∀ i j k, (mul i j ▷ M k) ≫ mul (i + j) k =
    (α_ _ _ _).hom ≫ (M i ◁ mul j k) ≫ mul i (j + k) ≫
      eqToHom (congrArg M (add_assoc i j k).symm))
include one_mul mul_one mul_assoc

/-- The graded ring structure on the carriers of a family of modules `M` with a unit
`one : R ⟶ M 0` and homogeneous multiplications `mul i j : M i ⊗ M j ⟶ M (i + j)` satisfying the
graded unit and associativity laws. The product of `a : M i` and `b : M j` is
`mul i j (a ⊗ₜ b)` and the unit is `one 1`. -/
@[expose, instance_reducible]
def gRingOfHomogeneous : DirectSum.GRing (fun i ↦ M i) :=
  letI : GradedMonoid.GMul (fun i ↦ M i) := ⟨fun a b ↦ (mul _ _).hom (a ⊗ₜ b)⟩
  letI : GradedMonoid.GOne (fun i ↦ M i) := ⟨one.hom 1⟩
  { mul_zero a := (congrArg (mul _ _).hom (TensorProduct.tmul_zero _ a)).trans (map_zero _)
    zero_mul b := (congrArg (mul _ _).hom (TensorProduct.zero_tmul _ b)).trans (map_zero _)
    mul_add a b c := (congrArg (mul _ _).hom (TensorProduct.tmul_add a b c)).trans (map_add _ _ _)
    add_mul a b c := (congrArg (mul _ _).hom (TensorProduct.add_tmul a b c)).trans (map_add _ _ _)
    one_mul a := (gradedMonoid_mk_mul_one_hom_tmul one_mul 1 a.2).trans
      (congrArg (GradedMonoid.mk _) (one_smul R a.2))
    mul_one a := (gradedMonoid_mk_mul_tmul_one_hom mul_one 1 a.2).trans
      (congrArg (GradedMonoid.mk _) (one_smul R a.2))
    mul_assoc a b c :=
      (congrArg (GradedMonoid.mk (A := fun i ↦ M i) _)
        congr($(ModuleCat.hom_ext_iff.mp (mul_assoc a.1 b.1 c.1)) (a.2 ⊗ₜ b.2 ⊗ₜ c.2))).trans
        (gradedMonoid_mk_eqToHom_hom M (add_assoc a.1 b.1 c.1).symm _)
    natCast n := n • one.hom 1
    natCast_zero := zero_smul _ _
    natCast_succ n := succ_nsmul _ n
    intCast n := n • one.hom 1
    intCast_ofNat n := natCast_zsmul _ n
    intCast_negSucc_ofNat n := negSucc_zsmul _ n }

/-- In `gRingOfHomogeneous`, the product of homogeneous elements is the given homogeneous
multiplication applied to their tensor product. -/
@[simp]
lemma gRingOfHomogeneous_gMul {i j : ι} (a : M i) (b : M j) :
    letI := gRingOfHomogeneous M one mul one_mul mul_one mul_assoc
    GradedMonoid.GMul.mul (A := fun i ↦ M i) a b = (mul i j).hom (a ⊗ₜ b) :=
  rfl

/-- In `gRingOfHomogeneous`, the unit is the image of `1` under the given unit. -/
@[simp]
lemma gRingOfHomogeneous_gOne :
    letI := gRingOfHomogeneous M one mul one_mul mul_one mul_assoc
    GradedMonoid.GOne.one (A := fun i ↦ M i) = one.hom 1 :=
  rfl

/-- The graded `R`-algebra structure of `gRingOfHomogeneous`: its structure map
`R → M 0` is the given unit `one`. -/
@[expose, instance_reducible]
def gAlgebraOfHomogeneous :
    @DirectSum.GAlgebra ι R (fun i ↦ M i) _ _ _ _
      (gRingOfHomogeneous M one mul one_mul mul_one mul_assoc).toGSemiring :=
  letI := gRingOfHomogeneous M one mul one_mul mul_one mul_assoc
  { toFun := one.hom.toAddMonoidHom
    map_one := rfl
    map_mul r s := by
      refine Eq.trans ?_ (gradedMonoid_mk_mul_one_hom_tmul one_mul r (one.hom s)).symm
      rw [LinearMap.toAddMonoidHom_coe, ← smul_eq_mul, map_smul]
    commutes r x := (gradedMonoid_mk_mul_one_hom_tmul one_mul r x.2).trans
      (gradedMonoid_mk_mul_tmul_one_hom mul_one r x.2).symm
    smul_def r x := (gradedMonoid_mk_mul_one_hom_tmul one_mul r x.2).symm }

/-- The structure map of `gAlgebraOfHomogeneous` is the given unit. -/
@[simp]
lemma gAlgebraOfHomogeneous_toFun (r : R) :
    letI := gRingOfHomogeneous M one mul one_mul mul_one mul_assoc
    (gAlgebraOfHomogeneous M one mul one_mul mul_one mul_assoc).toFun r = one.hom r :=
  rfl

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid ι] (M : ι → ModuleCat.{u} R) (one : 𝟙_ (ModuleCat.{u} R) ⟶ M 0)
  (mul : ∀ i j, M i ⊗ M j ⟶ M (i + j))
  (one_mul : ∀ n, (one ▷ M n) ≫ mul 0 n =
    (λ_ (M n)).hom ≫ eqToHom (congrArg M (zero_add n).symm))
  (mul_one : ∀ n, (M n ◁ one) ≫ mul n 0 =
    (ρ_ (M n)).hom ≫ eqToHom (congrArg M (add_zero n).symm))
  (mul_assoc : ∀ i j k, (mul i j ▷ M k) ≫ mul (i + j) k =
    (α_ _ _ _).hom ≫ (M i ◁ mul j k) ≫ mul i (j + k) ≫
      eqToHom (congrArg M (add_assoc i j k).symm))
  (mul_comm : ∀ i j, (β_ (M i) (M j)).hom ≫ mul j i =
    mul i j ≫ eqToHom (congrArg M (add_comm i j)))

/-- The graded commutative ring structure of `gRingOfHomogeneous`, when the homogeneous
multiplications are moreover graded commutative. -/
@[expose, instance_reducible]
def gCommRingOfHomogeneous : DirectSum.GCommRing (fun i ↦ M i) where
  __ := gRingOfHomogeneous M one mul one_mul mul_one mul_assoc
  mul_comm a b :=
    ((congrArg (GradedMonoid.mk (A := fun i ↦ M i) _)
      congr($(ModuleCat.hom_ext_iff.mp (mul_comm a.1 b.1)) (a.2 ⊗ₜ b.2))).trans
      (gradedMonoid_mk_eqToHom_hom M (add_comm a.1 b.1) _)).symm

end AddCommMonoid

end TauCeti.ModuleCat
