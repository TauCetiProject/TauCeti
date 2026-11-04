/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# The Cayley–Dickson double of a ring with involution

For a possibly nonassociative ring `A` with an involution `star`, the **Cayley–Dickson double**
`CayleyDickson A` is the set of ordered pairs `⟨a, b⟩` of elements of `A`, added coordinatewise
and multiplied by

`⟨a, b⟩ * ⟨c, d⟩ = ⟨a * c - star d * b, d * a + b * star c⟩`,

with unit `⟨1, 0⟩` and the involution `star ⟨a, b⟩ = ⟨star a, -b⟩`. Doubling `ℝ` with its trivial
involution gives `ℂ`, doubling `ℂ` gives the quaternions, and doubling the quaternions `ℍ[ℝ]`
gives the octonions, the eight-dimensional real division algebra; the identities of the double of
the quaternions are proved in `TauCeti.Algebra.CayleyDickson.Quaternion`.

The double of an associative ring is in general no longer associative, so it is a `NonAssocRing`
and nothing more. This file builds that structure for every possibly nonassociative ring with
involution: the additive and module structures, transported from `A × A`, the multiplication with
its unit and integer casts,
the involution, which reverses products, so that the double is again a ring with involution, and
the two scalar towers for scalars acting on `A` compatibly with its product (and, for
`SMulCommClass`, with its involution).

## Main definitions

* `TauCeti.CayleyDickson A`: the Cayley–Dickson double of `A`, the ordered pairs `⟨fst, snd⟩`.
* `TauCeti.CayleyDickson.linearEquivProd`: the coordinates of an element of the double, as a
  linear isomorphism with `A × A`.

## Main results

* The double is a `NonAssocRing` with the product above, a `StarRing` with the involution
  `star ⟨a, b⟩ = ⟨star a, -b⟩`, which reverses products, and a module over every ring of scalars
  acting on `A`, with the two scalar towers when the action is compatible with the product of `A`
  (and, for `SMulCommClass`, with its involution).
* `TauCeti.CayleyDickson.finrank_eq`: the double has twice the dimension of `A`.

## Implementation notes

The double is a structure with two fields rather than the type `A × A` itself, so that it carries
neither the coordinatewise product nor the coordinatewise involution of a product type. Several
equivalent sign conventions for the product are in use; with the one chosen here the unit is
`⟨1, 0⟩`, the element `⟨0, 1⟩` squares to `-1`, and the involution is
`star ⟨a, b⟩ = ⟨star a, -b⟩`, positive on the double of `ℍ[ℝ]`.

## References

* J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. **39** (2002), 145–205, §2.2.
* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*,
  Springer (2000), §1.5.
-/

public section

namespace TauCeti

/-- The **Cayley–Dickson double** of a ring with involution `A`: the ordered pairs `⟨fst, snd⟩` of
elements of `A`, multiplied by `⟨a, b⟩ * ⟨c, d⟩ = ⟨a * c - star d * b, d * a + b * star c⟩`. -/
@[ext]
structure CayleyDickson (A : Type*) where
  /-- The first coordinate of an element of the Cayley–Dickson double. -/
  fst : A
  /-- The second coordinate of an element of the Cayley–Dickson double. -/
  snd : A

namespace CayleyDickson

variable {R A : Type*}

/-! ### The additive and module structure -/

instance [Zero A] : Zero (CayleyDickson A) := ⟨⟨0, 0⟩⟩

@[simp] theorem zero_fst [Zero A] : (0 : CayleyDickson A).fst = 0 := (rfl)
@[simp] theorem zero_snd [Zero A] : (0 : CayleyDickson A).snd = 0 := (rfl)

instance [Zero A] : Inhabited (CayleyDickson A) := ⟨0⟩

instance [Zero A] [One A] : One (CayleyDickson A) := ⟨⟨1, 0⟩⟩

@[simp] theorem one_fst [Zero A] [One A] : (1 : CayleyDickson A).fst = 1 := (rfl)
@[simp] theorem one_snd [Zero A] [One A] : (1 : CayleyDickson A).snd = 0 := (rfl)

instance [Add A] : Add (CayleyDickson A) := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩

@[simp] theorem add_fst [Add A] (x y : CayleyDickson A) : (x + y).fst = x.fst + y.fst := (rfl)
@[simp] theorem add_snd [Add A] (x y : CayleyDickson A) : (x + y).snd = x.snd + y.snd := (rfl)

instance [Neg A] : Neg (CayleyDickson A) := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩

@[simp] theorem neg_fst [Neg A] (x : CayleyDickson A) : (-x).fst = -x.fst := (rfl)
@[simp] theorem neg_snd [Neg A] (x : CayleyDickson A) : (-x).snd = -x.snd := (rfl)

instance [Sub A] : Sub (CayleyDickson A) := ⟨fun x y => ⟨x.fst - y.fst, x.snd - y.snd⟩⟩

@[simp] theorem sub_fst [Sub A] (x y : CayleyDickson A) : (x - y).fst = x.fst - y.fst := (rfl)
@[simp] theorem sub_snd [Sub A] (x y : CayleyDickson A) : (x - y).snd = x.snd - y.snd := (rfl)

instance [SMul R A] : SMul R (CayleyDickson A) := ⟨fun r x => ⟨r • x.fst, r • x.snd⟩⟩

@[simp] theorem smul_fst [SMul R A] (r : R) (x : CayleyDickson A) : (r • x).fst = r • x.fst :=
  (rfl)
@[simp] theorem smul_snd [SMul R A] (r : R) (x : CayleyDickson A) : (r • x).snd = r • x.snd :=
  (rfl)

instance [AddCommMonoid A] : AddCommMonoid (CayleyDickson A) :=
  Function.Injective.addCommMonoid (fun x : CayleyDickson A => (x.fst, x.snd))
    (fun ⟨_, _⟩ ⟨_, _⟩ h => by simp_all) rfl (fun _ _ => rfl) fun _ _ => rfl

instance [AddCommGroup A] : AddCommGroup (CayleyDickson A) :=
  Function.Injective.addCommGroup (fun x : CayleyDickson A => (x.fst, x.snd))
    (fun ⟨_, _⟩ ⟨_, _⟩ h => by simp_all) rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

instance [Monoid R] [AddCommMonoid A] [DistribMulAction R A] :
    DistribMulAction R (CayleyDickson A) :=
  Function.Injective.distribMulAction
    ⟨⟨fun x : CayleyDickson A => (x.fst, x.snd), rfl⟩, fun _ _ => rfl⟩
    (fun ⟨_, _⟩ ⟨_, _⟩ h => by simp_all) fun _ _ => rfl

instance [Semiring R] [AddCommMonoid A] [Module R A] : Module R (CayleyDickson A) :=
  Function.Injective.module R
    ⟨⟨fun x : CayleyDickson A => (x.fst, x.snd), rfl⟩, fun _ _ => rfl⟩
    (fun ⟨_, _⟩ ⟨_, _⟩ h => by simp_all) fun _ _ => rfl

instance [Zero A] [NatCast A] : NatCast (CayleyDickson A) := ⟨fun n => ⟨n, 0⟩⟩

@[simp] theorem natCast_fst [Zero A] [NatCast A] (n : ℕ) : (n : CayleyDickson A).fst = n := (rfl)
@[simp] theorem natCast_snd [Zero A] [NatCast A] (n : ℕ) : (n : CayleyDickson A).snd = 0 := (rfl)

instance [Zero A] [IntCast A] : IntCast (CayleyDickson A) := ⟨fun z => ⟨z, 0⟩⟩

@[simp] theorem intCast_fst [Zero A] [IntCast A] (z : ℤ) : (z : CayleyDickson A).fst = z := (rfl)
@[simp] theorem intCast_snd [Zero A] [IntCast A] (z : ℤ) : (z : CayleyDickson A).snd = 0 := (rfl)

/-- The natural-number and integer casts of the double lie in the first coordinate. -/
instance [AddCommGroupWithOne A] : AddCommGroupWithOne (CayleyDickson A) where
  __ := (inferInstance : AddCommGroup (CayleyDickson A))
  one := 1
  natCast_zero := by ext <;> simp
  natCast_succ n := by ext <;> simp
  intCast_ofNat n := by ext <;> simp
  intCast_negSucc n := by ext <;> simp [Int.cast_negSucc]

@[simp] theorem ofNat_fst [AddCommGroupWithOne A] (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : CayleyDickson A).fst = ofNat(n) :=
  (rfl)
@[simp] theorem ofNat_snd [AddCommGroupWithOne A] (n : ℕ) [n.AtLeastTwo] :
    (ofNat(n) : CayleyDickson A).snd = 0 :=
  (rfl)

variable (R A) in
/-- The coordinates of an element of the Cayley–Dickson double, as a linear isomorphism with
`A × A`, over any semiring acting on `A`. -/
def linearEquivProd [Semiring R] [AddCommMonoid A] [Module R A] :
    CayleyDickson A ≃ₗ[R] A × A where
  toFun x := (x.fst, x.snd)
  invFun p := ⟨p.1, p.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem linearEquivProd_apply [Semiring R] [AddCommMonoid A] [Module R A]
    (x : CayleyDickson A) : linearEquivProd R A x = (x.fst, x.snd) := (rfl)

@[simp] theorem linearEquivProd_symm_apply [Semiring R] [AddCommMonoid A] [Module R A]
    (p : A × A) : (linearEquivProd R A).symm p = ⟨p.1, p.2⟩ := (rfl)

instance [Semiring R] [AddCommMonoid A] [Module R A] [Module.Free R A] :
    Module.Free R (CayleyDickson A) :=
  Module.Free.of_equiv (linearEquivProd R A).symm

instance [Semiring R] [AddCommMonoid A] [Module R A] [Module.Finite R A] :
    Module.Finite R (CayleyDickson A) :=
  Module.Finite.equiv (linearEquivProd R A).symm

variable (R A) in
/-- **The double has twice the dimension**: an element is a pair of elements of `A`. -/
theorem finrank_eq [Semiring R] [StrongRankCondition R] [AddCommMonoid A] [Module R A]
    [Module.Free R A] [Module.Finite R A] :
    Module.finrank R (CayleyDickson A) = 2 * Module.finrank R A := by
  rw [(linearEquivProd R A).finrank_eq, Module.finrank_prod, two_mul]

/-! ### The multiplication and the involution -/

section Ring

variable [NonAssocRing A] [StarRing A]

/-- The Cayley–Dickson product `⟨a, b⟩ * ⟨c, d⟩ = ⟨a * c - star d * b, d * a + b * star c⟩`. -/
instance : Mul (CayleyDickson A) :=
  ⟨fun x y => ⟨x.fst * y.fst - star y.snd * x.snd, y.snd * x.fst + x.snd * star y.fst⟩⟩

@[simp] theorem mul_fst (x y : CayleyDickson A) :
    (x * y).fst = x.fst * y.fst - star y.snd * x.snd := (rfl)
@[simp] theorem mul_snd (x y : CayleyDickson A) :
    (x * y).snd = y.snd * x.fst + x.snd * star y.fst := (rfl)

instance : NonAssocRing (CayleyDickson A) where
  __ := (inferInstance : AddCommGroupWithOne (CayleyDickson A))
  left_distrib x y z := by ext <;> simp [mul_add, add_mul] <;> abel
  right_distrib x y z := by ext <;> simp [mul_add, add_mul] <;> abel
  zero_mul x := by ext <;> simp
  mul_zero x := by ext <;> simp
  one_mul x := by ext <;> simp
  mul_one x := by ext <;> simp

/-- The involution `star ⟨a, b⟩ = ⟨star a, -b⟩` of the Cayley–Dickson double. -/
instance : Star (CayleyDickson A) := ⟨fun x => ⟨star x.fst, -x.snd⟩⟩

@[simp] theorem star_fst (x : CayleyDickson A) : (star x).fst = star x.fst := (rfl)
@[simp] theorem star_snd (x : CayleyDickson A) : (star x).snd = -x.snd := (rfl)

/-- The involution of the double reverses products, as the involution of `A` does, so the double
is again a ring with involution. -/
instance : StarRing (CayleyDickson A) where
  star_involutive x := by ext <;> simp
  star_mul x y := by ext <;> simp [StarMul.star_mul, add_comm]
  star_add x y := by ext <;> simp [add_comm]

/-- Scalars acting on `A` compatibly with its product and involution commute with left
multiplication in the double. -/
instance [Star R] [TrivialStar R] [Monoid R] [DistribMulAction R A] [SMulCommClass R A A]
    [IsScalarTower R A A] [StarModule R A] :
    SMulCommClass R (CayleyDickson A) (CayleyDickson A) where
  smul_comm r x y := by
    ext <;> simp [mul_smul_comm, smul_mul_assoc, smul_sub, smul_add]

/-- Scalars acting on `A` compatibly with its product associate with the product of the double. -/
instance [Monoid R] [DistribMulAction R A] [SMulCommClass R A A] [IsScalarTower R A A] :
    IsScalarTower R (CayleyDickson A) (CayleyDickson A) where
  smul_assoc r x y := by
    ext <;> simp [mul_smul_comm, smul_mul_assoc, smul_sub, smul_add]

end Ring

end CayleyDickson

end TauCeti
