/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Ring

/-!
# Graded rings from bi-additive products

Let `A : ι → Type*` be a family of additive groups indexed by an additive monoid, with bi-additive
products `mul i j : A i →+ A j →+ A (i + j)` and an element `one : A 0` satisfying the graded unit
and associativity laws, as equalities in the graded monoid `GradedMonoid A`, so that the degrees
`0 + i`, `i + 0` and `i + j + k`, `i + (j + k)` need not agree definitionally. The remaining fields
of Mathlib's `DirectSum.GRing` are determined by these: distributivity is the bi-additivity of
`mul`, and the casts of integers are the multiples of `one`. This file builds the graded ring from
the product and the unit alone, so that it depends only on them.

## Main definitions

* `TauCeti.DirectSum.gRingOfMul`: the `DirectSum.GRing` structure on `A` with homogeneous product
  `mul` and unit `one`.

## Main results

* `TauCeti.DirectSum.gRingOfMul_congr`: `TauCeti.DirectSum.gRingOfMul` depends only on the product
  and the unit, not on the proofs of the laws.

The structure is not an instance, since the product is data that is not determined by `A`.
-/

public section

namespace TauCeti.DirectSum

variable {ι : Type*} [AddMonoid ι] {A : ι → Type*} [∀ i, AddCommGroup (A i)]
  (mul : ∀ i j, A i →+ A j →+ A (i + j)) (one : A 0)

/-- **The graded ring of a bi-additive product.** A family of bi-additive products
`mul i j : A i →+ A j →+ A (i + j)` which is associative, with a two-sided unit `one` in degree
zero, as elements of the graded monoid, makes `A` a graded ring. Its data are `mul` and `one`
alone, so that it is determined by them (`TauCeti.DirectSum.gRingOfMul_congr`). -/
@[expose, instance_reducible]
def gRingOfMul
    (one_mul : ∀ {i : ι} (a : A i), GradedMonoid.mk (A := A) (0 + i) (mul 0 i one a) = ⟨i, a⟩)
    (mul_one : ∀ {i : ι} (a : A i), GradedMonoid.mk (A := A) (i + 0) (mul i 0 a one) = ⟨i, a⟩)
    (mul_assoc : ∀ {i j k : ι} (a : A i) (b : A j) (c : A k),
      GradedMonoid.mk (A := A) (i + j + k) (mul (i + j) k (mul i j a b) c) =
        ⟨i + (j + k), mul i (j + k) a (mul j k b c)⟩) :
    _root_.DirectSum.GRing A :=
  letI : GradedMonoid.GMul A := ⟨fun a b ↦ mul _ _ a b⟩
  letI : GradedMonoid.GOne A := ⟨one⟩
  { mul_zero a := map_zero (mul _ _ a)
    zero_mul b := DFunLike.congr_fun (map_zero (mul _ _)) b
    mul_add a b c := map_add (mul _ _ a) b c
    add_mul a b c := DFunLike.congr_fun (map_add (mul _ _) a b) c
    one_mul a := one_mul a.2
    mul_one a := mul_one a.2
    mul_assoc a b c := mul_assoc a.2 b.2 c.2
    natCast n := n • one
    natCast_zero := zero_smul _ _
    natCast_succ n := succ_nsmul _ n
    intCast n := n • one
    intCast_ofNat n := natCast_zsmul _ n
    intCast_negSucc_ofNat n := negSucc_zsmul _ n }

section

variable {mul one}
  {one_mul : ∀ {i : ι} (a : A i), GradedMonoid.mk (A := A) (0 + i) (mul 0 i one a) = ⟨i, a⟩}
  {mul_one : ∀ {i : ι} (a : A i), GradedMonoid.mk (A := A) (i + 0) (mul i 0 a one) = ⟨i, a⟩}
  {mul_assoc : ∀ {i j k : ι} (a : A i) (b : A j) (c : A k),
    GradedMonoid.mk (A := A) (i + j + k) (mul (i + j) k (mul i j a b) c) =
      ⟨i + (j + k), mul i (j + k) a (mul j k b c)⟩}

/-- In `TauCeti.DirectSum.gRingOfMul`, the product of homogeneous elements is the given
product. -/
-- Not `@[simp]`: the product passed to `TauCeti.DirectSum.gRingOfMul` is often a composite such
-- as `LinearMap.toAddMonoidHom'.comp f.toAddMonoidHom`, and the graded rings built from it state
-- their own simp lemmas in terms of `f`, such as `LinearMap.cohomologyGRing_gMul`.
theorem gRingOfMul_gMul {i j : ι} (a : A i) (b : A j) :
    letI := gRingOfMul mul one one_mul mul_one mul_assoc
    GradedMonoid.GMul.mul (A := A) a b = mul i j a b :=
  rfl

/-- In `TauCeti.DirectSum.gRingOfMul`, the unit is the given unit. -/
@[simp]
theorem gRingOfMul_gOne :
    letI := gRingOfMul mul one one_mul mul_one mul_assoc
    GradedMonoid.GOne.one (A := A) = one :=
  rfl

/-- `TauCeti.DirectSum.gRingOfMul` depends only on the product and the unit. -/
theorem gRingOfMul_congr {mul' : ∀ i j, A i →+ A j →+ A (i + j)} {one' : A 0}
    (hmul : mul = mul') (hone : one = one') {one_mul' mul_one' mul_assoc'} :
    gRingOfMul mul one one_mul mul_one mul_assoc =
      gRingOfMul mul' one' one_mul' mul_one' mul_assoc' := by
  subst hmul hone
  rfl

end

end TauCeti.DirectSum
