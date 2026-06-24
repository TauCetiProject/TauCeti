/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.GaloisGroup

/-!
# Sign-change automorphisms of a multiquadratic field

The equivalence `TauCeti.Multiquadratic.galoisGroupEquiv` identifies the Galois group of a
square-class independent multiquadratic field with the sign-pattern group `Multiplicative
(ι → ZMod 2)`. This file packages the inverse direction of that equivalence as named
automorphisms: for a vector `ε : ι → ZMod 2`, `signChangeAut hroot hindep ε` is the
automorphism sending the generator `root i` to `(-1)^(ε i) root i`.

The coordinate sign changes are the standard generators used in the Galois-group and
prime-splitting layers: `coordinateSignChangeAut hroot hindep j` negates the `j`-th generator and
fixes all the others.

## Main results

* `TauCeti.Multiquadratic.signChangeAut`: the automorphism attached to a sign vector.
* `TauCeti.Multiquadratic.signChangeAut_apply_gen`: its action on each generator.
* `TauCeti.Multiquadratic.coordinateSignChangeAut`: the coordinate sign-change automorphism.
* `TauCeti.Multiquadratic.coordinateSignChangeAut_apply_gen_self` and
  `TauCeti.Multiquadratic.coordinateSignChangeAut_apply_gen_of_ne`: the generator rules.

## Provenance

This file is a thin named API around the already-credited `GaloisGroup` construction, which
generalises the sign-change automorphisms analysed in
[kim-em/erdos-unit-distance](https://github.com/kim-em/erdos-unit-distance), the formalization
of L. Alpöge's disproof of the uniform-constant Erdős unit-distance conjecture.
-/

public section

open IntermediateField

namespace TauCeti.Multiquadratic

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {ι : Type*}
  [Finite ι] [NeZero (2 : K)] {d : ι → K} {root : ι → L}

/-- The sign-change automorphism with sign vector `ε`.

It is the inverse image of `ε` under the multiquadratic Galois-group equivalence, so it sends
`gen root i` to `(-1) ^ (ε i).val * gen root i`. -/
noncomputable def signChangeAut
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (ε : ι → ZMod 2) :
    adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root) :=
  (galoisGroupEquiv hroot hindep).symm (Multiplicative.ofAdd ε)

/-- The sign-change automorphism has the prescribed image under `galoisGroupEquiv`. -/
@[simp] theorem galoisGroupEquiv_signChangeAut
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (ε : ι → ZMod 2) :
    galoisGroupEquiv hroot hindep (signChangeAut hroot hindep ε) =
      Multiplicative.ofAdd ε := by
  simp [signChangeAut]

/-- The sign pattern of `signChangeAut hroot hindep ε` is exactly `ε`. -/
@[simp] theorem signPattern_signChangeAut
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (ε : ι → ZMod 2) :
    signPattern root (signChangeAut hroot hindep ε) = ε := by
  have h := galoisGroupEquiv_signChangeAut hroot hindep ε
  rw [galoisGroupEquiv_apply] at h
  exact Multiplicative.ofAdd.injective h

/-- The action of a sign-change automorphism on a generator. -/
@[simp] theorem signChangeAut_apply_gen
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (ε : ι → ZMod 2) (i : ι) :
    signChangeAut hroot hindep ε (gen root i) =
      (-1) ^ (ε i).val * gen root i :=
  galoisGroupEquiv_symm_apply_gen hroot hindep ε i

/-- The zero sign vector gives the identity automorphism. -/
@[simp] theorem signChangeAut_zero
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i)) :
    signChangeAut hroot hindep 0 = 1 := by
  apply (galoisGroupEquiv hroot hindep).injective
  simp

/-- Sign-change automorphisms multiply by adding their sign vectors. -/
@[simp] theorem signChangeAut_add
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (ε η : ι → ZMod 2) :
    signChangeAut hroot hindep (ε + η) =
      signChangeAut hroot hindep ε * signChangeAut hroot hindep η := by
  apply (galoisGroupEquiv hroot hindep).injective
  rw [galoisGroupEquiv_signChangeAut, map_mul, galoisGroupEquiv_signChangeAut,
    galoisGroupEquiv_signChangeAut, ofAdd_add]

/-- The coordinate sign vector: `1` at `j` and `0` elsewhere. -/
def coordinateSign (j : ι) [DecidableEq ι] : ι → ZMod 2 :=
  Pi.single j 1

omit [Finite ι] in
/-- The coordinate sign vector has value `1` at its coordinate. -/
@[simp] theorem coordinateSign_self (j : ι) [DecidableEq ι] :
    coordinateSign j j = 1 := by
  simp [coordinateSign]

omit [Finite ι] in
/-- The coordinate sign vector vanishes away from its coordinate. -/
@[simp] theorem coordinateSign_of_ne {i j : ι} [DecidableEq ι] (hij : i ≠ j) :
    coordinateSign j i = 0 := by
  simp [coordinateSign, Pi.single_eq_of_ne hij]

omit [Finite ι] in
/-- Twice the same coordinate sign vector is zero. -/
@[simp] theorem coordinateSign_add_self (j : ι) [DecidableEq ι] :
    coordinateSign j + coordinateSign j = (0 : ι → ZMod 2) := by
  funext i
  by_cases h : i = j
  · subst i
    simp only [Pi.add_apply, coordinateSign_self, Pi.zero_apply]
    decide
  · simp [coordinateSign_of_ne h]

/-- The automorphism that changes the sign of the `j`-th generator and fixes the others. -/
noncomputable def coordinateSignChangeAut
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (j : ι) [DecidableEq ι] :
    adjoin K (Set.range root) ≃ₐ[K] adjoin K (Set.range root) :=
  signChangeAut hroot hindep (coordinateSign j)

/-- The coordinate sign-change automorphism negates its own generator. -/
@[simp] theorem coordinateSignChangeAut_apply_gen_self
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (j : ι) [DecidableEq ι] :
    coordinateSignChangeAut hroot hindep j (gen root j) = -gen root j := by
  rw [coordinateSignChangeAut, signChangeAut_apply_gen, coordinateSign_self]
  rw [ZMod.val_one, pow_one, neg_one_mul]

/-- A coordinate sign-change automorphism fixes the other generators. -/
@[simp] theorem coordinateSignChangeAut_apply_gen_of_ne
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    {i j : ι} [DecidableEq ι] (hij : i ≠ j) :
    coordinateSignChangeAut hroot hindep j (gen root i) = gen root i := by
  rw [coordinateSignChangeAut, signChangeAut_apply_gen, coordinateSign_of_ne hij]
  simp

/-- The sign pattern of a coordinate sign-change automorphism is the coordinate sign vector. -/
@[simp] theorem signPattern_coordinateSignChangeAut
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (j : ι) [DecidableEq ι] :
    signPattern root (coordinateSignChangeAut hroot hindep j) = coordinateSign j := by
  simp [coordinateSignChangeAut]

/-- A coordinate sign-change automorphism has order dividing two. -/
@[simp] theorem coordinateSignChangeAut_mul_self
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (j : ι) [DecidableEq ι] :
    coordinateSignChangeAut hroot hindep j * coordinateSignChangeAut hroot hindep j = 1 := by
  rw [coordinateSignChangeAut]
  rw [← signChangeAut_add, coordinateSign_add_self, signChangeAut_zero]

/-- Coordinate sign-change automorphisms commute. -/
theorem coordinateSignChangeAut_commute
    (hroot : ∀ i, root i ^ 2 = algebraMap K L (d i))
    (hindep : ∀ S : Finset ι, S.Nonempty → ¬ IsSquare (∏ i ∈ S, d i))
    (i j : ι) [DecidableEq ι] :
    Commute (coordinateSignChangeAut hroot hindep i) (coordinateSignChangeAut hroot hindep j) :=
  aut_commute hroot _ _

end TauCeti.Multiquadratic
