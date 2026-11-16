/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotents.Corner.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Quotients of idempotent corners

For an idempotent `e` of a ring `A` and a two-sided ideal `I`, taking the corner commutes with
passing to the quotient:

`eAe / eIe ≃ e'(A/I)e'`, where `e'` is the image of `e`.

Here `eIe` consists of the elements of the corner whose ambient value lies in `I`. The quotient
map is surjective on corners: lift an element of the target and multiply its lift by `e` on both
sides. Its kernel is precisely `eIe`. The equivalence is also an algebra equivalence when `A`
is an algebra over a commutative semiring.

The ideal `eIe` is nilpotent whenever `I` is nilpotent, with the same vanishing exponent. Applied
to the Jacobson radical of an Artinian algebra, these facts compute the quotient of a corner by
a nilpotent ideal. This is the quotient calculation used when selecting one primitive
idempotent from each simple-module isomorphism class to obtain a basic algebra.

The equivalences use Mathlib's first isomorphism theorem
`RingHom.quotientKerEquivOfSurjective`.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras, Vol. 1*, Sections I.4 and I.6.
-/

public section

namespace IsIdempotentElem

section Semiring

variable {A : Type*} [Semiring A] {e : A} (he : IsIdempotentElem e)

/-- The left ideal `I ∩ eAe` of the corner: its elements have ambient value in `I`.
For two-sided `I`, this is the ideal `eIe`. -/
def cornerIdeal (I : Ideal A) : Ideal he.Corner where
  carrier := {x | x.1 ∈ I}
  zero_mem' := I.zero_mem
  add_mem' hx hy := I.add_mem hx hy
  smul_mem' a _ hx := I.mul_mem_left a.1 hx

@[simp]
theorem mem_cornerIdeal (I : Ideal A) (x : he.Corner) :
    x ∈ he.cornerIdeal I ↔ x.1 ∈ I :=
  (Iff.rfl)

@[simp]
theorem cornerIdeal_bot : he.cornerIdeal ⊥ = ⊥ := by
  ext x
  simp only [mem_cornerIdeal, Ideal.mem_bot]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

@[simp]
theorem cornerIdeal_top : he.cornerIdeal ⊤ = ⊤ := by
  ext x
  simp

instance cornerIdeal_isTwoSided (I : Ideal A) [I.IsTwoSided] :
    (he.cornerIdeal I).IsTwoSided where
  mul_mem_of_left _ hx := I.mul_mem_right _ hx

/-- The `n`th power of a restricted ideal is contained in the restriction of `Iⁿ`.
The reverse inclusion need not hold. -/
theorem cornerIdeal_pow_le (I : Ideal A) (n : ℕ) :
    (he.cornerIdeal I) ^ n ≤ he.cornerIdeal (I ^ n) := by
  induction n with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    rw [Submodule.pow_succ, Submodule.pow_succ]
    refine Ideal.mul_le.mpr fun x hx y hy => ?_
    exact Ideal.mul_mem_mul (ih hx) hy

/-- A power vanishing in the ambient ring also vanishes in the corner ideal. -/
theorem cornerIdeal_pow_eq_bot (I : Ideal A) {n : ℕ} (hI : I ^ n = ⊥) :
    (he.cornerIdeal I) ^ n = ⊥ := by
  apply le_bot_iff.mp
  simpa only [hI, cornerIdeal_bot] using he.cornerIdeal_pow_le I n

/-- Restricting a nilpotent ideal to an idempotent corner preserves nilpotence. -/
theorem isNilpotent_cornerIdeal (I : Ideal A) (hI : IsNilpotent I) :
    IsNilpotent (he.cornerIdeal I) := by
  obtain ⟨n, hn⟩ := hI
  exact ⟨n, he.cornerIdeal_pow_eq_bot I (by simpa using hn)⟩

end Semiring

section Ring

variable {A : Type*} [Ring A] {e : A} (he : IsIdempotentElem e)
  (I : Ideal A) [I.IsTwoSided]

/-- The quotient homomorphism restricted to the corner `eAe`. -/
def cornerQuotientHom :
    he.Corner →+* (he.map (Ideal.Quotient.mk I)).Corner :=
  he.cornerMap (Ideal.Quotient.mk I).toNonUnitalRingHom

@[simp]
theorem val_cornerQuotientHom (x : he.Corner) :
    (he.cornerQuotientHom I x).1 = Ideal.Quotient.mk I x.1 :=
  he.val_cornerMap _ x

/-- The quotient homomorphism is surjective on the corner, even when `e` is not full. -/
theorem cornerQuotientHom_surjective : Function.Surjective (he.cornerQuotientHom I) :=
  he.cornerMap_surjective _ Ideal.Quotient.mk_surjective

@[simp]
theorem ker_cornerQuotientHom : RingHom.ker (he.cornerQuotientHom I) = he.cornerIdeal I := by
  ext x
  simp only [RingHom.mem_ker, mem_cornerIdeal]
  constructor
  · intro hx
    have hval := congrArg Subtype.val hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by
      simpa only [val_cornerQuotientHom, Corner.val_zero] using hval)
  · intro hx
    apply Subtype.ext
    simpa only [val_cornerQuotientHom, Corner.val_zero] using
      (Ideal.Quotient.eq_zero_iff_mem.mpr hx)

/-- Taking an idempotent corner commutes with quotienting by a two-sided ideal. -/
noncomputable def cornerQuotientEquiv :
    (he.Corner ⧸ he.cornerIdeal I) ≃+* (he.map (Ideal.Quotient.mk I)).Corner :=
  (Ideal.quotEquivOfEq (he.ker_cornerQuotientHom I).symm).trans
    ((he.cornerQuotientHom I).quotientKerEquivOfSurjective (he.cornerQuotientHom_surjective I))

@[simp]
theorem cornerQuotientEquiv_mk (x : he.Corner) :
    he.cornerQuotientEquiv I (Ideal.Quotient.mk _ x) = he.cornerQuotientHom I x := by
  simp [cornerQuotientEquiv]

section Algebra

variable (R : Type*) [CommSemiring R] [Algebra R A]

/-- The corner quotient equivalence preserves the scalar algebra structure. -/
noncomputable def cornerQuotientAlgEquiv :
    (he.Corner ⧸ he.cornerIdeal I) ≃ₐ[R] (he.map (Ideal.Quotient.mk I)).Corner :=
  AlgEquiv.ofRingEquiv (f := he.cornerQuotientEquiv I) fun r => by
    rw [← (Ideal.Quotient.mkₐ R (he.cornerIdeal I)).commutes r]
    rw [Ideal.Quotient.mkₐ_eq_mk, cornerQuotientEquiv_mk]
    apply Subtype.ext
    simp [Algebra.smul_def]

@[simp]
theorem cornerQuotientAlgEquiv_mk (x : he.Corner) :
    he.cornerQuotientAlgEquiv I R (Ideal.Quotient.mk _ x) = he.cornerQuotientHom I x :=
  he.cornerQuotientEquiv_mk I x

end Algebra
end Ring
end IsIdempotentElem
