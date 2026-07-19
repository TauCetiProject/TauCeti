/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Functoriality of class groups under ring equivalences

Mathlib defines `ClassGroup.mulEquiv f`, the multiplicative equivalence on ideal class groups
induced by a ring equivalence `f : R ≃+* S`. This file supplies its basic functorial API: the
induced map respects identity, composition, and inverses, and computes on the class of a unit
fractional ideal.

This is a prerequisite for the genus-field layer of the multiquadratic roadmap. For a quadratic
field, conjugation is a ring automorphism of its ring of integers; the roadmap's proof that
conjugation acts on the class group by inversion first needs to treat that action functorially and
compute it on ideal classes.

## Main results

* `ClassGroup.mulEquiv_mk`: the value of the induced equivalence on the class of a unit fractional
  ideal is the class of the transported ideal.
* `ClassGroup.mulEquiv_refl`: the identity ring equivalence induces the identity on class groups.
* `ClassGroup.mulEquiv_trans`: induced equivalences respect composition.
* `ClassGroup.mulEquiv_symm`: the inverse induced equivalence comes from the inverse ring
  equivalence.
* `ClassGroup.mulEquivHom`: the induced action bundled as a monoid homomorphism
  `(R ≃+* R) →* MulAut (ClassGroup R)`.
* `ClassGroup.mulEquiv_involutive`: an involutive ring equivalence acts involutively on the class
  group.
-/

public section

open scoped nonZeroDivisors

namespace ClassGroup

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [IsDomain R] [IsDomain S] [IsDomain T]

/-- `ClassGroup.mulEquiv f` sends the class of a unit fractional ideal `I` to the class of its
image under `FractionalIdeal.ringEquivOfRingEquiv f`. This is the characteristic computation of the
induced map on ideal classes; the functorial laws below are corollaries. -/
@[simp high] theorem mulEquiv_mk (f : R ≃+* S) (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    ClassGroup.mulEquiv f (ClassGroup.mk (FractionRing R) I) =
      ClassGroup.mk (FractionRing S)
        (Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv
          (FractionRing R) (FractionRing S) f) I) := by
  apply (ClassGroup.equiv (FractionRing S)).injective
  rw [ClassGroup.mulEquiv_apply, MulEquiv.apply_symm_apply, ClassGroup.equiv_mk,
    ClassGroup.equiv_mk, QuotientGroup.congr_mk']
  apply congrArg (QuotientGroup.mk' (toPrincipalIdeal S (FractionRing S)).range)
  apply Units.ext
  simp [FractionalIdeal.canonicalEquiv_self]

/-- The identity ring equivalence induces the identity class-group equivalence. -/
@[simp] theorem mulEquiv_refl :
    ClassGroup.mulEquiv (RingEquiv.refl R) = MulEquiv.refl (ClassGroup R) := by
  apply MulEquiv.ext
  intro x
  refine ClassGroup.induction (FractionRing R) (fun I => ?_) x
  rw [MulEquiv.refl_apply, mulEquiv_mk, FractionalIdeal.ringEquivOfRingEquiv_refl]
  apply congrArg (ClassGroup.mk (FractionRing R))
  apply Units.ext
  simp

/-- Composition of ring equivalences is carried to composition of the induced class-group
equivalences. -/
@[simp] theorem mulEquiv_trans (f : R ≃+* S) (g : S ≃+* T) :
    ClassGroup.mulEquiv (f.trans g) =
      (ClassGroup.mulEquiv f).trans (ClassGroup.mulEquiv g) := by
  apply MulEquiv.ext
  intro x
  refine ClassGroup.induction (FractionRing R) (fun I => ?_) x
  rw [MulEquiv.trans_apply, mulEquiv_mk, mulEquiv_mk, mulEquiv_mk]
  apply congrArg (ClassGroup.mk (FractionRing T))
  apply Units.ext
  simpa using FractionalIdeal.ringEquivOfRingEquiv_trans_apply
    (FractionRing R) (FractionRing S) (FractionRing T) f g I

/-- Pointwise form of `ClassGroup.mulEquiv_trans`. Like `ClassGroup.mulEquiv_symm_apply'` below,
it is deliberately not a `simp` lemma: the `@[simps!]` attribute on Mathlib's
`ClassGroup.mulEquiv` provides a `simp` lemma `ClassGroup.mulEquiv_apply` that already rewrites
this left-hand side into the underlying quotient construction. -/
theorem mulEquiv_trans_apply (f : R ≃+* S) (g : S ≃+* T) (x : ClassGroup R) :
    ClassGroup.mulEquiv (f.trans g) x = ClassGroup.mulEquiv g (ClassGroup.mulEquiv f x) :=
  DFunLike.congr_fun (mulEquiv_trans f g) x

/-- Pointwise form of `ClassGroup.mulEquiv_refl`. Like `ClassGroup.mulEquiv_trans_apply`, it is
deliberately not a `simp` lemma: the `@[simps!]` attribute on Mathlib's `ClassGroup.mulEquiv`
provides a `simp` lemma `ClassGroup.mulEquiv_apply` that already owns this left-hand side. -/
theorem mulEquiv_refl_apply (x : ClassGroup R) :
    ClassGroup.mulEquiv (RingEquiv.refl R) x = x :=
  DFunLike.congr_fun mulEquiv_refl x

/-- The inverse of the class-group equivalence induced by `f` is induced by `f.symm`. -/
@[simp] theorem mulEquiv_symm (f : R ≃+* S) :
    (ClassGroup.mulEquiv f).symm = ClassGroup.mulEquiv f.symm := by
  apply MulEquiv.ext
  intro x
  apply (ClassGroup.mulEquiv f).injective
  rw [MulEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun (mulEquiv_trans f.symm f) x
  rw [f.symm_trans_self, mulEquiv_refl] at h
  exact h

/-- Pointwise form of `ClassGroup.mulEquiv_symm`. It is deliberately not a `simp` lemma: the
`@[simps!]` attribute on Mathlib's `ClassGroup.mulEquiv` already provides a `simp` lemma
`ClassGroup.mulEquiv_symm_apply` with the same left-hand side, unfolding it into the underlying
quotient construction instead. -/
theorem mulEquiv_symm_apply' (f : R ≃+* S) (x : ClassGroup S) :
    (ClassGroup.mulEquiv f).symm x = ClassGroup.mulEquiv f.symm x :=
  DFunLike.congr_fun (mulEquiv_symm f) x

/-- The action of ring automorphisms of `R` on `ClassGroup R`, bundled as a monoid homomorphism
`(R ≃+* R) →* MulAut (ClassGroup R)`. This is the object the roadmap's Galois action on ideal
classes transports along; it is the class-group analogue of
`IsFractionRing.ringEquivOfRingEquivHom`. -/
@[expose] noncomputable def mulEquivHom : (R ≃+* R) →* MulAut (ClassGroup R) where
  toFun := ClassGroup.mulEquiv
  map_one' := mulEquiv_refl
  map_mul' f g := mulEquiv_trans g f

/-- `ClassGroup.mulEquivHom` acts as `ClassGroup.mulEquiv` on each ring automorphism. -/
@[simp] theorem mulEquivHom_apply (f : R ≃+* R) :
    mulEquivHom f = ClassGroup.mulEquiv f := rfl

/-- An involutive ring equivalence induces an involution on the class group. This is the form
used for quadratic conjugation; it is the pointwise specialization of `ClassGroup.mulEquivHom`
at an order-two automorphism. -/
theorem mulEquiv_involutive {f : R ≃+* R} (hf : Function.Involutive f) :
    Function.Involutive (ClassGroup.mulEquiv f) := by
  have hff : f * f = 1 := RingEquiv.ext hf
  have h : ClassGroup.mulEquiv f * ClassGroup.mulEquiv f = 1 := by
    rw [← mulEquivHom_apply f, ← map_mul, hff, map_one]
  intro x
  have := DFunLike.congr_fun h x
  rwa [MulAut.mul_apply, MulAut.one_apply] at this

end ClassGroup
