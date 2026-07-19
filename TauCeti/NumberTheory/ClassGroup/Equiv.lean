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
induced map respects identity, composition, and inverses, and its value on the class of a nonzero
integral ideal is represented by the transported ideal.

This is a prerequisite for the genus-field layer of the multiquadratic roadmap. For a quadratic
field, conjugation is a ring automorphism of its ring of integers; the roadmap's proof that
conjugation acts on the class group by inversion first needs to treat that action functorially and
compute it on ideal classes.

## Main results

* `ClassGroup.mulEquiv_refl`: the identity ring equivalence induces the identity on class groups.
* `ClassGroup.mulEquiv_trans`: induced equivalences respect composition.
* `ClassGroup.mulEquiv_symm`: the inverse induced equivalence comes from the inverse ring
  equivalence.
* `ClassGroup.mulEquiv_apply_apply_of_trans_eq_refl`: an involutive ring equivalence acts
  involutively on the class group.
-/

public section

namespace ClassGroup

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [IsDomain R] [IsDomain S] [IsDomain T]

/-- The identity ring equivalence induces the identity map on the class group. -/
@[simp] theorem mulEquiv_refl_apply (x : ClassGroup R) :
    ClassGroup.mulEquiv (RingEquiv.refl R) x = x := by
  refine ClassGroup.induction (FractionRing R) (fun I => ?_) x
  rw [ClassGroup.mulEquiv_apply]
  apply (ClassGroup.equiv (FractionRing R)).injective
  rw [MulEquiv.apply_symm_apply, ClassGroup.equiv_mk, QuotientGroup.congr_mk']
  congr 1
  apply Units.ext
  simp [FractionalIdeal.ringEquivOfRingEquiv_refl]

/-- Class-group equivalences induced by ring equivalences respect composition. -/
@[simp] theorem mulEquiv_trans_apply (f : R ≃+* S) (g : S ≃+* T) (x : ClassGroup R) :
    ClassGroup.mulEquiv (f.trans g) x =
      ClassGroup.mulEquiv g (ClassGroup.mulEquiv f x) := by
  refine ClassGroup.induction (FractionRing R) (fun I => ?_) x
  simp only [ClassGroup.mulEquiv_apply, ClassGroup.equiv_mk, MulEquiv.apply_symm_apply,
    QuotientGroup.congr_mk']
  apply congrArg (QuotientGroup.mk' (toPrincipalIdeal T (FractionRing T)).range)
  apply Units.ext
  simpa [FractionalIdeal.canonicalEquiv_self] using
    FractionalIdeal.ringEquivOfRingEquiv_trans_apply
      (FractionRing R) (FractionRing S) (FractionRing T) f g I

/-- The class-group equivalence induced by the inverse ring equivalence undoes the original
induced equivalence. -/
@[simp] theorem mulEquiv_symm_apply_apply (f : R ≃+* S) (x : ClassGroup R) :
    ClassGroup.mulEquiv f.symm (ClassGroup.mulEquiv f x) = x := by
  rw [← mulEquiv_trans_apply, f.self_trans_symm, mulEquiv_refl_apply]

/-- The class-group equivalence induced by a ring equivalence undoes the map induced by its
inverse. -/
@[simp] theorem mulEquiv_apply_symm_apply (f : R ≃+* S) (x : ClassGroup S) :
    ClassGroup.mulEquiv f (ClassGroup.mulEquiv f.symm x) = x := by
  rw [← mulEquiv_trans_apply, f.symm_trans_self, mulEquiv_refl_apply]

/-- The inverse of the class-group equivalence induced by `f` is induced by `f.symm`. -/
theorem mulEquiv_symm (f : R ≃+* S) :
    (ClassGroup.mulEquiv f).symm = ClassGroup.mulEquiv f.symm := by
  ext x
  apply (ClassGroup.mulEquiv f).injective
  rw [MulEquiv.apply_symm_apply, mulEquiv_apply_symm_apply]

/-- The identity ring equivalence induces the identity class-group equivalence. -/
@[simp] theorem mulEquiv_refl :
    ClassGroup.mulEquiv (RingEquiv.refl R) = MulEquiv.refl (ClassGroup R) := by
  ext x
  exact mulEquiv_refl_apply x

/-- Composition of ring equivalences is carried to composition of the induced class-group
equivalences. -/
theorem mulEquiv_trans (f : R ≃+* S) (g : S ≃+* T) :
    ClassGroup.mulEquiv (f.trans g) =
      (ClassGroup.mulEquiv f).trans (ClassGroup.mulEquiv g) := by
  ext x
  exact mulEquiv_trans_apply f g x

/-- An involutive ring equivalence induces an involution on the class group. This is the form
used for quadratic conjugation. -/
theorem mulEquiv_apply_apply_of_trans_eq_refl (f : R ≃+* R)
    (hf : f.trans f = RingEquiv.refl R) (x : ClassGroup R) :
    ClassGroup.mulEquiv f (ClassGroup.mulEquiv f x) = x := by
  rw [← mulEquiv_trans_apply, hf, mulEquiv_refl_apply]

end ClassGroup
