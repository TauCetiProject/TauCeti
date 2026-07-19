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

/-- The identity ring equivalence induces the identity class-group equivalence. -/
@[simp] theorem mulEquiv_refl :
    ClassGroup.mulEquiv (RingEquiv.refl R) = MulEquiv.refl (ClassGroup R) := by
  apply MulEquiv.ext
  intro x
  change ClassGroup.mulEquiv (RingEquiv.refl R) x = x
  refine ClassGroup.induction (FractionRing R) (fun I => ?_) x
  rw [ClassGroup.mulEquiv_apply]
  apply (ClassGroup.equiv (FractionRing R)).injective
  rw [MulEquiv.apply_symm_apply, ClassGroup.equiv_mk, QuotientGroup.congr_mk']
  congr 1
  apply Units.ext
  simp [FractionalIdeal.ringEquivOfRingEquiv_refl]

/-- Composition of ring equivalences is carried to composition of the induced class-group
equivalences. -/
theorem mulEquiv_trans (f : R ≃+* S) (g : S ≃+* T) :
    ClassGroup.mulEquiv (f.trans g) =
      (ClassGroup.mulEquiv f).trans (ClassGroup.mulEquiv g) := by
  apply MulEquiv.ext
  intro x
  refine ClassGroup.induction (FractionRing R) (fun I => ?_) x
  simp only [ClassGroup.mulEquiv_apply, ClassGroup.equiv_mk, QuotientGroup.congr_mk']
  apply congrArg (QuotientGroup.mk' (toPrincipalIdeal T (FractionRing T)).range)
  apply Units.ext
  simpa [FractionalIdeal.canonicalEquiv_self] using
    FractionalIdeal.ringEquivOfRingEquiv_trans_apply
      (FractionRing R) (FractionRing S) (FractionRing T) f g I

/-- The inverse of the class-group equivalence induced by `f` is induced by `f.symm`. -/
theorem mulEquiv_symm (f : R ≃+* S) :
    (ClassGroup.mulEquiv f).symm = ClassGroup.mulEquiv f.symm := by
  apply MulEquiv.ext
  intro x
  apply (ClassGroup.mulEquiv f).injective
  rw [MulEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun (mulEquiv_trans f.symm f) x
  rw [f.symm_trans_self, mulEquiv_refl] at h
  exact h

/-- An involutive ring equivalence induces an involution on the class group. This is the form
used for quadratic conjugation. -/
theorem mulEquiv_apply_apply_of_trans_eq_refl (f : R ≃+* R)
    (hf : f.trans f = RingEquiv.refl R) (x : ClassGroup R) :
    ClassGroup.mulEquiv f (ClassGroup.mulEquiv f x) = x := by
  have h := DFunLike.congr_fun (mulEquiv_trans f f) x
  rw [hf, mulEquiv_refl] at h
  exact h.symm

end ClassGroup
