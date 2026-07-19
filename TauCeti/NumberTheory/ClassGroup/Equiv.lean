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
induced map respects identity, composition, and inverses.

This is a prerequisite for the genus-field layer of the multiquadratic roadmap. For a quadratic
field, conjugation is a ring automorphism of its ring of integers; the roadmap's proof that
conjugation acts on the class group by inversion first needs to treat that action functorially and
compute it on ideal classes.

## Main results

* `ClassGroup.mulEquiv_refl`: the identity ring equivalence induces the identity on class groups.
* `ClassGroup.mulEquiv_trans`: induced equivalences respect composition.
* `ClassGroup.mulEquiv_symm`: the inverse induced equivalence comes from the inverse ring
  equivalence.
* `ClassGroup.mulEquiv_involutive`: an involutive ring equivalence acts involutively on the class
  group.
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
  simp only [MulEquiv.refl_apply]
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

/-- Pointwise form of `ClassGroup.mulEquiv_trans`. Like `ClassGroup.mulEquiv_symm_apply'` below,
it is deliberately not a `simp` lemma: the `@[simps!]` attribute on Mathlib's
`ClassGroup.mulEquiv` provides a `simp` lemma `ClassGroup.mulEquiv_apply` that already rewrites
this left-hand side into the underlying quotient construction. -/
theorem mulEquiv_trans_apply (f : R ≃+* S) (g : S ≃+* T) (x : ClassGroup R) :
    ClassGroup.mulEquiv (f.trans g) x = ClassGroup.mulEquiv g (ClassGroup.mulEquiv f x) :=
  DFunLike.congr_fun (mulEquiv_trans f g) x

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

/-- Pointwise form of `ClassGroup.mulEquiv_symm`. It is deliberately not a `simp` lemma: the
`@[simps!]` attribute on Mathlib's `ClassGroup.mulEquiv` already provides a `simp` lemma
`ClassGroup.mulEquiv_symm_apply` with the same left-hand side, unfolding it into the underlying
quotient construction instead. -/
theorem mulEquiv_symm_apply' (f : R ≃+* S) (x : ClassGroup S) :
    (ClassGroup.mulEquiv f).symm x = ClassGroup.mulEquiv f.symm x :=
  DFunLike.congr_fun (mulEquiv_symm f) x

/-- An involutive ring equivalence induces an involution on the class group. This is the form
used for quadratic conjugation. -/
theorem mulEquiv_involutive {f : R ≃+* R} (hf : Function.Involutive f) :
    Function.Involutive (ClassGroup.mulEquiv f) := fun x => by
  have hff : f.trans f = RingEquiv.refl R := RingEquiv.ext hf
  have h := DFunLike.congr_fun (mulEquiv_trans f f) x
  rw [hff, mulEquiv_refl] at h
  exact h.symm

end ClassGroup
