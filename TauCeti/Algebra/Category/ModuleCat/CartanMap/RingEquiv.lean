/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Morita

/-!
# `K₀(proj R)` and `G₀(mod R)` along ring isomorphisms

A ring isomorphism `e : R ≃+* S` induces, by restriction of scalars, the equivalence of module
categories `ModuleCat.restrictScalarsEquivalenceOfRingEquiv e : ModuleCat S ≌ ModuleCat R`. Its
isomorphisms of Grothendieck groups

```text
K₀(proj S) ≃ K₀(proj R),   G₀(mod S) ≃ G₀(mod R),
```

are those of `TauCeti/Algebra/Category/ModuleCat/CartanMap/Morita.lean`: they send the class of a
module to the class of the same module with scalars restricted along `e`, and they intertwine the
two Cartan maps, so the Cartan map of `R` is bijective if and only if that of `S` is. For an
algebra isomorphism `e : A ≃ₐ[k] B` the same applies to `e.toRingEquiv`, so `K₀(proj A)`,
`G₀(mod A)` and the bijectivity of the Cartan map are invariants of the isomorphism class of the
algebra `A`.

This file proves that these isomorphisms are functorial in the ring isomorphism: restriction along
the identity, the inverse and a composite of ring isomorphisms induces the identity, the inverse
and the reverse composite on Grothendieck groups. The identity and composition isomorphisms of
restriction of scalars in `ModuleCat` lift to the full subcategories, and isomorphic objects have
the same class in exact `K₀`, so these comparisons need no equality of the underlying restricted
module structures.

## Main results

* `ModuleCat.restrictScalarsEquivalenceOfRingEquiv_refl_finiteModulesK0Equiv`,
  `ModuleCat.restrictScalarsEquivalenceOfRingEquiv_finiteModulesK0Equiv_symm` and
  `ModuleCat.restrictScalarsEquivalenceOfRingEquiv_finiteModulesK0Equiv_trans`, with their
  `finiteProjectiveModulesK0Equiv` companions: the induced isomorphisms are functorial in the ring
  isomorphism.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 2,
  for the invariance of `K₀` of a ring under ring isomorphisms and Morita equivalences.
-/

public section

namespace ModuleCat

open CategoryTheory CategoryTheory.ObjectProperty TauCeti

universe u

variable {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)

/-- Restriction along the identity ring isomorphism induces the identity on `G₀(mod R)`. -/
@[simp]
theorem restrictScalarsEquivalenceOfRingEquiv_refl_finiteModulesK0Equiv :
    (restrictScalarsEquivalenceOfRingEquiv (RingEquiv.refl R)).finiteModulesK0Equiv =
      AddEquiv.refl _ :=
  AddEquiv.toAddMonoidHom_injective <| ExactK0.hom_ext fun M ↦ by
    simp only [AddEquiv.coe_toAddMonoidHom, Equivalence.finiteModulesK0Equiv_of,
      AddEquiv.refl_apply]
    apply ExactK0.of_congr
    apply ObjectProperty.isoMk
    simpa only [Equivalence.finiteModulesEquivalence_functor_obj_obj,
      restrictScalarsEquivalenceOfRingEquiv_functor, RingEquiv.toRingHom_eq_coe,
      RingEquiv.toRingHom_refl, Functor.id_obj] using (restrictScalarsId R).app M.obj

/-- Restriction along the inverse ring isomorphism induces the inverse isomorphism on `G₀`. -/
@[simp]
theorem restrictScalarsEquivalenceOfRingEquiv_finiteModulesK0Equiv_symm :
    (restrictScalarsEquivalenceOfRingEquiv e).finiteModulesK0Equiv.symm =
      (restrictScalarsEquivalenceOfRingEquiv e.symm).finiteModulesK0Equiv :=
  AddEquiv.toAddMonoidHom_injective <| ExactK0.hom_ext fun M ↦ by
    simp only [AddEquiv.coe_toAddMonoidHom, Equivalence.finiteModulesK0Equiv_symm_of,
      Equivalence.finiteModulesK0Equiv_of]
    apply congrArg ExactK0.of
    apply FullSubcategory.ext
    rw [Equivalence.finiteModulesEquivalence_inverse_obj_obj,
      Equivalence.finiteModulesEquivalence_functor_obj_obj]
    rfl

/-- Restriction along a composite of ring isomorphisms induces the reverse composite on `G₀`. -/
@[simp]
theorem restrictScalarsEquivalenceOfRingEquiv_finiteModulesK0Equiv_trans {T : Type u} [Ring T]
    (e' : S ≃+* T) :
    (restrictScalarsEquivalenceOfRingEquiv e').finiteModulesK0Equiv.trans
        (restrictScalarsEquivalenceOfRingEquiv e).finiteModulesK0Equiv =
      (restrictScalarsEquivalenceOfRingEquiv (e.trans e')).finiteModulesK0Equiv :=
  AddEquiv.toAddMonoidHom_injective <| ExactK0.hom_ext fun M ↦ by
    simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.trans_apply,
      Equivalence.finiteModulesK0Equiv_of]
    apply ExactK0.of_congr
    apply ObjectProperty.isoMk
    simpa only [Equivalence.finiteModulesEquivalence_functor_obj_obj,
      restrictScalarsEquivalenceOfRingEquiv_functor, RingEquiv.toRingHom_eq_coe,
      RingEquiv.toRingHom_trans, Functor.comp_obj] using
      (restrictScalarsComp e.toRingHom e'.toRingHom).symm.app M.obj

/-- Restriction along the identity ring isomorphism induces the identity on `K₀(proj R)`. -/
@[simp]
theorem restrictScalarsEquivalenceOfRingEquiv_refl_finiteProjectiveModulesK0Equiv :
    (restrictScalarsEquivalenceOfRingEquiv (RingEquiv.refl R)).finiteProjectiveModulesK0Equiv =
      AddEquiv.refl _ :=
  AddEquiv.toAddMonoidHom_injective <| ExactK0.hom_ext fun M ↦ by
    simp only [AddEquiv.coe_toAddMonoidHom, Equivalence.finiteProjectiveModulesK0Equiv_of,
      AddEquiv.refl_apply]
    apply ExactK0.of_congr
    apply ObjectProperty.isoMk
    simpa only [Equivalence.finiteProjectiveModulesEquivalence_functor_obj_obj,
      restrictScalarsEquivalenceOfRingEquiv_functor, RingEquiv.toRingHom_eq_coe,
      RingEquiv.toRingHom_refl, Functor.id_obj] using (restrictScalarsId R).app M.obj

/-- Restriction along the inverse ring isomorphism induces the inverse isomorphism on `K₀`. -/
@[simp]
theorem restrictScalarsEquivalenceOfRingEquiv_finiteProjectiveModulesK0Equiv_symm :
    (restrictScalarsEquivalenceOfRingEquiv e).finiteProjectiveModulesK0Equiv.symm =
      (restrictScalarsEquivalenceOfRingEquiv e.symm).finiteProjectiveModulesK0Equiv :=
  AddEquiv.toAddMonoidHom_injective <| ExactK0.hom_ext fun M ↦ by
    simp only [AddEquiv.coe_toAddMonoidHom, Equivalence.finiteProjectiveModulesK0Equiv_symm_of,
      Equivalence.finiteProjectiveModulesK0Equiv_of]
    apply congrArg ExactK0.of
    apply FullSubcategory.ext
    rw [Equivalence.finiteProjectiveModulesEquivalence_inverse_obj_obj,
      Equivalence.finiteProjectiveModulesEquivalence_functor_obj_obj]
    rfl

/-- Restriction along a composite of ring isomorphisms induces the reverse composite on `K₀`. -/
@[simp]
theorem restrictScalarsEquivalenceOfRingEquiv_finiteProjectiveModulesK0Equiv_trans {T : Type u}
    [Ring T] (e' : S ≃+* T) :
    (restrictScalarsEquivalenceOfRingEquiv e').finiteProjectiveModulesK0Equiv.trans
        (restrictScalarsEquivalenceOfRingEquiv e).finiteProjectiveModulesK0Equiv =
      (restrictScalarsEquivalenceOfRingEquiv (e.trans e')).finiteProjectiveModulesK0Equiv :=
  AddEquiv.toAddMonoidHom_injective <| ExactK0.hom_ext fun M ↦ by
    simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.trans_apply,
      Equivalence.finiteProjectiveModulesK0Equiv_of]
    apply ExactK0.of_congr
    apply ObjectProperty.isoMk
    simpa only [Equivalence.finiteProjectiveModulesEquivalence_functor_obj_obj,
      restrictScalarsEquivalenceOfRingEquiv_functor, RingEquiv.toRingHom_eq_coe,
      RingEquiv.toRingHom_trans, Functor.comp_obj] using
      (restrictScalarsComp e.toRingHom e'.toRingHom).symm.app M.obj

end ModuleCat
