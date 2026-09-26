/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Morita.Basic
public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Category.ModuleCat.Equivalence
public import TauCeti.CategoryTheory.Preadditive.Equivalence

/-!
# Morita invariance of `K₀(proj A)`, `G₀(mod A)` and the Cartan map

An equivalence of categories `e : ModuleCat A ≌ ModuleCat B` between the module categories of two
rings -- for instance the underlying equivalence of a Morita equivalence -- preserves and reflects
finite generation and projectivity, and it is exact. It therefore restricts to exact equivalences
between the finitely generated modules and between the finitely generated projective modules over
the two rings, and on Grothendieck groups it induces isomorphisms

```text
K₀(proj A) ≃ K₀(proj B),   G₀(mod A) ≃ G₀(mod B),
```

both sending the class of a module `M` to the class of `e.functor.obj M`. The square they form
with the two Cartan maps commutes, so the Cartan map of `A` is an isomorphism if and only if that
of `B` is. In particular, for Morita equivalent algebras `A` and `B` in Mathlib's sense
(`IsMoritaEquivalent R A B`), the groups `K₀(proj A)` and `G₀(mod A)` and the bijectivity of the
Cartan map are Morita invariants.

The special case of the equivalence induced by a ring isomorphism is
`TauCeti/Algebra/Category/ModuleCat/CartanMap/RingEquiv.lean`, where the induced maps are
described through restriction of scalars.

The API is dot notation on the equivalence: use `e.finiteModulesK0Equiv`,
`e.finiteProjectiveModulesK0Equiv` and `e.cartanMap_bijective_iff`. The two rings may live in
different universes; only the Morita corollaries put them in one, as Mathlib's
`MoritaEquivalence` does.

## Main definitions

* `CategoryTheory.Equivalence.finiteModulesEquivalence` and
  `CategoryTheory.Equivalence.finiteProjectiveModulesEquivalence`: the restrictions of an
  equivalence of module categories to the finitely generated, respectively finitely generated
  projective, modules over the two rings.
* `CategoryTheory.Equivalence.finiteModulesK0Equiv` and
  `CategoryTheory.Equivalence.finiteProjectiveModulesK0Equiv`: the induced isomorphisms
  `G₀(mod A) ≃+ G₀(mod B)` and `K₀(proj A) ≃+ K₀(proj B)`.

## Main results

* `CategoryTheory.Equivalence.finiteProjectiveModules_inverseImage`: an equivalence of module
  categories pulls the finitely generated projective modules back to the finitely generated
  projective modules.
* `CategoryTheory.Equivalence.cartanMap_comp_finiteProjectiveModulesK0Equiv` and
  `CategoryTheory.Equivalence.cartanMap_finiteProjectiveModulesK0Equiv`: the Cartan maps of `A`
  and `B` commute with the two induced isomorphisms.
* `CategoryTheory.Equivalence.cartanMap_bijective_iff`: the Cartan map of `A` is bijective if and
  only if the Cartan map of `B` is.
* `IsMoritaEquivalent.nonempty_finiteProjectiveModulesK0Equiv`,
  `IsMoritaEquivalent.nonempty_finiteModulesK0Equiv` and
  `IsMoritaEquivalent.cartanMap_bijective_iff`: the same statements for Morita equivalent
  algebras.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 2,
  for the Morita invariance of `K₀` of a ring.
-/

public section

namespace CategoryTheory.Equivalence

open CategoryTheory.ObjectProperty TauCeti

universe u u'

variable {A : Type u} [Ring A] {B : Type u'} [Ring B] (e : ModuleCat.{u} A ≌ ModuleCat.{u'} B)

/-! ### The two object properties -/

/-- An equivalence of module categories pulls the finitely generated projective `B`-modules back
to the finitely generated projective `A`-modules. -/
@[simp]
theorem finiteProjectiveModules_inverseImage :
    (finiteProjectiveModules B).inverseImage e.functor = finiteProjectiveModules A := by
  funext M
  rw [prop_inverseImage_iff, finiteProjectiveModules_iff, finiteProjectiveModules_iff,
    e.finite_functor_obj_iff, e.projective_functor_obj_iff]

/-! ### The equivalences of module subcategories -/

/-- **Finitely generated modules along an equivalence of module categories.** An equivalence
`e : ModuleCat A ≌ ModuleCat B` restricts to an equivalence from the finitely generated
`A`-modules to the finitely generated `B`-modules. -/
noncomputable def finiteModulesEquivalence : FGModuleCat.{u} A ≌ FGModuleCat.{u'} B :=
  e.congrFullSubcategory e.isFG_inverseImage

/-- **Finitely generated projective modules along an equivalence of module categories.** An
equivalence `e : ModuleCat A ≌ ModuleCat B` restricts to an equivalence from the finitely
generated projective `A`-modules to the finitely generated projective `B`-modules. -/
noncomputable def finiteProjectiveModulesEquivalence :
    (finiteProjectiveModules A).FullSubcategory ≌ (finiteProjectiveModules B).FullSubcategory :=
  e.congrFullSubcategory e.finiteProjectiveModules_inverseImage

instance : e.finiteModulesEquivalence.functor.Additive := by
  unfold finiteModulesEquivalence
  infer_instance

instance : e.finiteProjectiveModulesEquivalence.functor.Additive := by
  unfold finiteProjectiveModulesEquivalence
  infer_instance

@[simp]
theorem finiteModulesEquivalence_functor_obj_obj (M : FGModuleCat.{u} A) :
    (e.finiteModulesEquivalence.functor.obj M).obj = e.functor.obj M.obj :=
  e.congrFullSubcategory_functor_obj_obj _ M

@[simp]
theorem finiteModulesEquivalence_functor_map_hom {M N : FGModuleCat.{u} A} (f : M ⟶ N) :
    (e.finiteModulesEquivalence.functor.map f).hom =
      eqToHom (e.finiteModulesEquivalence_functor_obj_obj M) ≫ e.functor.map f.hom ≫
        eqToHom (e.finiteModulesEquivalence_functor_obj_obj N).symm :=
  e.congrFullSubcategory_functor_map_hom _ f

@[simp]
theorem finiteModulesEquivalence_inverse_obj_obj (M : FGModuleCat.{u'} B) :
    (e.finiteModulesEquivalence.inverse.obj M).obj = e.inverse.obj M.obj :=
  e.congrFullSubcategory_inverse_obj_obj _ M

@[simp]
theorem finiteModulesEquivalence_inverse_map_hom {M N : FGModuleCat.{u'} B} (f : M ⟶ N) :
    (e.finiteModulesEquivalence.inverse.map f).hom =
      eqToHom (e.finiteModulesEquivalence_inverse_obj_obj M) ≫ e.inverse.map f.hom ≫
        eqToHom (e.finiteModulesEquivalence_inverse_obj_obj N).symm :=
  e.congrFullSubcategory_inverse_map_hom _ f

@[simp]
theorem finiteProjectiveModulesEquivalence_functor_obj_obj
    (M : (finiteProjectiveModules A).FullSubcategory) :
    (e.finiteProjectiveModulesEquivalence.functor.obj M).obj = e.functor.obj M.obj :=
  e.congrFullSubcategory_functor_obj_obj _ M

@[simp]
theorem finiteProjectiveModulesEquivalence_functor_map_hom
    {M N : (finiteProjectiveModules A).FullSubcategory} (f : M ⟶ N) :
    (e.finiteProjectiveModulesEquivalence.functor.map f).hom =
      eqToHom (e.finiteProjectiveModulesEquivalence_functor_obj_obj M) ≫ e.functor.map f.hom ≫
        eqToHom (e.finiteProjectiveModulesEquivalence_functor_obj_obj N).symm :=
  e.congrFullSubcategory_functor_map_hom _ f

@[simp]
theorem finiteProjectiveModulesEquivalence_inverse_obj_obj
    (M : (finiteProjectiveModules B).FullSubcategory) :
    (e.finiteProjectiveModulesEquivalence.inverse.obj M).obj = e.inverse.obj M.obj :=
  e.congrFullSubcategory_inverse_obj_obj _ M

@[simp]
theorem finiteProjectiveModulesEquivalence_inverse_map_hom
    {M N : (finiteProjectiveModules B).FullSubcategory} (f : M ⟶ N) :
    (e.finiteProjectiveModulesEquivalence.inverse.map f).hom =
      eqToHom (e.finiteProjectiveModulesEquivalence_inverse_obj_obj M) ≫ e.inverse.map f.hom ≫
        eqToHom (e.finiteProjectiveModulesEquivalence_inverse_obj_obj N).symm :=
  e.congrFullSubcategory_inverse_map_hom _ f

/-! ### Exactness of the restricted equivalences -/

/-- The restriction of an equivalence of module categories to the finitely generated modules is
conflation-exact. -/
theorem isConflationExact_finiteModulesEquivalence_functor :
    (finiteModulesExactStructure A).IsConflationExact (finiteModulesExactStructure B)
      e.finiteModulesEquivalence.functor :=
  isConflationExact_finiteModules_congrFullSubcategory_functor _
    (ExactStructure.isConflationExact_abelian _) _

/-- The inverse of the restriction of an equivalence of module categories to the finitely
generated modules is conflation-exact. -/
theorem isConflationExact_finiteModulesEquivalence_inverse :
    (finiteModulesExactStructure B).IsConflationExact (finiteModulesExactStructure A)
      e.finiteModulesEquivalence.inverse :=
  isConflationExact_finiteModules_congrFullSubcategory_inverse _
    (ExactStructure.isConflationExact_abelian _) _

/-- The restriction of an equivalence of module categories to the finitely generated projective
modules is conflation-exact. -/
theorem isConflationExact_finiteProjectiveModulesEquivalence_functor :
    (finiteProjectiveModulesExactStructure A).IsConflationExact
      (finiteProjectiveModulesExactStructure B) e.finiteProjectiveModulesEquivalence.functor :=
  isConflationExact_finiteProjectiveModules_congrFullSubcategory_functor _
    (ExactStructure.isConflationExact_abelian _) _

/-- The inverse of the restriction of an equivalence of module categories to the finitely
generated projective modules is conflation-exact. -/
theorem isConflationExact_finiteProjectiveModulesEquivalence_inverse :
    (finiteProjectiveModulesExactStructure B).IsConflationExact
      (finiteProjectiveModulesExactStructure A) e.finiteProjectiveModulesEquivalence.inverse :=
  isConflationExact_finiteProjectiveModules_congrFullSubcategory_inverse _
    (ExactStructure.isConflationExact_abelian _) _

/-! ### The induced isomorphisms of Grothendieck groups -/

/-- **Morita invariance of `G₀(mod A)`.** An equivalence `e : ModuleCat A ≌ ModuleCat B` induces
`G₀(mod A) ≃+ G₀(mod B)`, sending the class of a finitely generated `A`-module `M` to the class
of `e.functor.obj M`. -/
noncomputable def finiteModulesK0Equiv :
    ExactK0.{u} (finiteModulesExactStructure A) ≃+ ExactK0.{u'} (finiteModulesExactStructure B) :=
  ExactK0.mapEquiv e.finiteModulesEquivalence e.isConflationExact_finiteModulesEquivalence_functor
    e.isConflationExact_finiteModulesEquivalence_inverse

/-- **Morita invariance of `K₀(proj A)`.** An equivalence `e : ModuleCat A ≌ ModuleCat B` induces
`K₀(proj A) ≃+ K₀(proj B)`, sending the class of a finitely generated projective `A`-module `M`
to the class of `e.functor.obj M`. -/
noncomputable def finiteProjectiveModulesK0Equiv :
    ExactK0.{u} (finiteProjectiveModulesExactStructure A) ≃+
      ExactK0.{u'} (finiteProjectiveModulesExactStructure B) :=
  ExactK0.mapEquiv e.finiteProjectiveModulesEquivalence
    e.isConflationExact_finiteProjectiveModulesEquivalence_functor
    e.isConflationExact_finiteProjectiveModulesEquivalence_inverse

@[simp]
theorem finiteModulesK0Equiv_of (M : FGModuleCat.{u} A) :
    e.finiteModulesK0Equiv (ExactK0.of M) = ExactK0.of (e.finiteModulesEquivalence.functor.obj M) :=
  ExactK0.mapEquiv_of.{u, u'} _ _ _ M

@[simp]
theorem finiteModulesK0Equiv_symm_of (M : FGModuleCat.{u'} B) :
    e.finiteModulesK0Equiv.symm (ExactK0.of M) =
      ExactK0.of (e.finiteModulesEquivalence.inverse.obj M) :=
  ExactK0.mapEquiv_symm_of.{u, u'} _ _ _ M

@[simp]
theorem finiteProjectiveModulesK0Equiv_of (M : (finiteProjectiveModules A).FullSubcategory) :
    e.finiteProjectiveModulesK0Equiv (ExactK0.of.{u} M) =
      ExactK0.of.{u'} (e.finiteProjectiveModulesEquivalence.functor.obj M) :=
  ExactK0.mapEquiv_of.{u, u'} _ _ _ M

@[simp]
theorem finiteProjectiveModulesK0Equiv_symm_of
    (M : (finiteProjectiveModules B).FullSubcategory) :
    e.finiteProjectiveModulesK0Equiv.symm (ExactK0.of.{u'} M) =
      ExactK0.of.{u} (e.finiteProjectiveModulesEquivalence.inverse.obj M) :=
  ExactK0.mapEquiv_symm_of.{u, u'} _ _ _ M

/-! ### Compatibility with the Cartan map -/

/-- **Morita naturality of the Cartan map.** The Cartan maps of two rings with equivalent module
categories are intertwined by the induced isomorphisms of Grothendieck groups. -/
theorem cartanMap_comp_finiteProjectiveModulesK0Equiv :
    (cartanMap B).comp e.finiteProjectiveModulesK0Equiv.toAddMonoidHom =
      e.finiteModulesK0Equiv.toAddMonoidHom.comp (cartanMap A) := by
  apply ExactK0.hom_ext
  rintro ⟨M, hM⟩
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    finiteProjectiveModulesK0Equiv_of, cartanMap_of A hM, finiteModulesK0Equiv_of]
  rw [cartanMap_of B (e.finiteProjectiveModulesEquivalence.functor.obj ⟨M, hM⟩).property]
  exact congrArg ExactK0.of (FullSubcategory.ext (by simp))

/-- Pointwise form of `CategoryTheory.Equivalence.cartanMap_comp_finiteProjectiveModulesK0Equiv`:
applying the Cartan map of `B` after transporting a class from `K₀(proj A)` along `e` agrees
with transporting its image under the Cartan map of `A` from `G₀(mod A)` along `e`. -/
@[simp]
theorem cartanMap_finiteProjectiveModulesK0Equiv
    (x : ExactK0.{u} (finiteProjectiveModulesExactStructure A)) :
    cartanMap B (e.finiteProjectiveModulesK0Equiv x) =
      e.finiteModulesK0Equiv (cartanMap A x) :=
  DFunLike.congr_fun e.cartanMap_comp_finiteProjectiveModulesK0Equiv x

include e in
/-- **The resolution-theorem hypothesis is a Morita invariant**: for rings with equivalent module
categories, the Cartan map of `A` is bijective if and only if the Cartan map of `B` is. -/
theorem cartanMap_bijective_iff :
    Function.Bijective (cartanMap A) ↔ Function.Bijective (cartanMap B) := by
  have hB : ⇑(cartanMap B) =
      ⇑e.finiteModulesK0Equiv ∘ ⇑(cartanMap A) ∘ ⇑e.finiteProjectiveModulesK0Equiv.symm := by
    ext x
    simp only [Function.comp_apply, ← cartanMap_finiteProjectiveModulesK0Equiv,
      AddEquiv.apply_symm_apply]
  have hA : ⇑(cartanMap A) =
      ⇑e.finiteModulesK0Equiv.symm ∘ ⇑(cartanMap B) ∘ ⇑e.finiteProjectiveModulesK0Equiv := by
    ext x
    simp only [Function.comp_apply, cartanMap_finiteProjectiveModulesK0Equiv,
      AddEquiv.symm_apply_apply]
  constructor
  · intro h
    rw [hB]
    exact e.finiteModulesK0Equiv.bijective.comp
      (h.comp e.finiteProjectiveModulesK0Equiv.symm.bijective)
  · intro h
    rw [hA]
    exact e.finiteModulesK0Equiv.symm.bijective.comp
      (h.comp e.finiteProjectiveModulesK0Equiv.bijective)

end CategoryTheory.Equivalence

/-! ### Morita equivalent algebras -/

namespace IsMoritaEquivalent

open CategoryTheory TauCeti

universe u₀ u

variable {R : Type u₀} [CommSemiring R] {A B : Type u} [Ring A] [Ring B] [Algebra R A]
  [Algebra R B] (h : IsMoritaEquivalent R A B)

include h

/-- **`K₀(proj A)` is a Morita invariant**: Morita equivalent algebras have isomorphic
Grothendieck groups of finitely generated projective modules. -/
theorem nonempty_finiteProjectiveModulesK0Equiv :
    Nonempty (ExactK0.{u} (finiteProjectiveModulesExactStructure A) ≃+
      ExactK0.{u} (finiteProjectiveModulesExactStructure B)) :=
  h.cond.map fun e ↦ e.eqv.finiteProjectiveModulesK0Equiv

/-- **`G₀(mod A)` is a Morita invariant**: Morita equivalent algebras have isomorphic Grothendieck
groups of finitely generated modules. -/
theorem nonempty_finiteModulesK0Equiv :
    Nonempty (ExactK0.{u} (finiteModulesExactStructure A) ≃+
      ExactK0.{u} (finiteModulesExactStructure B)) :=
  h.cond.map fun e ↦ e.eqv.finiteModulesK0Equiv

/-- **Bijectivity of the Cartan map is a Morita invariant**: for Morita equivalent algebras, the
Cartan map of `A` is bijective if and only if the Cartan map of `B` is. -/
theorem cartanMap_bijective_iff :
    Function.Bijective (cartanMap A) ↔ Function.Bijective (cartanMap B) :=
  h.cond.elim fun e ↦ e.eqv.cartanMap_bijective_iff

end IsMoritaEquivalent
