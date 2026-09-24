/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Basic
public import TauCeti.Algebra.Category.ModuleCat.RestrictScalars

/-!
# Invariance of `K₀(proj R)`, `G₀(mod R)` and the Cartan map under ring isomorphisms

A ring isomorphism `e : R ≃+* S` induces, by restriction of scalars, an equivalence of module
categories `ModuleCat S ≌ ModuleCat R`. It preserves and reflects finite generation and
projectivity, and it is exact, so it restricts to exact equivalences between the finitely
generated modules and between the finitely generated projective modules over the two rings. On
Grothendieck groups this gives isomorphisms

```text
K₀(proj S) ≃ K₀(proj R),   G₀(mod S) ≃ G₀(mod R),
```

both sending the class of a module to the class of the same module with scalars restricted along
`e`, and the square they form with the two Cartan maps commutes. In particular the Cartan map of
`R` is an isomorphism if and only if that of `S` is.

For an algebra isomorphism `e : A ≃ₐ[k] B` the statements apply to `e.toRingEquiv`, so
`K₀(proj A)`, `G₀(mod A)` and the Cartan map are invariants of the isomorphism class of the
algebra `A`.

The API is dot notation on the ring isomorphism: use `e.finiteModulesK0Equiv`,
`e.finiteProjectiveModulesK0Equiv` and `e.cartanMap_bijective_iff`.

## Main definitions

* `RingEquiv.finiteModulesEquivalence` and `RingEquiv.finiteProjectiveModulesEquivalence`:
  restriction of scalars along a ring isomorphism, as equivalences between the finitely generated,
  respectively finitely generated projective, modules over the two rings.
* `RingEquiv.finiteModulesK0Equiv` and `RingEquiv.finiteProjectiveModulesK0Equiv`: the induced
  isomorphisms `G₀(mod S) ≃+ G₀(mod R)` and `K₀(proj S) ≃+ K₀(proj R)`.

## Main results

* `RingEquiv.isFG_inverseImage_restrictScalars` and
  `RingEquiv.finiteProjectiveModules_inverseImage_restrictScalars`: restriction of scalars along a
  ring isomorphism pulls the two object properties back to each other.
* `RingEquiv.finiteModulesK0Equiv_refl`, `RingEquiv.finiteModulesK0Equiv_symm` and
  `RingEquiv.finiteModulesK0Equiv_trans`, with their `finiteProjectiveModulesK0Equiv`
  companions: the induced isomorphisms are functorial in the ring isomorphism.
* `RingEquiv.cartanMap_comp_finiteProjectiveModulesK0Equiv` and
  `RingEquiv.cartanMap_finiteProjectiveModulesK0Equiv`: the Cartan maps of `R` and `S` commute
  with the two induced isomorphisms.
* `RingEquiv.cartanMap_bijective_iff`: the Cartan map of `R` is bijective if and only if the
  Cartan map of `S` is.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, Section 2,
  for the invariance of `K₀` of a ring under ring isomorphisms and Morita equivalences.
-/

public section

namespace RingEquiv

open CategoryTheory CategoryTheory.ObjectProperty TauCeti

universe u

variable {R S : Type u} [Ring R] [Ring S] (e : R ≃+* S)

/-! ### Restriction of scalars on the two object properties -/

/-- Restriction of scalars along a ring isomorphism pulls the finitely generated `R`-modules
back to the finitely generated `S`-modules. -/
theorem isFG_inverseImage_restrictScalars :
    (ModuleCat.isFG.{u} R).inverseImage (ModuleCat.restrictScalars e.toRingHom) =
      ModuleCat.isFG.{u} S :=
  funext fun M ↦ propext (e.toRingHom.isFG_restrictScalars_iff e.surjective M)

/-- Restriction of scalars along a ring isomorphism pulls the finitely generated projective
`R`-modules back to the finitely generated projective `S`-modules. -/
theorem finiteProjectiveModules_inverseImage_restrictScalars :
    (finiteProjectiveModules R).inverseImage (ModuleCat.restrictScalars e.toRingHom) =
      finiteProjectiveModules S := by
  funext M
  rw [prop_inverseImage_iff, finiteProjectiveModules_iff, finiteProjectiveModules_iff,
    e.toRingHom.finite_restrictScalars_iff e.surjective, e.projective_restrictScalars_iff]

/-! ### The equivalences of module subcategories

The two pullback equalities above are transported along
`ModuleCat.restrictScalarsEquivalenceOfRingEquiv_functor` before being passed to
`CategoryTheory.Equivalence.congrFullSubcategory`: the additivity instance of the restricted
equivalence is found by instance search only when the hypothesis is stated syntactically for the
functor of `ModuleCat.restrictScalarsEquivalenceOfRingEquiv e`. -/

/-- **Restriction of scalars on finitely generated modules.** A ring isomorphism `e : R ≃+* S`
induces an equivalence from the finitely generated `S`-modules to the finitely generated
`R`-modules, sending a module to the same module with scalars restricted along `e`. -/
noncomputable def finiteModulesEquivalence : FGModuleCat.{u} S ≌ FGModuleCat.{u} R :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).congrFullSubcategory
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv_functor e ▸
      e.isFG_inverseImage_restrictScalars)

/-- **Restriction of scalars on finitely generated projective modules.** A ring isomorphism
`e : R ≃+* S` induces an equivalence from the finitely generated projective `S`-modules to the
finitely generated projective `R`-modules, sending a module to the same module with scalars
restricted along `e`. -/
noncomputable def finiteProjectiveModulesEquivalence :
    (finiteProjectiveModules S).FullSubcategory ≌ (finiteProjectiveModules R).FullSubcategory :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).congrFullSubcategory
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv_functor e ▸
      e.finiteProjectiveModules_inverseImage_restrictScalars)

instance : e.finiteModulesEquivalence.functor.Additive := by
  unfold finiteModulesEquivalence
  infer_instance

instance : e.finiteProjectiveModulesEquivalence.functor.Additive := by
  unfold finiteProjectiveModulesEquivalence
  infer_instance

@[simp]
theorem finiteModulesEquivalence_functor_obj_obj (M : FGModuleCat.{u} S) :
    (e.finiteModulesEquivalence.functor.obj M).obj =
      (ModuleCat.restrictScalars e.toRingHom).obj M.obj := by
  simp only [finiteModulesEquivalence, Equivalence.congrFullSubcategory_functor_eq_lift,
    lift_obj_obj, Functor.comp_obj, ι_obj,
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv_functor]

@[simp]
theorem finiteModulesEquivalence_functor_map_hom {M N : FGModuleCat.{u} S} (f : M ⟶ N) :
    (e.finiteModulesEquivalence.functor.map f).hom =
      eqToHom (e.finiteModulesEquivalence_functor_obj_obj M) ≫
        (ModuleCat.restrictScalars e.toRingHom).map f.hom ≫
        eqToHom (e.finiteModulesEquivalence_functor_obj_obj N).symm := by
  have h : e.finiteModulesEquivalence.functor ⋙ (ModuleCat.isFG R).ι =
      (ModuleCat.isFG S).ι ⋙ ModuleCat.restrictScalars e.toRingHom := by
    rw [finiteModulesEquivalence, Equivalence.congrFullSubcategory_functor_comp_ι,
      ModuleCat.restrictScalarsEquivalenceOfRingEquiv_functor]
  simpa only [Functor.comp_map, ι_map] using Functor.congr_hom h f

@[simp]
theorem finiteModulesEquivalence_inverse_obj_obj (M : FGModuleCat.{u} R) :
    (e.finiteModulesEquivalence.inverse.obj M).obj =
      (ModuleCat.restrictScalars e.symm.toRingHom).obj M.obj := by
  simp only [finiteModulesEquivalence, Equivalence.congrFullSubcategory_inverse_eq_lift,
    lift_obj_obj, Functor.comp_obj, ι_obj,
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv_inverse, toRingHom_eq_coe]

@[simp]
theorem finiteModulesEquivalence_inverse_map_hom {M N : FGModuleCat.{u} R} (f : M ⟶ N) :
    (e.finiteModulesEquivalence.inverse.map f).hom =
      eqToHom (e.finiteModulesEquivalence_inverse_obj_obj M) ≫
        (ModuleCat.restrictScalars e.symm.toRingHom).map f.hom ≫
        eqToHom (e.finiteModulesEquivalence_inverse_obj_obj N).symm := by
  have h : e.finiteModulesEquivalence.inverse ⋙ (ModuleCat.isFG S).ι =
      (ModuleCat.isFG R).ι ⋙ ModuleCat.restrictScalars e.symm.toRingHom := by
    rw [finiteModulesEquivalence, Equivalence.congrFullSubcategory_inverse_comp_ι,
      ModuleCat.restrictScalarsEquivalenceOfRingEquiv_inverse, toRingHom_eq_coe]
  simpa only [Functor.comp_map, ι_map] using Functor.congr_hom h f

@[simp]
theorem finiteProjectiveModulesEquivalence_functor_obj_obj
    (M : (finiteProjectiveModules S).FullSubcategory) :
    (e.finiteProjectiveModulesEquivalence.functor.obj M).obj =
      (ModuleCat.restrictScalars e.toRingHom).obj M.obj := by
  simp only [finiteProjectiveModulesEquivalence,
    Equivalence.congrFullSubcategory_functor_eq_lift, lift_obj_obj, Functor.comp_obj, ι_obj,
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv_functor]

@[simp]
theorem finiteProjectiveModulesEquivalence_functor_map_hom
    {M N : (finiteProjectiveModules S).FullSubcategory} (f : M ⟶ N) :
    (e.finiteProjectiveModulesEquivalence.functor.map f).hom =
      eqToHom (e.finiteProjectiveModulesEquivalence_functor_obj_obj M) ≫
        (ModuleCat.restrictScalars e.toRingHom).map f.hom ≫
        eqToHom (e.finiteProjectiveModulesEquivalence_functor_obj_obj N).symm := by
  have h : e.finiteProjectiveModulesEquivalence.functor ⋙ (finiteProjectiveModules R).ι =
      (finiteProjectiveModules S).ι ⋙ ModuleCat.restrictScalars e.toRingHom := by
    rw [finiteProjectiveModulesEquivalence, Equivalence.congrFullSubcategory_functor_comp_ι,
      ModuleCat.restrictScalarsEquivalenceOfRingEquiv_functor]
  simpa only [Functor.comp_map, ι_map] using Functor.congr_hom h f

@[simp]
theorem finiteProjectiveModulesEquivalence_inverse_obj_obj
    (M : (finiteProjectiveModules R).FullSubcategory) :
    (e.finiteProjectiveModulesEquivalence.inverse.obj M).obj =
      (ModuleCat.restrictScalars e.symm.toRingHom).obj M.obj := by
  simp only [finiteProjectiveModulesEquivalence,
    Equivalence.congrFullSubcategory_inverse_eq_lift, lift_obj_obj, Functor.comp_obj, ι_obj,
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv_inverse, toRingHom_eq_coe]

@[simp]
theorem finiteProjectiveModulesEquivalence_inverse_map_hom
    {M N : (finiteProjectiveModules R).FullSubcategory} (f : M ⟶ N) :
    (e.finiteProjectiveModulesEquivalence.inverse.map f).hom =
      eqToHom (e.finiteProjectiveModulesEquivalence_inverse_obj_obj M) ≫
        (ModuleCat.restrictScalars e.symm.toRingHom).map f.hom ≫
        eqToHom (e.finiteProjectiveModulesEquivalence_inverse_obj_obj N).symm := by
  have h : e.finiteProjectiveModulesEquivalence.inverse ⋙ (finiteProjectiveModules S).ι =
      (finiteProjectiveModules R).ι ⋙ ModuleCat.restrictScalars e.symm.toRingHom := by
    rw [finiteProjectiveModulesEquivalence, Equivalence.congrFullSubcategory_inverse_comp_ι,
      ModuleCat.restrictScalarsEquivalenceOfRingEquiv_inverse, toRingHom_eq_coe]
  simpa only [Functor.comp_map, ι_map] using Functor.congr_hom h f

/-- The equivalence of finitely generated module categories induced by a ring isomorphism is
conflation-exact. -/
theorem isConflationExact_finiteModulesEquivalence_functor :
    (finiteModulesExactStructure S).IsConflationExact (finiteModulesExactStructure R)
      e.finiteModulesEquivalence.functor :=
  Equivalence.isConflationExact_finiteModules_congrFullSubcategory_functor _
    (ExactStructure.isConflationExact_abelian _) _

/-- The inverse of the equivalence of finitely generated module categories induced by a ring
isomorphism is conflation-exact. -/
theorem isConflationExact_finiteModulesEquivalence_inverse :
    (finiteModulesExactStructure R).IsConflationExact (finiteModulesExactStructure S)
      e.finiteModulesEquivalence.inverse :=
  Equivalence.isConflationExact_finiteModules_congrFullSubcategory_inverse _
    (ExactStructure.isConflationExact_abelian _) _

/-- The equivalence of finitely generated projective module categories induced by a ring
isomorphism is conflation-exact. -/
theorem isConflationExact_finiteProjectiveModulesEquivalence_functor :
    (finiteProjectiveModulesExactStructure S).IsConflationExact
      (finiteProjectiveModulesExactStructure R) e.finiteProjectiveModulesEquivalence.functor :=
  Equivalence.isConflationExact_finiteProjectiveModules_congrFullSubcategory_functor _
    (ExactStructure.isConflationExact_abelian _) _

/-- The inverse of the equivalence of finitely generated projective module categories induced by
a ring isomorphism is conflation-exact. -/
theorem isConflationExact_finiteProjectiveModulesEquivalence_inverse :
    (finiteProjectiveModulesExactStructure R).IsConflationExact
      (finiteProjectiveModulesExactStructure S) e.finiteProjectiveModulesEquivalence.inverse :=
  Equivalence.isConflationExact_finiteProjectiveModules_congrFullSubcategory_inverse _
    (ExactStructure.isConflationExact_abelian _) _

/-! ### The induced isomorphisms of Grothendieck groups -/

/-- **Invariance of `G₀(mod R)` under ring isomorphisms.** A ring isomorphism `e : R ≃+* S`
induces `G₀(mod S) ≃+ G₀(mod R)`, sending the class of a finitely generated `S`-module to the
class of the same module with scalars restricted along `e`. -/
noncomputable def finiteModulesK0Equiv :
    ExactK0.{u} (finiteModulesExactStructure S) ≃+ ExactK0.{u} (finiteModulesExactStructure R) :=
  ExactK0.mapEquiv e.finiteModulesEquivalence e.isConflationExact_finiteModulesEquivalence_functor
    e.isConflationExact_finiteModulesEquivalence_inverse

/-- **Invariance of `K₀(proj R)` under ring isomorphisms.** A ring isomorphism `e : R ≃+* S`
induces `K₀(proj S) ≃+ K₀(proj R)`, sending the class of a finitely generated projective
`S`-module to the class of the same module with scalars restricted along `e`. -/
noncomputable def finiteProjectiveModulesK0Equiv :
    ExactK0.{u} (finiteProjectiveModulesExactStructure S) ≃+
      ExactK0.{u} (finiteProjectiveModulesExactStructure R) :=
  ExactK0.mapEquiv e.finiteProjectiveModulesEquivalence
    e.isConflationExact_finiteProjectiveModulesEquivalence_functor
    e.isConflationExact_finiteProjectiveModulesEquivalence_inverse

@[simp]
theorem finiteModulesK0Equiv_of (M : FGModuleCat.{u} S) :
    e.finiteModulesK0Equiv (ExactK0.of M) = ExactK0.of (e.finiteModulesEquivalence.functor.obj M) :=
  ExactK0.mapEquiv_of.{u, u} _ _ _ M

-- Not a `simp` lemma: `simp` normalises the left-hand side through `finiteModulesK0Equiv_symm`
-- and `finiteModulesK0Equiv_of` instead.
theorem finiteModulesK0Equiv_symm_of (M : FGModuleCat.{u} R) :
    e.finiteModulesK0Equiv.symm (ExactK0.of M) =
      ExactK0.of (e.finiteModulesEquivalence.inverse.obj M) :=
  ExactK0.mapEquiv_symm_of.{u, u} _ _ _ M

@[simp]
theorem finiteProjectiveModulesK0Equiv_of (M : (finiteProjectiveModules S).FullSubcategory) :
    e.finiteProjectiveModulesK0Equiv (ExactK0.of.{u} M) =
      ExactK0.of.{u} (e.finiteProjectiveModulesEquivalence.functor.obj M) :=
  ExactK0.mapEquiv_of.{u, u} _ _ _ M

-- Not a `simp` lemma: `simp` normalises the left-hand side through
-- `finiteProjectiveModulesK0Equiv_symm` and `finiteProjectiveModulesK0Equiv_of` instead.
theorem finiteProjectiveModulesK0Equiv_symm_of
    (M : (finiteProjectiveModules R).FullSubcategory) :
    e.finiteProjectiveModulesK0Equiv.symm (ExactK0.of.{u} M) =
      ExactK0.of.{u} (e.finiteProjectiveModulesEquivalence.inverse.obj M) :=
  ExactK0.mapEquiv_symm_of.{u, u} _ _ _ M

/-! ### Functoriality in the ring isomorphism

Restriction of scalars along the identity, along the inverse and along a composite of ring
isomorphisms identifies with the identity, the inverse and the composite of the restrictions.
The identity and composition isomorphisms in `ModuleCat` lift to the full subcategories.
Isomorphic objects have the same class in exact `K₀`, so these comparisons give functoriality
without requiring equality of the underlying restricted module structures. -/

/-- Restriction along the identity ring isomorphism induces the identity on `G₀(mod R)`. -/
@[simp]
theorem finiteModulesK0Equiv_refl :
    (RingEquiv.refl R).finiteModulesK0Equiv = AddEquiv.refl _ :=
  AddEquiv.toAddMonoidHom_injective <| ExactK0.hom_ext fun M ↦ by
    simp only [AddEquiv.coe_toAddMonoidHom, finiteModulesK0Equiv_of, AddEquiv.refl_apply]
    apply ExactK0.of_congr
    apply ObjectProperty.isoMk
    simpa only [finiteModulesEquivalence_functor_obj_obj, toRingHom_refl, Functor.id_obj] using
      (ModuleCat.restrictScalarsId R).app M.obj

/-- Restriction along the inverse ring isomorphism induces the inverse isomorphism on `G₀`. -/
@[simp]
theorem finiteModulesK0Equiv_symm : e.finiteModulesK0Equiv.symm = e.symm.finiteModulesK0Equiv :=
  AddEquiv.toAddMonoidHom_injective <| ExactK0.hom_ext fun M ↦ by
    simp only [AddEquiv.coe_toAddMonoidHom, finiteModulesK0Equiv_symm_of, finiteModulesK0Equiv_of]
    apply congrArg ExactK0.of
    apply FullSubcategory.ext
    rw [finiteModulesEquivalence_inverse_obj_obj, finiteModulesEquivalence_functor_obj_obj]

/-- Restriction along a composite of ring isomorphisms induces the reverse composite on `G₀`. -/
@[simp]
theorem finiteModulesK0Equiv_trans {T : Type u} [Ring T] (e' : S ≃+* T) :
    e'.finiteModulesK0Equiv.trans e.finiteModulesK0Equiv = (e.trans e').finiteModulesK0Equiv :=
  AddEquiv.toAddMonoidHom_injective <| ExactK0.hom_ext fun M ↦ by
    simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.trans_apply, finiteModulesK0Equiv_of]
    apply ExactK0.of_congr
    apply ObjectProperty.isoMk
    simpa only [finiteModulesEquivalence_functor_obj_obj, toRingHom_trans, Functor.comp_obj] using
      (ModuleCat.restrictScalarsComp e.toRingHom e'.toRingHom).symm.app M.obj

/-- Restriction along the identity ring isomorphism induces the identity on `K₀(proj R)`. -/
@[simp]
theorem finiteProjectiveModulesK0Equiv_refl :
    (RingEquiv.refl R).finiteProjectiveModulesK0Equiv = AddEquiv.refl _ :=
  AddEquiv.toAddMonoidHom_injective <| ExactK0.hom_ext fun M ↦ by
    simp only [AddEquiv.coe_toAddMonoidHom, finiteProjectiveModulesK0Equiv_of,
      AddEquiv.refl_apply]
    apply ExactK0.of_congr
    apply ObjectProperty.isoMk
    simpa only [finiteProjectiveModulesEquivalence_functor_obj_obj, toRingHom_refl,
      Functor.id_obj] using
      (ModuleCat.restrictScalarsId R).app M.obj

/-- Restriction along the inverse ring isomorphism induces the inverse isomorphism on `K₀`. -/
@[simp]
theorem finiteProjectiveModulesK0Equiv_symm :
    e.finiteProjectiveModulesK0Equiv.symm = e.symm.finiteProjectiveModulesK0Equiv :=
  AddEquiv.toAddMonoidHom_injective <| ExactK0.hom_ext fun M ↦ by
    simp only [AddEquiv.coe_toAddMonoidHom, finiteProjectiveModulesK0Equiv_symm_of,
      finiteProjectiveModulesK0Equiv_of]
    apply congrArg ExactK0.of
    apply FullSubcategory.ext
    rw [finiteProjectiveModulesEquivalence_inverse_obj_obj,
      finiteProjectiveModulesEquivalence_functor_obj_obj]

/-- Restriction along a composite of ring isomorphisms induces the reverse composite on `K₀`. -/
@[simp]
theorem finiteProjectiveModulesK0Equiv_trans {T : Type u} [Ring T] (e' : S ≃+* T) :
    e'.finiteProjectiveModulesK0Equiv.trans e.finiteProjectiveModulesK0Equiv =
      (e.trans e').finiteProjectiveModulesK0Equiv :=
  AddEquiv.toAddMonoidHom_injective <| ExactK0.hom_ext fun M ↦ by
    simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.trans_apply,
      finiteProjectiveModulesK0Equiv_of]
    apply ExactK0.of_congr
    apply ObjectProperty.isoMk
    simpa only [finiteProjectiveModulesEquivalence_functor_obj_obj, toRingHom_trans,
      Functor.comp_obj] using
      (ModuleCat.restrictScalarsComp e.toRingHom e'.toRingHom).symm.app M.obj

/-! ### Compatibility with the Cartan map -/

/-- **Naturality of the Cartan map in the ring.** The Cartan maps of two isomorphic rings are
intertwined by the induced isomorphisms of Grothendieck groups. -/
theorem cartanMap_comp_finiteProjectiveModulesK0Equiv :
    (cartanMap R).comp e.finiteProjectiveModulesK0Equiv.toAddMonoidHom =
      e.finiteModulesK0Equiv.toAddMonoidHom.comp (cartanMap S) := by
  apply ExactK0.hom_ext
  rintro ⟨M, hM⟩
  simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    finiteProjectiveModulesK0Equiv_of, cartanMap_of S hM, finiteModulesK0Equiv_of]
  rw [cartanMap_of R (e.finiteProjectiveModulesEquivalence.functor.obj ⟨M, hM⟩).property]
  exact congrArg ExactK0.of (FullSubcategory.ext (by simp))

/-- Pointwise form of `RingEquiv.cartanMap_comp_finiteProjectiveModulesK0Equiv`: applying the
Cartan map of `R` after transporting a class from `K₀(proj S)` along `e` agrees with transporting
its image under the Cartan map of `S` from `G₀(mod S)` along `e`. -/
@[simp]
theorem cartanMap_finiteProjectiveModulesK0Equiv
    (x : ExactK0.{u} (finiteProjectiveModulesExactStructure S)) :
    cartanMap R (e.finiteProjectiveModulesK0Equiv x) =
      e.finiteModulesK0Equiv (cartanMap S x) :=
  DFunLike.congr_fun e.cartanMap_comp_finiteProjectiveModulesK0Equiv x

include e in
/-- **The resolution-theorem hypothesis is invariant under ring isomorphisms**: the Cartan map of
`R` is bijective if and only if the Cartan map of `S` is. -/
theorem cartanMap_bijective_iff :
    Function.Bijective (cartanMap R) ↔ Function.Bijective (cartanMap S) := by
  have hR : ⇑(cartanMap R) =
      ⇑e.finiteModulesK0Equiv ∘ ⇑(cartanMap S) ∘ ⇑e.finiteProjectiveModulesK0Equiv.symm := by
    ext x
    simp only [Function.comp_apply, ← cartanMap_finiteProjectiveModulesK0Equiv,
      AddEquiv.apply_symm_apply]
  have hS : ⇑(cartanMap S) =
      ⇑e.finiteModulesK0Equiv.symm ∘ ⇑(cartanMap R) ∘ ⇑e.finiteProjectiveModulesK0Equiv := by
    ext x
    simp only [Function.comp_apply, cartanMap_finiteProjectiveModulesK0Equiv,
      AddEquiv.symm_apply_apply]
  constructor
  · intro h
    rw [hS]
    exact e.finiteModulesK0Equiv.symm.bijective.comp
      (h.comp e.finiteProjectiveModulesK0Equiv.bijective)
  · intro h
    rw [hR]
    exact e.finiteModulesK0Equiv.bijective.comp
      (h.comp e.finiteProjectiveModulesK0Equiv.symm.bijective)

end RingEquiv
