/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import TauCeti.AlgebraicGeometry.FiniteEtale.GroupScheme
public import TauCeti.CategoryTheory.Action.Cartesian
public import TauCeti.RingTheory.Etale.Galois

/-!
# Finite étale group schemes over a field and Galois groups

Let `K` be a field and `Ω` a separable closure of `K`. Grothendieck's Galois theory for `K`
(`TauCeti.galoisFiber`, `TauCeti.isEquivalence_galoisFiber`) identifies finite étale `K`-algebras
with finite sets carrying a continuous action of `Gal(Ω/K)`. Composed with the anti-equivalence
between finite étale algebras and finite étale schemes, it gives the scheme form of the
correspondence (`TauCeti.FiniteEtaleScheme.galoisEquivalence`):

`FiniteEtaleScheme (Spec K) ≌ ContAction FintypeCat Gal(Ω/K)`,

sending a finite étale `K`-scheme `Spec A` to the finite `Gal(Ω/K)`-set of `Ω`-valued points of
`A` (`TauCeti.FiniteEtaleScheme.specCompGaloisEquivalenceFunctorIso`).

Both categories are cartesian monoidal: finite étale schemes over `K` are closed under fibre
products over `K`, and continuous actions on finite sets are closed under products with the
diagonal action. Like every equivalence of categories, `galoisEquivalence K Ω` preserves finite
products, so it is a monoidal functor for these structures, braided as well, and it carries
group objects to group objects. The correspondence therefore restricts to an equivalence between
group objects in finite étale `K`-schemes and group objects in finite continuous
`Gal(Ω/K)`-sets, that is, finite groups on which `Gal(Ω/K)` acts continuously by group
automorphisms (`TauCeti.FiniteEtaleScheme.galoisEquivalenceGrp`), and between their commutative
versions (`TauCeti.FiniteEtaleScheme.galoisEquivalenceCommGrp`). Being equivalences of
categories, these also identify the homomorphisms of group objects on the two sides.

Group objects in `FiniteEtaleScheme S` are the finite étale group schemes over `S`
(`TauCeti.FiniteEtaleScheme.essImage_mapGrp_ι_iff`, in
`TauCeti.AlgebraicGeometry.FiniteEtale.GroupScheme`).

## Main definitions

* `TauCeti.FiniteEtaleScheme.galoisEquivalence K Ω`: finite étale `K`-schemes are equivalent to
  finite continuous `Gal(Ω/K)`-sets.
* `TauCeti.FiniteEtaleScheme.galoisEquivalenceGrp K Ω`: group objects in finite étale `K`-schemes
  are equivalent to group objects in finite continuous `Gal(Ω/K)`-sets.
* `TauCeti.FiniteEtaleScheme.galoisEquivalenceCommGrp K Ω`: the same for commutative group
  objects.

## Main results

* `TauCeti.FiniteEtaleScheme.specCompGaloisEquivalenceFunctorIso`: on spectra, the equivalence is
  the functor of `Ω`-valued points with its Galois action.
* `TauCeti.FiniteEtaleScheme.galoisEquivalenceGrp_functor_comp_forget` and
  `TauCeti.FiniteEtaleScheme.galoisEquivalenceCommGrp_functor_comp_forget`: on underlying objects,
  the equivalences of group objects are `galoisEquivalence K Ω`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental (SGA 1)*, Exposé V, §8.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, Graduate Texts in Mathematics 66,
  Springer, 1979, §6.4.
-/

public section

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry FintypeCatDiscrete

universe u

namespace TauCeti

namespace FiniteEtaleScheme

variable (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] [IsGalois K Ω]

/-- **Galois theory for finite étale schemes over a field.** For a separable closure `Ω` of `K`,
finite étale `K`-schemes are equivalent to finite sets with a continuous action of `Gal(Ω/K)`.
A finite étale scheme `Spec A` goes to the set of `Ω`-valued points of `A`
(`specCompGaloisEquivalenceFunctorIso`). -/
noncomputable def galoisEquivalence :
    FiniteEtaleScheme (Spec (.of K)) ≌ ContAction FintypeCat.{u} Gal(Ω/K) :=
  (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).symm.trans
    (galoisFiber K Ω).asEquivalence

/-- The functor of `galoisEquivalence K Ω` takes coordinate algebras and then `Ω`-valued points. -/
@[simp]
theorem galoisEquivalence_functor :
    (galoisEquivalence K Ω).functor =
      (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).inverse ⋙ galoisFiber K Ω :=
  (rfl)

/-- The inverse of `galoisEquivalence K Ω` inverts the Galois fibre functor and then takes the
spectrum. -/
@[simp]
theorem galoisEquivalence_inverse :
    (galoisEquivalence K Ω).inverse = (galoisFiber K Ω).asEquivalence.inverse ⋙ spec (.of K) := by
  simp only [galoisEquivalence, Equivalence.trans_inverse, Equivalence.symm_inverse,
    finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor]

/-- **The Galois set of a spectrum.** For a finite étale `K`-algebra `A`, `galoisEquivalence K Ω`
sends `Spec A` to the finite set `A →ₐ[K] Ω` of `Ω`-valued points of `A`, with `Gal(Ω/K)` acting by
postcomposition. -/
noncomputable def specCompGaloisEquivalenceFunctorIso :
    spec (.of K) ⋙ (galoisEquivalence K Ω).functor ≅ galoisFiber K Ω :=
  Functor.isoWhiskerLeft _ (eqToIso (galoisEquivalence_functor K Ω)) ≪≫
    Functor.isoWhiskerRight
      (eqToIso (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme_functor (.of K)).symm) _ ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).unitIso.symm
      (galoisFiber K Ω) ≪≫ Functor.leftUnitor _

/-- The component of `specCompGaloisEquivalenceFunctorIso` at `A` is the Galois fibre functor
applied to the inverse unit of the finite étale anti-equivalence at `A`, after identifying
`spec` with the forward functor of that anti-equivalence. -/
@[simp]
theorem specCompGaloisEquivalenceFunctorIso_hom_app (A : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ) :
    (specCompGaloisEquivalenceFunctorIso K Ω).hom.app A =
      eqToHom (by simp) ≫ (galoisFiber K Ω).map
        ((finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).unitIso.inv.app A) := by
  simp only [specCompGaloisEquivalenceFunctorIso, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    eqToIso.hom, Functor.isoWhiskerRight_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, eqToHom_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Category.id_comp]
  rw [eqToHom_map, eqToHom_map, eqToHom_trans_assoc]
  exact congrArg _ (Category.comp_id _)

/-- The inverse component of `specCompGaloisEquivalenceFunctorIso` at `A` is the Galois fibre
functor applied to the unit of the finite étale anti-equivalence at `A`, after identifying the
forward functor of that anti-equivalence with `spec`. -/
@[simp]
theorem specCompGaloisEquivalenceFunctorIso_inv_app (A : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ) :
    (specCompGaloisEquivalenceFunctorIso K Ω).inv.app A =
      (galoisFiber K Ω).map
        ((finiteEtaleCommAlgCatOpEquivFiniteEtaleScheme (.of K)).unitIso.hom.app A) ≫
        eqToHom (by simp) := by
  simp only [specCompGaloisEquivalenceFunctorIso, Iso.trans_inv, Functor.isoWhiskerRight_inv,
    Iso.symm_inv, Category.assoc, eqToIso.inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.associator_hom_app, eqToHom_app,
    Functor.comp_map, Functor.whiskerLeft_app, Category.id_comp]
  rw [eqToHom_map, eqToHom_map, eqToHom_trans]

/-- The functor of `galoisEquivalence K Ω` is monoidal for the cartesian monoidal structures, as
it preserves finite products. -/
noncomputable instance : (galoisEquivalence K Ω).functor.Monoidal :=
  .ofChosenFiniteProducts _

/-- The inverse of `galoisEquivalence K Ω` is monoidal for the cartesian monoidal structures, as it
preserves finite products. -/
noncomputable instance : (galoisEquivalence K Ω).inverse.Monoidal :=
  .ofChosenFiniteProducts _

/-- The functor of `galoisEquivalence K Ω` is braided. -/
noncomputable instance : (galoisEquivalence K Ω).functor.Braided :=
  .ofChosenFiniteProducts _

/-- The inverse of `galoisEquivalence K Ω` is braided. -/
noncomputable instance : (galoisEquivalence K Ω).inverse.Braided :=
  .ofChosenFiniteProducts _

/-- **Finite étale group schemes over a field are finite Galois groups.** Group objects in finite
étale `K`-schemes are equivalent to group objects in finite continuous `Gal(Ω/K)`-sets, that is,
to finite groups on which `Gal(Ω/K)` acts continuously by group automorphisms. Morphisms on both
sides are homomorphisms of group objects. -/
noncomputable def galoisEquivalenceGrp :
    Grp (FiniteEtaleScheme (Spec (.of K))) ≌ Grp (ContAction FintypeCat.{u} Gal(Ω/K)) :=
  (galoisEquivalence K Ω).mapGrp

/-- On underlying objects, `galoisEquivalenceGrp K Ω` is `galoisEquivalence K Ω`. -/
theorem galoisEquivalenceGrp_functor_comp_forget :
    (galoisEquivalenceGrp K Ω).functor ⋙ Grp.forget _ =
      Grp.forget _ ⋙ (galoisEquivalence K Ω).functor :=
  (rfl)

/-- On underlying objects, the inverse of `galoisEquivalenceGrp K Ω` is the inverse of
`galoisEquivalence K Ω`. -/
theorem galoisEquivalenceGrp_inverse_comp_forget :
    (galoisEquivalenceGrp K Ω).inverse ⋙ Grp.forget _ =
      Grp.forget _ ⋙ (galoisEquivalence K Ω).inverse :=
  (rfl)

/-- **Finite étale commutative group schemes over a field are finite Galois modules.**
Commutative group objects in finite étale `K`-schemes are equivalent to commutative group objects
in finite continuous `Gal(Ω/K)`-sets, that is, to finite abelian groups with a continuous action
of `Gal(Ω/K)` by group automorphisms. -/
noncomputable def galoisEquivalenceCommGrp :
    CommGrp (FiniteEtaleScheme (Spec (.of K))) ≌ CommGrp (ContAction FintypeCat.{u} Gal(Ω/K)) :=
  (galoisEquivalence K Ω).mapCommGrp

/-- On underlying objects, `galoisEquivalenceCommGrp K Ω` is `galoisEquivalence K Ω`. -/
theorem galoisEquivalenceCommGrp_functor_comp_forget :
    (galoisEquivalenceCommGrp K Ω).functor ⋙ CommGrp.forget _ =
      CommGrp.forget _ ⋙ (galoisEquivalence K Ω).functor :=
  (rfl)

/-- On underlying objects, the inverse of `galoisEquivalenceCommGrp K Ω` is the inverse of
`galoisEquivalence K Ω`. -/
theorem galoisEquivalenceCommGrp_inverse_comp_forget :
    (galoisEquivalenceCommGrp K Ω).inverse ⋙ CommGrp.forget _ =
      CommGrp.forget _ ⋙ (galoisEquivalence K Ω).inverse :=
  (rfl)

end FiniteEtaleScheme

end TauCeti
