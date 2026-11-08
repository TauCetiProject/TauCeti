/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Twisted.Direct.Basic

/-!
# Pullback of singular cochains with local coefficients

A continuous map `f : X ⟶ Y` pulls a cochain valued in a local system `L` on `Y` back to a
cochain valued in `f^* L` on `X`. Its value on a simplex `σ` is the original value on `f ∘ σ`.
Inverse vertex transport commutes with this operation, so it defines a map of cosimplicial
modules, cochain complexes, and cohomology groups. These maps respect identities, composition,
and coefficient maps, using the canonical identifications of pullback systems.

These are cochains valued in `L` itself, not in its dual. In particular, pullback to a covering
space can be followed by a trivialization of the pulled-back system to compare local cochains
on the base with cochains on the cover.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.H.
* K. S. Brown, *Cohomology of Groups*, Springer, 1982, Sections II.4 and III.1.
-/

public section

noncomputable section

open CategoryTheory SimplexCategory
open scoped Simplicial

universe u v w

namespace TauCeti.LocalCoefficientSystem

variable {R : Type u} [Ring R] {X Y Z : TopCat.{v}}
  (f : X ⟶ Y) (L : LocalCoefficientSystem.{u, v, w} R Y)

/-- Pullback commutes with a change of local coefficients. -/
@[reassoc]
lemma cochainsPullback_coefficient_naturality {K : LocalCoefficientSystem.{u, v, w} R Y}
    (η : L ⟶ K) :
    cochainsCoefficientMap η ≫ cochainsPullback f K =
      cochainsPullback f L ≫ cochainsCoefficientMap ((pullback f.hom).map η) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  apply cochains_ext
  intro σ
  simp only [NatTrans.comp_app, ModuleCat.comp_apply]
  rw [cochainsPullback_eval, cochainsCoefficientMap_eval, cochainsCoefficientMap_eval,
    cochainsPullback_eval]
  -- A pullback fibre and its coefficient map are definitionally those at the image vertex.
  rfl

/-- Pullback along the identity is the canonical identification of coefficient systems. -/
@[simp]
lemma cochainsPullback_id (L : LocalCoefficientSystem.{u, v, w} R X) :
    cochainsPullback (𝟙 X) L =
      cochainsCoefficientMap ((pullbackIdIso (R := R) X).inv.app L) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  apply cochains_ext
  intro σ
  rw [cochainsPullback_eval, cochainsCoefficientMap_eval]
  simp only [pullbackIdIso_inv_app_app]
  -- The identity simplex map and the identity on its fibre act definitionally as identities.
  rfl

/-- Pullback along a composite is successive pullback, with its canonical coefficient
identification. -/
@[reassoc]
lemma cochainsPullback_comp (g : Y ⟶ Z) (L : LocalCoefficientSystem.{u, v, w} R Z) :
    cochainsPullback (f ≫ g) L ≫
        cochainsCoefficientMap ((pullbackCompIso f.hom g.hom).hom.app L) =
      cochainsPullback g L ≫ cochainsPullback f ((pullback g.hom).obj L) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro c
  apply cochains_ext
  intro σ
  simp only [NatTrans.comp_app, ModuleCat.comp_apply]
  simp only [Functor.comp_obj]
  rw [cochainsCoefficientMap_eval, pullbackCompIso_hom_app_app]
  rw [cochainsPullback_eval f, cochainsPullback_eval g, cochainsPullback_eval (f ≫ g)]
  -- Composite simplex maps and pullback fibres agree definitionally; the fibre map is identity.
  rfl

/-- Pullback of cochain complexes is natural in the local coefficient system. -/
@[reassoc]
lemma cochainComplexPullback_coefficient_naturality
    {K : LocalCoefficientSystem.{u, v, w} R Y} (η : L ⟶ K) :
    cochainComplexCoefficientMap η ≫ cochainComplexPullback f K =
      cochainComplexPullback f L ≫ cochainComplexCoefficientMap ((pullback f.hom).map η) := by
  simp only [cochainComplexPullback_eq, cochainComplexCoefficientMap_eq, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ← Functor.map_comp_assoc,
    cochainsPullback_coefficient_naturality]

/-- Pullback of cochain complexes along the identity is the canonical coefficient map. -/
@[simp]
lemma cochainComplexPullback_id (L : LocalCoefficientSystem.{u, v, w} R X) :
    cochainComplexPullback (𝟙 X) L =
      cochainComplexCoefficientMap ((pullbackIdIso (R := R) X).inv.app L) := by
  simp only [cochainComplexPullback_eq, cochainComplexCoefficientMap_eq, cochainsPullback_id]

/-- Pullback of cochain complexes respects composition. -/
@[reassoc]
lemma cochainComplexPullback_comp (g : Y ⟶ Z) (L : LocalCoefficientSystem.{u, v, w} R Z) :
    cochainComplexPullback (f ≫ g) L ≫
        cochainComplexCoefficientMap ((pullbackCompIso f.hom g.hom).hom.app L) =
      cochainComplexPullback g L ≫ cochainComplexPullback f ((pullback g.hom).obj L) := by
  simp only [cochainComplexPullback_eq, cochainComplexCoefficientMap_eq, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ← Functor.map_comp_assoc,
    cochainsPullback_comp]

/-- Pullback on singular cohomology with values in a local system. -/
def cohomologyPullback (n : ℕ) : cohomology L n ⟶ cohomology ((pullback f.hom).obj L) n :=
  HomologicalComplex.homologyMap (cochainComplexPullback f L) n

/-- Cohomology pullback is induced by cochain pullback. -/
lemma cohomologyPullback_eq (n : ℕ) :
    cohomologyPullback f L n =
      HomologicalComplex.homologyMap (cochainComplexPullback f L) n := (rfl)

/-- Pullback on cohomology is natural in the local coefficient system. -/
@[reassoc]
lemma cohomologyPullback_coefficient_naturality {K : LocalCoefficientSystem.{u, v, w} R Y}
    (η : L ⟶ K) (n : ℕ) :
    cohomologyCoefficientMap η n ≫ cohomologyPullback f K n =
      cohomologyPullback f L n ≫ cohomologyCoefficientMap ((pullback f.hom).map η) n := by
  simp only [cohomologyPullback, cohomologyCoefficientMap_eq,
    ← HomologicalComplex.homologyMap_comp, cochainComplexPullback_coefficient_naturality]

/-- Identity pullback on cohomology is the canonical coefficient identification. -/
@[simp]
lemma cohomologyPullback_id (L : LocalCoefficientSystem.{u, v, w} R X) (n : ℕ) :
    cohomologyPullback (𝟙 X) L n =
      cohomologyCoefficientMap ((pullbackIdIso (R := R) X).inv.app L) n := by
  simp [cohomologyPullback, cohomologyCoefficientMap_eq]

/-- Pullback on cohomology respects composition. -/
@[reassoc]
lemma cohomologyPullback_comp (g : Y ⟶ Z) (L : LocalCoefficientSystem.{u, v, w} R Z) (n : ℕ) :
    cohomologyPullback (f ≫ g) L n ≫
        cohomologyCoefficientMap ((pullbackCompIso f.hom g.hom).hom.app L) n =
      cohomologyPullback g L n ≫ cohomologyPullback f ((pullback g.hom).obj L) n := by
  simp only [cohomologyPullback, cohomologyCoefficientMap_eq,
    ← HomologicalComplex.homologyMap_comp, cochainComplexPullback_comp]

end TauCeti.LocalCoefficientSystem
