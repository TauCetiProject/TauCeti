/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Equivalence
public import TauCeti.AlgebraicGeometry.Sites.Etale.ModuleSheaf
public import TauCeti.AlgebraicGeometry.Sites.EtaleSepClosed

/-!
# Finite lisse étale sheaves on a separably closed field

Let `Ω` be a separably closed field and `Λ` a ring. Étale sheaves of `Λ`-modules on `Spec Ω` are
the same as `Λ`-modules, through the constant sheaf functor and the global sections functor
(`AlgebraicGeometry.Scheme.isEquivalence_constantSheaf`). This file shows that this equivalence
restricts to the finite coefficients: a sheaf is finite lisse exactly when its global sections
are a finitely generated `Λ`-module, so the finite lisse étale sheaves of `Λ`-modules on `Spec Ω`
form a category equivalent to the finitely generated `Λ`-modules.

A finite lisse sheaf has finitely generated stalks, and the stalk at the geometric point
`𝟙 (Spec Ω)` is the global sections; conversely every sheaf on `Spec Ω` is the constant sheaf on
its global sections, which is finite lisse when they are finitely generated. Consequently, if a
scheme `S` has a surjective étale geometric point `s : Spec Ω ⟶ S`, as `Spec ℝ` has, a sheaf on
`S` whose stalk at `s` is finitely generated is finite lisse
(`CategoryTheory.Sheaf.IsFiniteLisse.of_etale_of_surjective_of_isSepClosed`).

## Main results

* `CategoryTheory.Sheaf.isFiniteLisse_iff_finite_Γ`: on `Spec Ω`, a sheaf of `Λ`-modules is finite
  lisse exactly when its global sections are a finitely generated `Λ`-module.
* `CategoryTheory.Sheaf.finiteLisseSepClosedEquivalence`: the finite lisse étale sheaves of
  `Λ`-modules on `Spec Ω` are equivalent to `FGModuleCat Λ`, through the constant sheaf functor.
* `CategoryTheory.Sheaf.IsFiniteLisse.of_etale_of_surjective_of_isSepClosed`: over a base with a
  surjective étale geometric point, finite generation of the stalk there suffices.

## References

* M. Artin, A. Grothendieck, J.-L. Verdier, *SGA 4*, Exposé VIII, §2, for sheaves on the étale
  site of a field as discrete Galois modules; here the Galois group is trivial.
-/

public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme TauCeti.AlgebraicGeometry.Scheme

namespace CategoryTheory.Sheaf

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] {Λ : Type u} [Ring Λ]

/-- On a separably closed field, an étale sheaf of `Λ`-modules is finite lisse exactly when its
global sections are a finitely generated `Λ`-module. -/
theorem isFiniteLisse_iff_finite_Γ
    (F : Sheaf (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ)) :
    F.IsFiniteLisse ↔ Module.Finite Λ ((Sheaf.Γ _ (ModuleCat.{u} Λ)).obj F) := by
  let adj := constantSheafΓAdj (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ)
  -- `F` is the constant sheaf on its global sections.
  have e : (constantSheaf _ (ModuleCat.{u} Λ)).obj ((Sheaf.Γ _ (ModuleCat.{u} Λ)).obj F) ≅ F :=
    asIso (adj.counit.app F)
  rw [← isFiniteLisse_constantSheaf_iff (𝟙 (Spec (.of Ω)))]
  exact isLocallyConstantIn_iff_of_iso e.symm

variable (Λ) in
/-- On a separably closed field, the finite lisse étale sheaves of `Λ`-modules form a category
equivalent to the finitely generated `Λ`-modules, through the constant sheaf functor and the
global sections functor. -/
noncomputable def finiteLisseSepClosedEquivalence :
    FGModuleCat.{u} Λ ≌ ObjectProperty.FullSubcategory
      fun F : Sheaf (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ) ↦ F.IsFiniteLisse :=
  (constantSheafΓAdj (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ)).toEquivalence
    |>.congrFullSubcategory <| funext fun M ↦ propext <|
      (ObjectProperty.prop_inverseImage_iff _ _ M).trans <|
        (isFiniteLisse_constantSheaf_iff (𝟙 _) M).trans (ModuleCat.isFG_iff M).symm

/-- The equivalence `finiteLisseSepClosedEquivalence` sends a finitely generated module to its
constant sheaf. -/
@[simp]
theorem finiteLisseSepClosedEquivalence_functor_obj_obj (M : FGModuleCat.{u} Λ) :
    ((finiteLisseSepClosedEquivalence Ω Λ).functor.obj M).obj =
      (constantSheaf (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ)).obj M.obj := by
  rfl

/-- The inverse of `finiteLisseSepClosedEquivalence` sends a finite lisse sheaf to its global
sections. -/
@[simp]
theorem finiteLisseSepClosedEquivalence_inverse_obj_obj
    (F : ObjectProperty.FullSubcategory
      fun F : Sheaf (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ) ↦ F.IsFiniteLisse) :
    ((finiteLisseSepClosedEquivalence Ω Λ).inverse.obj F).obj =
      (Sheaf.Γ (smallEtaleTopology (Spec (.of Ω))) (ModuleCat.{u} Λ)).obj F.obj := by
  rfl

/-- **Finite lisse sheaves over a base covered by one geometric point.** Let `s : Spec Ω ⟶ S` be
a surjective étale geometric point, with `Ω` separably closed. An étale sheaf of `Λ`-modules on
`S` whose stalk at `s` is finitely generated is finite lisse. -/
theorem IsFiniteLisse.of_etale_of_surjective_of_isSepClosed {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] {S : Scheme.{u}} (F : Sheaf (smallEtaleTopology S) (ModuleCat.{u} Λ))
    (s : Spec (.of Ω) ⟶ S) [Etale s] [Surjective s] [Module.Finite Λ ((etaleStalk Λ s).obj F)] :
    F.IsFiniteLisse := by
  -- The global sections of the pullback of `F` to `Spec Ω` are its stalk at `s`.
  rw [isFiniteLisse_iff_of_etale_of_surjective F s, isFiniteLisse_iff_finite_Γ]
  exact Module.Finite.equiv (((pointSmallEtaleIdSheafFiberIso Ω).app _).symm ≪≫
    (s.smallEtalePullbackCompEtaleStalkIso Λ (𝟙 _)).app F ≪≫
    eqToIso (by rw [Category.id_comp])).toLinearEquiv.symm

end CategoryTheory.Sheaf
