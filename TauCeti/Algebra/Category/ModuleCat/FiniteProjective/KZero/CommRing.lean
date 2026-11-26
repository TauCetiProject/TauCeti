/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.CartanMap.Morita
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Defs

/-!
# Projective `K₀` of a commutative ring through left modules

The projective `K₀` of a ring `R`, `TauCeti.KZero R`, is built from finitely generated projective
right `R`-modules, encoded as left `Rᵐᵒᵖ`-modules. When `R` is commutative, a left `R`-module is a
right `R`-module with the same action, and `KZero R` is the split `K₀` of finitely generated
projective left `R`-modules. Classes of modules over commutative rings, such as the modules of
sections over rings of continuous functions, are therefore computed with the left-module API of
`TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent` and transported to `KZero R`
along this identification.

The identification is induced by Mathlib's `ModuleCat.restrictScalarsEquivalenceOfRingEquiv` for
the ring isomorphism `Rᵐᵒᵖ ≃+* R`, restricted to finitely generated projective modules.

## Main definitions

* `TauCeti.KZero.finiteProjectiveRightEquivalence`: for a commutative ring `R`, the equivalence
  from finitely generated projective left `R`-modules to finitely generated projective right
  `R`-modules which keeps the underlying abelian group.
* `TauCeti.KZero.splitK0Equiv`: for a commutative ring `R`, the induced isomorphism of `KZero R`
  with the split `K₀` of finitely generated projective left `R`-modules.

## Main results

* `TauCeti.KZero.splitK0Equiv_of`: the class of a right module `X` goes to the class of `X`
  regarded as a left module.
* `TauCeti.KZero.splitK0Equiv_symm_of`: the class of a left module `P` goes to the class of `P`
  regarded as a right module.
* `TauCeti.KZero.splitK0Equiv_symm_of_finiteProjectiveModulesRegular`: the class of the free left
  module of rank one goes to the class of the free right module of rank one;
  `TauCeti.KZero.splitK0Equiv_of_finiteProjectiveModulesRegular` is the converse.
* `TauCeti.KZero.splitK0Equiv_symm_classOf`: the class `[M] - n[R]` of a finitely generated
  projective left module goes to the corresponding class in `KZero R`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u

namespace KZero

variable (R : Type u) [CommRing R]

/-- For a commutative ring `R`, the equivalence between finitely generated projective left
`R`-modules and finitely generated projective right `R`-modules which keeps the underlying
abelian group and lets `op r` act as `r`: restriction of scalars along `Rᵐᵒᵖ ≃+* R`. -/
noncomputable def finiteProjectiveRightEquivalence :
    (finiteProjectiveModules R).FullSubcategory ≌ FiniteProjectiveRight R :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv (RingEquiv.toOpposite R).symm :
    ModuleCat.{u} R ≌ ModuleCat.{u} Rᵐᵒᵖ).finiteProjectiveModulesEquivalence

/-- The right module attached to a left module by `TauCeti.KZero.finiteProjectiveRightEquivalence`
is its restriction of scalars along `Rᵐᵒᵖ ≃+* R`. -/
@[simp]
theorem finiteProjectiveRightEquivalence_functor_obj_obj
    (P : (finiteProjectiveModules R).FullSubcategory) :
    ((finiteProjectiveRightEquivalence R).functor.obj P).obj =
      (ModuleCat.restrictScalars (RingEquiv.toOpposite R).symm.toRingHom).obj P.obj :=
  Equivalence.finiteProjectiveModulesEquivalence_functor_obj_obj _ P

/-- The left module attached to a right module by
`TauCeti.KZero.finiteProjectiveRightEquivalence` is its restriction of scalars along
`R ≃+* Rᵐᵒᵖ`. -/
@[simp]
theorem finiteProjectiveRightEquivalence_inverse_obj_obj (X : FiniteProjectiveRight R) :
    ((finiteProjectiveRightEquivalence R).inverse.obj X).obj =
      (ModuleCat.restrictScalars (RingEquiv.toOpposite R).toRingHom).obj X.obj :=
  Equivalence.finiteProjectiveModulesEquivalence_inverse_obj_obj _ X

/-- For a commutative ring `R`, `KZero R`, the split `K₀` of finitely generated projective right
`R`-modules, is the split `K₀` of finitely generated projective left `R`-modules: a left
`R`-module is a right `R`-module with the same action. -/
noncomputable def splitK0Equiv :
    KZero R ≃+ SplitK0.{u} (finiteProjectiveModules R).FullSubcategory :=
  (SplitK0.mapEquiv.{u, u} (finiteProjectiveRightEquivalence R)).symm

variable {R}

/-- `TauCeti.KZero.splitK0Equiv` sends the class of a right module `X` to the class of `X`
regarded as a left module. -/
@[simp]
theorem splitK0Equiv_of (X : FiniteProjectiveRight R) :
    splitK0Equiv R (SplitK0.of.{u} X) =
      SplitK0.of.{u} ((finiteProjectiveRightEquivalence R).inverse.obj X) :=
  SplitK0.mapEquiv_symm_of.{u, u} _ X

/-- The inverse of `TauCeti.KZero.splitK0Equiv` sends the class of a left module `P` to the class
of `P` regarded as a right module. -/
@[simp]
theorem splitK0Equiv_symm_of (P : (finiteProjectiveModules R).FullSubcategory) :
    (splitK0Equiv R).symm (SplitK0.of.{u} P) =
      SplitK0.of.{u} ((finiteProjectiveRightEquivalence R).functor.obj P) := by
  rw [splitK0Equiv, AddEquiv.symm_symm, SplitK0.mapEquiv_of]

/-- The class of the free left module of rank one corresponds to the class of the free right
module of rank one. -/
theorem splitK0Equiv_symm_of_finiteProjectiveModulesRegular :
    (splitK0Equiv R).symm (SplitK0.of.{u} (finiteProjectiveModulesRegular R)) =
      SplitK0.of.{u} (finiteProjectiveModulesRegular Rᵐᵒᵖ) := by
  rw [splitK0Equiv_symm_of]
  exact SplitK0.of_congr (ObjectProperty.isoMk _
    (eqToIso (finiteProjectiveRightEquivalence_functor_obj_obj R _) ≪≫
      ModuleCat.restrictScalarsIsoOfEquiv (RingEquiv.toOpposite R).symm))

/-- The class of the free right module of rank one corresponds to the class of the free left
module of rank one. -/
theorem splitK0Equiv_of_finiteProjectiveModulesRegular :
    splitK0Equiv R (SplitK0.of.{u} (finiteProjectiveModulesRegular Rᵐᵒᵖ)) =
      SplitK0.of.{u} (finiteProjectiveModulesRegular R) := by
  rw [← splitK0Equiv_symm_of_finiteProjectiveModulesRegular, AddEquiv.apply_symm_apply]

/-- The inverse of `TauCeti.KZero.splitK0Equiv` sends the class `[M] - n[R]` of a finitely
generated projective left `R`-module `M` to the class of `M` in `KZero R` minus `n` times the
class of the free right module of rank one. -/
theorem splitK0Equiv_symm_classOf (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (n : ℕ) :
    (splitK0Equiv R).symm (FiniteProjectiveModules.classOf R M n) =
      SplitK0.of.{u} ((finiteProjectiveRightEquivalence R).functor.obj
          (FiniteProjectiveModules.of R M)) -
        n • SplitK0.of.{u} (finiteProjectiveModulesRegular Rᵐᵒᵖ) := by
  rw [FiniteProjectiveModules.classOf_def, map_sub, map_nsmul, ← splitK0Equiv_symm_of,
    ← splitK0Equiv_symm_of_finiteProjectiveModulesRegular]
  -- `FiniteProjectiveModules.of R R` and `finiteProjectiveModulesRegular R` are both
  -- `ModuleCat.of R R`, as objects of the full subcategory.
  rfl

end KZero

end TauCeti
