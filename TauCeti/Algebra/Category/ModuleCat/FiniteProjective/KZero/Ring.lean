/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.KZero.Rank
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.Monoidal
public import TauCeti.Algebra.Category.ModuleCat.FiniteProjective.StableEquivalent
public import TauCeti.CategoryTheory.GrothendieckGroup.Monoidal.Basic

/-!
# Products and integer rank equivalences in projective `K₀` of a commutative ring

For a commutative ring `R`, the tensor product makes the split Grothendieck group of finitely
generated projective `R`-modules a commutative ring (`TauCeti.SplitK0.instCommRing`, with the
symmetric monoidal structure of `TauCeti.finiteProjectiveModulesSymmetricCategory`). This file
records that ring structure in terms of modules: the class of `R` is the unit, the class of `Rⁿ` is
the integer `n`, and the class of a tensor product `M ⊗[R] N` is the product of the classes of `M`
and `N`. Extension of scalars along a ring homomorphism of commutative rings preserves the unit.

When `R` is nontrivial and every finitely generated projective `R`-module is stably free (in
particular, over any commutative principal ideal domain), this upgrades to a ring isomorphism
`K₀(proj R) ≃+* ℤ` (`TauCeti.FiniteProjectiveModules.rankEquivIntOfForallIsStablyFree`,
`TauCeti.FiniteProjectiveModules.rankEquivIntOfIsPrincipalIdealRing`).

## Main definitions

* `TauCeti.FiniteProjectiveModules.rankEquivIntOfForallIsStablyFree` and
  `TauCeti.FiniteProjectiveModules.rankEquivIntOfIsPrincipalIdealRing`: the ring isomorphism
  `K₀(proj R) ≃+* ℤ` for a nontrivial commutative ring whose finitely generated projective modules
  are stably free, and in particular for a commutative principal ideal domain.

## Main results

* `TauCeti.FiniteProjectiveModules.splitK0_of_self`: `[R] = 1`.
* `TauCeti.FiniteProjectiveModules.splitK0_of_fin`: `[Rⁿ] = n`.
* `TauCeti.FiniteProjectiveModules.splitK0_of_tensorProduct`: `[M ⊗[R] N] = [M] * [N]`.
* `TauCeti.FiniteProjectiveModules.splitK0_of_eq_classOf_add`: `[M] = ([M] - n[R]) + n`.
* `TauCeti.SplitK0.map_extendScalars_one`: extension of scalars sends `1 = [R]` to `1 = [S]`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter II, §2,
  pp. 69–70.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

namespace FiniteProjectiveModules

universe u

variable (R : Type u) [CommRing R]

/-- The class of the regular module is the unit of projective `K₀`: `R` is the tensor unit of
finite projective `R`-modules. -/
@[simp]
theorem splitK0_of_self : SplitK0.of.{u} (of R R) = 1 :=
  SplitK0.one_def.symm

/-- The class of `TauCeti.finiteProjectiveModulesRegular R` is the unit of projective `K₀`. -/
@[simp]
theorem splitK0_of_finiteProjectiveModulesRegular :
    SplitK0.of.{u} (finiteProjectiveModulesRegular R) = 1 :=
  splitK0_of_self R

/-- The class of the free module `Rⁿ` is the integer `n` in projective `K₀`. -/
theorem splitK0_of_fin (n : ℕ) : SplitK0.of.{u} (freeProjective R n) = n := by
  rw [of_freeProjective, splitK0_of_finiteProjectiveModulesRegular, nsmul_one]

/-- If `R` is nontrivial and every finitely generated projective `R`-module is stably free, then
the integer cast gives a ring isomorphism `K₀(proj R) ≃+* ℤ`. -/
noncomputable def rankEquivIntOfForallIsStablyFree [Nontrivial R]
    (h : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.IsStablyFree R P.obj) :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+* ℤ :=
  (RingEquiv.ofBijective
    (Int.castRingHom (SplitK0.{u} (finiteProjectiveModules R).FullSubcategory))
    (by
      have hcoe :
          ⇑(Int.castRingHom (SplitK0.{u} (finiteProjectiveModules R).FullSubcategory)) =
            ⇑(rankEquiv R h).symm := by
        ext z
        simp [splitK0_of_finiteProjectiveModulesRegular R]
      exact hcoe ▸ (rankEquiv R h).symm.bijective)).symm

theorem rankEquivIntOfForallIsStablyFree_symm_apply [Nontrivial R]
    (h : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.IsStablyFree R P.obj)
    (n : ℤ) :
    (rankEquivIntOfForallIsStablyFree R h).symm n = n := by
  simp [rankEquivIntOfForallIsStablyFree]

@[simp]
theorem rankEquivIntOfForallIsStablyFree_of [Nontrivial R]
    (h : ∀ P : (finiteProjectiveModules R).FullSubcategory, Module.IsStablyFree R P.obj)
    (P : (finiteProjectiveModules R).FullSubcategory) [Module.Free R P.obj] :
    rankEquivIntOfForallIsStablyFree R h (SplitK0.of.{u} P) = (Module.finrank R P.obj : ℤ) := by
  apply (rankEquivIntOfForallIsStablyFree R h).symm.injective
  rw [RingEquiv.symm_apply_apply, rankEquivIntOfForallIsStablyFree_symm_apply,
    SplitK0.of_eq_nsmul_of_linearEquiv_fin (R' := finiteProjectiveModulesRegular R)
      (Module.finBasis R P.obj).equivFun (.refl _ _),
    splitK0_of_finiteProjectiveModulesRegular, nsmul_one, Int.cast_natCast]

/-- **PID `K₀` classification.** Over a principal ideal domain `R`, every finitely generated
projective module is free, so stalk rank gives a ring isomorphism `K₀(proj R) ≃+* ℤ`. -/
noncomputable def rankEquivIntOfIsPrincipalIdealRing [IsDomain R] [IsPrincipalIdealRing R] :
    SplitK0.{u} (finiteProjectiveModules R).FullSubcategory ≃+* ℤ :=
  rankEquivIntOfForallIsStablyFree R fun P ↦
    have : Module.Free R P.obj := Module.free_of_finite_type_torsion_free'
    inferInstance

theorem rankEquivIntOfIsPrincipalIdealRing_symm_apply [IsDomain R] [IsPrincipalIdealRing R]
    (n : ℤ) :
    (rankEquivIntOfIsPrincipalIdealRing R).symm n = n :=
  rankEquivIntOfForallIsStablyFree_symm_apply R _ n

@[simp]
theorem rankEquivIntOfIsPrincipalIdealRing_of [IsDomain R] [IsPrincipalIdealRing R]
    (P : (finiteProjectiveModules R).FullSubcategory) :
    rankEquivIntOfIsPrincipalIdealRing R (SplitK0.of.{u} P) = (Module.finrank R P.obj : ℤ) :=
  haveI : Module.Free R P.obj := Module.free_of_finite_type_torsion_free'
  rankEquivIntOfForallIsStablyFree_of R _ P

variable {R}

/-- The class of a tensor product of finite projective modules is the product of their classes. -/
theorem splitK0_of_tensorProduct (M N : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] [AddCommGroup N] [Module R N] [Module.Finite R N]
    [Module.Projective R N] :
    SplitK0.of.{u} (of R (M ⊗[R] N)) = SplitK0.of.{u} (of R M) * SplitK0.of.{u} (of R N) :=
  (SplitK0.of_congr (ObjectProperty.isoMk _ (LinearEquiv.refl R (M ⊗[R] N)).toModuleIso)).trans
    (SplitK0.of_mul_of _ _).symm

/-- The class of a finite projective module `M` is its reduced class `[M] - n[R]`
(`TauCeti.FiniteProjectiveModules.classOf`) plus the integer `n` in the ring projective `K₀`. -/
theorem splitK0_of_eq_classOf_add (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (n : ℕ) :
    SplitK0.of.{u} (of R M) = classOf R M n + n := by
  rw [classOf_def, splitK0_of_self, nsmul_one, sub_add_cancel]

end FiniteProjectiveModules

namespace SplitK0

open FiniteProjectiveModules

/-- Extension of scalars along a ring homomorphism `f : R →+* S` of commutative rings sends the
unit `[R]` of projective `K₀(R)` to the unit `[S]` of projective `K₀(S)`. -/
@[simp]
theorem map_extendScalars_one {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    SplitK0.map.{u, u} f.finiteProjectiveModulesExtendScalars 1 = 1 := by
  rw [← splitK0_of_finiteProjectiveModulesRegular, SplitK0.map_of,
    of_extendScalars_obj_finiteProjectiveModulesRegular, splitK0_of_finiteProjectiveModulesRegular]

end SplitK0

end TauCeti
