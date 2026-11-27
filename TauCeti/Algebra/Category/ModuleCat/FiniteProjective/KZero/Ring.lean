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
# Products of classes in projective `K₀` of a commutative ring

For a commutative ring `R`, the tensor product makes the split Grothendieck group of finitely
generated projective `R`-modules a commutative ring (`TauCeti.SplitK0.instCommRing`, with the
symmetric monoidal structure of `TauCeti.finiteProjectiveModulesSymmetricCategory`). This file
records that ring structure in terms of modules: the class of `R` is the unit, the class of `Rⁿ` is
the integer `n`, and the class of a tensor product `M ⊗[R] N` is the product of the classes of `M`
and `N`. Extension of scalars along a ring homomorphism of commutative rings preserves the unit.

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
