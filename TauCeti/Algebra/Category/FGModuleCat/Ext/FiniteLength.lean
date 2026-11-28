/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.RingTheory.FiniteLength
public import TauCeti.Algebra.Category.FGModuleCat.Basic
public import TauCeti.CategoryTheory.Exact.Abelian
public import TauCeti.CategoryTheory.Exact.YonedaExt.BaerSum
import TauCeti.Algebra.Category.FGModuleCat.Projective
import TauCeti.Algebra.Module.LinearMap.FiniteLength
import TauCeti.CategoryTheory.Exact.YonedaExt.Projective

/-!
# Finite length of `Ext¹` of finitely generated modules

In the abelian exact structure on `FGModuleCat A` for a left Noetherian `R`-algebra `A`,
a projective presentation computes Yoneda `Ext¹(Z, W)` as a quotient of `Hom(K, W)`,
where `K` is finitely generated. Thus finite length of `W` over `R` suffices for finite
length of `Ext¹(Z, W)` over `R`.
-/

public section

namespace FGModuleCat

open CategoryTheory TauCeti
open scoped ModuleCat.Algebra

universe u v w

variable {R : Type u} {A : Type v} [CommRing R] [Ring A] [Algebra R A]

/-- Over an algebra `A` that is left Noetherian, Yoneda `Ext¹(Z, W)` in `FGModuleCat A` has
finite length over the base ring if `W` does. -/
theorem isFiniteLength_ext1_of_isFiniteLength [IsNoetherianRing A] [Small.{w} A]
    (Z W : FGModuleCat.{w} A) (hW : IsFiniteLength R W.obj) :
    IsFiniteLength R ((ExactStructure.abelian (FGModuleCat.{w} A)).Ext1 Z W) :=
  ExactStructure.abelian_enoughProjectives.isFiniteLength_ext1 R Z W fun K ↦
    (InducedCategory.homLinearEquiv (R := R) ≪≫ₗ ModuleCat.homLinearEquiv).symm.isFiniteLength
      (isFiniteLength_linearMap K.obj W.obj hW)

end FGModuleCat
