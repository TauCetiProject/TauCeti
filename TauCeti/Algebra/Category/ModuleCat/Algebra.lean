/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Algebra
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
-- Non-public: the finiteness transfer for linear maps is used only inside the proof.
import TauCeti.Algebra.Module.LinearMap.Finite

/-!
# Finitely generated morphism modules over a finite algebra

For an algebra `A` over a commutative ring `R`, Mathlib's scoped `ModuleCat.Algebra.instLinear`
makes `ModuleCat A` an `R`-linear category. When `R` is Noetherian and `A` is finitely generated
as an `R`-module (for instance an Artin algebra, or a finite-dimensional algebra over a field), the
morphisms between two finitely generated `A`-modules form a finitely generated `R`-module (the
instance `ModuleCat.finite_hom_of_finite`, and `FGModuleCat.finite_hom` in `FGModuleCat A`). This is
the Hom-finiteness that dimension and length counts in the module category of such an algebra rest
on.

The morphism space is identified with the `A`-linear maps by `ModuleCat.homLinearEquiv`, and
those embed in maps into a power of the target by `Module.Finite.linearMap_of_isNoetherian`.
-/

public section

open CategoryTheory

open scoped ModuleCat.Algebra

universe u v w

namespace ModuleCat

variable {R : Type u} {A : Type v} [CommRing R] [IsNoetherianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A]

/-- Morphisms between finitely generated modules over a finite algebra over a Noetherian ring form a
finitely generated module over the base ring. -/
instance finite_hom_of_finite (M N : ModuleCat.{w} A) [Module.Finite A M]
    [Module.Finite A N] : Module.Finite R (M ⟶ N) := by
  have : Module.Finite R N := Module.Finite.trans A N
  have : Module.Finite R (M →ₗ[A] N) := Module.Finite.linearMap_of_isNoetherian
  exact Module.Finite.equiv (ModuleCat.homLinearEquiv (S := R)).symm

end ModuleCat

namespace FGModuleCat

variable {R : Type u} {A : Type v} [CommRing R] [IsNoetherianRing R] [Ring A] [Algebra R A]
  [Module.Finite R A]

/-- Morphisms in `FGModuleCat A`, for a finite algebra `A` over a Noetherian ring, form a finitely
generated module over the base ring. -/
instance finite_hom (X Y : FGModuleCat.{w} A) : Module.Finite R (X ⟶ Y) :=
  Module.Finite.equiv (InducedCategory.homLinearEquiv (R := R)).symm

end FGModuleCat
