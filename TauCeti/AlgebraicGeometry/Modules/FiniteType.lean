/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Restriction.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-!
# Quotients and images of modules of finite type

A quotient of an `𝒪_X`-module of finite type is of finite type, and so the image of a morphism
out of a module of finite type is of finite type. Local generators of the source are carried to
local generators of the quotient by Mathlib's `SheafOfModules.GeneratingSections.ofEpi`, after
restriction to the slice site over each open, which preserves epimorphisms.

These closure properties produce the finite-type submodules of a quasi-coherent module: the image
of `𝒪_X^n ⟶ N` for finitely many global sections of `N`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isFiniteType_of_epi`: a quotient of a module of finite type
  is of finite type.
* `AlgebraicGeometry.Scheme.Modules.isFiniteType_image`: the image of a morphism out of a module
  of finite type is of finite type.

## References

* The Stacks Project, *Sheaves of Modules*, Section 17.9, Modules of finite type.
-/

public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A quotient of a module of finite type is of finite type: local generators of `M` map to
local generators of `N`. -/
theorem isFiniteType_of_epi {M N : X.Modules} (p : M ⟶ N) [Epi p] [M.IsFiniteType] :
    N.IsFiniteType := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData.{u} M
  let q' : SheafOfModules.LocalGeneratorsData.{u} N :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators := fun i ↦
        have := epi_overFunctor_map p (q.X i)
        (q.generators i).ofEpi ((SheafOfModules.overFunctor.{u} _ (q.X i)).map p) }
  have hq' : q'.IsFiniteType := by
    constructor
    intro i
    have := hq.isFiniteType i
    exact ⟨SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := q.generators i)⟩
  exact SheafOfModules.IsFiniteType.mk (R := X.ringCatSheaf) ⟨q', hq'⟩

/-- The image of a morphism out of a module of finite type is of finite type. -/
instance isFiniteType_image {M N : X.Modules} (f : M ⟶ N) [M.IsFiniteType] :
    (image f).IsFiniteType :=
  isFiniteType_of_epi (factorThruImage f)

end AlgebraicGeometry.Scheme.Modules
