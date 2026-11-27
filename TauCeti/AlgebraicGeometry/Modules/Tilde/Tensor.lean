/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Monoidal.Tensor.Map
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# Tilde and the tensor product of unbounded cochain complexes

For a commutative ring `R`, applying `M ↦ M~` degreewise commutes with the tensor
product of arbitrary integer-indexed cochain complexes. This is the cochain-level
comparison underlying the affine derived tensor comparison, with no boundedness or
flatness assumption on either complex.

The comparison is the specialization of `Functor.mapCochainTensorNatIso` to the
exact, colimit-preserving functor `AlgebraicGeometry.tilde.functor R`, using
`TauCeti.AlgebraicGeometry.tildeMonoidal`. Its summand maps are the tensor comparison
of tilde, with the signs of the existing tensor differential unchanged.
-/

public section

open CategoryTheory MonoidalCategory
open AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {R : CommRingCat.{u}}

/-- Degreewise tilde commutes naturally with tensor products of unbounded cochain
complexes of `R`-modules. -/
noncomputable def tildeCochainTensorIso :
    ((tilde.functor R).mapHomologicalComplex (.up ℤ)).prod
        ((tilde.functor R).mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj (curriedTensor (Spec R).Modules).map₂CochainComplex ≅
      Functor.uncurry.obj (curriedTensor (ModuleCat.{u} R)).map₂CochainComplex ⋙
        (tilde.functor R).mapHomologicalComplex (.up ℤ) :=
  (tilde.functor R).mapCochainTensorNatIso

/-- The forward tilde comparison at a pair is the generic cochain tensor comparison. -/
@[simp]
lemma tildeCochainTensorIso_hom_app {K L : CochainComplex (ModuleCat.{u} R) ℤ} :
    tildeCochainTensorIso.hom.app (K, L) =
      ((tilde.functor R).mapCochainTensorIso K L).hom := by
  simp only [tildeCochainTensorIso, Functor.mapCochainTensorNatIso_hom_app]

/-- The inverse tilde comparison at a pair is the inverse generic cochain comparison. -/
@[simp]
lemma tildeCochainTensorIso_inv_app {K L : CochainComplex (ModuleCat.{u} R) ℤ} :
    tildeCochainTensorIso.inv.app (K, L) =
      ((tilde.functor R).mapCochainTensorIso K L).inv := by
  simp only [tildeCochainTensorIso, Functor.mapCochainTensorNatIso_inv_app]

end TauCeti.AlgebraicGeometry
