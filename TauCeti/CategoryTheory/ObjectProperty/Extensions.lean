/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels

/-!
# Weak Serre subcategories, five-term exact sequences and closed classes

Let `P` be a property of objects of an abelian category which is closed under kernels, cokernels
and extensions; such a `P` is called a weak Serre subcategory. If `A ⟶ B ⟶ M ⟶ D ⟶ E` is exact at
`B`, `M` and `D` and the four outer objects satisfy `P`, then so does `M`
(`CategoryTheory.ObjectProperty.prop_X₂_of_exact_of_exact_of_exact`): the object `M` is an extension
of the kernel of `D ⟶ E` by the cokernel of `A ⟶ B`.

Applied to the long exact homology sequence of a distinguished triangle, this shows that the
objects of a derived category whose homology objects all satisfy `P` form a triangulated
subcategory.

A *closed class* (`CategoryTheory.ObjectProperty.IsClosedClass`) is a property that holds for
zero objects and, in a short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `X₁` in it, holds for
`X₂` exactly when it holds for `X₃`. A closed class is closed under extensions
(`CategoryTheory.ObjectProperty.IsClosedClass.isClosedUnderExtensions`).

A property of objects of an abelian category which contains zero and is closed under isomorphisms
and extensions, for instance a Serre class, is closed under finite coproducts
(`CategoryTheory.ObjectProperty.isClosedUnderFiniteCoproducts_of_isClosedUnderExtensions`), since a
binary coproduct is a biproduct, an extension of its two summands
(`CategoryTheory.ObjectProperty.isClosedUnderBinaryCoproducts_of_isClosedUnderExtensions`).

## References

* The Stacks project, chapter Homological Algebra, section Serre subcategories: the
  characterization of weak Serre subcategories by five-term exact sequences.
* [ShortProof]: `grh-lean`, https://github.com/lsernau/grh-lean, file
  `src/Lib/Cohomology/Etale/BijectiveComparisons.lean` (declaration `New.Variety.IsClosedClass`);
  Apache 2.0, Copyright 2026 Anthropic, PBC. `CategoryTheory.ObjectProperty.IsClosedClass` is
  adapted from it and stated for an arbitrary abelian category.
-/

public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C)
  [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]

/-- A property closed under kernels, cokernels and extensions contains the middle object of a
five-term exact sequence `A ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ E` whose four outer objects it contains. -/
theorem prop_X₂_of_exact_of_exact_of_exact {S : ShortComplex C} (hS : S.Exact) {A E : C}
    {a : A ⟶ S.X₁} {e : S.X₃ ⟶ E} (wa : a ≫ S.f = 0) (we : S.g ≫ e = 0)
    (ha : (ShortComplex.mk a S.f wa).Exact) (he : (ShortComplex.mk S.g e we).Exact)
    (hA : P A) (h₁ : P S.X₁) (h₃ : P S.X₃) (hE : P E) : P S.X₂ := by
  exact P.prop_X₂_of_shortExact (S := ShortComplex.mk
    (cokernel.desc a S.f wa) (kernel.lift e S.g we) (by ext; simp))
    (hS.shortExact_cokernelDesc_kernelLift wa we ha he)
    (P.prop_cokernel a hA h₁) (P.prop_kernel e h₃ hE)

end CategoryTheory.ObjectProperty

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] [Abelian C]

/-- A property `P` of objects of an abelian category is a *closed class* if it holds for every
zero object and, for every short exact sequence `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` with `P X₁`, `P X₂`
holds exactly when `P X₃` does. Such a class is closed under extensions
(`CategoryTheory.ObjectProperty.IsClosedClass.isClosedUnderExtensions`). -/
class IsClosedClass (P : ObjectProperty C) : Prop where
  /-- A closed class contains every zero object. -/
  prop_of_isZero {X : C} : IsZero X → P X
  /-- In a short exact sequence whose first term is in the class, the middle term is in it
  exactly when the last one is. -/
  prop_X₂_iff_prop_X₃ {S : ShortComplex C} (hS : S.ShortExact) (h₁ : P S.X₁) : P S.X₂ ↔ P S.X₃

/-- A closed class is closed under extensions. -/
instance IsClosedClass.isClosedUnderExtensions (P : ObjectProperty C) [P.IsClosedClass] :
    P.IsClosedUnderExtensions where
  prop_X₂_of_shortExact hS h₁ h₃ := (IsClosedClass.prop_X₂_iff_prop_X₃ hS h₁).2 h₃

/-- **A property closed under isomorphisms and extensions is closed under binary coproducts.** In
an abelian category a binary coproduct of `X` and `Y` is isomorphic to the biproduct `X ⊞ Y`, an
extension of `Y` by `X`. -/
theorem isClosedUnderBinaryCoproducts_of_isClosedUnderExtensions (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions] :
    P.IsClosedUnderBinaryCoproducts where
  colimitsOfShape_le := by
    rintro X ⟨p⟩
    refine P.prop_of_iso ?_
      (P.prop_biprod (p.prop_diag_obj (.mk .left)) (p.prop_diag_obj (.mk .right)))
    exact IsColimit.coconePointUniqueUpToIso (BinaryBiproduct.isColimit _ _)
      ((IsColimit.precomposeHomEquiv (diagramIsoPair p.diag).symm _).invFun p.isColimit)

/-- **A property containing zero and closed under isomorphisms and extensions is closed under
finite coproducts**, for instance a Serre class: a finite coproduct is an iterated extension of its
summands. -/
instance isClosedUnderFiniteCoproducts_of_isClosedUnderExtensions (P : ObjectProperty C)
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions] :
    P.IsClosedUnderFiniteCoproducts :=
  have := P.isClosedUnderBinaryCoproducts_of_isClosedUnderExtensions
  .mk'

end CategoryTheory.ObjectProperty
