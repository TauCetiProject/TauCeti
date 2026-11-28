/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import TauCeti.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Weak Serre subcategories, five-term exact sequences and closed classes

An extension-closed property containing zero is closed under finite products in a preadditive
category with finite products.

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

A property of objects of a preadditive category with a zero object and finite biproducts which
contains zero and is closed under isomorphisms and extensions, for instance a Serre class, is closed
under finite coproducts
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

/-- An extension-closed property containing zero is closed under finite products. -/
instance isClosedUnderFiniteProducts_of_isClosedUnderExtensions {C : Type*} [Category* C]
    [Preadditive C] [HasFiniteProducts C] (P : ObjectProperty C)
    [P.ContainsZero] [P.IsClosedUnderExtensions] : P.IsClosedUnderFiniteProducts := by
  have : HasFiniteBiproducts C := HasFiniteBiproducts.of_hasFiniteProducts
  have : P.IsClosedUnderIsomorphisms := by
    refine ⟨fun {X Y} e hX ↦ ?_⟩
    obtain ⟨Z, hZ, hPZ⟩ := P.exists_prop_of_containsZero
    let S := ShortComplex.mk (0 : Z ⟶ Y) e.inv (by simp)
    exact P.prop_X₂_of_shortExact
      ((ShortComplex.Splitting.ofIsZeroOfIsIso S hZ
        (inferInstanceAs (IsIso e.inv))).shortExact) hPZ hX
  have : HasBinaryBiproducts C := hasBinaryBiproducts_of_finite_biproducts C
  have : P.IsClosedUnderBinaryProducts :=
    P.isClosedUnderBinaryProducts_of_prop_biprod fun _ _ hX hY ↦ P.prop_biprod hX hY
  exact .mk'

variable {C : Type*} [Category* C] [Abelian C] (P : ObjectProperty C)
  [P.IsClosedUnderKernels] [P.IsClosedUnderCokernels] [P.IsClosedUnderExtensions]

/-- A property closed under kernels, cokernels and extensions contains the middle object of a
five-term exact sequence `A ⟶ S.X₁ ⟶ S.X₂ ⟶ S.X₃ ⟶ E` whose four outer objects it contains. -/
theorem prop_X₂_of_exact_of_exact_of_exact {S : ShortComplex C} (hS : S.Exact) {A E : C}
    {a : A ⟶ S.X₁} {e : S.X₃ ⟶ E} (wa : a ≫ S.f = 0) (we : S.g ≫ e = 0)
    (ha : (ShortComplex.mk a S.f wa).Exact) (he : (ShortComplex.mk S.g e we).Exact)
    (hA : P A) (h₁ : P S.X₁) (h₃ : P S.X₃) (hE : P E) : P S.X₂ := by
  -- `S.X₂` is an extension of the kernel of `e` by the cokernel of `a`
  let T := ShortComplex.mk (cokernel.desc a S.f wa) (kernel.lift e S.g we) (by ext; simp)
  have : Mono T.f := ha.mono_cokernelDesc
  have : Epi T.g := he.epi_kernelLift
  -- exactness of `T` follows from that of `S`, via the short complex `cokernel a ⟶ S.X₂ ⟶ S.X₃`
  let T' := ShortComplex.mk (cokernel.desc a S.f wa) S.g (by ext; simp)
  let φ : S ⟶ T' := ShortComplex.homMk (cokernel.π a) (𝟙 _) (𝟙 _) (by simp [T']) (by simp [T'])
  have : Epi φ.τ₁ := inferInstanceAs (Epi (cokernel.π a))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 S.X₂))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (𝟙 S.X₃))
  let ψ : T ⟶ T' := ShortComplex.homMk (𝟙 _) (𝟙 _) (kernel.ι e) (by simp [T, T'])
    (by simp [T, T'])
  have : Epi ψ.τ₁ := inferInstanceAs (Epi (𝟙 (cokernel a)))
  have : IsIso ψ.τ₂ := inferInstanceAs (IsIso (𝟙 S.X₂))
  have : Mono ψ.τ₃ := inferInstanceAs (Mono (kernel.ι e))
  have hT : T.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2
    ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).1 hS)
  exact P.prop_X₂_of_shortExact (S := T) ⟨hT⟩ (P.prop_cokernel a hA h₁) (P.prop_kernel e h₃ hE)

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

end CategoryTheory.ObjectProperty

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C]

/-- **A property closed under isomorphisms and extensions is closed under binary coproducts.** In
a preadditive category with a zero object and binary biproducts, a binary coproduct of `X` and `Y`
is isomorphic to the biproduct `X ⊞ Y`, an extension of `Y` by `X`. -/
theorem isClosedUnderBinaryCoproducts_of_isClosedUnderExtensions (P : ObjectProperty C)
    [HasBinaryBiproducts C] [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderExtensions] :
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
    [HasFiniteBiproducts C] [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderExtensions] :
    P.IsClosedUnderFiniteCoproducts :=
  have := hasBinaryBiproducts_of_finite_biproducts C
  have := P.isClosedUnderBinaryCoproducts_of_isClosedUnderExtensions
  .mk'

end CategoryTheory.ObjectProperty
