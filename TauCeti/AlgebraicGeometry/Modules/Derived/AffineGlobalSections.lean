/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.RightDerivedFunctor.Adjunction
public import TauCeti.Algebra.Homology.ModelCategory.KInjective.Resolution
public import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic

/-!
# Derived global sections on an affine scheme

For a commutative ring `A`, this file defines derived global sections
`RΓ(Spec A, -) : D(𝒪_{Spec A}) ⥤ D(A)` on unbounded complexes
(`TauCeti.AlgebraicGeometry.Coherent.derivedModuleSpecΓFunctor`), the right derived functor of the
global-section functor with values in `A`-modules, computed on K-injective replacements. The
category of `𝒪_{Spec A}`-modules is Grothendieck abelian, so these replacements exist.

Since `M ↦ M~` is exact and left adjoint to global sections, the functor it induces on derived
categories is left adjoint to `RΓ(Spec A, -)`
(`TauCeti.AlgebraicGeometry.Coherent.tildeDerivedAdjunction`). This adjunction is an equivalence
onto the complexes with quasi-coherent cohomology, `DQCoh.affineEquiv`, in
`TauCeti.AlgebraicGeometry.Modules.Derived.DQCoh.Affine`.
-/

public section

open CategoryTheory DerivedCategory

namespace TauCeti.AlgebraicGeometry.Coherent

open _root_.AlgebraicGeometry

universe w w' u

variable (A : CommRingCat.{u}) [HasDerivedCategory.{w} (Spec A).Modules]
  [HasDerivedCategory.{w'} (ModuleCat.{u} A)]

/-- Derived global sections `RΓ(Spec A, -) : D(𝒪_{Spec A}) ⥤ D(A)` on unbounded complexes: the right
derived functor of the global-section functor, computed on K-injective replacements. -/
noncomputable abbrev derivedModuleSpecΓFunctor :
    DerivedCategory (Spec A).Modules ⥤ DerivedCategory (ModuleCat.{u} A) :=
  (moduleSpecΓFunctor (R := A)).rightDerivedFunctor

/-- The derived adjunction `M ↦ M~ ⊣ RΓ(Spec A, -)` between `D(A)` and `D(𝒪_{Spec A})`, derived from
the adjunction between `M ↦ M~` and global sections. -/
@[expose]
noncomputable def tildeDerivedAdjunction :
    (tilde.functor A).mapDerivedCategory ⊣ derivedModuleSpecΓFunctor A :=
  tilde.adjunction.mapDerivedCategoryRightDerivedFunctor

end TauCeti.AlgebraicGeometry.Coherent
