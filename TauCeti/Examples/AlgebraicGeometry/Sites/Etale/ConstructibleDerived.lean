/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Homology.DerivedCategory.HomologyIn
import TauCeti.AlgebraicGeometry.Sites.Etale.Constructible.Serre

/-!
# Triangulated subcategory of complexes with constructible cohomology

For any scheme `X` and left Noetherian ring `Λ`, complexes in `DerivedCategory` with constructible
cohomology sheaves (`DerivedCategory.homologyIn (X.constructibleSheaf Λ)`) form a triangulated
subcategory.
-/

open CategoryTheory AlgebraicGeometry Scheme

universe w u

example (X : Scheme.{u}) (Λ : Type u) [Ring Λ] [IsNoetherianRing Λ]
    [HasDerivedCategory.{w} (Sheaf (smallEtaleTopology X) (ModuleCat.{u} Λ))] :
    (DerivedCategory.homologyIn (X.constructibleSheaf Λ)).IsTriangulated :=
  inferInstance
