/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.KFlat
public import TauCeti.Algebra.Homology.Monoidal.KFlat.LeftDerivedTensor
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product

/-!
# The derived tensor product on `D(𝒪_X)`

For a scheme `X`, the K-flat complexes of `𝒪_X`-modules form a left derivability structure
(`TauCeti.AlgebraicGeometry.Coherent.isLeftDerivabilityStructure_kFlat_localizerMorphism`), so
the derived tensor product `TauCeti.derivedTensor X.Modules` exists on the unbounded derived
category `D(𝒪_X)`, stated on `X.Modules` itself rather than on the unfolded category of sheaves of
modules over `X.ringCatSheaf`.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Coherent

variable (X : Scheme.{u})

/-- K-flat complexes of `𝒪_X`-modules form a left derivability structure, so the derived tensor
product exists on `D(𝒪_X)`. This is the site-level instance for the structure sheaf of `X`. -/
instance isLeftDerivabilityStructure_kFlat_localizerMorphism :
    (CochainComplex.KFlat.localizerMorphism X.Modules).IsLeftDerivabilityStructure :=
  CochainComplex.KFlat.instIsLeftDerivabilityStructureLocalizerMorphismSheafOfModules
    (R := X.sheaf)

end TauCeti.AlgebraicGeometry.Coherent
