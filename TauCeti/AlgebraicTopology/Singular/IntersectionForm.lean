/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import TauCeti.AlgebraicTopology.Singular.MinimalGenus

/-!
# Intersection forms on the second homology

The intersection form of a closed oriented four-manifold `X` is a symmetric `ℤ`-bilinear form on
`H₂(X; ℤ)` (`TauCeti.secondHomology X`). This file names the type of such forms,
`TauCeti.IntersectionForm X`, and their symmetry, `TauCeti.IntersectionForm.IsSymm`.

They are bilinear for the `ℤ`-module structure `AddCommGroup.toIntModule`, the one the abstract
counts and cycles over an additive group use, rather than for the `ModuleCat ℤ` structure of
`secondHomology X`, which agrees with it only propositionally. Naming the forms with this instance
spares their consumers a local instance override.

## Main definitions

* `TauCeti.IntersectionForm X`: the `ℤ`-bilinear forms on `H₂(X; ℤ)`.
* `TauCeti.IntersectionForm.IsSymm`: symmetry of such a form.
-/

public section

namespace TauCeti

/-- The `ℤ`-bilinear forms on `H₂(X; ℤ)`, such as the intersection form of a closed oriented
four-manifold `X`. They are bilinear for the `ℤ`-module structure `AddCommGroup.toIntModule`, the
one the abstract counts and cycles over an additive group use, rather than for the `ModuleCat ℤ`
structure of `secondHomology X`, which agrees with it only propositionally. -/
abbrev IntersectionForm (X : Type) [TopologicalSpace X] : Type :=
  @LinearMap.BilinForm ℤ _ (secondHomology X) _ (AddCommGroup.toIntModule _)

/-- An intersection form `B : TauCeti.IntersectionForm X` is **symmetric**,
`LinearMap.BilinForm.IsSymm` for the `ℤ`-module structure `AddCommGroup.toIntModule`. -/
abbrev IntersectionForm.IsSymm {X : Type} [TopologicalSpace X] (B : IntersectionForm X) : Prop :=
  @LinearMap.BilinForm.IsSymm ℤ (secondHomology X) _ _ (AddCommGroup.toIntModule _) B

end TauCeti
