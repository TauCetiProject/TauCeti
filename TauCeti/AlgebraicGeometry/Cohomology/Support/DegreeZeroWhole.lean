/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Support

/-!
# Degree-zero cohomology with supports in the whole scheme

Let `X` be a scheme and `M` a sheaf of `𝒪_X`-modules. For a closed subset `Z` equal to the whole
of `X`, cohomology with supports in `Z` is cohomology
(`Scheme.Modules.cohomologyWithSupportLinearEquivOfSubset`), so in degree zero it is the module of
global sections: `H⁰_Z(X, M) ≃ₗ Γ(X, M)` over global functions
(`Scheme.Modules.cohomologyWithSupportZeroLinearEquivOfEqUniv`).

For `X = Spec A` and `Z = V(I)` this is the geometric degree-zero local cohomology. When
`V(I) = Spec A` it is all of `A`, whatever the ideal `I`, while Mathlib's native local cohomology
`H⁰_I(A)` is the `I`-power torsion of `A`, which can vanish when `A` is not Noetherian.
-/

public section

open AlgebraicGeometry TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

variable {X : Scheme.{u}} (M : X.Modules)

/-- Degree-zero cohomology with supports in a closed subset `Z` equal to the whole scheme is the
module of global sections: `H⁰_X(X, M) ≃ₗ Γ(X, M)`, linearly over global functions. -/
noncomputable def
    _root_.AlgebraicGeometry.Scheme.Modules.cohomologyWithSupportZeroLinearEquivOfEqUniv
    (Z : Closeds X) (hZ : (Z : Set X) = Set.univ) :
    M.cohomologyWithSupport Z ⊤ 0 ≃ₗ[Γ(X, ⊤)] Γ(M, ⊤) :=
  (M.cohomologyWithSupportLinearEquivOfSubset Z (hZ ▸ Set.subset_univ _) 0).trans
    ((M.cohomologyOnTopLinearEquiv 0).trans M.cohomologyZeroLinearEquiv)

end TauCeti.AlgebraicGeometry
