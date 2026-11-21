/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
public import TauCeti.Analysis.Complex.Fuchsian.Compactification.Signature
public import TauCeti.Geometry.Manifold.Complex.FiniteCWType

/-!
# Finite CW type for compactified modular curves

Every finite-index subgroup `Γ' ≤ PSL(2, ℤ)` has cofinite effective image in `PSL(2, ℝ)`
(`Subgroup.isCofinite_map_psl2zToPSL2R`), so its compactified quotient `X(Γ')` has finite CW type.
Isolating this instance here keeps cellular and signature dependencies out of
`TauCeti.Analysis.Complex.Fuchsian.Arithmetic`.
-/

public noncomputable section

open TauCeti Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups

namespace Subgroup

/-- The compactified modular curve `X(Γ')` of a finite-index `Γ' ≤ PSL(2, ℤ)` has finite CW
type. -/
instance finiteCWType_compactifiedQuotient_map_psl2zToPSL2R (Γ' : Subgroup PSL(2, ℤ))
    [Γ'.FiniteIndex] : FiniteCWType (Γ'.map psl2zToPSL2R).CompactifiedQuotient :=
  (isCofinite_map_psl2zToPSL2R Γ').finiteCWType_compactifiedQuotient

end Subgroup
