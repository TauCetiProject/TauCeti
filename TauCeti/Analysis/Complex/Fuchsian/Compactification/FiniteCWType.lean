/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Analysis.Complex.Fuchsian.Arithmetic
import TauCeti.Analysis.Complex.Fuchsian.Compactification.Manifold
import TauCeti.Analysis.Complex.Fuchsian.DirichletDomain.Cofinite
import TauCeti.Geometry.Manifold.Complex.FiniteCWType

/-!
# Finite CW type of cofinite Fuchsian compactifications

The cusp compactification `Γ.CompactifiedQuotient` of a cofinite Fuchsian group `Γ ≤ PSL(2, ℝ)`
is a compact Riemann surface (`Subgroup.IsCofinite.compactSpace_compactifiedQuotient`,
`Subgroup.CompactifiedQuotient.instIsManifold`). By `TauCeti.ComplexManifold.instFiniteCWType`,
it therefore has finite CW type. In particular, this applies to the effective image
`Γ'.map psl2zToPSL2R` of every finite-index subgroup `Γ' ≤ PSL(2, ℤ)`.

This file is split out from `TauCeti.Analysis.Complex.Fuchsian.Arithmetic` so that users of
cofiniteness and cusp combinatorics do not transitively import the Morse-theoretic finite-CW
machinery.

## Main results

* `Subgroup.IsCofinite.finiteCWType_compactifiedQuotient`: the compactified quotient of a cofinite
  Fuchsian group has finite CW type.
* `Subgroup.finiteCWType_compactifiedQuotient_map_psl2zToPSL2R`: the compactified modular curve
  `X(Γ')` of a finite-index subgroup `Γ' ≤ PSL(2, ℤ)` has finite CW type.
-/

public section

open scoped MatrixGroups

namespace Subgroup

/-- The compactified quotient of a cofinite Fuchsian group has finite CW type, as a compact
Riemann surface. -/
theorem IsCofinite.finiteCWType_compactifiedQuotient {Γ : Subgroup PSL(2, ℝ)}
    [DiscreteTopology Γ] (hΓ : Γ.IsCofinite) :
    TauCeti.FiniteCWType Γ.CompactifiedQuotient :=
  have := hΓ.compactSpace_compactifiedQuotient
  inferInstance

/-- The compactified modular curve `X(Γ')` of a finite-index `Γ' ≤ PSL(2, ℤ)` has finite CW
type. -/
instance finiteCWType_compactifiedQuotient_map_psl2zToPSL2R (Γ' : Subgroup PSL(2, ℤ))
    [Γ'.FiniteIndex] : TauCeti.FiniteCWType (Γ'.map psl2zToPSL2R).CompactifiedQuotient :=
  (isCofinite_map_psl2zToPSL2R Γ').finiteCWType_compactifiedQuotient

end Subgroup
