/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Homotopy.Contractible
import TauCeti.AlgebraicTopology.Singular.Contractible

/-!
# The genus of a surface from its rational first homology

A compact, connected, orientable surface of genus `g` has `H₁(S; ℚ) ≅ ℚ²ᵍ` when it is closed and
`H₁(S; ℚ) ≅ ℚ²ᵍ⁺ᵇ⁻¹` when it has `b ≥ 1` boundary circles. So for a closed surface, or a surface
with one or two boundary circles, the genus is `⌊dim H₁(S; ℚ) / 2⌋`. This file defines that
quantity once for every topological space (`TauCeti.surfaceGenus`), as the common genus convention
of Seifert surfaces, slice surfaces, knot cobordisms and surfaces representing a homology class.

## Main definitions

* `TauCeti.surfaceGenus X`: half the dimension of `H₁(X; ℚ)`, rounded down.

## Main results

* `TauCeti.surfaceGenus_eq_zero_of_contractibleSpace`: a contractible space, such as a disc, has
  genus `0`.
-/

public section

noncomputable section

open CategoryTheory AlgebraicTopology Module

namespace TauCeti

/-- The **genus** of a surface `X`, read off its rational singular homology: half the dimension of
`H₁(X; ℚ)`, rounded down. For a compact, connected, orientable surface which is closed or has at
most two boundary circles, this is its genus. -/
def surfaceGenus (X : Type) [TopologicalSpace X] : ℕ :=
  finrank ℚ (((singularHomologyFunctor (ModuleCat.{0} ℚ) 1).obj (ModuleCat.of ℚ ℚ)).obj
    (TopCat.of X)) / 2

/-- The genus of a surface is half the dimension of its first rational homology, rounded down. -/
theorem surfaceGenus_def (X : Type) [TopologicalSpace X] :
    surfaceGenus X = finrank ℚ (((singularHomologyFunctor (ModuleCat.{0} ℚ) 1).obj
      (ModuleCat.of ℚ ℚ)).obj (TopCat.of X)) / 2 :=
  (rfl)

/-- **A contractible space has genus `0`**: its first homology vanishes. -/
@[simp]
theorem surfaceGenus_eq_zero_of_contractibleSpace (X : Type) [TopologicalSpace X]
    [ContractibleSpace X] : surfaceGenus X = 0 := by
  have := ModuleCat.isZero_iff_subsingleton.1 <|
    isZero_singularHomologyFunctor_of_contractibleSpace (ModuleCat.of ℚ ℚ) (TopCat.of X)
      one_ne_zero
  rw [surfaceGenus_def, finrank_zero_of_subsingleton, Nat.zero_div]

end TauCeti
