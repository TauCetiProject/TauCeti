/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiffMap.Chart.BranchLog
public import TauCeti.Geometry.Manifold.Instances.Rectangle

/-!
# Nowhere-vanishing vector fields on a rectangle standard near the boundary

Reading `ℂ` as `ℝ²`, the nowhere-vanishing `C^n` functions on the rectangle `[a, b] × [c, d]` equal
to `1` near its boundary are the nowhere-vanishing vector fields equal to the constant field
`(1, 0)` near the boundary. They form a contractible space in the weak Whitney topology
(`ContMDiffMap.contractibleSpace_nonvanishingEqOneNear_boundary_rectangle`), the case of a
rectangle and its connected boundary of `ContMDiffMap.contractibleSpace_nonvanishingEqOneNear`.
This is the homotopy-theoretic input to Smale's proof that the diffeomorphisms of the square equal
to the identity near the boundary form a contractible space (S. Smale, *Diffeomorphisms of the
2-sphere*, Proc. Amer. Math. Soc. 10 (1959), 621–626).
-/

public section

open Set
open scoped Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffMap

/-- **The nowhere-vanishing functions on a rectangle equal to `1` near its boundary form a
contractible space.** Reading `ℂ` as `ℝ²`, these are the nowhere-vanishing vector fields on
`[a, b] × [c, d]` equal to the constant field `(1, 0)` near the boundary. -/
theorem contractibleSpace_nonvanishingEqOneNear_boundary_rectangle {a b c d : ℝ}
    [Fact (a < b)] [Fact (c < d)] {n : WithTop ℕ∞} [ENat.LEInfty n] :
    ContractibleSpace (nonvanishingEqOneNear ((𝓡∂ 1).prod (𝓡∂ 1)) n
      (((𝓡∂ 1).prod (𝓡∂ 1)).boundary (Icc a b × Icc c d))) :=
  contractibleSpace_nonvanishingEqOneNear TauCeti.isConnected_boundary_rectangle

end ContMDiffMap
