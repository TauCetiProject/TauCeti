/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Surface
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Orientation.Smooth
public import TauCeti.Geometry.Manifold.Morse.CWModel

/-!
# Euler characteristic of a closed oriented smooth surface

Let `M` be a compact connected Hausdorff smooth surface without boundary, modelled on a real
two-dimensional inner product space `E`, with a smooth orientation `o`. Then `M` has finite CW
type (`TauCeti.FiniteCWType.of_isManifold`, from a Morse function on `M`), so its finite-CW Euler
characteristic `TauCeti.eulerChar M` is defined, and `o` determines a homological orientation
(`TauCeti.Manifold.Orientation.toHomologicalOrientation`). The Euler--Poincaré computation for
homologically oriented surfaces
(`TauCeti.HomologicalOrientation.eulerChar_eq_two_sub_finrank_singularHomology_one`) then gives
`χ(M) = 2 - b₁(M; ℚ)`, and in particular `χ(M) ≤ 2`.

The finite CW type instance enters the statements through `FiniteCWType.of_isManifold`. Since
`TauCeti.FiniteCWType` is a proposition, the statements apply verbatim to `eulerChar M` formed
with any other instance.

These statements do not assert that `b₁` is even, nor do they define a genus; both need the
nondegenerate alternating cup pairing of Poincaré duality.

## Main results

* `TauCeti.Manifold.Orientation.eulerChar_eq_two_sub_finrank_singularHomology_one`: a closed
  connected oriented smooth surface has `χ = 2 - b₁`, with rational coefficients.
* `TauCeti.Manifold.Orientation.eulerChar_le_two`: a closed connected oriented smooth surface has
  `χ ≤ 2`.

## References

* A. Hatcher, *Algebraic Topology*, Sections 2.2 and 3.3.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Module
open scoped Manifold ContDiff

namespace TauCeti.Manifold.Orientation

variable {M E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [T2Space M] [CompactSpace M] [ConnectedSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] (o : TauCeti.Manifold.Orientation 𝓘(ℝ, E) M (Fin 2))
  (hn : finrank ℝ E = 2)

include o hn

/-- **The Euler characteristic of a closed oriented smooth surface is `2 - b₁`.** For a compact
connected Hausdorff smooth surface `M` without boundary with a smooth orientation `o`, the
finite-CW Euler characteristic, defined through the finite CW type of
`TauCeti.FiniteCWType.of_isManifold`, is `2` minus the rank of the first rational singular
homology. -/
theorem eulerChar_eq_two_sub_finrank_singularHomology_one :
    haveI := FiniteCWType.of_isManifold (I := 𝓘(ℝ, E)) M
    eulerChar M = 2 - (finrank ℚ
      (((singularHomologyFunctor (ModuleCat.{0} ℚ) 1).obj (ModuleCat.of ℚ ℚ)).obj
        (TopCat.of M)) : ℤ) :=
  haveI := FiniteCWType.of_isManifold (I := 𝓘(ℝ, E)) M
  (o.toHomologicalOrientation (n := 1) hn).eulerChar_eq_two_sub_finrank_singularHomology_one hn

/-- A closed connected oriented smooth surface has Euler characteristic at most two. -/
theorem eulerChar_le_two :
    haveI := FiniteCWType.of_isManifold (I := 𝓘(ℝ, E)) M
    eulerChar M ≤ 2 :=
  haveI := FiniteCWType.of_isManifold (I := 𝓘(ℝ, E)) M
  (o.toHomologicalOrientation (n := 1) hn).eulerChar_le_two hn

end TauCeti.Manifold.Orientation
