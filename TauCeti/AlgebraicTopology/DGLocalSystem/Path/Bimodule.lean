/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.DGLocalSystem.LoopAlgebra
public import TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Bimodule
public import TauCeti.Topology.PathSpace.Moore.Between.Basic

/-!
# The chain bimodule of Moore paths between two basepoints

For two points `b` and `b'` of a space `B`, the Moore loops at `b` act on the Moore paths from `b`
to `b'` by concatenation in front, and those at `b'` by concatenation behind; the two actions are
strictly associative and unital, and commute (`TauCeti.MoorePathBetween`).  So the normalized
cubical chains `C_*(P_{b→b'} B; R)` form a differential graded
`(C_*(Ω_b B; R), C_*(Ω_{b'} B; R))`-bimodule.  The derived tensor product with this bimodule
carries DG local systems at `b` to DG local systems at `b'`, which is how a DG local system
changes basepoint.

The chains are the module
`TauCeti.cubicalChainModule (MoorePathBetween B b b') (MooreLoopSpace B b') R` of
`TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Action`, whose left action is that of
`TauCeti.AlgebraicTopology.Singular.Cubical.MonoidAlgebra.Bimodule`.

## Main results

* `TauCeti.pathChain_isDGBimodule`: the chains `C_*(P_{b→b'} B; R)` form a DG
  `(C_*(Ω_b B), C_*(Ω_{b'} B))`-bimodule.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 2 and §7.1.
-/

public section

namespace TauCeti

variable (B : Type*) [TopologicalSpace B] (b b' : B) (R : Type*) [CommRing R]

/-- **The chains of the Moore paths from `b` to `b'` form a differential graded
`(C_*(Ω_b B), C_*(Ω_{b'} B))`-bimodule**: the loops at `b` act by concatenation in front, those
at `b'` by concatenation behind, the chains of dimension `n` lie in cohomological degree `-n`, and
the boundary is the differential. -/
theorem pathChain_isDGBimodule :
    IsDGBimodule (loopChain_isDGAlgebra B b R) (loopChain_isDGAlgebra B b' R)
      (cubicalChainModuleGrading (MoorePathBetween B b b') (MooreLoopSpace B b') R)
      (cubicalChainModuleDifferential (MoorePathBetween B b b') (MooreLoopSpace B b') R) :=
  cubicalChainModule_isDGBimodule (MooreLoopSpace B b) (MoorePathBetween B b b')
    (MooreLoopSpace B b') R

end TauCeti
