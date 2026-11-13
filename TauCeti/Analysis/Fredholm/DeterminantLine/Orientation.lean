/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Bundle
public import TauCeti.Topology.VectorBundle.Orientation.Cover

/-!
# The orientation double cover of the determinant line bundle

Over `ℝ` the determinant line bundle of Fredholm operators (`TauCeti.FredholmDetLine`) has an
orientation double cover, and its projection is a covering map
(`TauCeti.FredholmDetLine.isCoveringMap_orientationCover_proj`). Orientations of determinant lines
are therefore transported along continuous paths of Fredholm operators by lifting to this cover
(`TauCeti.VectorBundleOrientationCover.orientationTransport`), canonically and without any choice
of connection. This transport is how orientations of moduli spaces in Morse and Floer theory,
which are orientations of the determinant lines of their linearized operators, are compared along
paths of operators.

## Main results

* `TauCeti.FredholmDetLine.isCoveringMap_orientationCover_proj`: over `ℝ`, the orientation double
  cover of the determinant line bundle is a covering map.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

namespace TauCeti.FredholmDetLine

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **The orientation double cover of the determinant line bundle is a covering map.** Lifting
paths of Fredholm operators to it transports orientations of determinant lines
(`TauCeti.VectorBundleOrientationCover.orientationTransport`). -/
theorem isCoveringMap_orientationCover_proj :
    IsCoveringMap (VectorBundleOrientationCover.proj :
      VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1) →
        {T : E →L[ℝ] F // T.IsFredholm}) :=
  VectorBundleOrientationCover.isCoveringMap_proj (by simp)

end TauCeti.FredholmDetLine
