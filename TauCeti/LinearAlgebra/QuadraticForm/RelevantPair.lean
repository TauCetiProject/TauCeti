/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.RelevantPair.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.RelevantPair.Stabilizer
public import TauCeti.LinearAlgebra.QuadraticForm.RelevantPair.BaseChange
public import TauCeti.LinearAlgebra.QuadraticForm.RelevantPair.OfProd

/-!
# Orthogonal relevant pairs and framed complements

This module re-exports the orthogonal relevant pair API:

* `TauCeti.LinearAlgebra.QuadraticForm.RelevantPair.Basic`: split hyperbolic sums,
  `OrthogonalRelevantPair`, `FramedOrthogonalRelevantPair`, orthogonal complement geometry,
  ambient splitting, and framing accessors.
* `TauCeti.LinearAlgebra.QuadraticForm.RelevantPair.Stabilizer`: the stabilizer embedding
  `SO(Q_W) →* SO(Q_V)`, transport along isometries, and intertwining.
* `TauCeti.LinearAlgebra.QuadraticForm.RelevantPair.BaseChange`: compatibility with scalar
  extension to a field extension `L / K`.
* `TauCeti.LinearAlgebra.QuadraticForm.RelevantPair.OfProd`: the canonical product model
  `FramedOrthogonalRelevantPair.ofProd` and non-vacuous dimension witnesses.
-/
