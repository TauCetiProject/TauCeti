/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Diffeology.Manifold

/-!
# The standard manifold diffeology on the unit circle

This file equips `Circle` (the unit sphere in `ℂ`, modelled as a smooth 1-manifold on
`EuclideanSpace ℝ (Fin 1)`) with its canonical manifold diffeology (`instDiffeologicalSpaceCircle`),
registers `IsContMDiffCompatible` (`instIsContMDiffCompatibleCircle`), and records diffeological
smoothness of `Circle.exp : ℝ → Circle` (`dSmooth_circleExp`).

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), §4.3.
-/

public noncomputable section

open scoped ContDiff Manifold

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

/-- The standard manifold diffeology on the unit circle `Circle` in `ℂ`. -/
instance instDiffeologicalSpaceCircle : DiffeologicalSpace Circle :=
  manifoldDiffeology (𝔼¹) Circle

/-- `Circle` with `instDiffeologicalSpaceCircle` is compatible with its standard manifold
structure modelled on `𝔼¹`. -/
instance instIsContMDiffCompatibleCircle : IsContMDiffCompatible (𝔼¹) Circle :=
  inferInstanceAs (@IsContMDiffCompatible (𝔼¹) _ _ Circle _ _ (manifoldDiffeology (𝔼¹) Circle))

/-- The exponential map `Circle.exp : ℝ → Circle` is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_circleExp : _root_.Diffeology.DSmooth Circle.exp :=
  contMDiff_circleExp.dSmooth

end TauCeti.Diffeology
