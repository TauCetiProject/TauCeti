/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeology.Circle
public import TauCeti.Geometry.Diffeology.ContMDiffMap

/-!
# Examples: smooth circle rotations in the functional diffeology

Right multiplication on `Circle` by `Circle.exp t` defines a one-parameter family of rotations
`circleRotation : ℝ → C^∞⟮𝓡 1, Circle; 𝓡 1, Circle⟯`. Using `dSmooth_smoothRightMul` and
`dSmooth_circleExp`, this family is diffeologically smooth for the functional diffeology on
`C^∞⟮𝓡 1, Circle; 𝓡 1, Circle⟯`, and its `𝔼¹`-reparametrization `u ↦ circleRotation (u 0)` is a
plot (`isPlot_circleRotation`).

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), §1.57 and §4.3.
-/

public noncomputable section

open TauCeti
open scoped ContDiff Manifold

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

/-- Rotation of `Circle` by angle `t : ℝ`, bundled in `C^∞⟮𝓡 1, Circle; 𝓡 1, Circle⟯`. -/
def circleRotation (t : ℝ) : C^∞⟮𝓡 1, Circle; 𝓡 1, Circle⟯ :=
  smoothRightMul (𝓡 1) (Circle.exp t)

/-- Evaluating `circleRotation t` at `z` returns `z * Circle.exp t`. -/
@[simp]
theorem circleRotation_apply (t : ℝ) (z : Circle) : circleRotation t z = z * Circle.exp t :=
  (rfl)

/-- The circle rotation family `ℝ → C^∞⟮𝓡 1, Circle; 𝓡 1, Circle⟯` is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_circleRotation : _root_.Diffeology.DSmooth circleRotation :=
  dSmooth_smoothRightMul.comp dSmooth_circleExp

/-- Reparametrizing `circleRotation` by `𝔼¹` via `u ↦ u 0` yields a plot of the functional
diffeology on `C^∞⟮𝓡 1, Circle; 𝓡 1, Circle⟯`. -/
theorem isPlot_circleRotation :
    _root_.Diffeology.IsPlot (fun u : 𝔼¹ ↦ circleRotation (u 0)) :=
  (dSmooth_circleRotation.comp (EuclideanSpace.proj (0 : Fin 1)).contDiff.dSmooth).isPlot

end TauCeti.Diffeology
