/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Trivial
import TauCeti.Geometry.Manifold.VectorField.LieBracket

/-! # Curvature of the trivial connection -/

public section

open Bundle TauCeti
open scoped ContDiff Manifold

namespace CovariantDerivative

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F H M : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (minSmoothness 𝕜 2) M]

/-- The trivial connection has zero curvature on differentiable vector fields and a section
with enough derivatives for symmetry of its second derivative. -/
theorem curvatureOperator_trivial {X Y : Π y : M, TangentSpace I y} {s : M → F} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hs : ContMDiffAt I 𝓘(𝕜, F) (minSmoothness 𝕜 2) s x) :
    (trivial (I := I) F).curvatureOperator X Y s x = 0 := by
  simp only [curvatureOperator_apply, trivial_apply, mvfderiv_mlieBracket hs le_rfl hX hY,
    sub_self]

end CovariantDerivative
