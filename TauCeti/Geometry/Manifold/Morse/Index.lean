/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Geometry.Manifold.Morse.Basic

/-!
# The Morse index on a smooth manifold

The Morse index of a critical point is the negative index of inertia of its Hessian. This file
lifts `TauCeti.morseIndex` from a normed vector space to a smooth manifold by applying it to the
coordinate expression in the preferred extended chart.

Following `TauCeti.IsManifoldNondegenerateCriticalPoint`, the definition itself assumes no
smoothness and no boundarylessness; it is the intrinsic invariant of a `C²` critical point of a
boundaryless `C²` manifold, and the invariance results state the hypotheses they use. In
particular, `TauCeti.manifoldMorseIndex_transContinuousLinearEquiv` proves that the index is
unchanged when the model space is replaced through a continuous linear equivalence, assuming
exactly `C²` regularity and criticality of the chart expression. The model-space comparison
theorem makes the construction reduce exactly to the existing calculus definition.

The index supplies the grading of the Morse complex. Negating the function exchanges the stable
and unstable directions, so the two indices add to the dimension of the model space; this is the
dimension relation used for the stable and unstable manifolds of the negative-gradient flow.

## Main declarations

* `TauCeti.manifoldMorseIndex`: the Morse index in the preferred manifold chart.
* `TauCeti.manifoldMorseIndex_modelSpace`: comparison with `TauCeti.morseIndex` on a normed
  vector space.
* `TauCeti.manifoldMorseIndex_transContinuousLinearEquiv`: invariance under an equivalent choice
  of model space.
* `TauCeti.IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_neg_add_eq_finrank`: the
  complementary-index formula for a function and its negation.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 2.
-/

public section

open Function
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E E' H M : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable [TopologicalSpace M] [ChartedSpace H M]
variable {f : M → ℝ} {x : M}

/-- The **Morse index** of a real-valued function at a point of a smooth manifold: the negative
index of inertia of the Hessian of its expression in the preferred extended chart.

As with `TauCeti.morseIndex` and `TauCeti.IsManifoldNondegenerateCriticalPoint`, the definition
carries no smoothness or boundary hypotheses and is available at every point; the results that
give it intrinsic meaning carry the hypotheses they need explicitly. It is the intended
chart-independent invariant when `I.Boundaryless` and `IsManifold I 2 M` hold and `x` is a `C²`
critical point: only then does the unconstrained Hessian of the chart expression used here
compute the intrinsic Hessian, because `range I` is then a neighbourhood of `extChartAt I x x`
and the chart transitions are `C²`. For a model with boundary or corners the unconstrained
Hessian can depend on the behaviour of the chart inverse off `range I`, and it is in any case
not the boundary Morse condition, which is a different theory. Its interpretation as the
dimension of the unstable space assumes finite-dimensionality. -/
noncomputable def manifoldMorseIndex (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) : ℕ :=
  morseIndex (f ∘ (extChartAt I x).symm) (extChartAt I x x)

/-- The manifold Morse index is the Morse index of the preferred coordinate expression. -/
theorem manifoldMorseIndex_def :
    manifoldMorseIndex I f x =
      morseIndex (f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
  (rfl)

/-- On a normed vector space with its self-model manifold structure, the manifold Morse index is
the ordinary Morse index. -/
@[simp]
theorem manifoldMorseIndex_modelSpace {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : V → ℝ} {v : V} :
    manifoldMorseIndex (modelWithCornersSelf ℝ V) g v = morseIndex g v := by
  simp only [manifoldMorseIndex, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, Function.comp_id, id_eq]

/-- The manifold Morse index is at most the dimension of a finite-dimensional model space. -/
theorem manifoldMorseIndex_le_finrank [FiniteDimensional ℝ E] :
    manifoldMorseIndex I f x ≤ Module.finrank ℝ E :=
  morseIndex_le_finrank

/-- The manifold Morse index is unchanged when the manifold model is transported through a
continuous linear equivalence. This is the model-coordinate invariance of the index at any `C²`
critical point; nondegeneracy is not needed. -/
theorem manifoldMorseIndex_transContinuousLinearEquiv
    (hreg : ContDiffAt ℝ 2 (f ∘ (extChartAt I x).symm) (extChartAt I x x))
    (hcrit : fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) = 0)
    (e : E ≃L[ℝ] E') :
    manifoldMorseIndex (I.transContinuousLinearEquiv e) f x = manifoldMorseIndex I f x := by
  let g : E → ℝ := f ∘ (extChartAt I x).symm
  let a : E := extChartAt I x x
  have hfun : f ∘ (extChartAt (I.transContinuousLinearEquiv e) x).symm = g ∘ e.symm := by
    rw [I.coe_extChartAt_transContinuousLinearEquiv_symm]
    rfl
  have hpoint : extChartAt (I.transContinuousLinearEquiv e) x x = e a := by
    simpa only [a, Function.comp_apply] using
      congrFun (I.coe_extChartAt_transContinuousLinearEquiv e x) x
  rw [manifoldMorseIndex_def, manifoldMorseIndex_def, hfun, hpoint]
  have hgreg : ContDiffAt ℝ 2 g (e.symm (e a)) := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hreg
  have hcrit' : fderiv ℝ g (e.symm (e a)) = 0 := by
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hcrit
  have hinv : (fderiv ℝ (e.symm : E' → E) (e a)).IsInvertible := by
    rw [e.symm.hasFDerivAt.fderiv]
    exact ContinuousLinearMap.isInvertible_equiv
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using
    (morseIndex_comp (f := g) (φ := (e.symm : E' → E)) (b := e a) hgreg
      e.symm.contDiff.contDiffAt hcrit' hinv)

namespace IsManifoldNondegenerateCriticalPoint

/-- At a nondegenerate critical point, the Morse indices of a function and its negation add to
the dimension of the manifold. -/
theorem manifoldMorseIndex_neg_add_eq_finrank [FiniteDimensional ℝ E]
    (h : IsManifoldNondegenerateCriticalPoint I f x) :
    manifoldMorseIndex I (-f) x + manifoldMorseIndex I f x = Module.finrank ℝ E := by
  have hfun : (-f) ∘ (extChartAt I x).symm = -(f ∘ (extChartAt I x).symm) := by
    funext y
    rfl
  rw [manifoldMorseIndex_def, manifoldMorseIndex_def, hfun]
  exact ((isManifoldNondegenerateCriticalPoint_iff I).mp h)
    |>.morseIndex_neg_add_morseIndex_eq_finrank

end IsManifoldNondegenerateCriticalPoint

end TauCeti

end
