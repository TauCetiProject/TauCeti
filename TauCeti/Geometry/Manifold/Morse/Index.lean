/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Geometry.Manifold.Morse.Basic
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic

import TauCeti.Analysis.Calculus.ContDiff.Differentiable

/-!
# The Morse index on a smooth manifold

This file defines the preferred-extended-chart Morse index by applying `TauCeti.morseIndex` to a
function's coordinate expression in the preferred extended chart.

Following `TauCeti.IsManifoldNondegenerateCriticalPoint`, the definition itself assumes no
smoothness and no boundarylessness. The results below prove that it depends only on the germ of
the function, and that it is unchanged when the model space is transported through a continuous
linear equivalence. The model-space comparison
theorem makes the construction reduce exactly to the existing calculus definition. This file does
not compare the preferred chart with arbitrary manifold charts.

When the preferred-chart Hessian is nondegenerate, the indices of a function and its negation add
to the dimension of the model space. At an interior local minimum of a `C¹` function,
the index vanishes without a nondegeneracy assumption.

## Main declarations

* `TauCeti.manifoldMorseIndex`: the Morse index in the preferred manifold chart.
* `TauCeti.manifoldMorseIndex_congr_of_eventuallyEq`: the index depends only on the germ of the
  function.
* `TauCeti.manifoldMorseIndex_modelSpace`: comparison with `TauCeti.morseIndex` on a normed
  vector space.
* `ContMDiffAt.hessianQuadraticForm_comp_extChartAt_symm_nonneg`: the preferred-chart Hessian
  quadratic form is nonnegative at an interior local minimum of a `C¹` function.
* `TauCeti.manifoldMorseIndex_const` and `TauCeti.manifoldMorseIndex_eq_zero_of_isLocalMin`: the
  index vanishes for a constant function and at an interior local minimum of a `C¹` function.
* `TauCeti.manifoldMorseIndex_transContinuousLinearEquiv`: invariance under an equivalent choice
  of model space.
* `TauCeti.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank`: the complementary-index
  formula under nondegeneracy of the preferred-chart Hessian.
* `IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank`:
  the critical-point specialization.
* `IsManifoldNondegenerateCriticalPoint.manifoldMorseIndex_neg_eq_add_one_of_eq_add_one`: critical
  points of consecutive index for `f` have consecutive index for `-f`, in the opposite order.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 1.
* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Section 2.
-/

public section

open Filter Function Topology
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
carries no smoothness or boundary hypotheses and is available at every point. It is specifically
the index computed in the preferred extended chart; the results below prove germ locality and
invariance under transport of the model by a continuous linear equivalence. For a model with
boundary or corners the unconstrained Hessian can depend on the behaviour of the chart inverse
off `range I`, and it is not the boundary Morse condition, which is a different theory. -/
noncomputable def manifoldMorseIndex (I : ModelWithCorners ℝ E H) (f : M → ℝ) (x : M) : ℕ :=
  morseIndex (f ∘ (extChartAt I x).symm) (extChartAt I x x)

/-- The manifold Morse index is the Morse index of the preferred coordinate expression. -/
theorem manifoldMorseIndex_def :
    manifoldMorseIndex I f x =
      morseIndex (f ∘ (extChartAt I x).symm) (extChartAt I x x) :=
  (rfl)

/-- The manifold Morse index depends only on the germ of the function at the point. -/
theorem manifoldMorseIndex_congr_of_eventuallyEq {g : M → ℝ} (hfg : f =ᶠ[𝓝 x] g) :
    manifoldMorseIndex I f x = manifoldMorseIndex I g x := by
  rw [manifoldMorseIndex_def, manifoldMorseIndex_def]
  have hfg' := hfg
  have hchart : (extChartAt I x).symm (extChartAt I x x) = x := by simp
  have hnhds : 𝓝 x = 𝓝 ((extChartAt I x).symm (extChartAt I x x)) :=
    (congrArg 𝓝 hchart).symm
  rw [hnhds] at hfg'
  exact morseIndex_congr_of_eventuallyEq
    (hfg'.comp_tendsto (continuousAt_extChartAt_symm (I := I) x))

/-- On a normed vector space with its self-model manifold structure, the manifold Morse index is
the ordinary Morse index. -/
@[simp]
theorem manifoldMorseIndex_modelSpace {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g : V → ℝ} {v : V} :
    manifoldMorseIndex (modelWithCornersSelf ℝ V) g v = morseIndex g v := by
  simp only [manifoldMorseIndex, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, Function.comp_id, id_eq]

/-- A constant function has zero Hessian, hence Morse index `0` at every point. -/
@[simp]
theorem manifoldMorseIndex_const (c : ℝ) (x : M) : manifoldMorseIndex I (fun _ : M ↦ c) x = 0 := by
  simp [manifoldMorseIndex_def, Function.comp_def]

/-- The manifold Morse index is at most the dimension of the model space. -/
theorem manifoldMorseIndex_le_finrank :
    manifoldMorseIndex I f x ≤ Module.finrank ℝ E :=
  morseIndex_le_finrank

/-- On a manifold modelled on a zero-dimensional space every Morse index is `0`. -/
@[simp]
theorem manifoldMorseIndex_eq_zero_of_subsingleton [Subsingleton E] :
    manifoldMorseIndex I f x = 0 :=
  Nat.le_zero.1 (manifoldMorseIndex_le_finrank.trans_eq Module.finrank_zero_of_subsingleton)

/-- At an interior local minimum of a `C¹` function, the Hessian quadratic form of its
preferred coordinate expression is nonnegative. No finite-dimensionality assumption is needed. -/
theorem _root_.ContMDiffAt.hessianQuadraticForm_comp_extChartAt_symm_nonneg
    (hf : ContMDiffAt I 𝓘(ℝ) 1 f x) (hx : I.IsInteriorPoint x) (hmin : IsLocalMin f x)
    (v : E) : 0 ≤ hessianQuadraticForm (f ∘ (extChartAt I x).symm) (extChartAt I x x) v := by
  rw [hessianQuadraticForm_apply]
  exact fderiv_fderiv_self_nonneg_of_isLocalMin
    ((hf.contDiffAt_comp_extChartAt_symm_of_isInteriorPoint hx).eventually_differentiableAt le_rfl)
    (hmin.comp_extChartAt_symm (I := I)) v

/-- At an interior local minimum of a `C¹` function, the preferred-chart Morse index is zero.
No nondegeneracy assumption is needed. -/
theorem manifoldMorseIndex_eq_zero_of_isLocalMin
    (hf : ContMDiffAt I 𝓘(ℝ) 1 f x) (hx : I.IsInteriorPoint x) (hmin : IsLocalMin f x) :
    manifoldMorseIndex I f x = 0 := by
  rw [manifoldMorseIndex_def]
  by_cases hE : FiniteDimensional ℝ E
  swap
  · exact morseIndex_eq_zero_of_not_finiteDimensional hE
  rw [morseIndex_def]
  exact (QuadraticForm.forall_nonneg_iff_sigNeg_eq_zero _).mp
    (hf.hessianQuadraticForm_comp_extChartAt_symm_nonneg hx hmin)

/-- The manifold Morse index is unchanged when the manifold model is transported through a
continuous linear equivalence. -/
theorem manifoldMorseIndex_transContinuousLinearEquiv (e : E ≃L[ℝ] E') :
    manifoldMorseIndex (I.transContinuousLinearEquiv e) f x = manifoldMorseIndex I f x := by
  let g : E → ℝ := f ∘ (extChartAt I x).symm
  let a : E := extChartAt I x x
  have hfun : f ∘ (extChartAt (I.transContinuousLinearEquiv e) x).symm =
      g ∘ (e.symm.toContinuousLinearMap : E' → E) := by
    rw [I.coe_extChartAt_transContinuousLinearEquiv_symm]
    rfl
  have hpoint : extChartAt (I.transContinuousLinearEquiv e) x x = e a := by
    simpa only [a, Function.comp_apply] using
      congrFun (I.coe_extChartAt_transContinuousLinearEquiv e x) x
  rw [manifoldMorseIndex_def, manifoldMorseIndex_def, hfun, hpoint]
  rw [morseIndex_def, morseIndex_def]
  have hquad : hessianQuadraticForm
      (g ∘ (e.symm.toContinuousLinearMap : E' → E)) (e a) =
      (hessianQuadraticForm g (e.symm (e a))).comp e.symm.toLinearMap :=
    e.symm.hessianQuadraticForm_comp g (e a)
  rw [hquad]
  simpa only [ContinuousLinearEquiv.symm_apply_apply, g, a] using
    (QuadraticMap.Equivalent.sigNeg_eq
    ⟨QuadraticMap.isometryEquivOfCompLinearEquiv
      (hessianQuadraticForm g (e.symm (e a))) e.symm.toLinearEquiv⟩).symm

/-- If the preferred-chart Hessian is nondegenerate, the manifold Morse indices of a function and
its negation add to the dimension of the model space. -/
theorem manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
    (h : (hessianQuadraticForm (f ∘ (extChartAt I x).symm)
      (extChartAt I x x)).Nondegenerate) :
    manifoldMorseIndex I (-f) x + manifoldMorseIndex I f x = Module.finrank ℝ E := by
  have hfun : (-f) ∘ (extChartAt I x).symm = -(f ∘ (extChartAt I x).symm) := by
    funext y
    rfl
  rw [manifoldMorseIndex_def, manifoldMorseIndex_def, hfun]
  exact morseIndex_neg_add_morseIndex_eq_finrank h

namespace IsManifoldNondegenerateCriticalPoint

/-- At a nondegenerate critical point, the Morse indices of a function and its negation add to
the dimension of the manifold. -/
theorem manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
    (h : IsManifoldNondegenerateCriticalPoint I f x) :
    manifoldMorseIndex I (-f) x + manifoldMorseIndex I f x = Module.finrank ℝ E := by
  exact TauCeti.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
    (((isManifoldNondegenerateCriticalPoint_iff I).mp h).hessianQuadraticForm_nondegenerate)

/-- If the Morse index of `f` drops by one from a nondegenerate critical point `x` to another one
`y`, then the Morse index of `-f` rises by one from `x` to `y`. -/
theorem manifoldMorseIndex_neg_eq_add_one_of_eq_add_one {y : M}
    (hx : IsManifoldNondegenerateCriticalPoint I f x)
    (hy : IsManifoldNondegenerateCriticalPoint I f y)
    (hxy : manifoldMorseIndex I f x = manifoldMorseIndex I f y + 1) :
    manifoldMorseIndex I (-f) y = manifoldMorseIndex I (-f) x + 1 := by
  have := hx.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  have := hy.manifoldMorseIndex_neg_add_manifoldMorseIndex_eq_finrank
  omega

end IsManifoldNondegenerateCriticalPoint

end TauCeti

end
