/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz
public import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Surface measure of Lipschitz graphs

This file specializes the injective Lipschitz area formula to graphs in an `L²` product.  For a
map `f : E → F`, `normalGraph f` parametrizes its graph by `x ↦ (f x, x)`.  The second
coordinate makes this parametrization injective without any hypothesis on `f`.

For a Lipschitz map, integration over the graph with normalized Euclidean Hausdorff measure is
therefore integration over the parameter space against the geometric Jacobian of the graph map.
The unweighted form computes the surface measure of every measurable graph patch.  This is the
chart formula used when boundary traces are assembled from Lipschitz graph charts.

## Main declarations

* `TauCeti.normalGraph`: the graph parametrization into `WithLp 2 (F × E)`.
* `ContinuousLinearMap.normalGraphL`: the corresponding construction for continuous linear maps.
* `LipschitzWith.lintegral_normalGraph_image_eq_lintegral_normDet_fderiv_mul`: the weighted
  graph area formula.
* `LipschitzWith.lintegral_normDet_fderiv_normalGraph_eq_euclideanHausdorffMeasure_image`: the
  surface-measure formula for a graph patch.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §8.
* L. C. Evans and R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, §3.3.
-/

public section

noncomputable section

open Function MeasureTheory Module Set
open scoped ENNReal NNReal

namespace TauCeti

variable {E F : Type*}

/-- The graph parametrization `x ↦ (f x, x)` into the `L²` product `WithLp 2 (F × E)`.
The ordering puts a scalar-valued function in the normal coordinate used by Lipschitz boundary
charts. -/
def normalGraph (f : E → F) (x : E) : WithLp 2 (F × E) :=
  WithLp.toLp 2 (f x, x)

/-- The graph parametrization written as an `L²` pair. -/
@[simp]
theorem normalGraph_apply (f : E → F) (x : E) :
    normalGraph f x = WithLp.toLp 2 (f x, x) := by
  simp [normalGraph]

/-- A graph parametrization is injective, since its second coordinate is the parameter. -/
theorem normalGraph_injective (f : E → F) : Injective (normalGraph f) := by
  intro x y h
  simpa using congrArg WithLp.snd h

/-- A restricted graph is exactly the set of `L²` pairs whose tangential coordinate lies in the
parameter set and whose normal coordinate is the function value. -/
theorem image_normalGraph (f : E → F) (s : Set E) :
    normalGraph f '' s = {z | z.snd ∈ s ∧ z.fst = f z.snd} := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp [hx]
  · intro hz
    refine ⟨z.snd, hz.1, ?_⟩
    exact (WithLp.ext_iff 2).2 (Prod.ext hz.2.symm rfl)

/-- The range of the graph parametrization is the graph relation in the `L²` product. -/
theorem range_normalGraph (f : E → F) :
    range (normalGraph f) = {z | z.fst = f z.snd} := by
  rw [← image_univ, image_normalGraph]
  simp only [mem_univ, true_and]

section Topology

variable [TopologicalSpace E] [TopologicalSpace F]

/-- The graph parametrization is continuous when the function is continuous. -/
theorem _root_.Continuous.normalGraph {f : E → F} (hf : Continuous f) :
    Continuous (normalGraph f) :=
  (WithLp.prod_continuous_toLp 2 F E).comp (hf.prodMk continuous_id)

end Topology

section Normed

variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- A Lipschitz map has a Lipschitz graph parametrization.  The displayed constant comes from
the comparison between the max product metric and the `L²` product metric. -/
theorem _root_.LipschitzWith.normalGraph {K : ℝ≥0} {f : E → F} (hf : LipschitzWith K f) :
    LipschitzWith
      (((2 : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal) * max K 1) (normalGraph f) :=
  (WithLp.prod_lipschitzWith_toLp 2 F E).comp (hf.prodMk LipschitzWith.id)

end Normed

section Linear

variable [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The continuous linear graph map associated to `A : E →L[ℝ] F`. -/
def _root_.ContinuousLinearMap.normalGraphL (A : E →L[ℝ] F) : E →L[ℝ] WithLp 2 (F × E) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ F E).symm.toContinuousLinearMap ∘L
    A.prod (ContinuousLinearMap.id ℝ E)

/-- The continuous linear graph map acts by `x ↦ (A x, x)`. -/
@[simp]
theorem _root_.ContinuousLinearMap.normalGraphL_apply (A : E →L[ℝ] F) (x : E) :
    A.normalGraphL x = normalGraph A x := by
  simp [ContinuousLinearMap.normalGraphL, normalGraph]

/-- The derivative of a graph parametrization is the graph of the derivative. -/
theorem _root_.HasFDerivAt.normalGraph {f : E → F} {f' : E →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f f' x) : HasFDerivAt (normalGraph f) f'.normalGraphL x := by
  rw [funext (normalGraph_apply f)]
  convert (((WithLp.prodContinuousLinearEquiv 2 ℝ F E).symm :
    (F × E) →L[ℝ] WithLp 2 (F × E)).hasFDerivAt.comp x
      (hf.prodMk (hasFDerivAt_id x))) using 1 <;>
    simp [ContinuousLinearMap.normalGraphL, Function.comp_def]

/-- At a differentiability point, the Fréchet derivative of a graph parametrization is the
continuous linear graph of the derivative. -/
theorem _root_.DifferentiableAt.fderiv_normalGraph {f : E → F} {x : E}
    (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (normalGraph f) x = (fderiv ℝ f x).normalGraphL :=
  hf.hasFDerivAt.normalGraph.fderiv

end Linear

section AreaFormula

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  {K : ℝ≥0} {f : E → F} {s : Set E}

/-- **Weighted area formula for a Lipschitz graph.** Integration over a measurable graph patch
against normalized `dim E`-dimensional Hausdorff measure equals integration over its parameter
set against the graph Jacobian.  The weight need not be measurable. -/
theorem _root_.LipschitzWith.lintegral_normalGraph_image_eq_lintegral_normDet_fderiv_mul
    (hf : LipschitzWith K f)
    (hs : MeasurableSet s) (g : WithLp 2 (F × E) → ℝ≥0∞) :
    ∫⁻ z in normalGraph f '' s, g z ∂μHE[finrank ℝ E] =
      ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ (normalGraph f) x).normDet *
        g (normalGraph f x) := by
  exact hf.normalGraph.lintegral_image_eq_lintegral_normDet_fderiv_mul hs
    (normalGraph_injective f).injOn g

/-- **Surface measure of a Lipschitz graph.** The normalized `dim E`-dimensional Hausdorff
measure of a measurable graph patch is the integral of the geometric Jacobian of its graph
parametrization. -/
theorem _root_.LipschitzWith.lintegral_normDet_fderiv_normalGraph_eq_euclideanHausdorffMeasure_image
    (hf : LipschitzWith K f)
    (hs : MeasurableSet s) :
    ∫⁻ x in s, ENNReal.ofReal (fderiv ℝ (normalGraph f) x).normDet =
      μHE[finrank ℝ E] (normalGraph f '' s) :=
  hf.normalGraph.lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image hs
    (normalGraph_injective f).injOn

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- Projection to the parameter space shows that the surface measure of a graph patch is at
least the Lebesgue measure of its parameter set.  No measurability hypothesis on the set is
needed. -/
theorem volume_le_euclideanHausdorffMeasure_normalGraph_image (f : E → F) (s : Set E) :
    volume s ≤ μHE[finrank ℝ E] (normalGraph f '' s) := by
  have hproj : LipschitzWith 1 (WithLp.snd : WithLp 2 (F × E) → E) :=
    LipschitzWith.of_edist_le WithLp.edist_snd_le
  have h := hproj.lipschitzOnWith.euclideanHausdorffMeasure_image_le
    (s := normalGraph f '' s) (finrank ℝ E)
  have himage : WithLp.snd '' (normalGraph f '' s) = s :=
    LeftInverse.image_image (g := WithLp.snd) (f := normalGraph f) (fun _ ↦ rfl) s
  rw [himage, InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at h
  simpa using h

omit [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] in
/-- A Lipschitz graph has locally finite surface measure whenever its parameter set has finite
volume, with an explicit bound in terms of the graph parametrization's Lipschitz constant. -/
theorem _root_.LipschitzWith.euclideanHausdorffMeasure_normalGraph_image_le
    (hf : LipschitzWith K f) (s : Set E) :
    μHE[finrank ℝ E] (normalGraph f '' s) ≤
      ((((2 : ℝ≥0) ^ (1 / (2 : ℝ≥0∞)).toReal) * max K 1 : ℝ≥0) : ℝ≥0∞) ^
        finrank ℝ E * volume s := by
  simpa only [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] using
    hf.normalGraph.lipschitzOnWith.euclideanHausdorffMeasure_image_le (finrank ℝ E)

end AreaFormula

end TauCeti

end
