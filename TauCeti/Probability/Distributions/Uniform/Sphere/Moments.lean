/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Sphere.Basic
public import TauCeti.Probability.Moments.Covariance

/-!
# Second moments of the uniform sphere law

The uniform law on the unit sphere in dimension `d > 0` has embedded covariance equal to
`1 / d` times the inner product. Thus its covariance matrix in orthonormal coordinates is
`I / d`, and the variance of projection onto a vector `u` is `‖u‖ ^ 2 / d`.

The embedding is bounded, so all its `Lᵖ` norms, including `L∞`, are finite. Together with the
vanishing mean, the covariance formula also evaluates the mixed second moments of linear
observables. These formulas describe the isotropic second moments without choosing coordinates.

## References

* R. J. Muirhead, *Aspects of Multivariate Statistical Theory*, Wiley, 1982, section 1.5.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Module
open scoped ENNReal RealInnerProductSpace

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- The unit-sphere embedding has every finite moment and is essentially bounded. -/
@[simp]
theorem memLp_coe_uniformSphereMeasure (p : ℝ≥0∞) :
    MemLp ((↑) : sphere (0 : E) 1 → E) p (uniformSphereMeasure E) := by
  exact MemLp.of_bound (by fun_prop) 1 (by filter_upwards with x; simp)

/-- The covariance of the embedded uniform sphere law is the inner product divided by the
dimension. -/
@[simp]
theorem covarianceBilin_map_coe_uniformSphereMeasure :
    covarianceBilin ((uniformSphereMeasure E).map ((↑) : sphere (0 : E) 1 → E)) =
      (1 / (finrank ℝ E : ℝ)) • innerSL ℝ := by
  have hinv (f : E ≃ₗᵢ[ℝ] E) :
      ((uniformSphereMeasure E).map ((↑) : sphere (0 : E) 1 → E)).map f =
        (uniformSphereMeasure E).map ((↑) : sphere (0 : E) 1 → E) := by
    let g : sphere (0 : E) 1 → sphere (0 : E) 1 :=
      Subtype.map f (fun x hx ↦ by simpa using hx)
    have hg : Measurable g := f.continuous.measurable.subtype_map _
    rw [Measure.map_map (by fun_prop) measurable_subtype_coe]
    calc
      _ = ((uniformSphereMeasure E).map g).map ((↑) : sphere (0 : E) 1 → E) := by
        rw [Measure.map_map measurable_subtype_coe hg]
        rfl
      _ = _ := by rw [f.map_uniformSphereMeasure]
  rw [covarianceBilin_eq_smul_innerSL hinv,
    integral_map measurable_subtype_coe.aemeasurable (by fun_prop)]
  simp

/-- The covariance of two linear observables of a uniform unit vector is their inner product
divided by the dimension. -/
@[simp]
theorem covariance_inner_uniformSphereMeasure (u v : E) :
    cov[fun x : sphere (0 : E) 1 ↦ ⟪u, (x : E)⟫,
      fun x : sphere (0 : E) 1 ↦ ⟪v, (x : E)⟫; uniformSphereMeasure E] =
      ⟪u, v⟫ / (finrank ℝ E : ℝ) := by
  have hLp : MemLp id 2 ((uniformSphereMeasure E).map ((↑) : sphere (0 : E) 1 → E)) :=
    (memLp_map_measure_iff (by fun_prop) (by fun_prop)).2
      (memLp_coe_uniformSphereMeasure 2)
  have h := congrArg (fun B ↦ B u v) (covarianceBilin_map_coe_uniformSphereMeasure (E := E))
  rw [covarianceBilin_apply_eq_cov hLp,
    covariance_map (by fun_prop) (by fun_prop) (by fun_prop)] at h
  -- The real-linear view of the conjugate-linear `innerSL` needs a typed evaluation lemma.
  have hinner : (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) u v = ⟪u, v⟫ :=
    innerSL_apply_apply (𝕜 := ℝ) u v
  simpa only [Function.comp_def, smul_apply, smul_eq_mul, hinner,
    one_div, mul_one, mul_comm, div_eq_mul_inv] using h

/-- The mixed second moment of two linear observables of a uniform unit vector is their inner
product divided by the dimension. -/
@[simp]
theorem integral_inner_mul_inner_uniformSphereMeasure (u v : E) :
    ∫ x : sphere (0 : E) 1, ⟪u, (x : E)⟫ * ⟪v, (x : E)⟫ ∂uniformSphereMeasure E =
      ⟪u, v⟫ / (finrank ℝ E : ℝ) := by
  have hmean (w : E) : ∫ x : sphere (0 : E) 1, ⟪w, (x : E)⟫ ∂uniformSphereMeasure E = 0 := by
    rw [integral_inner ((memLp_coe_uniformSphereMeasure 1).integrable le_rfl),
      integral_coe_uniformSphereMeasure, inner_zero_right]
  have h := covariance_inner_uniformSphereMeasure u v
  rwa [covariance_eq_sub ((memLp_coe_uniformSphereMeasure 2).const_inner u)
    ((memLp_coe_uniformSphereMeasure 2).const_inner v), hmean u, hmean v,
    mul_zero, sub_zero] at h

/-- The variance of a linear observable of a uniform unit vector is its squared norm divided
by the dimension. -/
@[simp]
theorem variance_inner_uniformSphereMeasure (u : E) :
    Var[fun x : sphere (0 : E) 1 ↦ ⟪u, (x : E)⟫; uniformSphereMeasure E] =
      ‖u‖ ^ 2 / (finrank ℝ E : ℝ) := by
  rw [← covariance_self (by fun_prop), covariance_inner_uniformSphereMeasure,
    real_inner_self_eq_norm_sq]

/-- The covariance matrix of an embedded uniform unit vector is the identity matrix divided
by the number of coordinates. -/
@[simp]
theorem covMatrix_map_coe_uniformSphereMeasure {ι : Type*} [Fintype ι] [DecidableEq ι]
    [Nonempty ι] :
    covMatrix ((uniformSphereMeasure (EuclideanSpace ℝ ι)).map
      ((↑) : sphere (0 : EuclideanSpace ℝ ι) 1 → EuclideanSpace ℝ ι)) =
      (1 / (Fintype.card ι : ℝ)) • (1 : Matrix ι ι ℝ) := by
  classical
  ext i j
  rw [covMatrix_apply, covariance_map (by fun_prop) (by fun_prop) (by fun_prop)]
  have h := covariance_inner_uniformSphereMeasure (EuclideanSpace.single i (1 : ℝ))
    (EuclideanSpace.single j (1 : ℝ))
  simpa [EuclideanSpace.inner_single_left, Function.comp_def, Matrix.one_apply,
    div_eq_mul_inv, mul_comm] using h

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
  [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → sphere (0 : E) 1}

/-- Linear observables of a uniform random unit vector have covariance equal to their inner
product divided by the dimension. -/
theorem HasLaw.covariance_inner_uniformSphereMeasure
    (hX : HasLaw X (uniformSphereMeasure E) P) (u v : E) :
    cov[fun ω ↦ ⟪u, (X ω : E)⟫, fun ω ↦ ⟪v, (X ω : E)⟫; P] =
      ⟪u, v⟫ / (finrank ℝ E : ℝ) := by
  rw [hX.covariance_fun_comp (f := fun x : sphere (0 : E) 1 ↦ ⟪u, (x : E)⟫)
    (g := fun x : sphere (0 : E) 1 ↦ ⟪v, (x : E)⟫) (by fun_prop) (by fun_prop),
    TauCeti.Probability.covariance_inner_uniformSphereMeasure]

end ProbabilityTheory
