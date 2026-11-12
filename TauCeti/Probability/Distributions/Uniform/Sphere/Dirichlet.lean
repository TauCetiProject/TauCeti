/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Uniform.Sphere.Basic
public import TauCeti.Probability.Distributions.Dirichlet.Marginal
import TauCeti.Probability.Distributions.Dirichlet.Factorization

/-!
# Squared coordinates of a uniform sphere point

The squared coordinates of a uniform point on a real Euclidean unit sphere have the Dirichlet
law with every concentration parameter equal to one half. Consequently, the sum of squares
over any nonempty proper block of coordinates has a Beta law, with parameters half the sizes
of the block and its complement. In particular, an individual squared coordinate has shapes
`1 / 2` and `(d - 1) / 2` in dimension `d ≥ 2`.

These measure identities describe the magnitudes of sphere coordinates and supply their
integrability and moments through the Dirichlet and Beta APIs. They do not identify the signs
of the coordinates. The joint identity also includes dimension one, where the squared vector
is constantly one, and dimension zero, where both measures vanish.

The construction combines `stdGaussian_map_sphereDirection` with
`gaussianReal_map_sq` and `map_dirichletNormalize_pi_gammaMeasure`: independent Gaussian squares
are Gamma variables with a common rate, and their normalization gives the squared direction.

## References

* K.-T. Fang, S. Kotz, K. W. Ng, *Symmetric Multivariate and Related Distributions*, Chapman and
  Hall, 1990, Chapter 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- The joint law of the squared coordinates of a uniform sphere point is Dirichlet with
all concentrations equal to one half. In dimension zero both measures are zero. -/
@[simp]
theorem map_sq_uniformSphereMeasure :
    (uniformSphereMeasure (EuclideanSpace ℝ ι)).map
        (fun u ↦ WithLp.toLp 2 (fun i ↦ (u.val i) ^ 2)) =
      dirichletMeasure (fun _ : ι ↦ 1 / 2) := by
  classical
  by_cases hι : Nonempty ι
  swap
  · have : IsEmpty ι := not_nonempty_iff.1 hι
    have hzero : uniformSphereMeasure (EuclideanSpace ℝ ι) = 0 := Subsingleton.elim _ _
    rw [hzero, Measure.map_zero, dirichletMeasure_eq_zero_of_invalid (fun h ↦ hι h.1)]
  have : Nonempty ι := hι
  let : NullSingletonClass (gaussianReal 0 1) := nullSingletonClass_gaussianReal one_ne_zero
  let i₀ : ι := Classical.arbitrary ι
  let e : sphere (0 : EuclideanSpace ℝ ι) 1 :=
    ⟨EuclideanSpace.single i₀ 1, by simp⟩
  have hsq : (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map (fun x i ↦ (x i) ^ 2) =
      Measure.pi (fun _ : ι ↦ gammaMeasure (1 / 2) (1 / 2)) := by
    rw [Measure.pi_map_pi (f := fun _ (x : ℝ) ↦ x ^ 2) (fun _ ↦ by fun_prop)]
    simp only [gaussianReal_map_sq, chiSquaredMeasure_eq_gammaMeasure zero_lt_one]
  rw [← stdGaussian_map_sphereDirection e, ← map_pi_eq_stdGaussian,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  calc
    _ = (Measure.pi fun _ : ι ↦ gaussianReal 0 1).map
        (dirichletNormalize ∘ (fun x i ↦ (x i) ^ 2)) := by
      refine Measure.map_congr ?_
      filter_upwards [(Measure.pi fun _ : ι ↦ gaussianReal 0 1).ae_ne 0] with x hx
      have hx' : WithLp.toLp 2 x ≠ (0 : EuclideanSpace ℝ ι) := by
        simpa using hx
      ext i
      simp only [Function.comp_apply, coe_sphereDirection_of_ne_zero e hx',
        NormedSpace.normalize, PiLp.smul_apply, smul_eq_mul, WithLp.ofLp_toLp,
        dirichletNormalize_apply, mul_pow, inv_pow]
      rw [← EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)]
      simp [div_eq_mul_inv, mul_comm]
    _ = _ := by
      rw [← Measure.map_map measurable_dirichletNormalize (by fun_prop), hsq]
      exact map_dirichletNormalize_pi_gammaMeasure (fun _ ↦ by norm_num) (by norm_num)

/-- The squared norm of a nonempty proper coordinate block of a uniform sphere point has a
Beta law whose shapes are half the dimensions of the block and its complement. -/
theorem map_sum_sq_uniformSphereMeasure [DecidableEq ι] {s : Finset ι}
    (hs : s.Nonempty) (hsc : sᶜ.Nonempty) :
    (uniformSphereMeasure (EuclideanSpace ℝ ι)).map (fun u ↦ ∑ i ∈ s, (u.val i) ^ 2) =
      betaMeasure ((s.card : ℝ) / 2) ((sᶜ.card : ℝ) / 2) := by
  have h := congrArg (Measure.map (fun x : EuclideanSpace ℝ ι ↦ ∑ i ∈ s, x i))
    (map_sq_uniformSphereMeasure (ι := ι))
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    map_sum_dirichletMeasure (fun _ ↦ by norm_num) hs hsc] at h
  simpa [Function.comp_def, div_eq_mul_inv] using h

/-- In dimension at least two, a squared coordinate of a uniform sphere point has the
Beta law with shapes `1 / 2` and `(d - 1) / 2`. -/
@[simp]
theorem map_sq_eval_uniformSphereMeasure [Nontrivial ι] (i : ι) :
    (uniformSphereMeasure (EuclideanSpace ℝ ι)).map (fun u ↦ (u.val i) ^ 2) =
      betaMeasure (1 / 2) (((Fintype.card ι : ℝ) - 1) / 2) := by
  classical
  have hsc : ({i} : Finset ι)ᶜ.Nonempty := by
    obtain ⟨j, hj⟩ := exists_ne i
    exact ⟨j, by simpa using hj⟩
  simpa [Finset.card_compl, Nat.cast_sub (Nat.succ_le_of_lt Fintype.card_pos),
    Finset.sum_singleton] using
    map_sum_sq_uniformSphereMeasure (Finset.singleton_nonempty i) hsc

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : Measure Ω}
  {U : Ω → sphere (0 : EuclideanSpace ℝ ι) 1}

/-- Squaring all coordinates of a uniform sphere random vector gives a Dirichlet vector
with all shapes one half. -/
theorem HasLaw.sq_uniformSphereMeasure
    (hU : HasLaw U (uniformSphereMeasure (EuclideanSpace ℝ ι)) P) :
    HasLaw (fun ω ↦ WithLp.toLp 2 (fun i ↦ ((U ω).val i) ^ 2))
      (dirichletMeasure (fun _ : ι ↦ 1 / 2)) P :=
  (HasLaw.mk (by fun_prop) map_sq_uniformSphereMeasure).fun_comp hU

/-- The energy in a nonempty proper coordinate block of a uniform sphere random vector
is Beta distributed with shapes half the block dimensions. -/
theorem HasLaw.sum_sq_uniformSphereMeasure [DecidableEq ι]
    (hU : HasLaw U (uniformSphereMeasure (EuclideanSpace ℝ ι)) P)
    {s : Finset ι} (hs : s.Nonempty) (hsc : sᶜ.Nonempty) :
    HasLaw (fun ω ↦ ∑ i ∈ s, ((U ω).val i) ^ 2)
      (betaMeasure ((s.card : ℝ) / 2) ((sᶜ.card : ℝ) / 2)) P :=
  (HasLaw.mk (by fun_prop) (map_sum_sq_uniformSphereMeasure hs hsc)).fun_comp hU

/-- A squared coordinate of a uniform sphere random vector in dimension at least two is
Beta distributed with shapes `1 / 2` and `(d - 1) / 2`. -/
theorem HasLaw.sq_eval_uniformSphereMeasure [Nontrivial ι]
    (hU : HasLaw U (uniformSphereMeasure (EuclideanSpace ℝ ι)) P) (i : ι) :
    HasLaw (fun ω ↦ ((U ω).val i) ^ 2)
      (betaMeasure (1 / 2) (((Fintype.card ι : ℝ) - 1) / 2)) P :=
  (HasLaw.mk (by fun_prop) (map_sq_eval_uniformSphereMeasure i)).fun_comp hU

end ProbabilityTheory
