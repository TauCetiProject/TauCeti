/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.Volume.Sphere

/-!
# The area of the round sphere and the Yamabe constant of the sphere

The *area* `|Sⁿ|` of the unit round sphere `Sⁿ ⊆ ℝⁿ⁺¹` is its normalized `n`-dimensional
Hausdorff measure `μHE[n]`, not the ambient Lebesgue measure of the sphere (which vanishes). It is
finite and positive, with the classical value

`|Sⁿ| = 2 π ^ ((n + 1) / 2) / Γ((n + 1) / 2)`.

The *Yamabe constant of the sphere* is

`Y(Sⁿ) = n (n - 1) |Sⁿ| ^ (2 / n)`.

For `n > 2` it is the value of the Yamabe quotient `Q(u) = ∫ (aₙ |du|² + Scal u²) / ‖u‖_{pₙ}²` of
the round metric (scalar curvature `n (n - 1)`) at a constant function `u`; it is the sharp
constant of the Euclidean Sobolev inequality `aₙ ∫ |du|² ≥ Y(Sⁿ) ‖u‖_{pₙ}²` and the upper bound for
the Yamabe invariant of every closed `n`-manifold. Neither of these facts is proved here; they are
the reasons for introducing the constant.

## Main declarations

* `TauCeti.Yamabe.roundSphereVolume`: the area `|Sⁿ|` of the unit round sphere.
* `TauCeti.Yamabe.euclideanHausdorffMeasure_sphere_eq_ofReal_roundSphereVolume`: the unit sphere
  of every real inner product space of dimension `n + 1` has `n`-dimensional Hausdorff measure
  `|Sⁿ|`; in particular this measure is finite.
* `TauCeti.Yamabe.roundSphereVolume_eq_two_mul_pi_rpow_div_Gamma`, `roundSphereVolume_pos`: the
  value and positivity of `|Sⁿ|`.
* `TauCeti.Yamabe.sphereYamabeConstant`: the constant `Y(Sⁿ)`, with its positivity for `n > 1`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2–§3.
-/

public section

noncomputable section

namespace TauCeti.Yamabe

open MeasureTheory Metric Module Real

/-- The area `|Sⁿ|` of the unit round sphere `Sⁿ ⊆ ℝⁿ⁺¹`: the normalized `n`-dimensional Hausdorff
measure of the unit sphere of `EuclideanSpace ℝ (Fin (n + 1))`. -/
def roundSphereVolume (n : ℕ) : ℝ :=
  (μHE[n] (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).toReal

/-- Unfolding lemma for `TauCeti.Yamabe.roundSphereVolume`. -/
theorem roundSphereVolume_def (n : ℕ) :
    roundSphereVolume n = (μHE[n] (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).toReal :=
  (rfl)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]

/-- The `n`-dimensional Hausdorff measure of the unit sphere of an `(n + 1)`-dimensional real
inner product space, in terms of the Gamma function. -/
private theorem euclideanHausdorffMeasure_sphere_eq_ofReal_Gamma {n : ℕ}
    (hE : finrank ℝ E = n + 1) :
    μHE[n] (sphere (0 : E) 1) =
      ENNReal.ofReal (2 * π ^ (((n : ℝ) + 1) / 2) / Gamma (((n : ℝ) + 1) / 2)) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  have h := euclideanHausdorffMeasure_sphere_zero_one_eq_ofReal (E := E)
  rw [hE, Nat.add_sub_cancel] at h
  exact_mod_cast h

/-- **The area of the unit round sphere**: `|Sⁿ| = 2 π ^ ((n + 1) / 2) / Γ((n + 1) / 2)`. -/
theorem roundSphereVolume_eq_two_mul_pi_rpow_div_Gamma (n : ℕ) :
    roundSphereVolume n = 2 * π ^ (((n : ℝ) + 1) / 2) / Gamma (((n : ℝ) + 1) / 2) := by
  rw [roundSphereVolume_def, euclideanHausdorffMeasure_sphere_eq_ofReal_Gamma
    finrank_euclideanSpace_fin, ENNReal.toReal_ofReal (by positivity)]

/-- The unit round sphere has positive area. -/
theorem roundSphereVolume_pos (n : ℕ) : 0 < roundSphereVolume n := by
  rw [roundSphereVolume_eq_two_mul_pi_rpow_div_Gamma]
  positivity

/-- The unit sphere of every real inner product space of dimension `n + 1` has normalized
`n`-dimensional Hausdorff measure `|Sⁿ|`. In particular, this measure is finite. -/
theorem euclideanHausdorffMeasure_sphere_eq_ofReal_roundSphereVolume {n : ℕ}
    (hE : finrank ℝ E = n + 1) :
    μHE[n] (sphere (0 : E) 1) = ENNReal.ofReal (roundSphereVolume n) := by
  rw [euclideanHausdorffMeasure_sphere_eq_ofReal_Gamma hE,
    roundSphereVolume_eq_two_mul_pi_rpow_div_Gamma]

/-- The **Yamabe constant of the sphere**, `Y(Sⁿ) = n (n - 1) |Sⁿ| ^ (2 / n)`, where `|Sⁿ|` is
the area `TauCeti.Yamabe.roundSphereVolume n` of the unit round sphere. -/
def sphereYamabeConstant (n : ℕ) : ℝ :=
  n * (n - 1) * roundSphereVolume n ^ (2 / (n : ℝ))

/-- Unfolding lemma for `TauCeti.Yamabe.sphereYamabeConstant`. -/
theorem sphereYamabeConstant_def (n : ℕ) :
    sphereYamabeConstant n = n * (n - 1) * roundSphereVolume n ^ (2 / (n : ℝ)) :=
  (rfl)

/-- The Yamabe constant of the sphere is positive in every dimension `n > 1`. -/
theorem sphereYamabeConstant_pos {n : ℕ} (hn : 1 < n) : 0 < sphereYamabeConstant n := by
  have h : (1 : ℝ) < n := by exact_mod_cast hn
  have := roundSphereVolume_pos n
  rw [sphereYamabeConstant_def]
  exact mul_pos (mul_pos (by linarith) (by linarith)) (by positivity)

/-- In dimension `n ≠ 0`, `Y(Sⁿ) |Sⁿ| ^ ((n - 2) / n) = n (n - 1) |Sⁿ|`. For `n > 2` the exponent
`(n - 2) / n` is `2 / pₙ`, with `pₙ = 2 n / (n - 2)`. -/
theorem sphereYamabeConstant_mul_roundSphereVolume_rpow {n : ℕ} (hn : n ≠ 0) :
    sphereYamabeConstant n * roundSphereVolume n ^ (((n : ℝ) - 2) / n) =
      n * (n - 1) * roundSphereVolume n := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  rw [sphereYamabeConstant_def, mul_assoc, ← Real.rpow_add (roundSphereVolume_pos n),
    show 2 / (n : ℝ) + ((n : ℝ) - 2) / n = 1 by field_simp; ring, Real.rpow_one]

end TauCeti.Yamabe
