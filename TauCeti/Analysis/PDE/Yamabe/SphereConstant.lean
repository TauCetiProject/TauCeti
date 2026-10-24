/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.Volume.Sphere

/-!
# The Yamabe constant of the sphere

Let `|Sⁿ|` be the area of the unit round sphere `Sⁿ ⊆ ℝⁿ⁺¹` (`TauCeti.roundSphereVolume`), its
normalized `n`-dimensional Hausdorff measure. The *Yamabe constant of the sphere* is

`Y(Sⁿ) = n (n - 1) |Sⁿ| ^ (2 / n)`.

For `n > 2` it is the value of the Yamabe quotient `Q(u) = ∫ (aₙ |du|² + Scal u²) / ‖u‖_{pₙ}²` of
the round metric (scalar curvature `n (n - 1)`) at a constant function `u`; it is the sharp
constant of the Euclidean Sobolev inequality `aₙ ∫ |du|² ≥ Y(Sⁿ) ‖u‖_{pₙ}²` and the upper bound for
the Yamabe invariant of every closed `n`-manifold. Neither of these facts is proved here; they are
the reasons for introducing the constant.

## Main declarations

* `TauCeti.Yamabe.sphereYamabeConstant`: the constant `Y(Sⁿ)`, with its positivity for `n > 1`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §2–§3.
-/

public section

noncomputable section

namespace TauCeti.Yamabe

/-- The **Yamabe constant of the sphere**, `Y(Sⁿ) = n (n - 1) |Sⁿ| ^ (2 / n)`, where `|Sⁿ|` is
the area `TauCeti.roundSphereVolume n` of the unit round sphere. -/
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
  have hexp : 2 / (n : ℝ) + ((n : ℝ) - 2) / n = 1 := by
    field_simp
    ring
  rw [sphereYamabeConstant_def, mul_assoc, ← Real.rpow_add (roundSphereVolume_pos n), hexp,
    Real.rpow_one]

end TauCeti.Yamabe
