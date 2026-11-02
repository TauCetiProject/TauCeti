/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Suyama.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Montgomery.Coordinates

/-!
# The native point supplied by Suyama's parametrization

Suyama's parametrization supplies the Montgomery point `(u³/v³, 1)`, where `u = σ² - 5`
and `v = 4σ`. On the monic Weierstrass model its coordinates are `(B u³/v³, B²)`.
The definition `suyamaPoint` bundles this as a native nonsingular point when `2 ≠ 0` and
`B ≠ 0`; ellipticity of the whole model is unnecessary.

The polynomial pair `(u³, v³)` is nonzero and represents the projective `x`-coordinate of
this point. Thus it can serve as the initial representative in Montgomery arithmetic
without computing the affine division `u³/v³`. Both the raw cross-difference statement
and the equality in the projective line are provided.

## References

* P. Zimmermann, *20 years of ECM*, ANTS VII (2006), author's submitted version, §1, p. 3,
  for Suyama's parametrization and its supplied point.
-/

public section

namespace TauCeti.Montgomery

open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K] {σ : K}

/-- The native point supplied by Suyama's parametrization, corresponding to the Montgomery
point `(u³/v³, 1)`. Only `2 ≠ 0` and `B ≠ 0` are needed, even on a singular model. -/
def suyamaPoint (h₂ : (2 : K) ≠ 0) (hB : suyamaB σ ≠ 0) :
    (model (suyamaA σ) (suyamaB σ)).toAffine.Point :=
  .some (suyamaB σ * suyamaX σ) (suyamaB σ ^ 2) (nonsingular_suyama h₂ hB)

/-- Suyama's native point has monic coordinates `(B u³/v³, B²)`. -/
theorem suyamaPoint_def (h₂ : (2 : K) ≠ 0) (hB : suyamaB σ ≠ 0) :
    suyamaPoint h₂ hB = .some (suyamaB σ * suyamaX σ) (suyamaB σ ^ 2)
      (nonsingular_suyama h₂ hB) := (rfl)

/-- The coordinate pair of Suyama's native point uses the Montgomery coordinate `u³/v³`. -/
@[simp]
theorem coordinates_suyamaPoint (h₂ : (2 : K) ≠ 0) (hB : suyamaB σ ≠ 0) :
    coordinates (suyamaA σ) (suyamaB σ) (suyamaPoint h₂ hB) =
      ⟨suyamaB σ * suyamaX σ, suyamaB σ⟩ := by
  rw [suyamaPoint_def, coordinates_some]

/-- If Suyama's `B` is nonzero, the polynomial seed pair `(u³, v³)` is nonzero. -/
theorem suyama_pair_ne_zero (hB : suyamaB σ ≠ 0) :
    (⟨suyamaU σ ^ 3, suyamaV σ ^ 3⟩ : Pair K) ≠ 0 := by
  have hv := suyamaV_ne_zero hB
  exact Pair.ne_zero_iff.mpr (.inr (pow_ne_zero 3 hv))

/-- The polynomial seed pair `(u³, v³)` represents Suyama's native point. -/
theorem cross_coordinates_suyamaPoint (h₂ : (2 : K) ≠ 0) (hB : suyamaB σ ≠ 0) :
    (⟨suyamaU σ ^ 3, suyamaV σ ^ 3⟩ : Pair K).cross
      (coordinates (suyamaA σ) (suyamaB σ) (suyamaPoint h₂ hB)) = 0 := by
  have hv := suyamaV_ne_zero hB
  rw [coordinates_suyamaPoint, Pair.cross_def, suyamaX_def]
  rw [mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 3 hv)]
  exact sub_eq_zero.mpr (mul_comm _ _)

/-- Suyama's polynomial seed `(u³ : v³)` is the projective `x`-coordinate of the supplied
native point. No ellipticity or separate denominator restrictions are required. -/
theorem projectiveX_suyamaPoint (h₂ : (2 : K) ≠ 0) (hB : suyamaB σ ≠ 0) :
    projectiveX (suyamaA σ) hB (suyamaPoint h₂ hB) =
      (⟨suyamaU σ ^ 3, suyamaV σ ^ 3⟩ : Pair K).toProj (suyama_pair_ne_zero hB) := by
  rw [projectiveX_def, Pair.toProj_eq_toProj_iff, Pair.cross_eq_zero_comm]
  exact cross_coordinates_suyamaPoint h₂ hB

end TauCeti.Montgomery
