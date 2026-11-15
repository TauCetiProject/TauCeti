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
The definition `suyamaPoint` bundles this as a native nonsingular point whenever `B ≠ 0`;
both `2 ≠ 0` and nonvanishing of the coordinate denominators follow automatically from `B ≠ 0`,
and ellipticity of the whole model is unnecessary.

Whenever `suyamaB σ ≠ 0`, `suyamaPoint` is neither infinity nor the distinguished point of
order two `twoTorsionPoint` (so it lies outside the exceptional locus of binary Montgomery
ladder steps), nor does it have order dividing two. The polynomial pair `(u³, v³)` is nonzero
and represents the projective `x`-coordinate of this point without computing the affine
division `u³/v³`, and this projective `x`-coordinate commutes with field embeddings.

## Main definitions

* `TauCeti.Montgomery.suyamaPoint`: the native point `(B u³/v³, B²)` of
  `model (suyamaA σ) (suyamaB σ)` when `suyamaB σ ≠ 0`.

## Main results

* `TauCeti.Montgomery.suyamaPoint_ne_zero`,
  `TauCeti.Montgomery.suyamaPoint_ne_twoTorsionPoint`, and
  `TauCeti.Montgomery.suyamaPoint_add_self_ne_zero`: Suyama's point is neither infinity nor
  `twoTorsionPoint`, and is not killed by `2`.
* `TauCeti.Montgomery.cross_coordinates_suyamaPoint` and
  `TauCeti.Montgomery.projectiveX_suyamaPoint`: the polynomial pair `(u³, v³)` represents the
  projective `x`-coordinate of `suyamaPoint`.
* `TauCeti.Montgomery.mapProjective_projectiveX_suyamaPoint`: the projective `x`-coordinate of
  `suyamaPoint` commutes with field embeddings.

## References

* P. Zimmermann, *20 years of ECM*, ANTS VII (2006), author's submitted version, §1, p. 3,
  for Suyama's parametrization and its supplied point.
-/

public section

namespace TauCeti.Montgomery

open WeierstrassCurve
open scoped LinearAlgebra.Projectivization

variable {K : Type*} [Field K] {σ : K}

/-- The native point supplied by Suyama's parametrization, corresponding to the Montgomery
point `(u³/v³, 1)`. Only `B ≠ 0` is needed, even on a singular model. -/
def suyamaPoint (hB : suyamaB σ ≠ 0) :
    (model (suyamaA σ) (suyamaB σ)).toAffine.Point :=
  .some (suyamaB σ * suyamaX σ) (suyamaB σ ^ 2) (nonsingular_suyama hB)

/-- Suyama's native point has monic coordinates `(B u³/v³, B²)`. -/
theorem suyamaPoint_def (hB : suyamaB σ ≠ 0) :
    suyamaPoint hB = .some (suyamaB σ * suyamaX σ) (suyamaB σ ^ 2)
      (nonsingular_suyama hB) := (rfl)

/-- Suyama's native point is not the point at infinity. -/
@[simp]
theorem suyamaPoint_ne_zero (hB : suyamaB σ ≠ 0) : suyamaPoint hB ≠ 0 :=
  Affine.Point.some_ne_zero _

/-- Suyama's native point is distinct from the distinguished point of order two `(0, 0)`, so it
is non-exceptional as a base point for the binary Montgomery ladder. -/
theorem suyamaPoint_ne_twoTorsionPoint (hB : suyamaB σ ≠ 0) :
    suyamaPoint hB ≠ twoTorsionPoint (suyamaA σ) hB := by
  rw [suyamaPoint_def, Ne, some_eq_twoTorsionPoint_iff hB, mul_eq_zero, not_or]
  exact ⟨hB, suyamaX_ne_zero hB⟩

variable [DecidableEq K] in
/-- Suyama's native point is not killed by `2`: its `y`-coordinate `B²` on the monic model is
nonzero in characteristic different from two. -/
theorem suyamaPoint_add_self_ne_zero (hB : suyamaB σ ≠ 0) :
    suyamaPoint hB + suyamaPoint hB ≠ 0 := by
  intro h
  have hneg : suyamaPoint hB = -suyamaPoint hB := add_eq_zero_iff_eq_neg.mp h
  rw [suyamaPoint_def, Affine.Point.neg_some] at hneg
  have hy : suyamaB σ ^ 2 = -suyamaB σ ^ 2 := by
    simpa [Affine.negY] using (Affine.Point.some.inj hneg).2
  have h₂B : 2 * suyamaB σ ^ 2 = 0 := by linear_combination hy
  exact mul_ne_zero (suyamaB_ne_zero_iff.mp hB).1 (pow_ne_zero 2 hB) h₂B

/-- The coordinate pair of Suyama's native point uses the Montgomery coordinate `u³/v³`. -/
@[simp]
theorem coordinates_suyamaPoint (hB : suyamaB σ ≠ 0) :
    coordinates (suyamaA σ) (suyamaB σ) (suyamaPoint hB) =
      ⟨suyamaB σ * suyamaX σ, suyamaB σ⟩ := by
  rw [suyamaPoint_def, coordinates_some]

/-- If Suyama's `B` is nonzero, the polynomial seed pair `(u³, v³)` is nonzero. -/
theorem suyama_pair_ne_zero (hB : suyamaB σ ≠ 0) :
    (⟨suyamaU σ ^ 3, suyamaV σ ^ 3⟩ : Pair K) ≠ 0 := by
  have hv := suyamaV_ne_zero hB
  exact Pair.ne_zero_iff.mpr (.inr (pow_ne_zero 3 hv))

/-- The polynomial seed pair `(u³, v³)` represents Suyama's native point. -/
theorem cross_coordinates_suyamaPoint (hB : suyamaB σ ≠ 0) :
    (⟨suyamaU σ ^ 3, suyamaV σ ^ 3⟩ : Pair K).cross
      (coordinates (suyamaA σ) (suyamaB σ) (suyamaPoint hB)) = 0 := by
  have hv := suyamaV_ne_zero hB
  rw [coordinates_suyamaPoint, Pair.cross_def, suyamaX_def]
  rw [mul_assoc, div_mul_cancel₀ _ (pow_ne_zero 3 hv)]
  exact sub_eq_zero.mpr (mul_comm _ _)

/-- Suyama's polynomial seed `(u³ : v³)` is the projective `x`-coordinate of the supplied
native point. No ellipticity or separate denominator restrictions are required. -/
theorem projectiveX_suyamaPoint (hB : suyamaB σ ≠ 0) :
    projectiveX (suyamaA σ) hB (suyamaPoint hB) =
      (⟨suyamaU σ ^ 3, suyamaV σ ^ 3⟩ : Pair K).toProj (suyama_pair_ne_zero hB) := by
  rw [projectiveX_def, Pair.toProj_eq_toProj_iff, Pair.cross_eq_zero_comm]
  exact cross_coordinates_suyamaPoint hB

/-- The projective `x`-coordinate of Suyama's native point commutes with field embeddings. -/
theorem mapProjective_projectiveX_suyamaPoint {L : Type*} [Field L] (f : K →+* L)
    (hB : suyamaB σ ≠ 0) (hB' : suyamaB (f σ) ≠ 0) :
    f.mapProjective (projectiveX (suyamaA σ) hB (suyamaPoint hB)) =
      projectiveX (suyamaA (f σ)) hB' (suyamaPoint hB') := by
  rw [projectiveX_suyamaPoint, Pair.mapProjective_toProj, projectiveX_suyamaPoint]
  congr 1
  ext <;> simp [map_ofNat]

end TauCeti.Montgomery
