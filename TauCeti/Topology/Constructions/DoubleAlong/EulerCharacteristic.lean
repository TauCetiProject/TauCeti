/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.ClosedAnnulus
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.ClosedBall
public import TauCeti.Topology.Constructions.DoubleAlong.Annulus
public import TauCeti.Topology.Constructions.DoubleAlong.Disc

/-!
# Euler characteristics of the doubled disc and the doubled annulus

The Euler characteristic of the double of a compact surface along its whole boundary is twice the
Euler characteristic of the surface. This file checks this on the two basic examples, using the
homeomorphisms of `TauCeti.DoubleAlong.discDoubleHomeomorph` and
`TauCeti.DoubleAlong.annulusDoubleHomeomorph`:

* the closed unit disc is contractible, so `χ = 1`, and its double is the Riemann sphere
  `OnePoint ℂ`, so `χ = 2 = 2 · 1`;
* the closed annulus `r₁ ≤ ‖z‖ ≤ r₂` with `0 < r₁` is homeomorphic to `Circle × [r₁, r₂]`
  by polar coordinates (`Complex.closedAnnulusHomeomorph`), so `χ = χ(S¹) · χ([r₁, r₂]) = 0`, and
  for `r₁ < r₂` its double is the torus `Circle × Circle`, so `χ = 0 = 2 · 0`.

In both cases the fixed set of the sheet exchange is the boundary: one circle for the disc
(`TauCeti.DoubleAlong.discDoubleHomeomorph_image_fixed_eq_sphere`) and two circles for the annulus
(`TauCeti.DoubleAlong.annulusDoubleHomeomorph_image_fixed`).

The Euler characteristic is `TauCeti.eulerChar`, defined for spaces of finite CW type. The
Euler characteristics of the disc and the annulus themselves are `TauCeti.eulerChar_closedBall`
and `TauCeti.eulerChar_closedAnnulus`.

## Main declarations

* `TauCeti.DoubleAlong.eulerChar_discDouble`, `TauCeti.DoubleAlong.eulerChar_discDouble_eq_two_mul`:
  the doubled disc has `χ = 2 = 2 · χ(disc)`.
* `TauCeti.DoubleAlong.eulerChar_annulusDouble`,
  `TauCeti.DoubleAlong.eulerChar_annulusDouble_eq_two_mul`: the doubled annulus has
  `χ = 0 = 2 · χ(annulus)`; its finite CW type is `TauCeti.DoubleAlong.finiteCWType_annulusDouble`.

## References

* L. V. Ahlfors and L. Sario, *Riemann Surfaces*, Princeton University Press, 1960, Chapter II,
  the double of a bordered Riemann surface.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the Euler characteristic after Theorem 2.44.
-/

public section

open Complex Metric Set

namespace TauCeti

namespace DoubleAlong

/-! ### The doubled disc -/

/-- The doubled closed disc has finite CW type, being homeomorphic to the Riemann sphere. -/
instance finiteCWType_discDouble : FiniteCWType (DoubleAlong discBoundary) :=
  discDoubleHomeomorph.finiteCWType

/-- **Euler characteristic of the doubled disc.** The closed unit disc doubled along its boundary
circle is the Riemann sphere, with Euler characteristic `2`. -/
@[simp]
theorem eulerChar_discDouble : eulerChar (DoubleAlong discBoundary) = 2 := by
  rw [discDoubleHomeomorph.eulerChar_eq, eulerChar_onePoint, finrank_real_complex]
  norm_num

/-- The Euler characteristic of the doubled disc is twice that of the disc: `2 = 2 · 1`. -/
theorem eulerChar_discDouble_eq_two_mul :
    eulerChar (DoubleAlong discBoundary) = 2 * eulerChar (closedBall (0 : ℂ) 1) := by
  rw [eulerChar_discDouble, eulerChar_closedBall _ zero_le_one, mul_one]

/-! ### The doubled annulus -/

variable {r₁ r₂ : ℝ}

/-- For `0 < r₁ < r₂`, the doubled closed annulus has finite CW type, being homeomorphic to the
torus `Circle × Circle`. -/
theorem finiteCWType_annulusDouble (h₀ : 0 < r₁) (h : r₁ < r₂) :
    FiniteCWType (DoubleAlong (annulusBoundary r₁ r₂)) :=
  (annulusDoubleHomeomorph h₀ h).finiteCWType

/-- **Euler characteristic of the doubled annulus.** For `0 < r₁ < r₂`, the closed annulus
`r₁ ≤ ‖z‖ ≤ r₂` doubled along its two boundary circles is the torus, with Euler characteristic `0`.
The finite CW type of the double is `TauCeti.DoubleAlong.finiteCWType_annulusDouble`. -/
@[simp]
theorem eulerChar_annulusDouble (h₀ : 0 < r₁) (h : r₁ < r₂) :
    haveI := finiteCWType_annulusDouble h₀ h
    eulerChar (DoubleAlong (annulusBoundary r₁ r₂)) = 0 := by
  have := finiteCWType_annulusDouble h₀ h
  rw [(annulusDoubleHomeomorph h₀ h).eulerChar_eq, eulerChar_prod, eulerChar_circle, zero_mul]

/-- For `0 < r₁ < r₂`, the Euler characteristic of the doubled closed annulus is twice that of the
annulus: `0 = 2 · 0`. -/
theorem eulerChar_annulusDouble_eq_two_mul (h₀ : 0 < r₁) (h : r₁ < r₂) :
    haveI := finiteCWType_annulusDouble h₀ h
    eulerChar (DoubleAlong (annulusBoundary r₁ r₂)) = 2 * eulerChar (closedAnnulus r₁ r₂) := by
  rw [eulerChar_annulusDouble h₀ h, eulerChar_closedAnnulus h₀, mul_zero]

end DoubleAlong

end TauCeti
