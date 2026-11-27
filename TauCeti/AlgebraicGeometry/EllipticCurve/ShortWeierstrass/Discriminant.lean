/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Discriminant.Depressed.Basic

import Mathlib.RingTheory.Prime
import TauCeti.RingTheory.MvPolynomial.Discriminant.Depressed.Prime

/-!
# The short Weierstrass cubic discriminant factor

On short Weierstrass cubics `y² = x³ + a x + b`, the coordinate scaling `(x, y) ↦ (t² x, t³ y)`
assigns `(a, b)` weights `(4, 6)` — twice `TauCeti.depressedWeight 3` — and makes the discriminant
factor `TauCeti.weierstrassDiscrFactor R = 4 X₀³ + 27 X₁² = -TauCeti.depressedDiscr R 3` weighted
homogeneous of weight `12` over any commutative ring, and prime over any integral domain `R` with
`(2 : R) ≠ 0` and `(3 : R) ≠ 0`.

For a Weierstrass curve `W` in short normal form (`W.a₁ = W.a₂ = W.a₃ = 0`), Mathlib's full
elliptic-curve discriminant is `W.Δ = -16 * (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2)`
(`WeierstrassCurve.Δ_of_isShortNF` in `Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms`), which
equals `-16` times `TauCeti.weierstrassDiscrFactor R` evaluated at `(W.a₄, W.a₆)`. When `2` is not
a unit (for example over `ℤ`), `-16` is a non-unit, so primality applies to the factor
`TauCeti.weierstrassDiscrFactor R` itself rather than to the full elliptic-curve discriminant `W.Δ`
(which is prime at `(W.a₄, W.a₆)` only after `2` becomes invertible).

## Main definitions

* `TauCeti.weierstrassDiscrFactor`: the Weierstrass cubic discriminant factor `4 X₀³ + 27 X₁²`.

## Main results

* `TauCeti.weierstrassDiscrFactor_def`,
  `TauCeti.weierstrassDiscrFactor_eq_neg_depressedDiscr_three`: definitional identity and
  identification with `-TauCeti.depressedDiscr R 3`.
* `TauCeti.isWeightedHomogeneous_weierstrassDiscrFactor`: weighted homogeneity of weight `12` for
  weights `(4, 6)`.
* `TauCeti.prime_weierstrassDiscrFactor`: primality over any integral domain `R` with `(2 : R) ≠ 0`
  and `(3 : R) ≠ 0`.
-/

public section

namespace TauCeti

/-- The **Weierstrass cubic discriminant factor** `4 X₀³ + 27 X₁²` over `R`, equal to
`-TauCeti.depressedDiscr R 3`. -/
noncomputable def weierstrassDiscrFactor (R : Type*) [CommRing R] : MvPolynomial (Fin 2) R :=
  4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2

/-- Definitional equation for `TauCeti.weierstrassDiscrFactor`. -/
theorem weierstrassDiscrFactor_def (R : Type*) [CommRing R] :
    weierstrassDiscrFactor R = 4 * MvPolynomial.X 0 ^ 3 + 27 * MvPolynomial.X 1 ^ 2 := (rfl)

/-- `TauCeti.weierstrassDiscrFactor R = -TauCeti.depressedDiscr R 3`. -/
theorem weierstrassDiscrFactor_eq_neg_depressedDiscr_three (R : Type*) [CommRing R] :
    weierstrassDiscrFactor R = -depressedDiscr R 3 := by
  rw [weierstrassDiscrFactor_def, depressedDiscr_three]
  ring

/-- The **Weierstrass cubic discriminant factor**
`TauCeti.weierstrassDiscrFactor R = -depressedDiscr R 3` is weighted homogeneous of weight `12` when
`X₀` and `X₁` are given integer weights `4` and `6`. -/
theorem isWeightedHomogeneous_weierstrassDiscrFactor (R : Type*) [CommRing R] :
    (weierstrassDiscrFactor R).IsWeightedHomogeneous ![(4 : ℤ), 6] 12 := by
  have hw : (![(4 : ℤ), 6] : Fin 2 → ℤ) = fun i : Fin 2 ↦ ((i : ℕ) + 2) • (2 : ℤ) :=
    funext (Fin.forall_fin_two.mpr ⟨by decide, by decide⟩)
  rw [weierstrassDiscrFactor_eq_neg_depressedDiscr_three, hw,
    ← MvPolynomial.mem_weightedHomogeneousSubmodule]
  exact Submodule.neg_mem _ (depressedDiscr_mem_smul R 3 (2 : ℤ))

/-- Over an integral domain `R` with `(2 : R) ≠ 0` and `(3 : R) ≠ 0`, the Weierstrass cubic
discriminant factor `TauCeti.weierstrassDiscrFactor R` is prime in `MvPolynomial (Fin 2) R`. -/
theorem prime_weierstrassDiscrFactor {R : Type*} [CommRing R] [IsDomain R]
    (h2 : (2 : R) ≠ 0) (h3 : (3 : R) ≠ 0) :
    Prime (weierstrassDiscrFactor R) := by
  rw [weierstrassDiscrFactor_eq_neg_depressedDiscr_three]
  exact Prime.neg (prime_depressedDiscr_of_three_le h2 (by omega) (by simpa using h3))

end TauCeti
