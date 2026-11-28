/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PolynomialLaw.Determinant

/-!
# `D(1 + r r') = D(1 + r' r)`

For a determinant `D` on an `A`-algebra `R` over an additively cancellative semiring `A`,
`D(1 + r r') = D(1 + r' r)` for any `r, r' ∈ R`, the analogue of Mathlib's
`Matrix.det_one_add_mul_comm`.

This follows from the cyclicity of each characteristic coefficient
(`TauCeti.Determinant.charCoeff_mul_comm`) and the evaluation formula for a scalar translate
(`TauCeti.Determinant.map_smul_add_algebraMap`).

## Main declarations

* `TauCeti.Determinant.map_one_add_mul_comm`: `D(1 + r r') = D(1 + r' r)`.

## References

* [G. Chenevier, *The p-adic analytic space of pseudocharacters of a profinite group and
  pseudorepresentations over arbitrary rings*, Lemma 1.12(i)](https://arxiv.org/abs/0809.0415)
-/

public section

noncomputable section

universe u

namespace TauCeti

namespace Determinant

variable {A : Type u} [CommSemiring A] [IsCancelAdd A] {R : Type*} [Semiring R] [Algebra A R]
  {d : ℕ} (D : Determinant A R d)

/-- For a determinant over an additively cancellative semiring,
`D(1 + r r') = D(1 + r' r)` for any `r, r'`. -/
theorem map_one_add_mul_comm (r r' : R) : D (1 + r * r') = D (1 + r' * r) := by
  have h (x : R) : D (1 + x) = ∑ i ∈ Finset.range (d + 1), D.charCoeff i x := by
    simpa only [one_smul, _root_.map_one, one_pow, mul_one, one_mul, add_comm (1 : R)]
      using D.map_smul_add_algebraMap 1 1 x
  simp only [h, D.charCoeff_mul_comm]

end Determinant

end TauCeti
