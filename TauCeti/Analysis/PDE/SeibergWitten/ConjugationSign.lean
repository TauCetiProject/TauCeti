/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import TauCeti.LinearAlgebra.Determinant.Complex.Prod

/-!
# The point-pairing sign of charge conjugation

Let `X` be a closed oriented four-manifold with Betti numbers `b₁` and `b⁺`, and `s` a `Spinᶜ`
structure. After a homotopy through operators of order zero, the gauge-fixed linearization of the
Seiberg–Witten equations splits as the direct sum of the real deformation operator `T` on
imaginary one-forms, with kernel of dimension `b₁` and cokernel of dimension `1 + b⁺`, and the
complex Dirac operator `D`. Charge conjugation negates imaginary forms and acts on spinors by a
conjugate-linear intertwiner `j` of the Dirac operators of `s` and of its conjugate. On the
determinant line `det T ⊗ det D` the transport along `(-1 × j, -1 × j)` is multiplication by the
determinant sign

`ε_det = (-1) ^ (1 + b₁ + b⁺ + ind_ℂ D)`,

relative to a fixed orientation of `det T` and the complex orientations of the two Dirac
determinant lines (`LinearMap.IsComplexPositiveDetLine.exists_detLineCongr_neg_prodCongr`).

The expected dimension of the moduli space is `d = 2 ind_ℂ D - (1 - b₁ + b⁺)`. When `d = 2k`,
the `k` point insertions pull the charge-one point class `μ` back to `-μ` and contribute
`(-1) ^ k`, so the point pairings of `s` and of its conjugate differ by `ε_det (-1) ^ k`. This file
proves that this total sign depends only on the topology of `X`:

`ε_det (-1) ^ k = (-1) ^ ((1 - b₁ + b⁺) / 2)`

(`TauCeti.SeibergWitten.neg_one_pow_mul_neg_one_pow_eq_negOnePow`), and states the resulting
comparison of determinant lines (`TauCeti.SeibergWitten.exists_neg_one_pow_smul_detLineCongr_eq`).
The parity identity alone does not transport determinant lines along the homotopy from the
linearization to `T ⊕ D`; that comparison is separate.

## Main results

* `TauCeti.SeibergWitten.neg_one_pow_mul_neg_one_pow_eq_negOnePow`: if
  `2 (k_D - c_D) - (1 - b₁ + b⁺) = 2k`, then
  `(-1) ^ (b₁ + (1 + b⁺) + (k_D + c_D)) (-1) ^ k = (-1) ^ ((1 - b₁ + b⁺) / 2)`.
* `TauCeti.SeibergWitten.exists_neg_one_pow_smul_detLineCongr_eq`: the transport of
  `det (T ⊕ D)` along `(-1 × j₁, -1 × j₂)`, multiplied by `(-1) ^ k`, carries `x ⊗ z` to
  `(-1) ^ ((1 - b₁ + b⁺) / 2) x ⊗ z'`, for complex positive `z` and `z'`.

## References

* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
-/

public section

open Module TensorProduct Complex LinearMap

namespace TauCeti.SeibergWitten

/-- **The point-pairing sign of charge conjugation.** Let `k_D` and `c_D` be the complex dimensions
of the kernel and cokernel of the Dirac operator, and suppose the expected dimension
`2 (k_D - c_D) - (1 - b₁ + b⁺)` is `2k`. Then the determinant sign
`(-1) ^ (b₁ + (1 + b⁺) + (k_D + c_D))` of charge conjugation times the sign `(-1) ^ k` of `k` point
insertions is `(-1) ^ ((1 - b₁ + b⁺) / 2)`. -/
theorem neg_one_pow_mul_neg_one_pow_eq_negOnePow {b₁ bp kD cD k : ℕ}
    (hd : 2 * ((kD : ℤ) - cD) - (1 - b₁ + bp) = 2 * k) :
    (-1 : ℝ) ^ (b₁ + (1 + bp) + (kD + cD)) * (-1) ^ k =
      (((1 - b₁ + bp : ℤ) / 2).negOnePow : ℝ) := by
  have h2 : (1 - b₁ + bp : ℤ) / 2 = kD - cD - k := by
    rw [show (1 - b₁ + bp : ℤ) = 2 * (kD - cD - k) by linarith, Int.mul_ediv_cancel_left _
      two_ne_zero]
  rw [← pow_add, ← Int.cast_negOnePow_natCast, h2, (Int.negOnePow_eq_iff _ _).2]
  exact ⟨b₁ + kD, by push_cast; linarith⟩

variable {M N P Q P' Q' : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  [AddCommGroup P] [Module ℂ P] [Module ℝ P] [IsScalarTower ℝ ℂ P]
  [AddCommGroup Q] [Module ℂ Q] [Module ℝ Q] [IsScalarTower ℝ ℂ Q]
  [AddCommGroup P'] [Module ℂ P'] [Module ℝ P'] [IsScalarTower ℝ ℂ P']
  [AddCommGroup Q'] [Module ℂ Q'] [Module ℝ Q'] [IsScalarTower ℝ ℂ Q']
  {T : M →ₗ[ℝ] N} [FiniteDimensional ℝ (ker T)] [FiniteDimensional ℝ (N ⧸ range T)]
  {D : P →ₗ[ℂ] Q} [FiniteDimensional ℂ (ker D)] [FiniteDimensional ℂ (Q ⧸ range D)]
  {D' : P' →ₗ[ℂ] Q'} [FiniteDimensional ℂ (ker D')] [FiniteDimensional ℂ (Q' ⧸ range D')]

/-- **Charge conjugation on the split deformation operator.** Let `T` have kernel of dimension
`b₁` and cokernel of dimension `1 + b⁺`, let `j₁` and `j₂` be real isomorphisms anticommuting
with `I` and intertwining the complex-linear maps `D` and `D'`, and suppose
`2 ind_ℂ D - (1 - b₁ + b⁺) = 2k`. Then the transport of `det (T ⊕ D)` to `det (T ⊕ D')` along
`(-1 × j₁, -1 × j₂)`, multiplied by `(-1) ^ k`, carries `x ⊗ z`, for `z` complex positive, to
`(-1) ^ ((1 - b₁ + b⁺) / 2)` times `x ⊗ z'` for a complex positive `z'`. -/
theorem exists_neg_one_pow_smul_detLineCongr_eq (j₁ : P ≃ₗ[ℝ] P') (j₂ : Q ≃ₗ[ℝ] Q')
    (hj : D'.restrictScalars ℝ ∘ₗ j₁.toLinearMap = j₂.toLinearMap ∘ₗ D.restrictScalars ℝ)
    (hj₁ : ∀ x, j₁ (I • x) = -(I • j₁ x)) (hj₂ : ∀ y, j₂ (I • y) = -(I • j₂ y))
    {b₁ bp k : ℕ} (hT₁ : finrank ℝ (ker T) = b₁) (hT₂ : finrank ℝ (N ⧸ range T) = 1 + bp)
    (hd : 2 * ((finrank ℂ (ker D) : ℤ) - finrank ℂ (Q ⧸ range D)) - (1 - b₁ + bp) = 2 * k)
    (x : T.detLine) {z : (D.restrictScalars ℝ).detLine} (hz : D.IsComplexPositiveDetLine z) :
    ∃ z', D'.IsComplexPositiveDetLine z' ∧
      (-1 : ℝ) ^ k • (T.prodMap (D.restrictScalars ℝ)).detLineCongr
          ((LinearEquiv.neg ℝ).prodCongr j₁) ((LinearEquiv.neg ℝ).prodCongr j₂)
          (prodMap_comp_prodCongr_eq_of_comp_eq (comp_neg_eq_neg_comp T) hj)
          ((detLineProdMapEquiv T (D.restrictScalars ℝ)).symm (x ⊗ₜ z)) =
        (((1 - b₁ + bp : ℤ) / 2).negOnePow : ℝ) •
          (detLineProdMapEquiv T (D'.restrictScalars ℝ)).symm (x ⊗ₜ z') := by
  obtain ⟨z', hz', h⟩ := hz.exists_detLineCongr_neg_prodCongr T j₁ j₂ hj hj₁ hj₂ x
  refine ⟨z', hz', (congrArg ((-1 : ℝ) ^ k • ·) h).trans ?_⟩
  rw [smul_smul]
  congr 1
  rw [hT₁, hT₂, mul_comm ((-1 : ℝ) ^ k)]
  exact neg_one_pow_mul_neg_one_pow_eq_negOnePow hd

end TauCeti.SeibergWitten
