/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Complex.LinearMap
public import TauCeti.LinearAlgebra.Determinant.DirectSum

/-!
# Conjugation on the determinant line of a real operator plus a complex operator

Let `T : M → N` be a real-linear map and `D : P → Q` a complex-linear map, both with
finite-dimensional kernel and cokernel, and consider the direct sum `T ⊕ D`, a real-linear map
`M × P → N × Q`. Its determinant line is `det T ⊗ det D` (`LinearMap.detLineProdMapEquiv`). Let
`D' : P' → Q'` be a second complex-linear map and `j₁ : P → P'`, `j₂ : Q → Q'` real isomorphisms
which anticommute with `I` and intertwine `D` with `D'`. Transporting `det (T ⊕ D)` to
`det (T ⊕ D')` along the commuting square `(-1 × j₁, -1 × j₂)` splits, by the naturality of the
direct sum isomorphism (`LinearMap.detLineProdMapEquiv_detLineCongr_prodCongr`), into the
transport of `det T` along `(-1, -1)`, which is multiplication by
`(-1) ^ (dim ker T + dim coker T)` (`LinearMap.detLineCongr_neg_apply`), and the transport of
`det D` along `(j₁, j₂)`, which carries a complex positive element to `(-1) ^ (k + c)` times a
complex positive element, `k` and `c` being the complex dimensions of the kernel and cokernel of
`D` (`LinearMap.IsComplexPositiveDetLine.neg_one_pow_smul_detLineCongr`). So an element
`x ⊗ z` with `z` complex positive is carried to

`(-1) ^ (dim ker T + dim coker T + k + c) • x ⊗ z'`

with `z'` complex positive for `D'`
(`LinearMap.IsComplexPositiveDetLine.exists_detLineCongr_neg_prodCongr`).

This is the linear algebra of the determinant sign of charge conjugation in Seiberg–Witten
theory. After a homotopy through operators of order zero, the gauge-fixed linearization of the
Seiberg–Witten equations at a reducible configuration is the direct sum of the real deformation
operator `T = (-2 d*, d⁺)` on imaginary one-forms and the complex Dirac operator `D`. Charge
conjugation negates imaginary forms and acts on spinors by the quaternionic structure, a
conjugate-linear isomorphism intertwining the Dirac operators of a `Spinᶜ` structure and of its
conjugate. With `dim ker T = b₁` and `dim coker T = 1 + b⁺`, the sign is
`ε_det = (-1) ^ (1 + b₁ + b⁺ + ind_ℂ D)`.

The kernel and cokernel of the underlying real-linear map of `D` are finite-dimensional over `ℝ`
as soon as those of `D` are over `ℂ` (`LinearMap.finite_ker_restrictScalars`,
`LinearMap.finite_quotient_range_restrictScalars`).

## Main results

* `LinearMap.IsComplexPositiveDetLine.exists_detLineCongr_neg_prodCongr`: the transport of
  `det (T ⊕ D)` along `(-1 × j₁, -1 × j₂)` multiplies `x ⊗ z`, for `z` complex positive, by
  `(-1) ^ (dim ker T + dim coker T + k + c)`, up to replacing `z` by a complex positive element of
  `det D'`.

## References

* C. H. Taubes, *The Seiberg–Witten and Gromov invariants*, Math. Res. Lett. 2 (1995), 221–238.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996.
-/

public section

noncomputable section

open Module TensorProduct Complex

namespace LinearMap

open TauCeti

variable {M N P Q P' Q' : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
  [AddCommGroup P] [Module ℂ P] [Module ℝ P] [IsScalarTower ℝ ℂ P]
  [AddCommGroup Q] [Module ℂ Q] [Module ℝ Q] [IsScalarTower ℝ ℂ Q]
  [AddCommGroup P'] [Module ℂ P'] [Module ℝ P'] [IsScalarTower ℝ ℂ P']
  [AddCommGroup Q'] [Module ℂ Q'] [Module ℝ Q'] [IsScalarTower ℝ ℂ Q']
  (T : M →ₗ[ℝ] N) [FiniteDimensional ℝ (ker T)] [FiniteDimensional ℝ (N ⧸ range T)]
  {D : P →ₗ[ℂ] Q} [FiniteDimensional ℂ (ker D)] [FiniteDimensional ℂ (Q ⧸ range D)]
  {D' : P' →ₗ[ℂ] Q'} [FiniteDimensional ℂ (ker D')] [FiniteDimensional ℂ (Q' ⧸ range D')]
  (j₁ : P ≃ₗ[ℝ] P') (j₂ : Q ≃ₗ[ℝ] Q')
  (hj : D'.restrictScalars ℝ ∘ₗ j₁.toLinearMap = j₂.toLinearMap ∘ₗ D.restrictScalars ℝ)

/-- **The determinant sign of a conjugation on a real plus complex operator.** Let `j₁` and `j₂`
be real isomorphisms anticommuting with `I` and intertwining the complex-linear maps `D` and
`D'`. The transport of `det (T ⊕ D)` to `det (T ⊕ D')` along `(-1 × j₁, -1 × j₂)` carries the
element `x ⊗ z` of `det T ⊗ det D`, for `z` complex positive, to
`(-1) ^ (dim ker T + dim coker T + k + c)` times `x ⊗ z'` for a complex positive `z'`, where `k`
and `c` are the complex dimensions of the kernel and cokernel of `D`. Both elements are read
through `LinearMap.detLineProdMapEquiv`. -/
theorem IsComplexPositiveDetLine.exists_detLineCongr_neg_prodCongr
    (hj₁ : ∀ x, j₁ (I • x) = -(I • j₁ x)) (hj₂ : ∀ y, j₂ (I • y) = -(I • j₂ y))
    (x : T.detLine) {z : (D.restrictScalars ℝ).detLine} (hz : D.IsComplexPositiveDetLine z) :
    ∃ z', D'.IsComplexPositiveDetLine z' ∧
      (T.prodMap (D.restrictScalars ℝ)).detLineCongr ((LinearEquiv.neg ℝ).prodCongr j₁)
          ((LinearEquiv.neg ℝ).prodCongr j₂)
          (prodMap_comp_prodCongr_eq_of_comp_eq (comp_neg_eq_neg_comp T) hj)
          ((detLineProdMapEquiv T (D.restrictScalars ℝ)).symm (x ⊗ₜ z)) =
        (-1 : ℝ) ^ (finrank ℝ (ker T) + finrank ℝ (N ⧸ range T) +
            (finrank ℂ (ker D) + finrank ℂ (Q ⧸ range D))) •
          (detLineProdMapEquiv T (D'.restrictScalars ℝ)).symm (x ⊗ₜ z') := by
  set c := finrank ℂ (ker D) + finrank ℂ (Q ⧸ range D)
  refine ⟨(-1 : ℝ) ^ c • (D.restrictScalars ℝ).detLineCongr j₁ j₂ hj z,
    hz.neg_one_pow_smul_detLineCongr j₁ j₂ hj hj₁ hj₂, ?_⟩
  apply (detLineProdMapEquiv T (D'.restrictScalars ℝ)).injective
  have h := detLineProdMapEquiv_detLineCongr_prodCongr T (D.restrictScalars ℝ)
    (LinearEquiv.neg ℝ) (LinearEquiv.neg ℝ) j₁ j₂ (comp_neg_eq_neg_comp T) hj
    ((detLineProdMapEquiv T (D.restrictScalars ℝ)).symm (x ⊗ₜ z))
  refine h.trans ?_
  simp only [LinearEquiv.apply_symm_apply, map_smul, map_tmul, LinearEquiv.coe_coe,
    detLineCongr_neg_apply, tmul_smul, smul_tmul', smul_smul, ← pow_add]
  -- The exponents differ by the even number `c + c`.
  rw [add_assoc _ c c, pow_add _ _ (c + c), Even.neg_one_pow ⟨c, rfl⟩, mul_one]

end LinearMap
