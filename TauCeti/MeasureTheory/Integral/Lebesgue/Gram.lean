/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import TauCeti.LinearAlgebra.BilinearForm.Prod
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.LinearAlgebra.Matrix.BilinearForm
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# Gram densities of Haar measures

Let `B` be a field of bilinear forms on a finite-dimensional real vector space `E`, for instance
a Riemannian metric read in a chart. In a basis `b` of `E` it has the Gram density
`√(det G_b(x))`, where `G_b(x)` is the Gram matrix of `B x` in `b`, and this density weights the
Haar measure `b.addHaar` normalized by `b`. This is the coordinate expression of the Riemannian
volume. The weighted measure does not depend on the basis
(`Module.Basis.addHaar_withDensity_ofReal_sqrt_det_toMatrix_eq`): a change of basis with matrix
`P` multiplies the Gram determinant by `(det P)²`, hence the density by `|det P|`, and the Haar
measure by `|det P|⁻¹` (`Module.Basis.addHaar_withDensity_eq_of_eq_abs_det_mul`).

Consequently, for fields of forms `B₁` on `E` and `B₂` on `F`, the Gram density of the
block-diagonal field `(B₁ x).prod (B₂ y)` on `E × F`, integrated over a product set, is the product
of the integrals of the two Gram densities
(`Module.Basis.setLIntegral_ofReal_sqrt_det_toMatrix_prod`): in a product basis the Gram matrix is
block diagonal and the Haar measure is the product of the Haar measures. This is the computation
behind the Riemannian volume of a product of Riemannian manifolds.

Both results follow their top-form versions for the density `|ω(b)|` of a top-degree form,
`Module.Basis.addHaar_withDensity_ofReal_abs_apply_eq` and
`Module.Basis.setLIntegral_ofReal_abs_apply_prod`.

## Main results

* `Module.Basis.addHaar_withDensity_ofReal_sqrt_det_toMatrix_eq`: the Haar measure weighted by
  the Gram density does not depend on the basis.
* `Module.Basis.setLIntegral_ofReal_sqrt_det_toMatrix_prod`: the integral of the Gram density of a
  block-diagonal field of forms over a product set is the product of the factor integrals.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Module.Basis

variable {E F ι ι' κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype ι] [Fintype ι'] [Fintype κ]
  [DecidableEq ι] [DecidableEq ι'] [DecidableEq κ]

/-- **The Gram density of a field of bilinear forms is independent of the basis.** The Haar
measure of a basis `b` weighted by `√(det G_b(x))`, with `G_b(x)` the Gram matrix of `B x` in `b`,
is the same for every basis: changing the basis multiplies the density by the absolute determinant
of the change and the Haar measure by its inverse. -/
theorem addHaar_withDensity_ofReal_sqrt_det_toMatrix_eq (b b' : Basis ι ℝ E)
    (B : E → LinearMap.BilinForm ℝ E) :
    b'.addHaar.withDensity
        (fun x ↦ ENNReal.ofReal √(LinearMap.BilinForm.toMatrix b' (B x)).det) =
      b.addHaar.withDensity
        (fun x ↦ ENNReal.ofReal √(LinearMap.BilinForm.toMatrix b (B x)).det) := by
  refine addHaar_withDensity_eq_of_eq_abs_det_mul b b' fun x ↦ ?_
  rw [LinearMap.BilinForm.det_toMatrix_eq_det_sq_mul_det b b', Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq_eq_abs, b.det_apply, ENNReal.ofReal_mul (abs_nonneg _)]

/-- **Gram densities of block-diagonal forms integrate as products.** Let `B₁` and `B₂` be fields of
bilinear forms on `E` and on `F`. Over a product `A₁ ×ˢ A₂` of measurable sets, the Gram density of
the block-diagonal forms `(B₁ x).prod (B₂ y)` on `E × F`, in any basis `b₀`, integrates to the
product of the integrals of the Gram densities of `B₁` and `B₂` in bases `b₁` and `b₂`. The Borel
structure on `E × F` is arbitrary, so this applies to the chart measurable structure of a manifold
model space. -/
theorem setLIntegral_ofReal_sqrt_det_toMatrix_prod [MeasurableSpace F] [BorelSpace F]
    [mEF : MeasurableSpace (E × F)] [BorelSpace (E × F)]
    (b₀ : Basis κ ℝ (E × F)) (b₁ : Basis ι ℝ E) (b₂ : Basis ι' ℝ F)
    {A₁ : Set E} {A₂ : Set F} (hA₁ : MeasurableSet A₁) (hA₂ : MeasurableSet A₂)
    (B₁ : E → LinearMap.BilinForm ℝ E) (B₂ : F → LinearMap.BilinForm ℝ F)
    (hB₁ : ∀ x ∈ A₁, 0 ≤ (LinearMap.BilinForm.toMatrix b₁ (B₁ x)).det)
    (hf : AEMeasurable (fun x ↦ ENNReal.ofReal √(LinearMap.BilinForm.toMatrix b₁ (B₁ x)).det)
      (b₁.addHaar.restrict A₁))
    (hg : AEMeasurable (fun y ↦ ENNReal.ofReal √(LinearMap.BilinForm.toMatrix b₂ (B₂ y)).det)
      (b₂.addHaar.restrict A₂)) :
    ∫⁻ z in A₁ ×ˢ A₂,
        ENNReal.ofReal √(LinearMap.BilinForm.toMatrix b₀ ((B₁ z.1).prod (B₂ z.2))).det
          ∂b₀.addHaar =
      (∫⁻ x in A₁, ENNReal.ofReal √(LinearMap.BilinForm.toMatrix b₁ (B₁ x)).det ∂b₁.addHaar) *
        ∫⁻ y in A₂, ENNReal.ofReal √(LinearMap.BilinForm.toMatrix b₂ (B₂ y)).det ∂b₂.addHaar := by
  have : FiniteDimensional ℝ F := b₂.finiteDimensional_of_finite
  obtain rfl : mEF = Prod.instMeasurableSpace :=
    BorelSpace.measurable_eq.trans (Prod.borelSpace (α := E) (β := F)).measurable_eq.symm
  -- Compute in the product basis, reindexed along the index type of `b₀`.
  set b := (b₁.prod b₂).reindex ((b₁.prod b₂).indexEquiv b₀)
  have hprod : ∀ z ∈ A₁ ×ˢ A₂,
      ENNReal.ofReal √(LinearMap.BilinForm.toMatrix b ((B₁ z.1).prod (B₂ z.2))).det =
        ENNReal.ofReal √(LinearMap.BilinForm.toMatrix b₁ (B₁ z.1)).det *
          ENNReal.ofReal √(LinearMap.BilinForm.toMatrix b₂ (B₂ z.2)).det := fun z hz ↦ by
    rw [LinearMap.BilinForm.det_toMatrix_reindex, LinearMap.BilinForm.toMatrix_prod,
      Matrix.det_fromBlocks_zero₂₁, Real.sqrt_mul (hB₁ _ hz.1),
      ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  rw [← withDensity_apply _ (hA₁.prod hA₂),
    addHaar_withDensity_ofReal_sqrt_det_toMatrix_eq b b₀ (fun z ↦ (B₁ z.1).prod (B₂ z.2)),
    withDensity_apply _ (hA₁.prod hA₂), setLIntegral_congr_fun (hA₁.prod hA₂) hprod,
    addHaar_reindex, prod_addHaar, ← Measure.prod_restrict, lintegral_prod_mul hf hg]

end Module.Basis
