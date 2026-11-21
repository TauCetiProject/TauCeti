/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Basic
public import TauCeti.LinearAlgebra.Determinant.DirectSum
import TauCeti.Algebra.Ring.Parity

/-!
# Stabilization of direct sums of operators

The determinant lines `det (ker D) ⊗ (det (coker D))^*` of a family of Fredholm operators are
trivialized locally by finite stabilizations: if `D₁.coprod D₂ : E × Λ → F` is onto, with `Λ`
finite-dimensional, the normalized stabilization isomorphism
`ContinuousLinearMap.detLineStabilizationEquiv` identifies `det (ker (D₁.coprod D₂)) ⊗ (det Λ)^*`
with the determinant line of `D₁`, and kernel charts (`ContinuousLinearMap.detLineChartEquiv`) are
built from it. This file compares the stabilization of a direct sum with the stabilizations of its
summands, which is how the direct sum isomorphism of determinant lines
`LinearMap.detLineProdMapEquiv : det (D₁ ⊕ D₁') ≃ det D₁ ⊗ det D₁'` is compared with the local
trivializations.

If `D₁.coprod D₂` and `D₁'.coprod D₂'` are onto, so is the stabilization
`(D₁.prodMap D₁').coprod (D₂.prodMap D₂')` of the direct sum by the direct sum of the stabilizers
(`ContinuousLinearMap.surjective_coprod_prodMap`), and its kernel is the product of the two
stabilized kernels (`ContinuousLinearMap.kerCoprodProdMapEquiv`), both in
`TauCeti.Analysis.Fredholm.Parametric`. The stabilization sequence
`0 → ker D → ker (D.coprod D₂) → Λ → coker D → 0` of the direct sum is the product of the
sequences of the summands, so the four-term product law `TauCeti.detLineFourTermEquiv_prodMap`
computes its stabilization isomorphism. The result,
`ContinuousLinearMap.detLineStabilizationEquiv_prodMap`, is that the stabilization isomorphism of
the direct sum, applied to the product of `x` and `x'`, is the inverse direct sum isomorphism of
the tensor product of the stabilization isomorphisms of `x` and `x'`, up to the sign

`(-1) ^ (dim Λ * (dim ker D₁' + dim coker D₁') + dim coker D₁ * dim coker D₁')`.

The first term depends only on `dim Λ` and on the parity of the index of `D₁'`, and so is
constant along a family read through fixed stabilizers. The second is not: cokernel dimensions
jump along a family. So the multiple
`(-1) ^ (dim coker D₁ * dim coker D₁') • LinearMap.detLineProdMapEquiv`, whose Koszul sign is
`(-1) ^ (dim coker D₁ * (dim ker D₁' + dim coker D₁'))`, the parity of `dim coker D₁ * ind D₁'`,
is the direct sum isomorphism compatible with the normalized stabilizations up to a locally
constant sign.

## Main results

* `ContinuousLinearMap.detLineStabilizationEquiv_prodMap`: the normalized stabilization
  isomorphism of a direct sum, through `LinearMap.detLineProdMapEquiv`.

## References

* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368 (stabilizations and the
  direct sum isomorphism of determinant lines).
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
-/

public section

open Module TensorProduct

namespace ContinuousLinearMap

-- Stabilized kernels `(D₁.coprod D₂).ker` are finite-dimensional when `D₁.ker` and `Λ` are.
attribute [local instance] finiteDimensional_ker_coprod

section Stabilization

variable {𝕜 E Λ F E' Λ' F' : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [ContinuousAdd F] [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E']
  [AddCommGroup Λ'] [Module 𝕜 Λ'] [TopologicalSpace Λ'] [AddCommGroup F'] [Module 𝕜 F']
  [TopologicalSpace F'] [ContinuousAdd F']
  {D₁ : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F} {D₁' : E' →L[𝕜] F'} {D₂' : Λ' →L[𝕜] F'}

variable [FiniteDimensional 𝕜 D₁.ker] [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 D₁'.ker]
  [FiniteDimensional 𝕜 Λ'] [FiniteDimensional 𝕜 (F ⧸ D₁.range)]
  [FiniteDimensional 𝕜 (F' ⧸ D₁'.range)]

/-- The four-term isomorphism `ContinuousLinearMap.detLineCoprodEquiv` of a direct sum of
stabilized operators is the product of those of the summands, read through the splittings `eA`
and `eD` of the kernel and cokernel of `D₁.prodMap D₁'`, up to the Koszul sign of
`TauCeti.detLineFourTermEquiv_prodMap`. -/
private theorem detLineCoprodEquiv_prodMap (h : Function.Surjective (D₁.coprod D₂))
    (h' : Function.Surjective (D₁'.coprod D₂'))
    (eA : (D₁.ker × D₁'.ker) ≃ₗ[𝕜] (D₁.prodMap D₁').ker)
    (heA : ∀ v, (eA v : E × E') = ((v.1 : E), (v.2 : E')))
    (eD : ((F ⧸ D₁.range) × (F' ⧸ D₁'.range)) ≃ₗ[𝕜] (F × F') ⧸ (D₁.prodMap D₁').range)
    (heD : ∀ y y', eD (D₁.range.mkQ y, D₁'.range.mkQ y') = (D₁.prodMap D₁').range.mkQ (y, y'))
    (x : TauCeti.detLine 𝕜 (D₁.coprod D₂).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ))
    (x' : TauCeti.detLine 𝕜 (D₁'.coprod D₂').ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ')) :
    detLineCoprodEquiv (D₁.prodMap D₁') (D₂.prodMap D₂') (surjective_coprod_prodMap h h')
        (LinearEquiv.rTensor _ (kerCoprodProdMapEquiv D₁ D₂ D₁' D₂').detLineCongr
          (TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _ (x ⊗ₜ x'))) =
      (-1 : 𝕜) ^ (finrank 𝕜 D₁'.ker * finrank 𝕜 (parameterProj D₁ D₂).range +
          finrank 𝕜 (parameterProj D₁' D₂').range * finrank 𝕜 (F ⧸ D₁.range)) •
        TensorProduct.congr eA.detLineCongr eD.detLineCongr.symm.dualMap
          (TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _
            (detLineCoprodEquiv D₁ D₂ h x ⊗ₜ detLineCoprodEquiv D₁' D₂' h' x')) := by
  -- The stabilization sequence of the direct sum is isomorphic to the product of the two
  -- stabilization sequences, through `eA`, `kerCoprodProdMapEquiv`, the identity and `eD`.
  have hcongr := TauCeti.detLineFourTermEquiv_congr
    (f := (kerCoprodHom D₁ D₂ : D₁.ker →ₗ[𝕜] (D₁.coprod D₂).ker).prodMap
      (kerCoprodHom D₁' D₂' : D₁'.ker →ₗ[𝕜] (D₁'.coprod D₂').ker))
    (g := (parameterProj D₁ D₂ : (D₁.coprod D₂).ker →ₗ[𝕜] Λ).prodMap
      (parameterProj D₁' D₂' : (D₁'.coprod D₂').ker →ₗ[𝕜] Λ'))
    (h := (parameterToCoker D₁ D₂).prodMap (parameterToCoker D₁' D₂'))
    (f' := (kerCoprodHom (D₁.prodMap D₁') (D₂.prodMap D₂') : (D₁.prodMap D₁').ker →ₗ[𝕜] _))
    (g' := (parameterProj (D₁.prodMap D₁') (D₂.prodMap D₂') : _ →ₗ[𝕜] Λ × Λ'))
    (h' := parameterToCoker (D₁.prodMap D₁') (D₂.prodMap D₂'))
    ((kerCoprodHom_injective D₁ D₂).prodMap (kerCoprodHom_injective D₁' D₂'))
    ((exact_kerCoprodHom_parameterProj D₁ D₂).prodMap
      (exact_kerCoprodHom_parameterProj D₁' D₂'))
    ((exact_parameterProj_parameterToCoker D₁ D₂).prodMap
      (exact_parameterProj_parameterToCoker D₁' D₂'))
    (((parameterToCoker_surjective_iff_coprod_surjective D₁ D₂).2 h).prodMap
      ((parameterToCoker_surjective_iff_coprod_surjective D₁' D₂').2 h'))
    (kerCoprodHom_injective (D₁.prodMap D₁') (D₂.prodMap D₂'))
    (exact_kerCoprodHom_parameterProj (D₁.prodMap D₁') (D₂.prodMap D₂'))
    (exact_parameterProj_parameterToCoker (D₁.prodMap D₁') (D₂.prodMap D₂'))
    ((parameterToCoker_surjective_iff_coprod_surjective _ _).2 (surjective_coprod_prodMap h h'))
    eA (kerCoprodProdMapEquiv D₁ D₂ D₁' D₂') (LinearEquiv.refl 𝕜 _) eD ?_ ?_ ?_
    (TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _ (x ⊗ₜ x'))
  rotate_left
  · refine LinearMap.ext fun v ↦ Subtype.ext ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, ContinuousLinearMap.coe_coe,
      kerCoprodHom_apply, LinearMap.prodMap_apply]
    exact Prod.ext ((heA v).trans (by simp)) (by simp [Prod.mk_zero_zero])
  · exact LinearMap.ext fun v ↦ by simp
  · refine LinearMap.ext fun ⟨l, l'⟩ ↦ ?_
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.prodMap_apply,
      parameterToCoker_apply]
    exact (heD (D₂ l) (D₂' l')).symm
  have hprod := TauCeti.detLineFourTermEquiv_prodMap (kerCoprodHom_injective D₁ D₂)
    (exact_kerCoprodHom_parameterProj D₁ D₂) (exact_parameterProj_parameterToCoker D₁ D₂)
    ((parameterToCoker_surjective_iff_coprod_surjective D₁ D₂).2 h)
    (kerCoprodHom_injective D₁' D₂') (exact_kerCoprodHom_parameterProj D₁' D₂')
    (exact_parameterProj_parameterToCoker D₁' D₂')
    ((parameterToCoker_surjective_iff_coprod_surjective D₁' D₂').2 h') x x'
  -- The stabilizers of the two sides agree, so the stabilizer factor is not transported.
  have hr : TensorProduct.congr (kerCoprodProdMapEquiv D₁ D₂ D₁' D₂').detLineCongr
      (LinearEquiv.refl 𝕜 (Λ × Λ')).detLineCongr.symm.dualMap =
        LinearEquiv.rTensor _ (kerCoprodProdMapEquiv D₁ D₂ D₁' D₂').detLineCongr :=
    LinearEquiv.toLinearMap_injective (TensorProduct.ext' fun a φ ↦ by simp)
  rw [← hr]
  simp only [detLineCoprodEquiv_def (D₁ := D₁.prodMap D₁') (D₂ := D₂.prodMap D₂'), hcongr,
    hprod, LinearEquiv.map_smul, detLineCoprodEquiv_def h, detLineCoprodEquiv_def h']

/-- **The stabilization isomorphism of a direct sum.** Let `D₁.coprod D₂` and `D₁'.coprod D₂'` be
onto, so that `D₁.prodMap D₁'` is stabilized by `D₂.prodMap D₂'`. Gather `x` and `x'` into
`det (ker (D₁.coprod D₂) × ker (D₁'.coprod D₂')) ⊗ (det (Λ × Λ'))^*` by
`TauCeti.detLineTensorDualProdEquiv`, with no sign, and read the product of the stabilized kernels
as the stabilized kernel of the direct sum (`ContinuousLinearMap.kerCoprodProdMapEquiv`). Its
image under the normalized stabilization isomorphism of the direct sum is the image of the
tensor product of the normalized stabilization isomorphisms of `x` and `x'` under the inverse of
the direct sum isomorphism `LinearMap.detLineProdMapEquiv`, times the sign
`(-1) ^ (dim Λ * (dim ker D₁' + dim coker D₁') + dim coker D₁ * dim coker D₁')`. -/
theorem detLineStabilizationEquiv_prodMap
    (h : Function.Surjective (D₁.coprod D₂)) (h' : Function.Surjective (D₁'.coprod D₂'))
    (x : TauCeti.detLine 𝕜 (D₁.coprod D₂).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ))
    (x' : TauCeti.detLine 𝕜 (D₁'.coprod D₂').ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ')) :
    detLineStabilizationEquiv (D₁.prodMap D₁') (D₂.prodMap D₂') (surjective_coprod_prodMap h h')
        (LinearEquiv.rTensor _ (kerCoprodProdMapEquiv D₁ D₂ D₁' D₂').detLineCongr
          (TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _ (x ⊗ₜ x'))) =
      (-1 : 𝕜) ^ (finrank 𝕜 Λ * (finrank 𝕜 D₁'.ker + finrank 𝕜 (F' ⧸ D₁'.range)) +
          finrank 𝕜 (F ⧸ D₁.range) * finrank 𝕜 (F' ⧸ D₁'.range)) •
        (LinearMap.detLineProdMapEquiv (D₁ : E →ₗ[𝕜] F) (D₁' : E' →ₗ[𝕜] F')).symm
          (detLineStabilizationEquiv D₁ D₂ h x ⊗ₜ detLineStabilizationEquiv D₁' D₂' h' x') := by
  -- The componentwise splittings of the kernel and of the cokernel of `D₁.prodMap D₁'`.
  have hK : (D₁.prodMap D₁').ker = D₁.ker.prod D₁'.ker :=
    LinearMap.ker_prodMap (D₁ : E →ₗ[𝕜] F) (D₁' : E' →ₗ[𝕜] F')
  have hR : (D₁.prodMap D₁').range = D₁.range.prod D₁'.range :=
    LinearMap.range_prodMap (D₁ : E →ₗ[𝕜] F) (D₁' : E' →ₗ[𝕜] F')
  obtain ⟨eA, heA⟩ : ∃ eA : (D₁.ker × D₁'.ker) ≃ₗ[𝕜] (D₁.prodMap D₁').ker,
      ∀ v, (eA v : E × E') = ((v.1 : E), (v.2 : E')) :=
    ⟨((LinearEquiv.ofEq _ _ hK).trans (Submodule.prodEquiv _ _)).symm, fun _ ↦ rfl⟩
  obtain ⟨eD, heD⟩ : ∃ eD : ((F ⧸ D₁.range) × (F' ⧸ D₁'.range)) ≃ₗ[𝕜]
      (F × F') ⧸ (D₁.prodMap D₁').range,
      ∀ y y', eD (D₁.range.mkQ y, D₁'.range.mkQ y') = (D₁.prodMap D₁').range.mkQ (y, y') :=
    ⟨((Submodule.quotEquivOfEq _ _ hR).trans (Submodule.quotientProdEquiv _ _)).symm,
      fun y y' ↦ (LinearEquiv.symm_apply_eq _).mpr (by simp [-ContinuousLinearMap.coe_prodMap])⟩
  have hsum := detLineCoprodEquiv_prodMap h h' eA heA eD heD x x'
  simp only [detLineStabilizationEquiv_apply, hsum, smul_smul, TensorProduct.smul_tmul_smul]
  have hsplit := LinearMap.detLineProdMapEquiv_symm_tmul (D₁ : E →ₗ[𝕜] F)
    (D₁' : E' →ₗ[𝕜] F') eA heA eD heD (detLineCoprodEquiv D₁ D₂ h x)
    (detLineCoprodEquiv D₁' D₂' h' x')
  simp only [LinearEquiv.map_smul, hsplit, smul_smul]
  congr 1
  -- The sign: write `dim Λ = dim (range p) + dim (coker D₁)` for the parameter projection `p`;
  -- the two exponents then differ by `2 * dim (coker D₁) * dim (range p')`.
  have hc : finrank 𝕜 ((F × F') ⧸ (D₁.prodMap D₁').range) =
      finrank 𝕜 (F ⧸ D₁.range) + finrank 𝕜 (F' ⧸ D₁'.range) := by
    rw [← Module.finrank_prod]
    exact eD.finrank_eq.symm
  have hΛ : finrank 𝕜 Λ = finrank 𝕜 (parameterProj D₁ D₂).range + finrank 𝕜 (F ⧸ D₁.range) := by
    rw [← finrank_quotient_range_parameterProj D₁ D₂ h, add_comm]
    exact (Submodule.finrank_quotient_add_finrank _).symm
  have hΛ' : finrank 𝕜 Λ' =
      finrank 𝕜 (parameterProj D₁' D₂').range + finrank 𝕜 (F' ⧸ D₁'.range) := by
    rw [← finrank_quotient_range_parameterProj D₁' D₂' h', add_comm]
    exact (Submodule.finrank_quotient_add_finrank _).symm
  rw [hc, Module.finrank_prod, hΛ, hΛ']
  simp only [← pow_add]
  rw [← TauCeti.neg_one_pow_add_two_mul _ (finrank 𝕜 (F ⧸ D₁.range) * finrank 𝕜 D₁'.ker)]
  conv_rhs => rw [← TauCeti.neg_one_pow_add_two_mul _
    (finrank 𝕜 (F ⧸ D₁.range) * finrank 𝕜 (parameterProj D₁' D₂').range)]
  congr 1
  ring

end Stabilization

end ContinuousLinearMap
