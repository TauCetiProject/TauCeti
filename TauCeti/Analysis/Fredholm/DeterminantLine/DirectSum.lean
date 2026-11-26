/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Transport
public import TauCeti.LinearAlgebra.Determinant.DirectSum
public import Mathlib.Analysis.Normed.Operator.Prod
public import TauCeti.Analysis.Fredholm.Prod
import TauCeti.Algebra.Ring.Parity
import TauCeti.LinearAlgebra.Ray
import TauCeti.LinearAlgebra.TensorProduct.Separation

/-!
# Direct sums of Fredholm determinant lines

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

The same holds for kernel charts. Kernel charts `(D₂, q)` of `T` and `(D₂', q')` of `T'` give the
kernel chart `(D₂.prodMap D₂', ContinuousLinearMap.prodMapKerCoord q q')` of `T.prodMap T'`
(`ContinuousLinearMap.IsInvertible.prod_coprod_prodMap`). It reads the normalized direct sum
`(-1) ^ (dim coker T * dim coker T') • (detLineProdMapEquiv T T').symm (v ⊗ v')` as the product of
the readings of `v` and `v'`, times `(-1) ^ (dim Λ * (dim G' + dim Λ'))`
(`ContinuousLinearMap.detLineChartEquiv_neg_one_pow_smul_prodMap`). This sign depends only on the
charts, because a kernel chart fixes the index, `dim ker T' - dim coker T' = dim G' - dim Λ'`
(`ContinuousLinearMap.finrank_ker_add_finrank_eq_of_isInvertible_prod_coprod`). Hence over `ℝ`
the normalized direct sum of coherent families of `T` and `T'` is coherent for `T ⊕ T'`
(`TauCeti.IsDetLineCoherentOn.prodMap`): the direct sum isomorphism carries continuous orientations
of the determinant lines of two families to a continuous orientation of the determinant lines of
their direct sum, although kernels and cokernels jump. In particular orientation transport along
a direct sum of paths is the direct sum of the transports
(`TauCeti.detLineOrientationTransport_prodMap`).

## Main results

* `ContinuousLinearMap.detLineStabilizationEquiv_prodMap`: the normalized stabilization
  isomorphism of a direct sum, through `LinearMap.detLineProdMapEquiv`.
* `ContinuousLinearMap.IsInvertible.prod_coprod_prodMap`: the direct sum of kernel charts is a
  kernel chart.
* `ContinuousLinearMap.detLineChartEquiv_prodMap`,
  `ContinuousLinearMap.detLineChartEquiv_neg_one_pow_smul_prodMap`: the direct sum kernel chart
  reads the direct sum isomorphism.
* `TauCeti.IsDetLineCoherentOn.prodMap`: normalized direct sums of coherent families are
  coherent.
* `TauCeti.detLineOrientationTransport_prodMap`: orientation transport commutes with direct sums.

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
  rw [hc, Module.finrank_prod, ← finrank_range_parameterProj_add_finrank_quotient_range D₁ D₂ h,
    ← finrank_range_parameterProj_add_finrank_quotient_range D₁' D₂' h']
  simp only [← pow_add]
  rw [← TauCeti.neg_one_pow_add_two_mul _ (finrank 𝕜 (F ⧸ D₁.range) * finrank 𝕜 D₁'.ker)]
  conv_rhs => rw [← TauCeti.neg_one_pow_add_two_mul _
    (finrank 𝕜 (F ⧸ D₁.range) * finrank 𝕜 (parameterProj D₁' D₂').range)]
  congr 1
  ring

end Stabilization

section Chart

/-! ### Kernel charts of direct sums -/

variable {𝕜 E Λ F G E' Λ' F' G' : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [AddCommGroup Λ] [Module 𝕜 Λ] [TopologicalSpace Λ] [AddCommGroup F]
  [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F] [AddCommGroup G] [Module 𝕜 G]
  [TopologicalSpace G] [AddCommGroup E'] [Module 𝕜 E'] [TopologicalSpace E'] [AddCommGroup Λ']
  [Module 𝕜 Λ'] [TopologicalSpace Λ'] [AddCommGroup F'] [Module 𝕜 F'] [TopologicalSpace F']
  [ContinuousAdd F'] [AddCommGroup G'] [Module 𝕜 G'] [TopologicalSpace G']
  {T : E →L[𝕜] F} {D₂ : Λ →L[𝕜] F} {q : E × Λ →L[𝕜] G}
  {T' : E' →L[𝕜] F'} {D₂' : Λ' →L[𝕜] F'} {q' : E' × Λ' →L[𝕜] G'}

variable (q q') in
/-- **The kernel coordinate of a direct sum of kernel charts.** Kernel coordinates
`q : E × Λ → G` and `q' : E' × Λ' → G'` of stabilizations of `T` and `T'` give the coordinate
`((x, x'), (l, l')) ↦ (q (x, l), q' (x', l'))` of the stabilization of `T.prodMap T'` by
`D₂.prodMap D₂'`. -/
def prodMapKerCoord : (E × E') × (Λ × Λ') →L[𝕜] G × G' :=
  q.prodMap q' ∘L (ContinuousLinearEquiv.prodProdProdComm 𝕜 E E' Λ Λ' :
    (E × E') × (Λ × Λ') →L[𝕜] (E × Λ) × (E' × Λ'))

@[simp]
theorem prodMapKerCoord_apply (x : E × E') (l : Λ × Λ') :
    prodMapKerCoord q q' (x, l) = (q (x.1, l.1), q' (x.2, l.2)) :=
  (rfl)

/-- **The direct sum of kernel charts is a kernel chart.** If `(D₂, q)` is a kernel chart of `T`
and `(D₂', q')` one of `T'`, then `(D₂.prodMap D₂', prodMapKerCoord q q')` is a kernel chart of
`T.prodMap T'`: up to reordering the factors, its pair is the product of the two pairs. -/
theorem IsInvertible.prod_coprod_prodMap (h : ((T.coprod D₂).prod q).IsInvertible)
    (h' : ((T'.coprod D₂').prod q').IsInvertible) :
    (((T.prodMap T').coprod (D₂.prodMap D₂')).prod (prodMapKerCoord q q')).IsInvertible := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  refine ⟨(ContinuousLinearEquiv.prodProdProdComm 𝕜 E E' Λ Λ').trans
    ((e.prodCongr e').trans (ContinuousLinearEquiv.prodProdProdComm 𝕜 F G F' G')), ?_⟩
  refine ContinuousLinearMap.ext fun ⟨⟨x, x'⟩, ⟨l, l'⟩⟩ ↦ ?_
  have h₁ := DFunLike.congr_fun he (x, l)
  have h₂ := DFunLike.congr_fun he' (x', l')
  simp only [ContinuousLinearEquiv.coe_coe] at h₁ h₂
  simp [h₁, h₂]

section FiniteDimensional

variable [FiniteDimensional 𝕜 Λ] [FiniteDimensional 𝕜 G]

variable [FiniteDimensional 𝕜 Λ'] [FiniteDimensional 𝕜 G']

/-- **The kernel chart of a direct sum reads the direct sum isomorphism.** In the direct sum
`(D₂.prodMap D₂', prodMapKerCoord q q')` of kernel charts of `T` and `T'`, the element of the
determinant line of `T.prodMap T'` corresponding to `v ⊗ v'` under the direct sum isomorphism
`LinearMap.detLineProdMapEquiv` is read as the product, under
`TauCeti.detLineTensorDualProdEquiv`, of the readings of `v` and `v'`, times the sign
`(-1) ^ (dim Λ * (dim ker T' + dim coker T') + dim coker T * dim coker T')` of
`ContinuousLinearMap.detLineStabilizationEquiv_prodMap`. -/
theorem detLineChartEquiv_prodMap (h : ((T.coprod D₂).prod q).IsInvertible)
    (h' : ((T'.coprod D₂').prod q').IsInvertible) [FiniteDimensional 𝕜 T.ker]
    [FiniteDimensional 𝕜 (F ⧸ T.range)] [FiniteDimensional 𝕜 T'.ker]
    [FiniteDimensional 𝕜 (F' ⧸ T'.range)] (v : (T : E →ₗ[𝕜] F).detLine)
    (v' : (T' : E' →ₗ[𝕜] F').detLine) :
    detLineChartEquiv (T.prodMap T') (D₂.prodMap D₂') (prodMapKerCoord q q')
        (h.prod_coprod_prodMap h')
        ((LinearMap.detLineProdMapEquiv (T : E →ₗ[𝕜] F) (T' : E' →ₗ[𝕜] F')).symm (v ⊗ₜ v')) =
      (-1 : 𝕜) ^ (finrank 𝕜 Λ * (finrank 𝕜 T'.ker + finrank 𝕜 (F' ⧸ T'.range)) +
          finrank 𝕜 (F ⧸ T.range) * finrank 𝕜 (F' ⧸ T'.range)) •
        TauCeti.detLineTensorDualProdEquiv 𝕜 G Λ G' Λ'
          (detLineChartEquiv T D₂ q h v ⊗ₜ detLineChartEquiv T' D₂' q' h' v') := by
  have hs := surjective_of_isInvertible_prod h
  have hs' := surjective_of_isInvertible_prod h'
  have := finiteDimensional_ker_of_isInvertible_prod_coprod (h.prod_coprod_prodMap h')
  obtain ⟨x, rfl⟩ := (detLineStabilizationEquiv T D₂ hs).surjective v
  obtain ⟨x', rfl⟩ := (detLineStabilizationEquiv T' D₂' hs').surjective v'
  -- Solve the stabilization law of the direct sum for the inverse direct sum isomorphism.
  have hsum := detLineStabilizationEquiv_prodMap hs hs' x x'
  have hsign {c : 𝕜} {a b : (T.prodMap T' : E × E' →ₗ[𝕜] F × F').detLine} (hc : c * c = 1)
      (hab : a = c • b) : b = c • a := by
    rw [hab, smul_smul, hc, one_smul]
  rw [hsign (by rw [← pow_add, ← two_mul, (even_two_mul _).neg_one_pow]) hsum,
    LinearEquiv.map_smul, detLineChartEquiv_detLineStabilizationEquiv,
    detLineChartEquiv_detLineStabilizationEquiv, detLineChartEquiv_detLineStabilizationEquiv]
  congr 1
  -- The kernel coordinate of the direct sum restricts to the product of the kernel coordinates.
  have hE : (kerCoprodProdMapEquiv T D₂ T' D₂').trans
      (kerEquivOfProd _ _ (h.prod_coprod_prodMap h')).toLinearEquiv.symm =
        (kerEquivOfProd _ q h).toLinearEquiv.symm.prodCongr
          (kerEquivOfProd _ q' h').toLinearEquiv.symm :=
    LinearEquiv.ext fun _ ↦ by simp
  rw [← TensorProduct.congr_tmul,
    ← TauCeti.rTensor_detLineCongr_prodCongr_detLineTensorDualProdEquiv,
    ← hE, LinearEquiv.detLineCongr_trans, LinearEquiv.rTensor_trans_apply]

/-- **The normalized direct sum in a direct sum of kernel charts.** With the sign
`(-1) ^ (dim coker T * dim coker T')`, the direct sum of `v` and `v'` is read in the direct sum of
kernel charts of `T` and `T'` as the product of the readings of `v` and `v'` times the sign
`(-1) ^ (dim Λ * (dim G' + dim Λ'))`, which depends only on the charts. -/
theorem detLineChartEquiv_neg_one_pow_smul_prodMap (h : ((T.coprod D₂).prod q).IsInvertible)
    (h' : ((T'.coprod D₂').prod q').IsInvertible) [FiniteDimensional 𝕜 T.ker]
    [FiniteDimensional 𝕜 (F ⧸ T.range)] [FiniteDimensional 𝕜 T'.ker]
    [FiniteDimensional 𝕜 (F' ⧸ T'.range)] (v : (T : E →ₗ[𝕜] F).detLine)
    (v' : (T' : E' →ₗ[𝕜] F').detLine) :
    detLineChartEquiv (T.prodMap T') (D₂.prodMap D₂') (prodMapKerCoord q q')
        (h.prod_coprod_prodMap h')
        ((-1 : 𝕜) ^ (finrank 𝕜 (F ⧸ T.range) * finrank 𝕜 (F' ⧸ T'.range)) •
          (LinearMap.detLineProdMapEquiv (T : E →ₗ[𝕜] F) (T' : E' →ₗ[𝕜] F')).symm (v ⊗ₜ v')) =
      (-1 : 𝕜) ^ (finrank 𝕜 Λ * (finrank 𝕜 G' + finrank 𝕜 Λ')) •
        TauCeti.detLineTensorDualProdEquiv 𝕜 G Λ G' Λ'
          (detLineChartEquiv T D₂ q h v ⊗ₜ detLineChartEquiv T' D₂' q' h' v') := by
  refine ((detLineChartEquiv _ _ _ (h.prod_coprod_prodMap h')).map_smul _ _).trans ?_
  rw [detLineChartEquiv_prodMap h h', smul_smul, ← pow_add]
  congr 1
  -- The index of `T'` is `dim G' - dim Λ'`, so `dim ker T' + dim coker T'` has the parity of
  -- `dim G' + dim Λ'`.
  have hidx := finrank_ker_add_finrank_eq_of_isInvertible_prod_coprod h'
  refine neg_one_pow_congr ?_
  have hpar := (congrArg Even hidx).to_iff
  simp only [Nat.even_add, Nat.even_mul] at hpar ⊢
  grind

end FiniteDimensional

end Chart

end ContinuousLinearMap

namespace TauCeti

open Filter Set Topology ContinuousLinearMap

section Coherent

/-! ### Coherence of the direct sum isomorphism along families -/

variable {E F E' F' X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [CompleteSpace E'] [NormedAddCommGroup F'] [NormedSpace ℝ F']
  [CompleteSpace F'] [TopologicalSpace X] {T : X → E →L[ℝ] F} {T' : X → E' →L[ℝ] F'}
  {v : ∀ x, (T x : E →ₗ[ℝ] F).detLine} {v' : ∀ x, (T' x : E' →ₗ[ℝ] F').detLine}
  {w : ∀ x, ((T x).prodMap (T' x) : E × E' →ₗ[ℝ] F × F').detLine} {s : Set X}

/-- The step of `TauCeti.IsDetLineCoherentOn.prodMap` at one parameter: if kernel charts of `T`
and `T'` valid at `x₀` read `v x` and `v' x`, for `x ∈ s` near `x₀`, as nonnegative multiples of
their readings at `x₀`, then the direct sum family is coherent within `s` at `x₀`. -/
private theorem isDetLineCoherentWithinAt_prodMap {Λ G Λ' G' : Type*} [NormedAddCommGroup Λ]
    [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] [NormedAddCommGroup Λ'] [NormedSpace ℝ Λ'] [FiniteDimensional ℝ Λ']
    [NormedAddCommGroup G'] [NormedSpace ℝ G'] [FiniteDimensional ℝ G'] {D₂ : Λ →L[ℝ] F}
    {q : E × Λ →L[ℝ] G} {D₂' : Λ' →L[ℝ] F'} {q' : E' × Λ' →L[ℝ] G'} {x₀ : X} (hx₀ : x₀ ∈ s)
    (hT : ContinuousOn T s) (hT' : ContinuousOn T' s)
    (hF : ∀ x ∈ s, IsFredholm (T x)) (hF' : ∀ x ∈ s, IsFredholm (T' x))
    (hv : ∀ x ∈ s, v x ≠ 0) (hv' : ∀ x ∈ s, v' x ≠ 0)
    (hw : ∀ x ∈ s, ∀ [FiniteDimensional ℝ (T x).ker] [FiniteDimensional ℝ (F ⧸ (T x).range)]
      [FiniteDimensional ℝ (T' x).ker] [FiniteDimensional ℝ (F' ⧸ (T' x).range)],
      w x = (-1 : ℝ) ^ (finrank ℝ (F ⧸ (T x).range) * finrank ℝ (F' ⧸ (T' x).range)) •
        (LinearMap.detLineProdMapEquiv (T x : E →ₗ[ℝ] F) (T' x : E' →ₗ[ℝ] F')).symm
          (v x ⊗ₜ v' x))
    (h₀ : (((T x₀).coprod D₂).prod q).IsInvertible)
    (h₀' : (((T' x₀).coprod D₂').prod q').IsInvertible)
    (hev : ∀ᶠ x in 𝓝[s] x₀, ∃ h : (((T x).coprod D₂).prod q).IsInvertible,
      SameRay ℝ (detLineChartEquiv (T x) D₂ q h (v x)) (detLineChartEquiv (T x₀) D₂ q h₀ (v x₀)))
    (hev' : ∀ᶠ x in 𝓝[s] x₀, ∃ h : (((T' x).coprod D₂').prod q').IsInvertible,
      SameRay ℝ (detLineChartEquiv (T' x) D₂' q' h (v' x))
        (detLineChartEquiv (T' x₀) D₂' q' h₀' (v' x₀))) :
    IsDetLineCoherentWithinAt (fun x ↦ (T x).prodMap (T' x)) w s x₀ := by
  -- In the direct sum of the two kernel charts, `w x` is read as a constant sign times the product
  -- of the readings of `v x` and `v' x`.
  have hread (x : X) (hx : x ∈ s) (h : (((T x).coprod D₂).prod q).IsInvertible)
      (h' : (((T' x).coprod D₂').prod q').IsInvertible) :
      detLineChartEquiv ((T x).prodMap (T' x)) (D₂.prodMap D₂') (prodMapKerCoord q q')
          (h.prod_coprod_prodMap h') (w x) =
        (-1 : ℝ) ^ (finrank ℝ Λ * (finrank ℝ G' + finrank ℝ Λ')) •
          detLineTensorDualProdEquiv ℝ G Λ G' Λ'
            (detLineChartEquiv (T x) D₂ q h (v x) ⊗ₜ
              detLineChartEquiv (T' x) D₂' q' h' (v' x)) := by
    have := (hF x hx).finite_ker
    have := (hF x hx).finite_coker
    have := (hF' x hx).finite_ker
    have := (hF' x hx).finite_coker
    rw [hw x hx]
    exact detLineChartEquiv_neg_one_pow_smul_prodMap h h' (v x) (v' x)
  have hne₀ := (LinearEquiv.map_ne_zero_iff (detLineChartEquiv (T x₀) D₂ q h₀)).2 (hv x₀ hx₀)
  have hne₀' := (LinearEquiv.map_ne_zero_iff (detLineChartEquiv (T' x₀) D₂' q' h₀')).2
    (hv' x₀ hx₀)
  -- Naming the types of the direct sum chart keeps the elaboration of its instances cheap.
  refine isDetLineCoherentWithinAt_of_eventually_sameRay (T := fun x ↦ (T x).prodMap (T' x))
    (v := w) ((hT.prod_mapL ℝ hT') x₀ hx₀) ((hF x₀ hx₀).prodMap (hF' x₀ hx₀)) (Λ := Λ × Λ')
    (G := G × G') (D₂ := D₂.prodMap D₂') (q := prodMapKerCoord q q') ?_
    (h₀.prod_coprod_prodMap h₀') ?_
  · intro h0
    have hr := hread x₀ hx₀ h₀ h₀'
    rw [h0, LinearEquiv.map_zero] at hr
    exact smul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero))
      ((LinearEquiv.map_ne_zero_iff _).2 (tmul_ne_zero hne₀ hne₀')) hr.symm
  · filter_upwards [hev, hev', self_mem_nhdsWithin] with x ⟨h, hx⟩ ⟨h', hx'⟩ hxs
    refine ⟨h.prod_coprod_prodMap h', ?_⟩
    rw [hread x hxs h h', hread x₀ hx₀ h₀ h₀']
    exact (hx.tmul hx').map
      ((-1 : ℝ) ^ (finrank ℝ Λ * (finrank ℝ G' + finrank ℝ Λ')) •
        (detLineTensorDualProdEquiv ℝ G Λ G' Λ').toLinearMap)

/-- **The direct sum of coherent families is coherent.** Let `v` and `v'` be coherent families of
elements of the determinant lines of continuous families `T` and `T'` of Fredholm operators on
`s`. Then the family `w` of their direct sums, normalized by the sign
`(-1) ^ (dim coker T x * dim coker T' x)`,

`w x = (-1) ^ (dim coker T x * dim coker T' x) • (detLineProdMapEquiv (T x) (T' x)).symm
  (v x ⊗ v' x)`,

is coherent for the family `T x ⊕ T' x` on `s`. The sign is needed because cokernel dimensions jump
along the family. The direct sum of two kernel charts is a kernel chart
(`ContinuousLinearMap.IsInvertible.prod_coprod_prodMap`), which reads `w x` as the product of the
readings of `v x` and `v' x` times a sign depending only on the charts
(`ContinuousLinearMap.detLineChartEquiv_neg_one_pow_smul_prodMap`). So the direct sum isomorphism
carries continuous orientations of `T` and `T'` to a continuous orientation of `T ⊕ T'`. -/
theorem IsDetLineCoherentOn.prodMap (hT : ContinuousOn T s) (hT' : ContinuousOn T' s)
    (hF : ∀ x ∈ s, IsFredholm (T x)) (hF' : ∀ x ∈ s, IsFredholm (T' x))
    (hv : IsDetLineCoherentOn T v s) (hv' : IsDetLineCoherentOn T' v' s)
    (hw : ∀ x ∈ s, ∀ [FiniteDimensional ℝ (T x).ker] [FiniteDimensional ℝ (F ⧸ (T x).range)]
      [FiniteDimensional ℝ (T' x).ker] [FiniteDimensional ℝ (F' ⧸ (T' x).range)],
      w x = (-1 : ℝ) ^ (finrank ℝ (F ⧸ (T x).range) * finrank ℝ (F' ⧸ (T' x).range)) •
        (LinearMap.detLineProdMapEquiv (T x : E →ₗ[ℝ] F) (T' x : E' →ₗ[ℝ] F')).symm
          (v x ⊗ₜ v' x)) :
    IsDetLineCoherentOn (fun x ↦ (T x).prodMap (T' x)) w s := by
  refine isDetLineCoherentOn_iff.2 fun x₀ hx₀ ↦ ?_
  obtain ⟨-, S, _, G, _, q, h₀, hev⟩ :=
    isDetLineCoherentWithinAt_iff.1 (isDetLineCoherentOn_iff.1 hv x₀ hx₀)
  obtain ⟨-, S', _, G', _, q', h₀', hev'⟩ :=
    isDetLineCoherentWithinAt_iff.1 (isDetLineCoherentOn_iff.1 hv' x₀ hx₀)
  exact isDetLineCoherentWithinAt_prodMap hx₀ hT hT' hF hF' (fun _ hx ↦ hv.ne_zero hx)
    (fun _ hx ↦ hv'.ne_zero hx) hw h₀ h₀' hev hev'

section Transport

variable {T : ℝ → E →L[ℝ] F} {T' : ℝ → E' →L[ℝ] F'} {a b : ℝ}

/-- **Orientation transport commutes with direct sums.** Along paths `T` and `T'` of operators
which are continuous and Fredholm between `a` and `b`, let the orientations of `v₀` and `v₀'` be
transported to those of `u` and `u'`. Then along the direct sum path `T ⊕ T'` the orientation of
the direct sum of `v₀` and `v₀'` is transported to that of the direct sum of `u` and `u'`, each
normalized by the sign `(-1) ^ (dim coker T t * dim coker T' t)` of
`TauCeti.IsDetLineCoherentOn.prodMap` at its endpoint. -/
theorem detLineOrientationTransport_prodMap (hT : ContinuousOn T (uIcc a b))
    (hT' : ContinuousOn T' (uIcc a b)) (hF : ∀ t ∈ uIcc a b, IsFredholm (T t))
    (hF' : ∀ t ∈ uIcc a b, IsFredholm (T' t)) [FiniteDimensional ℝ (T a).ker]
    [FiniteDimensional ℝ (F ⧸ (T a).range)] [FiniteDimensional ℝ (T' a).ker]
    [FiniteDimensional ℝ (F' ⧸ (T' a).range)] [FiniteDimensional ℝ (T b).ker]
    [FiniteDimensional ℝ (F ⧸ (T b).range)] [FiniteDimensional ℝ (T' b).ker]
    [FiniteDimensional ℝ (F' ⧸ (T' b).range)] {v₀ : (T a : E →ₗ[ℝ] F).detLine}
    {v₀' : (T' a : E' →ₗ[ℝ] F').detLine} {u : (T b : E →ₗ[ℝ] F).detLine}
    {u' : (T' b : E' →ₗ[ℝ] F').detLine} (hv₀ : v₀ ≠ 0) (hv₀' : v₀' ≠ 0) (hu : u ≠ 0)
    (hu' : u' ≠ 0)
    (htr : detLineOrientationTransport a b hT hF (rayOfNeZero ℝ v₀ hv₀) = rayOfNeZero ℝ u hu)
    (htr' : detLineOrientationTransport a b hT' hF' (rayOfNeZero ℝ v₀' hv₀') =
      rayOfNeZero ℝ u' hu') :
    detLineOrientationTransport (T := fun t ↦ (T t).prodMap (T' t)) a b (hT.prod_mapL ℝ hT')
        (fun t ht ↦ (hF t ht).prodMap (hF' t ht))
        (rayOfNeZero ℝ ((-1 : ℝ) ^ (finrank ℝ (F ⧸ (T a).range) * finrank ℝ (F' ⧸ (T' a).range)) •
          ((LinearMap.detLineProdMapEquiv (T a : E →ₗ[ℝ] F) (T' a : E' →ₗ[ℝ] F')).symm
            (v₀ ⊗ₜ v₀') : ((T a).prodMap (T' a) : E × E' →ₗ[ℝ] F × F').detLine))
          (LinearMap.neg_one_pow_smul_detLineProdMapEquiv_symm_tmul_ne_zero _ _ _ hv₀ hv₀')) =
      rayOfNeZero ℝ ((-1 : ℝ) ^ (finrank ℝ (F ⧸ (T b).range) * finrank ℝ (F' ⧸ (T' b).range)) •
          ((LinearMap.detLineProdMapEquiv (T b : E →ₗ[ℝ] F) (T' b : E' →ₗ[ℝ] F')).symm (u ⊗ₜ u') :
            ((T b).prodMap (T' b) : E × E' →ₗ[ℝ] F × F').detLine))
        (LinearMap.neg_one_pow_smul_detLineProdMapEquiv_symm_tmul_ne_zero _ _ _ hu hu') := by
  classical
  refine detLineOrientationTransport_rayOfNeZero_apply_tmul hT hT' (hT.prod_mapL ℝ hT') hF hF'
    (fun t ht ↦ (hF t ht).prodMap (hF' t ht))
    ((-1 : ℝ) ^ (finrank ℝ (F ⧸ (T a).range) * finrank ℝ (F' ⧸ (T' a).range)) •
      (LinearMap.detLineProdMapEquiv (T a : E →ₗ[ℝ] F) (T' a : E' →ₗ[ℝ] F')).symm.toLinearMap)
    ((-1 : ℝ) ^ (finrank ℝ (F ⧸ (T b).range) * finrank ℝ (F' ⧸ (T' b).range)) •
      (LinearMap.detLineProdMapEquiv (T b : E →ₗ[ℝ] F) (T' b : E' →ₗ[ℝ] F')).symm.toLinearMap)
    (fun V V' hV hV' ↦ ?_) hv₀ hv₀' hu hu' _ _ htr htr'
  -- The normalized direct sums of coherent families form a coherent family for `T ⊕ T'`.
  let W (t : ℝ) : ((T t).prodMap (T' t) : E × E' →ₗ[ℝ] F × F').detLine :=
    if ht : t ∈ uIcc a b then
      have := (hF t ht).finite_ker
      have := (hF t ht).finite_coker
      have := (hF' t ht).finite_ker
      have := (hF' t ht).finite_coker
      (-1 : ℝ) ^ (finrank ℝ (F ⧸ (T t).range) * finrank ℝ (F' ⧸ (T' t).range)) •
        (LinearMap.detLineProdMapEquiv (T t : E →ₗ[ℝ] F) (T' t : E' →ₗ[ℝ] F')).symm
          (V t ⊗ₜ V' t)
    else 0
  exact ⟨W, IsDetLineCoherentOn.prodMap hT hT' hF hF' hV hV' fun t ht _ _ _ _ ↦ dite_eq_left ht,
    dite_eq_left left_mem_uIcc, dite_eq_left right_mem_uIcc⟩

end Transport

end Coherent

end TauCeti
