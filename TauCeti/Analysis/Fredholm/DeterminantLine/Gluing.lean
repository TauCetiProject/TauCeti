/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.DirectSum
import TauCeti.LinearAlgebra.Determinant.Segment
import TauCeti.LinearAlgebra.Determinant.ShortExactProd

/-!
# The determinant-line isomorphism of stabilized linear gluing

Linear gluing compares an operator `D` with two pieces `D₁` and `D₂` through finite
stabilizations. Let `ι₁ : S₁ → F₁` and `ι₂ : S₂ → F₂` be finite-dimensional stabilizers making
`D₁.coprod ι₁` and `D₂.coprod ι₂` onto, with stabilized kernels `K₁ = ker (D₁.coprod ι₁)` and
`K₂ = ker (D₂.coprod ι₂)`, and let `j : S₁ × S₂ → F` be a stabilizer of `D` by the product of the
two stabilizing spaces, with `D.coprod j` onto and stabilized kernel `K = ker (D.coprod j)`. The
analytic gluing construction supplies a linear isomorphism `g : K₁ × K₂ ≃ K` of stabilized
kernels. Through the normalized stabilization isomorphisms
`ContinuousLinearMap.detLineStabilizationEquiv`, the determinant lines of the three operators are

`det D₁ ≃ det K₁ ⊗ (det S₁)^*`, `det D₂ ≃ det K₂ ⊗ (det S₂)^*`, `det D ≃ det K ⊗ (det (S₁ × S₂))^*`,

and gathering the factors of the pieces (`TauCeti.detLineTensorDualProdEquiv`) and transporting
the kernel factor along `g` gives the **ordered gluing isomorphism**

`det D₁ ⊗ det D₂ ≃ det D`

(`ContinuousLinearMap.detLineGluingEquiv`). The order `D₁`, `D₂` and `S₁`, `S₂` is part of the
data, and the isomorphism carries the Koszul sign `(-1) ^ (dim S₁ * (dim K₂ + dim S₂))`; its value
on the stabilization isomorphisms of the pieces is
`ContinuousLinearMap.detLineGluingEquiv_detLineStabilizationEquiv_tmul`.

The sign is the one for which gluing with no analytic content is the direct sum. If `D` is the
direct sum `D₁ ⊕ D₂`, stabilized by `ι₁ ⊕ ι₂`, and `g` is the identification of its stabilized
kernel with `K₁ × K₂` (`ContinuousLinearMap.kerCoprodProdMapEquiv`), the gluing isomorphism is the
inverse of the normalized direct sum isomorphism
`(-1) ^ (dim coker D₁ * dim coker D₂) • LinearMap.detLineProdMapEquiv`
(`ContinuousLinearMap.detLineGluingEquiv_kerCoprodProdMapEquiv`), which depends neither on the
stabilizers nor on the sign conventions of the stabilizations. The construction also depends on
the kernel isomorphism `g` only through the determinant of a change of `g`: replacing `g` by
`g'` multiplies it by `det (g⁻¹ ∘ g')` (`ContinuousLinearMap.detLineGluingEquiv_apply_eq_det_smul`).
Over `ℝ`, if the segment between `g` and `g'` consists of isomorphisms, this determinant is
positive (`ContinuousLinearMap.exists_pos_detLineGluingEquiv_apply_eq_smul`), so the transported
orientation does not change. Through `g`, the stabilization sequence of `D` becomes an exact
sequence `0 → ker D → K₁ × K₂ → S₁ × S₂ → coker D → 0`, and the gluing isomorphism is its four-term
isomorphism up to sign
(`ContinuousLinearMap.detLineGluingEquiv_detLineStabilizationEquiv_tmul_eq_detLineFourTermEquiv`).

The isomorphism does not depend on the stabilizers. Enlarge `S₁` and `S₂` along injective maps
`κᵢ : Sᵢ → Sᵢ'` compatible with the stabilizers, and let `g' : K₁' × K₂' ≃ K'` be a kernel
isomorphism for the larger stabilizers which extends `g` along the inclusions of stabilized
kernels and preserves stabilizer components modulo the smaller stabilizers. Then `g` and `g'`
give the same gluing isomorphism
(`ContinuousLinearMap.detLineGluingEquiv_eq_of_kerCoprodMap`). Comparing two stabilizations
through a common enlargement still needs such a compatible `g'` for the enlargement, which is not
constructed here. No sign appears: the Koszul sign
`(-1) ^ (dim S₁ * (dim K₂ + dim S₂))` of the definition changes under the enlargement exactly by
the sign of moving the new directions of `S₁'` past those of the second piece.

## Main definitions

* `ContinuousLinearMap.detLineGluingEquiv`: the ordered isomorphism `det D₁ ⊗ det D₂ ≃ det D`
  induced by an isomorphism `K₁ × K₂ ≃ K` of stabilized kernels.

## Main results

* `ContinuousLinearMap.detLineGluingEquiv_detLineStabilizationEquiv_tmul`: its value on the
  stabilization isomorphisms of the pieces.
* `ContinuousLinearMap.detLineGluingEquiv_apply_eq_det_smul`: changing the kernel isomorphism
  multiplies it by the determinant of the change.
* `ContinuousLinearMap.detLineGluingEquiv_detLineStabilizationEquiv_tmul_eq_detLineFourTermEquiv`:
  it is the four-term isomorphism of the exact sequence
  `0 → ker D → K₁ × K₂ → S₁ × S₂ → coker D → 0` defined by `g`, up to sign.
* `ContinuousLinearMap.detLineGluingEquiv_kerCoprodProdMapEquiv`: for the direct sum and its
  tautological kernel identification it is the inverse of the normalized direct sum isomorphism.
* `ContinuousLinearMap.detLineGluingEquiv_eq_of_kerCoprodMap`: enlarging the stabilizers, with a
  compatible kernel isomorphism, does not change it.
* `ContinuousLinearMap.exists_pos_detLineGluingEquiv_apply_eq_smul`: over `ℝ`, kernel
  isomorphisms joined by a segment of isomorphisms give gluing isomorphisms differing by a
  positive factor.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles and stabilization).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

open Module TensorProduct

namespace ContinuousLinearMap

-- Stabilized kernels `(D₁.coprod D₂).ker` are finite-dimensional when `D₁.ker` and `Λ` are.
attribute [local instance] finiteDimensional_ker_coprod

variable {𝕜 E₁ S₁ F₁ E₂ S₂ F₂ E F : Type*} [Field 𝕜]
  [AddCommGroup E₁] [Module 𝕜 E₁] [TopologicalSpace E₁]
  [AddCommGroup S₁] [Module 𝕜 S₁] [TopologicalSpace S₁]
  [AddCommGroup F₁] [Module 𝕜 F₁] [TopologicalSpace F₁] [ContinuousAdd F₁]
  [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
  [AddCommGroup S₂] [Module 𝕜 S₂] [TopologicalSpace S₂]
  [AddCommGroup F₂] [Module 𝕜 F₂] [TopologicalSpace F₂] [ContinuousAdd F₂]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F]
  {D₁ : E₁ →L[𝕜] F₁} {ι₁ : S₁ →L[𝕜] F₁} {D₂ : E₂ →L[𝕜] F₂} {ι₂ : S₂ →L[𝕜] F₂}
  [FiniteDimensional 𝕜 D₁.ker] [FiniteDimensional 𝕜 S₁]
  [FiniteDimensional 𝕜 D₂.ker] [FiniteDimensional 𝕜 S₂]

section Gluing

variable {D : E →L[𝕜] F} {j : S₁ × S₂ →L[𝕜] F}

/-- **The ordered determinant-line isomorphism of stabilized linear gluing.** Let `D₁.coprod ι₁`
and `D₂.coprod ι₂` be onto, with finite-dimensional stabilizing spaces `S₁` and `S₂` and
stabilized kernels `K₁ = ker (D₁.coprod ι₁)` and `K₂ = ker (D₂.coprod ι₂)`, and let `D.coprod j`
be onto for a stabilizer `j` of `D` by `S₁ × S₂`. An isomorphism `g : K₁ × K₂ ≃ K` onto the
stabilized kernel `K = ker (D.coprod j)` of `D` induces

`det D₁ ⊗ det D₂ ≃ det D`:

read `det Dᵢ` as `det Kᵢ ⊗ (det Sᵢ)^*` by the normalized stabilization isomorphisms
(`ContinuousLinearMap.detLineStabilizationEquiv`), gather the two factors into
`det (K₁ × K₂) ⊗ (det (S₁ × S₂))^*` (`TauCeti.detLineTensorDualProdEquiv`), transport the kernel
factor along `g`, read the result as `det D`, and multiply by the Koszul sign
`(-1) ^ (dim S₁ * (dim K₂ + dim S₂))`. The sign makes the direct sum with its tautological kernel
identification glue to the normalized direct sum isomorphism
(`ContinuousLinearMap.detLineGluingEquiv_kerCoprodProdMapEquiv`). The kernel of `D` is
finite-dimensional, since `g` makes the stabilized kernel of `D` finite-dimensional. -/
noncomputable def detLineGluingEquiv (h₁ : Function.Surjective (D₁.coprod ι₁))
    (h₂ : Function.Surjective (D₂.coprod ι₂)) (h : Function.Surjective (D.coprod j))
    (g : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) ≃ₗ[𝕜] (D.coprod j).ker) :
    (D₁ : E₁ →ₗ[𝕜] F₁).detLine ⊗[𝕜] (D₂ : E₂ →ₗ[𝕜] F₂).detLine ≃ₗ[𝕜]
      (D : E →ₗ[𝕜] F).detLine :=
  haveI : FiniteDimensional 𝕜 (D.coprod j).ker := g.finiteDimensional
  haveI := finiteDimensional_ker_of_finiteDimensional_ker_coprod D j
  TensorProduct.congr (detLineStabilizationEquiv D₁ ι₁ h₁).symm
      (detLineStabilizationEquiv D₂ ι₂ h₂).symm ≪≫ₗ
    TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _ ≪≫ₗ
    LinearEquiv.rTensor _ g.detLineCongr ≪≫ₗ
    detLineStabilizationEquiv D j h ≪≫ₗ
    LinearEquiv.smulOfUnit ((-1) ^ (finrank 𝕜 S₁ * (finrank 𝕜 (D₂.coprod ι₂).ker + finrank 𝕜 S₂)))

/-- `ContinuousLinearMap.detLineGluingEquiv` is the composite of the inverse stabilization
isomorphisms of the pieces, the gathering isomorphism `TauCeti.detLineTensorDualProdEquiv`, the
transport along `g`, the stabilization isomorphism of `D` and the Koszul sign. -/
theorem detLineGluingEquiv_def [FiniteDimensional 𝕜 D.ker] (h₁ : Function.Surjective (D₁.coprod ι₁))
    (h₂ : Function.Surjective (D₂.coprod ι₂)) (h : Function.Surjective (D.coprod j))
    (g : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) ≃ₗ[𝕜] (D.coprod j).ker) :
    detLineGluingEquiv h₁ h₂ h g =
      TensorProduct.congr (detLineStabilizationEquiv D₁ ι₁ h₁).symm
          (detLineStabilizationEquiv D₂ ι₂ h₂).symm ≪≫ₗ
        TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _ ≪≫ₗ
        LinearEquiv.rTensor _ g.detLineCongr ≪≫ₗ
        detLineStabilizationEquiv D j h ≪≫ₗ
        LinearEquiv.smulOfUnit
          ((-1) ^ (finrank 𝕜 S₁ * (finrank 𝕜 (D₂.coprod ι₂).ker + finrank 𝕜 S₂))) :=
  (rfl)

/-- **The gluing isomorphism on stabilizations of the pieces.** For `x₁` in
`det K₁ ⊗ (det S₁)^*` and `x₂` in `det K₂ ⊗ (det S₂)^*`, the gluing isomorphism sends the tensor
product of their images in `det D₁` and `det D₂` to the image in `det D` of their product
(`TauCeti.detLineTensorDualProdEquiv`) transported along `g`, times
`(-1) ^ (dim S₁ * (dim K₂ + dim S₂))`. -/
theorem detLineGluingEquiv_detLineStabilizationEquiv_tmul [FiniteDimensional 𝕜 D.ker]
    (h₁ : Function.Surjective (D₁.coprod ι₁)) (h₂ : Function.Surjective (D₂.coprod ι₂))
    (h : Function.Surjective (D.coprod j))
    (g : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) ≃ₗ[𝕜] (D.coprod j).ker)
    (x₁ : TauCeti.detLine 𝕜 (D₁.coprod ι₁).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 S₁))
    (x₂ : TauCeti.detLine 𝕜 (D₂.coprod ι₂).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 S₂)) :
    detLineGluingEquiv h₁ h₂ h g
        (detLineStabilizationEquiv D₁ ι₁ h₁ x₁ ⊗ₜ detLineStabilizationEquiv D₂ ι₂ h₂ x₂) =
      (-1 : 𝕜) ^ (finrank 𝕜 S₁ * (finrank 𝕜 (D₂.coprod ι₂).ker + finrank 𝕜 S₂)) •
        detLineStabilizationEquiv D j h (LinearEquiv.rTensor _ g.detLineCongr
          (TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _ (x₁ ⊗ₜ x₂))) := by
  simp [detLineGluingEquiv_def, LinearEquiv.smulOfUnit, Units.smul_def]

/-- **Changing the kernel isomorphism.** Replacing the isomorphism `g : K₁ × K₂ ≃ K` of stabilized
kernels by `g'` multiplies the gluing isomorphism by the determinant of the automorphism
`g⁻¹ ∘ g'` of `K₁ × K₂`. Over `ℝ`, two kernel isomorphisms therefore induce the same orientation
transport exactly when this determinant is positive. -/
theorem detLineGluingEquiv_apply_eq_det_smul (h₁ : Function.Surjective (D₁.coprod ι₁))
    (h₂ : Function.Surjective (D₂.coprod ι₂)) (h : Function.Surjective (D.coprod j))
    (g g' : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) ≃ₗ[𝕜] (D.coprod j).ker)
    (t : (D₁ : E₁ →ₗ[𝕜] F₁).detLine ⊗[𝕜] (D₂ : E₂ →ₗ[𝕜] F₂).detLine) :
    detLineGluingEquiv h₁ h₂ h g' t =
      LinearMap.det (g'.trans g.symm).toLinearMap •
        detLineGluingEquiv h₁ h₂ h g t := by
  have : FiniteDimensional 𝕜 (D.coprod j).ker := g.finiteDimensional
  have := finiteDimensional_ker_of_finiteDimensional_ker_coprod D j
  -- On the determinant line of `K₁ × K₂`, transport along `g'` is transport along the
  -- automorphism `g⁻¹ ∘ g'`, which is multiplication by its determinant, followed by `g`.
  have hg : ∀ y, LinearEquiv.rTensor (Dual 𝕜 (TauCeti.detLine 𝕜 (S₁ × S₂))) g'.detLineCongr y =
      LinearMap.det (g'.trans g.symm).toLinearMap •
        LinearEquiv.rTensor (Dual 𝕜 (TauCeti.detLine 𝕜 (S₁ × S₂))) g.detLineCongr y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul a φ =>
      have ha := congrArg g.detLineCongr
        (LinearEquiv.detLineCongr_apply_eq_det_smul (g'.trans g.symm) a)
      rw [LinearEquiv.detLineCongr_trans, LinearEquiv.trans_apply, map_smul,
        ← LinearEquiv.detLineCongr_symm, LinearEquiv.apply_symm_apply] at ha
      rw [LinearEquiv.rTensor_tmul, LinearEquiv.rTensor_tmul, ha, smul_tmul']
    | add y y' hy hy' => rw [map_add, map_add, hy, hy', smul_add]
  simp only [detLineGluingEquiv_def, LinearEquiv.trans_apply, hg, map_smul]

/-- **The gluing isomorphism and the exact sequence of gluing.** Let `fK : ker D → K₁ × K₂` and
`b : K₁ × K₂ → S₁ × S₂` be the maps through which `g` identifies the stabilization sequence
`0 → ker D → K → S₁ × S₂ → coker D → 0` of `D` with an exact sequence

`0 → ker D → K₁ × K₂ → S₁ × S₂ → coker D → 0`:

`g ∘ fK` is the inclusion of `ker D` and `b` is the stabilizer component of `g`. Then the gluing
isomorphism, on the stabilization isomorphisms of the pieces, is the four-term isomorphism
(`TauCeti.detLineFourTermEquiv`) of this sequence applied to the product of `x₁` and `x₂`, times
the sign `(-1) ^ (dim S₁ * (dim K₂ + dim S₂) + dim coker D * dim (S₁ × S₂))`. -/
theorem detLineGluingEquiv_detLineStabilizationEquiv_tmul_eq_detLineFourTermEquiv
    [FiniteDimensional 𝕜 D.ker] (h₁ : Function.Surjective (D₁.coprod ι₁))
    (h₂ : Function.Surjective (D₂.coprod ι₂)) (h : Function.Surjective (D.coprod j))
    (g : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) ≃ₗ[𝕜] (D.coprod j).ker)
    {fK : D.ker →ₗ[𝕜] (D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker}
    {b : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) →ₗ[𝕜] S₁ × S₂}
    (hfK : ∀ v, g (fK v) = kerCoprodHom D j v) (hb : ∀ k, b k = parameterProj D j (g k))
    (hf : Function.Injective fK) (hfb : Function.Exact fK b)
    (hbc : Function.Exact b (parameterToCoker D j))
    (x₁ : TauCeti.detLine 𝕜 (D₁.coprod ι₁).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 S₁))
    (x₂ : TauCeti.detLine 𝕜 (D₂.coprod ι₂).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 S₂)) :
    detLineGluingEquiv h₁ h₂ h g
        (detLineStabilizationEquiv D₁ ι₁ h₁ x₁ ⊗ₜ detLineStabilizationEquiv D₂ ι₂ h₂ x₂) =
      (-1 : 𝕜) ^ (finrank 𝕜 S₁ * (finrank 𝕜 (D₂.coprod ι₂).ker + finrank 𝕜 S₂) +
          finrank 𝕜 (F ⧸ D.range) * finrank 𝕜 (S₁ × S₂)) •
        TauCeti.detLineFourTermEquiv hf hfb hbc
          ((parameterToCoker_surjective_iff_coprod_surjective D j).2 h)
          (TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _ (x₁ ⊗ₜ x₂)) := by
  -- `g` is an isomorphism from the given sequence to the stabilization sequence of `D`.
  have hcongr := TauCeti.detLineFourTermEquiv_congr hf hfb hbc
    ((parameterToCoker_surjective_iff_coprod_surjective D j).2 h)
    (kerCoprodHom_injective D j) (exact_kerCoprodHom_parameterProj D j)
    (exact_parameterProj_parameterToCoker D j)
    ((parameterToCoker_surjective_iff_coprod_surjective D j).2 h)
    (LinearEquiv.refl 𝕜 _) g (LinearEquiv.refl 𝕜 _) (LinearEquiv.refl 𝕜 _)
    (LinearMap.ext fun v ↦ (hfK v).symm) (LinearMap.ext fun k ↦ (hb k).symm) rfl
    (TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _ (x₁ ⊗ₜ x₂))
  simp only [LinearEquiv.detLineCongr_refl, LinearEquiv.refl_symm, LinearEquiv.dualMap_refl,
    TensorProduct.congr_refl_refl, LinearEquiv.refl_apply] at hcongr
  -- `LinearEquiv.rTensor` is by definition `TensorProduct.congr` with the identity on the right.
  have hr : TensorProduct.congr g.detLineCongr (LinearEquiv.refl 𝕜 _) =
      LinearEquiv.rTensor (Dual 𝕜 (TauCeti.detLine 𝕜 (S₁ × S₂))) g.detLineCongr := rfl
  rw [hr] at hcongr
  rw [detLineGluingEquiv_detLineStabilizationEquiv_tmul, detLineStabilizationEquiv_apply,
    detLineCoprodEquiv_def, smul_smul, ← pow_add, hcongr]

section ChangeOfStabilizer

/-! ### Changing the stabilizers -/

/-- The sign bookkeeping of a change of stabilizers: with `dim Sᵢ' = sᵢ + qᵢ` and
`dim K₂' = k₂ + q₂`, the Koszul and four-term signs of the larger stabilizers are those of the
smaller ones times the signs of the cancellations, since the exponents differ by
`2 * q₂ * (s₁ + q₁)`. -/
private theorem neg_one_pow_stabilizerChange {R : Type*} [Monoid R] [HasDistribNeg R]
    (s₁ q₁ k₂ s₂ q₂ c : ℕ) :
    (-1 : R) ^ ((s₁ + q₁) * (k₂ + q₂ + (s₂ + q₂)) + c * (s₁ + q₁ + (s₂ + q₂))) =
      (-1) ^ (s₁ * (k₂ + s₂) + c * (s₁ + s₂)) *
        ((-1) ^ ((k₂ + s₂) * q₁) * (-1) ^ (c * (q₁ + q₂))) := by
  rw [← pow_add, ← pow_add, show (s₁ + q₁) * (k₂ + q₂ + (s₂ + q₂)) + c * (s₁ + q₁ + (s₂ + q₂)) =
    s₁ * (k₂ + s₂) + c * (s₁ + s₂) + ((k₂ + s₂) * q₁ + c * (q₁ + q₂)) + 2 * (q₂ * (s₁ + q₁)) by
    ring, pow_add _ _ (2 * _), pow_mul, neg_one_sq, one_pow, mul_one]

omit [FiniteDimensional 𝕜 D₁.ker] [FiniteDimensional 𝕜 S₁] [FiniteDimensional 𝕜 D₂.ker]
  [FiniteDimensional 𝕜 S₂] in
/-- Through an isomorphism `g : K₁ × K₂ ≃ K` of stabilized kernels, the stabilization sequence
`0 → ker D → K → S₁ × S₂ → coker D → 0` of `D` becomes an exact sequence
`0 → ker D → K₁ × K₂ → S₁ × S₂ → coker D → 0`. -/
private theorem exact_symm_comp_kerCoprodHom
    (g : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) ≃ₗ[𝕜] (D.coprod j).ker) :
    Function.Injective (g.symm.toLinearMap ∘ₗ (kerCoprodHom D j : D.ker →ₗ[𝕜] (D.coprod j).ker)) ∧
      Function.Exact (g.symm.toLinearMap ∘ₗ (kerCoprodHom D j : D.ker →ₗ[𝕜] (D.coprod j).ker))
        ((parameterProj D j : (D.coprod j).ker →ₗ[𝕜] S₁ × S₂) ∘ₗ g.toLinearMap) ∧
      Function.Exact ((parameterProj D j : (D.coprod j).ker →ₗ[𝕜] S₁ × S₂) ∘ₗ g.toLinearMap)
        (parameterToCoker D j) :=
  ⟨g.symm.injective.comp (kerCoprodHom_injective D j),
    (LinearEquiv.conj_symm_exact_iff_exact _ _ g).2 (exact_kerCoprodHom_parameterProj D j),
    LinearEquiv.precomp_exact_iff_exact.2 (exact_parameterProj_parameterToCoker D j)⟩

variable {S₁' S₂' : Type*} [AddCommGroup S₁'] [Module 𝕜 S₁'] [TopologicalSpace S₁']
  [AddCommGroup S₂'] [Module 𝕜 S₂'] [TopologicalSpace S₂'] [FiniteDimensional 𝕜 S₁']
  [FiniteDimensional 𝕜 S₂'] {ι₁' : S₁' →L[𝕜] F₁} {ι₂' : S₂' →L[𝕜] F₂}
  {κ₁ : S₁ →ₗ[𝕜] S₁'} {κ₂ : S₂ →ₗ[𝕜] S₂'} {j' : S₁' × S₂' →L[𝕜] F}

omit [TopologicalSpace S₁] [ContinuousAdd F] [TopologicalSpace S₁'] in
/-- The signs of a change of stabilizers, in terms of the dimensions of `Sᵢ`, `Sᵢ'`, `K₂`, `K₂'`
and `coker D`: since `dim Sᵢ' = dim Sᵢ + dim Qᵢ` and `dim K₂' = dim K₂ + dim Q₂` for
`Qᵢ = Sᵢ' ⧸ range κᵢ`, this is `neg_one_pow_stabilizerChange`. -/
private theorem neg_one_pow_finrank_stabilizerChange (h₂ : Function.Surjective (D₂.coprod ι₂))
    (hκ₂ : ∀ l, ι₂' (κ₂ l) = ι₂ l) (hκ₁' : Function.Injective κ₁)
    (hκ₂' : Function.Injective κ₂) :
    (-1 : 𝕜) ^ (finrank 𝕜 S₁' * (finrank 𝕜 (D₂.coprod ι₂').ker + finrank 𝕜 S₂') +
        finrank 𝕜 (F ⧸ D.range) * finrank 𝕜 (S₁' × S₂')) =
      (-1) ^ (finrank 𝕜 S₁ * (finrank 𝕜 (D₂.coprod ι₂).ker + finrank 𝕜 S₂) +
          finrank 𝕜 (F ⧸ D.range) * finrank 𝕜 (S₁ × S₂)) *
        ((-1) ^ ((finrank 𝕜 (D₂.coprod ι₂).ker + finrank 𝕜 S₂) *
            finrank 𝕜 (S₁' ⧸ LinearMap.range κ₁)) *
          (-1) ^ (finrank 𝕜 (F ⧸ D.range) *
            finrank 𝕜 ((S₁' ⧸ LinearMap.range κ₁) × (S₂' ⧸ LinearMap.range κ₂)))) := by
  rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_prod,
    (LinearMap.exact_map_mkQ_range κ₁).finrank_eq_add hκ₁' (Submodule.mkQ_surjective _),
    (LinearMap.exact_map_mkQ_range κ₂).finrank_eq_add hκ₂' (Submodule.mkQ_surjective _),
    (exact_kerCoprodMap hκ₂).finrank_eq_add (kerCoprodMap_injective hκ₂ hκ₂')
      (surjective_mkQ_comp_parameterProj hκ₂ h₂)]
  exact neg_one_pow_stabilizerChange _ _ _ _ _ _

/-- The four-term isomorphisms of the gluing sequences
`0 → ker D → K₁ × K₂ → S₁ × S₂ → coker D → 0` and `0 → ker D → K₁' × K₂' → S₁' × S₂' → coker D → 0`
of a stabilizer change, evaluated on the gathered stabilized data of the pieces, agree up to the
signs of cancelling `Q₁ = S₁' ⧸ range κ₁` and `Q₂ = S₂' ⧸ range κ₂`: the gathered change of
stabilizer of the pieces is the cancellation of `Q₁ × Q₂`
(`TauCeti.detLineShortExactCancelEquiv_prodMap`), which relates the two four-term isomorphisms
(`TauCeti.detLineFourTermEquiv_detLineShortExactCancelEquiv`). -/
private theorem detLineFourTermEquiv_detLineCoprodMapEquiv_tmul [FiniteDimensional 𝕜 D.ker]
    (h₁ : Function.Surjective (D₁.coprod ι₁)) (h₂ : Function.Surjective (D₂.coprod ι₂))
    (h : Function.Surjective (D.coprod j)) (hκ₁ : ∀ l, ι₁' (κ₁ l) = ι₁ l)
    (hκ₂ : ∀ l, ι₂' (κ₂ l) = ι₂ l) (hκ : ∀ l, j' (κ₁.prodMap κ₂ l) = j l)
    (hκ₁' : Function.Injective κ₁) (hκ₂' : Function.Injective κ₂)
    {fK : D.ker →ₗ[𝕜] (D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker}
    {b : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) →ₗ[𝕜] S₁ × S₂}
    {fK' : D.ker →ₗ[𝕜] (D₁.coprod ι₁').ker × (D₂.coprod ι₂').ker}
    {b' : ((D₁.coprod ι₁').ker × (D₂.coprod ι₂').ker) →ₗ[𝕜] S₁' × S₂'}
    (hf : Function.Injective fK) (hfb : Function.Exact fK b)
    (hbc : Function.Exact b (parameterToCoker D j)) (hf' : Function.Injective fK')
    (hfb' : Function.Exact fK' b') (hbc' : Function.Exact b' (parameterToCoker D j'))
    (hJf : (kerCoprodMap D₁ hκ₁).prodMap (kerCoprodMap D₂ hκ₂) ∘ₗ fK = fK')
    (hbJ : b' ∘ₗ (kerCoprodMap D₁ hκ₁).prodMap (kerCoprodMap D₂ hκ₂) = κ₁.prodMap κ₂ ∘ₗ b)
    (hb₁ : ∀ k, (b' k).1 - parameterProj D₁ ι₁' k.1 ∈ LinearMap.range κ₁)
    (hb₂ : ∀ k, (b' k).2 - parameterProj D₂ ι₂' k.2 ∈ LinearMap.range κ₂)
    (y₁ : TauCeti.detLine 𝕜 (D₁.coprod ι₁').ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 S₁'))
    (y₂ : TauCeti.detLine 𝕜 (D₂.coprod ι₂').ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 S₂')) :
    TauCeti.detLineFourTermEquiv hf hfb hbc
        ((parameterToCoker_surjective_iff_coprod_surjective D j).2 h)
        (TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _
          (detLineCoprodMapEquiv D₁ hκ₁ hκ₁' h₁ y₁ ⊗ₜ detLineCoprodMapEquiv D₂ hκ₂ hκ₂' h₂ y₂)) =
      ((-1 : 𝕜) ^ ((finrank 𝕜 (D₂.coprod ι₂).ker + finrank 𝕜 S₂) *
          finrank 𝕜 (S₁' ⧸ LinearMap.range κ₁)) *
        (-1) ^ (finrank 𝕜 (F ⧸ D.range) *
          finrank 𝕜 ((S₁' ⧸ LinearMap.range κ₁) × (S₂' ⧸ LinearMap.range κ₂)))) •
        TauCeti.detLineFourTermEquiv hf' hfb' hbc'
          ((parameterToCoker_surjective_iff_coprod_surjective D j').2
            (surjective_coprod_of_comp hκ h))
          (TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _ (y₁ ⊗ₜ y₂)) := by
  -- The exact sequences `0 → K₁ × K₂ → K₁' × K₂' → Q₁ × Q₂ → 0` and
  -- `0 → S₁ × S₂ → S₁' × S₂' → Q₁ × Q₂ → 0`, products of those of the two pieces.
  set J := (kerCoprodMap D₁ hκ₁).prodMap (kerCoprodMap D₂ hκ₂)
  set P := ((LinearMap.range κ₁).mkQ ∘ₗ
      (parameterProj D₁ ι₁' : (D₁.coprod ι₁').ker →ₗ[𝕜] S₁')).prodMap
    ((LinearMap.range κ₂).mkQ ∘ₗ (parameterProj D₂ ι₂' : (D₂.coprod ι₂').ker →ₗ[𝕜] S₂'))
  set π := (LinearMap.range κ₁).mkQ.prodMap (LinearMap.range κ₂).mkQ
  have hJ : Function.Injective J :=
    (kerCoprodMap_injective hκ₁ hκ₁').prodMap (kerCoprodMap_injective hκ₂ hκ₂')
  have hJP : Function.Exact J P := (exact_kerCoprodMap hκ₁).prodMap (exact_kerCoprodMap hκ₂)
  have hP : Function.Surjective P := (surjective_mkQ_comp_parameterProj hκ₁ h₁).prodMap
    (surjective_mkQ_comp_parameterProj hκ₂ h₂)
  have hκι : Function.Injective (κ₁.prodMap κ₂) := hκ₁'.prodMap hκ₂'
  have hκπ : Function.Exact (κ₁.prodMap κ₂) π :=
    (LinearMap.exact_map_mkQ_range κ₁).prodMap (LinearMap.exact_map_mkQ_range κ₂)
  have hπ : Function.Surjective π :=
    (Submodule.mkQ_surjective _).prodMap (Submodule.mkQ_surjective _)
  have hπb : π ∘ₗ b' = P := LinearMap.ext fun k ↦
    Prod.ext ((Submodule.Quotient.eq _).2 (hb₁ k)) ((Submodule.Quotient.eq _).2 (hb₂ k))
  have hjπ : Function.Exact J (π ∘ₗ b') := hπb ▸ hJP
  have hπb' : Function.Surjective (π ∘ₗ b') := hπb ▸ hP
  -- Cancelling `Q₁ × Q₂` depends on the quotient map `π ∘ b'` only through the map `P`.
  have hcancel : ∀ G, G = P → ∀ (h₁ : Function.Exact J G) (h₂ : Function.Surjective G),
      TauCeti.detLineShortExactCancelEquiv hJ h₁ h₂ hκι hκπ hπ =
        TauCeti.detLineShortExactCancelEquiv hJ hJP hP hκι hκπ hπ := by
    rintro _ rfl _ _
    rfl
  -- The gathered changes of stabilizer of the pieces are the cancellation of `Q₁ × Q₂`.
  have hprod := TauCeti.detLineShortExactCancelEquiv_prodMap (kerCoprodMap_injective hκ₁ hκ₁')
    (exact_kerCoprodMap hκ₁) (surjective_mkQ_comp_parameterProj hκ₁ h₁)
    (kerCoprodMap_injective hκ₂ hκ₂') (exact_kerCoprodMap hκ₂)
    (surjective_mkQ_comp_parameterProj hκ₂ h₂) hκ₁' (LinearMap.exact_map_mkQ_range κ₁)
    (Submodule.mkQ_surjective _) hκ₂' (LinearMap.exact_map_mkQ_range κ₂)
    (Submodule.mkQ_surjective _) y₁ y₂
  rw [← detLineCoprodMapEquiv_def hκ₁ hκ₁' h₁, ← detLineCoprodMapEquiv_def hκ₂ hκ₂' h₂] at hprod
  -- Cancelling `Q₁ × Q₂` relates the two four-term isomorphisms. The rewriting is by `simp`:
  -- `rw` here spends its time checking the motive.
  have hmid := TauCeti.detLineFourTermEquiv_detLineShortExactCancelEquiv hf hfb hbc
    ((parameterToCoker_surjective_iff_coprod_surjective D j).2 h) hf' hfb' hbc'
    ((parameterToCoker_surjective_iff_coprod_surjective D j').2 (surjective_coprod_of_comp hκ h))
    hJ hjπ hπb' hκι hκπ hπ hJf hbJ (LinearMap.ext fun l ↦ by
      rw [LinearMap.comp_apply, parameterToCoker_apply, parameterToCoker_apply, hκ])
    (TauCeti.detLineTensorDualProdEquiv 𝕜 (D₁.coprod ι₁').ker S₁' (D₂.coprod ι₂').ker S₂'
      (y₁ ⊗ₜ y₂))
  simp only [hcancel (π ∘ₗ b') hπb hjπ hπb', hprod, LinearEquiv.map_smul] at hmid
  have hmid' := congrArg (fun x ↦ (-1 : 𝕜) ^ ((finrank 𝕜 (D₂.coprod ι₂).ker + finrank 𝕜 S₂) *
      finrank 𝕜 (S₁' ⧸ LinearMap.range κ₁)) • x) hmid
  simpa only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul] using hmid'

/-- **The gluing isomorphism does not depend on the stabilizers.** Enlarge the stabilizers along
injective maps `κ₁ : S₁ → S₁'` and `κ₂ : S₂ → S₂'` with `ι₁' ∘ κ₁ = ι₁`, `ι₂' ∘ κ₂ = ι₂` and
`j' ∘ (κ₁ × κ₂) = j`, so that the stabilized kernels `K₁ × K₂` and `K` embed in `K₁' × K₂'` and
`K'` by `(x, l) ↦ (x, κ l)` (`ContinuousLinearMap.kerCoprodMap`). Let `g' : K₁' × K₂' ≃ K'` be a
kernel isomorphism extending `g` along these inclusions whose stabilizer components agree with
those of its argument modulo the smaller stabilizers. Then `g'` and `g` induce the same gluing
isomorphism `det D₁ ⊗ det D₂ ≃ det D`. -/
theorem detLineGluingEquiv_eq_of_kerCoprodMap (h₁ : Function.Surjective (D₁.coprod ι₁))
    (h₂ : Function.Surjective (D₂.coprod ι₂)) (h : Function.Surjective (D.coprod j))
    (hκ₁ : ∀ l, ι₁' (κ₁ l) = ι₁ l) (hκ₂ : ∀ l, ι₂' (κ₂ l) = ι₂ l)
    (hκ : ∀ l, j' (κ₁.prodMap κ₂ l) = j l) (hκ₁' : Function.Injective κ₁)
    (hκ₂' : Function.Injective κ₂)
    (g : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) ≃ₗ[𝕜] (D.coprod j).ker)
    (g' : ((D₁.coprod ι₁').ker × (D₂.coprod ι₂').ker) ≃ₗ[𝕜] (D.coprod j').ker)
    (hg : ∀ k₁ k₂, g' (kerCoprodMap D₁ hκ₁ k₁, kerCoprodMap D₂ hκ₂ k₂) =
      kerCoprodMap D hκ (g (k₁, k₂)))
    (hg₁ : ∀ k, (parameterProj D j' (g' k)).1 - parameterProj D₁ ι₁' k.1 ∈ LinearMap.range κ₁)
    (hg₂ : ∀ k, (parameterProj D j' (g' k)).2 - parameterProj D₂ ι₂' k.2 ∈ LinearMap.range κ₂) :
    detLineGluingEquiv (surjective_coprod_of_comp hκ₁ h₁) (surjective_coprod_of_comp hκ₂ h₂)
        (surjective_coprod_of_comp hκ h) g' = detLineGluingEquiv h₁ h₂ h g := by
  have : FiniteDimensional 𝕜 (D.coprod j).ker := g.finiteDimensional
  have := finiteDimensional_ker_of_finiteDimensional_ker_coprod D j
  -- Through `g` and `g'`, the stabilization sequences of `D` become the four-term exact sequences
  -- `0 → ker D → K₁ × K₂ → S₁ × S₂ → coker D → 0` and its analogue for the larger stabilizers,
  -- and the inclusions of stabilized kernels and stabilizers map the first to the second.
  set fK := g.symm.toLinearMap ∘ₗ (kerCoprodHom D j : D.ker →ₗ[𝕜] (D.coprod j).ker)
  set b := (parameterProj D j : (D.coprod j).ker →ₗ[𝕜] S₁ × S₂) ∘ₗ g.toLinearMap
  set fK' := g'.symm.toLinearMap ∘ₗ (kerCoprodHom D j' : D.ker →ₗ[𝕜] (D.coprod j').ker)
  set b' := (parameterProj D j' : (D.coprod j').ker →ₗ[𝕜] S₁' × S₂') ∘ₗ g'.toLinearMap
  obtain ⟨hf, hfb, hbc⟩ := exact_symm_comp_kerCoprodHom g
  obtain ⟨hf', hfb', hbc'⟩ := exact_symm_comp_kerCoprodHom g'
  have hJf : (kerCoprodMap D₁ hκ₁).prodMap (kerCoprodMap D₂ hκ₂) ∘ₗ fK = fK' := by
    refine LinearMap.ext fun v ↦ g'.injective ?_
    have hv := hg (g.symm (kerCoprodHom D j v)).1 (g.symm (kerCoprodHom D j v)).2
    rw [Prod.mk.eta, LinearEquiv.apply_symm_apply] at hv
    simp only [fK, fK', LinearMap.comp_apply, LinearMap.prodMap_apply, LinearEquiv.coe_coe,
      coe_coe, LinearEquiv.apply_symm_apply]
    rw [hv]
    exact Subtype.ext (by simp [coe_kerCoprodMap, kerCoprodHom_apply])
  have hbJ : b' ∘ₗ (kerCoprodMap D₁ hκ₁).prodMap (kerCoprodMap D₂ hκ₂) = κ₁.prodMap κ₂ ∘ₗ b := by
    refine LinearMap.ext fun k ↦ ?_
    simp only [b, b', LinearMap.comp_apply, LinearMap.prodMap_apply, LinearEquiv.coe_coe,
      hg k.1 k.2]
    simp [parameterProj_apply, coe_kerCoprodMap]
  -- Both gluing isomorphisms are four-term isomorphisms of these sequences, up to sign, and the
  -- stabilization isomorphisms of the pieces are compatible with the changes of stabilizer.
  refine LinearEquiv.ext fun t ↦ ?_
  induction t using TensorProduct.inductionOn with
  | add t t' ht ht' => rw [map_add, map_add, ht, ht']
  | tmul a₁ a₂ =>
  obtain ⟨y₁, rfl⟩ :=
    (detLineStabilizationEquiv D₁ ι₁' (surjective_coprod_of_comp hκ₁ h₁)).surjective a₁
  obtain ⟨y₂, rfl⟩ :=
    (detLineStabilizationEquiv D₂ ι₂' (surjective_coprod_of_comp hκ₂ h₂)).surjective a₂
  have hR := detLineGluingEquiv_detLineStabilizationEquiv_tmul_eq_detLineFourTermEquiv h₁ h₂ h
    g (fK := fK) (b := b) (fun v ↦ by simp [fK]) (fun _ ↦ rfl) hf hfb hbc
    (detLineCoprodMapEquiv D₁ hκ₁ hκ₁' h₁ y₁) (detLineCoprodMapEquiv D₂ hκ₂ hκ₂' h₂ y₂)
  rw [detLineStabilizationEquiv_detLineCoprodMapEquiv,
    detLineStabilizationEquiv_detLineCoprodMapEquiv] at hR
  rw [detLineGluingEquiv_detLineStabilizationEquiv_tmul_eq_detLineFourTermEquiv
    (surjective_coprod_of_comp hκ₁ h₁) (surjective_coprod_of_comp hκ₂ h₂)
    (surjective_coprod_of_comp hκ h) g' (fK := fK') (b := b') (fun v ↦ by simp [fK'])
    (fun _ ↦ rfl) hf' hfb' hbc', hR, detLineFourTermEquiv_detLineCoprodMapEquiv_tmul h₁ h₂ h hκ₁
    hκ₂ hκ hκ₁' hκ₂' hf hfb hbc hf' hfb' hbc' hJf hbJ hg₁ hg₂, smul_smul]
  exact congrArg (· • _) (neg_one_pow_finrank_stabilizerChange h₂ hκ₂ hκ₁' hκ₂')

end ChangeOfStabilizer

end Gluing

section Real

variable {E₁ S₁ F₁ E₂ S₂ F₂ E F : Type*}
  [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [AddCommGroup S₁] [Module ℝ S₁] [TopologicalSpace S₁]
  [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁] [ContinuousAdd F₁]
  [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [AddCommGroup S₂] [Module ℝ S₂] [TopologicalSpace S₂]
  [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂] [ContinuousAdd F₂]
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ContinuousAdd F]
  {D₁ : E₁ →L[ℝ] F₁} {ι₁ : S₁ →L[ℝ] F₁} {D₂ : E₂ →L[ℝ] F₂} {ι₂ : S₂ →L[ℝ] F₂}
  {D : E →L[ℝ] F} {j : S₁ × S₂ →L[ℝ] F}
  [FiniteDimensional ℝ D₁.ker] [FiniteDimensional ℝ S₁]
  [FiniteDimensional ℝ D₂.ker] [FiniteDimensional ℝ S₂]

/-- **Kernel isomorphisms joined by a segment of isomorphisms glue to the same orientation.** If
every point `(1 - s) • g + s • g'`, `s ∈ [0, 1]`, of the segment between two isomorphisms
`g g' : K₁ × K₂ ≃ K` of stabilized kernels is bijective, the gluing isomorphisms along `g` and
`g'` differ by a positive factor, so they carry orientations of `det D₁ ⊗ det D₂` to the same
orientation of `det D`. -/
theorem exists_pos_detLineGluingEquiv_apply_eq_smul (h₁ : Function.Surjective (D₁.coprod ι₁))
    (h₂ : Function.Surjective (D₂.coprod ι₂)) (h : Function.Surjective (D.coprod j))
    (g g' : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) ≃ₗ[ℝ] (D.coprod j).ker)
    (hg : ∀ s ∈ Set.Icc (0 : ℝ) 1, Function.Bijective
      ((1 - s) • g.toLinearMap + s • g'.toLinearMap :
        ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) →ₗ[ℝ] (D.coprod j).ker)) :
    ∃ c : ℝ, 0 < c ∧ ∀ t, detLineGluingEquiv h₁ h₂ h g' t = c • detLineGluingEquiv h₁ h₂ h g t :=
  ⟨_, LinearEquiv.det_trans_symm_pos_of_forall_bijective g g' hg,
    detLineGluingEquiv_apply_eq_det_smul h₁ h₂ h g g'⟩

end Real

section DirectSum

variable [FiniteDimensional 𝕜 (F₁ ⧸ D₁.range)] [FiniteDimensional 𝕜 (F₂ ⧸ D₂.range)]

/-- **Gluing a direct sum.** Stabilize the direct sum `D₁ ⊕ D₂` by `ι₁ ⊕ ι₂`, and identify its
stabilized kernel with `K₁ × K₂` tautologically (`ContinuousLinearMap.kerCoprodProdMapEquiv`).
Then the gluing isomorphism is the inverse of the normalized direct sum isomorphism
`(-1) ^ (dim coker D₁ * dim coker D₂) • LinearMap.detLineProdMapEquiv`, which does not depend on
the stabilizers. -/
theorem detLineGluingEquiv_kerCoprodProdMapEquiv (h₁ : Function.Surjective (D₁.coprod ι₁))
    (h₂ : Function.Surjective (D₂.coprod ι₂))
    (t : (D₁ : E₁ →ₗ[𝕜] F₁).detLine ⊗[𝕜] (D₂ : E₂ →ₗ[𝕜] F₂).detLine) :
    detLineGluingEquiv h₁ h₂ (surjective_coprod_prodMap h₁ h₂)
        (kerCoprodProdMapEquiv D₁ ι₁ D₂ ι₂) t =
      (-1 : 𝕜) ^ (finrank 𝕜 (F₁ ⧸ D₁.range) * finrank 𝕜 (F₂ ⧸ D₂.range)) •
        (LinearMap.detLineProdMapEquiv (D₁ : E₁ →ₗ[𝕜] F₁) (D₂ : E₂ →ₗ[𝕜] F₂)).symm t := by
  -- The Koszul sign of the gluing isomorphism agrees with the stabilizer-dependent part of the
  -- sign in `ContinuousLinearMap.detLineStabilizationEquiv_prodMap`: the two exponents differ by
  -- `2 * dim S₁ * dim (range p)` for the parameter projection `p` of `D₂.coprod ι₂`.
  have hsign : (-1 : 𝕜) ^ (finrank 𝕜 S₁ * (finrank 𝕜 (D₂.coprod ι₂).ker + finrank 𝕜 S₂)) =
      (-1 : 𝕜) ^ (finrank 𝕜 S₁ * (finrank 𝕜 D₂.ker + finrank 𝕜 (F₂ ⧸ D₂.range))) := by
    have hk := finrank_ker_add_finrank_range_parameterProj D₂ ι₂
    have hc := finrank_range_parameterProj_add_finrank_quotient_range D₂ ι₂ h₂
    have hdim : finrank 𝕜 (D₂.coprod ι₂).ker + finrank 𝕜 S₂ = finrank 𝕜 D₂.ker +
        finrank 𝕜 (F₂ ⧸ D₂.range) + 2 * finrank 𝕜 (parameterProj D₂ ι₂).range := by
      omega
    exact neg_one_pow_congr (by simp [hdim, parity_simps])
  -- Both cases end in `rfl`: the two sides live in the determinant lines of the coerced direct sum
  -- `↑(D₁.prodMap D₂)` and of `(↑D₁).prodMap ↑D₂`, which agree by definition but not reducibly.
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => rw [map_add, map_add, hs, ht, smul_add]; rfl
  | tmul a b =>
    obtain ⟨x₁, rfl⟩ := (detLineStabilizationEquiv D₁ ι₁ h₁).surjective a
    obtain ⟨x₂, rfl⟩ := (detLineStabilizationEquiv D₂ ι₂ h₂).surjective b
    rw [detLineGluingEquiv_detLineStabilizationEquiv_tmul,
      detLineStabilizationEquiv_prodMap h₁ h₂ x₁ x₂, hsign]
    refine (smul_smul _ _ _).trans ?_
    rw [← pow_add, neg_one_pow_congr (n := finrank 𝕜 (F₁ ⧸ D₁.range) * finrank 𝕜 (F₂ ⧸ D₂.range))
      (by simp only [Nat.even_add]; tauto)]
    rfl

end DirectSum

end ContinuousLinearMap
