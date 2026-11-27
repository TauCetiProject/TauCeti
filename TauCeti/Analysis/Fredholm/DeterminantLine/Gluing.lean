/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.DirectSum
import TauCeti.LinearAlgebra.Determinant.Segment

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
