/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Basic
public import TauCeti.LinearAlgebra.Determinant.DirectSum
import TauCeti.Topology.Algebra.Module.Determinant

/-!
# The determinant line of a glued operator

Linear gluing compares an operator `D` with two operators `D₁ : E₁ → F₁` and `D₂ : E₂ → F₂`
through their stabilizations. Let `ι₁ : Λ₁ → F₁` and `ι₂ : Λ₂ → F₂` be finite-dimensional
stabilizers making `A₁ = D₁.coprod ι₁` and `A₂ = D₂.coprod ι₂` onto, with kernels `E₁'` and `E₂'`,
and let `j : Λ₁ × Λ₂ → F` make `A = D.coprod j` onto, with kernel `E'`. A **gluing isomorphism**
of the stabilized kernels is a linear isomorphism `g : E₁' × E₂' ≃ E'`. For first-order operators
on a cylinder glued along a long neck, `g` is the corrected pregluing map
(`TauCeti.CylinderSobolev.gluingKerMap`), and its existence is the analytic content of linear
gluing. This file builds from such a `g` the **ordered determinant-line isomorphism**

`det D ≃ det D₁ ⊗ det D₂`

(`ContinuousLinearMap.detLineGluingEquiv`), with `det D = det (ker D) ⊗ (det (coker D))^*`. It is
the composite of

* the inverse of the normalized stabilization isomorphism of `D`,
  `det D ≃ det E' ⊗ (det (Λ₁ × Λ₂))^*` (`ContinuousLinearMap.detLineStabilizationEquiv`);
* the isomorphism induced by `g⁻¹` on `det E'`;
* the splitting of `det (E₁' × E₂') ⊗ (det (Λ₁ × Λ₂))^*` as
  `(det E₁' ⊗ (det Λ₁)^*) ⊗ (det E₂' ⊗ (det Λ₂)^*)` by `TauCeti.detLineTensorDualProdEquiv`, which
  gathers the factors in the order `D₁`, `D₂` and `Λ₁`, `Λ₂`, with no sign;
* the normalized stabilization isomorphisms of `D₁` and `D₂`.

So it is characterized by sending the stabilization of the image of `x₁ ⊗ x₂` under `g` to the
tensor product of the stabilizations of `x₁` and `x₂`
(`ContinuousLinearMap.detLineGluingEquiv_detLineStabilizationEquiv`). It does not presuppose any
splitting of the kernel or the cokernel of `D`, which need not be the direct sums of those of
`D₁` and `D₂`: a kernel direction of one piece can cancel against a cokernel direction of the
other.

The isomorphism depends on `g` only through a scalar: for two gluing isomorphisms `g` and `g'`,
the two determinant-line isomorphisms differ by the determinant of the automorphism `g'⁻¹ ∘ g`
of `E₁' × E₂'` (`ContinuousLinearMap.detLineGluingEquiv_apply_eq_det_smul`). Over `ℝ` this
determinant is positive when `g` and `g'` are joined by a segment of gluing isomorphisms
(`ContinuousLinearMap.exists_pos_detLineGluingEquiv_eq_smul_of_forall_bijective`), so the
orientations of `det D` and of `det D₁ ⊗ det D₂` it relates do not depend on the choice of `g`
within such a family.

## Main definitions

* `ContinuousLinearMap.detLineGluingEquiv`: the isomorphism `det D ≃ det D₁ ⊗ det D₂` of a
  gluing isomorphism of stabilized kernels.

## Main results

* `ContinuousLinearMap.detLineGluingEquiv_detLineStabilizationEquiv`: its value on
  stabilizations of products.
* `ContinuousLinearMap.detLineGluingEquiv_apply_eq_det_smul`: changing the gluing isomorphism
  multiplies it by a determinant.
* `ContinuousLinearMap.exists_pos_detLineGluingEquiv_eq_smul_of_forall_bijective`: over `ℝ`,
  gluing isomorphisms joined by a segment of isomorphisms give the same orientation.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section A.2
  (determinant line bundles and their stabilization) and Section 10.6 (gluing and the
  orientation of moduli spaces).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. **118** (2016), 203--268, arXiv:1304.6368 (the normalized
  stabilization isomorphisms).
-/

public section

open Module TensorProduct

namespace ContinuousLinearMap

variable {𝕜 E F E₁ F₁ E₂ F₂ Λ₁ Λ₂ : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F]
  [AddCommGroup E₁] [Module 𝕜 E₁] [TopologicalSpace E₁]
  [AddCommGroup F₁] [Module 𝕜 F₁] [TopologicalSpace F₁] [ContinuousAdd F₁]
  [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
  [AddCommGroup F₂] [Module 𝕜 F₂] [TopologicalSpace F₂] [ContinuousAdd F₂]
  [AddCommGroup Λ₁] [Module 𝕜 Λ₁] [TopologicalSpace Λ₁]
  [AddCommGroup Λ₂] [Module 𝕜 Λ₂] [TopologicalSpace Λ₂]
  {D₁ : E₁ →L[𝕜] F₁} {ι₁ : Λ₁ →L[𝕜] F₁} {D₂ : E₂ →L[𝕜] F₂} {ι₂ : Λ₂ →L[𝕜] F₂}
  [FiniteDimensional 𝕜 D₁.ker] [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 D₂.ker]
  [FiniteDimensional 𝕜 Λ₂]

-- Stabilized kernels `(D₁.coprod ι₁).ker` are finite-dimensional when `D₁.ker` and `Λ₁` are.
attribute [local instance] finiteDimensional_ker_coprod

variable (D : E →L[𝕜] F) (j : Λ₁ × Λ₂ →L[𝕜] F)

/-- **The determinant-line isomorphism of linear gluing.** Let `D₁.coprod ι₁`, `D₂.coprod ι₂`
and `D.coprod j` be onto, with `j` defined on the product `Λ₁ × Λ₂` of the stabilizers of the
pieces, and let `g` be an isomorphism from the product of the stabilized kernels of the pieces to
the stabilized kernel of `D`. The isomorphism `det D ≃ det D₁ ⊗ det D₂` is the inverse of the
normalized stabilization isomorphism of `D`, followed by the isomorphism induced by `g⁻¹` on the
determinant line of the stabilized kernel, by the splitting
`TauCeti.detLineTensorDualProdEquiv` of the determinant lines of the products, ordered `D₁`, `D₂`,
and by the normalized stabilization isomorphisms of `D₁` and `D₂`
(`ContinuousLinearMap.detLineGluingEquiv_detLineStabilizationEquiv`). -/
noncomputable def detLineGluingEquiv (h : Function.Surjective (D.coprod j))
    (h₁ : Function.Surjective (D₁.coprod ι₁)) (h₂ : Function.Surjective (D₂.coprod ι₂))
    (g : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) ≃ₗ[𝕜] (D.coprod j).ker) :
    (D : E →ₗ[𝕜] F).detLine ≃ₗ[𝕜] (D₁ : E₁ →ₗ[𝕜] F₁).detLine ⊗[𝕜] (D₂ : E₂ →ₗ[𝕜] F₂).detLine :=
  have : FiniteDimensional 𝕜 (D.coprod j).ker := LinearEquiv.finiteDimensional g
  have := finiteDimensional_ker_of_finiteDimensional_ker_coprod D j
  (detLineStabilizationEquiv D j h).symm ≪≫ₗ LinearEquiv.rTensor _ g.symm.detLineCongr ≪≫ₗ
    (TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _).symm ≪≫ₗ
    TensorProduct.congr (detLineStabilizationEquiv D₁ ι₁ h₁) (detLineStabilizationEquiv D₂ ι₂ h₂)

/-- **Changing the gluing isomorphism.** Two gluing isomorphisms `g` and `g'` of the stabilized
kernels give determinant-line isomorphisms differing by the determinant of the automorphism
`g'⁻¹ ∘ g` of the product of the stabilized kernels of the pieces. -/
theorem detLineGluingEquiv_apply_eq_det_smul (h : Function.Surjective (D.coprod j))
    (h₁ : Function.Surjective (D₁.coprod ι₁)) (h₂ : Function.Surjective (D₂.coprod ι₂))
    (g g' : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) ≃ₗ[𝕜] (D.coprod j).ker)
    (x : (D : E →ₗ[𝕜] F).detLine) :
    detLineGluingEquiv D j h h₁ h₂ g' x =
      LinearMap.det (g.trans g'.symm : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) →ₗ[𝕜] _) •
        detLineGluingEquiv D j h h₁ h₂ g x := by
  -- `g'⁻¹` is `g⁻¹` followed by the automorphism `g'⁻¹ ∘ g`, which acts on the determinant line
  -- of the product of the stabilized kernels by its determinant.
  have hg : g'.symm = g.symm.trans (g.trans g'.symm) := LinearEquiv.ext fun _ ↦ by simp
  have key : ∀ y : TauCeti.detLine 𝕜 (D.coprod j).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 (Λ₁ × Λ₂)),
      LinearEquiv.rTensor _ g'.symm.detLineCongr y =
        LinearMap.det (g.trans g'.symm : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) →ₗ[𝕜] _) •
          LinearEquiv.rTensor _ g.symm.detLineCongr y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => rw [LinearEquiv.map_add, LinearEquiv.map_add, hy, hz, smul_add]
    | tmul a φ =>
      conv_lhs => rw [hg, LinearEquiv.detLineCongr_trans]
      simp only [LinearEquiv.rTensor_tmul, LinearEquiv.trans_apply,
        LinearEquiv.detLineCongr_apply_eq_det_smul, TensorProduct.smul_tmul']
  simp only [detLineGluingEquiv, LinearEquiv.trans_apply, key, LinearEquiv.map_smul]

variable [FiniteDimensional 𝕜 D.ker]

/-- **Characterization of the gluing isomorphism.** For `x₁` and `x₂` in the stabilized
determinant lines `det (ker (D₁.coprod ι₁)) ⊗ (det Λ₁)^*` and
`det (ker (D₂.coprod ι₂)) ⊗ (det Λ₂)^*`, gather them by `TauCeti.detLineTensorDualProdEquiv`,
transport the result to the stabilized kernel of `D` along `g` and apply the normalized
stabilization isomorphism of `D`. The gluing isomorphism sends this element of `det D` to the
tensor product of the normalized stabilizations of `x₁` and `x₂`. -/
@[simp]
theorem detLineGluingEquiv_detLineStabilizationEquiv (h : Function.Surjective (D.coprod j))
    (h₁ : Function.Surjective (D₁.coprod ι₁)) (h₂ : Function.Surjective (D₂.coprod ι₂))
    (g : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) ≃ₗ[𝕜] (D.coprod j).ker)
    (x₁ : TauCeti.detLine 𝕜 (D₁.coprod ι₁).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ₁))
    (x₂ : TauCeti.detLine 𝕜 (D₂.coprod ι₂).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ₂)) :
    detLineGluingEquiv D j h h₁ h₂ g (detLineStabilizationEquiv D j h
        (LinearEquiv.rTensor _ g.detLineCongr
          (TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _ (x₁ ⊗ₜ x₂)))) =
      detLineStabilizationEquiv D₁ ι₁ h₁ x₁ ⊗ₜ detLineStabilizationEquiv D₂ ι₂ h₂ x₂ := by
  simp [detLineGluingEquiv, ← LinearEquiv.detLineCongr_symm, ← LinearEquiv.symm_rTensor]

section Real

variable {E F E₁ F₁ E₂ F₂ Λ₁ Λ₂ : Type*}
  [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [ContinuousAdd F]
  [AddCommGroup E₁] [Module ℝ E₁] [TopologicalSpace E₁]
  [AddCommGroup F₁] [Module ℝ F₁] [TopologicalSpace F₁] [ContinuousAdd F₁]
  [AddCommGroup E₂] [Module ℝ E₂] [TopologicalSpace E₂]
  [AddCommGroup F₂] [Module ℝ F₂] [TopologicalSpace F₂] [ContinuousAdd F₂]
  [AddCommGroup Λ₁] [Module ℝ Λ₁] [TopologicalSpace Λ₁]
  [AddCommGroup Λ₂] [Module ℝ Λ₂] [TopologicalSpace Λ₂]
  {D₁ : E₁ →L[ℝ] F₁} {ι₁ : Λ₁ →L[ℝ] F₁} {D₂ : E₂ →L[ℝ] F₂} {ι₂ : Λ₂ →L[ℝ] F₂}
  [FiniteDimensional ℝ D₁.ker] [FiniteDimensional ℝ Λ₁] [FiniteDimensional ℝ D₂.ker]
  [FiniteDimensional ℝ Λ₂]

/-- **Gluing isomorphisms joined by a segment give the same orientation.** Over `ℝ`, if the
gluing isomorphisms `g` and `g'` of the stabilized kernels are joined by the segment
`(1 - t) • g' + t • g`, `t ∈ [0, 1]`, of bijective linear maps, then the two determinant-line
isomorphisms `det D ≃ det D₁ ⊗ det D₂` differ by a positive factor. So they carry an orientation
of `det D₁ ⊗ det D₂` to the same orientation of `det D`. -/
theorem exists_pos_detLineGluingEquiv_eq_smul_of_forall_bijective (D : E →L[ℝ] F)
    (j : Λ₁ × Λ₂ →L[ℝ] F) (h : Function.Surjective (D.coprod j))
    (h₁ : Function.Surjective (D₁.coprod ι₁)) (h₂ : Function.Surjective (D₂.coprod ι₂))
    (g g' : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) ≃ₗ[ℝ] (D.coprod j).ker)
    (hgg' : ∀ t ∈ Set.Icc (0 : ℝ) 1, Function.Bijective
      ⇑((1 - t) • (g' : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) →ₗ[ℝ] (D.coprod j).ker) +
        t • (g : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) →ₗ[ℝ] (D.coprod j).ker))) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : (D : E →ₗ[ℝ] F).detLine,
      detLineGluingEquiv D j h h₁ h₂ g' x = c • detLineGluingEquiv D j h h₁ h₂ g x := by
  refine ⟨_, ?_, detLineGluingEquiv_apply_eq_det_smul D j h h₁ h₂ g g'⟩
  -- `(1 - t) • id + t • g'⁻¹ ∘ g` is `g'⁻¹` composed with the bijective map at `t`, so it is
  -- never singular, and the determinant of `g'⁻¹ ∘ g` is positive.
  refine LinearMap.det_pos_of_forall_det_one_sub_smul_id_add_smul_ne_zero _ fun t ht ↦ ?_
  have hc : (1 - t) • LinearMap.id +
      t • (g.trans g'.symm : ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) →ₗ[ℝ] _) =
        ((LinearEquiv.ofBijective _ (hgg' t ht)).trans g'.symm :
          ((D₁.coprod ι₁).ker × (D₂.coprod ι₂).ker) →ₗ[ℝ] _) :=
    LinearMap.ext fun v ↦ by simp
  rw [hc]
  exact (LinearEquiv.isUnit_det' _).ne_zero

end Real

end ContinuousLinearMap
