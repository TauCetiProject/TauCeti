/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.DirectSum

/-!
# The determinant line of a glued operator

Linear gluing compares an operator `D` with two operators `D₁ : E₁ → F₁` and `D₂ : E₂ → F₂`
without asking `D` to be their direct sum. Stabilize the pieces by finite-dimensional spaces
`j₁ : Λ₁ → F₁` and `j₂ : Λ₂ → F₂`, so that `D₁.coprod j₁` and `D₂.coprod j₂` are onto with
kernels `E₁'` and `E₂'`, and stabilize `D` by the product `j : Λ₁ × Λ₂ → F`, so that `D.coprod j`
is onto with kernel `E'`. For two cylinder operators glued along a long neck, `j` is the pair of
stabilizers translated to the two ends of the neck, and pregluing corrected along a right inverse
gives an isomorphism `e : E₁' × E₂' ≃ E'` of the stabilized kernels.

Such an isomorphism identifies the determinant lines,

`det D ≃ det D₁ ⊗ det D₂`

(`ContinuousLinearMap.detLineGluingEquiv`). It reads `det D` as `det E' ⊗ (det (Λ₁ × Λ₂))^*`
through the normalized stabilization isomorphism
`ContinuousLinearMap.detLineStabilizationEquiv`, transports along `e`, splits the products in the
fixed order `E₁', E₂'` and `Λ₁, Λ₂` by `TauCeti.detLineTensorDualProdEquiv`, and reads the two
factors as `det D₁` and `det D₂`, again by the normalized stabilization isomorphisms. The Koszul
sign `(-1) ^ (dim Λ₁ * (dim ker D₂ + dim coker D₂))` of moving `(det Λ₁)^*` past the determinant
line of `D₂` is included, so that for the direct sum `D = D₁ ⊕ D₂`, stabilized by `j₁ ⊕ j₂`, with
`e` the identification of the stabilized kernels (`ContinuousLinearMap.kerCoprodProdMapEquiv`),
the isomorphism is the normalized direct sum isomorphism
`(-1) ^ (dim coker D₁ * dim coker D₂) • LinearMap.detLineProdMapEquiv`
(`ContinuousLinearMap.detLineGluingEquiv_kerCoprodProdMapEquiv`).

Through `e` the stabilization sequence `0 → ker D → ker (D.coprod j) → Λ₁ × Λ₂ → coker D → 0`
of `D` becomes an exact sequence `0 → ker D → E₁' × E₂' → Λ₁ × Λ₂ → coker D → 0`; for linear
gluing its middle map is the obstruction map. The inverse of the gluing isomorphism is, up to an
explicit sign, the four-term isomorphism `TauCeti.detLineFourTermEquiv` of this sequence read
through the stabilization isomorphisms of the pieces
(`ContinuousLinearMap.detLineGluingEquiv_symm_congr_eq_detLineFourTermEquiv`).

The isomorphism depends on `e` only through the determinant of the change of kernel
identification: replacing `e` by `e'` multiplies it by `det (e'⁻¹ ∘ e)`
(`ContinuousLinearMap.detLineGluingEquiv_eq_det_smul`). Over `ℝ` two identifications joined by a
path of isomorphisms therefore induce the same orientations of the determinant lines.

## Main definitions

* `ContinuousLinearMap.detLineGluingEquiv`: the isomorphism `det D ≃ det D₁ ⊗ det D₂` induced by
  an isomorphism `E₁' × E₂' ≃ E'` of stabilized kernels.

## Main results

* `ContinuousLinearMap.detLineGluingEquiv_detLineStabilizationEquiv`: its value on the image of
  the stabilized determinant lines, which characterizes it.
* `ContinuousLinearMap.detLineGluingEquiv_symm_congr_eq_detLineFourTermEquiv`: it is the
  four-term isomorphism of the transported exact sequence, up to sign.
* `ContinuousLinearMap.detLineGluingEquiv_eq_det_smul`: changing the identification of the
  stabilized kernels multiplies it by a determinant.
* `ContinuousLinearMap.detLineGluingEquiv_kerCoprodProdMapEquiv`: for a direct sum it is the
  normalized direct sum isomorphism.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Section A.2 (determinant line bundles) and Section 3.1
  (stabilizing a Fredholm operator).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368 (stabilizations, direct sums
  and their signs).
-/

public section

noncomputable section

open Module TensorProduct

namespace ContinuousLinearMap

-- Stabilized kernels `(D₁.coprod D₂).ker` are finite-dimensional when `D₁.ker` and `Λ` are.
attribute [local instance] finiteDimensional_ker_coprod

variable {𝕜 E F Λ₁ Λ₂ E₁ F₁ E₂ F₂ : Type*} [Field 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F] [ContinuousAdd F]
  [AddCommGroup Λ₁] [Module 𝕜 Λ₁] [TopologicalSpace Λ₁]
  [AddCommGroup Λ₂] [Module 𝕜 Λ₂] [TopologicalSpace Λ₂]
  [AddCommGroup E₁] [Module 𝕜 E₁] [TopologicalSpace E₁]
  [AddCommGroup F₁] [Module 𝕜 F₁] [TopologicalSpace F₁] [ContinuousAdd F₁]
  [AddCommGroup E₂] [Module 𝕜 E₂] [TopologicalSpace E₂]
  [AddCommGroup F₂] [Module 𝕜 F₂] [TopologicalSpace F₂] [ContinuousAdd F₂]
  {D₁ : E₁ →L[𝕜] F₁} {j₁ : Λ₁ →L[𝕜] F₁} {D₂ : E₂ →L[𝕜] F₂} {j₂ : Λ₂ →L[𝕜] F₂}
  [FiniteDimensional 𝕜 D₁.ker] [FiniteDimensional 𝕜 Λ₁] [FiniteDimensional 𝕜 D₂.ker]
  [FiniteDimensional 𝕜 Λ₂]

section Gluing

variable {D : E →L[𝕜] F} {j : Λ₁ × Λ₂ →L[𝕜] F}

variable (D) in
/-- **The determinant line of a glued operator.** Let `D₁.coprod j₁`, `D₂.coprod j₂` and
`D.coprod j` be onto, with `j` defined on `Λ₁ × Λ₂`, and let `e` identify the product of the
stabilized kernels of the pieces with the stabilized kernel of `D`. Then `det D ≃ det D₁ ⊗ det D₂`:
read `det D` as `det (ker (D.coprod j)) ⊗ (det (Λ₁ × Λ₂))^*` by the normalized stabilization
isomorphism, transport along `e`, split the products in the order `1, 2`
(`TauCeti.detLineTensorDualProdEquiv`), read the factors as `det D₁` and `det D₂` by the
normalized stabilization isomorphisms, and multiply by the Koszul sign
`(-1) ^ (dim Λ₁ * (dim ker D₂ + dim coker D₂))`. Its value is
`ContinuousLinearMap.detLineGluingEquiv_detLineStabilizationEquiv`. The kernel of `D` is
finite-dimensional, since `e` makes the stabilized kernel of `D` finite-dimensional. -/
def detLineGluingEquiv (e : ((D₁.coprod j₁).ker × (D₂.coprod j₂).ker) ≃ₗ[𝕜] (D.coprod j).ker)
    (h₁ : Function.Surjective (D₁.coprod j₁)) (h₂ : Function.Surjective (D₂.coprod j₂))
    (h : Function.Surjective (D.coprod j)) :
    (D : E →ₗ[𝕜] F).detLine ≃ₗ[𝕜] (D₁ : E₁ →ₗ[𝕜] F₁).detLine ⊗[𝕜] (D₂ : E₂ →ₗ[𝕜] F₂).detLine :=
  haveI : FiniteDimensional 𝕜 (D.coprod j).ker := e.finiteDimensional
  haveI := finiteDimensional_ker_of_finiteDimensional_ker_coprod D j
  (detLineStabilizationEquiv D j h).symm ≪≫ₗ
    LinearEquiv.rTensor _ e.detLineCongr.symm ≪≫ₗ
    (TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _).symm ≪≫ₗ
    TensorProduct.congr (detLineStabilizationEquiv D₁ j₁ h₁)
      (detLineStabilizationEquiv D₂ j₂ h₂) ≪≫ₗ
    LinearEquiv.smulOfUnit ((-1) ^ (finrank 𝕜 Λ₁ * (finrank 𝕜 D₂.ker + finrank 𝕜 (F₂ ⧸ D₂.range))))

/-- **The value of `ContinuousLinearMap.detLineGluingEquiv`.** Gather `w`, a tensor of the
stabilized determinant lines of the two pieces, into the stabilized determinant line of `D` by
`TauCeti.detLineTensorDualProdEquiv` and `e`. The gluing isomorphism sends its image under the
normalized stabilization isomorphism of `D` to the tensor product of the normalized stabilization
isomorphisms of the pieces applied to `w`, times `(-1) ^ (dim Λ₁ * (dim ker D₂ + dim coker D₂))`.
-/
theorem detLineGluingEquiv_detLineStabilizationEquiv [FiniteDimensional 𝕜 D.ker]
    (e : ((D₁.coprod j₁).ker × (D₂.coprod j₂).ker) ≃ₗ[𝕜] (D.coprod j).ker)
    (h₁ : Function.Surjective (D₁.coprod j₁)) (h₂ : Function.Surjective (D₂.coprod j₂))
    (h : Function.Surjective (D.coprod j))
    (w : (TauCeti.detLine 𝕜 (D₁.coprod j₁).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ₁)) ⊗[𝕜]
      (TauCeti.detLine 𝕜 (D₂.coprod j₂).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ₂))) :
    detLineGluingEquiv D e h₁ h₂ h (detLineStabilizationEquiv D j h
        (LinearEquiv.rTensor _ e.detLineCongr (TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _ w))) =
      (-1 : 𝕜) ^ (finrank 𝕜 Λ₁ * (finrank 𝕜 D₂.ker + finrank 𝕜 (F₂ ⧸ D₂.range))) •
        TensorProduct.congr (detLineStabilizationEquiv D₁ j₁ h₁)
          (detLineStabilizationEquiv D₂ j₂ h₂) w := by
  simp only [detLineGluingEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    ← LinearEquiv.symm_rTensor]
  simp [LinearEquiv.smulOfUnit, Units.smul_def]

/-- **The gluing isomorphism of the exact sequence of gluing.** Through `e`, the stabilization
sequence `0 → ker D → ker (D.coprod j) → Λ₁ × Λ₂ → coker D → 0` becomes an exact sequence
`0 → ker D → E₁' × E₂' → Λ₁ × Λ₂ → coker D → 0`, with first map `f = e⁻¹ ∘ kerCoprodHom`, middle
map `g = parameterProj ∘ e` and last map `ContinuousLinearMap.parameterToCoker`. The inverse of
the gluing isomorphism, applied to the tensor product of the normalized stabilization isomorphisms
of the pieces, is the four-term isomorphism `TauCeti.detLineFourTermEquiv` of this sequence
applied to the product of the stabilized lines of the pieces, up to the sign
`(-1) ^ (dim Λ₁ * (dim ker D₂ + dim coker D₂) + dim coker D * dim (Λ₁ × Λ₂))`. -/
theorem detLineGluingEquiv_symm_congr_eq_detLineFourTermEquiv [FiniteDimensional 𝕜 D.ker]
    (e : ((D₁.coprod j₁).ker × (D₂.coprod j₂).ker) ≃ₗ[𝕜] (D.coprod j).ker)
    (h₁ : Function.Surjective (D₁.coprod j₁)) (h₂ : Function.Surjective (D₂.coprod j₂))
    (h : Function.Surjective (D.coprod j))
    {f : D.ker →ₗ[𝕜] (D₁.coprod j₁).ker × (D₂.coprod j₂).ker}
    {g : ((D₁.coprod j₁).ker × (D₂.coprod j₂).ker) →ₗ[𝕜] Λ₁ × Λ₂}
    (hf : ∀ v, e (f v) = kerCoprodHom D j v) (hg : ∀ k, g k = parameterProj D j (e k))
    (hfi : Function.Injective f) (hfg : Function.Exact f g)
    (hgh : Function.Exact g (parameterToCoker D j))
    (hh : Function.Surjective (parameterToCoker D j))
    (w : (TauCeti.detLine 𝕜 (D₁.coprod j₁).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ₁)) ⊗[𝕜]
      (TauCeti.detLine 𝕜 (D₂.coprod j₂).ker ⊗[𝕜] Dual 𝕜 (TauCeti.detLine 𝕜 Λ₂))) :
    (detLineGluingEquiv D e h₁ h₂ h).symm (TensorProduct.congr
        (detLineStabilizationEquiv D₁ j₁ h₁) (detLineStabilizationEquiv D₂ j₂ h₂) w) =
      (-1 : 𝕜) ^ (finrank 𝕜 Λ₁ * (finrank 𝕜 D₂.ker + finrank 𝕜 (F₂ ⧸ D₂.range)) +
          finrank 𝕜 (F ⧸ D.range) * finrank 𝕜 (Λ₁ × Λ₂)) •
        TauCeti.detLineFourTermEquiv hfi hfg hgh hh
          (TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _ w) := by
  set a := finrank 𝕜 Λ₁ * (finrank 𝕜 D₂.ker + finrank 𝕜 (F₂ ⧸ D₂.range))
  set c := finrank 𝕜 (F ⧸ D.range) * finrank 𝕜 (Λ₁ × Λ₂)
  -- The stabilization sequence and the transported sequence are isomorphic through `e`.
  have hcongr := TauCeti.detLineFourTermEquiv_congr (kerCoprodHom_injective D j)
    (exact_kerCoprodHom_parameterProj D j) (exact_parameterProj_parameterToCoker D j)
    ((parameterToCoker_surjective_iff_coprod_surjective D j).2 h) hfi hfg hgh hh
    (LinearEquiv.refl 𝕜 D.ker) e.symm (LinearEquiv.refl 𝕜 (Λ₁ × Λ₂))
    (LinearEquiv.refl 𝕜 (F ⧸ D.range))
    (LinearMap.ext fun v ↦ by simp [LinearEquiv.eq_symm_apply, hf])
    (LinearMap.ext fun k ↦ by simp [hg]) (LinearMap.ext fun _ ↦ rfl)
    (LinearEquiv.rTensor _ e.detLineCongr (TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _ w))
  have hB : ∀ y : TauCeti.detLine 𝕜 ((D₁.coprod j₁).ker × (D₂.coprod j₂).ker) ⊗[𝕜]
      Dual 𝕜 (TauCeti.detLine 𝕜 (Λ₁ × Λ₂)), TensorProduct.congr e.symm.detLineCongr
        (LinearEquiv.refl 𝕜 (Λ₁ × Λ₂)).detLineCongr.symm.dualMap
          (LinearEquiv.rTensor _ e.detLineCongr y) = y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul b φ => simp [← LinearEquiv.detLineCongr_symm]
    | add y y' hy hy' => rw [LinearEquiv.map_add, LinearEquiv.map_add, hy, hy']
  have hA : ∀ z : (D : E →ₗ[𝕜] F).detLine, TensorProduct.congr
      (LinearEquiv.refl 𝕜 D.ker).detLineCongr
        (LinearEquiv.refl 𝕜 (F ⧸ D.range)).detLineCongr.symm.dualMap z = z := by
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul b φ => simp
    | add z z' hz hz' => rw [LinearEquiv.map_add, hz, hz']
  rw [hB, hA] at hcongr
  -- The four-term isomorphism of the stabilization sequence is the normalized stabilization
  -- isomorphism up to `(-1) ^ c`.
  have hS : ∀ y, TauCeti.detLineFourTermEquiv (kerCoprodHom_injective D j)
      (exact_kerCoprodHom_parameterProj D j) (exact_parameterProj_parameterToCoker D j)
      ((parameterToCoker_surjective_iff_coprod_surjective D j).2 h) y =
        (-1 : 𝕜) ^ c • detLineStabilizationEquiv D j h y := by
    intro y
    rw [detLineStabilizationEquiv_apply, smul_smul, ← pow_add, Even.neg_one_pow ⟨c, rfl⟩,
      one_smul, detLineCoprodEquiv_def]
  rw [hcongr, hS, smul_smul, ← pow_add, LinearEquiv.symm_apply_eq, LinearEquiv.map_smul,
    detLineGluingEquiv_detLineStabilizationEquiv, smul_smul, ← pow_add,
    show a + c + c + a = (a + c) + (a + c) by ring, Even.neg_one_pow ⟨a + c, rfl⟩, one_smul]

/-- **Changing the identification of the stabilized kernels.** Replacing `e` by `e'` multiplies
the gluing isomorphism by the determinant of the automorphism `e'⁻¹ ∘ e` of `E₁' × E₂'`. -/
theorem detLineGluingEquiv_eq_det_smul
    (e e' : ((D₁.coprod j₁).ker × (D₂.coprod j₂).ker) ≃ₗ[𝕜] (D.coprod j).ker)
    (h₁ : Function.Surjective (D₁.coprod j₁)) (h₂ : Function.Surjective (D₂.coprod j₂))
    (h : Function.Surjective (D.coprod j)) (x : (D : E →ₗ[𝕜] F).detLine) :
    detLineGluingEquiv D e' h₁ h₂ h x =
      LinearMap.det (e.trans e'.symm).toLinearMap • detLineGluingEquiv D e h₁ h₂ h x := by
  have : FiniteDimensional 𝕜 (D.coprod j).ker := e.finiteDimensional
  -- `e'⁻¹ = (e'⁻¹ ∘ e) ∘ e⁻¹`, and `e'⁻¹ ∘ e` acts on `det (E₁' × E₂')` by its determinant.
  have hmid : ∀ y : TauCeti.detLine 𝕜 (D.coprod j).ker ⊗[𝕜]
      Dual 𝕜 (TauCeti.detLine 𝕜 (Λ₁ × Λ₂)),
      LinearEquiv.rTensor _ e'.detLineCongr.symm y = LinearMap.det (e.trans e'.symm).toLinearMap •
        LinearEquiv.rTensor _ e.detLineCongr.symm y := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul a φ =>
      have he : e.symm.trans (e.trans e'.symm) = e'.symm := LinearEquiv.ext fun v ↦ by simp
      rw [LinearEquiv.rTensor_tmul, LinearEquiv.rTensor_tmul, smul_tmul',
        ← LinearEquiv.detLineCongr_apply_eq_det_smul, LinearEquiv.detLineCongr_symm,
        LinearEquiv.detLineCongr_symm, ← LinearEquiv.trans_apply, ← LinearEquiv.detLineCongr_trans,
        he]
    | add y y' hy hy' => rw [LinearEquiv.map_add, LinearEquiv.map_add, hy, hy', smul_add]
  simp only [detLineGluingEquiv, LinearEquiv.trans_apply, hmid, LinearEquiv.map_smul]

end Gluing

section DirectSum

variable [FiniteDimensional 𝕜 (F₁ ⧸ D₁.range)] [FiniteDimensional 𝕜 (F₂ ⧸ D₂.range)]

/-- **Gluing a direct sum.** For the direct sum `D₁ ⊕ D₂`, stabilized by `j₁ ⊕ j₂`, with the
stabilized kernels identified by `ContinuousLinearMap.kerCoprodProdMapEquiv`, the gluing
isomorphism is the normalized direct sum isomorphism
`(-1) ^ (dim coker D₁ * dim coker D₂) • LinearMap.detLineProdMapEquiv`. -/
theorem detLineGluingEquiv_kerCoprodProdMapEquiv (h₁ : Function.Surjective (D₁.coprod j₁))
    (h₂ : Function.Surjective (D₂.coprod j₂))
    (x : (D₁.prodMap D₂ : E₁ × E₂ →ₗ[𝕜] F₁ × F₂).detLine) :
    detLineGluingEquiv (D₁.prodMap D₂) (kerCoprodProdMapEquiv D₁ j₁ D₂ j₂) h₁ h₂
        (surjective_coprod_prodMap h₁ h₂) x =
      (-1 : 𝕜) ^ (finrank 𝕜 (F₁ ⧸ D₁.range) * finrank 𝕜 (F₂ ⧸ D₂.range)) •
        LinearMap.detLineProdMapEquiv (D₁ : E₁ →ₗ[𝕜] F₁) (D₂ : E₂ →ₗ[𝕜] F₂) x := by
  set S := detLineStabilizationEquiv (D₁.prodMap D₂) (j₁.prodMap j₂)
    (surjective_coprod_prodMap h₁ h₂)
  set P := LinearMap.detLineProdMapEquiv (D₁ : E₁ →ₗ[𝕜] F₁) (D₂ : E₂ →ₗ[𝕜] F₂)
  set G := TauCeti.detLineTensorDualProdEquiv 𝕜 _ _ _ _ ≪≫ₗ
    LinearEquiv.rTensor (Dual 𝕜 (TauCeti.detLine 𝕜 (Λ₁ × Λ₂)))
      (kerCoprodProdMapEquiv D₁ j₁ D₂ j₂).detLineCongr
  set a : ℕ := finrank 𝕜 Λ₁ * (finrank 𝕜 D₂.ker + finrank 𝕜 (F₂ ⧸ D₂.range))
  set b : ℕ := finrank 𝕜 (F₁ ⧸ D₁.range) * finrank 𝕜 (F₂ ⧸ D₂.range)
  -- The direct sum law of the normalized stabilizations, extended from pure tensors.
  have hS : ∀ w, S (G w) = (-1 : 𝕜) ^ (a + b) • P.symm (TensorProduct.congr
      (detLineStabilizationEquiv D₁ j₁ h₁) (detLineStabilizationEquiv D₂ j₂ h₂) w) :=
    LinearMap.congr_fun (f := S.toLinearMap ∘ₗ G.toLinearMap)
      (g := (-1 : 𝕜) ^ (a + b) • (P.symm.toLinearMap ∘ₗ (TensorProduct.congr
        (detLineStabilizationEquiv D₁ j₁ h₁) (detLineStabilizationEquiv D₂ j₂ h₂)).toLinearMap))
      (TensorProduct.ext' fun y y' ↦ detLineStabilizationEquiv_prodMap h₁ h₂ y y')
  -- Every element of `det (D₁ ⊕ D₂)` is `S (G w)` for some `w`.
  obtain ⟨w, rfl⟩ : ∃ w, S (G w) = x :=
    ⟨G.symm (S.symm x), by rw [G.apply_symm_apply]; exact S.apply_symm_apply x⟩
  have hval := detLineGluingEquiv_detLineStabilizationEquiv
    (kerCoprodProdMapEquiv D₁ j₁ D₂ j₂) h₁ h₂ (surjective_coprod_prodMap h₁ h₂) w
  simp only [G, LinearEquiv.trans_apply] at hS ⊢
  rw [hval, hS, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply, smul_smul, ← pow_add,
    show b + (a + b) = a + (b + b) by ring, pow_add, Even.neg_one_pow ⟨b, rfl⟩, mul_one]

end DirectSum

end ContinuousLinearMap
