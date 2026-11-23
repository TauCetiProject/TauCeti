/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Determinant
public import TauCeti.Topology.VectorBundle.TensorProduct.Operations
public import TauCeti.LinearAlgebra.Determinant.DirectSum

/-!
# The determinant line of a product of vector bundles

The Whitney comparison identifies the tensor product of the native determinant lines of two
finite-rank vector bundles with the determinant line of their fibrewise product. The order of the
exterior factors is the order of the two bundles. All ranks, including zero, are allowed.
-/

public section

noncomputable section

open Bundle FiberBundle Module Set TopologicalSpace
open scoped Bundle TensorProduct

universe u v₁ v₂ w w₁ w₂

namespace TauCeti.DetBundle

private theorem coe_exteriorPower_apply {R : Type u} [CommRing R]
    {U : Type w₁} [AddCommGroup U] [Module R U]
    {V : Type w₂} [AddCommGroup V] [Module R V]
    (e : U ≃ₗ[R] V) (n : ℕ) (a : ⋀[R]^n U) :
    (e.exteriorPower n a : ExteriorAlgebra R V) = ExteriorAlgebra.map e.toLinearMap a := by
  have h : e.exteriorPower n a = exteriorPower.map n e.toLinearMap a := by
    simpa only [LinearEquiv.coe_coe] using
      LinearMap.congr_fun (LinearEquiv.exteriorPower_toLinearMap e n) a
  exact (congrArg (fun v : ⋀[R]^n V ↦ (v : ExteriorAlgebra R V)) h).trans
    (exteriorPower.coe_map _ _)

private theorem coe_degree_zero {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
    (a : ⋀[K]^0 V) :
    (a : ExteriorAlgebra K V) =
      algebraMap K (ExteriorAlgebra K V) (exteriorPower.zeroEquiv K V a) := by
  obtain ⟨r, rfl⟩ := (exteriorPower.zeroEquiv K V).symm.surjective a
  simp only [exteriorPower.zeroEquiv_symm_apply, Submodule.coe_smul_of_tower,
    exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_zero_apply,
    map_smul, exteriorPower.zeroEquiv_ιMulti, smul_eq_mul, mul_one,
    Algebra.algebraMap_eq_smul_one]

section ExteriorDegrees

variable (K : Type u) [Field K] (U : Type w₁) (V : Type w₂)
  [AddCommGroup U] [Module K U] [FiniteDimensional K U]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private def exteriorProdLinearEquiv (r s t : ℕ) (hr : r = finrank K U)
    (hs : s = finrank K V) (ht : t = finrank K (U × V)) :
    ⋀[K]^r U ⊗[K] ⋀[K]^s V ≃ₗ[K] ⋀[K]^t (U × V) :=
  (TensorProduct.congr (LinearEquiv.ofEq _ _ (congrArg (⋀[K]^· U) hr))
      (LinearEquiv.ofEq _ _ (congrArg (⋀[K]^· V) hs))).trans
    ((detLineProdEquiv K U V).trans
      (LinearEquiv.ofEq _ _ (congrArg (⋀[K]^· (U × V)) ht)).symm)

private theorem coe_exteriorProdLinearEquiv_tmul (r s t : ℕ) (hr : r = finrank K U)
    (hs : s = finrank K V) (ht : t = finrank K (U × V))
    (a : ⋀[K]^r U) (b : ⋀[K]^s V) :
    (exteriorProdLinearEquiv K U V r s t hr hs ht (a ⊗ₜ b) : ExteriorAlgebra K (U × V)) =
      ExteriorAlgebra.map (LinearMap.inl K U V) a *
        ExteriorAlgebra.map (LinearMap.inr K U V) b := by
  simp only [exteriorProdLinearEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.ofEq_symm, LinearEquiv.coe_ofEq_apply,
    coe_detLineProdEquiv_tmul_eq_mul]

end ExteriorDegrees

section Models

variable (K : Type u) [NontriviallyNormedField K] [CompleteSpace K]
  (F₁ : Type v₁) [NormedAddCommGroup F₁] [NormedSpace K F₁] [FiniteDimensional K F₁]
  (F₂ : Type v₂) [NormedAddCommGroup F₂] [NormedSpace K F₂] [FiniteDimensional K F₂]

private def prodModelLinearEquiv : ProjectiveTensor K K K ≃ₗ[K] K :=
  (ProjectiveTensor.linearEquiv K K K).trans
    ((TensorProduct.congr (modelCoord F₁).symm (modelCoord F₂).symm).trans
      ((detLineProdEquiv K F₁ F₂).trans (modelCoord (F₁ × F₂))))

/-- The fixed model comparison in determinant coordinates. It uses the chosen model coordinates
on the three determinant lines; it need not be the multiplication map in arbitrary model bases. -/
def prodModelEquiv : ProjectiveTensor K K K ≃L[K] K := by
  letI : IsModuleTopology K (ProjectiveTensor K K K) := isModuleTopologyOfFiniteDimensional
  exact (prodModelLinearEquiv K F₁ F₂).toContinuousLinearEquivOfIsModuleTopology

/-- On scalar pure tensors, the model comparison is the determinant product read through the
chosen coordinates of the two models and their product. -/
theorem prodModelEquiv_tmul (a b : K) :
    prodModelEquiv K F₁ F₂ ⟨a ⊗ₜ b⟩ = modelCoord (F₁ × F₂)
      (detLineProdEquiv K F₁ F₂ ((modelCoord F₁).symm a ⊗ₜ (modelCoord F₂).symm b)) := by
  let : IsModuleTopology K (ProjectiveTensor K K K) := isModuleTopologyOfFiniteDimensional
  have hp := congrFun (LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology
    (prodModelLinearEquiv K F₁ F₂)) ⟨a ⊗ₜ b⟩
  unfold prodModelEquiv
  rw [hp]
  simp only [prodModelLinearEquiv, LinearEquiv.trans_apply,
    ProjectiveTensor.linearEquiv_apply, TensorProduct.congr_tmul]

end Models

variable {K : Type u} {B : Type w}
  [NontriviallyNormedField K] [TopologicalSpace B]
  {F₁ : Type v₁} [NormedAddCommGroup F₁] [NormedSpace K F₁] [FiniteDimensional K F₁]
  {E₁ : B → Type w₁}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module K (E₁ x)]
  [∀ x, TopologicalSpace (E₁ x)] [TopologicalSpace (TotalSpace F₁ E₁)]
  [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
  {F₂ : Type v₂} [NormedAddCommGroup F₂] [NormedSpace K F₂] [FiniteDimensional K F₂]
  {E₂ : B → Type w₂}
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module K (E₂ x)]
  [∀ x, TopologicalSpace (E₂ x)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]

private def prodLinearEquiv (x : B) :
    DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x ≃ₗ[K]
      DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂) x := by
  letI : FiniteDimensional K (E₁ x) := VectorBundle.finiteDimensional K F₁ E₁ x
  letI : FiniteDimensional K (E₂ x) := VectorBundle.finiteDimensional K F₂ E₂ x
  exact (TensorProduct.congr (linearEquiv K F₁ E₁ x) (linearEquiv K F₂ E₂ x)).trans
    ((exteriorProdLinearEquiv K (E₁ x) (E₂ x)
      (finrank K F₁) (finrank K F₂) (finrank K (F₁ × F₂))
      (VectorBundle.finrank_eq K F₁ E₁ x).symm (VectorBundle.finrank_eq K F₂ E₂ x).symm
      (VectorBundle.finrank_eq K (F₁ × F₂) (E₁ ×ᵇ E₂) x).symm).trans
        (linearEquiv K (F₁ × F₂) (E₁ ×ᵇ E₂) x).symm)

private def fiberDetLineEquiv (x : B) : DetBundle K F₁ E₁ x ≃ₗ[K] detLine K (E₁ x) :=
  (linearEquiv K F₁ E₁ x).trans
    (LinearEquiv.ofEq _ _ (congrArg (⋀[K]^· (E₁ x))
      (VectorBundle.finrank_eq K F₁ E₁ x).symm))

omit [FiniteDimensional K F₁] in
private theorem coe_fiberDetLineEquiv (x : B) (a : DetBundle K F₁ E₁ x) :
    (fiberDetLineEquiv (K := K) (F₁ := F₁) (E₁ := E₁) x a : ExteriorAlgebra K (E₁ x)) =
      linearEquiv K F₁ E₁ x a := by
  simp only [fiberDetLineEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply]

variable [∀ x, TopologicalSpace (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]
  [∀ x, IsModuleTopology K (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]

variable (K F₁ E₁ F₂ E₂) in
/-- The fibrewise Whitney comparison for the native determinant bundles. It orders the first
bundle before the second and applies also when either model fibre has rank zero. -/
def prodEquiv (x : B) : DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x ≃L[K]
    DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂) x :=
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology
    (prodLinearEquiv (K := K) (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂) x)

/-- In the exterior algebra, the Whitney comparison is the exterior product of the images of
its two determinant-line factors. This description includes the empty exterior product. -/
theorem coe_prodEquiv_tmul (x : B) (a : DetBundle K F₁ E₁ x) (b : DetBundle K F₂ E₂ x) :
    (linearEquiv K (F₁ × F₂) (E₁ ×ᵇ E₂) x (prodEquiv K F₁ E₁ F₂ E₂ x (a ⊗ₜ b)) :
        ExteriorAlgebra K (E₁ x × E₂ x)) =
      ExteriorAlgebra.map (LinearMap.inl K (E₁ x) (E₂ x)) (linearEquiv K F₁ E₁ x a) *
        ExteriorAlgebra.map (LinearMap.inr K (E₁ x) (E₂ x)) (linearEquiv K F₂ E₂ x b) := by
  let : FiniteDimensional K (E₁ x) := VectorBundle.finiteDimensional K F₁ E₁ x
  let : FiniteDimensional K (E₂ x) := VectorBundle.finiteDimensional K F₂ E₂ x
  have hp := congrFun (LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology
    (prodLinearEquiv (K := K) (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂) x)) (a ⊗ₜ b)
  unfold prodEquiv
  rw [hp]
  simp only [prodLinearEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.apply_symm_apply]
  exact coe_exteriorProdLinearEquiv_tmul K (E₁ x) (E₂ x)
    (finrank K F₁) (finrank K F₂) (finrank K (F₁ × F₂))
    (VectorBundle.finrank_eq K F₁ E₁ x).symm (VectorBundle.finrank_eq K F₂ E₂ x).symm
    (VectorBundle.finrank_eq K (F₁ × F₂) (E₁ ×ᵇ E₂) x).symm
    (linearEquiv K F₁ E₁ x a) (linearEquiv K F₂ E₂ x b)

private theorem fiberDetLineEquiv_prodEquiv (x : B)
    [FiniteDimensional K (E₁ x)] [FiniteDimensional K (E₂ x)]
    (t : DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x) :
    fiberDetLineEquiv (K := K) (F₁ := F₁ × F₂) (E₁ := E₁ ×ᵇ E₂) x
      (prodEquiv K F₁ E₁ F₂ E₂ x t) =
      detLineProdEquiv K (E₁ x) (E₂ x)
        (TensorProduct.congr (fiberDetLineEquiv (K := K) (F₁ := F₁) (E₁ := E₁) x)
          (fiberDetLineEquiv (K := K) (F₁ := F₂) (E₁ := E₂) x) t) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b =>
    apply Subtype.ext
    simp only [coe_fiberDetLineEquiv, coe_prodEquiv_tmul, TensorProduct.congr_tmul,
      coe_detLineProdEquiv_tmul_eq_mul]

variable [CompleteSpace K]

omit [FiniteDimensional K F₁] [VectorBundle K F₁ E₁]
  [FiniteDimensional K F₂] [VectorBundle K F₂ E₂]
  [∀ x, TopologicalSpace (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]
  [∀ x, IsModuleTopology K (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]
  [CompleteSpace K] in
private theorem linearEquivAt_prod_eq
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [e₁.IsLinear K] [e₂.IsLinear K] {x : B} (hx₁ : x ∈ e₁.baseSet) (hx₂ : x ∈ e₂.baseSet) :
    (e₁.prod e₂).linearEquivAt K x
      (by simpa only [Trivialization.prod_baseSet, Set.mem_inter_iff] using And.intro hx₁ hx₂) =
      (e₁.linearEquivAt K x hx₁).prodCongr (e₂.linearEquivAt K x hx₂) := by
  exact congrArg ContinuousLinearEquiv.toLinearEquiv
    (Trivialization.continuousLinearEquivAt_prod (𝕜 := K)
      (by simpa only [Trivialization.prod_baseSet, Set.mem_inter_iff] using And.intro hx₁ hx₂))

/-- The Whitney comparison in any pair of linear charts is the fixed model conjugation.
No compatibility of the chosen model bases with the product basis is assumed. -/
theorem chartCoord_prodEquiv_tmul
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [e₁.IsLinear K] [e₂.IsLinear K] {x : B} (hx₁ : x ∈ e₁.baseSet) (hx₂ : x ∈ e₂.baseSet)
    (a : DetBundle K F₁ E₁ x) (b : DetBundle K F₂ E₂ x) :
    chartCoord (e₁.prod e₂)
      (by simpa only [Trivialization.prod_baseSet, Set.mem_inter_iff] using And.intro hx₁ hx₂)
      (prodEquiv K F₁ E₁ F₂ E₂ x (a ⊗ₜ b)) =
      prodModelEquiv K F₁ F₂ ⟨chartCoord e₁ hx₁ a ⊗ₜ chartCoord e₂ hx₂ b⟩ := by
  simp only [chartCoord_apply, prodModelEquiv_tmul, LinearEquiv.symm_apply_apply]
  apply congrArg (modelCoord (F₁ × F₂))
  apply Subtype.ext
  rw [coe_exteriorPower_apply, coe_prodEquiv_tmul, coe_detLineProdEquiv_tmul_eq_mul,
    coe_exteriorPower_apply, coe_exteriorPower_apply]
  let e := (e₁.prod e₂).linearEquivAt K x
    (by simpa only [Trivialization.prod_baseSet, Set.mem_inter_iff] using And.intro hx₁ hx₂)
  have he : e = (e₁.linearEquivAt K x hx₁).prodCongr (e₂.linearEquivAt K x hx₂) :=
    linearEquivAt_prod_eq e₁ e₂ hx₁ hx₂
  have h₁ : e.toLinearMap.comp (LinearMap.inl K (E₁ x) (E₂ x)) =
      (LinearMap.inl K F₁ F₂).comp (e₁.linearEquivAt K x hx₁).toLinearMap := by
    rw [he]
    ext v <;> simp only [LinearMap.comp_apply, LinearMap.inl_apply,
      LinearEquiv.coe_coe, LinearEquiv.prodCongr_apply, map_zero]
  have h₂ : e.toLinearMap.comp (LinearMap.inr K (E₁ x) (E₂ x)) =
      (LinearMap.inr K F₁ F₂).comp (e₂.linearEquivAt K x hx₂).toLinearMap := by
    rw [he]
    ext v <;> simp only [LinearMap.comp_apply, LinearMap.inr_apply,
      LinearEquiv.coe_coe, LinearEquiv.prodCongr_apply, map_zero]
  dsimp only [e] at h₁ h₂
  simp only [map_mul, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, h₁, h₂]

/-- In preferred tensor-product and determinant charts, the Whitney equivalence is a constant
operator from the projective tensor model to the scalar model. -/
theorem prodEquiv_inCoordinates (a x : B)
    (hx₁ : x ∈ (trivializationAt F₁ E₁ a).baseSet)
    (hx₂ : x ∈ (trivializationAt F₂ E₂ a).baseSet) :
    ContinuousLinearMap.inCoordinates (ProjectiveTensor K K K)
        (fun y ↦ DetBundle K F₁ E₁ y ⊗[K] DetBundle K F₂ E₂ y)
        K (DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂)) a x a x
        (prodEquiv K F₁ E₁ F₂ E₂ x).toContinuousLinearMap =
      (prodModelEquiv K F₁ F₂).toContinuousLinearMap := by
  refine ProjectiveTensor.continuousLinearMap_ext fun c d ↦ ?_
  have hd₁ : x ∈ (trivializationAt K (DetBundle K F₁ E₁) a).baseSet := by
    simpa only [trivializationAt_eq, trivialization_baseSet] using hx₁
  have hd₂ : x ∈ (trivializationAt K (DetBundle K F₂ E₂) a).baseSet := by
    simpa only [trivializationAt_eq, trivialization_baseSet] using hx₂
  have hs : x ∈ (trivializationAt (ProjectiveTensor K K K)
      (fun y ↦ DetBundle K F₁ E₁ y ⊗[K] DetBundle K F₂ E₂ y) a).baseSet := by
    simpa only [tensorProduct_trivializationAt_baseSet, Set.mem_inter_iff] using And.intro hd₁ hd₂
  have hp : trivializationAt (F₁ × F₂) (E₁ ×ᵇ E₂) a =
      (trivializationAt F₁ E₁ a).prod (trivializationAt F₂ E₂ a) := by
    simpa only [trivializationAt] using
      (FiberBundle.prod_trivializationAt' (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂) a)
  have ht : x ∈ (trivializationAt K (DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂)) a).baseSet := by
    simpa only [trivializationAt_eq, trivialization_baseSet, hp,
      Trivialization.prod_baseSet, Set.mem_inter_iff] using And.intro hx₁ hx₂
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.symmL_apply (R := K) _ hs,
    tensorProduct_trivializationAt_symm_apply_tmul hd₁ hd₂]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem K _ ht]
  simp only [ContinuousLinearEquiv.coe_coe, trivializationAt_eq,
    trivialization_symm_apply _ hx₁, trivialization_symm_apply _ hx₂, hp]
  rw [trivialization_apply_mk _ (by simpa only [Trivialization.prod_baseSet,
    Set.mem_inter_iff] using And.intro hx₁ hx₂)]
  simpa only [LinearEquiv.apply_symm_apply] using
    (chartCoord_prodEquiv_tmul (K := K) (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂)
      (trivializationAt F₁ E₁ a) (trivializationAt F₂ E₂ a) hx₁ hx₂
      ((chartCoord (trivializationAt F₁ E₁ a) hx₁).symm c)
      ((chartCoord (trivializationAt F₂ E₂ a) hx₂).symm d))

/-- The Whitney equivalences form a continuous section of the native Hom bundle. -/
theorem continuous_prodEquiv_hom :
    Continuous (fun x ↦ TotalSpace.mk' (ProjectiveTensor K K K →L[K] K)
      (E := fun y ↦ (DetBundle K F₁ E₁ y ⊗[K] DetBundle K F₂ E₂ y) →L[K]
        DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂) y) x
      (prodEquiv K F₁ E₁ F₂ E₂ x).toContinuousLinearMap) := by
  apply continuous_hom_bundle_of_inCoordinates_eq_const
    (c := fun _ ↦ (prodModelEquiv K F₁ F₂).toContinuousLinearMap)
  intro a x hs _
  have hd : x ∈ (trivializationAt K (DetBundle K F₁ E₁) a).baseSet ∧
      x ∈ (trivializationAt K (DetBundle K F₂ E₂) a).baseSet := by
    simpa only [tensorProduct_trivializationAt_baseSet, Set.mem_inter_iff] using hs
  apply prodEquiv_inCoordinates a x
  · simpa only [trivializationAt_eq, trivialization_baseSet] using hd.1
  · simpa only [trivializationAt_eq, trivialization_baseSet] using hd.2

/-- The Whitney comparison is continuous on the actual total spaces of the native bundles. -/
theorem continuous_prodEquiv :
    Continuous (fun p : TotalSpace (ProjectiveTensor K K K)
        (fun y ↦ DetBundle K F₁ E₁ y ⊗[K] DetBundle K F₂ E₂ y) ↦
      TotalSpace.mk' K p.proj (prodEquiv K F₁ E₁ F₂ E₂ p.proj p.snd)) := by
  exact ((continuous_hom_bundle_iff
    (fun x ↦ (prodEquiv K F₁ E₁ F₂ E₂ x).toContinuousLinearMap)).1
      continuous_prodEquiv_hom).congr fun _ ↦ rfl

variable (K F₁ E₁ F₂ E₂) in
/-- The native Whitney homeomorphism of total spaces. Its domain retains the projective tensor
model of the tensor bundle; it is not replaced by a scalar-model bundle. -/
def prodHomeomorph :
    TotalSpace (ProjectiveTensor K K K)
      (fun y ↦ DetBundle K F₁ E₁ y ⊗[K] DetBundle K F₂ E₂ y) ≃ₜ
        TotalSpace K (DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂)) :=
  bundleHomeomorph (prodEquiv K F₁ E₁ F₂ E₂) continuous_prodEquiv

/-- The total-space Whitney homeomorphism is the fibrewise determinant product. -/
@[simp]
theorem prodHomeomorph_apply
    (p : TotalSpace (ProjectiveTensor K K K)
      (fun y ↦ DetBundle K F₁ E₁ y ⊗[K] DetBundle K F₂ E₂ y)) :
    prodHomeomorph K F₁ E₁ F₂ E₂ p =
      ⟨p.proj, prodEquiv K F₁ E₁ F₂ E₂ p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

/-- The inverse total-space comparison is the inverse Whitney equivalence on each fibre. -/
@[simp]
theorem prodHomeomorph_symm_apply
    (p : TotalSpace K (DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂))) :
    (prodHomeomorph K F₁ E₁ F₂ E₂).symm p =
      ⟨p.proj, (prodEquiv K F₁ E₁ F₂ E₂ p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

/-- The Whitney homeomorphism is over the identity of the base. -/
theorem prodHomeomorph_proj
    (p : TotalSpace (ProjectiveTensor K K K)
      (fun y ↦ DetBundle K F₁ E₁ y ⊗[K] DetBundle K F₂ E₂ y)) :
    (prodHomeomorph K F₁ E₁ F₂ E₂ p).proj = p.proj := by
  simp only [prodHomeomorph_apply]

/-- The inverse Whitney homeomorphism is also over the identity of the base. -/
theorem prodHomeomorph_symm_proj
    (p : TotalSpace K (DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂))) :
    ((prodHomeomorph K F₁ E₁ F₂ E₂).symm p).proj = p.proj := by
  simp only [prodHomeomorph_symm_apply]

section ModelCongr

variable {F' : Type*} [NormedAddCommGroup F'] [NormedSpace K F'] [FiniteDimensional K F']
  {E' : B → Type*} [∀ x, AddCommGroup (E' x)] [∀ x, Module K (E' x)]
  [∀ x, TopologicalSpace (E' x)] [TopologicalSpace (TotalSpace F' E')]
  [FiberBundle F' E'] [VectorBundle K F' E']

private def modelCongrLinearEquiv (e : ∀ x, E₁ x ≃L[K] E' x) (x : B) :
    DetBundle K F₁ E₁ x ≃ₗ[K] DetBundle K F' E' x := by
  let : FiniteDimensional K (E₁ x) := VectorBundle.finiteDimensional K F₁ E₁ x
  let : FiniteDimensional K (E' x) := VectorBundle.finiteDimensional K F' E' x
  exact (fiberDetLineEquiv (K := K) (F₁ := F₁) (E₁ := E₁) x).trans
    ((e x).toLinearEquiv.detLineCongr.trans
      (fiberDetLineEquiv (K := K) (F₁ := F') (E₁ := E') x).symm)

/-- The native determinant transport of a bundle isomorphism between independently presented
finite-dimensional models. It is induced by the actual exterior action on the fibres. -/
def congrModelEquiv (e : ∀ x, E₁ x ≃L[K] E' x) (x : B) :
    DetBundle K F₁ E₁ x ≃L[K] DetBundle K F' E' x :=
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology
    (modelCongrLinearEquiv (F₁ := F₁) (F' := F') e x)

omit [CompleteSpace K]
  [∀ x, IsModuleTopology K (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]
  [∀ x, TopologicalSpace (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)] in
private theorem fiberDetLineEquiv_congrModelEquiv (e : ∀ x, E₁ x ≃L[K] E' x) (x : B)
    (a : DetBundle K F₁ E₁ x) :
    fiberDetLineEquiv (K := K) (F₁ := F') (E₁ := E') x
      (congrModelEquiv (F₁ := F₁) (F' := F') e x a) =
      (e x).toLinearEquiv.detLineCongr
        (fiberDetLineEquiv (K := K) (F₁ := F₁) (E₁ := E₁) x a) := by
  have hp := congrFun (LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology
    (modelCongrLinearEquiv (F₁ := F₁) (F' := F') e x)) a
  unfold congrModelEquiv
  rw [hp]
  simp only [modelCongrLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

omit [CompleteSpace K]
  [∀ x, IsModuleTopology K (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]
  [∀ x, TopologicalSpace (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)] in
/-- Independent model presentations do not change the exterior-algebra action of an isomorphism. -/
theorem coe_congrModelEquiv (e : ∀ x, E₁ x ≃L[K] E' x) (x : B) (a : DetBundle K F₁ E₁ x) :
    (linearEquiv K F' E' x (congrModelEquiv (F₁ := F₁) (F' := F') e x a) :
      ExteriorAlgebra K (E' x)) =
      ExteriorAlgebra.map (e x).toLinearMap (linearEquiv K F₁ E₁ x a) := by
  let : FiniteDimensional K (E₁ x) := VectorBundle.finiteDimensional K F₁ E₁ x
  let : FiniteDimensional K (E' x) := VectorBundle.finiteDimensional K F' E' x
  have h := congrArg (fun v : detLine K (E' x) ↦ (v : ExteriorAlgebra K (E' x)))
    (fiberDetLineEquiv_congrModelEquiv (F₁ := F₁) (F' := F') e x a)
  simpa only [coe_fiberDetLineEquiv, LinearEquiv.coe_detLineCongr] using h

end ModelCongr

section ModelNaturality

variable {F₁' : Type*} {F₂' : Type*}
  [NormedAddCommGroup F₁'] [NormedSpace K F₁'] [FiniteDimensional K F₁']
  [NormedAddCommGroup F₂'] [NormedSpace K F₂'] [FiniteDimensional K F₂']
  {E₁' : B → Type*} {E₂' : B → Type*}
  [∀ x, AddCommGroup (E₁' x)] [∀ x, Module K (E₁' x)] [∀ x, TopologicalSpace (E₁' x)]
  [∀ x, AddCommGroup (E₂' x)] [∀ x, Module K (E₂' x)] [∀ x, TopologicalSpace (E₂' x)]
  [TopologicalSpace (TotalSpace F₁' E₁')] [FiberBundle F₁' E₁'] [VectorBundle K F₁' E₁']
  [TopologicalSpace (TotalSpace F₂' E₂')] [FiberBundle F₂' E₂'] [VectorBundle K F₂' E₂']
  [∀ x, TopologicalSpace (DetBundle K F₁' E₁' x ⊗[K] DetBundle K F₂' E₂' x)]
  [∀ x, IsModuleTopology K (DetBundle K F₁' E₁' x ⊗[K] DetBundle K F₂' E₂' x)]

omit [CompleteSpace K] in
/-- Whitney naturality for isomorphic bundles presented with different model spaces and
independent universes. No compatibility of chosen model bases is assumed. -/
theorem congrModelEquiv_prodEquiv (e₁ : ∀ x, E₁ x ≃L[K] E₁' x)
    (e₂ : ∀ x, E₂ x ≃L[K] E₂' x) (x : B)
    (t : DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x) :
    congrModelEquiv (F₁ := F₁ × F₂) (F' := F₁' × F₂')
      (fun y ↦ (e₁ y).prodCongr (e₂ y)) x (prodEquiv K F₁ E₁ F₂ E₂ x t) =
      prodEquiv K F₁' E₁' F₂' E₂' x
        (bundleTensorCongr (congrModelEquiv (F₁ := F₁) (F' := F₁') e₁)
          (congrModelEquiv (F₁ := F₂) (F' := F₂') e₂) x t) := by
  let : FiniteDimensional K (E₁ x) := VectorBundle.finiteDimensional K F₁ E₁ x
  let : FiniteDimensional K (E₂ x) := VectorBundle.finiteDimensional K F₂ E₂ x
  let : FiniteDimensional K (E₁' x) := VectorBundle.finiteDimensional K F₁' E₁' x
  let : FiniteDimensional K (E₂' x) := VectorBundle.finiteDimensional K F₂' E₂' x
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b =>
    apply (fiberDetLineEquiv (K := K) (F₁ := F₁' × F₂') (E₁ := E₁' ×ᵇ E₂') x).injective
    rw [fiberDetLineEquiv_congrModelEquiv, fiberDetLineEquiv_prodEquiv,
      bundleTensorCongr_tmul, fiberDetLineEquiv_prodEquiv]
    have hp : ((e₁ x).prodCongr (e₂ x)).toLinearEquiv =
        (e₁ x).toLinearEquiv.prodCongr (e₂ x).toLinearEquiv := by
      ext v : 1
      rfl
    rw [hp]
    simpa only [TensorProduct.congr_tmul, fiberDetLineEquiv_congrModelEquiv] using
      detLineCongr_prodCongr_detLineProdEquiv (e₁ x).toLinearEquiv (e₂ x).toLinearEquiv
        (fiberDetLineEquiv (K := K) (F₁ := F₁) (E₁ := E₁) x a ⊗ₜ
          fiberDetLineEquiv (K := K) (F₁ := F₂) (E₁ := E₂) x b)

end ModelNaturality

section Naturality

variable {E₁' : B → Type*}
  [∀ x, AddCommGroup (E₁' x)] [∀ x, Module K (E₁' x)]
  [∀ x, TopologicalSpace (E₁' x)] [TopologicalSpace (TotalSpace F₁ E₁')]
  [FiberBundle F₁ E₁'] [VectorBundle K F₁ E₁']
  {E₂' : B → Type*}
  [∀ x, AddCommGroup (E₂' x)] [∀ x, Module K (E₂' x)]
  [∀ x, TopologicalSpace (E₂' x)] [TopologicalSpace (TotalSpace F₂ E₂')]
  [FiberBundle F₂ E₂'] [VectorBundle K F₂ E₂']
  [∀ x, TopologicalSpace (DetBundle K F₁ E₁' x ⊗[K] DetBundle K F₂ E₂' x)]
  [∀ x, IsModuleTopology K (DetBundle K F₁ E₁' x ⊗[K] DetBundle K F₂ E₂' x)]

omit [CompleteSpace K] in
/-- For the same model, the presentation-independent transport is the existing native map. -/
theorem congrModelEquiv_eq_congrEquiv (e : ∀ x, E₁ x ≃L[K] E₁' x) (x : B) :
    congrModelEquiv (F₁ := F₁) (F' := F₁) e x = congrEquiv (F := F₁) e x := by
  ext a
  apply (linearEquiv K F₁ E₁' x).injective
  apply Subtype.ext
  rw [coe_congrModelEquiv, congrEquiv_apply, LinearEquiv.apply_symm_apply,
    coe_exteriorPower_apply]

omit [CompleteSpace K] in
/-- The Whitney comparison is natural for fibrewise bundle isomorphisms. The equation is for
all elements of the native tensor fibre, and requires no continuity of the family in the base. -/
theorem congrEquiv_prodEquiv (e₁ : ∀ x, E₁ x ≃L[K] E₁' x)
    (e₂ : ∀ x, E₂ x ≃L[K] E₂' x) (x : B)
    (t : DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x) :
    congrEquiv (F := F₁ × F₂) (fun y ↦ (e₁ y).prodCongr (e₂ y)) x
      (prodEquiv K F₁ E₁ F₂ E₂ x t) =
      prodEquiv K F₁ E₁' F₂ E₂' x
        (bundleTensorCongr (congrEquiv (F := F₁) e₁) (congrEquiv (F := F₂) e₂) x t) := by
  have h₁ : congrModelEquiv (F₁ := F₁) (F' := F₁) e₁ = congrEquiv (F := F₁) e₁ :=
    funext fun y ↦ congrModelEquiv_eq_congrEquiv e₁ y
  have h₂ : congrModelEquiv (F₁ := F₂) (F' := F₂) e₂ = congrEquiv (F := F₂) e₂ :=
    funext fun y ↦ congrModelEquiv_eq_congrEquiv e₂ y
  simpa only [congrModelEquiv_eq_congrEquiv, h₁, h₂] using
    congrModelEquiv_prodEquiv (F₁' := F₁) (F₂' := F₂) e₁ e₂ x t

end Naturality

section Symmetry

variable (K F₁ E₁ F₂ E₂) in
/-- The determinant action of exchanging the two bundle factors. It uses the actual fibre
permutation, including the change from model `F₁ × F₂` to model `F₂ × F₁`. -/
def prodCommEquiv (x : B) : DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂) x ≃L[K]
    DetBundle K (F₂ × F₁) (E₂ ×ᵇ E₁) x :=
  congrModelEquiv (F₁ := F₁ × F₂) (F' := F₂ × F₁)
    (fun y ↦ ContinuousLinearEquiv.prodComm K (E₁ y) (E₂ y)) x

omit [CompleteSpace K]
  [∀ x, IsModuleTopology K (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]
  [∀ x, TopologicalSpace (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)] in
private theorem fiberDetLineEquiv_prodCommEquiv (x : B)
    (a : DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂) x) :
    fiberDetLineEquiv (K := K) (F₁ := F₂ × F₁) (E₁ := E₂ ×ᵇ E₁) x
      (prodCommEquiv K F₁ E₁ F₂ E₂ x a) =
      (LinearEquiv.prodComm K (E₁ x) (E₂ x)).detLineCongr
        (fiberDetLineEquiv (K := K) (F₁ := F₁ × F₂) (E₁ := E₁ ×ᵇ E₂) x a) := by
  simpa only [prodCommEquiv, ContinuousLinearEquiv.prodComm_toLinearEquiv] using
    fiberDetLineEquiv_congrModelEquiv (F₁ := F₁ × F₂) (F' := F₂ × F₁)
      (fun y ↦ ContinuousLinearEquiv.prodComm K (E₁ y) (E₂ y)) x a

variable [∀ x, TopologicalSpace (DetBundle K F₂ E₂ x ⊗[K] DetBundle K F₁ E₁ x)]
  [∀ x, IsModuleTopology K (DetBundle K F₂ E₂ x ⊗[K] DetBundle K F₁ E₁ x)]

omit [CompleteSpace K] in
/-- Exchanging the bundle factors multiplies the native Whitney comparison by exactly the
Koszul sign `(-1)^(rank F₁ * rank F₂)`, including when either rank is zero. -/
theorem prodCommEquiv_prodEquiv (x : B)
    (t : DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x) :
    prodCommEquiv K F₁ E₁ F₂ E₂ x (prodEquiv K F₁ E₁ F₂ E₂ x t) =
      (-1 : K) ^ (finrank K F₁ * finrank K F₂) •
        prodEquiv K F₂ E₂ F₁ E₁ x (bundleTensorCommEquiv x t) := by
  let : FiniteDimensional K (E₁ x) := VectorBundle.finiteDimensional K F₁ E₁ x
  let : FiniteDimensional K (E₂ x) := VectorBundle.finiteDimensional K F₂ E₂ x
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht, smul_add]
  | tmul a b =>
    apply (fiberDetLineEquiv (K := K) (F₁ := F₂ × F₁) (E₁ := E₂ ×ᵇ E₁) x).injective
    rw [fiberDetLineEquiv_prodCommEquiv, fiberDetLineEquiv_prodEquiv, map_smul,
      bundleTensorCommEquiv_tmul, fiberDetLineEquiv_prodEquiv]
    simpa only [TensorProduct.congr_tmul, TensorProduct.comm_tmul,
      VectorBundle.finrank_eq K F₁ E₁ x, VectorBundle.finrank_eq K F₂ E₂ x] using
      detLineCongr_prodComm_detLineProdEquiv
        (fiberDetLineEquiv (K := K) (F₁ := F₁) (E₁ := E₁) x a ⊗ₜ
          fiberDetLineEquiv (K := K) (F₁ := F₂) (E₁ := E₂) x b)

end Symmetry

section Associativity

variable {F₃ : Type*} [NormedAddCommGroup F₃] [NormedSpace K F₃] [FiniteDimensional K F₃]
  {E₃ : B → Type*} [∀ x, AddCommGroup (E₃ x)] [∀ x, Module K (E₃ x)]
  [∀ x, TopologicalSpace (E₃ x)] [TopologicalSpace (TotalSpace F₃ E₃)]
  [FiberBundle F₃ E₃] [VectorBundle K F₃ E₃]

variable (K F₁ E₁ F₂ E₂ F₃ E₃) in
/-- The determinant action of the canonical reassociation of three bundle factors, with its
corresponding change of model. -/
def prodAssocEquiv (x : B) :
    DetBundle K ((F₁ × F₂) × F₃) ((E₁ ×ᵇ E₂) ×ᵇ E₃) x ≃L[K]
      DetBundle K (F₁ × (F₂ × F₃)) (E₁ ×ᵇ (E₂ ×ᵇ E₃)) x :=
  congrModelEquiv (F₁ := (F₁ × F₂) × F₃) (F' := F₁ × (F₂ × F₃))
    (fun y ↦ ContinuousLinearEquiv.prodAssoc K (E₁ y) (E₂ y) (E₃ y)) x

omit [CompleteSpace K]
  [∀ x, IsModuleTopology K (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]
  [∀ x, TopologicalSpace (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)] in
private theorem fiberDetLineEquiv_prodAssocEquiv (x : B)
    (a : DetBundle K ((F₁ × F₂) × F₃) ((E₁ ×ᵇ E₂) ×ᵇ E₃) x) :
    fiberDetLineEquiv (K := K) (F₁ := F₁ × (F₂ × F₃)) (E₁ := E₁ ×ᵇ (E₂ ×ᵇ E₃)) x
      (prodAssocEquiv K F₁ E₁ F₂ E₂ F₃ E₃ x a) =
      (LinearEquiv.prodAssoc K (E₁ x) (E₂ x) (E₃ x)).detLineCongr
        (fiberDetLineEquiv (K := K) (F₁ := (F₁ × F₂) × F₃)
          (E₁ := (E₁ ×ᵇ E₂) ×ᵇ E₃) x a) := by
  simpa only [prodAssocEquiv, ContinuousLinearEquiv.prodAssoc_toLinearEquiv] using
    fiberDetLineEquiv_congrModelEquiv (F₁ := (F₁ × F₂) × F₃) (F' := F₁ × (F₂ × F₃))
      (fun y ↦ ContinuousLinearEquiv.prodAssoc K (E₁ y) (E₂ y) (E₃ y)) x a

variable
  [∀ x, TopologicalSpace (DetBundle K F₂ E₂ x ⊗[K] DetBundle K F₃ E₃ x)]
  [∀ x, IsModuleTopology K (DetBundle K F₂ E₂ x ⊗[K] DetBundle K F₃ E₃ x)]
  [∀ x, TopologicalSpace (DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂) x ⊗[K] DetBundle K F₃ E₃ x)]
  [∀ x, IsModuleTopology K
    (DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂) x ⊗[K] DetBundle K F₃ E₃ x)]
  [∀ x, TopologicalSpace (DetBundle K F₁ E₁ x ⊗[K] DetBundle K (F₂ × F₃) (E₂ ×ᵇ E₃) x)]
  [∀ x, IsModuleTopology K
    (DetBundle K F₁ E₁ x ⊗[K] DetBundle K (F₂ × F₃) (E₂ ×ᵇ E₃) x)]
  [∀ x, TopologicalSpace ((DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x) ⊗[K]
    DetBundle K F₃ E₃ x)]
  [∀ x, IsModuleTopology K ((DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x) ⊗[K]
    DetBundle K F₃ E₃ x)]
  [∀ x, TopologicalSpace (DetBundle K F₁ E₁ x ⊗[K]
    (DetBundle K F₂ E₂ x ⊗[K] DetBundle K F₃ E₃ x))]
  [∀ x, IsModuleTopology K (DetBundle K F₁ E₁ x ⊗[K]
    (DetBundle K F₂ E₂ x ⊗[K] DetBundle K F₃ E₃ x))]

omit [CompleteSpace K] in
/-- The two native Whitney identifications for three bundles agree under the product and
tensor associators. The equation holds on the full tensor fibre and introduces no sign. -/
theorem prodAssocEquiv_prodEquiv (x : B)
    (t : (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x) ⊗[K] DetBundle K F₃ E₃ x) :
    prodAssocEquiv K F₁ E₁ F₂ E₂ F₃ E₃ x
      (prodEquiv K (F₁ × F₂) (E₁ ×ᵇ E₂) F₃ E₃ x
        (bundleTensorCongr (prodEquiv K F₁ E₁ F₂ E₂)
          (fun y ↦ ContinuousLinearEquiv.refl K (DetBundle K F₃ E₃ y)) x t)) =
      prodEquiv K F₁ E₁ (F₂ × F₃) (E₂ ×ᵇ E₃) x
        (bundleTensorCongr (fun y ↦ ContinuousLinearEquiv.refl K (DetBundle K F₁ E₁ y))
          (prodEquiv K F₂ E₂ F₃ E₃) x (bundleTensorAssocEquiv x t)) := by
  let : FiniteDimensional K (E₁ x) := VectorBundle.finiteDimensional K F₁ E₁ x
  let : FiniteDimensional K (E₂ x) := VectorBundle.finiteDimensional K F₂ E₂ x
  let : FiniteDimensional K (E₃ x) := VectorBundle.finiteDimensional K F₃ E₃ x
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul ab c =>
    induction ab using TensorProduct.inductionOn with
    | add s t hs ht => simp only [TensorProduct.add_tmul, map_add, hs, ht]
    | tmul a b =>
      simp only [bundleTensorCongr_tmul, ContinuousLinearEquiv.refl_apply,
        bundleTensorAssocEquiv_tmul]
      apply (fiberDetLineEquiv (K := K) (F₁ := F₁ × (F₂ × F₃))
        (E₁ := E₁ ×ᵇ (E₂ ×ᵇ E₃)) x).injective
      rw [fiberDetLineEquiv_prodAssocEquiv, fiberDetLineEquiv_prodEquiv,
        fiberDetLineEquiv_prodEquiv]
      simpa only [TensorProduct.congr_tmul, fiberDetLineEquiv_prodEquiv,
        LinearMap.rTensor_tmul, LinearMap.lTensor_tmul, TensorProduct.assoc_tmul,
        LinearEquiv.coe_coe] using
        detLineCongr_prodAssoc_detLineProdEquiv
          ((fiberDetLineEquiv (K := K) (F₁ := F₁) (E₁ := E₁) x a ⊗ₜ
            fiberDetLineEquiv (K := K) (F₁ := F₂) (E₁ := E₂) x b) ⊗ₜ
              fiberDetLineEquiv (K := K) (F₁ := F₃) (E₁ := E₃) x c)

end Associativity

section Pullback

variable {B' : Type*} [TopologicalSpace B']
  {T : Type*} [FunLike T B' B] [ContinuousMapClass T B' B]

variable (f : T)
  [∀ y, TopologicalSpace (DetBundle K F₁ ((f : B' → B) *ᵖ E₁) y ⊗[K]
    DetBundle K F₂ ((f : B' → B) *ᵖ E₂) y)]
  [∀ y, IsModuleTopology K (DetBundle K F₁ ((f : B' → B) *ᵖ E₁) y ⊗[K]
    DetBundle K F₂ ((f : B' → B) *ᵖ E₂) y)]

/-- In every pair of pulled-back charts, the native Whitney product of the determinant
pullbacks has exactly the original product coordinate. This is the pullback comparison on
pure tensor generators, using the existing native determinant pullback maps. -/
theorem chartCoord_pullback_prodEquiv_tmul
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [e₁.IsLinear K] [e₂.IsLinear K] {y : B'}
    (hx₁ : f y ∈ e₁.baseSet) (hx₂ : f y ∈ e₂.baseSet)
    (a : DetBundle K F₁ E₁ (f y)) (b : DetBundle K F₂ E₂ (f y)) :
    chartCoord ((e₁.pullback f).prod (e₂.pullback f))
      (by simpa only [Trivialization.prod_baseSet, Trivialization.pullback_baseSet,
        Set.mem_inter_iff, Set.mem_preimage] using And.intro hx₁ hx₂)
      (prodEquiv K F₁ ((f : B' → B) *ᵖ E₁) F₂ ((f : B' → B) *ᵖ E₂) y
        (pullbackEquiv (F := F₁) (E := E₁) (f : B' → B) y a ⊗ₜ
          pullbackEquiv (F := F₂) (E := E₂) (f : B' → B) y b)) =
      chartCoord (e₁.prod e₂)
        (by simpa only [Trivialization.prod_baseSet, Set.mem_inter_iff] using And.intro hx₁ hx₂)
        (prodEquiv K F₁ E₁ F₂ E₂ (f y) (a ⊗ₜ b)) := by
  have hy₁ : y ∈ (e₁.pullback f).baseSet := by
    simpa only [Trivialization.pullback_baseSet, Set.mem_preimage] using hx₁
  have hy₂ : y ∈ (e₂.pullback f).baseSet := by
    simpa only [Trivialization.pullback_baseSet, Set.mem_preimage] using hx₂
  rw [chartCoord_prodEquiv_tmul _ _ hy₁ hy₂, chartCoord_prodEquiv_tmul _ _ hx₁ hx₂,
    chartCoord_pullbackEquiv e₁ f hy₁ a, chartCoord_pullbackEquiv e₂ f hy₂ b]


private def pullbackPointLinearEquiv (y : B') :
    DetBundle K F₁ E₁ (f y) ≃ₗ[K] DetBundle K F₁ ((f : B' → B) *ᵖ E₁) y := by
  let e := trivializationAt F₁ E₁ (f y)
  have hx : f y ∈ e.baseSet := mem_baseSet_trivializationAt F₁ E₁ (f y)
  have hy : y ∈ (e.pullback f).baseSet := by
    simpa only [Trivialization.pullback_baseSet, Set.mem_preimage] using hx
  exact (chartCoord e hx).trans (chartCoord (e.pullback f) hy).symm

omit [CompleteSpace K] in
private theorem pullbackPointLinearEquiv_apply (y : B') (a : DetBundle K F₁ E₁ (f y)) :
    pullbackPointLinearEquiv f y a =
      pullbackEquiv (𝕜 := K) (F := F₁) (E := E₁) (f : B' → B) y a := by
  let e := trivializationAt F₁ E₁ (f y)
  have hx : f y ∈ e.baseSet := mem_baseSet_trivializationAt F₁ E₁ (f y)
  have hy : y ∈ (e.pullback f).baseSet := by
    simpa only [Trivialization.pullback_baseSet, Set.mem_preimage] using hx
  apply (chartCoord (e.pullback f) hy).injective
  rw [show pullbackPointLinearEquiv f y =
    (chartCoord e hx).trans (chartCoord (e.pullback f) hy).symm from rfl,
    LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  exact (chartCoord_pullbackEquiv e f hy a).symm

variable (K F₁ E₁ F₂ E₂) in
/-- The canonical comparison from the original determinant tensor fibre at `f y` to the
native tensor of the two determinant pullbacks. -/
def prodPullbackTensorEquiv (y : B') :
    DetBundle K F₁ E₁ (f y) ⊗[K] DetBundle K F₂ E₂ (f y) ≃L[K]
      DetBundle K F₁ ((f : B' → B) *ᵖ E₁) y ⊗[K]
        DetBundle K F₂ ((f : B' → B) *ᵖ E₂) y :=
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology
    (TensorProduct.congr
      (pullbackPointLinearEquiv (K := K) (F₁ := F₁) (E₁ := E₁) f y)
      (pullbackPointLinearEquiv (K := K) (F₁ := F₂) (E₁ := E₂) f y))

omit [CompleteSpace K] in
/-- The tensor pullback comparison uses the existing determinant pullback map on each factor. -/
theorem prodPullbackTensorEquiv_tmul (y : B')
    (a : DetBundle K F₁ E₁ (f y)) (b : DetBundle K F₂ E₂ (f y)) :
    prodPullbackTensorEquiv K F₁ E₁ F₂ E₂ f y (a ⊗ₜ b) =
      pullbackEquiv (𝕜 := K) (F := F₁) (E := E₁) (f : B' → B) y a ⊗ₜ
        pullbackEquiv (𝕜 := K) (F := F₂) (E := E₂) (f : B' → B) y b := by
  have hp := congrFun (LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology
    (TensorProduct.congr
      (pullbackPointLinearEquiv (K := K) (F₁ := F₁) (E₁ := E₁) f y)
      (pullbackPointLinearEquiv (K := K) (F₁ := F₂) (E₁ := E₂) f y))) (a ⊗ₜ b)
  unfold prodPullbackTensorEquiv
  rw [hp, TensorProduct.congr_tmul, pullbackPointLinearEquiv_apply f y a,
    pullbackPointLinearEquiv_apply f y b]

private def prodPullbackLinearEquiv (y : B') :
    DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂) (f y) ≃ₗ[K]
      DetBundle K (F₁ × F₂) (((f : B' → B) *ᵖ E₁) ×ᵇ ((f : B' → B) *ᵖ E₂)) y := by
  let e₁ := trivializationAt F₁ E₁ (f y)
  let e₂ := trivializationAt F₂ E₂ (f y)
  have hx : f y ∈ (e₁.prod e₂).baseSet := by
    simpa only [Trivialization.prod_baseSet, Set.mem_inter_iff] using
      And.intro (mem_baseSet_trivializationAt F₁ E₁ (f y))
        (mem_baseSet_trivializationAt F₂ E₂ (f y))
  have hy : y ∈ ((e₁.pullback f).prod (e₂.pullback f)).baseSet := by
    simpa only [Trivialization.prod_baseSet, Trivialization.pullback_baseSet,
      Set.mem_inter_iff, Set.mem_preimage] using hx
  exact (chartCoord (e₁.prod e₂) hx).trans
    (chartCoord ((e₁.pullback f).prod (e₂.pullback f)) hy).symm

variable (K F₁ E₁ F₂ E₂) in
/-- The determinant comparison for reindexing a product bundle. The target is the product of
the pulled-back bundles, with its native module data. Original product coordinates and the
product of their pullback charts define this map independently of the Whitney comparison. -/
def prodPullbackEquiv (y : B') :
    DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂) (f y) ≃L[K]
      DetBundle K (F₁ × F₂) (((f : B' → B) *ᵖ E₁) ×ᵇ ((f : B' → B) *ᵖ E₂)) y :=
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology
    (prodPullbackLinearEquiv (K := K) (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂) f y)


omit [CompleteSpace K]
  [∀ x, IsModuleTopology K (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]
  [∀ x, TopologicalSpace (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]
  [∀ y, IsModuleTopology K (DetBundle K F₁ ((f : B' → B) *ᵖ E₁) y ⊗[K]
    DetBundle K F₂ ((f : B' → B) *ᵖ E₂) y)]
  [∀ y, TopologicalSpace (DetBundle K F₁ ((f : B' → B) *ᵖ E₁) y ⊗[K]
    DetBundle K F₂ ((f : B' → B) *ᵖ E₂) y)] in
/-- The product pullback map identifies original product coordinates with the product of the
pulled-back coordinates. This characterization is independent of the Whitney comparison. -/
theorem prodPullbackEquiv_apply (y : B') (v : DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂) (f y)) :
    let e₁ := trivializationAt F₁ E₁ (f y)
    let e₂ := trivializationAt F₂ E₂ (f y)
    let hx : f y ∈ (e₁.prod e₂).baseSet := by
      simpa only [Trivialization.prod_baseSet, Set.mem_inter_iff] using
        And.intro (mem_baseSet_trivializationAt F₁ E₁ (f y))
          (mem_baseSet_trivializationAt F₂ E₂ (f y))
    let hy : y ∈ ((e₁.pullback f).prod (e₂.pullback f)).baseSet := by
      simpa only [Trivialization.prod_baseSet, Trivialization.pullback_baseSet,
        Set.mem_inter_iff, Set.mem_preimage] using hx
    prodPullbackEquiv K F₁ E₁ F₂ E₂ f y v =
      (chartCoord ((e₁.pullback f).prod (e₂.pullback f)) hy).symm
        (chartCoord (e₁.prod e₂) hx v) := by
  dsimp only
  have hp := congrFun (LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology
    (prodPullbackLinearEquiv (K := K) (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂) f y)) v
  unfold prodPullbackEquiv
  rw [hp]
  rfl

/-- The full native Whitney square commutes with pullback. Both comparisons retain their
native carriers, rather than identifying opaque module data by a type cast. -/
theorem prodPullbackEquiv_prodEquiv (y : B')
    (t : DetBundle K F₁ E₁ (f y) ⊗[K] DetBundle K F₂ E₂ (f y)) :
    prodPullbackEquiv K F₁ E₁ F₂ E₂ f y (prodEquiv K F₁ E₁ F₂ E₂ (f y) t) =
      prodEquiv K F₁ ((f : B' → B) *ᵖ E₁) F₂ ((f : B' → B) *ᵖ E₂) y
        (prodPullbackTensorEquiv K F₁ E₁ F₂ E₂ f y t) := by
  let e₁ := trivializationAt F₁ E₁ (f y)
  let e₂ := trivializationAt F₂ E₂ (f y)
  have hx₁ : f y ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ E₁ (f y)
  have hx₂ : f y ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ E₂ (f y)
  have hy : y ∈ ((e₁.pullback f).prod (e₂.pullback f)).baseSet := by
    simpa only [Trivialization.prod_baseSet, Trivialization.pullback_baseSet,
      Set.mem_inter_iff, Set.mem_preimage] using And.intro hx₁ hx₂
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b =>
    rw [prodPullbackTensorEquiv_tmul]
    apply (chartCoord ((e₁.pullback f).prod (e₂.pullback f)) hy).injective
    have hc := prodPullbackEquiv_apply f y
      (prodEquiv K F₁ E₁ F₂ E₂ (f y) (a ⊗ₜ b))
    dsimp only at hc
    rw [hc, LinearEquiv.apply_symm_apply]
    exact (chartCoord_pullback_prodEquiv_tmul f e₁ e₂ hx₁ hx₂ a b).symm

end Pullback

section RankZero

private def zeroLinearEquiv (h : finrank K F₁ = 0) (x : B) : DetBundle K F₁ E₁ x ≃ₗ[K] K :=
  (linearEquiv K F₁ E₁ x).trans
    ((LinearEquiv.ofEq _ _ (congrArg (⋀[K]^· (E₁ x)) h)).trans
      (exteriorPower.zeroEquiv K (E₁ x)))

variable (K F₁ E₁) in
/-- A rank-zero determinant fibre has its canonical empty-exterior-product coordinate. This
unit coordinate uses no choice of a basis of a positive-rank determinant line. -/
def zeroEquiv (h : finrank K F₁ = 0) (x : B) : DetBundle K F₁ E₁ x ≃L[K] K :=
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology
    (zeroLinearEquiv (K := K) (F₁ := F₁) (E₁ := E₁) h x)

omit [CompleteSpace K] [FiniteDimensional K F₁] [VectorBundle K F₁ E₁]
  [TopologicalSpace B] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁]
  [∀ x, IsModuleTopology K (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]
  [∀ x, TopologicalSpace (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)] in
/-- In rank zero, the native exterior-algebra image is the scalar empty product. -/
theorem coe_linearEquiv_zeroEquiv (h : finrank K F₁ = 0) (x : B)
    (a : DetBundle K F₁ E₁ x) :
    (linearEquiv K F₁ E₁ x a : ExteriorAlgebra K (E₁ x)) =
      algebraMap K (ExteriorAlgebra K (E₁ x)) (zeroEquiv K F₁ E₁ h x a) := by
  have hp := congrFun (LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology
    (zeroLinearEquiv (K := K) (F₁ := F₁) (E₁ := E₁) h x)) a
  unfold zeroEquiv
  rw [hp]
  have hz := coe_degree_zero
    ((LinearEquiv.ofEq _ _ (congrArg (⋀[K]^· (E₁ x)) h)) (linearEquiv K F₁ E₁ x a))
  simpa only [zeroLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply] using hz

omit [CompleteSpace K] in
/-- A zero-rank left factor acts by its canonical scalar unit coordinate. This applies to
all determinant vectors, including the empty exterior product. -/
theorem coe_prodEquiv_tmul_of_finrank_left_eq_zero (h : finrank K F₁ = 0) (x : B)
    (a : DetBundle K F₁ E₁ x) (b : DetBundle K F₂ E₂ x) :
    (linearEquiv K (F₁ × F₂) (E₁ ×ᵇ E₂) x (prodEquiv K F₁ E₁ F₂ E₂ x (a ⊗ₜ b)) :
      ExteriorAlgebra K (E₁ x × E₂ x)) =
      zeroEquiv K F₁ E₁ h x a •
        ExteriorAlgebra.map (LinearMap.inr K (E₁ x) (E₂ x)) (linearEquiv K F₂ E₂ x b) := by
  rw [coe_prodEquiv_tmul, coe_linearEquiv_zeroEquiv h]
  simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, smul_mul_assoc, one_mul]

omit [CompleteSpace K] in
/-- A zero-rank right factor acts by its canonical scalar unit coordinate. -/
theorem coe_prodEquiv_tmul_of_finrank_right_eq_zero (h : finrank K F₂ = 0) (x : B)
    (a : DetBundle K F₁ E₁ x) (b : DetBundle K F₂ E₂ x) :
    (linearEquiv K (F₁ × F₂) (E₁ ×ᵇ E₂) x (prodEquiv K F₁ E₁ F₂ E₂ x (a ⊗ₜ b)) :
      ExteriorAlgebra K (E₁ x × E₂ x)) =
      zeroEquiv K F₂ E₂ h x b •
        ExteriorAlgebra.map (LinearMap.inl K (E₁ x) (E₂ x)) (linearEquiv K F₁ E₁ x a) := by
  rw [coe_prodEquiv_tmul, coe_linearEquiv_zeroEquiv h]
  simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, mul_smul_comm, mul_one]

end RankZero

end TauCeti.DetBundle
