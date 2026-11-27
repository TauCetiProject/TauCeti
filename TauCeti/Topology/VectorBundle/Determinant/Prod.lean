/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Determinant
public import TauCeti.Topology.VectorBundle.Determinant.Trivial
public import TauCeti.Topology.VectorBundle.TensorProduct.Operations
public import TauCeti.LinearAlgebra.Determinant.DirectSum
public import TauCeti.Topology.VectorBundle.Trivialization
public import TauCeti.Topology.Algebra.Module.Equiv.Prod

/-!
# The determinant line of a product of vector bundles

For finite-rank vector bundles, the Whitney comparison identifies `det E ⊗ det E'` with
`det (E ⊕ E')`; its inverse gives the determinant-product identification used in first-Chern-class
additivity. Exterior factors follow the order of the two bundles, and all ranks, including zero,
are allowed.

## Main declarations

* `TauCeti.DetBundle.prodEquiv` and `TauCeti.DetBundle.prodHomeomorph` give the fibrewise
  continuous linear equivalence and total-space homeomorphism.
* `TauCeti.DetBundle.fiberDetLineEquiv_prodEquiv` reads the Whitney comparison as
  `TauCeti.detLineProdEquiv` on the intrinsic top exterior powers of the fibres.
* `TauCeti.DetBundle.congrModelEquiv_prodEquiv` gives naturality for fibrewise families of
  continuous linear equivalences between arbitrary model presentations.
* `TauCeti.DetBundle.prodCommEquiv_prodEquiv` and `TauCeti.DetBundle.prodAssocEquiv_prodEquiv`
  give the rank-dependent swap sign and the sign-free associativity law.
* `TauCeti.DetBundle.prodPullbackEquiv` is the canonical determinant pullback of the product
  bundle, read on the product of the pulled-back bundles, and
  `TauCeti.DetBundle.prodPullbackEquiv_prodEquiv` is the native pullback square.
* `TauCeti.DetBundle.chartCoord_prodPullbackEquiv` and
  `TauCeti.DetBundle.coe_prodPullbackEquiv` characterize its arbitrary-chart and intrinsic action.
* `TauCeti.DetBundle.trivialProdEquiv` and `TauCeti.DetBundle.trivialProdHomeomorph`: a trivial
  summand does not change the determinant line, `det E ≃ det ((B × V) ⊕ E)`, by
  `a ↦ ω ⊗ a ↦ ω ∧ a` for the constant section `ω` of `det (B × V) = B × K` with value `1`.
* `TauCeti.DetBundle.coe_prodEquiv_tmul_of_finrank_left_eq_zero` and
  `TauCeti.DetBundle.coe_prodEquiv_tmul_of_finrank_right_eq_zero` give the empty-product unit
  formulas, using `TauCeti.DetBundle.zeroEquiv` from the determinant module.
-/

public section

noncomputable section

open Bundle FiberBundle Module Set TopologicalSpace
open scoped Bundle TensorProduct

universe u v₁ v₂ w w₁ w₂

namespace TauCeti.DetBundle

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
  simp only [prodModelEquiv, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology]
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
  exact (TensorProduct.congr (fiberDetLineEquiv (K := K) (F₁ := F₁) (E₁ := E₁) x)
      (fiberDetLineEquiv (K := K) (F₁ := F₂) (E₁ := E₂) x)).trans
    ((detLineProdEquiv K (E₁ x) (E₂ x)).trans
      (fiberDetLineEquiv (K := K) (F₁ := F₁ × F₂) (E₁ := E₁ ×ᵇ E₂) x).symm)

variable [∀ x, TopologicalSpace (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]
  [∀ x, IsModuleTopology K (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]

variable (K F₁ E₁ F₂ E₂) in
/-- The fibrewise Whitney comparison for the native determinant bundles. It orders the first
bundle before the second and applies also when either model fibre has rank zero. -/
def prodEquiv (x : B) : DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x ≃L[K]
    DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂) x :=
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology
    (prodLinearEquiv (K := K) (F₁ := F₁) (E₁ := E₁) (F₂ := F₂) (E₂ := E₂) x)

/-- Read in the intrinsic top exterior powers of the fibres, the Whitney comparison is the
determinant-line product `TauCeti.detLineProdEquiv` on every element of the tensor fibre. -/
theorem fiberDetLineEquiv_prodEquiv (x : B)
    [FiniteDimensional K (E₁ x)] [FiniteDimensional K (E₂ x)]
    (t : DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x) :
    fiberDetLineEquiv (K := K) (F₁ := F₁ × F₂) (E₁ := E₁ ×ᵇ E₂) x
      (prodEquiv K F₁ E₁ F₂ E₂ x t) =
      detLineProdEquiv K (E₁ x) (E₂ x)
        (TensorProduct.congr (fiberDetLineEquiv (K := K) (F₁ := F₁) (E₁ := E₁) x)
          (fiberDetLineEquiv (K := K) (F₁ := F₂) (E₁ := E₂) x) t) := by
  simp only [prodEquiv, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology,
    prodLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]

/-- In the exterior algebra, the Whitney comparison is the exterior product of the images of
its two determinant-line factors. This description includes the empty exterior product. -/
theorem coe_prodEquiv_tmul (x : B) (a : DetBundle K F₁ E₁ x) (b : DetBundle K F₂ E₂ x) :
    (linearEquiv K (F₁ × F₂) (E₁ ×ᵇ E₂) x (prodEquiv K F₁ E₁ F₂ E₂ x (a ⊗ₜ b)) :
        ExteriorAlgebra K (E₁ x × E₂ x)) =
      ExteriorAlgebra.map (LinearMap.inl K (E₁ x) (E₂ x)) (linearEquiv K F₁ E₁ x a) *
        ExteriorAlgebra.map (LinearMap.inr K (E₁ x) (E₂ x)) (linearEquiv K F₂ E₂ x b) := by
  let : FiniteDimensional K (E₁ x) := VectorBundle.finiteDimensional K F₁ E₁ x
  let : FiniteDimensional K (E₂ x) := VectorBundle.finiteDimensional K F₂ E₂ x
  rw [← coe_fiberDetLineEquiv, fiberDetLineEquiv_prodEquiv, TensorProduct.congr_tmul,
    coe_detLineProdEquiv_tmul_eq_mul, coe_fiberDetLineEquiv, coe_fiberDetLineEquiv]

variable [CompleteSpace K]

/-- The Whitney comparison in any pair of linear charts is the fixed model conjugation.
No compatibility of the chosen model bases with the product basis is assumed. -/
theorem chartCoord_prodEquiv_tmul
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [e₁.IsLinear K] [e₂.IsLinear K] {x : B} (hx₁ : x ∈ e₁.baseSet) (hx₂ : x ∈ e₂.baseSet)
    (a : DetBundle K F₁ E₁ x) (b : DetBundle K F₂ E₂ x) :
    chartCoord (e₁.prod e₂)
      (Trivialization.mem_prod_baseSet hx₁ hx₂)
      (prodEquiv K F₁ E₁ F₂ E₂ x (a ⊗ₜ b)) =
      prodModelEquiv K F₁ F₂ ⟨chartCoord e₁ hx₁ a ⊗ₜ chartCoord e₂ hx₂ b⟩ := by
  simp only [chartCoord_apply, prodModelEquiv_tmul, LinearEquiv.symm_apply_apply]
  apply congrArg (modelCoord (F₁ × F₂))
  apply Subtype.ext
  rw [LinearEquiv.coe_exteriorPower_apply, coe_prodEquiv_tmul,
    coe_detLineProdEquiv_tmul_eq_mul,
    LinearEquiv.coe_exteriorPower_apply,
    LinearEquiv.coe_exteriorPower_apply]
  let e := (e₁.prod e₂).linearEquivAt K x
    (Trivialization.mem_prod_baseSet hx₁ hx₂)
  have he : e = (e₁.linearEquivAt K x hx₁).prodCongr (e₂.linearEquivAt K x hx₂) :=
    Trivialization.linearEquivAt_prod e₁ e₂ hx₁ hx₂
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
  have hp := FiberBundle.trivializationAt_prod F₁ E₁ F₂ E₂ a
  have ht : x ∈ (trivializationAt K (DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂)) a).baseSet := by
    simpa only [trivializationAt_eq, trivialization_baseSet, hp] using
      (Trivialization.mem_prod_baseSet hx₁ hx₂)
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.symmL_apply (R := K) _ hs,
    tensorProduct_trivializationAt_symm_apply_tmul hd₁ hd₂]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem K _ ht]
  simp only [ContinuousLinearEquiv.coe_coe, trivializationAt_eq,
    trivialization_symm_apply _ hx₁, trivialization_symm_apply _ hx₂, hp]
  rw [trivialization_apply_mk _ (Trivialization.mem_prod_baseSet hx₁ hx₂)]
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
/-- The Whitney homeomorphism from the native tensor total space, modelled on
`ProjectiveTensor K K K`, to the determinant total space modelled on `K`. -/
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
/-- Whitney naturality for fibrewise families of continuous linear equivalences between
different model presentations and independent universes. The families need not be continuous
in the base; no compatibility of chosen model bases is assumed. -/
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
    rw [ContinuousLinearEquiv.prodCongr_toLinearEquiv]
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
/-- The Whitney comparison is natural for fibrewise families of continuous linear equivalences
between bundles with the same models. The equation is for all elements of the native tensor
fibre, and requires no continuity of the family in the base. -/
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
      (Trivialization.mem_prod_pullback_baseSet f hx₁ hx₂)
      (prodEquiv K F₁ ((f : B' → B) *ᵖ E₁) F₂ ((f : B' → B) *ᵖ E₂) y
        (pullbackEquiv (F := F₁) (E := E₁) (f : B' → B) y a ⊗ₜ
          pullbackEquiv (F := F₂) (E := E₂) (f : B' → B) y b)) =
      chartCoord (e₁.prod e₂)
        (Trivialization.mem_prod_baseSet hx₁ hx₂)
        (prodEquiv K F₁ E₁ F₂ E₂ (f y) (a ⊗ₜ b)) := by
  have hy₁ : y ∈ (e₁.pullback f).baseSet := by
    simpa only [Trivialization.pullback_baseSet, Set.mem_preimage] using hx₁
  have hy₂ : y ∈ (e₂.pullback f).baseSet := by
    simpa only [Trivialization.pullback_baseSet, Set.mem_preimage] using hx₂
  rw [chartCoord_prodEquiv_tmul _ _ hy₁ hy₂, chartCoord_prodEquiv_tmul _ _ hx₁ hx₂,
    chartCoord_pullbackEquiv e₁ f hy₁ a, chartCoord_pullbackEquiv e₂ f hy₂ b]


variable (K F₁ E₁ F₂ E₂) in
/-- The canonical comparison from the original determinant tensor fibre at `f y` to the
native tensor of the two determinant pullbacks. -/
def prodPullbackTensorEquiv (y : B') :
    DetBundle K F₁ E₁ (f y) ⊗[K] DetBundle K F₂ E₂ (f y) ≃L[K]
      DetBundle K F₁ ((f : B' → B) *ᵖ E₁) y ⊗[K]
        DetBundle K F₂ ((f : B' → B) *ᵖ E₂) y := by
  letI : ∀ z : B', TopologicalSpace
      (DetBundle K F₁ E₁ (f z) ⊗[K] DetBundle K F₂ E₂ (f z)) := fun z ↦ inferInstance
  letI : ∀ z : B', IsModuleTopology K
      (DetBundle K F₁ E₁ (f z) ⊗[K] DetBundle K F₂ E₂ (f z)) := fun z ↦ inferInstance
  exact bundleTensorCongr
    (E₁ := fun z : B' ↦ DetBundle K F₁ E₁ (f z))
    (E₂ := fun z : B' ↦ DetBundle K F₂ E₂ (f z))
    (fun z ↦ pullbackEquiv (𝕜 := K) (F := F₁) (E := E₁) (f : B' → B) z)
    (fun z ↦ pullbackEquiv (𝕜 := K) (F := F₂) (E := E₂) (f : B' → B) z) y

omit [CompleteSpace K] [TopologicalSpace B]
  [FiniteDimensional K F₁] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
  [FiniteDimensional K F₂] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
  [TopologicalSpace B'] [ContinuousMapClass T B' B] in
/-- The tensor pullback comparison uses the existing determinant pullback map on each factor. -/
@[simp]
theorem prodPullbackTensorEquiv_tmul (y : B')
    (a : DetBundle K F₁ E₁ (f y)) (b : DetBundle K F₂ E₂ (f y)) :
    prodPullbackTensorEquiv K F₁ E₁ F₂ E₂ f y (a ⊗ₜ b) =
      pullbackEquiv (𝕜 := K) (F := F₁) (E := E₁) (f : B' → B) y a ⊗ₜ
        pullbackEquiv (𝕜 := K) (F := F₂) (E := E₂) (f : B' → B) y b := by
  unfold prodPullbackTensorEquiv
  apply bundleTensorCongr_tmul

variable (K F₁ E₁ F₂ E₂) in
/-- The canonical determinant pullback `TauCeti.DetBundle.pullbackEquiv` of the product bundle
`E₁ ×ᵇ E₂`, with target the determinant fibre of the product `(f *ᵖ E₁) ×ᵇ (f *ᵖ E₂)` of the
pulled-back bundles. Both target fibres are `⋀ (E₁ (f y) × E₂ (f y))`, but their module
structures are the pullback of the product structure and the product of the pullback structures,
which agree only after unfolding `Bundle.Pullback`. -/
def prodPullbackEquiv (y : B') :
    DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂) (f y) ≃L[K]
      DetBundle K (F₁ × F₂) (((f : B' → B) *ᵖ E₁) ×ᵇ ((f : B' → B) *ᵖ E₂)) y :=
  pullbackEquiv (𝕜 := K) (F := F₁ × F₂) (E := E₁ ×ᵇ E₂) (f : B' → B) y

omit [CompleteSpace K] [TopologicalSpace B]
  [FiniteDimensional K F₁] [∀ x, TopologicalSpace (E₁ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
  [FiniteDimensional K F₂] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₂ E₂)] [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
  [TopologicalSpace B'] [ContinuousMapClass T B' B]
  [∀ x, IsModuleTopology K (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]
  [∀ x, TopologicalSpace (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]
  [∀ y, IsModuleTopology K (DetBundle K F₁ ((f : B' → B) *ᵖ E₁) y ⊗[K]
    DetBundle K F₂ ((f : B' → B) *ᵖ E₂) y)]
  [∀ y, TopologicalSpace (DetBundle K F₁ ((f : B' → B) *ᵖ E₁) y ⊗[K]
    DetBundle K F₂ ((f : B' → B) *ᵖ E₂) y)] in
/-- The native product-pullback comparison preserves the intrinsic exterior-algebra image
of every determinant vector. Pullback fibres are the original fibres at the image point. -/
theorem coe_prodPullbackEquiv (y : B')
    (v : DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂) (f y)) :
    (linearEquiv K (F₁ × F₂)
      (((f : B' → B) *ᵖ E₁) ×ᵇ ((f : B' → B) *ᵖ E₂)) y
      (prodPullbackEquiv K F₁ E₁ F₂ E₂ f y v) :
      ExteriorAlgebra K (((f : B' → B) *ᵖ E₁) y × ((f : B' → B) *ᵖ E₂) y)) =
      (linearEquiv K (F₁ × F₂) (E₁ ×ᵇ E₂) (f y) v :
        ExteriorAlgebra K (E₁ (f y) × E₂ (f y))) :=
  coe_linearEquiv_pullbackEquiv (𝕜 := K) (F := F₁ × F₂) (E := E₁ ×ᵇ E₂) (f : B' → B) y v

omit [CompleteSpace K] [VectorBundle K F₁ E₁] [VectorBundle K F₂ E₂]
  [∀ x, IsModuleTopology K (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]
  [∀ x, TopologicalSpace (DetBundle K F₁ E₁ x ⊗[K] DetBundle K F₂ E₂ x)]
  [∀ y, IsModuleTopology K (DetBundle K F₁ ((f : B' → B) *ᵖ E₁) y ⊗[K]
    DetBundle K F₂ ((f : B' → B) *ᵖ E₂) y)]
  [∀ y, TopologicalSpace (DetBundle K F₁ ((f : B' → B) *ᵖ E₁) y ⊗[K]
    DetBundle K F₂ ((f : B' → B) *ᵖ E₂) y)] in
/-- Every linear product chart reads the product-pullback comparison in the original
coordinates, on an arbitrary determinant vector. No preferred chart is part of the statement. -/
theorem chartCoord_prodPullbackEquiv
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [e₁.IsLinear K] [e₂.IsLinear K] {y : B'}
    (hx₁ : f y ∈ e₁.baseSet) (hx₂ : f y ∈ e₂.baseSet)
    (v : DetBundle K (F₁ × F₂) (E₁ ×ᵇ E₂) (f y)) :
    chartCoord ((e₁.pullback f).prod (e₂.pullback f))
      (Trivialization.mem_prod_pullback_baseSet f hx₁ hx₂)
      (prodPullbackEquiv K F₁ E₁ F₂ E₂ f y v) =
      chartCoord (e₁.prod e₂) (Trivialization.mem_prod_baseSet hx₁ hx₂) v := by
  have hy₁ : y ∈ (e₁.pullback f).baseSet := by
    simpa only [Trivialization.pullback_baseSet, Set.mem_preimage] using hx₁
  have hy₂ : y ∈ (e₂.pullback f).baseSet := by
    simpa only [Trivialization.pullback_baseSet, Set.mem_preimage] using hx₂
  -- Restate the membership proof so the pulled-back product chart uses the standard fibre
  -- instances rather than the local ones of `Trivialization.mem_prod_pullback_baseSet`.
  change chartCoord ((e₁.pullback f).prod (e₂.pullback f))
      (Trivialization.mem_prod_baseSet hy₁ hy₂) (prodPullbackEquiv K F₁ E₁ F₂ E₂ f y v) = _
  rw [chartCoord_apply, chartCoord_apply, Trivialization.linearEquivAt_prod _ _ hy₁ hy₂,
    Trivialization.linearEquivAt_prod _ _ hx₁ hx₂, Trivialization.linearEquivAt_pullback,
    Trivialization.linearEquivAt_pullback]
  apply congrArg (modelCoord (F₁ × F₂))
  apply Subtype.ext
  rw [LinearEquiv.coe_exteriorPower_apply, LinearEquiv.coe_exteriorPower_apply,
    coe_prodPullbackEquiv]
  -- Both sides apply the product of the fibre equivalences of `e₁` and `e₂` at `f y`; they
  -- differ only in whether its source is written with pulled-back or original fibres.
  rfl

/-- The Whitney square commutes with pullback between the native product and tensor fibres. -/
theorem prodPullbackEquiv_prodEquiv (y : B')
    (t : DetBundle K F₁ E₁ (f y) ⊗[K] DetBundle K F₂ E₂ (f y)) :
    prodPullbackEquiv K F₁ E₁ F₂ E₂ f y (prodEquiv K F₁ E₁ F₂ E₂ (f y) t) =
      prodEquiv K F₁ ((f : B' → B) *ᵖ E₁) F₂ ((f : B' → B) *ᵖ E₂) y
        (prodPullbackTensorEquiv K F₁ E₁ F₂ E₂ f y t) := by
  let e₁ := trivializationAt F₁ E₁ (f y)
  let e₂ := trivializationAt F₂ E₂ (f y)
  have hx₁ : f y ∈ e₁.baseSet := mem_baseSet_trivializationAt F₁ E₁ (f y)
  have hx₂ : f y ∈ e₂.baseSet := mem_baseSet_trivializationAt F₂ E₂ (f y)
  have hy : y ∈ ((e₁.pullback f).prod (e₂.pullback f)).baseSet :=
    Trivialization.mem_prod_pullback_baseSet f hx₁ hx₂
  apply (chartCoord ((e₁.pullback f).prod (e₂.pullback f)) hy).injective
  rw [chartCoord_prodPullbackEquiv f e₁ e₂ hx₁ hx₂]
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [map_add, hs, ht]
  | tmul a b =>
    rw [prodPullbackTensorEquiv_tmul]
    exact (chartCoord_pullback_prodEquiv_tmul f e₁ e₂ hx₁ hx₂ a b).symm

end Pullback

section RankZero

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

section TrivialSummand

open scoped TauCeti.ModuleTopology

variable (V : Type v₁) [NormedAddCommGroup V] [NormedSpace K V] [FiniteDimensional K V]

omit [CompleteSpace K] in
variable (K B F₂ E₂) in
/-- **A trivial summand does not change the determinant line**, fibrewise: `det E ≃ det (V ⊕ E)`
over `x` sends `a` to the Whitney product `ω ⊗ a` of `a` with the vector `ω` of the determinant
line of `B × V` of coordinate `1` (`TauCeti.DetBundle.trivialEquiv`). -/
def trivialProdEquiv (x : B) :
    DetBundle K F₂ E₂ x ≃L[K] DetBundle K (V × F₂) (Trivial B V ×ᵇ E₂) x :=
  LinearEquiv.toContinuousLinearEquivOfIsModuleTopology
    ((TensorProduct.lid K _).symm ≪≫ₗ
      TensorProduct.congr (trivialEquiv K B V x).symm.toLinearEquiv (LinearEquiv.refl K _) ≪≫ₗ
      (prodEquiv K V (Trivial B V) F₂ E₂ x).toLinearEquiv)

variable {V}

omit [CompleteSpace K] in
@[simp]
theorem trivialProdEquiv_apply (x : B) (a : DetBundle K F₂ E₂ x) :
    trivialProdEquiv K B F₂ E₂ V x a =
      prodEquiv K V (Trivial B V) F₂ E₂ x ((trivialEquiv K B V x).symm 1 ⊗ₜ a) := by
  simp only [trivialProdEquiv, LinearEquiv.coe_toContinuousLinearEquivOfIsModuleTopology,
    LinearEquiv.trans_apply, TensorProduct.lid_symm_apply, TensorProduct.congr_tmul,
    ContinuousLinearEquiv.coe_toLinearEquiv, LinearEquiv.refl_apply]

variable (K B F₂ E₂ V) in
/-- **A trivial summand does not change the determinant line**: the fibrewise isomorphisms
`TauCeti.DetBundle.trivialProdEquiv` form a homeomorphism `det E ≃ det ((B × V) ⊕ E)` of total
spaces. -/
def trivialProdHomeomorph :
    TotalSpace K (DetBundle K F₂ E₂) ≃ₜ TotalSpace K (DetBundle K (V × F₂) (Trivial B V ×ᵇ E₂)) :=
  bundleHomeomorph (trivialProdEquiv K B F₂ E₂ V) <| by
    -- The constant section `ω` of `det (B × V)`, tensored with the identity of `det E`, followed
    -- by the Whitney homeomorphism.
    have hω : Continuous fun p : TotalSpace K (DetBundle K F₂ E₂) ↦
        TotalSpace.mk' K p.proj ((trivialEquiv K B V p.proj).symm 1) :=
      ((trivialHomeomorph K B V).symm.continuous.comp
        ((Trivial.homeomorphProd B K).symm.continuous.comp
          ((FiberBundle.continuous_proj K _).prodMk (continuous_const (y := (1 : K)))))).congr
        fun p ↦ by
          rw [Function.comp_apply, Function.comp_apply, trivialHomeomorph_symm_apply]
          -- `Bundle.Trivial.homeomorphProd` is `TotalSpace.toProd`, so its inverse is `⟨b, v⟩`.
          rfl
    refine ((prodHomeomorph K V (Trivial B V) F₂ E₂).continuous.comp
      (hω.tmul_section (b := TotalSpace.proj) (w := fun p ↦ p.snd) continuous_id)).congr
        fun p ↦ ?_
    rw [Function.comp_apply, prodHomeomorph_apply, trivialProdEquiv_apply]

@[simp]
theorem trivialProdHomeomorph_apply (p : TotalSpace K (DetBundle K F₂ E₂)) :
    trivialProdHomeomorph K B F₂ E₂ V p = ⟨p.proj, trivialProdEquiv K B F₂ E₂ V p.proj p.snd⟩ :=
  bundleHomeomorph_apply _ _ p

@[simp]
theorem trivialProdHomeomorph_symm_apply
    (p : TotalSpace K (DetBundle K (V × F₂) (Trivial B V ×ᵇ E₂))) :
    (trivialProdHomeomorph K B F₂ E₂ V).symm p =
      ⟨p.proj, (trivialProdEquiv K B F₂ E₂ V p.proj).symm p.snd⟩ :=
  bundleHomeomorph_symm_apply _ _ p

end TrivialSummand

end TauCeti.DetBundle
