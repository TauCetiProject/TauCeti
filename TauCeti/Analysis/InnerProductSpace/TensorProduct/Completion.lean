/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Completion
public import TauCeti.Analysis.InnerProductSpace.TensorProduct.Map
public import TauCeti.Analysis.InnerProductSpace.UltraweakTopology
public import TauCeti.Analysis.Normed.Operator.Completion

/-!
# Completed Hilbert tensor products of inner product spaces and bounded operators

For inner product spaces `E` and `F` over `𝕜` (`ℝ` or `ℂ`), Mathlib equips
`UniformSpace.Completion (E ⊗[𝕜] F)` with the completed Hilbert space structure extending
`⟪x₁ ⊗ₜ y₁, x₂ ⊗ₜ y₂⟫ = ⟪x₁, x₂⟫ * ⟪y₁, y₂⟫`. This file develops:

* `ContinuousLinearMap.rTensorCompletion` / `lTensorCompletion`: completed amplifications `f ⊗ 1`
  and `1 ⊗ g` (with no completeness on passive factors), exact norms, adjoints, and
  `ContinuousLinearMap.rTensorCompletionStarAlgHom` / `lTensorCompletionStarAlgHom`.
* `TensorProduct.lidCompletionEquiv`, `ridCompletionEquiv`, `completionRTensorEquiv`,
  `completionLTensorEquiv`, and `assocCompletion`: structural linear isometric equivalences.
* `HilbertBasis.tensorCompletionEquiv` and `TensorProduct.lpTensorCompletionEquiv`: isometric
  identification `Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] ℓ²(ι, E)`, giving ultraweak continuity
  `continuous_rTensorCompletion` and `continuous_lTensorCompletion`.
* `TensorProduct.sliceRight` and `sliceLeft`: bounded, ultraweakly continuous, `⋆`-compatible
  bimodule slice maps separating all operators on completed tensor products.

## References

* J. Dixmier, *Von Neumann Algebras*, North-Holland, 1981, Part I, Chapter 2, §§3–4.
* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras*, Vols. I–II,
  Academic Press, 1983/1986, §2.6 and §11.1–11.2.
* M. Takesaki, *Theory of Operator Algebras I*, Springer, 1979, Chapter IV, §1 and §5.
-/

public section

open Filter UniformSpace
open scoped Topology TensorProduct InnerProduct InnerProductSpace lp

namespace TensorProduct

variable {𝕜 E F G H : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-! ### Pure tensors, density, and extensionality in `Completion (E ⊗[𝕜] F)` -/

/-- Two continuous linear maps from `Completion (E ⊗[𝕜] F)` into a Hausdorff space agree if they
agree on completed pure tensors `(x ⊗ₜ[𝕜] y : E ⊗[𝕜] F)`. -/
theorem continuousLinearMap_ext_completion {M : Type*} [AddCommGroup M] [Module 𝕜 M]
    [TopologicalSpace M] [T2Space M] {l l' : Completion (E ⊗[𝕜] F) →L[𝕜] M}
    (h : ∀ (x : E) (y : F), l (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = l' (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F)) : l = l' := by
  have h' : (l ∘L Completion.toComplL).toLinearMap = (l' ∘L Completion.toComplL).toLinearMap :=
    TensorProduct.ext' fun x y ↦ by simpa using h x y
  exact DFunLike.coe_injective <| Completion.ext l.continuous l'.continuous fun u ↦
    by simpa using congr($h' u)

theorem continuousLinearMap_ext_completion_iff {M : Type*} [AddCommGroup M] [Module 𝕜 M]
    [TopologicalSpace M] [T2Space M] {l l' : Completion (E ⊗[𝕜] F) →L[𝕜] M} :
    l = l' ↔ ∀ (x : E) (y : F), l (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = l' (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) :=
  ⟨fun h _ _ ↦ h ▸ rfl, continuousLinearMap_ext_completion⟩

/-- Vectors in `Completion (E ⊗[𝕜] F)` are determined by right inner products with pure tensors. -/
theorem ext_completion_inner_tmul_right {u v : Completion (E ⊗[𝕜] F)} :
    u = v ↔ ∀ (x : E) (y : F),
      ⟪u, (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F)⟫_𝕜 = ⟪v, (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F)⟫_𝕜 := by
  rw [← innerSL_inj (𝕜 := 𝕜), continuousLinearMap_ext_completion_iff]; simp

/-- Vectors in `Completion (E ⊗[𝕜] F)` are determined by left inner products with pure tensors. -/
theorem ext_completion_inner_tmul_left {u v : Completion (E ⊗[𝕜] F)} :
    u = v ↔ ∀ (x : E) (y : F), ⟪((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)), u⟫_𝕜 =
      ⟪((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)), v⟫_𝕜 := by
  simp_rw [ext_completion_inner_tmul_right (𝕜 := 𝕜), ← inner_conj_symm u, ← inner_conj_symm v,
    (starRingEnd 𝕜).injective.eq_iff]

/-- The linear span of completed pure tensors is dense in `Completion (E ⊗[𝕜] F)`. -/
theorem topologicalClosure_span_tmul_coe :
    (Submodule.span 𝕜 {u : Completion (E ⊗[𝕜] F) |
      ∃ (x : E) (y : F), (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = u}).topologicalClosure = ⊤ := by
  let S : Submodule 𝕜 (Completion (E ⊗[𝕜] F)) :=
    .span 𝕜 {u | ∃ (x : E) (y : F), (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = u}
  refine eq_top_iff.2 fun u _ ↦ Completion.induction_on u S.isClosed_topologicalClosure fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact S.le_topologicalClosure (Submodule.subset_span ⟨x, y, rfl⟩)
  | add _ _ hz₁ hz₂ => rw [Completion.coe_add]; exact add_mem hz₁ hz₂

instance instSubsingletonCompletionLeft [Subsingleton E] : Subsingleton (Completion (E ⊗[𝕜] F)) :=
  ⟨fun u v ↦ Completion.induction_on₂ u v (isClosed_eq continuous_fst continuous_snd)
    fun a b ↦ congrArg _ (Subsingleton.elim a b)⟩
instance instSubsingletonCompletionRight [Subsingleton F] : Subsingleton (Completion (E ⊗[𝕜] F)) :=
  ⟨fun u v ↦ Completion.induction_on₂ u v (isClosed_eq continuous_fst continuous_snd)
    fun a b ↦ congrArg _ (Subsingleton.elim a b)⟩

instance instNontrivialCompletion [Nontrivial E] [Nontrivial F] :
    Nontrivial (Completion (E ⊗[𝕜] F)) := by
  obtain ⟨x, hx⟩ := exists_ne (0 : E); obtain ⟨y, hy⟩ := exists_ne (0 : F)
  refine ⟨(x ⊗ₜ[𝕜] y : E ⊗[𝕜] F), 0, fun h ↦ ?_⟩
  have h0 : ‖((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F))‖ = 0 := by simp [h]
  rw [Completion.norm_coe, norm_tmul, mul_eq_zero, norm_eq_zero, norm_eq_zero] at h0
  exact h0.elim hx hy

/-- `Completion (E ⊗[𝕜] F)` is nontrivial if and only if both `E` and `F` are nontrivial. -/
theorem nontrivial_completion_iff :
    Nontrivial (Completion (E ⊗[𝕜] F)) ↔ Nontrivial E ∧ Nontrivial F := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨_, _⟩ ↦ inferInstance⟩ <;> (contrapose! h; exact inferInstance)

variable (𝕜 E F) in
/-- The canonical bounded bilinear map `(x, y) ↦ ↑(x ⊗ₜ[𝕜] y)` into `Completion (E ⊗[𝕜] F)`. -/
noncomputable def tmulCLM : E →L[𝕜] F →L[𝕜] Completion (E ⊗[𝕜] F) :=
  (ContinuousLinearMap.compL 𝕜 F (E ⊗[𝕜] F) (Completion (E ⊗[𝕜] F)) Completion.toComplL).comp
    (mkL 𝕜 E F)

@[simp] theorem tmulCLM_apply (x : E) (y : F) :
    tmulCLM 𝕜 E F x y = (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) := by simp [tmulCLM]
theorem norm_tmulCLM_apply_le (x : E) : ‖tmulCLM 𝕜 E F x‖ ≤ ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun _ ↦ by simp
theorem norm_flip_tmulCLM_apply_le (y : F) : ‖(tmulCLM 𝕜 E F).flip y‖ ≤ ‖y‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y) fun _ ↦ by simp [mul_comm]
@[simp] theorem adjoint_flip_tmulCLM_tmul [CompleteSpace E] (ξ y : F) (x : E) :
    ((tmulCLM 𝕜 E F).flip ξ).adjoint (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = ⟪ξ, y⟫_𝕜 • x :=
  ext_inner_left 𝕜 fun _ ↦ by simp [ContinuousLinearMap.adjoint_inner_right, inner_smul_right,
    mul_comm]
@[simp] theorem adjoint_tmulCLM_tmul [CompleteSpace F] (e x : E) (y : F) :
    (tmulCLM 𝕜 E F e).adjoint (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = ⟪e, x⟫_𝕜 • y :=
  ext_inner_left 𝕜 fun _ ↦ by simp [ContinuousLinearMap.adjoint_inner_right, inner_smul_right]

/-! ### Completed operator tensor products `(mapL f g).completion` -/

theorem mapL_completion_tmul (f : E →L[𝕜] F) (g : G →L[𝕜] H) (x : E) (y : G) :
    (mapL f g).completion (x ⊗ₜ[𝕜] y : E ⊗[𝕜] G) = (f x ⊗ₜ[𝕜] g y : F ⊗[𝕜] H) :=
  ContinuousLinearMap.completion_apply_coe _ (x ⊗ₜ[𝕜] y)
theorem norm_mapL_completion (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    ‖(mapL f g).completion‖ = ‖f‖ * ‖g‖ := by rw [ContinuousLinearMap.norm_completion, norm_mapL]
theorem mapL_completion_id :
    (mapL (.id 𝕜 E) (.id 𝕜 F)).completion = .id 𝕜 (Completion (E ⊗[𝕜] F)) :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp
theorem mapL_completion_comp {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]
    [NormedAddCommGroup B] [InnerProductSpace 𝕜 B]
    (f₁ : E →L[𝕜] F) (f₂ : A →L[𝕜] E) (g₁ : G →L[𝕜] H) (g₂ : B →L[𝕜] G) :
    (mapL (f₁ ∘L f₂) (g₁ ∘L g₂)).completion =
      (mapL f₁ g₁).completion ∘L (mapL f₂ g₂).completion :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp
theorem mapL_completion_mul (f₁ f₂ : E →L[𝕜] E) (g₁ g₂ : F →L[𝕜] F) :
    (mapL (f₁ * f₂) (g₁ * g₂)).completion = (mapL f₁ g₁).completion * (mapL f₂ g₂).completion :=
  mapL_completion_comp f₁ f₂ g₁ g₂

/-- Pure-tensor criterion for the Hilbert-space adjoint on completed tensor products. -/
theorem eq_adjoint_completion_iff {E₁ F₁ E₂ F₂ : Type*}
    [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup F₁]
    [InnerProductSpace 𝕜 F₁] [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
    [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]
    (A : Completion (E₂ ⊗[𝕜] F₂) →L[𝕜] Completion (E₁ ⊗[𝕜] F₁))
    (B : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) :
    A = B.adjoint ↔ ∀ (x₁ : E₁) (y₁ : F₁) (x₂ : E₂) (y₂ : F₂),
      ⟪A (x₂ ⊗ₜ[𝕜] y₂ : E₂ ⊗[𝕜] F₂), (x₁ ⊗ₜ[𝕜] y₁ : E₁ ⊗[𝕜] F₁)⟫_𝕜 =
        ⟪((x₂ ⊗ₜ[𝕜] y₂ : E₂ ⊗[𝕜] F₂) : Completion (E₂ ⊗[𝕜] F₂)),
          B (x₁ ⊗ₜ[𝕜] y₁ : E₁ ⊗[𝕜] F₁)⟫_𝕜 := by
  simp_rw [continuousLinearMap_ext_completion_iff, ext_completion_inner_tmul_right (𝕜 := 𝕜),
    ContinuousLinearMap.adjoint_inner_left]
  exact ⟨fun h x₁ y₁ x₂ y₂ ↦ h x₂ y₂ x₁ y₁, fun h x₂ y₂ x₁ y₁ ↦ h x₁ y₁ x₂ y₂⟩

@[simp] theorem adjoint_mapL_completion [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]
    [CompleteSpace H] (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    ((mapL f g).completion).adjoint = (mapL f.adjoint g.adjoint).completion := by
  rw [eq_comm, eq_adjoint_completion_iff]; simp [ContinuousLinearMap.adjoint_inner_left]
@[simp] theorem star_mapL_completion [CompleteSpace E] [CompleteSpace F]
    (f : E →L[𝕜] E) (g : F →L[𝕜] F) :
    star (mapL f g).completion = (mapL (star f) (star g)).completion := by
  simp only [ContinuousLinearMap.star_eq_adjoint, adjoint_mapL_completion]

end TensorProduct

/-! ### Completed operator amplifications `rTensorCompletion` and `lTensorCompletion` -/

namespace ContinuousLinearMap

open TensorProduct

/-- The amplification `f ⊗ 1` on `Completion (E ⊗[𝕜] G)`: the continuous extension of
`ContinuousLinearMap.rTensor`, sending `(x ⊗ₜ y : E ⊗[𝕜] G)` to `(f x ⊗ₜ y : F ⊗[𝕜] G)`. No
completeness of `E`, `F`, or `G` is assumed. -/
noncomputable def rTensorCompletion {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (G : Type*) [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] (f : E →L[𝕜] F) :
    Completion (E ⊗[𝕜] G) →L[𝕜] Completion (F ⊗[𝕜] G) :=
  (f.rTensor G).completion

/-- The amplification `1 ⊗ g` on `Completion (E ⊗[𝕜] F)`: the continuous extension of
`ContinuousLinearMap.lTensor`, sending `(x ⊗ₜ y : E ⊗[𝕜] F)` to `(x ⊗ₜ g y : E ⊗[𝕜] G)`. No
completeness of `E`, `F`, or `G` is assumed. -/
noncomputable def lTensorCompletion (E : Type*) {𝕜 F G : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] (g : F →L[𝕜] G) :
    Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] G) :=
  (g.lTensor E).completion

variable {𝕜 E F G H : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem rTensorCompletion_def (f : E →L[𝕜] F) : f.rTensorCompletion G = (f.rTensor G).completion :=
  (rfl)
theorem lTensorCompletion_def (g : F →L[𝕜] G) : g.lTensorCompletion E = (g.lTensor E).completion :=
  (rfl)

@[simp] theorem rTensorCompletion_coe (f : E →L[𝕜] F) (z : E ⊗[𝕜] G) :
    f.rTensorCompletion G z = (f.rTensor G z : F ⊗[𝕜] G) := completion_apply_coe _ z
@[simp] theorem lTensorCompletion_coe (g : F →L[𝕜] G) (z : E ⊗[𝕜] F) :
    g.lTensorCompletion E z = (g.lTensor E z : E ⊗[𝕜] G) := completion_apply_coe _ z
theorem rTensorCompletion_tmul (f : E →L[𝕜] F) (x : E) (y : G) :
    f.rTensorCompletion G (x ⊗ₜ[𝕜] y : E ⊗[𝕜] G) = (f x ⊗ₜ[𝕜] y : F ⊗[𝕜] G) :=
  completion_apply_coe _ (x ⊗ₜ[𝕜] y)
theorem lTensorCompletion_tmul (g : F →L[𝕜] G) (x : E) (y : F) :
    g.lTensorCompletion E (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = (x ⊗ₜ[𝕜] g y : E ⊗[𝕜] G) :=
  completion_apply_coe _ (x ⊗ₜ[𝕜] y)

/-- `f.rTensorCompletion G` is uniquely characterized by its action on pure tensors. -/
theorem eq_rTensorCompletion_iff (T : Completion (E ⊗[𝕜] G) →L[𝕜] Completion (F ⊗[𝕜] G))
    (f : E →L[𝕜] F) : T = f.rTensorCompletion G ↔
      ∀ (x : E) (y : G), T (x ⊗ₜ[𝕜] y : E ⊗[𝕜] G) = (f x ⊗ₜ[𝕜] y : F ⊗[𝕜] G) := by
  rw [continuousLinearMap_ext_completion_iff]; simp
/-- `g.lTensorCompletion E` is uniquely characterized by its action on pure tensors. -/
theorem eq_lTensorCompletion_iff (T : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] G))
    (g : F →L[𝕜] G) : T = g.lTensorCompletion E ↔
      ∀ (x : E) (y : F), T (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = (x ⊗ₜ[𝕜] g y : E ⊗[𝕜] G) := by
  rw [continuousLinearMap_ext_completion_iff]; simp

theorem rTensorCompletion_eq_mapL_completion (f : E →L[𝕜] F) :
    f.rTensorCompletion G = (mapL f (.id 𝕜 G)).completion := by
  rw [rTensorCompletion_def, rTensor_eq_mapL]
theorem lTensorCompletion_eq_mapL_completion (g : F →L[𝕜] G) :
    g.lTensorCompletion E = (mapL (.id 𝕜 E) g).completion := by
  rw [lTensorCompletion_def, lTensor_eq_mapL]

@[simp] theorem rTensorCompletion_add (f₁ f₂ : E →L[𝕜] F) :
    (f₁ + f₂).rTensorCompletion G = f₁.rTensorCompletion G + f₂.rTensorCompletion G :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp [Completion.coe_add]
@[simp] theorem lTensorCompletion_add (g₁ g₂ : F →L[𝕜] G) :
    (g₁ + g₂).lTensorCompletion E = g₁.lTensorCompletion E + g₂.lTensorCompletion E :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp [Completion.coe_add]
@[simp] theorem rTensorCompletion_smul (c : 𝕜) (f : E →L[𝕜] F) :
    (c • f).rTensorCompletion G = c • f.rTensorCompletion G :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp [Completion.coe_smul]
@[simp] theorem lTensorCompletion_smul (c : 𝕜) (g : F →L[𝕜] G) :
    (c • g).lTensorCompletion E = c • g.lTensorCompletion E :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp [Completion.coe_smul]
@[simp] theorem rTensorCompletion_zero : (0 : E →L[𝕜] F).rTensorCompletion G = 0 :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp
@[simp] theorem lTensorCompletion_zero : (0 : F →L[𝕜] G).lTensorCompletion E = 0 :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp
@[simp] theorem rTensorCompletion_neg (f : E →L[𝕜] F) :
    (-f).rTensorCompletion G = -f.rTensorCompletion G :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp [Completion.coe_neg]
@[simp] theorem lTensorCompletion_neg (g : F →L[𝕜] G) :
    (-g).lTensorCompletion E = -g.lTensorCompletion E :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp [Completion.coe_neg]
@[simp] theorem rTensorCompletion_sub (f₁ f₂ : E →L[𝕜] F) :
    (f₁ - f₂).rTensorCompletion G = f₁.rTensorCompletion G - f₂.rTensorCompletion G :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp [Completion.coe_sub]
@[simp] theorem lTensorCompletion_sub (g₁ g₂ : F →L[𝕜] G) :
    (g₁ - g₂).lTensorCompletion E = g₁.lTensorCompletion E - g₂.lTensorCompletion E :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp [Completion.coe_sub]
@[simp] theorem rTensorCompletion_id :
    (.id 𝕜 E : E →L[𝕜] E).rTensorCompletion G = .id 𝕜 (Completion (E ⊗[𝕜] G)) :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp
@[simp] theorem lTensorCompletion_id :
    (.id 𝕜 F : F →L[𝕜] F).lTensorCompletion E = .id 𝕜 (Completion (E ⊗[𝕜] F)) :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp
@[simp] theorem rTensorCompletion_one : (1 : E →L[𝕜] E).rTensorCompletion G = 1 :=
  rTensorCompletion_id
@[simp] theorem lTensorCompletion_one : (1 : F →L[𝕜] F).lTensorCompletion E = 1 :=
  lTensorCompletion_id
theorem rTensorCompletion_comp (f₁ : F →L[𝕜] G) (f₂ : E →L[𝕜] F) :
    (f₁ ∘L f₂).rTensorCompletion H = f₁.rTensorCompletion H ∘L f₂.rTensorCompletion H :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp
theorem lTensorCompletion_comp (g₁ : G →L[𝕜] H) (g₂ : F →L[𝕜] G) :
    (g₁ ∘L g₂).lTensorCompletion E = g₁.lTensorCompletion E ∘L g₂.lTensorCompletion E :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp
theorem rTensorCompletion_mul (f₁ f₂ : E →L[𝕜] E) :
    (f₁ * f₂).rTensorCompletion G = f₁.rTensorCompletion G * f₂.rTensorCompletion G :=
  rTensorCompletion_comp f₁ f₂
theorem lTensorCompletion_mul (g₁ g₂ : F →L[𝕜] F) :
    (g₁ * g₂).lTensorCompletion E = g₁.lTensorCompletion E * g₂.lTensorCompletion E :=
  lTensorCompletion_comp g₁ g₂
@[simp] theorem rTensorCompletion_pow (f : E →L[𝕜] E) (n : ℕ) :
    (f ^ n).rTensorCompletion G = f.rTensorCompletion G ^ n := by
  induction n <;> simp [pow_succ, rTensorCompletion_mul, *]
@[simp] theorem lTensorCompletion_pow (g : F →L[𝕜] F) (n : ℕ) :
    (g ^ n).lTensorCompletion E = g.lTensorCompletion E ^ n := by
  induction n <;> simp [pow_succ, lTensorCompletion_mul, *]
@[simp] theorem rTensorCompletion_comp_lTensorCompletion (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    f.rTensorCompletion H ∘L g.lTensorCompletion E = (mapL f g).completion :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp
@[simp] theorem lTensorCompletion_comp_rTensorCompletion (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    g.lTensorCompletion F ∘L f.rTensorCompletion G = (mapL f g).completion :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp

/-- Operators amplified on opposite tensor factors commute. -/
theorem rTensorCompletion_mul_lTensorCompletion_comm (f : E →L[𝕜] E) (g : F →L[𝕜] F) :
    f.rTensorCompletion F * g.lTensorCompletion E =
      g.lTensorCompletion E * f.rTensorCompletion F := by
  rw [mul_def, mul_def, rTensorCompletion_comp_lTensorCompletion,
    lTensorCompletion_comp_rTensorCompletion]

theorem norm_rTensorCompletion_le (f : E →L[𝕜] F) : ‖f.rTensorCompletion G‖ ≤ ‖f‖ := by
  rw [rTensorCompletion_def, norm_completion]; exact norm_rTensor_le G f
theorem norm_lTensorCompletion_le (g : F →L[𝕜] G) : ‖g.lTensorCompletion E‖ ≤ ‖g‖ := by
  rw [lTensorCompletion_def, norm_completion]; exact norm_lTensor_le E g
@[simp] theorem norm_rTensorCompletion [Nontrivial G] (f : E →L[𝕜] F) :
    ‖f.rTensorCompletion G‖ = ‖f‖ := by rw [rTensorCompletion_def, norm_completion, norm_rTensor]
@[simp] theorem norm_lTensorCompletion [Nontrivial E] (g : F →L[𝕜] G) :
    ‖g.lTensorCompletion E‖ = ‖g‖ := by rw [lTensorCompletion_def, norm_completion, norm_lTensor]

variable (𝕜 E F G) in
/-- `f ↦ f.rTensorCompletion G` bundled as a linear isometry when `G` is nontrivial. -/
noncomputable def rTensorCompletionₗᵢ [Nontrivial G] :
    (E →L[𝕜] F) →ₗᵢ[𝕜] (Completion (E ⊗[𝕜] G) →L[𝕜] Completion (F ⊗[𝕜] G)) where
  toLinearMap :=
    { toFun := rTensorCompletion G, map_add' := rTensorCompletion_add,
      map_smul' := rTensorCompletion_smul }
  norm_map' := norm_rTensorCompletion
@[simp] theorem rTensorCompletionₗᵢ_apply [Nontrivial G] (f : E →L[𝕜] F) :
    rTensorCompletionₗᵢ 𝕜 E F G f = f.rTensorCompletion G := (rfl)

variable (𝕜 E F G) in
/-- `g ↦ g.lTensorCompletion E` bundled as a linear isometry when `E` is nontrivial. -/
noncomputable def lTensorCompletionₗᵢ [Nontrivial E] :
    (F →L[𝕜] G) →ₗᵢ[𝕜] (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] G)) where
  toLinearMap :=
    { toFun := lTensorCompletion E, map_add' := lTensorCompletion_add,
      map_smul' := lTensorCompletion_smul }
  norm_map' := norm_lTensorCompletion
@[simp] theorem lTensorCompletionₗᵢ_apply [Nontrivial E] (g : F →L[𝕜] G) :
    lTensorCompletionₗᵢ 𝕜 E F G g = g.lTensorCompletion E := (rfl)

theorem rTensorCompletion_injective (G : Type*) [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [Nontrivial G] : Function.Injective (rTensorCompletion G : (E →L[𝕜] F) → _) :=
  (rTensorCompletionₗᵢ 𝕜 E F G).injective
theorem lTensorCompletion_injective (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [Nontrivial E] : Function.Injective (lTensorCompletion E : (F →L[𝕜] G) → _) :=
  (lTensorCompletionₗᵢ 𝕜 E F G).injective
@[simp] theorem rTensorCompletion_eq_zero [Subsingleton G] (f : E →L[𝕜] F) :
    f.rTensorCompletion G = 0 := Subsingleton.elim _ _
@[simp] theorem lTensorCompletion_eq_zero [Subsingleton E] (g : F →L[𝕜] G) :
    g.lTensorCompletion E = 0 := Subsingleton.elim _ _

/-- Adjoint of `f.rTensorCompletion G`, needing completeness only on `E` and `F`. -/
@[simp] theorem adjoint_rTensorCompletion [CompleteSpace E] [CompleteSpace F] (f : E →L[𝕜] F) :
    (f.rTensorCompletion G).adjoint = f.adjoint.rTensorCompletion G := by
  rw [eq_comm, eq_adjoint_completion_iff]; simp [adjoint_inner_left]
/-- Adjoint of `g.lTensorCompletion E`, needing completeness only on `F` and `G`. -/
@[simp] theorem adjoint_lTensorCompletion [CompleteSpace F] [CompleteSpace G] (g : F →L[𝕜] G) :
    (g.lTensorCompletion E).adjoint = g.adjoint.lTensorCompletion E := by
  rw [eq_comm, eq_adjoint_completion_iff]; simp [adjoint_inner_left]
@[simp] theorem star_rTensorCompletion [CompleteSpace E] (f : E →L[𝕜] E) :
    star (f.rTensorCompletion G) = (star f).rTensorCompletion G := by
  simp only [star_eq_adjoint, adjoint_rTensorCompletion]
@[simp] theorem star_lTensorCompletion [CompleteSpace F] (g : F →L[𝕜] F) :
    star (g.lTensorCompletion E) = (star g).lTensorCompletion E := by
  simp only [star_eq_adjoint, adjoint_lTensorCompletion]

variable (𝕜 E F) in
/-- Left tensor amplification `x ↦ x ⊗ 1` bundled as a unital `⋆`-algebra homomorphism. -/
noncomputable def rTensorCompletionStarAlgHom [CompleteSpace E] :
    (E →L[𝕜] E) →⋆ₐ[𝕜] (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F)) :=
  { toFun := rTensorCompletion F, map_one' := rTensorCompletion_one,
    map_mul' := rTensorCompletion_mul, map_zero' := rTensorCompletion_zero,
    map_add' := rTensorCompletion_add, map_star' := fun f ↦ (star_rTensorCompletion f).symm,
    commutes' := fun _ ↦ by simp [Algebra.algebraMap_eq_smul_one] }
@[simp] theorem rTensorCompletionStarAlgHom_apply [CompleteSpace E] (f : E →L[𝕜] E) :
    rTensorCompletionStarAlgHom 𝕜 E F f = f.rTensorCompletion F := (rfl)

variable (𝕜 E F) in
/-- Right tensor amplification `y ↦ 1 ⊗ y` bundled as a unital `⋆`-algebra homomorphism. -/
noncomputable def lTensorCompletionStarAlgHom [CompleteSpace F] :
    (F →L[𝕜] F) →⋆ₐ[𝕜] (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F)) :=
  { toFun := lTensorCompletion E, map_one' := lTensorCompletion_one,
    map_mul' := lTensorCompletion_mul, map_zero' := lTensorCompletion_zero,
    map_add' := lTensorCompletion_add, map_star' := fun g ↦ (star_lTensorCompletion g).symm,
    commutes' := fun _ ↦ by simp [Algebra.algebraMap_eq_smul_one] }
@[simp] theorem lTensorCompletionStarAlgHom_apply [CompleteSpace F] (g : F →L[𝕜] F) :
    lTensorCompletionStarAlgHom 𝕜 E F g = g.lTensorCompletion E := (rfl)

/-- Right pure-tensor creation composed with another's adjoint is `1 ⊗ |η⟩⟨ξ|`. -/
theorem flip_tmulCLM_comp_adjoint [CompleteSpace E] (ξ η : F) :
    (tmulCLM 𝕜 E F).flip η ∘L ((tmulCLM 𝕜 E F).flip ξ).adjoint =
      (InnerProductSpace.rankOne 𝕜 η ξ).lTensorCompletion E :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp
/-- Left pure-tensor creation composed with another's adjoint is `|e₂⟩⟨e₁| ⊗ 1`. -/
theorem tmulCLM_comp_adjoint [CompleteSpace F] (e₁ e₂ : E) :
    tmulCLM 𝕜 E F e₂ ∘L (tmulCLM 𝕜 E F e₁).adjoint =
      (InnerProductSpace.rankOne 𝕜 e₂ e₁).rTensorCompletion F :=
  continuousLinearMap_ext_completion fun _ _ ↦ by
    simp only [comp_apply, adjoint_tmulCLM_tmul, map_smul, tmulCLM_apply, rTensorCompletion_coe,
      rTensor_tmul, InnerProductSpace.rankOne_apply, ← smul_tmul', Completion.coe_smul]

end ContinuousLinearMap

/-! ### Structural linear isometric equivalences -/

namespace TensorProduct

variable {𝕜 E F G H : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

theorem commIsometry_completion_tmul (x : E) (y : F) :
    (commIsometry 𝕜 E F).completion (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = (y ⊗ₜ[𝕜] x : F ⊗[𝕜] E) :=
  LinearIsometryEquiv.completion_apply_coe _ (x ⊗ₜ[𝕜] y)
theorem commIsometry_completion_comp_rTensorCompletion (f : E →L[𝕜] F) :
    ((commIsometry 𝕜 F G).completion : _ →L[𝕜] _) ∘L f.rTensorCompletion G =
      f.lTensorCompletion G ∘L ((commIsometry 𝕜 E G).completion : _ →L[𝕜] _) :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp
theorem commIsometry_completion_comp_lTensorCompletion (g : F →L[𝕜] G) :
    ((commIsometry 𝕜 E G).completion : _ →L[𝕜] _) ∘L g.lTensorCompletion E =
      g.rTensorCompletion E ∘L ((commIsometry 𝕜 E F).completion : _ →L[𝕜] _) :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp
theorem conjStarAlgEquiv_commIsometry_completion_rTensorCompletion (f : E →L[𝕜] E) :
    (commIsometry 𝕜 E F).completion.conjStarAlgEquiv (f.rTensorCompletion F) =
      f.lTensorCompletion F :=
  continuousLinearMap_ext_completion fun _ _ ↦ by
    simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]
theorem conjStarAlgEquiv_commIsometry_completion_lTensorCompletion (g : F →L[𝕜] F) :
    (commIsometry 𝕜 E F).completion.conjStarAlgEquiv (g.lTensorCompletion E) =
      g.rTensorCompletion E :=
  continuousLinearMap_ext_completion fun _ _ ↦ by
    simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

variable (𝕜 E) in
/-- Left scalar unit identification `Completion (𝕜 ⊗[𝕜] E) ≃ₗᵢ[𝕜] E` for complete `E`. -/
noncomputable def lidCompletionEquiv [CompleteSpace E] : Completion (𝕜 ⊗[𝕜] E) ≃ₗᵢ[𝕜] E :=
  (lidIsometry 𝕜 E).toLinearEquiv.extendOfIsometry Completion.toComplₗᵢ.toLinearMap LinearMap.id
    Completion.denseRange_coe Function.surjective_id.denseRange fun _ ↦ by simp
@[simp] theorem lidCompletionEquiv_tmul [CompleteSpace E] (c : 𝕜) (x : E) :
    lidCompletionEquiv 𝕜 E (c ⊗ₜ[𝕜] x : 𝕜 ⊗[𝕜] E) = c • x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ (c ⊗ₜ[𝕜] x)
@[simp] theorem lidCompletionEquiv_symm_apply [CompleteSpace E] (x : E) :
    (lidCompletionEquiv 𝕜 E).symm x = ((1 : 𝕜) ⊗ₜ[𝕜] x : 𝕜 ⊗[𝕜] E) :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ x
theorem lidCompletionEquiv_comp_lTensorCompletion [CompleteSpace E] [CompleteSpace F]
    (f : E →L[𝕜] F) : (lidCompletionEquiv 𝕜 F : _ →L[𝕜] F) ∘L f.lTensorCompletion 𝕜 =
      f ∘L (lidCompletionEquiv 𝕜 E : _ →L[𝕜] E) :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp
theorem conjStarAlgEquiv_lidCompletionEquiv_lTensorCompletion [CompleteSpace E] (f : E →L[𝕜] E) :
    (lidCompletionEquiv 𝕜 E).conjStarAlgEquiv (f.lTensorCompletion 𝕜) = f := by
  ext; simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

variable (𝕜 E) in
/-- Right scalar unit identification `Completion (E ⊗[𝕜] 𝕜) ≃ₗᵢ[𝕜] E` for complete `E`. -/
noncomputable def ridCompletionEquiv [CompleteSpace E] : Completion (E ⊗[𝕜] 𝕜) ≃ₗᵢ[𝕜] E :=
  (ridIsometry 𝕜 E).toLinearEquiv.extendOfIsometry Completion.toComplₗᵢ.toLinearMap LinearMap.id
    Completion.denseRange_coe Function.surjective_id.denseRange fun _ ↦ by simp
@[simp] theorem ridCompletionEquiv_tmul [CompleteSpace E] (x : E) (c : 𝕜) :
    ridCompletionEquiv 𝕜 E (x ⊗ₜ[𝕜] c : E ⊗[𝕜] 𝕜) = c • x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ (x ⊗ₜ[𝕜] c)
@[simp] theorem ridCompletionEquiv_symm_apply [CompleteSpace E] (x : E) :
    (ridCompletionEquiv 𝕜 E).symm x = (x ⊗ₜ[𝕜] (1 : 𝕜) : E ⊗[𝕜] 𝕜) :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ x
theorem ridCompletionEquiv_comp_rTensorCompletion [CompleteSpace E] [CompleteSpace F]
    (f : E →L[𝕜] F) : (ridCompletionEquiv 𝕜 F : _ →L[𝕜] F) ∘L f.rTensorCompletion 𝕜 =
      f ∘L (ridCompletionEquiv 𝕜 E : _ →L[𝕜] E) :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp
theorem conjStarAlgEquiv_ridCompletionEquiv_rTensorCompletion [CompleteSpace E] (f : E →L[𝕜] E) :
    (ridCompletionEquiv 𝕜 E).conjStarAlgEquiv (f.rTensorCompletion 𝕜) = f := by
  ext; simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

/-! ### Partial completions and the completed associator -/

theorem denseRange_toComplₗᵢ_rTensor :
    DenseRange ((Completion.toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).rTensor F) := by
  let f := (Completion.toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).rTensor F
  let R : Submodule 𝕜 (Completion E ⊗[𝕜] F) := LinearMap.range f.toLinearMap
  have hmem (z : Completion E ⊗[𝕜] F) : z ∈ R.topologicalClosure := by
    induction z using TensorProduct.inductionOn with
    | add _ _ hz₁ hz₂ => exact add_mem hz₁ hz₂
    | tmul u y =>
      induction u using Completion.induction_on with
      | hp => exact R.isClosed_topologicalClosure.preimage ((mkL 𝕜 (Completion E) F).flip y).2
      | ih x => exact Submodule.le_topologicalClosure R ⟨x ⊗ₜ[𝕜] y, rfl⟩
  intro z; have hz : z ∈ (R.topologicalClosure : Set (Completion E ⊗[𝕜] F)) := hmem z
  rwa [Submodule.topologicalClosure_coe, LinearMap.coe_range, LinearIsometry.coe_toLinearMap] at hz
theorem denseRange_toComplₗᵢ_lTensor :
    DenseRange ((Completion.toComplₗᵢ : F →ₗᵢ[𝕜] Completion F).lTensor E) := by
  let f := (Completion.toComplₗᵢ : F →ₗᵢ[𝕜] Completion F).lTensor E
  let R : Submodule 𝕜 (E ⊗[𝕜] Completion F) := LinearMap.range f.toLinearMap
  have hmem (z : E ⊗[𝕜] Completion F) : z ∈ R.topologicalClosure := by
    induction z using TensorProduct.inductionOn with
    | add _ _ hz₁ hz₂ => exact add_mem hz₁ hz₂
    | tmul x v =>
      induction v using Completion.induction_on with
      | hp => exact R.isClosed_topologicalClosure.preimage (mkL 𝕜 E (Completion F) x).2
      | ih y => exact Submodule.le_topologicalClosure R ⟨x ⊗ₜ[𝕜] y, rfl⟩
  intro z; have hz : z ∈ (R.topologicalClosure : Set (E ⊗[𝕜] Completion F)) := hmem z
  rwa [Submodule.topologicalClosure_coe, LinearMap.coe_range, LinearIsometry.coe_toLinearMap] at hz
theorem denseRange_toCompl_comp_rTensor :
    DenseRange ((Completion.toComplₗᵢ : Completion E ⊗[𝕜] F →ₗᵢ[𝕜] _).comp
      ((Completion.toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).rTensor F)) :=
  Completion.denseRange_coe.comp denseRange_toComplₗᵢ_rTensor (Completion.continuous_coe _)
theorem denseRange_toCompl_comp_lTensor :
    DenseRange ((Completion.toComplₗᵢ : E ⊗[𝕜] Completion F →ₗᵢ[𝕜] _).comp
      ((Completion.toComplₗᵢ : F →ₗᵢ[𝕜] Completion F).lTensor E)) :=
  Completion.denseRange_coe.comp denseRange_toComplₗᵢ_lTensor (Completion.continuous_coe _)

variable (𝕜 E F) in
/-- Completing the left factor before completing the tensor product produces the same Hilbert
space: `Completion (Completion E ⊗[𝕜] F) ≃ₗᵢ[𝕜] Completion (E ⊗[𝕜] F)`. -/
noncomputable def completionRTensorEquiv :
    Completion (Completion E ⊗[𝕜] F) ≃ₗᵢ[𝕜] Completion (E ⊗[𝕜] F) :=
  (LinearEquiv.refl 𝕜 (E ⊗[𝕜] F)).extendOfIsometry
    ((Completion.toComplₗᵢ : Completion E ⊗[𝕜] F →ₗᵢ[𝕜] _).comp
      ((Completion.toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).rTensor F)).toLinearMap
    (Completion.toComplₗᵢ : E ⊗[𝕜] F →ₗᵢ[𝕜] _).toLinearMap
    denseRange_toCompl_comp_rTensor Completion.denseRange_coe fun x ↦ by
      simpa using (((Completion.toComplₗᵢ : Completion E ⊗[𝕜] F →ₗᵢ[𝕜] _).comp
        ((Completion.toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).rTensor F)).norm_map x).symm
@[simp] theorem completionRTensorEquiv_tmul_coe (x : E) (y : F) :
    completionRTensorEquiv 𝕜 E F (((x : Completion E) ⊗ₜ[𝕜] y : Completion E ⊗[𝕜] F)) =
      (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ (x ⊗ₜ[𝕜] y)
@[simp] theorem completionRTensorEquiv_symm_tmul (x : E) (y : F) :
    (completionRTensorEquiv 𝕜 E F).symm (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) =
      (((x : Completion E) ⊗ₜ[𝕜] y : Completion E ⊗[𝕜] F)) :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ (x ⊗ₜ[𝕜] y)

variable (𝕜 E F) in
/-- Completing the right factor before completing the tensor product produces the same Hilbert
space: `Completion (E ⊗[𝕜] Completion F) ≃ₗᵢ[𝕜] Completion (E ⊗[𝕜] F)`. -/
noncomputable def completionLTensorEquiv :
    Completion (E ⊗[𝕜] Completion F) ≃ₗᵢ[𝕜] Completion (E ⊗[𝕜] F) :=
  (LinearEquiv.refl 𝕜 (E ⊗[𝕜] F)).extendOfIsometry
    ((Completion.toComplₗᵢ : E ⊗[𝕜] Completion F →ₗᵢ[𝕜] _).comp
      ((Completion.toComplₗᵢ : F →ₗᵢ[𝕜] Completion F).lTensor E)).toLinearMap
    (Completion.toComplₗᵢ : E ⊗[𝕜] F →ₗᵢ[𝕜] _).toLinearMap
    denseRange_toCompl_comp_lTensor Completion.denseRange_coe fun x ↦ by
      simpa using (((Completion.toComplₗᵢ : E ⊗[𝕜] Completion F →ₗᵢ[𝕜] _).comp
        ((Completion.toComplₗᵢ : F →ₗᵢ[𝕜] Completion F).lTensor E)).norm_map x).symm
@[simp] theorem completionLTensorEquiv_tmul_coe (x : E) (y : F) :
    completionLTensorEquiv 𝕜 E F ((x ⊗ₜ[𝕜] (y : Completion F) : E ⊗[𝕜] Completion F)) =
      (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ (x ⊗ₜ[𝕜] y)
@[simp] theorem completionLTensorEquiv_symm_tmul (x : E) (y : F) :
    (completionLTensorEquiv 𝕜 E F).symm (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) =
      ((x ⊗ₜ[𝕜] (y : Completion F) : E ⊗[𝕜] Completion F)) :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ (x ⊗ₜ[𝕜] y)
theorem completionLTensorEquiv_symm_comp_rTensorCompletion (f : E →L[𝕜] F) :
    ((completionLTensorEquiv 𝕜 F G).symm : _ →L[𝕜] _) ∘L f.rTensorCompletion G =
      f.rTensorCompletion (Completion G) ∘L ((completionLTensorEquiv 𝕜 E G).symm : _ →L[𝕜] _) :=
  continuousLinearMap_ext_completion fun _ _ ↦ by simp

variable (𝕜 E F G) in
/-- **Completed associator** between iterated Hilbert tensor completions:
`Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) ≃ₗᵢ[𝕜] Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G))`. -/
noncomputable def assocCompletion :
    Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) ≃ₗᵢ[𝕜]
      Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G)) :=
  (assocIsometry 𝕜 E F G).toLinearEquiv.extendOfIsometry
    ((Completion.toComplₗᵢ : Completion (E ⊗[𝕜] F) ⊗[𝕜] G →ₗᵢ[𝕜] _).comp
      ((Completion.toComplₗᵢ : E ⊗[𝕜] F →ₗᵢ[𝕜] Completion (E ⊗[𝕜] F)).rTensor G)).toLinearMap
    ((Completion.toComplₗᵢ : E ⊗[𝕜] Completion (F ⊗[𝕜] G) →ₗᵢ[𝕜] _).comp
      ((Completion.toComplₗᵢ : F ⊗[𝕜] G →ₗᵢ[𝕜] Completion (F ⊗[𝕜] G)).lTensor E)).toLinearMap
    denseRange_toCompl_comp_rTensor denseRange_toCompl_comp_lTensor fun x ↦ by
      have h₁ := ((Completion.toComplₗᵢ : Completion (E ⊗[𝕜] F) ⊗[𝕜] G →ₗᵢ[𝕜] _).comp
        ((Completion.toComplₗᵢ : E ⊗[𝕜] F →ₗᵢ[𝕜] Completion (E ⊗[𝕜] F)).rTensor G)).norm_map x
      have h₂ := ((Completion.toComplₗᵢ : E ⊗[𝕜] Completion (F ⊗[𝕜] G) →ₗᵢ[𝕜] _).comp
        ((Completion.toComplₗᵢ : F ⊗[𝕜] G →ₗᵢ[𝕜] Completion (F ⊗[𝕜] G)).lTensor E)).norm_map
        (assocIsometry 𝕜 E F G x)
      exact (h₂.trans ((assocIsometry 𝕜 E F G).norm_map x)).trans h₁.symm
@[simp] theorem assocCompletion_tmul (x : E) (y : F) (z : G) :
    assocCompletion 𝕜 E F G (((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] z :
      Completion (E ⊗[𝕜] F) ⊗[𝕜] G) =
      (x ⊗ₜ[𝕜] ((y ⊗ₜ[𝕜] z : F ⊗[𝕜] G) : Completion (F ⊗[𝕜] G)) :
        E ⊗[𝕜] Completion (F ⊗[𝕜] G)) :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ ((x ⊗ₜ[𝕜] y) ⊗ₜ[𝕜] z)
@[simp] theorem assocCompletion_symm_tmul (x : E) (y : F) (z : G) :
    (assocCompletion 𝕜 E F G).symm (x ⊗ₜ[𝕜] ((y ⊗ₜ[𝕜] z : F ⊗[𝕜] G) : Completion (F ⊗[𝕜] G)) :
      E ⊗[𝕜] Completion (F ⊗[𝕜] G)) =
      (((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] z :
        Completion (E ⊗[𝕜] F) ⊗[𝕜] G) :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ (x ⊗ₜ[𝕜] (y ⊗ₜ[𝕜] z))

/-- Continuous linear maps out of `Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G)` are determined by
their values on pure threefold tensors `↑(↑(x ⊗ₜ y) ⊗ₜ z)`. -/
theorem continuousLinearMap_ext_iteratedCompletion {M : Type*} [AddCommGroup M] [Module 𝕜 M]
    [TopologicalSpace M] [T2Space M] {l l' : Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) →L[𝕜] M}
    (h : ∀ (x : E) (y : F) (z : G),
      l (((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] z :
        Completion (E ⊗[𝕜] F) ⊗[𝕜] G) =
      l' (((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] z :
        Completion (E ⊗[𝕜] F) ⊗[𝕜] G)) : l = l' := by
  let emb : (E ⊗[𝕜] F) ⊗[𝕜] G →ₗᵢ[𝕜] Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) :=
    Completion.toComplₗᵢ.comp (Completion.toComplₗᵢ.rTensor G)
  have hlin : l.toLinearMap.comp emb.toLinearMap = l'.toLinearMap.comp emb.toLinearMap :=
    TensorProduct.ext_threefold h
  exact DFunLike.coe_injective <| denseRange_toCompl_comp_rTensor.equalizer
    l.continuous l'.continuous <| funext fun w ↦ congr($hlin w)

theorem assocCompletion_comp_rTensorCompletion_rTensorCompletion (f : E →L[𝕜] H) :
    (assocCompletion 𝕜 H F G : _ →L[𝕜] _) ∘L (f.rTensorCompletion F).rTensorCompletion G =
      f.rTensorCompletion (Completion (F ⊗[𝕜] G)) ∘L (assocCompletion 𝕜 E F G : _ →L[𝕜] _) :=
  continuousLinearMap_ext_iteratedCompletion fun _ _ _ ↦ by simp
theorem assocCompletion_comp_lTensorCompletion_rTensorCompletion (g : F →L[𝕜] H) :
    (assocCompletion 𝕜 E H G : _ →L[𝕜] _) ∘L (g.lTensorCompletion E).rTensorCompletion G =
      (g.rTensorCompletion G).lTensorCompletion E ∘L (assocCompletion 𝕜 E F G : _ →L[𝕜] _) :=
  continuousLinearMap_ext_iteratedCompletion fun _ _ _ ↦ by simp
theorem assocCompletion_comp_lTensorCompletion (h : G →L[𝕜] H) :
    (assocCompletion 𝕜 E F H : _ →L[𝕜] _) ∘L h.lTensorCompletion (Completion (E ⊗[𝕜] F)) =
      (h.lTensorCompletion F).lTensorCompletion E ∘L (assocCompletion 𝕜 E F G : _ →L[𝕜] _) :=
  continuousLinearMap_ext_iteratedCompletion fun _ _ _ ↦ by simp

theorem conjStarAlgEquiv_assocCompletion_rTensorCompletion_rTensorCompletion (f : E →L[𝕜] E) :
    (assocCompletion 𝕜 E F G).conjStarAlgEquiv ((f.rTensorCompletion F).rTensorCompletion G) =
      f.rTensorCompletion (Completion (F ⊗[𝕜] G)) := by
  ext w; simpa [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] using congr(
    $(assocCompletion_comp_rTensorCompletion_rTensorCompletion f)
      ((assocCompletion 𝕜 E F G).symm w))
theorem conjStarAlgEquiv_assocCompletion_lTensorCompletion_rTensorCompletion (g : F →L[𝕜] F) :
    (assocCompletion 𝕜 E F G).conjStarAlgEquiv ((g.lTensorCompletion E).rTensorCompletion G) =
      (g.rTensorCompletion G).lTensorCompletion E := by
  ext w; simpa [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] using congr(
    $(assocCompletion_comp_lTensorCompletion_rTensorCompletion g)
      ((assocCompletion 𝕜 E F G).symm w))
theorem conjStarAlgEquiv_assocCompletion_lTensorCompletion (h : G →L[𝕜] G) :
    (assocCompletion 𝕜 E F G).conjStarAlgEquiv (h.lTensorCompletion (Completion (E ⊗[𝕜] F))) =
      (h.lTensorCompletion F).lTensorCompletion E := by
  ext w; simpa [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] using congr(
    $(assocCompletion_comp_lTensorCompletion h) ((assocCompletion 𝕜 E F G).symm w))

end TensorProduct

/-! ### Vector-valued `ℓ²` coordinates and ultraweak continuity -/

namespace HilbertBasis

open TensorProduct

variable {ι 𝕜 E E' F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

variable (E) in
/-- The `i`-th fiberwise isometric embedding `x ↦ ↑(x ⊗ₜ b i)` of `E` into `Completion (E ⊗[𝕜] F)`
associated to a Hilbert basis `b` of `F`. -/
noncomputable def tensorCompletionFiber (b : HilbertBasis ι 𝕜 F) (i : ι) :
    E →ₗᵢ[𝕜] Completion (E ⊗[𝕜] F) where
  toLinearMap := ((tmulCLM 𝕜 E F).flip (b i)).toLinearMap
  norm_map' x := by simp [b.orthonormal.1 i]
@[simp] theorem tensorCompletionFiber_apply (b : HilbertBasis ι 𝕜 F) (i : ι) (x : E) :
    b.tensorCompletionFiber E i x = (x ⊗ₜ[𝕜] b i : E ⊗[𝕜] F) := tmulCLM_apply x (b i)

variable [CompleteSpace E] [CompleteSpace E']

variable (E) in
theorem isHilbertSum_tensorCompletionFiber (b : HilbertBasis ι 𝕜 F) :
    IsHilbertSum 𝕜 (fun _ : ι ↦ E) (b.tensorCompletionFiber E) := by
  refine IsHilbertSum.mk (fun _ _ hij _ _ ↦ by simp [b.orthonormal.2 hij]) ?_
  rw [← topologicalClosure_span_tmul_coe (𝕜 := 𝕜) (E := E) (F := F)]
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
    (Submodule.isClosed_topologicalClosure _)
  rintro _ ⟨x, y, rfl⟩
  exact mem_closure_of_tendsto ((b.hasSum_repr y).mapL (tmulCLM 𝕜 E F x))
    (Eventually.of_forall fun _ ↦ sum_mem fun i _ ↦
      Submodule.mem_iSup_of_mem i ⟨b.repr y i • x, by simp⟩)

variable (E) in
/-- **Vector-valued `ℓ²` identification of a completed tensor product.** A Hilbert basis `b` of `F`
identifies `Completion (E ⊗[𝕜] F)` isometrically with `ℓ²(ι, E)`, sending `(x ⊗ₜ y : E ⊗[𝕜] F)` to
the sequence `i ↦ ⟪b i, y⟫ • x`. -/
noncomputable def tensorCompletionEquiv (b : HilbertBasis ι 𝕜 F) :
    Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] ℓ²(ι, E) :=
  (b.isHilbertSum_tensorCompletionFiber E).linearIsometryEquiv
@[simp] theorem tensorCompletionEquiv_symm_single [DecidableEq ι] (b : HilbertBasis ι 𝕜 F) (i : ι)
    (x : E) : (b.tensorCompletionEquiv E).symm (lp.single 2 i x) = (x ⊗ₜ[𝕜] b i : E ⊗[𝕜] F) :=
  ((b.isHilbertSum_tensorCompletionFiber E).linearIsometryEquiv_symm_apply_single x).trans
    (b.tensorCompletionFiber_apply i x)
@[simp] theorem tensorCompletionEquiv_tmul_apply (b : HilbertBasis ι 𝕜 F) (x : E) (y : F) (i : ι) :
    b.tensorCompletionEquiv E (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) i = b.repr y i • x := by
  classical
  refine ext_inner_left 𝕜 fun z ↦ ?_
  calc ⟪z, b.tensorCompletionEquiv E (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) i⟫_𝕜
      = ⟪lp.single 2 i z, b.tensorCompletionEquiv E (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F)⟫_𝕜 :=
        (lp.inner_single_left (G := fun _ : ι ↦ E) i z _).symm
    _ = ⟪(b.tensorCompletionEquiv E).symm (lp.single 2 i z), (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F)⟫_𝕜 :=
        ((b.tensorCompletionEquiv E).symm.inner_map_eq_flip (lp.single 2 i z) _).symm
    _ = ⟪z, b.repr y i • x⟫_𝕜 := by
        rw [tensorCompletionEquiv_symm_single, Completion.inner_coe, inner_tmul,
          b.repr_apply_apply, inner_smul_right, mul_comm]

/-- Under `HilbertBasis.tensorCompletionEquiv`, right amplification `f.rTensorCompletion F` becomes
the Hilbert-sum ampliation `lp.ampliation ι 2 f`. -/
theorem tensorCompletionEquiv_comp_rTensorCompletion (b : HilbertBasis ι 𝕜 F) (f : E →L[𝕜] E') :
    (b.tensorCompletionEquiv E' : _ →L[𝕜] _) ∘L f.rTensorCompletion F =
      lp.ampliation ι 2 f ∘L (b.tensorCompletionEquiv E : _ →L[𝕜] _) :=
  continuousLinearMap_ext_completion fun _ _ ↦ by ext; simp

end HilbertBasis

namespace TensorProduct

variable {𝕜 ι E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

variable (𝕜 ι E) in
/-- Canonical isometric identification `Completion (E ⊗[𝕜] ℓ²(ι, 𝕜)) ≃ₗᵢ[𝕜] ℓ²(ι, E)` for a
Hilbert space `E` and any index type `ι`. -/
noncomputable def lpTensorCompletionEquiv : Completion (E ⊗[𝕜] ℓ²(ι, 𝕜)) ≃ₗᵢ[𝕜] ℓ²(ι, E) :=
  (HilbertBasis.ofRepr (.refl 𝕜 ℓ²(ι, 𝕜))).tensorCompletionEquiv E
@[simp] theorem lpTensorCompletionEquiv_tmul_apply (x : E) (ξ : ℓ²(ι, 𝕜)) (i : ι) :
    lpTensorCompletionEquiv 𝕜 ι E (x ⊗ₜ[𝕜] ξ : E ⊗[𝕜] ℓ²(ι, 𝕜)) i = ξ i • x :=
  (HilbertBasis.ofRepr (.refl 𝕜 ℓ²(ι, 𝕜))).tensorCompletionEquiv_tmul_apply x ξ i
@[simp] theorem lpTensorCompletionEquiv_symm_single [DecidableEq ι] (i : ι) (x : E) :
    (lpTensorCompletionEquiv 𝕜 ι E).symm (lp.single 2 i x) =
      (x ⊗ₜ[𝕜] lp.single 2 i (1 : 𝕜) : E ⊗[𝕜] ℓ²(ι, 𝕜)) := by
  rw [lpTensorCompletionEquiv, HilbertBasis.tensorCompletionEquiv_symm_single]
  exact congrArg (fun ξ ↦ ((x ⊗ₜ[𝕜] ξ : E ⊗[𝕜] ℓ²(ι, 𝕜)) : Completion (E ⊗[𝕜] ℓ²(ι, 𝕜))))
    ((HilbertBasis.ofRepr (.refl 𝕜 ℓ²(ι, 𝕜))).repr_self i)
theorem lpTensorCompletionEquiv_comp_rTensorCompletion (f : E →L[𝕜] F) :
    (lpTensorCompletionEquiv 𝕜 ι F : _ →L[𝕜] _) ∘L f.rTensorCompletion ℓ²(ι, 𝕜) =
      lp.ampliation ι 2 f ∘L (lpTensorCompletionEquiv 𝕜 ι E : _ →L[𝕜] _) :=
  (HilbertBasis.ofRepr (.refl 𝕜 ℓ²(ι, 𝕜))).tensorCompletionEquiv_comp_rTensorCompletion f

end TensorProduct

namespace TauCeti.ContinuousLinearMapUltraweak

open TensorProduct

variable {𝕜 E F G : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- Amplification on the right is ultraweakly continuous for any inner product space `G` (without
separability, nontriviality, or completeness assumptions on `G`). -/
@[fun_prop]
theorem continuous_rTensorCompletion [CompleteSpace E] [CompleteSpace F] (G : Type*)
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] :
    Continuous fun A : ContinuousLinearMapUltraweak 𝕜 E F ↦
      ofCLM (A.toCLM.rTensorCompletion G) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 (Completion G)
  let uE := (completionLTensorEquiv 𝕜 E G).symm.trans (b.tensorCompletionEquiv E)
  let uF := (completionLTensorEquiv 𝕜 F G).symm.trans (b.tensorCompletionEquiv F)
  refine ((continuous_linearIsometryEquiv_comp_left uF.symm).comp
    ((continuous_comp_right uE.toLinearIsometry.toContinuousLinearMap).comp
      (continuous_ampliation w))).congr fun A ↦ congrArg ofCLM ?_
  refine continuousLinearMap_ext_completion fun x z ↦ uF.injective ?_
  simpa [uE, uF] using (congr($(b.tensorCompletionEquiv_comp_rTensorCompletion A.toCLM)
    ((x ⊗ₜ[𝕜] (z : Completion G) : E ⊗[𝕜] Completion G) : Completion (E ⊗[𝕜] Completion G)))).symm

/-- Amplification on the left is ultraweakly continuous for any inner product space `E` (without
separability, nontriviality, or completeness assumptions on `E`). -/
@[fun_prop]
theorem continuous_lTensorCompletion (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [CompleteSpace F] [CompleteSpace G] :
    Continuous fun A : ContinuousLinearMapUltraweak 𝕜 F G ↦
      ofCLM (A.toCLM.lTensorCompletion E) := by
  let cEF := (commIsometry 𝕜 E F).completion
  let cGE := (commIsometry 𝕜 G E).completion
  refine ((continuous_linearIsometryEquiv_comp_left cGE).comp
    ((continuous_comp_right cEF.toLinearIsometry.toContinuousLinearMap).comp
      (continuous_rTensorCompletion E))).congr fun _ ↦
    congrArg ofCLM <| continuousLinearMap_ext_completion fun _ _ ↦ by simp [cEF, cGE]

end TauCeti.ContinuousLinearMapUltraweak

/-! ### Vector-functional slice maps (Fubini maps) -/

namespace TensorProduct

variable {𝕜 E₁ E₂ E₃ F₁ F₂ F₃ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃] [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [NormedAddCommGroup F₃] [InnerProductSpace 𝕜 F₃]

private theorem norm_sliceRight_aux [CompleteSpace E₂] (ξ : F₁) (η : F₂)
    (T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) :
    ‖((tmulCLM 𝕜 E₂ F₂).flip η).adjoint ∘L T ∘L (tmulCLM 𝕜 E₁ F₁).flip ξ‖ ≤ ‖ξ‖ * ‖η‖ * ‖T‖ := by
  calc ‖((tmulCLM 𝕜 E₂ F₂).flip η).adjoint ∘L T ∘L (tmulCLM 𝕜 E₁ F₁).flip ξ‖
      ≤ ‖((tmulCLM 𝕜 E₂ F₂).flip η).adjoint‖ * (‖T‖ * ‖(tmulCLM 𝕜 E₁ F₁).flip ξ‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans <|
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ ‖η‖ * (‖T‖ * ‖ξ‖) := by
        rw [ContinuousLinearMap.adjoint.norm_map]
        gcongr; exacts [norm_flip_tmulCLM_apply_le η, norm_flip_tmulCLM_apply_le ξ]
    _ = ‖ξ‖ * ‖η‖ * ‖T‖ := by ring

private theorem norm_sliceLeft_aux [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂)
    (T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) :
    ‖(tmulCLM 𝕜 E₂ F₂ e₂).adjoint ∘L T ∘L tmulCLM 𝕜 E₁ F₁ e₁‖ ≤ ‖e₁‖ * ‖e₂‖ * ‖T‖ := by
  calc ‖(tmulCLM 𝕜 E₂ F₂ e₂).adjoint ∘L T ∘L tmulCLM 𝕜 E₁ F₁ e₁‖
      ≤ ‖(tmulCLM 𝕜 E₂ F₂ e₂).adjoint‖ * (‖T‖ * ‖tmulCLM 𝕜 E₁ F₁ e₁‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans <|
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ ‖e₂‖ * (‖T‖ * ‖e₁‖) := by
        rw [ContinuousLinearMap.adjoint.norm_map]
        gcongr; exacts [norm_tmulCLM_apply_le e₂, norm_tmulCLM_apply_le e₁]
    _ = ‖e₁‖ * ‖e₂‖ * ‖T‖ := by ring

/-- **Right slice map** `R_{ξ, η}`: contracts the right tensor factor against `ξ ∈ F₁` and
`η ∈ F₂`, characterized by `⟪x₂, sliceRight ξ η T x₁⟫ = ⟪↑(x₂ ⊗ₜ η), T ↑(x₁ ⊗ₜ ξ)⟫`. -/
noncomputable def sliceRight [CompleteSpace E₂] (ξ : F₁) (η : F₂) :
    (Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) →L[𝕜] (E₁ →L[𝕜] E₂) :=
  LinearMap.mkContinuous
    { toFun := fun T ↦ ((tmulCLM 𝕜 E₂ F₂).flip η).adjoint ∘L T ∘L (tmulCLM 𝕜 E₁ F₁).flip ξ
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp } (‖ξ‖ * ‖η‖) (norm_sliceRight_aux ξ η)

/-- **Left slice map** `L_{e₁, e₂}`: contracts the left tensor factor against `e₁ ∈ E₁` and
`e₂ ∈ E₂`, characterized by `⟪y₂, sliceLeft e₁ e₂ T y₁⟫ = ⟪↑(e₂ ⊗ₜ y₂), T ↑(e₁ ⊗ₜ y₁)⟫`. -/
noncomputable def sliceLeft [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) :
    (Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) →L[𝕜] (F₁ →L[𝕜] F₂) :=
  LinearMap.mkContinuous
    { toFun := fun T ↦ (tmulCLM 𝕜 E₂ F₂ e₂).adjoint ∘L T ∘L tmulCLM 𝕜 E₁ F₁ e₁
      map_add' := fun _ _ ↦ by ext; simp
      map_smul' := fun _ _ ↦ by ext; simp } (‖e₁‖ * ‖e₂‖) (norm_sliceLeft_aux e₁ e₂)

section SliceLemmas
variable (T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂))

theorem sliceRight_def [CompleteSpace E₂] (ξ : F₁) (η : F₂) :
    sliceRight ξ η T = ((tmulCLM 𝕜 E₂ F₂).flip η).adjoint ∘L T ∘L (tmulCLM 𝕜 E₁ F₁).flip ξ :=
  (rfl)
theorem sliceLeft_def [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) :
    sliceLeft e₁ e₂ T = (tmulCLM 𝕜 E₂ F₂ e₂).adjoint ∘L T ∘L tmulCLM 𝕜 E₁ F₁ e₁ := (rfl)

@[simp] theorem inner_sliceRight_apply [CompleteSpace E₂] (ξ : F₁) (η : F₂) (x₁ : E₁) (x₂ : E₂) :
    ⟪x₂, sliceRight ξ η T x₁⟫_𝕜 =
      ⟪((x₂ ⊗ₜ[𝕜] η : E₂ ⊗[𝕜] F₂) : Completion (E₂ ⊗[𝕜] F₂)), T (x₁ ⊗ₜ[𝕜] ξ : E₁ ⊗[𝕜] F₁)⟫_𝕜 := by
  simp [sliceRight_def, ContinuousLinearMap.adjoint_inner_right]
@[simp] theorem inner_sliceLeft_apply [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) (y₁ : F₁) (y₂ : F₂) :
    ⟪y₂, sliceLeft e₁ e₂ T y₁⟫_𝕜 =
      ⟪((e₂ ⊗ₜ[𝕜] y₂ : E₂ ⊗[𝕜] F₂) : Completion (E₂ ⊗[𝕜] F₂)), T (e₁ ⊗ₜ[𝕜] y₁ : E₁ ⊗[𝕜] F₁)⟫_𝕜 := by
  simp [sliceLeft_def, ContinuousLinearMap.adjoint_inner_right]

theorem norm_sliceRight_le [CompleteSpace E₂] (ξ : F₁) (η : F₂) :
    ‖(sliceRight ξ η :
      (Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) →L[𝕜] (E₁ →L[𝕜] E₂))‖ ≤ ‖ξ‖ * ‖η‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _
theorem norm_sliceLeft_le [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) :
    ‖(sliceLeft e₁ e₂ :
      (Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) →L[𝕜] (F₁ →L[𝕜] F₂))‖ ≤ ‖e₁‖ * ‖e₂‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _
theorem norm_sliceRight_apply_le [CompleteSpace E₂] (ξ : F₁) (η : F₂) :
    ‖sliceRight ξ η T‖ ≤ ‖T‖ * ‖ξ‖ * ‖η‖ := by
  simpa only [sliceRight_def, mul_right_comm, mul_comm ‖T‖] using norm_sliceRight_aux ξ η T
theorem norm_sliceLeft_apply_le [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) :
    ‖sliceLeft e₁ e₂ T‖ ≤ ‖T‖ * ‖e₁‖ * ‖e₂‖ := by
  simpa only [sliceLeft_def, mul_right_comm, mul_comm ‖T‖] using norm_sliceLeft_aux e₁ e₂ T

@[simp] theorem adjoint_sliceRight [CompleteSpace E₁] [CompleteSpace E₂] (ξ : F₁) (η : F₂) :
    (sliceRight ξ η T).adjoint = sliceRight η ξ T.adjoint := by
  simp [sliceRight_def, ContinuousLinearMap.comp_assoc]
@[simp] theorem adjoint_sliceLeft [CompleteSpace F₁] [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) :
    (sliceLeft e₁ e₂ T).adjoint = sliceLeft e₂ e₁ T.adjoint := by
  simp [sliceLeft_def, ContinuousLinearMap.comp_assoc]
end SliceLemmas

@[simp] theorem sliceRight_mapL_completion [CompleteSpace E₂] (ξ : F₁) (η : F₂)
    (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) :
    sliceRight ξ η (mapL f g).completion = ⟪η, g ξ⟫_𝕜 • f := by ext; simp [sliceRight_def]
@[simp] theorem sliceLeft_mapL_completion [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂)
    (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) :
    sliceLeft e₁ e₂ (mapL f g).completion = ⟪e₂, f e₁⟫_𝕜 • g := by ext; simp [sliceLeft_def]
@[simp] theorem sliceRight_rTensorCompletion [CompleteSpace E₂] (ξ η : F₁) (f : E₁ →L[𝕜] E₂) :
    sliceRight ξ η (f.rTensorCompletion F₁) = ⟪η, ξ⟫_𝕜 • f := by
  rw [ContinuousLinearMap.rTensorCompletion_eq_mapL_completion, sliceRight_mapL_completion,
    ContinuousLinearMap.id_apply]
@[simp] theorem sliceRight_lTensorCompletion [CompleteSpace E₁] (ξ : F₁) (η : F₂)
    (g : F₁ →L[𝕜] F₂) :
    sliceRight ξ η (g.lTensorCompletion E₁) = ⟪η, g ξ⟫_𝕜 • .id 𝕜 E₁ := by
  rw [ContinuousLinearMap.lTensorCompletion_eq_mapL_completion, sliceRight_mapL_completion]
@[simp] theorem sliceLeft_lTensorCompletion [CompleteSpace F₂] (e₁ e₂ : E₁) (g : F₁ →L[𝕜] F₂) :
    sliceLeft e₁ e₂ (g.lTensorCompletion E₁) = ⟪e₂, e₁⟫_𝕜 • g := by
  rw [ContinuousLinearMap.lTensorCompletion_eq_mapL_completion, sliceLeft_mapL_completion,
    ContinuousLinearMap.id_apply]
@[simp] theorem sliceLeft_rTensorCompletion [CompleteSpace F₁] (e₁ : E₁) (e₂ : E₂)
    (f : E₁ →L[𝕜] E₂) :
    sliceLeft e₁ e₂ (f.rTensorCompletion F₁) = ⟪e₂, f e₁⟫_𝕜 • .id 𝕜 F₁ := by
  rw [ContinuousLinearMap.rTensorCompletion_eq_mapL_completion, sliceLeft_mapL_completion]

/-- Right slice maps are right module homomorphisms over operators on the left factor. -/
theorem sliceRight_comp_rTensorCompletion [CompleteSpace E₃]
    (ξ : F₁) (η : F₂) (T : Completion (E₂ ⊗[𝕜] F₁) →L[𝕜] Completion (E₃ ⊗[𝕜] F₂))
    (f : E₁ →L[𝕜] E₂) :
    sliceRight ξ η (T ∘L f.rTensorCompletion F₁) = sliceRight ξ η T ∘L f := by
  ext; exact ext_inner_left 𝕜 fun _ ↦ by simp

/-- Right slice maps are left module homomorphisms over operators on the left factor. -/
theorem rTensorCompletion_comp_sliceRight [CompleteSpace E₂] [CompleteSpace E₃]
    (ξ : F₁) (η : F₂) (f : E₂ →L[𝕜] E₃)
    (T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) :
    sliceRight ξ η (f.rTensorCompletion F₂ ∘L T) = f ∘L sliceRight ξ η T := by
  ext x₁; refine ext_inner_left 𝕜 fun x₃ ↦ ?_
  rw [inner_sliceRight_apply, ContinuousLinearMap.comp_apply (f.rTensorCompletion F₂),
    ← ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_rTensorCompletion,
    ContinuousLinearMap.rTensorCompletion_tmul, ← inner_sliceRight_apply,
    ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply]

/-- Left slice maps are right module homomorphisms over operators on the right factor. -/
theorem sliceLeft_comp_lTensorCompletion [CompleteSpace F₃]
    (e₁ : E₁) (e₂ : E₂) (T : Completion (E₁ ⊗[𝕜] F₂) →L[𝕜] Completion (E₂ ⊗[𝕜] F₃))
    (g : F₁ →L[𝕜] F₂) :
    sliceLeft e₁ e₂ (T ∘L g.lTensorCompletion E₁) = sliceLeft e₁ e₂ T ∘L g := by
  ext; exact ext_inner_left 𝕜 fun _ ↦ by simp

/-- Left slice maps are left module homomorphisms over operators on the right factor. -/
theorem lTensorCompletion_comp_sliceLeft [CompleteSpace F₂] [CompleteSpace F₃]
    (e₁ : E₁) (e₂ : E₂) (g : F₂ →L[𝕜] F₃)
    (T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) :
    sliceLeft e₁ e₂ (g.lTensorCompletion E₂ ∘L T) = g ∘L sliceLeft e₁ e₂ T := by
  ext y₁; refine ext_inner_left 𝕜 fun y₃ ↦ ?_
  rw [inner_sliceLeft_apply, ContinuousLinearMap.comp_apply (g.lTensorCompletion E₂),
    ← ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_lTensorCompletion,
    ContinuousLinearMap.lTensorCompletion_tmul, ← inner_sliceLeft_apply,
    ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply]

@[simp] theorem star_sliceRight [CompleteSpace E₁] (ξ η : F₁)
    (T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₁ ⊗[𝕜] F₁)) :
    star (sliceRight ξ η T) = sliceRight η ξ (star T) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, adjoint_sliceRight]
@[simp] theorem star_sliceLeft [CompleteSpace F₁] (e₁ e₂ : E₁)
    (T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₁ ⊗[𝕜] F₁)) :
    star (sliceLeft e₁ e₂ T) = sliceLeft e₂ e₁ (star T) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, adjoint_sliceLeft]

/-- Right slice maps separate all bounded operators between completed tensor products. -/
theorem ext_of_sliceRight [CompleteSpace E₂]
    {S T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)}
    (h : ∀ (ξ : F₁) (η : F₂), sliceRight ξ η S = sliceRight ξ η T) : S = T :=
  continuousLinearMap_ext_completion fun x₁ ξ ↦ ext_completion_inner_tmul_left.2 fun x₂ η ↦ by
    rw [← inner_sliceRight_apply, ← inner_sliceRight_apply]
    exact congrArg (fun L ↦ ⟪x₂, L x₁⟫_𝕜) (h ξ η)

/-- Left slice maps separate all bounded operators between completed tensor products. -/
theorem ext_of_sliceLeft [CompleteSpace F₂]
    {S T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)}
    (h : ∀ (e₁ : E₁) (e₂ : E₂), sliceLeft e₁ e₂ S = sliceLeft e₁ e₂ T) : S = T :=
  continuousLinearMap_ext_completion fun e₁ y₁ ↦ ext_completion_inner_tmul_left.2 fun e₂ y₂ ↦ by
    rw [← inner_sliceLeft_apply, ← inner_sliceLeft_apply]
    exact congrArg (fun L ↦ ⟪y₂, L y₁⟫_𝕜) (h e₁ e₂)

end TensorProduct

namespace TauCeti.ContinuousLinearMapUltraweak

open TensorProduct

variable {𝕜 E₁ E₂ F₁ F₂ : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁] [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂]

/-- Every right slice map `T ↦ sliceRight ξ η T` is ultraweakly continuous. -/
@[fun_prop]
theorem continuous_sliceRight [CompleteSpace E₂] (ξ : F₁) (η : F₂) :
    Continuous fun A : ContinuousLinearMapUltraweak 𝕜 (Completion (E₁ ⊗[𝕜] F₁))
        (Completion (E₂ ⊗[𝕜] F₂)) ↦ ofCLM (sliceRight ξ η A.toCLM) :=
  (continuous_comp_left ((tmulCLM 𝕜 E₂ F₂).flip η).adjoint).comp
    (continuous_comp_right ((tmulCLM 𝕜 E₁ F₁).flip ξ))

/-- Every left slice map `T ↦ sliceLeft e₁ e₂ T` is ultraweakly continuous. -/
@[fun_prop]
theorem continuous_sliceLeft [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) :
    Continuous fun A : ContinuousLinearMapUltraweak 𝕜 (Completion (E₁ ⊗[𝕜] F₁))
        (Completion (E₂ ⊗[𝕜] F₂)) ↦ ofCLM (sliceLeft e₁ e₂ A.toCLM) :=
  (continuous_comp_left (tmulCLM 𝕜 E₂ F₂ e₂).adjoint).comp
    (continuous_comp_right (tmulCLM 𝕜 E₁ F₁ e₁))

end TauCeti.ContinuousLinearMapUltraweak
