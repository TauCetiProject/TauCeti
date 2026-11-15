/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import TauCeti.Analysis.Normed.Operator.Completion

/-!
# Completed Hilbert tensor products and operator amplifications

For inner product spaces `E` and `F` over `𝕜` (`ℝ` or `ℂ`), Mathlib equips the algebraic tensor
product `E ⊗[𝕜] F` with the positive-definite inner product
`⟪e₁ ⊗ₜ f₁, e₂ ⊗ₜ f₂⟫ = ⟪e₁, e₂⟫ ⟪f₁, f₂⟫`, and its uniform completion
`UniformSpace.Completion (E ⊗[𝕜] F)` is a complete inner product space. Neither `E` nor `F` is
assumed complete in the basic definitions, so operators on pre-Hilbert subspaces can be amplified
directly.

This file develops the bounded-operator and structural-unitary API of completed Hilbert tensor
products:

* **Exact algebraic and completed operator norms**: `‖TensorProduct.mapL f g‖ = ‖f‖ * ‖g‖`, hence
  `‖f.rTensor G‖ = ‖f‖` when `G` is nontrivial (and `0` when `G` is subsingleton), and the same
  identities for their extensions `TensorProduct.mapLCompletion`,
  `ContinuousLinearMap.rTensorCompletion` and `ContinuousLinearMap.lTensorCompletion`.
* **Density and uniqueness on pure tensors**: pure tensors `↑(e ⊗ₜ f)` have dense linear span in
  `Completion (E ⊗[𝕜] F)`, so continuous semilinear maps and vectors are determined by their values
  or inner products on pure tensors (`TensorProduct.completion_continuousLinearMap_ext`,
  `TensorProduct.completion_ext_iff_inner_right`).
* **Adjoints and star homomorphisms**: `(f.rTensorCompletion G)† = f†.rTensorCompletion G` for
  complete `E` and `F` (with no completeness assumption on `G`), and symmetrically for
  `lTensorCompletion`; for endomorphisms this bundles into the unital star algebra homomorphisms
  `ContinuousLinearMap.rTensorCompletionStarAlgHom` and
  `ContinuousLinearMap.lTensorCompletionStarAlgHom`.
* **Structural unitaries**: factor-completion equivalences `TensorProduct.completionLeftEquiv` and
  `TensorProduct.completionRightEquiv`, the iterated associativity unitary
  `TensorProduct.assocCompletion` between `(E ⊗̂ F) ⊗̂ G` and `E ⊗̂ (F ⊗̂ G)`, scalar-unit unitaries
  `TensorProduct.lidCompletion` and `TensorProduct.ridCompletion`, and their intertwining identities
  for amplified and tensor-product operators.

## References

* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras*, Vol. I,
  Academic Press, 1983, §2.6.
* M. Takesaki, *Theory of Operator Algebras I*, Springer, 1979, Chapter IV, §1.
-/

public section

open UniformSpace
open scoped TensorProduct InnerProductSpace InnerProduct

/-! ### Exact operator norms on algebraic inner-product tensor products -/

namespace TensorProduct

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Norm of an elementary operator tensor.** On inner-product tensor products, the operator norm
of `mapL f g` is the product of the operator norms of `f` and `g`, including when any factor is
zero. -/
@[simp]
theorem norm_mapL (f : E →L[𝕜] F) (g : G →L[𝕜] H) : ‖mapL f g‖ = ‖f‖ * ‖g‖ := by
  refine le_antisymm (norm_mapL_le f g) ?_
  have hpoint (x : E) : ‖f x‖ * ‖g‖ ≤ ‖mapL f g‖ * ‖x‖ := by
    rcases (norm_nonneg (f x)).eq_or_lt with hfx | hfx
    · rw [← hfx, zero_mul]
      positivity
    · rw [mul_comm ‖f x‖, ← le_div_iff₀ hfx]
      refine g.opNorm_le_bound (by positivity) fun y ↦ ?_
      rw [div_mul_eq_mul_div, le_div_iff₀ hfx, mul_comm _ ‖f x‖]
      simpa only [mapL_tmul, norm_tmul, mul_assoc] using (mapL f g).le_opNorm (x ⊗ₜ[𝕜] y)
  rcases (norm_nonneg g).eq_or_lt with hg | hg
  · rw [← hg, mul_zero]
    positivity
  · rw [← le_div_iff₀ hg]
    refine f.opNorm_le_bound (by positivity) fun x ↦ ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hg]
    exact hpoint x

end TensorProduct

namespace ContinuousLinearMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- Tensoring a bounded operator on the right with a nontrivial inner product space preserves its
operator norm. -/
@[simp]
theorem norm_rTensor [Nontrivial G] (f : E →L[𝕜] F) : ‖f.rTensor G‖ = ‖f‖ := by
  rw [f.rTensor_eq_mapL G, TensorProduct.norm_mapL, norm_id, mul_one]

/-- Tensoring on the right with a subsingleton space gives the zero operator. -/
@[simp]
theorem rTensor_eq_zero_of_subsingleton [Subsingleton G] (f : E →L[𝕜] F) : f.rTensor G = 0 :=
  Subsingleton.elim _ _

/-- Tensoring a bounded operator on the left with a nontrivial inner product space preserves its
operator norm. -/
@[simp]
theorem norm_lTensor [Nontrivial E] (g : F →L[𝕜] G) : ‖g.lTensor E‖ = ‖g‖ := by
  rw [g.lTensor_eq_mapL E, TensorProduct.norm_mapL, norm_id, one_mul]

/-- Tensoring on the left with a subsingleton space gives the zero operator. -/
@[simp]
theorem lTensor_eq_zero_of_subsingleton [Subsingleton E] (g : F →L[𝕜] G) : g.lTensor E = 0 :=
  Subsingleton.elim _ _

end ContinuousLinearMap

/-! ### Pure tensors, density and extensionality in completed Hilbert tensor products -/

namespace TensorProduct

section Density

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

variable (𝕜 E F) in
/-- The canonical bounded bilinear map sending `(e, f)` to the pure tensor `↑(e ⊗ₜ f)` in the
completed Hilbert tensor product `Completion (E ⊗[𝕜] F)`. -/
noncomputable def mkLCompletion : E →L[𝕜] F →L[𝕜] Completion (E ⊗[𝕜] F) :=
  (ContinuousLinearMap.compL 𝕜 F (E ⊗[𝕜] F) (Completion (E ⊗[𝕜] F)) Completion.toComplL) ∘L
    mkL 𝕜 E F

@[simp]
theorem mkLCompletion_apply (e : E) (f : F) :
    mkLCompletion 𝕜 E F e f = (↑(e ⊗ₜ[𝕜] f) : Completion (E ⊗[𝕜] F)) :=
  (rfl)

theorem norm_mkLCompletion_le : ‖mkLCompletion 𝕜 E F‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun e ↦ ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f ↦ ?_
  simp

/-- Pure tensors `↑(e ⊗ₜ f)` span a dense submodule of the completed Hilbert tensor product. -/
theorem dense_span_coe_tmul :
    Dense ((Submodule.span 𝕜
      {u : Completion (E ⊗[𝕜] F) | ∃ (e : E) (f : F), (↑(e ⊗ₜ[𝕜] f) : Completion (E ⊗[𝕜] F)) = u} :
        Submodule 𝕜 (Completion (E ⊗[𝕜] F))) : Set (Completion (E ⊗[𝕜] F))) := by
  let S : Submodule 𝕜 (Completion (E ⊗[𝕜] F)) := Submodule.span 𝕜
    {u : Completion (E ⊗[𝕜] F) | ∃ (e : E) (f : F), (↑(e ⊗ₜ[𝕜] f) : Completion (E ⊗[𝕜] F)) = u}
  refine Completion.denseRange_coe.mono ?_
  rintro _ ⟨z, rfl⟩
  change (Completion.toComplL : E ⊗[𝕜] F →L[𝕜] Completion (E ⊗[𝕜] F)) z ∈ (S : Set _)
  have hz : z ∈ Submodule.span 𝕜 {t : E ⊗[𝕜] F | ∃ (e : E) (f : F), e ⊗ₜ[𝕜] f = t} := by
    rw [span_tmul_eq_top]
    trivial
  exact SetLike.mem_coe.mpr <| Submodule.span_induction
    (p := fun x _ ↦ (Completion.toComplL : E ⊗[𝕜] F →L[𝕜] Completion (E ⊗[𝕜] F)) x ∈ S)
    (by rintro _ ⟨e, f, rfl⟩; exact Submodule.subset_span ⟨e, f, rfl⟩)
    (by simp)
    (fun x y _ _ hx hy ↦ by rw [map_add]; exact S.add_mem hx hy)
    (fun c x _ hx ↦ by rw [map_smul]; exact S.smul_mem c hx) hz

/-- Two continuous semilinear maps from a completed Hilbert tensor product into a Hausdorff space
are equal when they agree on pure tensors. -/
theorem completion_continuousLinearMap_ext {𝕜₂ M : Type*} [Semiring 𝕜₂] {σ : 𝕜 →+* 𝕜₂}
    [AddCommGroup M] [Module 𝕜₂ M] [TopologicalSpace M] [T2Space M]
    {l l' : Completion (E ⊗[𝕜] F) →SL[σ] M}
    (h : ∀ (e : E) (f : F), l ↑(e ⊗ₜ[𝕜] f) = l' ↑(e ⊗ₜ[𝕜] f)) : l = l' := by
  refine DFunLike.coe_injective (Completion.ext l.continuous l'.continuous fun z ↦ ?_)
  induction z using TensorProduct.inductionOn with
  | tmul e f => exact h e f
  | add x y hx hy => simp only [Completion.coe_add, map_add, hx, hy]

/-- Two vectors in `Completion (E ⊗[𝕜] F)` are equal if and only if they have the same inner
product with every pure tensor on the right. -/
theorem completion_ext_iff_inner_right {u v : Completion (E ⊗[𝕜] F)} :
    u = v ↔ ∀ (e : E) (f : F),
      ⟪u, (↑(e ⊗ₜ[𝕜] f) : Completion (E ⊗[𝕜] F))⟫_𝕜 = ⟪v, ↑(e ⊗ₜ[𝕜] f)⟫_𝕜 := by
  refine ⟨fun h _ _ ↦ h ▸ rfl, fun h ↦ ?_⟩
  have hfl : innerSL 𝕜 (E := Completion (E ⊗[𝕜] F)) u = innerSL 𝕜 v :=
    completion_continuousLinearMap_ext fun e f ↦ by simpa only [innerSL_apply_apply] using h e f
  exact innerSL_inj.mp hfl

/-- Two vectors in `Completion (E ⊗[𝕜] F)` are equal if and only if they have the same inner
product with every pure tensor on the left. -/
theorem completion_ext_iff_inner_left {u v : Completion (E ⊗[𝕜] F)} :
    u = v ↔ ∀ (e : E) (f : F),
      ⟪(↑(e ⊗ₜ[𝕜] f) : Completion (E ⊗[𝕜] F)), u⟫_𝕜 = ⟪↑(e ⊗ₜ[𝕜] f), v⟫_𝕜 := by
  refine ⟨fun h _ _ ↦ h ▸ rfl, fun h ↦ completion_ext_iff_inner_right.mpr fun e f ↦ ?_⟩
  rw [← inner_conj_symm u, ← inner_conj_symm v, h e f]

theorem subsingleton_completion_of_subsingleton_left [Subsingleton E] :
    Subsingleton (Completion (E ⊗[𝕜] F)) :=
  ⟨fun u v ↦ Completion.induction_on₂ u v (isClosed_eq continuous_fst continuous_snd)
    fun a b ↦ congrArg _ (Subsingleton.elim a b)⟩

theorem subsingleton_completion_of_subsingleton_right [Subsingleton F] :
    Subsingleton (Completion (E ⊗[𝕜] F)) :=
  ⟨fun u v ↦ Completion.induction_on₂ u v (isClosed_eq continuous_fst continuous_snd)
    fun a b ↦ congrArg _ (Subsingleton.elim a b)⟩

/-- The completed Hilbert tensor product `Completion (E ⊗[𝕜] F)` is nontrivial if and only if both
`E` and `F` are nontrivial. -/
@[simp]
theorem nontrivial_completion_iff :
    Nontrivial (Completion (E ⊗[𝕜] F)) ↔ Nontrivial E ∧ Nontrivial F := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hE, hF⟩ ↦ ?_⟩
  · by_contra hE
    rw [not_nontrivial_iff_subsingleton] at hE
    have := subsingleton_completion_of_subsingleton_left (𝕜 := 𝕜) (E := E) (F := F)
    exact false_of_nontrivial_of_subsingleton (Completion (E ⊗[𝕜] F))
  · by_contra hF
    rw [not_nontrivial_iff_subsingleton] at hF
    have := subsingleton_completion_of_subsingleton_right (𝕜 := 𝕜) (E := E) (F := F)
    exact false_of_nontrivial_of_subsingleton (Completion (E ⊗[𝕜] F))
  · obtain ⟨e, he⟩ := exists_ne (0 : E)
    obtain ⟨f, hf⟩ := exists_ne (0 : F)
    refine ⟨↑(e ⊗ₜ[𝕜] f), 0, fun h ↦ ?_⟩
    have hnorm : ‖(↑(e ⊗ₜ[𝕜] f) : Completion (E ⊗[𝕜] F))‖ = 0 := by simp [h]
    rw [Completion.norm_coe, norm_tmul, mul_eq_zero, norm_eq_zero, norm_eq_zero] at hnorm
    exact hnorm.elim he hf

end Density

/-! ### Completed operator tensor maps `mapLCompletion` -/

section MapLCompletion

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The bounded operator `e ⊗ₜ g ↦ f e ⊗ₜ h g` between completed Hilbert tensor products, defined
by extending `TensorProduct.mapL f h` to the completions. -/
noncomputable def mapLCompletion (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    Completion (E ⊗[𝕜] G) →L[𝕜] Completion (F ⊗[𝕜] H) :=
  (mapL f g).completion

@[simp]
theorem mapLCompletion_coe (f : E →L[𝕜] F) (g : G →L[𝕜] H) (z : E ⊗[𝕜] G) :
    mapLCompletion f g z = ↑(mapL f g z) :=
  ContinuousLinearMap.completion_apply_coe _ z

theorem mapLCompletion_coe_tmul (f : E →L[𝕜] F) (g : G →L[𝕜] H) (e : E) (x : G) :
    mapLCompletion f g ↑(e ⊗ₜ[𝕜] x) = ↑(f e ⊗ₜ[𝕜] g x) :=
  mapLCompletion_coe f g (e ⊗ₜ[𝕜] x)

/-- `mapLCompletion f g` is the unique bounded operator sending `↑(e ⊗ₜ x)` to `↑(f e ⊗ₜ g x)`. -/
theorem eq_mapLCompletion_iff {T : Completion (E ⊗[𝕜] G) →L[𝕜] Completion (F ⊗[𝕜] H)}
    {f : E →L[𝕜] F} {g : G →L[𝕜] H} :
    T = mapLCompletion f g ↔
      ∀ (e : E) (x : G), T ↑(e ⊗ₜ[𝕜] x) = ↑(f e ⊗ₜ[𝕜] g x) :=
  ⟨fun h e x ↦ h ▸ mapLCompletion_coe_tmul f g e x,
    fun h ↦ completion_continuousLinearMap_ext fun e x ↦ by rw [h, mapLCompletion_coe_tmul]⟩

/-- **Norm of a completed operator tensor.** `‖mapLCompletion f g‖ = ‖f‖ * ‖g‖`. -/
@[simp]
theorem norm_mapLCompletion (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    ‖mapLCompletion f g‖ = ‖f‖ * ‖g‖ := by
  rw [mapLCompletion, ContinuousLinearMap.norm_completion, norm_mapL]

@[simp]
theorem mapLCompletion_zero_left (g : G →L[𝕜] H) :
    mapLCompletion (0 : E →L[𝕜] F) g = 0 :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

@[simp]
theorem mapLCompletion_zero_right (f : E →L[𝕜] F) :
    mapLCompletion f (0 : G →L[𝕜] H) = 0 :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

theorem mapLCompletion_add_left (f₁ f₂ : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapLCompletion (f₁ + f₂) g = mapLCompletion f₁ g + mapLCompletion f₂ g :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp [add_tmul, Completion.coe_add]

theorem mapLCompletion_add_right (f : E →L[𝕜] F) (g₁ g₂ : G →L[𝕜] H) :
    mapLCompletion f (g₁ + g₂) = mapLCompletion f g₁ + mapLCompletion f g₂ :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp [tmul_add, Completion.coe_add]

theorem mapLCompletion_sub_left (f₁ f₂ : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapLCompletion (f₁ - f₂) g = mapLCompletion f₁ g - mapLCompletion f₂ g :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp [sub_tmul, Completion.coe_sub]

theorem mapLCompletion_sub_right (f : E →L[𝕜] F) (g₁ g₂ : G →L[𝕜] H) :
    mapLCompletion f (g₁ - g₂) = mapLCompletion f g₁ - mapLCompletion f g₂ :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp [tmul_sub, Completion.coe_sub]

@[simp]
theorem mapLCompletion_neg_left (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapLCompletion (-f) g = -mapLCompletion f g :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp [neg_tmul, Completion.coe_neg]

@[simp]
theorem mapLCompletion_neg_right (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapLCompletion f (-g) = -mapLCompletion f g :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp [tmul_neg, Completion.coe_neg]

theorem mapLCompletion_smul_left (c : 𝕜) (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapLCompletion (c • f) g = c • mapLCompletion f g :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp [smul_tmul', ← Completion.coe_smul]

theorem mapLCompletion_smul_right (c : 𝕜) (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapLCompletion f (c • g) = c • mapLCompletion f g :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp [tmul_smul, ← Completion.coe_smul]

theorem mapLCompletion_comp {A B : Type*} [NormedAddCommGroup A] [InnerProductSpace 𝕜 A]
    [NormedAddCommGroup B] [InnerProductSpace 𝕜 B] (f₁ : E →L[𝕜] F) (f₂ : A →L[𝕜] E)
    (g₁ : G →L[𝕜] H) (g₂ : B →L[𝕜] G) :
    mapLCompletion (f₁ ∘L f₂) (g₁ ∘L g₂) = mapLCompletion f₁ g₁ ∘L mapLCompletion f₂ g₂ :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

end MapLCompletion

section MapLCompletionEndo

variable {𝕜 E G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

@[simp]
theorem mapLCompletion_id_id :
    mapLCompletion (.id 𝕜 E) (.id 𝕜 G) = .id 𝕜 (Completion (E ⊗[𝕜] G)) :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

@[simp]
theorem mapLCompletion_one_one :
    mapLCompletion (1 : E →L[𝕜] E) (1 : G →L[𝕜] G) = 1 :=
  mapLCompletion_id_id

theorem mapLCompletion_mul (x₁ x₂ : E →L[𝕜] E) (y₁ y₂ : G →L[𝕜] G) :
    mapLCompletion (x₁ * x₂) (y₁ * y₂) = mapLCompletion x₁ y₁ * mapLCompletion x₂ y₂ :=
  mapLCompletion_comp x₁ x₂ y₁ y₂

@[simp]
theorem mapLCompletion_pow (x : E →L[𝕜] E) (y : G →L[𝕜] G) (n : ℕ) :
    mapLCompletion x y ^ n = mapLCompletion (x ^ n) (y ^ n) := by
  induction n with
  | zero => simp [pow_zero]
  | succ n ih => rw [pow_succ, pow_succ, pow_succ, ih, mapLCompletion_mul]

end MapLCompletionEndo

end TensorProduct

/-! ### Completed operator amplifications `rTensorCompletion` and `lTensorCompletion` -/

namespace ContinuousLinearMap

open TensorProduct

section Amplifications

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

variable (G) in
/-- The amplification `f ⊗ 1` on completed Hilbert tensor products: the extension by continuity of
`ContinuousLinearMap.rTensor`, sending `↑(e ⊗ₜ x)` to `↑(f e ⊗ₜ x)`. Neither factor is assumed
complete. -/
noncomputable def rTensorCompletion (f : E →L[𝕜] F) :
    Completion (E ⊗[𝕜] G) →L[𝕜] Completion (F ⊗[𝕜] G) :=
  (f.rTensor G).completion

variable (E) in
/-- The amplification `1 ⊗ g` on completed Hilbert tensor products: the extension by continuity of
`ContinuousLinearMap.lTensor`, sending `↑(e ⊗ₜ x)` to `↑(e ⊗ₜ g x)`. Neither factor is assumed
complete. -/
noncomputable def lTensorCompletion (g : F →L[𝕜] G) :
    Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] G) :=
  (g.lTensor E).completion

@[simp]
theorem rTensorCompletion_coe (f : E →L[𝕜] F) (z : E ⊗[𝕜] G) :
    f.rTensorCompletion G z = ↑(f.rTensor G z) :=
  completion_apply_coe _ z

@[simp]
theorem lTensorCompletion_coe (g : F →L[𝕜] G) (z : E ⊗[𝕜] F) :
    g.lTensorCompletion E z = ↑(g.lTensor E z) :=
  completion_apply_coe _ z

theorem rTensorCompletion_coe_tmul (f : E →L[𝕜] F) (e : E) (x : G) :
    f.rTensorCompletion G ↑(e ⊗ₜ[𝕜] x) = ↑(f e ⊗ₜ[𝕜] x) :=
  rTensorCompletion_coe f (e ⊗ₜ[𝕜] x)

theorem lTensorCompletion_coe_tmul (g : F →L[𝕜] G) (e : E) (x : F) :
    g.lTensorCompletion E ↑(e ⊗ₜ[𝕜] x) = ↑(e ⊗ₜ[𝕜] g x) :=
  lTensorCompletion_coe g (e ⊗ₜ[𝕜] x)

theorem rTensorCompletion_eq_mapLCompletion (G : Type*) [NormedAddCommGroup G]
    [InnerProductSpace 𝕜 G] (f : E →L[𝕜] F) :
    f.rTensorCompletion G = mapLCompletion f (.id 𝕜 G) :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

theorem lTensorCompletion_eq_mapLCompletion (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (g : F →L[𝕜] G) :
    g.lTensorCompletion E = mapLCompletion (.id 𝕜 E) g :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

/-- `f.rTensorCompletion G` is the unique bounded operator sending `↑(e ⊗ₜ x)` to `↑(f e ⊗ₜ x)`. -/
theorem eq_rTensorCompletion_iff {T : Completion (E ⊗[𝕜] G) →L[𝕜] Completion (F ⊗[𝕜] G)}
    {f : E →L[𝕜] F} :
    T = f.rTensorCompletion G ↔ ∀ (e : E) (x : G), T ↑(e ⊗ₜ[𝕜] x) = ↑(f e ⊗ₜ[𝕜] x) := by
  rw [rTensorCompletion_eq_mapLCompletion, eq_mapLCompletion_iff]
  simp

/-- `g.lTensorCompletion E` is the unique bounded operator sending `↑(e ⊗ₜ x)` to `↑(e ⊗ₜ g x)`. -/
theorem eq_lTensorCompletion_iff {T : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] G)}
    {g : F →L[𝕜] G} :
    T = g.lTensorCompletion E ↔ ∀ (e : E) (x : F), T ↑(e ⊗ₜ[𝕜] x) = ↑(e ⊗ₜ[𝕜] g x) := by
  rw [lTensorCompletion_eq_mapLCompletion, eq_mapLCompletion_iff]
  simp

@[simp]
theorem rTensorCompletion_comp_lTensorCompletion {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    f.rTensorCompletion H ∘L g.lTensorCompletion E = mapLCompletion f g :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

@[simp]
theorem lTensorCompletion_comp_rTensorCompletion {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 H] (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    g.lTensorCompletion F ∘L f.rTensorCompletion G = mapLCompletion f g :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

@[simp]
theorem rTensorCompletion_zero :
    (0 : E →L[𝕜] F).rTensorCompletion G = 0 :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

@[simp]
theorem rTensorCompletion_add (f₁ f₂ : E →L[𝕜] F) :
    (f₁ + f₂).rTensorCompletion G = f₁.rTensorCompletion G + f₂.rTensorCompletion G := by
  simp only [rTensorCompletion_eq_mapLCompletion, mapLCompletion_add_left]

@[simp]
theorem rTensorCompletion_sub (f₁ f₂ : E →L[𝕜] F) :
    (f₁ - f₂).rTensorCompletion G = f₁.rTensorCompletion G - f₂.rTensorCompletion G := by
  simp only [rTensorCompletion_eq_mapLCompletion, mapLCompletion_sub_left]

@[simp]
theorem rTensorCompletion_neg (f : E →L[𝕜] F) :
    (-f).rTensorCompletion G = -f.rTensorCompletion G := by
  simp only [rTensorCompletion_eq_mapLCompletion, mapLCompletion_neg_left]

@[simp]
theorem rTensorCompletion_smul (c : 𝕜) (f : E →L[𝕜] F) :
    (c • f).rTensorCompletion G = c • f.rTensorCompletion G := by
  simp only [rTensorCompletion_eq_mapLCompletion, mapLCompletion_smul_left]

theorem rTensorCompletion_comp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (f₁ : F →L[𝕜] H) (f₂ : E →L[𝕜] F) :
    (f₁ ∘L f₂).rTensorCompletion G = f₁.rTensorCompletion G ∘L f₂.rTensorCompletion G :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

@[simp]
theorem lTensorCompletion_zero :
    (0 : F →L[𝕜] G).lTensorCompletion E = 0 :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

@[simp]
theorem lTensorCompletion_add (g₁ g₂ : F →L[𝕜] G) :
    (g₁ + g₂).lTensorCompletion E = g₁.lTensorCompletion E + g₂.lTensorCompletion E := by
  simp only [lTensorCompletion_eq_mapLCompletion, mapLCompletion_add_right]

@[simp]
theorem lTensorCompletion_sub (g₁ g₂ : F →L[𝕜] G) :
    (g₁ - g₂).lTensorCompletion E = g₁.lTensorCompletion E - g₂.lTensorCompletion E := by
  simp only [lTensorCompletion_eq_mapLCompletion, mapLCompletion_sub_right]

@[simp]
theorem lTensorCompletion_neg (g : F →L[𝕜] G) :
    (-g).lTensorCompletion E = -g.lTensorCompletion E := by
  simp only [lTensorCompletion_eq_mapLCompletion, mapLCompletion_neg_right]

@[simp]
theorem lTensorCompletion_smul (c : 𝕜) (g : F →L[𝕜] G) :
    (c • g).lTensorCompletion E = c • g.lTensorCompletion E := by
  simp only [lTensorCompletion_eq_mapLCompletion, mapLCompletion_smul_right]

theorem lTensorCompletion_comp {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (g₁ : G →L[𝕜] H) (g₂ : F →L[𝕜] G) :
    (g₁ ∘L g₂).lTensorCompletion E = g₁.lTensorCompletion E ∘L g₂.lTensorCompletion E :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

theorem norm_rTensorCompletion_le (f : E →L[𝕜] F) : ‖f.rTensorCompletion G‖ ≤ ‖f‖ := by
  rw [rTensorCompletion, norm_completion]
  exact f.norm_rTensor_le G

@[simp]
theorem norm_rTensorCompletion [Nontrivial G] (f : E →L[𝕜] F) : ‖f.rTensorCompletion G‖ = ‖f‖ := by
  rw [rTensorCompletion, norm_completion, norm_rTensor]

@[simp]
theorem rTensorCompletion_eq_zero_of_subsingleton [Subsingleton G] (f : E →L[𝕜] F) :
    f.rTensorCompletion G = 0 := by
  have := subsingleton_completion_of_subsingleton_right (𝕜 := 𝕜) (E := F) (F := G)
  exact Subsingleton.elim _ _

theorem isometry_rTensorCompletion (G : Type*) [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [Nontrivial G] :
    Isometry (rTensorCompletion G : (E →L[𝕜] F) →
      Completion (E ⊗[𝕜] G) →L[𝕜] Completion (F ⊗[𝕜] G)) := by
  rw [isometry_iff_dist_eq]
  intro f₁ f₂
  rw [dist_eq_norm, dist_eq_norm, ← rTensorCompletion_sub, norm_rTensorCompletion]

theorem rTensorCompletion_injective (G : Type*) [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [Nontrivial G] :
    Function.Injective (rTensorCompletion G : (E →L[𝕜] F) →
      Completion (E ⊗[𝕜] G) →L[𝕜] Completion (F ⊗[𝕜] G)) :=
  (isometry_rTensorCompletion G).injective

theorem norm_lTensorCompletion_le (g : F →L[𝕜] G) : ‖g.lTensorCompletion E‖ ≤ ‖g‖ := by
  rw [lTensorCompletion, norm_completion]
  exact g.norm_lTensor_le E

@[simp]
theorem norm_lTensorCompletion [Nontrivial E] (g : F →L[𝕜] G) : ‖g.lTensorCompletion E‖ = ‖g‖ := by
  rw [lTensorCompletion, norm_completion, norm_lTensor]

@[simp]
theorem lTensorCompletion_eq_zero_of_subsingleton [Subsingleton E] (g : F →L[𝕜] G) :
    g.lTensorCompletion E = 0 := by
  have := subsingleton_completion_of_subsingleton_left (𝕜 := 𝕜) (E := E) (F := G)
  exact Subsingleton.elim _ _

theorem isometry_lTensorCompletion (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [Nontrivial E] :
    Isometry (lTensorCompletion E : (F →L[𝕜] G) →
      Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] G)) := by
  rw [isometry_iff_dist_eq]
  intro g₁ g₂
  rw [dist_eq_norm, dist_eq_norm, ← lTensorCompletion_sub, norm_lTensorCompletion]

theorem lTensorCompletion_injective (E : Type*) [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [Nontrivial E] :
    Function.Injective (lTensorCompletion E : (F →L[𝕜] G) →
      Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] G)) :=
  (isometry_lTensorCompletion E).injective

/-- The adjoint of `f ⊗ 1` on `Completion (E ⊗[𝕜] G)` is `f† ⊗ 1`. Only `E` and `F` need be
complete, since the completed tensor products are complete automatically. -/
@[simp]
theorem adjoint_rTensorCompletion [CompleteSpace E] [CompleteSpace F] (f : E →L[𝕜] F) :
    (f.rTensorCompletion G)† = (f†).rTensorCompletion G := by
  refine ((eq_adjoint_iff _ _).2 fun u v ↦ ?_).symm
  induction u, v using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u v =>
    induction u using TensorProduct.inductionOn with
    | tmul e₁ g₁ =>
      induction v using TensorProduct.inductionOn with
      | tmul e₂ g₂ => simp [adjoint_inner_left]
      | add _ _ h₁ h₂ => simp only [Completion.coe_add, map_add, inner_add_right, h₁, h₂]
    | add _ _ h₁ h₂ => simp only [Completion.coe_add, map_add, inner_add_left, h₁, h₂]

/-- The adjoint of `1 ⊗ g` on `Completion (E ⊗[𝕜] F)` is `1 ⊗ g†`. Only `F` and `G` need be
complete. -/
@[simp]
theorem adjoint_lTensorCompletion [CompleteSpace F] [CompleteSpace G] (g : F →L[𝕜] G) :
    (g.lTensorCompletion E)† = (g†).lTensorCompletion E := by
  refine ((eq_adjoint_iff _ _).2 fun u v ↦ ?_).symm
  induction u, v using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u v =>
    induction u using TensorProduct.inductionOn with
    | tmul e₁ g₁ =>
      induction v using TensorProduct.inductionOn with
      | tmul e₂ g₂ => simp [adjoint_inner_left]
      | add _ _ h₁ h₂ => simp only [Completion.coe_add, map_add, inner_add_right, h₁, h₂]
    | add _ _ h₁ h₂ => simp only [Completion.coe_add, map_add, inner_add_left, h₁, h₂]

end Amplifications

section Endomorphisms

variable {𝕜 E G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

theorem rTensorCompletion_mul_lTensorCompletion (x : E →L[𝕜] E) (y : G →L[𝕜] G) :
    x.rTensorCompletion G * y.lTensorCompletion E = mapLCompletion x y :=
  rTensorCompletion_comp_lTensorCompletion x y

theorem lTensorCompletion_mul_rTensorCompletion (x : E →L[𝕜] E) (y : G →L[𝕜] G) :
    y.lTensorCompletion E * x.rTensorCompletion G = mapLCompletion x y :=
  lTensorCompletion_comp_rTensorCompletion x y

/-- `x ⊗ 1` and `1 ⊗ y` commute on `Completion (E ⊗[𝕜] G)`. -/
theorem commute_rTensorCompletion_lTensorCompletion (x : E →L[𝕜] E) (y : G →L[𝕜] G) :
    Commute (x.rTensorCompletion G) (y.lTensorCompletion E) := by
  rw [Commute, SemiconjBy, rTensorCompletion_mul_lTensorCompletion,
    lTensorCompletion_mul_rTensorCompletion]

@[simp]
theorem rTensorCompletion_id :
    (ContinuousLinearMap.id 𝕜 E).rTensorCompletion G = .id 𝕜 (Completion (E ⊗[𝕜] G)) :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

@[simp]
theorem rTensorCompletion_one :
    (1 : E →L[𝕜] E).rTensorCompletion G = 1 :=
  rTensorCompletion_id

theorem rTensorCompletion_mul (x₁ x₂ : E →L[𝕜] E) :
    (x₁ * x₂).rTensorCompletion G = x₁.rTensorCompletion G * x₂.rTensorCompletion G :=
  rTensorCompletion_comp x₁ x₂

@[simp]
theorem rTensorCompletion_pow (x : E →L[𝕜] E) (n : ℕ) :
    (x ^ n).rTensorCompletion G = x.rTensorCompletion G ^ n := by
  simp only [rTensorCompletion_eq_mapLCompletion, mapLCompletion_pow, one_def.symm, one_pow]

@[simp]
theorem lTensorCompletion_id :
    (ContinuousLinearMap.id 𝕜 G).lTensorCompletion E = .id 𝕜 (Completion (E ⊗[𝕜] G)) :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

@[simp]
theorem lTensorCompletion_one :
    (1 : G →L[𝕜] G).lTensorCompletion E = 1 :=
  lTensorCompletion_id

theorem lTensorCompletion_mul (y₁ y₂ : G →L[𝕜] G) :
    (y₁ * y₂).lTensorCompletion E = y₁.lTensorCompletion E * y₂.lTensorCompletion E :=
  lTensorCompletion_comp y₁ y₂

@[simp]
theorem lTensorCompletion_pow (y : G →L[𝕜] G) (n : ℕ) :
    (y ^ n).lTensorCompletion E = y.lTensorCompletion E ^ n := by
  simp only [lTensorCompletion_eq_mapLCompletion, mapLCompletion_pow, one_def.symm, one_pow]

@[simp]
theorem star_rTensorCompletion [CompleteSpace E] (x : E →L[𝕜] E) :
    star (x.rTensorCompletion G) = (star x).rTensorCompletion G := by
  simp only [star_eq_adjoint, adjoint_rTensorCompletion]

@[simp]
theorem star_lTensorCompletion [CompleteSpace G] (y : G →L[𝕜] G) :
    star (y.lTensorCompletion E) = (star y).lTensorCompletion E := by
  simp only [star_eq_adjoint, adjoint_lTensorCompletion]

variable (𝕜 E G) in
/-- Amplification `x ↦ x ⊗ 1` on `Completion (E ⊗[𝕜] G)` as a unital star algebra homomorphism.
No completeness assumption on `G` is required. -/
noncomputable def rTensorCompletionStarAlgHom [CompleteSpace E] :
    (E →L[𝕜] E) →⋆ₐ[𝕜] (Completion (E ⊗[𝕜] G) →L[𝕜] Completion (E ⊗[𝕜] G)) where
  toFun := rTensorCompletion G
  map_one' := rTensorCompletion_one
  map_mul' := rTensorCompletion_mul
  map_zero' := rTensorCompletion_zero
  map_add' := rTensorCompletion_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, rTensorCompletion_smul,
      rTensorCompletion_one]
  map_star' x := (star_rTensorCompletion x).symm

@[simp]
theorem rTensorCompletionStarAlgHom_apply [CompleteSpace E] (x : E →L[𝕜] E) :
    rTensorCompletionStarAlgHom 𝕜 E G x = x.rTensorCompletion G :=
  (rfl)

variable (𝕜 E G) in
/-- Amplification `y ↦ 1 ⊗ y` on `Completion (E ⊗[𝕜] G)` as a unital star algebra homomorphism.
No completeness assumption on `E` is required. -/
noncomputable def lTensorCompletionStarAlgHom [CompleteSpace G] :
    (G →L[𝕜] G) →⋆ₐ[𝕜] (Completion (E ⊗[𝕜] G) →L[𝕜] Completion (E ⊗[𝕜] G)) where
  toFun := lTensorCompletion E
  map_one' := lTensorCompletion_one
  map_mul' := lTensorCompletion_mul
  map_zero' := lTensorCompletion_zero
  map_add' := lTensorCompletion_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, lTensorCompletion_smul,
      lTensorCompletion_one]
  map_star' y := (star_lTensorCompletion y).symm

@[simp]
theorem lTensorCompletionStarAlgHom_apply [CompleteSpace G] (y : G →L[𝕜] G) :
    lTensorCompletionStarAlgHom 𝕜 E G y = y.lTensorCompletion E :=
  (rfl)

end Endomorphisms

end ContinuousLinearMap

namespace TensorProduct

open ContinuousLinearMap

section AdjointAndMixedComp

variable {𝕜 E F G H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Adjoint of a completed operator tensor.** `(mapLCompletion f g)† = mapLCompletion f† g†` for
bounded operators between complete Hilbert spaces. -/
@[simp]
theorem adjoint_mapLCompletion [CompleteSpace E] [CompleteSpace F]
    [CompleteSpace G] [CompleteSpace H] (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    (mapLCompletion f g)† = mapLCompletion (f†) (g†) := by
  rw [← rTensorCompletion_comp_lTensorCompletion, adjoint_comp, adjoint_lTensorCompletion,
    adjoint_rTensorCompletion, lTensorCompletion_comp_rTensorCompletion]

@[simp]
theorem mapLCompletion_comp_rTensorCompletion {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace 𝕜 A] (f₁ : E →L[𝕜] F) (f₂ : A →L[𝕜] E) (g : G →L[𝕜] H) :
    mapLCompletion f₁ g ∘L f₂.rTensorCompletion G = mapLCompletion (f₁ ∘L f₂) g :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

@[simp]
theorem mapLCompletion_comp_lTensorCompletion {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace 𝕜 A] (f : E →L[𝕜] F) (g₁ : G →L[𝕜] H) (g₂ : A →L[𝕜] G) :
    mapLCompletion f g₁ ∘L g₂.lTensorCompletion E = mapLCompletion f (g₁ ∘L g₂) :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

@[simp]
theorem rTensorCompletion_comp_mapLCompletion {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace 𝕜 A] (f₁ : E →L[𝕜] F) (f₂ : A →L[𝕜] E) (g : G →L[𝕜] H) :
    f₁.rTensorCompletion H ∘L mapLCompletion f₂ g = mapLCompletion (f₁ ∘L f₂) g :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

@[simp]
theorem lTensorCompletion_comp_mapLCompletion {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace 𝕜 A] (f : E →L[𝕜] F) (g₁ : G →L[𝕜] H) (g₂ : A →L[𝕜] G) :
    g₁.lTensorCompletion F ∘L mapLCompletion f g₂ = mapLCompletion f (g₁ ∘L g₂) :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

end AdjointAndMixedComp

@[simp]
theorem star_mapLCompletion {𝕜 E G : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] [CompleteSpace G]
    (x : E →L[𝕜] E) (y : G →L[𝕜] G) :
    star (mapLCompletion x y) = mapLCompletion (star x) (star y) := by
  simp only [star_eq_adjoint, adjoint_mapLCompletion]

/-! ### Completed symmetry, factor completions, associativity and scalar-unit unitaries -/

section Symmetry

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

theorem commIsometry_completion_coe_tmul (e : E) (f : F) :
    (commIsometry 𝕜 E F).completion ↑(e ⊗ₜ[𝕜] f) = ↑(f ⊗ₜ[𝕜] e) :=
  LinearIsometryEquiv.completion_apply_coe _ (e ⊗ₜ[𝕜] f)

/-- `(commIsometry 𝕜 E F).completion` is the unique bounded operator sending `↑(e ⊗ₜ f)` to
`↑(f ⊗ₜ e)`. -/
theorem eq_commIsometry_completion_iff
    {T : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (F ⊗[𝕜] E)} :
    T = ((commIsometry 𝕜 E F).completion :
      Completion (E ⊗[𝕜] F) →L[𝕜] Completion (F ⊗[𝕜] E)) ↔
      ∀ (e : E) (f : F), T ↑(e ⊗ₜ[𝕜] f) = ↑(f ⊗ₜ[𝕜] e) :=
  ⟨fun h e f ↦ by simp [h],
    fun h ↦ completion_continuousLinearMap_ext fun e f ↦ by simp [h]⟩

theorem mapLCompletion_comp_commIsometry_completion {G H : Type*}
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (f : E →L[𝕜] F) (g : G →L[𝕜] H) :
    mapLCompletion f g ∘L ((commIsometry 𝕜 G E).completion :
        Completion (G ⊗[𝕜] E) →L[𝕜] Completion (E ⊗[𝕜] G)) =
      ((commIsometry 𝕜 H F).completion :
        Completion (H ⊗[𝕜] F) →L[𝕜] Completion (F ⊗[𝕜] H)) ∘L mapLCompletion g f :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

theorem commIsometry_completion_comp_rTensorCompletion_comp_commIsometry_completion
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] (g : F →L[𝕜] G) :
    ((commIsometry 𝕜 G E).completion :
        Completion (G ⊗[𝕜] E) →L[𝕜] Completion (E ⊗[𝕜] G)) ∘L g.rTensorCompletion E ∘L
        ((commIsometry 𝕜 E F).completion :
          Completion (E ⊗[𝕜] F) →L[𝕜] Completion (F ⊗[𝕜] E)) =
      g.lTensorCompletion E :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

theorem commIsometry_completion_comp_lTensorCompletion_comp_commIsometry_completion
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] (f : E →L[𝕜] F) :
    ((commIsometry 𝕜 G F).completion :
        Completion (G ⊗[𝕜] F) →L[𝕜] Completion (F ⊗[𝕜] G)) ∘L f.lTensorCompletion G ∘L
        ((commIsometry 𝕜 E G).completion :
          Completion (E ⊗[𝕜] G) →L[𝕜] Completion (G ⊗[𝕜] E)) =
      f.rTensorCompletion G :=
  completion_continuousLinearMap_ext fun _ _ ↦ by simp

private theorem completionLeft_surjective :
    Function.Surjective
      (((Completion.toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).rTensor F).completion) := by
  let i := ((Completion.toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).rTensor F).completion
  rw [← Set.range_eq_univ, ← i.isometry.isUniformInducing.isComplete_range.isClosed.closure_eq]
  refine Set.eq_univ_of_subset ?_ dense_span_coe_tmul.closure_eq
  have hsub : {u : Completion (Completion E ⊗[𝕜] F) |
      ∃ (x : Completion E) (f : F), (↑(x ⊗ₜ[𝕜] f) : Completion (Completion E ⊗[𝕜] F)) = u} ⊆
      (i.toLinearMap.range.topologicalClosure : Set _) := by
    rintro _ ⟨x, f, rfl⟩
    refine Completion.induction_on x
      ((Submodule.isClosed_topologicalClosure _).preimage
        ((mkLCompletion 𝕜 (Completion E) F).flip f).continuous)
      fun e ↦ Submodule.le_topologicalClosure _ ⟨↑(e ⊗ₜ[𝕜] f), ?_⟩
    simp [i, LinearIsometry.completion_apply_coe]
  simpa only [Submodule.topologicalClosure_coe, LinearMap.coe_range,
    LinearIsometry.coe_toLinearMap] using
    (Submodule.isClosed_topologicalClosure i.toLinearMap.range).closure_subset_iff.mpr
      (Submodule.span_le.mpr hsub)

variable (𝕜 E F) in
/-- Completing the left factor before taking the completed Hilbert tensor product produces a
canonically isometric Hilbert space: `Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] Completion (Completion E ⊗[𝕜] F)`
sending `↑(e ⊗ₜ f)` to `↑(↑e ⊗ₜ f)`. -/
noncomputable def completionLeftEquiv :
    Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] Completion (Completion E ⊗[𝕜] F) :=
  LinearIsometryEquiv.ofSurjective
    (((Completion.toComplₗᵢ : E →ₗᵢ[𝕜] Completion E).rTensor F).completion)
    completionLeft_surjective

@[simp]
theorem completionLeftEquiv_coe_tmul (e : E) (f : F) :
    completionLeftEquiv 𝕜 E F ↑(e ⊗ₜ[𝕜] f) = ↑((e : Completion E) ⊗ₜ[𝕜] f) := by
  simp [completionLeftEquiv, LinearIsometry.completion_apply_coe]

@[simp]
theorem completionLeftEquiv_symm_coe_tmul (e : E) (f : F) :
    (completionLeftEquiv 𝕜 E F).symm ↑((e : Completion E) ⊗ₜ[𝕜] f) = ↑(e ⊗ₜ[𝕜] f) :=
  (completionLeftEquiv 𝕜 E F).symm_apply_eq.2 (completionLeftEquiv_coe_tmul e f).symm

variable (𝕜 E F) in
/-- Completing the right factor before taking the completed Hilbert tensor product produces a
canonically isometric Hilbert space: `Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] Completion (E ⊗[𝕜] Completion F)`
sending `↑(e ⊗ₜ f)` to `↑(e ⊗ₜ ↑f)`. -/
noncomputable def completionRightEquiv :
    Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] Completion (E ⊗[𝕜] Completion F) :=
  ((commIsometry 𝕜 E F).completion).trans
    ((completionLeftEquiv 𝕜 F E).trans ((commIsometry 𝕜 (Completion F) E).completion))

@[simp]
theorem completionRightEquiv_coe_tmul (e : E) (f : F) :
    completionRightEquiv 𝕜 E F ↑(e ⊗ₜ[𝕜] f) = ↑(e ⊗ₜ[𝕜] (f : Completion F)) := by
  simp [completionRightEquiv]

@[simp]
theorem completionRightEquiv_symm_coe_tmul (e : E) (f : F) :
    (completionRightEquiv 𝕜 E F).symm ↑(e ⊗ₜ[𝕜] (f : Completion F)) = ↑(e ⊗ₜ[𝕜] f) :=
  (completionRightEquiv 𝕜 E F).symm_apply_eq.2 (completionRightEquiv_coe_tmul e f).symm

end Symmetry

section Associativity

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

theorem assocIsometry_completion_coe_tmul (e : E) (f : F) (g : G) :
    (assocIsometry 𝕜 E F G).completion ↑((e ⊗ₜ[𝕜] f) ⊗ₜ[𝕜] g) = ↑(e ⊗ₜ[𝕜] (f ⊗ₜ[𝕜] g)) :=
  LinearIsometryEquiv.completion_apply_coe _ ((e ⊗ₜ[𝕜] f) ⊗ₜ[𝕜] g)

/-- `(assocIsometry 𝕜 E F G).completion` is the unique bounded operator sending
`↑((e ⊗ₜ f) ⊗ₜ g)` to `↑(e ⊗ₜ (f ⊗ₜ g))`. -/
theorem eq_assocIsometry_completion_iff
    {T : Completion ((E ⊗[𝕜] F) ⊗[𝕜] G) →L[𝕜] Completion (E ⊗[𝕜] (F ⊗[𝕜] G))} :
    T = ((assocIsometry 𝕜 E F G).completion :
      Completion ((E ⊗[𝕜] F) ⊗[𝕜] G) →L[𝕜] Completion (E ⊗[𝕜] (F ⊗[𝕜] G))) ↔
      ∀ (e : E) (f : F) (g : G), T ↑((e ⊗ₜ[𝕜] f) ⊗ₜ[𝕜] g) = ↑(e ⊗ₜ[𝕜] (f ⊗ₜ[𝕜] g)) := by
  refine ⟨fun h e f g ↦ by simp [h], fun h ↦ ?_⟩
  refine completion_continuousLinearMap_ext fun u g ↦ ?_
  induction u using TensorProduct.inductionOn with
  | tmul e f => simp [h]
  | add x y hx hy => simp only [add_tmul, Completion.coe_add, map_add, hx, hy]

/-- A continuous semilinear map out of `Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G)` into a Hausdorff
space is determined by its values on threefold pure tensors `↑(↑(e ⊗ₜ f) ⊗ₜ g)`. -/
theorem completion_threefold_left_continuousLinearMap_ext {𝕜₂ M : Type*} [Semiring 𝕜₂]
    {σ : 𝕜 →+* 𝕜₂} [AddCommGroup M] [Module 𝕜₂ M] [TopologicalSpace M] [T2Space M]
    {l l' : Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) →SL[σ] M}
    (h : ∀ (e : E) (f : F) (g : G),
      l ↑((↑(e ⊗ₜ[𝕜] f) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] g) =
        l' ↑((↑(e ⊗ₜ[𝕜] f) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] g)) : l = l' := by
  refine completion_continuousLinearMap_ext fun u g ↦ ?_
  refine Completion.induction_on u
    (isClosed_eq (l.continuous.comp ((mkLCompletion 𝕜 _ G).flip g).continuous)
      (l'.continuous.comp ((mkLCompletion 𝕜 _ G).flip g).continuous))
    fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul e f => exact h e f g
  | add x y hx hy => simp only [Completion.coe_add, add_tmul, map_add, hx, hy]

/-- A continuous semilinear map out of `Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G))` into a Hausdorff
space is determined by its values on threefold pure tensors `↑(e ⊗ₜ ↑(f ⊗ₜ g))`. -/
theorem completion_threefold_right_continuousLinearMap_ext {𝕜₂ M : Type*} [Semiring 𝕜₂]
    {σ : 𝕜 →+* 𝕜₂} [AddCommGroup M] [Module 𝕜₂ M] [TopologicalSpace M] [T2Space M]
    {l l' : Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G)) →SL[σ] M}
    (h : ∀ (e : E) (f : F) (g : G),
      l ↑(e ⊗ₜ[𝕜] (↑(f ⊗ₜ[𝕜] g) : Completion (F ⊗[𝕜] G))) =
        l' ↑(e ⊗ₜ[𝕜] (↑(f ⊗ₜ[𝕜] g) : Completion (F ⊗[𝕜] G)))) : l = l' := by
  refine completion_continuousLinearMap_ext fun e u ↦ ?_
  refine Completion.induction_on u
    (isClosed_eq (l.continuous.comp (mkLCompletion 𝕜 E _ e).continuous)
      (l'.continuous.comp (mkLCompletion 𝕜 E _ e).continuous))
    fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul f g => exact h e f g
  | add x y hx hy => simp only [Completion.coe_add, tmul_add, map_add, hx, hy]

variable (𝕜 E F G) in
/-- **Associativity of completed Hilbert tensor products.** The canonical linear isometric
equivalence `(E ⊗̂ F) ⊗̂ G ≃ₗᵢ[𝕜] E ⊗̂ (F ⊗̂ G)` sending `↑(↑(e ⊗ₜ f) ⊗ₜ g)` to
`↑(e ⊗ₜ ↑(f ⊗ₜ g))`. -/
noncomputable def assocCompletion :
    Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) ≃ₗᵢ[𝕜]
      Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G)) :=
  (completionLeftEquiv 𝕜 (E ⊗[𝕜] F) G).symm.trans
    (((assocIsometry 𝕜 E F G).completion).trans (completionRightEquiv 𝕜 E (F ⊗[𝕜] G)))

@[simp]
theorem assocCompletion_coe_tmul (e : E) (f : F) (g : G) :
    assocCompletion 𝕜 E F G ↑((↑(e ⊗ₜ[𝕜] f) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] g) =
      ↑(e ⊗ₜ[𝕜] (↑(f ⊗ₜ[𝕜] g) : Completion (F ⊗[𝕜] G))) := by
  simp [assocCompletion]

@[simp]
theorem assocCompletion_symm_coe_tmul (e : E) (f : F) (g : G) :
    (assocCompletion 𝕜 E F G).symm ↑(e ⊗ₜ[𝕜] (↑(f ⊗ₜ[𝕜] g) : Completion (F ⊗[𝕜] G))) =
      ↑((↑(e ⊗ₜ[𝕜] f) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] g) :=
  (assocCompletion 𝕜 E F G).symm_apply_eq.2 (assocCompletion_coe_tmul e f g).symm

/-- `assocCompletion 𝕜 E F G` is the unique bounded operator sending `↑(↑(e ⊗ₜ f) ⊗ₜ g)` to
`↑(e ⊗ₜ ↑(f ⊗ₜ g))`. -/
theorem eq_assocCompletion_iff
    {T : Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) →L[𝕜]
      Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G))} :
    T = (assocCompletion 𝕜 E F G :
      Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) →L[𝕜]
        Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G))) ↔
      ∀ (e : E) (f : F) (g : G),
        T ↑((↑(e ⊗ₜ[𝕜] f) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] g) =
          ↑(e ⊗ₜ[𝕜] (↑(f ⊗ₜ[𝕜] g) : Completion (F ⊗[𝕜] G))) :=
  ⟨fun h e f g ↦ by simp [h],
    fun h ↦ completion_threefold_left_continuousLinearMap_ext fun e f g ↦ by simp [h]⟩

/-- `assocCompletion` intertwines `(f ⊗ 1) ⊗ 1` with `f ⊗ 1`. -/
theorem assocCompletion_comp_rTensorCompletion_rTensorCompletion
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] (f : E →L[𝕜] E') :
    (assocCompletion 𝕜 E' F G :
        Completion (Completion (E' ⊗[𝕜] F) ⊗[𝕜] G) →L[𝕜]
          Completion (E' ⊗[𝕜] Completion (F ⊗[𝕜] G))) ∘L
        (f.rTensorCompletion F).rTensorCompletion G =
      f.rTensorCompletion (Completion (F ⊗[𝕜] G)) ∘L
        (assocCompletion 𝕜 E F G :
          Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) →L[𝕜]
            Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G))) :=
  completion_threefold_left_continuousLinearMap_ext fun _ _ _ ↦ by simp

/-- `assocCompletion` intertwines `(1 ⊗ g) ⊗ 1` with `1 ⊗ (g ⊗ 1)`. -/
theorem assocCompletion_comp_lTensorCompletion_rTensorCompletion
    {F' : Type*} [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] (g : F →L[𝕜] F') :
    (assocCompletion 𝕜 E F' G :
        Completion (Completion (E ⊗[𝕜] F') ⊗[𝕜] G) →L[𝕜]
          Completion (E ⊗[𝕜] Completion (F' ⊗[𝕜] G))) ∘L
        (g.lTensorCompletion E).rTensorCompletion G =
      (g.rTensorCompletion G).lTensorCompletion E ∘L
        (assocCompletion 𝕜 E F G :
          Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) →L[𝕜]
            Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G))) :=
  completion_threefold_left_continuousLinearMap_ext fun _ _ _ ↦ by simp

/-- `assocCompletion` intertwines `1 ⊗ h` with `1 ⊗ (1 ⊗ h)`. -/
theorem assocCompletion_comp_lTensorCompletion
    {G' : Type*} [NormedAddCommGroup G'] [InnerProductSpace 𝕜 G'] (h : G →L[𝕜] G') :
    (assocCompletion 𝕜 E F G' :
        Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G') →L[𝕜]
          Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G'))) ∘L
        h.lTensorCompletion (Completion (E ⊗[𝕜] F)) =
      (h.lTensorCompletion F).lTensorCompletion E ∘L
        (assocCompletion 𝕜 E F G :
          Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) →L[𝕜]
            Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G))) :=
  completion_threefold_left_continuousLinearMap_ext fun _ _ _ ↦ by simp

/-- `assocCompletion` intertwines `(f ⊗ g) ⊗ h` with `f ⊗ (g ⊗ h)`. -/
theorem assocCompletion_comp_mapLCompletion
    {E' F' G' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
    [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']
    [NormedAddCommGroup G'] [InnerProductSpace 𝕜 G']
    (f : E →L[𝕜] E') (g : F →L[𝕜] F') (h : G →L[𝕜] G') :
    (assocCompletion 𝕜 E' F' G' :
        Completion (Completion (E' ⊗[𝕜] F') ⊗[𝕜] G') →L[𝕜]
          Completion (E' ⊗[𝕜] Completion (F' ⊗[𝕜] G'))) ∘L
        mapLCompletion (mapLCompletion f g) h =
      mapLCompletion f (mapLCompletion g h) ∘L
        (assocCompletion 𝕜 E F G :
          Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) →L[𝕜]
            Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G))) :=
  completion_threefold_left_continuousLinearMap_ext fun _ _ _ ↦ by simp

end Associativity

section ScalarUnit

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

variable (𝕜 E) in
/-- Left scalar-unit unitary `Completion (𝕜 ⊗[𝕜] E) ≃ₗᵢ[𝕜] E` for a complete inner product space
`E`, sending `↑(c ⊗ₜ e)` to `c • e`. -/
noncomputable def lidCompletion : Completion (𝕜 ⊗[𝕜] E) ≃ₗᵢ[𝕜] E :=
  LinearIsometryEquiv.ofSurjective (lidIsometry 𝕜 E).toLinearIsometry.fromCompletion fun e ↦
    ⟨↑((1 : 𝕜) ⊗ₜ[𝕜] e), by simp [LinearIsometry.fromCompletion_apply_coe]⟩

@[simp]
theorem lidCompletion_coe (z : 𝕜 ⊗[𝕜] E) :
    lidCompletion 𝕜 E z = TensorProduct.lid 𝕜 E z :=
  LinearIsometry.fromCompletion_apply_coe _ z

theorem lidCompletion_coe_tmul (c : 𝕜) (e : E) :
    lidCompletion 𝕜 E ↑(c ⊗ₜ[𝕜] e) = c • e := by
  simp

@[simp]
theorem lidCompletion_symm_apply (e : E) :
    (lidCompletion 𝕜 E).symm e = ↑((1 : 𝕜) ⊗ₜ[𝕜] e) :=
  (lidCompletion 𝕜 E).symm_apply_eq.2 <| by simp

theorem lidCompletion_comp_lTensorCompletion (f : E →L[𝕜] F) :
    (lidCompletion 𝕜 F : Completion (𝕜 ⊗[𝕜] F) →L[𝕜] F) ∘L f.lTensorCompletion 𝕜 ∘L
        ((lidCompletion 𝕜 E).symm : E →L[𝕜] Completion (𝕜 ⊗[𝕜] E)) = f := by
  ext e
  simp

variable (𝕜 E) in
/-- Right scalar-unit unitary `Completion (E ⊗[𝕜] 𝕜) ≃ₗᵢ[𝕜] E` for a complete inner product space
`E`, sending `↑(e ⊗ₜ c)` to `c • e`. -/
noncomputable def ridCompletion : Completion (E ⊗[𝕜] 𝕜) ≃ₗᵢ[𝕜] E :=
  LinearIsometryEquiv.ofSurjective (ridIsometry 𝕜 E).toLinearIsometry.fromCompletion fun e ↦
    ⟨↑(e ⊗ₜ[𝕜] (1 : 𝕜)), by simp [LinearIsometry.fromCompletion_apply_coe]⟩

@[simp]
theorem ridCompletion_coe (z : E ⊗[𝕜] 𝕜) :
    ridCompletion 𝕜 E z = TensorProduct.rid 𝕜 E z :=
  LinearIsometry.fromCompletion_apply_coe _ z

theorem ridCompletion_coe_tmul (e : E) (c : 𝕜) :
    ridCompletion 𝕜 E ↑(e ⊗ₜ[𝕜] c) = c • e := by
  simp

@[simp]
theorem ridCompletion_symm_apply (e : E) :
    (ridCompletion 𝕜 E).symm e = ↑(e ⊗ₜ[𝕜] (1 : 𝕜)) :=
  (ridCompletion 𝕜 E).symm_apply_eq.2 <| by simp

/-- Conjugating `f ⊗ 1` on `Completion (E ⊗[𝕜] 𝕜)` by `ridCompletion` recovers `f`. -/
theorem ridCompletion_comp_rTensorCompletion (f : E →L[𝕜] F) :
    (ridCompletion 𝕜 F : Completion (F ⊗[𝕜] 𝕜) →L[𝕜] F) ∘L f.rTensorCompletion 𝕜 ∘L
        ((ridCompletion 𝕜 E).symm : E →L[𝕜] Completion (E ⊗[𝕜] 𝕜)) = f := by
  ext e
  simp

end ScalarUnit

end TensorProduct
