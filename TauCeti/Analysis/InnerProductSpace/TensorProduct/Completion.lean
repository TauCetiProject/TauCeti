/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import TauCeti.Analysis.InnerProductSpace.Completion
public import TauCeti.Analysis.Normed.Operator.Completion

/-!
# Completed tensor products of Hilbert spaces and amplified operators

For inner product spaces `E` and `F` over `𝕜` (`ℝ` or `ℂ`), Mathlib puts on the algebraic tensor
product `E ⊗[𝕜] F` the inner product with `⟪x ⊗ₜ y, x' ⊗ₜ y'⟫ = ⟪x, x'⟫ ⟪y, y'⟫`. Its completion
`UniformSpace.Completion (E ⊗[𝕜] F)` is the *completed Hilbert tensor product* `E ⊗̂ F`, a Hilbert
space, whether or not `E` and `F` are complete. This file develops the operators on it.

* The pure tensors `x ⊗ₜ y` span a dense subspace (`TensorProduct.dense_span_coe_tmul`), so a
  bounded operator out of `E ⊗̂ F` is determined by its values on them
  (`TensorProduct.completion_ext`).
* A bounded operator `f : E →L[𝕜] E'` induces the bounded operator `f ⊗ 1` on `E ⊗̂ F`, the
  *amplification* `f.rTensorCompletion F`, which extends `ContinuousLinearMap.rTensor` and sends
  `x ⊗ₜ y` to `f x ⊗ₜ y`. It is the only bounded operator doing so
  (`ContinuousLinearMap.eq_rTensorCompletion_iff`). Symmetrically `g.lTensorCompletion E` is
  `1 ⊗ g`. Operators on both factors commute
  (`ContinuousLinearMap.rTensorCompletion_comp_lTensorCompletion`), and their product is the
  extension of `TensorProduct.mapL f g`.
* Amplification preserves the operator norm when the other factor is nonzero
  (`ContinuousLinearMap.norm_rTensorCompletion`), composition and the identity, and it commutes
  with adjoints (`ContinuousLinearMap.adjoint_rTensorCompletion`): the extension of
  `f.adjoint.rTensor F` is a formal adjoint, so `ContinuousLinearMap.adjoint_completion` applies.
  When `E` is complete, `f ↦ f ⊗ 1` is therefore a unital star algebra homomorphism
  `B(E) →⋆ₐ[𝕜] B(E ⊗̂ F)` (`ContinuousLinearMap.rTensorCompletionStarAlgHom`), injective and
  isometric when `F ≠ 0`. When `F = 0` the completed tensor product is `0`, so every amplification
  is `0`.
* The flip `E ⊗ F ≃ F ⊗ E` extends to a unitary `E ⊗̂ F ≃ F ⊗̂ E`, which exchanges the two
  amplifications (`ContinuousLinearMap.lTensorCompletion_commIsometry_completion`).
* Completing a factor first does not change the completed tensor product: `E ⊗[𝕜] F` is dense in
  `Ê ⊗[𝕜] F` (`TensorProduct.denseRange_rTensor_toComplₗᵢ`), which gives the unitaries
  `E ⊗̂ F ≃ Ê ⊗̂ F` and `E ⊗̂ F ≃ E ⊗̂ F̂` (`TensorProduct.completionLeftIsometry`,
  `TensorProduct.completionRightIsometry`). Through them the associator of the algebraic tensor
  product extends to the unitary `(E ⊗̂ F) ⊗̂ G ≃ E ⊗̂ (F ⊗̂ G)`
  (`TensorProduct.assocIsometryCompletion`).

These are the bounded operators `A ⊗ 1` and `1 ⊗ B` on tensor products of Hilbert spaces from which
spatial tensor products of operator algebras are built, and they act on tensor products of `L²`
spaces of sections, for instance in the block operators of products of elliptic operators.

## References

* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras, Volume I*,
  Academic Press, 1983, §2.6 (tensor products of Hilbert spaces and of operators).
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, Academic
  Press, 1980, §II.4 and §VIII.10.
-/

public section

noncomputable section

open UniformSpace TensorProduct
open scoped InnerProductSpace

variable {𝕜 E E' E'' F F' F'' G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
  [NormedAddCommGroup E''] [InnerProductSpace 𝕜 E''] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']
  [NormedAddCommGroup F''] [InnerProductSpace 𝕜 F''] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

namespace TensorProduct

variable (𝕜 E F) in
/-- The pure tensors span a dense subspace of the completed tensor product of `E` and `F`. -/
theorem dense_span_coe_tmul :
    (Submodule.span 𝕜 (Set.range fun p : E × F ↦
      ((p.1 ⊗ₜ[𝕜] p.2 : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)))).topologicalClosure = ⊤ := by
  have h : Submodule.span 𝕜 (Set.range fun p : E × F ↦
      ((p.1 ⊗ₜ[𝕜] p.2 : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F))) =
      LinearMap.range ((Completion.toComplL : E ⊗[𝕜] F →L[𝕜] Completion (E ⊗[𝕜] F)) :
        E ⊗[𝕜] F →ₗ[𝕜] Completion (E ⊗[𝕜] F)) := by
    rw [LinearMap.range_eq_map, ← span_tmul_eq_top, Submodule.map_span]
    congr 1
    ext u
    simp
  rw [h, eq_top_iff]
  intro u _
  refine closure_minimal (fun v hv ↦ ?_) (Submodule.isClosed_topologicalClosure _)
    (Completion.denseRange_coe u)
  obtain ⟨w, rfl⟩ := hv
  exact Submodule.le_topologicalClosure _ ⟨w, rfl⟩

/-- Two bounded operators from the completed tensor product of `E` and `F` to a Hausdorff space
agree when they agree on pure tensors. -/
theorem completion_ext {M : Type*} [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M] [T2Space M]
    {l l' : Completion (E ⊗[𝕜] F) →L[𝕜] M}
    (h : ∀ x y, l (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = l' (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F)) : l = l' := by
  have h' : l ∘L Completion.toComplL = l' ∘L Completion.toComplL :=
    ContinuousLinearMap.coe_inj.1 <| TensorProduct.ext' fun x y ↦ by simpa using h x y
  exact DFunLike.coe_injective <|
    Completion.ext l.continuous l'.continuous fun u ↦ by simpa using congr($h' u)

section Associator

variable (𝕜 E F) in
/-- The pure tensors `x ⊗ₜ y` with `x` in `E` have dense span in `Completion E ⊗[𝕜] F`, so the
algebraic tensor product `E ⊗[𝕜] F` is dense there. -/
theorem denseRange_rTensor_toComplₗᵢ :
    DenseRange ((Completion.toComplₗᵢ (𝕜 := 𝕜) (E := E)).rTensor F) := by
  let T := LinearMap.range ((Completion.toComplₗᵢ (𝕜 := 𝕜) (E := E)).rTensor F).toLinearMap
  -- Every pure tensor `c ⊗ₜ y` lies in the closure of `T`: the closure is closed, and contains
  -- `c ⊗ₜ y` for `c` in `E`.
  have htmul (c : Completion E) (y : F) : c ⊗ₜ[𝕜] y ∈ T.topologicalClosure := by
    induction c using Completion.induction_on with
    | hp =>
      exact T.isClosed_topologicalClosure.preimage ((mkL 𝕜 (Completion E) F).flip y).continuous
    | ih x => exact T.le_topologicalClosure ⟨x ⊗ₜ[𝕜] y, by simp⟩
  have hT : T.topologicalClosure = ⊤ := eq_top_iff.2 <|
    (span_tmul_eq_top 𝕜 (Completion E) F).ge.trans <|
      Submodule.span_le.2 fun _ ⟨c, y, h⟩ ↦ h ▸ htmul c y
  rw [DenseRange, dense_iff_closure_eq, ← LinearIsometry.coe_toLinearMap, ← LinearMap.coe_range,
    ← Submodule.topologicalClosure_coe, hT, Submodule.top_coe]

variable (𝕜 E F) in
/-- Completing the left factor does not change the completed tensor product:
`E ⊗̂ F ≃ Ê ⊗̂ F`, sending `x ⊗ₜ y` to `x ⊗ₜ y`. -/
def completionLeftIsometry :
    Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] Completion (Completion E ⊗[𝕜] F) :=
  LinearIsometry.completionEquivOfDenseRange _ (denseRange_rTensor_toComplₗᵢ 𝕜 E F)

variable (𝕜 E F) in
/-- Completing the right factor does not change the completed tensor product:
`E ⊗̂ F ≃ E ⊗̂ F̂`, sending `x ⊗ₜ y` to `x ⊗ₜ y`. -/
def completionRightIsometry :
    Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] Completion (E ⊗[𝕜] Completion F) :=
  (commIsometry 𝕜 E F).completion.trans <| (completionLeftIsometry 𝕜 F E).trans
    (commIsometry 𝕜 (Completion F) E).completion

@[simp]
theorem completionLeftIsometry_coe_tmul (x : E) (y : F) :
    completionLeftIsometry 𝕜 E F (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) =
      ((x : Completion E) ⊗ₜ[𝕜] y : Completion E ⊗[𝕜] F) := by
  simp [completionLeftIsometry]

@[simp]
theorem completionRightIsometry_coe_tmul (x : E) (y : F) :
    completionRightIsometry 𝕜 E F (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) =
      (x ⊗ₜ[𝕜] (y : Completion F) : E ⊗[𝕜] Completion F) := by
  simp [completionRightIsometry]

@[simp]
theorem completionLeftIsometry_symm_coe_tmul (x : E) (y : F) :
    (completionLeftIsometry 𝕜 E F).symm ((x : Completion E) ⊗ₜ[𝕜] y : Completion E ⊗[𝕜] F) =
      (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) :=
  (LinearIsometryEquiv.symm_apply_eq _).2 (completionLeftIsometry_coe_tmul x y).symm

@[simp]
theorem completionRightIsometry_symm_coe_tmul (x : E) (y : F) :
    (completionRightIsometry 𝕜 E F).symm (x ⊗ₜ[𝕜] (y : Completion F) : E ⊗[𝕜] Completion F) =
      (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) :=
  (LinearIsometryEquiv.symm_apply_eq _).2 (completionRightIsometry_coe_tmul x y).symm

variable (𝕜 E F G) in
/-- The associator `(E ⊗̂ F) ⊗̂ G ≃ E ⊗̂ (F ⊗̂ G)` of completed tensor products, extending
`TensorProduct.assocIsometry`. -/
def assocIsometryCompletion :
    Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) ≃ₗᵢ[𝕜] Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G)) :=
  (completionLeftIsometry 𝕜 (E ⊗[𝕜] F) G).symm.trans <|
    (assocIsometry 𝕜 E F G).completion.trans (completionRightIsometry 𝕜 E (F ⊗[𝕜] G))

/-- The associator sends `(x ⊗ₜ y) ⊗ₜ z` to `x ⊗ₜ (y ⊗ₜ z)`. -/
@[simp]
theorem assocIsometryCompletion_coe_tmul (x : E) (y : F) (z : G) :
    assocIsometryCompletion 𝕜 E F G
        (((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] z :
          Completion (E ⊗[𝕜] F) ⊗[𝕜] G) =
      (x ⊗ₜ[𝕜] ((y ⊗ₜ[𝕜] z : F ⊗[𝕜] G) : Completion (F ⊗[𝕜] G)) :
        E ⊗[𝕜] Completion (F ⊗[𝕜] G)) := by
  simp [assocIsometryCompletion]

end Associator

end TensorProduct

namespace ContinuousLinearMap

section rTensor

variable (F) in
/-- The amplification `f ⊗ 1 : E ⊗̂ F →L[𝕜] E' ⊗̂ F` of a bounded operator `f : E →L[𝕜] E'` to the
completed tensor products with `F`: the extension of `ContinuousLinearMap.rTensor` to the
completions, sending `x ⊗ₜ y` to `f x ⊗ₜ y`. -/
def rTensorCompletion (f : E →L[𝕜] E') :
    Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F) :=
  (f.rTensor F).completion

/-- On the algebraic tensor product, the amplification is `ContinuousLinearMap.rTensor`. -/
@[simp]
theorem rTensorCompletion_coe (f : E →L[𝕜] E') (u : E ⊗[𝕜] F) :
    f.rTensorCompletion F u = (f.rTensor F u : Completion (E' ⊗[𝕜] F)) :=
  completion_apply_coe _ u

/-- The amplification `f ⊗ 1` sends `x ⊗ₜ y` to `f x ⊗ₜ y`. -/
theorem rTensorCompletion_tmul (f : E →L[𝕜] E') (x : E) (y : F) :
    f.rTensorCompletion F (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = (f x ⊗ₜ[𝕜] y : E' ⊗[𝕜] F) := by
  simp

/-- The amplification `f ⊗ 1` is the only bounded operator sending `x ⊗ₜ y` to `f x ⊗ₜ y`. -/
theorem eq_rTensorCompletion_iff {f : E →L[𝕜] E'}
    {T : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)} :
    T = f.rTensorCompletion F ↔
      ∀ x y, T (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = (f x ⊗ₜ[𝕜] y : E' ⊗[𝕜] F) :=
  ⟨fun h x y ↦ h ▸ f.rTensorCompletion_tmul x y,
    fun h ↦ completion_ext fun x y ↦ by rw [h, rTensorCompletion_tmul]⟩

/-- The amplification `f ⊗ 1` has norm at most `‖f‖`. -/
theorem norm_rTensorCompletion_le (f : E →L[𝕜] E') : ‖f.rTensorCompletion F‖ ≤ ‖f‖ :=
  (norm_completion _).trans_le (norm_rTensor_le _ _)

/-- The amplification `f ⊗ 1` to a nonzero space `F` has the same norm as `f`. -/
@[simp]
theorem norm_rTensorCompletion [Nontrivial F] (f : E →L[𝕜] E') :
    ‖f.rTensorCompletion F‖ = ‖f‖ := by
  refine le_antisymm (norm_rTensorCompletion_le f) (opNorm_le_bound _ (norm_nonneg _) fun x ↦ ?_)
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  have h := (f.rTensorCompletion F).le_opNorm (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F)
  rw [rTensorCompletion_tmul, Completion.norm_coe, Completion.norm_coe, norm_tmul, norm_tmul,
    ← mul_assoc] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.2 hy)

@[simp]
theorem rTensorCompletion_id :
    (ContinuousLinearMap.id 𝕜 E).rTensorCompletion F =
      ContinuousLinearMap.id 𝕜 (Completion (E ⊗[𝕜] F)) :=
  completion_ext fun _ _ ↦ by simp

@[simp]
theorem rTensorCompletion_one :
    (1 : E →L[𝕜] E).rTensorCompletion F = 1 :=
  rTensorCompletion_id

/-- Amplification respects composition: `(f₂ ∘ f₁) ⊗ 1 = (f₂ ⊗ 1) ∘ (f₁ ⊗ 1)`. -/
theorem rTensorCompletion_comp (f₂ : E' →L[𝕜] E'') (f₁ : E →L[𝕜] E') :
    (f₂ ∘L f₁).rTensorCompletion F = f₂.rTensorCompletion F ∘L f₁.rTensorCompletion F :=
  completion_ext fun _ _ ↦ by simp

theorem rTensorCompletion_mul (f₁ f₂ : E →L[𝕜] E) :
    (f₁ * f₂).rTensorCompletion F = f₁.rTensorCompletion F * f₂.rTensorCompletion F :=
  rTensorCompletion_comp f₁ f₂

@[simp]
theorem rTensorCompletion_add (f₁ f₂ : E →L[𝕜] E') :
    (f₁ + f₂).rTensorCompletion F = f₁.rTensorCompletion F + f₂.rTensorCompletion F :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_add]

@[simp]
theorem rTensorCompletion_smul (c : 𝕜) (f : E →L[𝕜] E') :
    (c • f).rTensorCompletion F = c • f.rTensorCompletion F :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_smul]

@[simp]
theorem rTensorCompletion_neg (f : E →L[𝕜] E') :
    (-f).rTensorCompletion F = -f.rTensorCompletion F :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_neg]

@[simp]
theorem rTensorCompletion_sub (f₁ f₂ : E →L[𝕜] E') :
    (f₁ - f₂).rTensorCompletion F = f₁.rTensorCompletion F - f₂.rTensorCompletion F :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_sub]

@[simp]
theorem rTensorCompletion_zero : (0 : E →L[𝕜] E').rTensorCompletion F = 0 :=
  completion_ext fun _ _ ↦ by simp

/-- Every amplification to the zero space is zero. -/
theorem rTensorCompletion_of_subsingleton [Subsingleton F] (f : E →L[𝕜] E') :
    f.rTensorCompletion F = 0 :=
  completion_ext fun x y ↦ by simp [Subsingleton.elim y 0]

variable (F) in
/-- The amplification `f† ⊗ 1` is the adjoint of `f ⊗ 1`. -/
@[simp]
theorem adjoint_rTensorCompletion [CompleteSpace E] [CompleteSpace E'] (f : E →L[𝕜] E') :
    adjoint (f.rTensorCompletion F) = (adjoint f).rTensorCompletion F := by
  refine adjoint_completion fun u v ↦ ?_
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | tmul x y =>
    induction v using TensorProduct.inductionOn with
    | add v₁ v₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | tmul x' y' => simp [adjoint_inner_right]

end rTensor

section lTensor

variable (E) in
/-- The amplification `1 ⊗ g : E ⊗̂ F →L[𝕜] E ⊗̂ F'` of a bounded operator `g : F →L[𝕜] F'` to the
completed tensor products with `E`: the extension of `ContinuousLinearMap.lTensor` to the
completions, sending `x ⊗ₜ y` to `x ⊗ₜ g y`. -/
def lTensorCompletion (g : F →L[𝕜] F') :
    Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F') :=
  (g.lTensor E).completion

/-- On the algebraic tensor product, the amplification is `ContinuousLinearMap.lTensor`. -/
@[simp]
theorem lTensorCompletion_coe (g : F →L[𝕜] F') (u : E ⊗[𝕜] F) :
    g.lTensorCompletion E u = (g.lTensor E u : Completion (E ⊗[𝕜] F')) :=
  completion_apply_coe _ u

/-- The amplification `1 ⊗ g` sends `x ⊗ₜ y` to `x ⊗ₜ g y`. -/
theorem lTensorCompletion_tmul (g : F →L[𝕜] F') (x : E) (y : F) :
    g.lTensorCompletion E (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = (x ⊗ₜ[𝕜] g y : E ⊗[𝕜] F') := by
  simp

/-- The amplification `1 ⊗ g` is the only bounded operator sending `x ⊗ₜ y` to `x ⊗ₜ g y`. -/
theorem eq_lTensorCompletion_iff {g : F →L[𝕜] F'}
    {T : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')} :
    T = g.lTensorCompletion E ↔
      ∀ x y, T (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = (x ⊗ₜ[𝕜] g y : E ⊗[𝕜] F') :=
  ⟨fun h x y ↦ h ▸ g.lTensorCompletion_tmul x y,
    fun h ↦ completion_ext fun x y ↦ by rw [h, lTensorCompletion_tmul]⟩

/-- The amplification `1 ⊗ g` has norm at most `‖g‖`. -/
theorem norm_lTensorCompletion_le (g : F →L[𝕜] F') : ‖g.lTensorCompletion E‖ ≤ ‖g‖ :=
  (norm_completion _).trans_le (norm_lTensor_le _ _)

/-- The amplification `1 ⊗ g` from a nonzero space `E` has the same norm as `g`. -/
@[simp]
theorem norm_lTensorCompletion [Nontrivial E] (g : F →L[𝕜] F') :
    ‖g.lTensorCompletion E‖ = ‖g‖ := by
  refine le_antisymm (norm_lTensorCompletion_le g) (opNorm_le_bound _ (norm_nonneg _) fun y ↦ ?_)
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have h := (g.lTensorCompletion E).le_opNorm (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F)
  rw [lTensorCompletion_tmul, Completion.norm_coe, Completion.norm_coe, norm_tmul, norm_tmul,
    mul_left_comm] at h
  exact le_of_mul_le_mul_left h (norm_pos_iff.2 hx)

@[simp]
theorem lTensorCompletion_id :
    (ContinuousLinearMap.id 𝕜 F).lTensorCompletion E =
      ContinuousLinearMap.id 𝕜 (Completion (E ⊗[𝕜] F)) :=
  completion_ext fun _ _ ↦ by simp

@[simp]
theorem lTensorCompletion_one :
    (1 : F →L[𝕜] F).lTensorCompletion E = 1 :=
  lTensorCompletion_id

/-- Amplification respects composition: `1 ⊗ (g₂ ∘ g₁) = (1 ⊗ g₂) ∘ (1 ⊗ g₁)`. -/
theorem lTensorCompletion_comp (g₂ : F' →L[𝕜] F'') (g₁ : F →L[𝕜] F') :
    (g₂ ∘L g₁).lTensorCompletion E = g₂.lTensorCompletion E ∘L g₁.lTensorCompletion E :=
  completion_ext fun _ _ ↦ by simp

theorem lTensorCompletion_mul (g₁ g₂ : F →L[𝕜] F) :
    (g₁ * g₂).lTensorCompletion E = g₁.lTensorCompletion E * g₂.lTensorCompletion E :=
  lTensorCompletion_comp g₁ g₂

@[simp]
theorem lTensorCompletion_add (g₁ g₂ : F →L[𝕜] F') :
    (g₁ + g₂).lTensorCompletion E = g₁.lTensorCompletion E + g₂.lTensorCompletion E :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_add]

@[simp]
theorem lTensorCompletion_smul (c : 𝕜) (g : F →L[𝕜] F') :
    (c • g).lTensorCompletion E = c • g.lTensorCompletion E :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_smul]

@[simp]
theorem lTensorCompletion_neg (g : F →L[𝕜] F') :
    (-g).lTensorCompletion E = -g.lTensorCompletion E :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_neg]

@[simp]
theorem lTensorCompletion_sub (g₁ g₂ : F →L[𝕜] F') :
    (g₁ - g₂).lTensorCompletion E = g₁.lTensorCompletion E - g₂.lTensorCompletion E :=
  completion_ext fun _ _ ↦ by simp [Completion.coe_sub]

@[simp]
theorem lTensorCompletion_zero : (0 : F →L[𝕜] F').lTensorCompletion E = 0 :=
  completion_ext fun _ _ ↦ by simp

/-- Every amplification from the zero space is zero. -/
theorem lTensorCompletion_of_subsingleton [Subsingleton E] (g : F →L[𝕜] F') :
    g.lTensorCompletion E = 0 :=
  completion_ext fun x y ↦ by simp [Subsingleton.elim x 0]

variable (E) in
/-- The amplification `1 ⊗ g†` is the adjoint of `1 ⊗ g`. -/
@[simp]
theorem adjoint_lTensorCompletion [CompleteSpace F] [CompleteSpace F'] (g : F →L[𝕜] F') :
    adjoint (g.lTensorCompletion E) = (adjoint g).lTensorCompletion E := by
  refine adjoint_completion fun u v ↦ ?_
  induction u using TensorProduct.inductionOn with
  | add u₁ u₂ h₁ h₂ => simp only [map_add, inner_add_left, h₁, h₂]
  | tmul x y =>
    induction v using TensorProduct.inductionOn with
    | add v₁ v₂ h₁ h₂ => simp only [map_add, inner_add_right, h₁, h₂]
    | tmul x' y' => simp [adjoint_inner_right]

end lTensor

/-- Amplifications on the two factors commute, with product the extension of
`TensorProduct.mapL f g`: `(f ⊗ 1) ∘ (1 ⊗ g) = f ⊗ g`. -/
theorem rTensorCompletion_comp_lTensorCompletion (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    f.rTensorCompletion F' ∘L g.lTensorCompletion E = (mapL f g).completion :=
  completion_ext fun _ _ ↦ by simp

/-- Amplifications on the two factors commute, with product the extension of
`TensorProduct.mapL f g`: `(1 ⊗ g) ∘ (f ⊗ 1) = f ⊗ g`. -/
theorem lTensorCompletion_comp_rTensorCompletion (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    g.lTensorCompletion E' ∘L f.rTensorCompletion F = (mapL f g).completion :=
  completion_ext fun _ _ ↦ by simp

/-- The amplifications `f ⊗ 1` and `1 ⊗ g` of endomorphisms commute. -/
theorem commute_rTensorCompletion_lTensorCompletion (f : E →L[𝕜] E) (g : F →L[𝕜] F) :
    Commute (f.rTensorCompletion F) (g.lTensorCompletion E) :=
  (rTensorCompletion_comp_lTensorCompletion f g).trans
    (lTensorCompletion_comp_rTensorCompletion f g).symm

/-- The extension of the flip `E ⊗ F ≃ F ⊗ E` to the completions exchanges the two
amplifications: `(1 ⊗ f) ∘ flip = flip ∘ (f ⊗ 1)`. -/
theorem lTensorCompletion_commIsometry_completion (f : E →L[𝕜] E') (u : Completion (E ⊗[𝕜] F)) :
    f.lTensorCompletion F ((commIsometry 𝕜 E F).completion u) =
      (commIsometry 𝕜 E' F).completion (f.rTensorCompletion F u) := by
  induction u using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((f.lTensorCompletion F).continuous.comp
      (commIsometry 𝕜 E F).completion.continuous)
      ((commIsometry 𝕜 E' F).completion.continuous.comp (f.rTensorCompletion F).continuous)
  | ih u =>
    rw [LinearIsometryEquiv.completion_apply_coe, rTensorCompletion_coe, lTensorCompletion_coe,
      LinearIsometryEquiv.completion_apply_coe]
    congr 1
    induction u using TensorProduct.inductionOn with
    | add u₁ u₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    | tmul x y => simp

section StarAlgHom

variable (𝕜 E F)

/-- The amplification `f ↦ f ⊗ 1` from the bounded operators on a Hilbert space `E` to the bounded
operators on the completed tensor product `E ⊗̂ F`, as a unital star algebra homomorphism. -/
def rTensorCompletionStarAlgHom [CompleteSpace E] :
    (E →L[𝕜] E) →⋆ₐ[𝕜] (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F)) where
  toFun f := f.rTensorCompletion F
  map_one' := rTensorCompletion_one
  map_mul' := rTensorCompletion_mul
  map_zero' := rTensorCompletion_zero
  map_add' := rTensorCompletion_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, rTensorCompletion_smul,
      rTensorCompletion_one]
  map_star' f := by
    rw [star_eq_adjoint, star_eq_adjoint, adjoint_rTensorCompletion]

/-- The amplification `g ↦ 1 ⊗ g` from the bounded operators on a Hilbert space `F` to the bounded
operators on the completed tensor product `E ⊗̂ F`, as a unital star algebra homomorphism. -/
def lTensorCompletionStarAlgHom [CompleteSpace F] :
    (F →L[𝕜] F) →⋆ₐ[𝕜] (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F)) where
  toFun g := g.lTensorCompletion E
  map_one' := lTensorCompletion_one
  map_mul' := lTensorCompletion_mul
  map_zero' := lTensorCompletion_zero
  map_add' := lTensorCompletion_add
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, lTensorCompletion_smul,
      lTensorCompletion_one]
  map_star' g := by
    rw [star_eq_adjoint, star_eq_adjoint, adjoint_lTensorCompletion]

variable {𝕜 E F}

@[simp]
theorem rTensorCompletionStarAlgHom_apply [CompleteSpace E] (f : E →L[𝕜] E) :
    rTensorCompletionStarAlgHom 𝕜 E F f = f.rTensorCompletion F :=
  (rfl)

@[simp]
theorem lTensorCompletionStarAlgHom_apply [CompleteSpace F] (g : F →L[𝕜] F) :
    lTensorCompletionStarAlgHom 𝕜 E F g = g.lTensorCompletion E :=
  (rfl)

/-- The amplification `f ↦ f ⊗ 1` to a nonzero space `F` is injective. -/
theorem rTensorCompletionStarAlgHom_injective [CompleteSpace E] [Nontrivial F] :
    Function.Injective (rTensorCompletionStarAlgHom 𝕜 E F) :=
  (injective_iff_map_eq_zero _).2 fun f hf ↦ by
    rw [← norm_eq_zero, ← norm_rTensorCompletion (F := F), ← rTensorCompletionStarAlgHom_apply, hf,
      norm_zero]

/-- The amplification `g ↦ 1 ⊗ g` from a nonzero space `E` is injective. -/
theorem lTensorCompletionStarAlgHom_injective [CompleteSpace F] [Nontrivial E] :
    Function.Injective (lTensorCompletionStarAlgHom 𝕜 E F) :=
  (injective_iff_map_eq_zero _).2 fun g hg ↦ by
    rw [← norm_eq_zero, ← norm_lTensorCompletion (E := E), ← lTensorCompletionStarAlgHom_apply, hg,
      norm_zero]

end StarAlgHom

end ContinuousLinearMap
