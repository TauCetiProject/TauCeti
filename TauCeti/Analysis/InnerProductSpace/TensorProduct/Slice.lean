/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
public import TauCeti.Analysis.InnerProductSpace.TensorProduct.Completion
public import TauCeti.Analysis.InnerProductSpace.UltraweakTopology

/-!
# Slice maps, orthonormal coordinate representations, and ultraweak continuity

For inner product spaces `E` and `F` over `𝕜` (`ℝ` or `ℂ`), each vector `v : F` induces a bounded
fiber embedding `TensorProduct.embedRight v : E →L[𝕜] Completion (E ⊗[𝕜] F)` sending `e ↦ ↑(e ⊗ₜ v)`
and, when `E` is complete, its adjoint `TensorProduct.sliceRight v : Completion (E ⊗[𝕜] F) →L[𝕜] E`
sending `↑(e ⊗ₜ y) ↦ ⟪v, y⟫_𝕜 • e` (and symmetrically `embedLeft` and `sliceLeft`).

Sandwiching a bounded operator `X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)` between
fiber embeddings and vector slices yields the operator slice map
`TensorProduct.opSliceRight η₁ η₂ X = sliceRight η₂ ∘L X ∘L embedRight η₁ : E →L[𝕜] E'`
characterized by `⟪ξ₂, opSliceRight η₁ η₂ X ξ₁⟫ = ⟪↑(ξ₂ ⊗ₜ η₂), X ↑(ξ₁ ⊗ₜ η₁)⟫`
(and symmetrically `TensorProduct.opSliceLeft`). Operator slice maps satisfy exact norm bounds,
commute with adjoints after swapping the two vectors, intertwine amplified operators, separate
bounded operators on the completed tensor product, and are continuous for the ultraweak topology.

Assembling the right slices along a Hilbert basis `b : HilbertBasis ι 𝕜 F` yields the canonical
linear isometric equivalence `b.tensorReprRight E : Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] ℓ²(ι, E)` that
intertwines `f.rTensorCompletion F` with `lp.ampliation ι 2 f`, as well as the product Hilbert basis
`b₁.tensorProduct b₂` of `Completion (E ⊗[𝕜] F)`. Combining this coordinate representation with a
dyadic telescopic factorization for `ContinuousLinearMap.completion` and countable-support
reindexing on `ℓ²` establishes ultraweak continuity of `ContinuousLinearMap.rTensorCompletion` and
`ContinuousLinearMap.lTensorCompletion` with no completeness hypotheses on either factor.

## References

* R. V. Kadison and J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras*, Vol. II,
  Academic Press, 1986, §11.2.
* M. Takesaki, *Theory of Operator Algebras I*, Springer, 1979, Chapter IV, §§1, 5.
-/

public section

open Filter Topology UniformSpace
open scoped ENNReal InnerProduct InnerProductSpace TensorProduct lp

/-! ### Vector fiber embeddings and vector slice maps -/

namespace TensorProduct

section VectorSlices

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Right-fiber embedding `e ↦ ↑(e ⊗ₜ v)` into `Completion (E ⊗[𝕜] F)`. -/
noncomputable def embedRight (v : F) : E →L[𝕜] Completion (E ⊗[𝕜] F) :=
  (mkLCompletion 𝕜 E F).flip v

@[simp]
theorem embedRight_apply (v : F) (e : E) :
    embedRight v e = (↑(e ⊗ₜ[𝕜] v) : Completion (E ⊗[𝕜] F)) := by
  simp [embedRight]

theorem norm_embedRight_le (v : F) : ‖(embedRight v : E →L[𝕜] Completion (E ⊗[𝕜] F))‖ ≤ ‖v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun e ↦ by
    simp [mul_comm]

@[simp]
theorem norm_embedRight [Nontrivial E] (v : F) :
    ‖(embedRight v : E →L[𝕜] Completion (E ⊗[𝕜] F))‖ = ‖v‖ := by
  refine le_antisymm (norm_embedRight_le v) ?_
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  have he' : 0 < ‖e‖ := norm_pos_iff.mpr he
  have hle := (embedRight v : E →L[𝕜] Completion (E ⊗[𝕜] F)).le_opNorm e
  rw [embedRight_apply, Completion.norm_coe, norm_tmul, mul_comm ‖e‖ ‖v‖] at hle
  exact le_of_mul_le_mul_right hle he'

/-- Left-fiber embedding `y ↦ ↑(v ⊗ₜ y)` into `Completion (E ⊗[𝕜] F)`. -/
noncomputable def embedLeft (v : E) : F →L[𝕜] Completion (E ⊗[𝕜] F) :=
  mkLCompletion 𝕜 E F v

@[simp]
theorem embedLeft_apply (v : E) (y : F) :
    embedLeft v y = (↑(v ⊗ₜ[𝕜] y) : Completion (E ⊗[𝕜] F)) := by
  simp [embedLeft]

theorem norm_embedLeft_le (v : E) : ‖(embedLeft v : F →L[𝕜] Completion (E ⊗[𝕜] F))‖ ≤ ‖v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun _ ↦ by simp

@[simp]
theorem norm_embedLeft [Nontrivial F] (v : E) :
    ‖(embedLeft v : F →L[𝕜] Completion (E ⊗[𝕜] F))‖ = ‖v‖ := by
  refine le_antisymm (norm_embedLeft_le v) ?_
  obtain ⟨y, hy⟩ := exists_ne (0 : F)
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hle := (embedLeft v : F →L[𝕜] Completion (E ⊗[𝕜] F)).le_opNorm y
  rw [embedLeft_apply, Completion.norm_coe, norm_tmul] at hle
  exact le_of_mul_le_mul_right hle hy'

/-- Right vector slice `↑(e ⊗ₜ y) ↦ ⟪v, y⟫_𝕜 • e` on `Completion (E ⊗[𝕜] F)`. Only `E` is assumed
complete. -/
noncomputable def sliceRight [CompleteSpace E] (v : F) : Completion (E ⊗[𝕜] F) →L[𝕜] E :=
  ((ridIsometry 𝕜 E : E ⊗[𝕜] 𝕜 →L[𝕜] E) ∘L (innerSL 𝕜 v).lTensor E).fromCompletion

@[simp]
theorem sliceRight_coe_tmul [CompleteSpace E] (v : F) (e : E) (y : F) :
    sliceRight v (↑(e ⊗ₜ[𝕜] y) : Completion (E ⊗[𝕜] F)) = ⟪v, y⟫_𝕜 • e := by
  simp [sliceRight]

/-- `sliceRight v` is the unique bounded operator sending `↑(e ⊗ₜ y)` to `⟪v, y⟫_𝕜 • e`. -/
theorem eq_sliceRight_iff [CompleteSpace E] {T : Completion (E ⊗[𝕜] F) →L[𝕜] E} {v : F} :
    T = sliceRight v ↔ ∀ (e : E) (y : F), T ↑(e ⊗ₜ[𝕜] y) = ⟪v, y⟫_𝕜 • e :=
  ⟨fun h e y ↦ by simp [h],
    fun h ↦ completion_continuousLinearMap_ext fun e y ↦ by simp [h]⟩

/-- The adjoint of `embedRight v` is `sliceRight v` (no completeness assumption on `F`). -/
@[simp]
theorem adjoint_embedRight [CompleteSpace E] (v : F) :
    (embedRight v : E →L[𝕜] Completion (E ⊗[𝕜] F))† = sliceRight v := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun u e ↦ ?_).symm
  refine Completion.induction_on u (isClosed_eq (by fun_prop) (by fun_prop)) fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul x y =>
    simp [inner_smul_left, mul_comm]
  | add _ _ h₁ h₂ =>
    simp only [Completion.coe_add, map_add, inner_add_left, h₁, h₂]

@[simp]
theorem adjoint_sliceRight [CompleteSpace E] (v : F) :
    (sliceRight v : Completion (E ⊗[𝕜] F) →L[𝕜] E)† = embedRight v := by
  rw [← adjoint_embedRight, ContinuousLinearMap.adjoint_adjoint]

theorem inner_sliceRight_right [CompleteSpace E] (v : F) (e : E) (u : Completion (E ⊗[𝕜] F)) :
    ⟪e, sliceRight v u⟫_𝕜 = ⟪(↑(e ⊗ₜ[𝕜] v) : Completion (E ⊗[𝕜] F)), u⟫_𝕜 := by
  rw [← adjoint_embedRight, ContinuousLinearMap.adjoint_inner_right, embedRight_apply]

theorem inner_sliceRight_left [CompleteSpace E] (v : F) (u : Completion (E ⊗[𝕜] F)) (e : E) :
    ⟪sliceRight v u, e⟫_𝕜 = ⟪u, (↑(e ⊗ₜ[𝕜] v) : Completion (E ⊗[𝕜] F))⟫_𝕜 := by
  rw [← adjoint_embedRight, ContinuousLinearMap.adjoint_inner_left, embedRight_apply]

theorem norm_sliceRight_le [CompleteSpace E] (v : F) :
    ‖(sliceRight v : Completion (E ⊗[𝕜] F) →L[𝕜] E)‖ ≤ ‖v‖ := by
  rw [← adjoint_embedRight, ContinuousLinearMap.adjoint.norm_map]
  exact norm_embedRight_le v

@[simp]
theorem norm_sliceRight [CompleteSpace E] [Nontrivial E] (v : F) :
    ‖(sliceRight v : Completion (E ⊗[𝕜] F) →L[𝕜] E)‖ = ‖v‖ := by
  rw [← adjoint_embedRight, ContinuousLinearMap.adjoint.norm_map, norm_embedRight]

/-- Left vector slice `↑(x ⊗ₜ y) ↦ ⟪v, x⟫_𝕜 • y` on `Completion (E ⊗[𝕜] F)`. Only `F` is assumed
complete. -/
noncomputable def sliceLeft [CompleteSpace F] (v : E) : Completion (E ⊗[𝕜] F) →L[𝕜] F :=
  sliceRight v ∘L ((commIsometry 𝕜 E F).completion :
    Completion (E ⊗[𝕜] F) →L[𝕜] Completion (F ⊗[𝕜] E))

@[simp]
theorem sliceLeft_coe_tmul [CompleteSpace F] (v : E) (x : E) (y : F) :
    sliceLeft v (↑(x ⊗ₜ[𝕜] y) : Completion (E ⊗[𝕜] F)) = ⟪v, x⟫_𝕜 • y := by
  simp [sliceLeft]

/-- `sliceLeft v` is the unique bounded operator sending `↑(x ⊗ₜ y)` to `⟪v, x⟫_𝕜 • y`. -/
theorem eq_sliceLeft_iff [CompleteSpace F] {T : Completion (E ⊗[𝕜] F) →L[𝕜] F} {v : E} :
    T = sliceLeft v ↔ ∀ (x : E) (y : F), T ↑(x ⊗ₜ[𝕜] y) = ⟪v, x⟫_𝕜 • y :=
  ⟨fun h x y ↦ by simp [h],
    fun h ↦ completion_continuousLinearMap_ext fun x y ↦ by simp [h]⟩

/-- The adjoint of `embedLeft v` is `sliceLeft v` (no completeness assumption on `E`). -/
@[simp]
theorem adjoint_embedLeft [CompleteSpace F] (v : E) :
    (embedLeft v : F →L[𝕜] Completion (E ⊗[𝕜] F))† = sliceLeft v := by
  refine ((ContinuousLinearMap.eq_adjoint_iff _ _).2 fun u y ↦ ?_).symm
  refine Completion.induction_on u (isClosed_eq (by fun_prop) (by fun_prop)) fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul x w => simp [inner_smul_left]
  | add _ _ h₁ h₂ => simp only [Completion.coe_add, map_add, inner_add_left, h₁, h₂]

@[simp]
theorem adjoint_sliceLeft [CompleteSpace F] (v : E) :
    (sliceLeft v : Completion (E ⊗[𝕜] F) →L[𝕜] F)† = embedLeft v := by
  rw [← adjoint_embedLeft, ContinuousLinearMap.adjoint_adjoint]

theorem inner_sliceLeft_right [CompleteSpace F] (v : E) (y : F) (u : Completion (E ⊗[𝕜] F)) :
    ⟪y, sliceLeft v u⟫_𝕜 = ⟪(↑(v ⊗ₜ[𝕜] y) : Completion (E ⊗[𝕜] F)), u⟫_𝕜 := by
  rw [← adjoint_embedLeft, ContinuousLinearMap.adjoint_inner_right, embedLeft_apply]

theorem inner_sliceLeft_left [CompleteSpace F] (v : E) (u : Completion (E ⊗[𝕜] F)) (y : F) :
    ⟪sliceLeft v u, y⟫_𝕜 = ⟪u, (↑(v ⊗ₜ[𝕜] y) : Completion (E ⊗[𝕜] F))⟫_𝕜 := by
  rw [← adjoint_embedLeft, ContinuousLinearMap.adjoint_inner_left, embedLeft_apply]

theorem norm_sliceLeft_le [CompleteSpace F] (v : E) :
    ‖(sliceLeft v : Completion (E ⊗[𝕜] F) →L[𝕜] F)‖ ≤ ‖v‖ := by
  rw [← adjoint_embedLeft, ContinuousLinearMap.adjoint.norm_map]
  exact norm_embedLeft_le v

@[simp]
theorem norm_sliceLeft [CompleteSpace F] [Nontrivial F] (v : E) :
    ‖(sliceLeft v : Completion (E ⊗[𝕜] F) →L[𝕜] F)‖ = ‖v‖ := by
  rw [← adjoint_embedLeft, ContinuousLinearMap.adjoint.norm_map, norm_embedLeft]

end VectorSlices

/-! ### Operator slice maps -/

section OperatorSlices

open ContinuousLinearMap

variable {𝕜 E E' F F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']

private theorem norm_sliceRight_comp_embedRight_le [CompleteSpace E'] (η₁ η₂ : F)
    (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)) :
    ‖(sliceRight η₂ : Completion (E' ⊗[𝕜] F) →L[𝕜] E') ∘L X ∘L embedRight η₁‖ ≤
      ‖η₁‖ * ‖η₂‖ * ‖X‖ :=
  calc ‖(sliceRight η₂ : Completion (E' ⊗[𝕜] F) →L[𝕜] E') ∘L X ∘L embedRight η₁‖
      ≤ ‖(sliceRight η₂ : Completion (E' ⊗[𝕜] F) →L[𝕜] E')‖ * ‖X ∘L embedRight η₁‖ :=
        opNorm_comp_le _ _
    _ ≤ ‖η₂‖ * (‖X‖ * ‖(embedRight η₁ : E →L[𝕜] Completion (E ⊗[𝕜] F))‖) := by
        gcongr
        · exact norm_sliceRight_le η₂
        · exact opNorm_comp_le _ _
    _ ≤ ‖η₂‖ * (‖X‖ * ‖η₁‖) := by
        gcongr
        exact norm_embedRight_le η₁
    _ = ‖η₁‖ * ‖η₂‖ * ‖X‖ := by ring

/-- **Right operator slice map.** Given `η₁, η₂ : F`, `opSliceRight η₁ η₂` maps a bounded operator
`X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)` to `sliceRight η₂ ∘L X ∘L embedRight η₁`,
the bounded operator `E →L[𝕜] E'` with matrix coefficients
`⟪ξ₂, opSliceRight η₁ η₂ X ξ₁⟫ = ⟪↑(ξ₂ ⊗ₜ η₂), X ↑(ξ₁ ⊗ₜ η₁)⟫`. -/
noncomputable def opSliceRight [CompleteSpace E'] (η₁ η₂ : F) :
    (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)) →L[𝕜] (E →L[𝕜] E') :=
  LinearMap.mkContinuous
    { toFun X := sliceRight η₂ ∘L X ∘L embedRight η₁
      map_add' X Y := by ext; simp
      map_smul' c X := by ext; simp }
    (‖η₁‖ * ‖η₂‖) (norm_sliceRight_comp_embedRight_le η₁ η₂)

theorem opSliceRight_apply [CompleteSpace E'] (η₁ η₂ : F)
    (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)) :
    opSliceRight η₁ η₂ X = sliceRight η₂ ∘L X ∘L embedRight η₁ :=
  (rfl)

theorem opSliceRight_apply_apply [CompleteSpace E'] (η₁ η₂ : F)
    (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)) (e : E) :
    opSliceRight η₁ η₂ X e = sliceRight η₂ (X ↑(e ⊗ₜ[𝕜] η₁)) := by
  simp [opSliceRight_apply]

@[simp]
theorem inner_opSliceRight_apply [CompleteSpace E'] (η₁ η₂ : F)
    (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)) (ξ₁ : E) (ξ₂ : E') :
    ⟪ξ₂, opSliceRight η₁ η₂ X ξ₁⟫_𝕜 =
      ⟪(↑(ξ₂ ⊗ₜ[𝕜] η₂) : Completion (E' ⊗[𝕜] F)), X ↑(ξ₁ ⊗ₜ[𝕜] η₁)⟫_𝕜 := by
  rw [opSliceRight_apply_apply, inner_sliceRight_right]

theorem norm_opSliceRight_le [CompleteSpace E'] (η₁ η₂ : F) :
    ‖(opSliceRight η₁ η₂ :
      (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)) →L[𝕜] (E →L[𝕜] E'))‖ ≤
      ‖η₁‖ * ‖η₂‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

@[simp]
theorem opSliceRight_mapLCompletion [CompleteSpace E'] (η₁ η₂ : F)
    (f : E →L[𝕜] E') (g : F →L[𝕜] F) :
    opSliceRight η₁ η₂ (mapLCompletion f g) = ⟪η₂, g η₁⟫_𝕜 • f := by
  ext e
  simp [opSliceRight_apply_apply]

@[simp]
theorem opSliceRight_rTensorCompletion [CompleteSpace E'] (η₁ η₂ : F) (f : E →L[𝕜] E') :
    opSliceRight η₁ η₂ (f.rTensorCompletion F) = ⟪η₂, η₁⟫_𝕜 • f := by
  rw [rTensorCompletion_eq_mapLCompletion, opSliceRight_mapLCompletion, id_apply]

@[simp]
theorem opSliceRight_lTensorCompletion [CompleteSpace E] (η₁ η₂ : F) (y : F →L[𝕜] F) :
    opSliceRight η₁ η₂ (y.lTensorCompletion E) = ⟪η₂, y η₁⟫_𝕜 • .id 𝕜 E := by
  rw [lTensorCompletion_eq_mapLCompletion, opSliceRight_mapLCompletion]

/-- **Exact norm of `opSliceRight`.** When `E` and `E'` are nontrivial,
`‖opSliceRight η₁ η₂‖ = ‖η₁‖ * ‖η₂‖`. -/
@[simp]
theorem norm_opSliceRight [CompleteSpace E'] [Nontrivial E] [Nontrivial E'] (η₁ η₂ : F) :
    ‖(opSliceRight η₁ η₂ :
      (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)) →L[𝕜] (E →L[𝕜] E'))‖ =
      ‖η₁‖ * ‖η₂‖ := by
  refine le_antisymm (norm_opSliceRight_le η₁ η₂) ?_
  rcases eq_or_ne η₁ 0 with rfl | hη₁
  · simp only [norm_zero, zero_mul]; positivity
  rcases eq_or_ne η₂ 0 with rfl | hη₂
  · simp only [norm_zero, mul_zero]; positivity
  obtain ⟨e, he⟩ := exists_ne (0 : E)
  obtain ⟨e', he'⟩ := exists_ne (0 : E')
  let f : E →L[𝕜] E' := InnerProductSpace.rankOne 𝕜 e' e
  have hf_ne : f ≠ 0 := fun h ↦ by
    have := congr($h e)
    simp [f, InnerProductSpace.rankOne_apply, he, he'] at this
  have hf : 0 < ‖f‖ := norm_pos_iff.mpr hf_ne
  let g : F →L[𝕜] F := InnerProductSpace.rankOne 𝕜 η₂ η₁
  have hg_le : ‖g‖ ≤ ‖η₁‖ * ‖η₂‖ := opNorm_le_bound g (by positivity) fun v ↦ by
    calc ‖⟪η₁, v⟫_𝕜 • η₂‖ = ‖⟪η₁, v⟫_𝕜‖ * ‖η₂‖ := norm_smul _ _
      _ ≤ (‖η₁‖ * ‖v‖) * ‖η₂‖ := by gcongr; exact norm_inner_le_norm η₁ v
      _ = ‖η₁‖ * ‖η₂‖ * ‖v‖ := by ring
  have hpos : 0 < ‖η₁‖ * ‖η₂‖ * ‖f‖ :=
    mul_pos (mul_pos (norm_pos_iff.mpr hη₁) (norm_pos_iff.mpr hη₂)) hf
  have hval : ‖opSliceRight η₁ η₂ (mapLCompletion f g)‖ = (‖η₁‖ * ‖η₂‖) * (‖η₁‖ * ‖η₂‖ * ‖f‖) := by
    rw [opSliceRight_mapLCompletion, norm_smul, show g η₁ = ⟪η₁, η₁⟫_𝕜 • η₂ from
      InnerProductSpace.rankOne_apply η₂ η₁ η₁, inner_smul_right, norm_mul,
      inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
    simp only [norm_pow, RCLike.norm_ofReal, abs_norm]
    ring
  have hfg : ‖f‖ * ‖g‖ ≤ ‖η₁‖ * ‖η₂‖ * ‖f‖ :=
    (mul_le_mul_of_nonneg_left hg_le (norm_nonneg f)).trans_eq (mul_comm _ _)
  have hbound : (‖η₁‖ * ‖η₂‖) * (‖η₁‖ * ‖η₂‖ * ‖f‖) ≤
      ‖(opSliceRight η₁ η₂ :
        (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)) →L[𝕜] (E →L[𝕜] E'))‖ *
        (‖η₁‖ * ‖η₂‖ * ‖f‖) := by
    rw [← hval]
    refine ((opSliceRight (𝕜 := 𝕜) (E := E) (E' := E') η₁ η₂).le_opNorm
      (mapLCompletion f g)).trans ?_
    rw [norm_mapLCompletion]
    exact mul_le_mul_of_nonneg_left hfg (norm_nonneg _)
  exact le_of_mul_le_mul_right hbound hpos

/-- Operator slice maps commute with adjoints after swapping the two fiber vectors. -/
@[simp]
theorem adjoint_opSliceRight_apply [CompleteSpace E] [CompleteSpace E'] (η₁ η₂ : F)
    (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)) :
    (opSliceRight η₁ η₂ X)† = opSliceRight η₂ η₁ (X†) := by
  rw [opSliceRight_apply, adjoint_comp, adjoint_comp, adjoint_embedRight, adjoint_sliceRight,
    comp_assoc, opSliceRight_apply]

theorem opSliceRight_rTensorCompletion_comp {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace 𝕜 A] [CompleteSpace E'] [CompleteSpace A]
    (η₁ η₂ : F) (a : E' →L[𝕜] A) (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)) :
    opSliceRight η₁ η₂ (a.rTensorCompletion F ∘L X) = a ∘L opSliceRight η₁ η₂ X := by
  have hsl : (sliceRight η₂ : Completion (A ⊗[𝕜] F) →L[𝕜] A) ∘L a.rTensorCompletion F =
      a ∘L sliceRight η₂ :=
    completion_continuousLinearMap_ext fun _ _ ↦ by simp
  ext e
  simpa [opSliceRight_apply_apply] using DFunLike.congr_fun hsl (X ↑(e ⊗ₜ[𝕜] η₁))

theorem opSliceRight_comp_rTensorCompletion {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace 𝕜 A] [CompleteSpace E']
    (η₁ η₂ : F) (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)) (b : A →L[𝕜] E) :
    opSliceRight η₁ η₂ (X ∘L b.rTensorCompletion F) = opSliceRight η₁ η₂ X ∘L b := by
  ext a
  simp [opSliceRight_apply_apply]

theorem opSliceRight_comp_lTensorCompletion [CompleteSpace E']
    (η₁ η₂ : F) (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)) (y : F →L[𝕜] F) :
    opSliceRight η₁ η₂ (X ∘L y.lTensorCompletion E) = opSliceRight (y η₁) η₂ X := by
  ext e
  simp [opSliceRight_apply_apply]

theorem opSliceRight_lTensorCompletion_comp [CompleteSpace E'] [CompleteSpace F]
    (η₁ η₂ : F) (y : F →L[𝕜] F)
    (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)) :
    opSliceRight η₁ η₂ (y.lTensorCompletion E' ∘L X) = opSliceRight η₁ ((y†) η₂) X := by
  have hsl : (sliceRight η₂ : Completion (E' ⊗[𝕜] F) →L[𝕜] E') ∘L y.lTensorCompletion E' =
      sliceRight ((y†) η₂) :=
    completion_continuousLinearMap_ext fun _ _ ↦ by simp [adjoint_inner_left]
  ext e
  simpa [opSliceRight_apply_apply] using DFunLike.congr_fun hsl (X ↑(e ⊗ₜ[𝕜] η₁))

/-- **Right operator slices separate bounded operators.** Two bounded operators on completed
Hilbert tensor products are equal iff all of their right operator slices agree. -/
theorem ext_opSliceRight [CompleteSpace E']
    {X Y : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)} :
    X = Y ↔ ∀ (η₁ η₂ : F), opSliceRight η₁ η₂ X = opSliceRight η₁ η₂ Y := by
  refine ⟨fun h _ _ ↦ h ▸ rfl, fun h ↦ completion_continuousLinearMap_ext fun ξ₁ η₁ ↦ ?_⟩
  refine completion_ext_iff_inner_left.mpr fun ξ₂ η₂ ↦ ?_
  simpa only [inner_opSliceRight_apply] using
    congr_arg (fun T : E →L[𝕜] E' ↦ ⟪ξ₂, T ξ₁⟫_𝕜) (h η₁ η₂)

private theorem norm_sliceLeft_comp_embedLeft_le [CompleteSpace F'] (ξ₁ ξ₂ : E)
    (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')) :
    ‖(sliceLeft ξ₂ : Completion (E ⊗[𝕜] F') →L[𝕜] F') ∘L X ∘L embedLeft ξ₁‖ ≤
      ‖ξ₁‖ * ‖ξ₂‖ * ‖X‖ :=
  calc ‖(sliceLeft ξ₂ : Completion (E ⊗[𝕜] F') →L[𝕜] F') ∘L X ∘L embedLeft ξ₁‖
      ≤ ‖(sliceLeft ξ₂ : Completion (E ⊗[𝕜] F') →L[𝕜] F')‖ * ‖X ∘L embedLeft ξ₁‖ :=
        opNorm_comp_le _ _
    _ ≤ ‖ξ₂‖ * (‖X‖ * ‖(embedLeft ξ₁ : F →L[𝕜] Completion (E ⊗[𝕜] F))‖) := by
        gcongr
        · exact norm_sliceLeft_le ξ₂
        · exact opNorm_comp_le _ _
    _ ≤ ‖ξ₂‖ * (‖X‖ * ‖ξ₁‖) := by
        gcongr
        exact norm_embedLeft_le ξ₁
    _ = ‖ξ₁‖ * ‖ξ₂‖ * ‖X‖ := by ring

/-- **Left operator slice map.** Given `ξ₁, ξ₂ : E`, `opSliceLeft ξ₁ ξ₂` maps a bounded operator
`X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')` to `sliceLeft ξ₂ ∘L X ∘L embedLeft ξ₁`,
with matrix coefficients `⟪η₂, opSliceLeft ξ₁ ξ₂ X η₁⟫ = ⟪↑(ξ₂ ⊗ₜ η₂), X ↑(ξ₁ ⊗ₜ η₁)⟫`. -/
noncomputable def opSliceLeft [CompleteSpace F'] (ξ₁ ξ₂ : E) :
    (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')) →L[𝕜] (F →L[𝕜] F') :=
  LinearMap.mkContinuous
    { toFun X := sliceLeft ξ₂ ∘L X ∘L embedLeft ξ₁
      map_add' X Y := by ext; simp
      map_smul' c X := by ext; simp }
    (‖ξ₁‖ * ‖ξ₂‖) (norm_sliceLeft_comp_embedLeft_le ξ₁ ξ₂)

theorem opSliceLeft_apply [CompleteSpace F'] (ξ₁ ξ₂ : E)
    (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')) :
    opSliceLeft ξ₁ ξ₂ X = sliceLeft ξ₂ ∘L X ∘L embedLeft ξ₁ :=
  (rfl)

theorem opSliceLeft_apply_apply [CompleteSpace F'] (ξ₁ ξ₂ : E)
    (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')) (y : F) :
    opSliceLeft ξ₁ ξ₂ X y = sliceLeft ξ₂ (X ↑(ξ₁ ⊗ₜ[𝕜] y)) := by
  simp [opSliceLeft_apply]

theorem opSliceLeft_eq_opSliceRight_conj_commIsometry [CompleteSpace F'] (ξ₁ ξ₂ : E)
    (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')) :
    opSliceLeft ξ₁ ξ₂ X = opSliceRight ξ₁ ξ₂
      (((commIsometry 𝕜 E F').completion :
          Completion (E ⊗[𝕜] F') →L[𝕜] Completion (F' ⊗[𝕜] E)) ∘L X ∘L
        ((commIsometry 𝕜 F E).completion :
          Completion (F ⊗[𝕜] E) →L[𝕜] Completion (E ⊗[𝕜] F))) := by
  ext y
  simp [opSliceLeft_apply_apply, opSliceRight_apply_apply, sliceLeft]

@[simp]
theorem inner_opSliceLeft_apply [CompleteSpace F'] (ξ₁ ξ₂ : E)
    (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')) (η₁ : F) (η₂ : F') :
    ⟪η₂, opSliceLeft ξ₁ ξ₂ X η₁⟫_𝕜 =
      ⟪(↑(ξ₂ ⊗ₜ[𝕜] η₂) : Completion (E ⊗[𝕜] F')), X ↑(ξ₁ ⊗ₜ[𝕜] η₁)⟫_𝕜 := by
  rw [opSliceLeft_apply_apply, inner_sliceLeft_right]

theorem norm_opSliceLeft_le [CompleteSpace F'] (ξ₁ ξ₂ : E) :
    ‖(opSliceLeft ξ₁ ξ₂ :
      (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')) →L[𝕜] (F →L[𝕜] F'))‖ ≤
      ‖ξ₁‖ * ‖ξ₂‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

@[simp]
theorem opSliceLeft_mapLCompletion [CompleteSpace F'] (ξ₁ ξ₂ : E)
    (f : E →L[𝕜] E) (g : F →L[𝕜] F') :
    opSliceLeft ξ₁ ξ₂ (mapLCompletion f g) = ⟪ξ₂, f ξ₁⟫_𝕜 • g := by
  ext y
  simp [opSliceLeft_apply_apply]

@[simp]
theorem opSliceLeft_lTensorCompletion [CompleteSpace F'] (ξ₁ ξ₂ : E) (g : F →L[𝕜] F') :
    opSliceLeft ξ₁ ξ₂ (g.lTensorCompletion E) = ⟪ξ₂, ξ₁⟫_𝕜 • g := by
  rw [lTensorCompletion_eq_mapLCompletion, opSliceLeft_mapLCompletion, id_apply]

@[simp]
theorem opSliceLeft_rTensorCompletion [CompleteSpace F] (ξ₁ ξ₂ : E) (x : E →L[𝕜] E) :
    opSliceLeft ξ₁ ξ₂ (x.rTensorCompletion F) = ⟪ξ₂, x ξ₁⟫_𝕜 • .id 𝕜 F := by
  rw [rTensorCompletion_eq_mapLCompletion, opSliceLeft_mapLCompletion]

@[simp]
theorem norm_opSliceLeft [CompleteSpace F'] [Nontrivial F] [Nontrivial F'] (ξ₁ ξ₂ : E) :
    ‖(opSliceLeft ξ₁ ξ₂ :
      (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')) →L[𝕜] (F →L[𝕜] F'))‖ =
      ‖ξ₁‖ * ‖ξ₂‖ := by
  refine le_antisymm (norm_opSliceLeft_le ξ₁ ξ₂) ?_
  refine (norm_opSliceRight (𝕜 := 𝕜) (E := F) (E' := F') (F := E) ξ₁ ξ₂).symm.trans_le ?_
  refine opNorm_le_bound _
    (norm_nonneg (opSliceLeft (𝕜 := 𝕜) (F := F) (F' := F') ξ₁ ξ₂)) fun Y ↦ ?_
  let X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F') :=
    ((commIsometry 𝕜 F' E).completion :
        Completion (F' ⊗[𝕜] E) →L[𝕜] Completion (E ⊗[𝕜] F')) ∘L Y ∘L
      ((commIsometry 𝕜 E F).completion :
        Completion (E ⊗[𝕜] F) →L[𝕜] Completion (F ⊗[𝕜] E))
  have hYX : opSliceRight ξ₁ ξ₂ Y = opSliceLeft ξ₁ ξ₂ X := by
    ext y
    refine ext_inner_left 𝕜 fun y' ↦ ?_
    simp only [inner_opSliceRight_apply, inner_opSliceLeft_apply, X, comp_apply,
      LinearIsometryEquiv.coe_coe'', commIsometry_completion_coe_tmul]
    rw [← commIsometry_completion_coe_tmul y' ξ₂]
    exact ((commIsometry 𝕜 F' E).completion.inner_map_map ↑(y' ⊗ₜ[𝕜] ξ₂) (Y ↑(y ⊗ₜ[𝕜] ξ₁))).symm
  have hnorm : ‖X‖ ≤ ‖Y‖ := by
    refine opNorm_le_bound _ (norm_nonneg Y) fun u ↦ ?_
    simpa only [X, comp_apply, LinearIsometryEquiv.coe_coe'', LinearIsometryEquiv.norm_map] using
      Y.le_opNorm ((commIsometry 𝕜 E F).completion u)
  rw [hYX]
  exact ((opSliceLeft (𝕜 := 𝕜) (F := F) (F' := F') ξ₁ ξ₂).le_opNorm X).trans (by gcongr)

@[simp]
theorem adjoint_opSliceLeft_apply [CompleteSpace F] [CompleteSpace F'] (ξ₁ ξ₂ : E)
    (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')) :
    (opSliceLeft ξ₁ ξ₂ X)† = opSliceLeft ξ₂ ξ₁ (X†) := by
  rw [opSliceLeft_apply, adjoint_comp, adjoint_comp, adjoint_embedLeft, adjoint_sliceLeft,
    comp_assoc, opSliceLeft_apply]

theorem opSliceLeft_lTensorCompletion_comp {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace 𝕜 A] [CompleteSpace F'] [CompleteSpace A]
    (ξ₁ ξ₂ : E) (a : F' →L[𝕜] A) (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')) :
    opSliceLeft ξ₁ ξ₂ (a.lTensorCompletion E ∘L X) = a ∘L opSliceLeft ξ₁ ξ₂ X := by
  have hsl : (sliceLeft ξ₂ : Completion (E ⊗[𝕜] A) →L[𝕜] A) ∘L a.lTensorCompletion E =
      a ∘L sliceLeft ξ₂ :=
    completion_continuousLinearMap_ext fun _ _ ↦ by simp
  ext y
  simpa [opSliceLeft_apply_apply] using DFunLike.congr_fun hsl (X ↑(ξ₁ ⊗ₜ[𝕜] y))

theorem opSliceLeft_comp_lTensorCompletion {A : Type*} [NormedAddCommGroup A]
    [InnerProductSpace 𝕜 A] [CompleteSpace F']
    (ξ₁ ξ₂ : E) (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')) (b : A →L[𝕜] F) :
    opSliceLeft ξ₁ ξ₂ (X ∘L b.lTensorCompletion E) = opSliceLeft ξ₁ ξ₂ X ∘L b := by
  ext a
  simp [opSliceLeft_apply_apply]

theorem opSliceLeft_comp_rTensorCompletion [CompleteSpace F']
    (ξ₁ ξ₂ : E) (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')) (x : E →L[𝕜] E) :
    opSliceLeft ξ₁ ξ₂ (X ∘L x.rTensorCompletion F) = opSliceLeft (x ξ₁) ξ₂ X := by
  ext y
  simp [opSliceLeft_apply_apply]

theorem opSliceLeft_rTensorCompletion_comp [CompleteSpace F'] [CompleteSpace E]
    (ξ₁ ξ₂ : E) (x : E →L[𝕜] E)
    (X : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')) :
    opSliceLeft ξ₁ ξ₂ (x.rTensorCompletion F' ∘L X) = opSliceLeft ξ₁ ((x†) ξ₂) X := by
  have hsl : (sliceLeft ξ₂ : Completion (E ⊗[𝕜] F') →L[𝕜] F') ∘L x.rTensorCompletion F' =
      sliceLeft ((x†) ξ₂) :=
    completion_continuousLinearMap_ext fun _ _ ↦ by simp [adjoint_inner_left]
  ext y
  simpa [opSliceLeft_apply_apply] using DFunLike.congr_fun hsl (X ↑(ξ₁ ⊗ₜ[𝕜] y))

/-- **Left operator slices separate bounded operators.** -/
theorem ext_opSliceLeft [CompleteSpace F']
    {X Y : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')} :
    X = Y ↔ ∀ (ξ₁ ξ₂ : E), opSliceLeft ξ₁ ξ₂ X = opSliceLeft ξ₁ ξ₂ Y := by
  refine ⟨fun h _ _ ↦ h ▸ rfl, fun h ↦ completion_continuousLinearMap_ext fun ξ₁ η₁ ↦ ?_⟩
  refine completion_ext_iff_inner_left.mpr fun ξ₂ η₂ ↦ ?_
  simpa only [inner_opSliceLeft_apply] using
    congr_arg (fun T : F →L[𝕜] F' ↦ ⟪η₂, T η₁⟫_𝕜) (h ξ₁ ξ₂)

/-- Right operator slice maps are continuous for the ultraweak operator topology. -/
theorem continuous_opSliceRight_ultraweak [CompleteSpace E'] (η₁ η₂ : F) :
    Continuous fun X : TauCeti.ContinuousLinearMapUltraweak 𝕜
        (Completion (E ⊗[𝕜] F)) (Completion (E' ⊗[𝕜] F)) ↦
      TauCeti.ContinuousLinearMapUltraweak.ofCLM (opSliceRight η₁ η₂ X.toCLM) :=
  TauCeti.ContinuousLinearMapUltraweak.continuous_of_continuous_inner_ampliation_apply
    fun ξ η ↦ by
      refine (TauCeti.ContinuousLinearMapUltraweak.continuous_inner_ampliation_apply
        (lp.ampliation ℕ 2 (embedRight (𝕜 := 𝕜) (E := E) η₁) ξ)
        (lp.ampliation ℕ 2 (embedRight (𝕜 := 𝕜) (E := E') η₂) η)).congr fun X ↦ ?_
      simp only [lp.inner_ampliation_apply, lp.ampliation_apply_apply,
        embedRight_apply, inner_opSliceRight_apply]

/-- Left operator slice maps are continuous for the ultraweak operator topology. -/
theorem continuous_opSliceLeft_ultraweak [CompleteSpace F'] (ξ₁ ξ₂ : E) :
    Continuous fun X : TauCeti.ContinuousLinearMapUltraweak 𝕜
        (Completion (E ⊗[𝕜] F)) (Completion (E ⊗[𝕜] F')) ↦
      TauCeti.ContinuousLinearMapUltraweak.ofCLM (opSliceLeft ξ₁ ξ₂ X.toCLM) :=
  TauCeti.ContinuousLinearMapUltraweak.continuous_of_continuous_inner_ampliation_apply
    fun ξ η ↦ by
      refine (TauCeti.ContinuousLinearMapUltraweak.continuous_inner_ampliation_apply
        (lp.ampliation ℕ 2 (embedLeft (𝕜 := 𝕜) (F := F) ξ₁) ξ)
        (lp.ampliation ℕ 2 (embedLeft (𝕜 := 𝕜) (F := F') ξ₂) η)).congr fun X ↦ ?_
      simp only [lp.inner_ampliation_apply, lp.ampliation_apply_apply,
        embedLeft_apply, inner_opSliceLeft_apply]

end OperatorSlices

end TensorProduct

/-! ### Orthonormal coordinate representation and tensor Hilbert bases -/

namespace HilbertBasis

open TensorProduct

section TensorRepr

variable {ι 𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

variable (E) in
/-- Fiber embedding `e ↦ ↑(e ⊗ₜ b i)` along the `i`-th vector of a Hilbert basis `b` of `F`, as a
linear isometry. -/
noncomputable def embedRightₗᵢ (b : HilbertBasis ι 𝕜 F) (i : ι) :
    E →ₗᵢ[𝕜] Completion (E ⊗[𝕜] F) where
  toLinearMap := (embedRight (b i) : E →L[𝕜] Completion (E ⊗[𝕜] F)).toLinearMap
  norm_map' e := by simp [b.orthonormal.1 i]

@[simp]
theorem embedRightₗᵢ_apply (b : HilbertBasis ι 𝕜 F) (i : ι) (e : E) :
    b.embedRightₗᵢ E i e = (↑(e ⊗ₜ[𝕜] b i) : Completion (E ⊗[𝕜] F)) := by
  simp [embedRightₗᵢ]

theorem orthogonalFamily_embedRightₗᵢ (b : HilbertBasis ι 𝕜 F) :
    OrthogonalFamily 𝕜 (fun _ : ι ↦ E) (b.embedRightₗᵢ E) := by
  intro i j hij e₁ e₂
  simp [b.orthonormal.2 hij]

theorem isHilbertSum_embedRightₗᵢ [CompleteSpace E] (b : HilbertBasis ι 𝕜 F) :
    IsHilbertSum 𝕜 (fun _ : ι ↦ E) (b.embedRightₗᵢ E) := by
  refine IsHilbertSum.mk b.orthogonalFamily_embedRightₗᵢ ?_
  let K : Submodule 𝕜 (Completion (E ⊗[𝕜] F)) :=
    ⨆ i, LinearMap.range (b.embedRightₗᵢ E i).toLinearMap
  rw [← K.orthogonal_orthogonal_eq_closure, ← eq_top_iff, Submodule.orthogonal_eq_top_iff,
    eq_bot_iff]
  intro u hu
  refine completion_ext_iff_inner_right.mpr fun e y ↦ ?_
  let c : ι → 𝕜 := fun i ↦ b.repr y i
  have hsum : HasSum (fun i ↦ c i • (↑(e ⊗ₜ[𝕜] b i) : Completion (E ⊗[𝕜] F))) ↑(e ⊗ₜ[𝕜] y) := by
    simpa only [embedLeft_apply, map_smul] using
      (embedLeft (𝕜 := 𝕜) (F := F) e).hasSum (b.hasSum_repr y)
  have hzero : ∀ i, ⟪u, c i • (↑(e ⊗ₜ[𝕜] b i) : Completion (E ⊗[𝕜] F))⟫_𝕜 = 0 := fun i ↦
    (Submodule.mem_orthogonal' K u).mp hu _ <|
      K.smul_mem (c i) (Submodule.mem_iSup_of_mem i ⟨e, b.embedRightₗᵢ_apply i e⟩)
  have hsum' := (innerSL 𝕜 (E := Completion (E ⊗[𝕜] F)) u).hasSum hsum
  simp only [innerSL_apply_apply, hzero] at hsum'
  rw [inner_zero_left]
  exact hsum'.unique hasSum_zero

variable (E) in
/-- **Orthonormal coordinate representation of a completed Hilbert tensor product.** Given a
Hilbert basis `b : HilbertBasis ι 𝕜 F` and a complete inner product space `E`, `b.tensorReprRight E`
is the linear isometric equivalence `Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] ℓ²(ι, E)` whose `i`-th coordinate
is `sliceRight (b i)`. -/
noncomputable def tensorReprRight [CompleteSpace E] (b : HilbertBasis ι 𝕜 F) :
    Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] ℓ²(ι, E) :=
  (b.isHilbertSum_embedRightₗᵢ (E := E)).linearIsometryEquiv

@[simp]
theorem tensorReprRight_symm_single [CompleteSpace E] [DecidableEq ι]
    (b : HilbertBasis ι 𝕜 F) (i : ι) (e : E) :
    (b.tensorReprRight E).symm (lp.single 2 i e) = ↑(e ⊗ₜ[𝕜] b i) := by
  simp [tensorReprRight]

@[simp]
theorem tensorReprRight_apply_apply [CompleteSpace E] (b : HilbertBasis ι 𝕜 F)
    (u : Completion (E ⊗[𝕜] F)) (i : ι) :
    b.tensorReprRight E u i = sliceRight (b i) u := by
  classical
  refine ext_inner_left 𝕜 fun e ↦ ?_
  have hsingle : ⟪e, b.tensorReprRight E u i⟫_𝕜 =
      ⟪lp.single 2 i e, b.tensorReprRight E u⟫_𝕜 := by
    simp [lp.inner_single_left]
  have hiso := (b.tensorReprRight E).inner_map_map
    ((b.tensorReprRight E).symm (lp.single 2 i e)) u
  rw [(b.tensorReprRight E).apply_symm_apply] at hiso
  rw [hsingle, hiso, tensorReprRight_symm_single, inner_sliceRight_right]

theorem tensorReprRight_coe_tmul_apply [CompleteSpace E] (b : HilbertBasis ι 𝕜 F)
    (e : E) (y : F) (i : ι) :
    b.tensorReprRight E ↑(e ⊗ₜ[𝕜] y) i = ⟪b i, y⟫_𝕜 • e := by
  rw [tensorReprRight_apply_apply, sliceRight_coe_tmul]

/-- `b.tensorReprRight` intertwines `f.rTensorCompletion F` with `lp.ampliation ι 2 f`. -/
theorem tensorReprRight_rTensorCompletion {E' : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [CompleteSpace E] [CompleteSpace E']
    (b : HilbertBasis ι 𝕜 F) (f : E →L[𝕜] E') (u : Completion (E ⊗[𝕜] F)) :
    b.tensorReprRight E' (f.rTensorCompletion F u) =
      lp.ampliation ι 2 f (b.tensorReprRight E u) := by
  ext i
  rw [tensorReprRight_apply_apply, lp.ampliation_apply_apply, tensorReprRight_apply_apply]
  have hsl : (sliceRight (b i) : Completion (E' ⊗[𝕜] F) →L[𝕜] E') ∘L f.rTensorCompletion F =
      f ∘L sliceRight (b i) :=
    completion_continuousLinearMap_ext fun _ _ ↦ by simp
  exact DFunLike.congr_fun hsl u

private theorem orthonormal_tmul_hilbertBasis {κ : Type*}
    (b₁ : HilbertBasis ι 𝕜 E) (b₂ : HilbertBasis κ 𝕜 F) :
    Orthonormal 𝕜 fun p : ι × κ ↦ (↑(b₁ p.1 ⊗ₜ[𝕜] b₂ p.2) : Completion (E ⊗[𝕜] F)) := by
  refine ⟨fun p ↦ by simp [b₁.orthonormal.1 p.1, b₂.orthonormal.1 p.2], fun p q hpq ↦ ?_⟩
  simp only [Completion.inner_coe, TensorProduct.inner_tmul]
  rcases not_and_or.mp (mt Prod.ext_iff.mpr hpq) with h₁ | h₂
  · simp [b₁.orthonormal.2 h₁]
  · simp [b₂.orthonormal.2 h₂]

private theorem orthogonal_span_tmul_hilbertBasis_eq_bot {κ : Type*}
    (b₁ : HilbertBasis ι 𝕜 E) (b₂ : HilbertBasis κ 𝕜 F) :
    (Submodule.span 𝕜 (Set.range fun p : ι × κ ↦
      (↑(b₁ p.1 ⊗ₜ[𝕜] b₂ p.2) : Completion (E ⊗[𝕜] F))))ᗮ = ⊥ := by
  have : CompleteSpace E := b₁.completeSpace
  have : CompleteSpace F := b₂.completeSpace
  refine eq_bot_iff.mpr fun u hu ↦ ?_
  have hmem (i : ι) (j : κ) :
      ⟪(↑(b₁ i ⊗ₜ[𝕜] b₂ j) : Completion (E ⊗[𝕜] F)), u⟫_𝕜 = 0 :=
    inner_eq_zero_symm.mp ((Submodule.mem_orthogonal' _ u).mp hu _
      (Submodule.subset_span ⟨(i, j), rfl⟩))
  have hsl (i : ι) : sliceLeft (b₁ i) u = 0 := by
    refine b₂.repr.injective (lp.ext <| funext fun j ↦ ?_)
    rw [b₂.repr_apply_apply, map_zero, lp.coeFn_zero, Pi.zero_apply, inner_sliceLeft_right]
    exact hmem i j
  have hsr (y : F) : sliceRight y u = 0 := by
    refine b₁.repr.injective (lp.ext <| funext fun i ↦ ?_)
    rw [b₁.repr_apply_apply, map_zero, lp.coeFn_zero, Pi.zero_apply, inner_sliceRight_right,
      ← inner_sliceLeft_right, hsl i, inner_zero_right]
  exact completion_ext_iff_inner_left.mpr fun e y ↦ by
    rw [← inner_sliceRight_right, hsr y, inner_zero_right, inner_zero_right]

/-- **Tensor product of two Hilbert bases.** Given Hilbert bases `b₁ : HilbertBasis ι 𝕜 E` and
`b₂ : HilbertBasis κ 𝕜 F`, pure tensors `↑(b₁ i ⊗ₜ b₂ j)` form a Hilbert basis of
`Completion (E ⊗[𝕜] F)`. -/
noncomputable def tensorProduct {κ : Type*} (b₁ : HilbertBasis ι 𝕜 E) (b₂ : HilbertBasis κ 𝕜 F) :
    HilbertBasis (ι × κ) 𝕜 (Completion (E ⊗[𝕜] F)) :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_tmul_hilbertBasis b₁ b₂)
    (orthogonal_span_tmul_hilbertBasis_eq_bot b₁ b₂)

@[simp]
theorem tensorProduct_apply {κ : Type*} (b₁ : HilbertBasis ι 𝕜 E) (b₂ : HilbertBasis κ 𝕜 F)
    (p : ι × κ) :
    b₁.tensorProduct b₂ p = (↑(b₁ p.1 ⊗ₜ[𝕜] b₂ p.2) : Completion (E ⊗[𝕜] F)) :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) p

end TensorRepr

end HilbertBasis

/-! ### Ultraweak continuity of completions, `ℓ²`-ampliations, and tensor amplifications -/

namespace TauCeti.ContinuousLinearMapUltraweak

section ConjugationAndCompletion

variable {𝕜 E E' G G' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup G'] [InnerProductSpace 𝕜 G']

/-- Conjugating bounded operators by linear isometric equivalences is ultraweakly continuous, with
no completeness assumptions. -/
theorem continuous_conj_linearIsometryEquiv (U : G ≃ₗᵢ[𝕜] E) (V : E' ≃ₗᵢ[𝕜] G') :
    Continuous fun T : ContinuousLinearMapUltraweak 𝕜 E E' ↦
      ofCLM ((V : E' →L[𝕜] G') ∘L T.toCLM ∘L (U : G →L[𝕜] E)) :=
  continuous_of_continuous_inner_ampliation_apply fun ξ η ↦ by
    refine (continuous_inner_ampliation_apply
      (lp.ampliation ℕ 2 (U : G →L[𝕜] E) ξ)
      (lp.ampliation ℕ 2 (V.symm : G' →L[𝕜] E') η)).congr fun T ↦ ?_
    simp only [lp.inner_ampliation_apply, lp.ampliation_apply_apply,
      ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_coe'']
    congr 1 with n
    rw [← V.inner_map_map (V.symm (η n)) (T.toCLM (U (ξ n))), V.apply_symm_apply]

private theorem dyadic_diff_norm_le {u : Completion E} {y : ℕ → E}
    (hy : ∀ j : ℕ, dist u ↑(y j) < (1 / 8 : ℝ) ^ (j + 1) * ‖u‖) (j : ℕ) :
    ‖(match j with | 0 => y 0 | k + 1 => y (k + 1) - y k)‖ ≤ 2 * (1 / 8 : ℝ) ^ j * ‖u‖ := by
  cases j with
  | zero =>
    have h0 := hy 0
    rw [dist_eq_norm, norm_sub_rev] at h0
    have htri : ‖(↑(y 0) : Completion E)‖ ≤ ‖(↑(y 0) : Completion E) - u‖ + ‖u‖ := by
      simpa using norm_add_le ((↑(y 0) : Completion E) - u) u
    rw [Completion.norm_coe] at htri
    have hu0 : 0 ≤ ‖u‖ := norm_nonneg u
    linarith
  | succ j =>
    have hj1 := hy (j + 1)
    have hj0 := hy j
    rw [dist_eq_norm, norm_sub_rev] at hj1
    rw [dist_eq_norm] at hj0
    have htri : ‖y (j + 1) - y j‖ ≤
        ‖(↑(y (j + 1)) : Completion E) - u‖ + ‖u - (↑(y j) : Completion E)‖ := by
      rw [← Completion.norm_coe, Completion.coe_sub]
      simpa [sub_add_sub_cancel] using
        norm_add_le ((↑(y (j + 1)) : Completion E) - u) (u - ↑(y j))
    have hpow : (1 / 8 : ℝ) ^ (j + 2) * ‖u‖ + (1 / 8 : ℝ) ^ (j + 1) * ‖u‖ ≤
        2 * (1 / 8 : ℝ) ^ (j + 1) * ‖u‖ := by
      have hp : 0 ≤ (1 / 8 : ℝ) ^ (j + 1) * ‖u‖ := by positivity
      nlinarith [show (1 / 8 : ℝ) ^ (j + 2) * ‖u‖ = (1 / 8) * ((1 / 8 : ℝ) ^ (j + 1) * ‖u‖)
        by ring]
    linarith

/-- Every vector `u` in `Completion E` expands into a series `∑' j, ↑(d j)` with
`‖d j‖ ≤ 2 * (1 / 8) ^ j * ‖u‖`. -/
private theorem exists_hasSum_coe_dyadic (u : Completion E) :
    ∃ d : ℕ → E, HasSum (fun j ↦ (↑(d j) : Completion E)) u ∧
      ∀ j, ‖d j‖ ≤ 2 * (1 / 8 : ℝ) ^ j * ‖u‖ := by
  rcases eq_or_ne u 0 with rfl | hu
  · exact ⟨0, hasSum_zero, fun j ↦ by simp⟩
  choose y hy using fun j : ℕ ↦
    Metric.denseRange_iff.mp Completion.denseRange_coe u ((1 / 8 : ℝ) ^ (j + 1) * ‖u‖)
      (mul_pos (by positivity) (norm_pos_iff.mpr hu))
  let d : ℕ → E := fun j ↦ match j with | 0 => y 0 | k + 1 => y (k + 1) - y k
  have hd_norm : ∀ j, ‖d j‖ ≤ 2 * (1 / 8 : ℝ) ^ j * ‖u‖ := dyadic_diff_norm_le hy
  have hgeom : Summable fun j : ℕ ↦ 2 * (1 / 8 : ℝ) ^ j * ‖u‖ :=
    ((summable_geometric_of_lt_one (r := (1 / 8 : ℝ)) (by positivity)
      (by norm_num)).mul_left 2).mul_right ‖u‖
  have hsum_norm : Summable fun j ↦ ‖(↑(d j) : Completion E)‖ :=
    Summable.of_norm_bounded hgeom fun j ↦ by
      rw [Real.norm_of_nonneg (norm_nonneg _), Completion.norm_coe]
      exact hd_norm j
  have hpart : ∀ n, ∑ i ∈ Finset.range (n + 1), (↑(d i) : Completion E) = ↑(y n) := fun n ↦ by
    induction n with
    | zero => simp [d]
    | succ n ih => rw [Finset.sum_range_succ, ih]; simp [d, Completion.coe_sub]
  have htend : Tendsto (fun n ↦ (↑(y n) : Completion E)) atTop (𝓝 u) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hlim : Tendsto (fun n : ℕ ↦ (1 / 8 : ℝ) ^ (n + 1) * ‖u‖) atTop (𝓝 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 8 : ℝ)) (by positivity)
        (by norm_num)).comp (tendsto_add_atTop_nat 1)).mul_const ‖u‖
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hlim) ε hε
    exact ⟨N, fun n hn ↦ dist_comm (↑(y n)) u ▸ (hy n).trans (by simpa using hN n hn)⟩
  refine ⟨d, (hasSum_iff_tendsto_nat_of_summable_norm hsum_norm).mpr ?_, hd_norm⟩
  rw [← tendsto_add_atTop_iff_nat 1]
  simpa only [hpart] using htend

private theorem summable_dyadic_balanced {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
    (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hc : Summable fun n ↦ c n ^ (2 : ℝ))
    (d : ℕ → ℕ → X) (hd : ∀ n j, ‖d n j‖ ≤ 2 * (1 / 8 : ℝ) ^ j * c n) :
    Summable fun p : ℕ × ℕ × ℕ ↦
      ‖(((2 : 𝕜) ^ p.2.1 * ((2 : 𝕜)⁻¹) ^ p.2.2) • d p.1 p.2.1)‖ ^ (2 : ℝ) := by
  have hdom : Summable fun p : ℕ × ℕ × ℕ ↦
      4 * c p.1 ^ (2 : ℝ) * ((1 / 16 : ℝ) ^ p.2.1 * (1 / 4 : ℝ) ^ p.2.2) := by
    have hjk : Summable fun q : ℕ × ℕ ↦ (1 / 16 : ℝ) ^ q.1 * (1 / 4 : ℝ) ^ q.2 :=
      Summable.mul_of_nonneg
        (summable_geometric_of_lt_one (r := (1 / 16 : ℝ)) (by positivity) (by norm_num))
        (summable_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by positivity) (by norm_num))
        (fun _ ↦ by positivity) (fun _ ↦ by positivity)
    exact Summable.mul_of_nonneg (hc.mul_left 4) hjk
      (fun n ↦ mul_nonneg (by norm_num) (Real.rpow_nonneg (hc0 n) _))
      (fun _ ↦ mul_nonneg (by positivity) (by positivity))
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun ⟨n, j, k⟩ ↦ ?_) hdom
  have h14 : (2 : ℝ) ^ j * (1 / 8 : ℝ) ^ j = (1 / 4 : ℝ) ^ j := by rw [← mul_pow]; norm_num
  have h12 : ((2 : ℝ)⁻¹) ^ k = (1 / 2 : ℝ) ^ k := by norm_num
  have h16 : ((1 / 4 : ℝ) ^ j) ^ 2 = (1 / 16 : ℝ) ^ j := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h4 : ((1 / 2 : ℝ) ^ k) ^ 2 = (1 / 4 : ℝ) ^ k := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hle : ‖(((2 : 𝕜) ^ j * ((2 : 𝕜)⁻¹) ^ k) • d n j)‖ ≤
      2 * c n * ((1 / 4 : ℝ) ^ j * (1 / 2 : ℝ) ^ k) := by
    calc ‖(((2 : 𝕜) ^ j * ((2 : 𝕜)⁻¹) ^ k) • d n j)‖
        = (2 : ℝ) ^ j * ((2 : ℝ)⁻¹) ^ k * ‖d n j‖ := by simp [norm_smul]
      _ ≤ (2 : ℝ) ^ j * ((2 : ℝ)⁻¹) ^ k * (2 * (1 / 8 : ℝ) ^ j * c n) := by
          gcongr; exact hd n j
      _ = 2 * c n * (((2 : ℝ) ^ j * (1 / 8 : ℝ) ^ j) * ((2 : ℝ)⁻¹) ^ k) := by ring
      _ = 2 * c n * ((1 / 4 : ℝ) ^ j * (1 / 2 : ℝ) ^ k) := by rw [h14, h12]
  rw [Real.rpow_two, Real.rpow_two]
  calc ‖(((2 : 𝕜) ^ j * ((2 : 𝕜)⁻¹) ^ k) • d n j)‖ ^ 2
      ≤ (2 * c n * ((1 / 4 : ℝ) ^ j * (1 / 2 : ℝ) ^ k)) ^ 2 :=
        sq_le_sq' (by linarith [norm_nonneg (((2 : 𝕜) ^ j * ((2 : 𝕜)⁻¹) ^ k) • d n j)]) hle
    _ = 4 * c n ^ 2 * ((1 / 16 : ℝ) ^ j * (1 / 4 : ℝ) ^ k) := by
        rw [mul_pow, mul_pow, mul_pow, h16, h4]; ring

private theorem inner_dyadic_balanced_smul {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace 𝕜 X] (y x : X) (j k : ℕ) :
    ⟪(((2 : 𝕜)⁻¹) ^ j * (2 : 𝕜) ^ k) • y, ((2 : 𝕜) ^ j * ((2 : 𝕜)⁻¹) ^ k) • x⟫_𝕜 =
      ⟪y, x⟫_𝕜 := by
  simp only [inner_smul_left, inner_smul_right, map_mul, map_pow, map_inv₀, map_ofNat, inv_pow]
  have hj : (2 : 𝕜) ^ j ≠ 0 := pow_ne_zero j two_ne_zero
  have hk : (2 : 𝕜) ^ k ≠ 0 := pow_ne_zero k two_ne_zero
  calc _ = ((2 : 𝕜) ^ j * ((2 : 𝕜) ^ j)⁻¹) * (((2 : 𝕜) ^ k)⁻¹ * (2 : 𝕜) ^ k) * ⟪y, x⟫_𝕜 := by ring
    _ = ⟪y, x⟫_𝕜 := by rw [mul_inv_cancel₀ hj, inv_mul_cancel₀ hk, one_mul, one_mul]

private theorem tsum_inner_completion_of_hasSum (T : E →L[𝕜] E') {x : Completion E}
    {y : Completion E'} {u : ℕ → E} {v : ℕ → E'}
    (hu : HasSum (fun j ↦ (u j : Completion E)) x)
    (hv : HasSum (fun k ↦ (v k : Completion E')) y)
    (hsum : Summable fun p : ℕ × ℕ ↦ ⟪v p.2, T (u p.1)⟫_𝕜) :
    (∑' p : ℕ × ℕ, ⟪v p.2, T (u p.1)⟫_𝕜) = ⟪y, T.completion x⟫_𝕜 := by
  rw [hsum.tsum_prod]
  have h1 (j : ℕ) : ∑' k, ⟪v k, T (u j)⟫_𝕜 = ⟪y, (↑(T (u j)) : Completion E')⟫_𝕜 := by
    simpa only [innerSLFlip_apply_apply, Completion.inner_coe] using
      ((innerSLFlip 𝕜 (E := Completion E') (↑(T (u j)) : Completion E')).hasSum hv).tsum_eq
  simp_rw [h1, ← T.completion_apply_coe]
  simpa only [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using
    ((innerSL 𝕜 (E := Completion E') y ∘L T.completion).hasSum hu).tsum_eq

/-- **Ultraweak continuity of operator completion.** Extending bounded operators `E →L[𝕜] E'` to
their completions `Completion E →L[𝕜] Completion E'` is continuous for the ultraweak operator
topology, with no completeness assumptions on `E` or `E'`. -/
theorem continuous_completion :
    Continuous fun T : ContinuousLinearMapUltraweak 𝕜 E E' ↦ ofCLM T.toCLM.completion := by
  refine continuous_of_continuous_inner_ampliation_apply fun ξ η ↦ ?_
  let ξ₀ : ℕ → Completion E := fun n ↦ ξ n
  let η₀ : ℕ → Completion E' := fun n ↦ η n
  choose d hd_sum hd_norm using fun n ↦ exists_hasSum_coe_dyadic (ξ₀ n)
  choose d' hd'_sum hd'_norm using fun n ↦ exists_hasSum_coe_dyadic (η₀ n)
  let ev : (ℕ × ℕ × ℕ) ≃ ℕ :=
    (Equiv.prodCongrRight fun _ ↦ Denumerable.eqv (ℕ × ℕ)).trans (Denumerable.eqv (ℕ × ℕ))
  let a₀ : ℕ × ℕ × ℕ → E := fun ⟨n, j, k⟩ ↦ ((2 : 𝕜) ^ j * ((2 : 𝕜)⁻¹) ^ k) • d n j
  let b₀ : ℕ × ℕ × ℕ → E' := fun ⟨n, j, k⟩ ↦ (((2 : 𝕜)⁻¹) ^ j * (2 : 𝕜) ^ k) • d' n k
  have ha_sum : Summable fun p : ℕ × ℕ × ℕ ↦ ‖a₀ p‖ ^ (2 : ℝ) :=
    summable_dyadic_balanced (𝕜 := 𝕜) (fun n ↦ ‖ξ₀ n‖) (fun n ↦ norm_nonneg _)
      ((lp.memℓp ξ).summable (by norm_num)) d hd_norm
  have hb_sum : Summable fun p : ℕ × ℕ × ℕ ↦ ‖b₀ p‖ ^ (2 : ℝ) := by
    rw [← (Equiv.prodCongrRight fun _ : ℕ ↦ Equiv.prodComm ℕ ℕ).summable_iff]
    exact (summable_dyadic_balanced (𝕜 := 𝕜) (fun n ↦ ‖η₀ n‖) (fun n ↦ norm_nonneg _)
      ((lp.memℓp η).summable (by norm_num)) d' hd'_norm).congr fun ⟨n, k, j⟩ ↦ by
        simp [b₀, mul_comm]
  let ξ'₀ : ℕ → E := a₀ ∘ ev.symm
  let η'₀ : ℕ → E' := b₀ ∘ ev.symm
  have ha_mem : Memℓp ξ'₀ 2 := memℓp_gen <| by
    simpa only [ENNReal.toReal_ofNat, ξ'₀, Function.comp_def] using ev.symm.summable_iff.mpr ha_sum
  have hb_mem : Memℓp η'₀ 2 := memℓp_gen <| by
    simpa only [ENNReal.toReal_ofNat, η'₀, Function.comp_def] using ev.symm.summable_iff.mpr hb_sum
  let ξ' : ℓ²(ℕ, E) := ⟨(ξ'₀ : PreLp fun _ : ℕ ↦ E), ha_mem⟩
  let η' : ℓ²(ℕ, E') := ⟨(η'₀ : PreLp fun _ : ℕ ↦ E'), hb_mem⟩
  refine (continuous_inner_ampliation_apply ξ' η').congr fun T ↦ ?_
  refine (lp.inner_ampliation_apply T.toCLM ξ' η').trans <|
    Eq.trans ?_ (lp.inner_ampliation_apply T.toCLM.completion ξ η).symm
  change (∑' i, ⟪η'₀ i, T.toCLM (ξ'₀ i)⟫_𝕜) = ∑' n, ⟪η₀ n, T.toCLM.completion (ξ₀ n)⟫_𝕜
  rw [← ev.tsum_eq]
  have hterm : ∀ p : ℕ × ℕ × ℕ,
      ⟪η'₀ (ev p), T.toCLM (ξ'₀ (ev p))⟫_𝕜 = ⟪d' p.1 p.2.2, T.toCLM (d p.1 p.2.1)⟫_𝕜 :=
    fun ⟨n, j, k⟩ ↦ by
      simpa only [ξ'₀, η'₀, Function.comp_apply, Equiv.symm_apply_apply, a₀, b₀, map_smul] using
        inner_dyadic_balanced_smul (d' n k) (T.toCLM (d n j)) j k
  have hsum_all : Summable fun p : ℕ × ℕ × ℕ ↦ ⟪d' p.1 p.2.2, T.toCLM (d p.1 p.2.1)⟫_𝕜 := by
    have hs : Summable fun i : ℕ ↦ ⟪η'₀ i, T.toCLM (ξ'₀ i)⟫_𝕜 :=
      (lp.summable_inner η' (lp.ampliation ℕ 2 T.toCLM ξ')).congr fun i ↦ by
        rw [lp.ampliation_apply_apply]
    exact (ev.summable_iff.mpr hs).congr hterm
  rw [tsum_congr hterm, hsum_all.tsum_prod]
  exact tsum_congr fun n ↦
    tsum_inner_completion_of_hasSum T.toCLM (hd_sum n) (hd'_sum n) (hsum_all.prod_factor n)

end ConjugationAndCompletion

end TauCeti.ContinuousLinearMapUltraweak

namespace lp

variable {ι 𝕜 E E' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']

private theorem memℓp_extend_subtype_prod {X : Type*} [NormedAddCommGroup X]
    {S : Set ι} {e : ℕ × S → ℕ} (he : Function.Injective e) (f : ℕ → ι → X)
    (hrow : ∀ n, Summable fun i : ι ↦ ‖f n i‖ ^ (2 : ℝ))
    (hcol : Summable fun n : ℕ ↦ ∑' i : ι, ‖f n i‖ ^ (2 : ℝ)) :
    Memℓp (Function.extend e (fun p : ℕ × S ↦ f p.1 p.2.1) 0) 2 := by
  refine memℓp_gen ?_
  simp only [ENNReal.toReal_ofNat]
  rw [← he.summable_iff fun k hk ↦ by simp [Function.extend_apply' _ _ _ hk]]
  have hcomp : ((fun k : ℕ ↦ ‖Function.extend e (fun p : ℕ × S ↦ f p.1 p.2.1) 0 k‖ ^ (2 : ℝ)) ∘
      e) = fun p : ℕ × S ↦ ‖f p.1 p.2.1‖ ^ (2 : ℝ) := by
    ext p
    simp [he.extend_apply]
  rw [hcomp, summable_prod_of_nonneg fun _ ↦ by positivity]
  exact ⟨fun n ↦ (hrow n).comp_injective Subtype.val_injective,
    Summable.of_nonneg_of_le (fun _ ↦ tsum_nonneg fun _ ↦ by positivity)
      (fun n ↦ tsum_comp_le_tsum_of_inj (hrow n) (fun _ ↦ by positivity) Subtype.val_injective)
      hcol⟩

private theorem memℓp_extend_lp {X : Type*} [NormedAddCommGroup X]
    {S : Set ι} {e : ℕ × S → ℕ} (he : Function.Injective e) (ζ : ℓ²(ℕ, ℓ²(ι, X))) :
    Memℓp (Function.extend e (fun p : ℕ × S ↦ (ζ p.1 : ι → X) p.2.1) 0) 2 :=
  memℓp_extend_subtype_prod he (fun n i ↦ ζ n i)
    (fun n ↦ (lp.memℓp (ζ n)).summable (by norm_num))
    (((lp.memℓp ζ).summable (by norm_num)).congr fun n ↦ by
      simpa only [ENNReal.toReal_ofNat] using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (ζ n))

/-- **Ultraweak continuity of `ℓ²`-ampliations.** For any index type `ι` (not assumed countable) and
any inner product spaces `E, E'` (not assumed complete), `T ↦ lp.ampliation ι 2 T` is continuous
with respect to the ultraweak operator topologies. -/
theorem continuous_ampliation_ultraweak :
    Continuous fun T : TauCeti.ContinuousLinearMapUltraweak 𝕜 E E' ↦
      TauCeti.ContinuousLinearMapUltraweak.ofCLM (lp.ampliation ι 2 T.toCLM) := by
  refine TauCeti.ContinuousLinearMapUltraweak.continuous_of_continuous_inner_ampliation_apply
    fun ξ η ↦ ?_
  let ξ₀ : ℕ → ι → E := fun n i ↦ ξ n i
  let η₀ : ℕ → ι → E' := fun n i ↦ η n i
  let S : Set ι := ⋃ n : ℕ, Function.support (ξ₀ n)
  have hS_cnt : S.Countable := Set.countable_iUnion fun n ↦ by
    have hsup : Function.support (ξ₀ n) = Function.support (fun i : ι ↦ ‖ξ₀ n i‖ ^ (2 : ℝ)) := by
      ext i; simp
    have hs : Summable fun i : ι ↦ ‖ξ₀ n i‖ ^ (2 : ℝ) := (lp.memℓp (ξ n)).summable (by norm_num)
    exact hsup ▸ hs.countable_support
  have : Countable S := hS_cnt.to_subtype
  obtain ⟨e, he⟩ := exists_injective_nat (ℕ × S)
  let ξ'₀ : ℕ → E := Function.extend e (fun p : ℕ × S ↦ ξ₀ p.1 p.2.1) 0
  let η'₀ : ℕ → E' := Function.extend e (fun p : ℕ × S ↦ η₀ p.1 p.2.1) 0
  let ξ' : ℓ²(ℕ, E) := ⟨(ξ'₀ : PreLp fun _ : ℕ ↦ E), memℓp_extend_lp he ξ⟩
  let η' : ℓ²(ℕ, E') := ⟨(η'₀ : PreLp fun _ : ℕ ↦ E'), memℓp_extend_lp he η⟩
  refine (TauCeti.ContinuousLinearMapUltraweak.continuous_inner_ampliation_apply ξ' η').congr
    fun T ↦ ?_
  have hrhs : ⟪η, lp.ampliation ℕ 2 (lp.ampliation ι 2 T.toCLM) ξ⟫_𝕜 =
      ∑' n, ∑' i, ⟪η₀ n i, T.toCLM (ξ₀ n i)⟫_𝕜 :=
    (lp.inner_ampliation_apply _ ξ η).trans <| tsum_congr fun n ↦
      lp.inner_ampliation_apply T.toCLM (ξ n) (η n)
  have hlhs : ⟪η', lp.ampliation ℕ 2 T.toCLM ξ'⟫_𝕜 = ∑' k, ⟪η'₀ k, T.toCLM (ξ'₀ k)⟫_𝕜 :=
    lp.inner_ampliation_apply T.toCLM ξ' η'
  refine hlhs.trans (Eq.trans ?_ hrhs.symm)
  have hsupp : Function.support (fun k : ℕ ↦ ⟪η'₀ k, T.toCLM (ξ'₀ k)⟫_𝕜) ⊆ Set.range e := by
    intro k hk
    by_contra hke
    exact hk (by simp [ξ'₀, Function.extend_apply' _ _ _ hke])
  rw [← he.tsum_eq hsupp]
  have hterm : ∀ p : ℕ × S, ⟪η'₀ (e p), T.toCLM (ξ'₀ (e p))⟫_𝕜 =
      ⟪η₀ p.1 p.2.1, T.toCLM (ξ₀ p.1 p.2.1)⟫_𝕜 := fun p ↦ by
    simp [ξ'₀, η'₀, he.extend_apply]
  have hsum_k : Summable fun k : ℕ ↦ ⟪η'₀ k, T.toCLM (ξ'₀ k)⟫_𝕜 :=
    (lp.summable_inner η' (lp.ampliation ℕ 2 T.toCLM ξ')).congr fun k ↦ by
      rw [lp.ampliation_apply_apply]
  have hsum_prod : Summable fun p : ℕ × S ↦ ⟪η₀ p.1 p.2.1, T.toCLM (ξ₀ p.1 p.2.1)⟫_𝕜 :=
    (hsum_k.comp_injective he).congr hterm
  simp_rw [hterm]
  rw [hsum_prod.tsum_prod]
  refine tsum_congr fun n ↦ ?_
  have hsupp_n : Function.support (fun i : ι ↦ ⟪η₀ n i, T.toCLM (ξ₀ n i)⟫_𝕜) ⊆
      Set.range (Subtype.val : S → ι) := by
    rw [Subtype.range_coe]
    exact fun i hi ↦ Set.mem_iUnion.mpr ⟨n, fun h0 ↦ hi (by simp [h0])⟩
  exact Subtype.val_injective.tsum_eq hsupp_n

end lp

namespace ContinuousLinearMap

open TensorProduct

variable {𝕜 E E' F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- **Ultraweak continuity of right tensor amplification `f ↦ f ⊗ 1`.** Neither `E`, `E'` nor `F`
is assumed complete. -/
theorem continuous_rTensorCompletion_ultraweak :
    Continuous fun T : TauCeti.ContinuousLinearMapUltraweak 𝕜 E E' ↦
      TauCeti.ContinuousLinearMapUltraweak.ofCLM (T.toCLM.rTensorCompletion F) := by
  obtain ⟨w, b, -⟩ := exists_hilbertBasis 𝕜 (Completion F)
  let U : Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] ℓ²(w, Completion E) :=
    (completionLeftEquiv 𝕜 E F).trans
      ((completionRightEquiv 𝕜 (Completion E) F).trans (b.tensorReprRight (Completion E)))
  let U' : Completion (E' ⊗[𝕜] F) ≃ₗᵢ[𝕜] ℓ²(w, Completion E') :=
    (completionLeftEquiv 𝕜 E' F).trans
      ((completionRightEquiv 𝕜 (Completion E') F).trans (b.tensorReprRight (Completion E')))
  have hconj :=
    (TauCeti.ContinuousLinearMapUltraweak.continuous_conj_linearIsometryEquiv U U'.symm).comp
      ((lp.continuous_ampliation_ultraweak (ι := w)).comp
        (TauCeti.ContinuousLinearMapUltraweak.continuous_completion (𝕜 := 𝕜) (E := E) (E' := E')))
  refine hconj.congr fun T ↦ ?_
  ext1
  refine completion_continuousLinearMap_ext fun e y ↦ ?_
  apply U'.injective
  ext i
  simp [U, U']

/-- **Ultraweak continuity of left tensor amplification `g ↦ 1 ⊗ g`.** Neither `E`, `E'` nor `F`
is assumed complete. -/
theorem continuous_lTensorCompletion_ultraweak :
    Continuous fun T : TauCeti.ContinuousLinearMapUltraweak 𝕜 E E' ↦
      TauCeti.ContinuousLinearMapUltraweak.ofCLM (T.toCLM.lTensorCompletion F) := by
  have hconj := (TauCeti.ContinuousLinearMapUltraweak.continuous_conj_linearIsometryEquiv
    ((commIsometry 𝕜 F E).completion) ((commIsometry 𝕜 E' F).completion)).comp
      (continuous_rTensorCompletion_ultraweak (𝕜 := 𝕜) (E := E) (E' := E') (F := F))
  refine hconj.congr fun T ↦ ?_
  ext1
  exact commIsometry_completion_comp_rTensorCompletion_comp_commIsometry_completion T.toCLM

end ContinuousLinearMap
