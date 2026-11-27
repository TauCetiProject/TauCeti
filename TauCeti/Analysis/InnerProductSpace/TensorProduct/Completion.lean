/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import TauCeti.Analysis.InnerProductSpace.Completion
public import TauCeti.Analysis.InnerProductSpace.HilbertSum
public import TauCeti.Analysis.InnerProductSpace.TensorProduct.Basic
public import TauCeti.Analysis.Normed.Operator.Completion
public import TauCeti.Topology.UniformSpace.Completion
import TauCeti.Analysis.InnerProductSpace.Adjoint

/-!
# Completed tensor products of Hilbert spaces, amplified operators, and slice maps

For inner product spaces `E` and `F` over `𝕜` (`ℝ` or `ℂ`), Mathlib puts on the algebraic tensor
product `E ⊗[𝕜] F` the inner product with `⟪x ⊗ₜ y, x' ⊗ₜ y'⟫ = ⟪x, x'⟫ ⟪y, y'⟫`. Its completion
`UniformSpace.Completion (E ⊗[𝕜] F)` is the *completed Hilbert tensor product* `E ⊗̂ F`, a Hilbert
space, whether or not `E` and `F` are complete. This file develops the operators on it.

* The pure tensors `x ⊗ₜ y` span a dense subspace (`TensorProduct.dense_span_coe_tmul`), so a
  bounded (semi)linear operator out of `E ⊗̂ F` is determined by its values on them
  (`TensorProduct.completion_ext`, `TensorProduct.completion_ext_iff`), a vector
  orthogonal to all of them vanishes (`TensorProduct.eq_zero_of_forall_inner_coe_tmul`), and a
  bounded operator maps `E ⊗̂ F` into a closed submodule if it maps every pure tensor there
  (`TensorProduct.apply_mem_of_forall_apply_coe_tmul_mem`). The bounded bilinear pure-tensor
  creation map `TensorProduct.tmulCLM` has partial adjoints contracting against a vector in one
  factor and generating amplified rank-one operators (`TensorProduct.flip_tmulCLM_comp_adjoint`,
  `TensorProduct.tmulCLM_comp_adjoint`).
* A bounded operator `f : E →L[𝕜] E'` induces the bounded operator `f ⊗ 1` on `E ⊗̂ F`, the
  *amplification* `f.rTensorCompletion F`, which extends `ContinuousLinearMap.rTensor` and sends
  `x ⊗ₜ y` to `f x ⊗ₜ y`. It is the only bounded operator doing so
  (`ContinuousLinearMap.eq_rTensorCompletion_iff`). Symmetrically `g.lTensorCompletion E` is
  `1 ⊗ g`. Operators on both factors commute
  (`ContinuousLinearMap.rTensorCompletion_comp_lTensorCompletion`), and their product is the
  extension `TensorProduct.mapLCompletion f g` of `TensorProduct.mapL f g`, the tensor product
  `f ⊗ g` of the operators, which is likewise unique on pure tensors, has norm `‖f‖ * ‖g‖`
  (`TensorProduct.norm_mapLCompletion`, from `TensorProduct.norm_mapL`) and satisfies
  `(f ⊗ g)† = f† ⊗ g†` (`TensorProduct.adjoint_mapLCompletion`): if `f'` and `g'` are formal
  adjoints of `f` and `g` then `mapL f' g'` is a formal adjoint of `mapL f g`
  (`TensorProduct.inner_mapL_left`), so `ContinuousLinearMap.adjoint_completion` applies.
* Amplification preserves the operator norm when the other factor is nonzero
  (`ContinuousLinearMap.norm_rTensorCompletion`, `ContinuousLinearMap.rTensorCompletionₗᵢ`),
  composition and the identity, and it commutes with adjoints
  (`ContinuousLinearMap.adjoint_rTensorCompletion`), since `f ⊗ 1` is `f ⊗ id`
  (`ContinuousLinearMap.rTensorCompletion_eq_mapLCompletion`) and `id` is its own formal adjoint.
  When `E` is complete, `f ↦ f ⊗ 1` is therefore a unital star algebra homomorphism
  `B(E) →⋆ₐ[𝕜] B(E ⊗̂ F)` (`ContinuousLinearMap.rTensorCompletionStarAlgHom`), injective and
  isometric when `F ≠ 0`. When `F = 0` the completed tensor product is `0`, so every amplification
  is `0`.
  Composing with this homomorphism amplifies a representation `π : A → B(E)` to
  `a ↦ π a ⊗ 1` (`NonUnitalStarAlgHom.rTensorCompletion`), and symmetrically `b ↦ 1 ⊗ ρ b`
  (`NonUnitalStarAlgHom.lTensorCompletion`); the two amplifications commute.
* The flip `E ⊗ F ≃ F ⊗ E` extends to a unitary `E ⊗̂ F ≃ F ⊗̂ E`, which exchanges the two
  amplifications (`ContinuousLinearMap.lTensorCompletion_commIsometry_completion`,
  `ContinuousLinearMap.rTensorCompletion_commIsometry_completion`) and the factors of `f ⊗ g`
  (`TensorProduct.mapLCompletion_commIsometry_completion`). Scalar unit identifications
  `TensorProduct.lidIsometryCompletion` and `TensorProduct.ridIsometryCompletion` identify
  `𝕜 ⊗̂ E` and `E ⊗̂ 𝕜` with `E` when `E` is complete.
* Completing a factor first does not change the completed tensor product: `E ⊗[𝕜] F` is dense in
  `Ê ⊗[𝕜] F` (`TensorProduct.denseRange_rTensor_toComplₗᵢ`, an instance of
  `ContinuousLinearMap.denseRange_rTensor`), which gives the unitaries
  `E ⊗̂ F ≃ Ê ⊗̂ F` and `E ⊗̂ F ≃ E ⊗̂ F̂` (`TensorProduct.completionLeftIsometry`,
  `TensorProduct.completionRightIsometry`). Through them the associator of the algebraic tensor
  product extends to the unitary `(E ⊗̂ F) ⊗̂ G ≃ E ⊗̂ (F ⊗̂ G)`
  (`TensorProduct.assocIsometryCompletion`). Bounded operators out of `(E ⊗̂ F) ⊗̂ G` are
  determined by their values on `(x ⊗ₜ y) ⊗ₜ z` (`TensorProduct.completion_ext₃`), so the
  associator is the only one sending it to `x ⊗ₜ (y ⊗ₜ z)`
  (`TensorProduct.eq_assocIsometryCompletion_iff`). It is natural in each factor:
  `(f ⊗ (g ⊗ h)) ∘ assoc = assoc ∘ ((f ⊗ g) ⊗ h)`
  (`TensorProduct.mapLCompletion_mapLCompletion_assocIsometryCompletion`).
* Choosing a Hilbert basis `b` of `F` identifies `E ⊗̂ F` isometrically with the vector-valued
  Hilbert sum `ℓ²(ι, E)` (`HilbertBasis.tensorCompletionEquiv`, specialized to `ℓ²(ι, 𝕜)` in
  `TensorProduct.lpTensorCompletionEquiv`), intertwining `f ⊗ 1` with `lp.ampliation ι 2 f`.
* Vector-functional *slice maps* (Fubini maps) `TensorProduct.sliceRight` and
  `TensorProduct.sliceLeft` contract one tensor factor against a pair of vectors, satisfy bimodule
  and adjoint covariance, separate all bounded operators (`TensorProduct.ext_of_sliceRight`,
  `TensorProduct.ext_of_sliceLeft`), and characterize operators commuting with amplified rank-one
  operators (`TensorProduct.eq_rTensorCompletion_sliceRight_of_commute_rankOne`,
  `TensorProduct.eq_lTensorCompletion_sliceLeft_of_commute_rankOne`). Ultraweak continuity is proved
  in `TauCeti.Analysis.InnerProductSpace.TensorProduct.Ultraweak`.

These are the bounded operators `A ⊗ 1` and `1 ⊗ B` on tensor products of Hilbert spaces from which
spatial tensor products of operator algebras are built, and they act on tensor products of `L²`
spaces of sections, for instance in the block operators of products of elliptic operators.

## References

* J. Dixmier, *Von Neumann Algebras*, North-Holland, 1981, Part I, Chapter 2, §§3–4.
* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras*, Vols. I–II,
  Academic Press, 1983–1986, §2.6 and §11.2.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, Academic
  Press, 1980, §II.4 and §VIII.10.
* M. Takesaki, *Theory of Operator Algebras I*, Springer, 1979, Chapter IV, §1 and §5.
-/

public section

noncomputable section

open Filter UniformSpace TensorProduct
open scoped Topology InnerProduct InnerProductSpace lp

variable {𝕜 E E' E'' F F' F'' G G' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']
  [NormedAddCommGroup E''] [InnerProductSpace 𝕜 E''] [NormedAddCommGroup F]
  [InnerProductSpace 𝕜 F] [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F']
  [NormedAddCommGroup F''] [InnerProductSpace 𝕜 F''] [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup G'] [InnerProductSpace 𝕜 G']

namespace TensorProduct

variable (𝕜 E F) in
/-- The pure tensors span a dense subspace of the completed tensor product of `E` and `F`. -/
theorem dense_span_coe_tmul :
    (Submodule.span 𝕜 (Set.range fun p : E × F ↦
      ((p.1 ⊗ₜ[𝕜] p.2 : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)))).topologicalClosure = ⊤ := by
  have h : Submodule.span 𝕜 (Set.range fun p : E × F ↦
      ((p.1 ⊗ₜ[𝕜] p.2 : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F))) =
      (⊤ : Submodule 𝕜 (E ⊗[𝕜] F)).map
        ((Completion.toComplL : E ⊗[𝕜] F →L[𝕜] Completion (E ⊗[𝕜] F)) :
          E ⊗[𝕜] F →ₗ[𝕜] Completion (E ⊗[𝕜] F)) := by
    rw [← span_tmul_eq_top, Submodule.map_span]
    congr 1
    ext u
    simp
  exact h ▸ Completion.denseRange_coe.topologicalClosure_map_submodule
    (top_unique (Submodule.le_topologicalClosure _))

/-- Two continuous semilinear maps from the completed tensor product of `E` and `F` to a Hausdorff
space agree when they agree on pure tensors. -/
theorem completion_ext {𝕜₂ M : Type*} [Semiring 𝕜₂] {σ : 𝕜 →+* 𝕜₂}
    [AddCommMonoid M] [Module 𝕜₂ M] [TopologicalSpace M] [T2Space M]
    {l l' : Completion (E ⊗[𝕜] F) →SL[σ] M}
    (h : ∀ (x : E) (y : F), l (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = l' (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F)) : l = l' := by
  refine DFunLike.coe_injective <| Completion.ext l.continuous l'.continuous fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul x y => exact h x y
  | add _ _ hz₁ hz₂ => rw [Completion.coe_add, map_add, map_add, hz₁, hz₂]

/-- Two continuous semilinear maps from the completed tensor product of `E` and `F` to a Hausdorff
space agree if and only if they agree on pure tensors. -/
theorem completion_ext_iff {𝕜₂ M : Type*} [Semiring 𝕜₂] {σ : 𝕜 →+* 𝕜₂}
    [AddCommMonoid M] [Module 𝕜₂ M] [TopologicalSpace M] [T2Space M]
    {l l' : Completion (E ⊗[𝕜] F) →SL[σ] M} :
    l = l' ↔ ∀ (x : E) (y : F), l (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = l' (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) :=
  ⟨fun h _ _ ↦ h ▸ rfl, completion_ext⟩

/-- A vector of the completed tensor product that is orthogonal to every pure tensor vanishes. -/
theorem eq_zero_of_forall_inner_coe_tmul {w : Completion (E ⊗[𝕜] F)}
    (h : ∀ x y, ⟪((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)), w⟫_𝕜 = 0) : w = 0 := by
  have hw : innerSL 𝕜 w = 0 := completion_ext fun x y ↦ by
    rw [innerSL_apply_apply, ← inner_conj_symm, h, map_zero, zero_apply]
  simpa using congr($hw w)

/-- A bounded operator out of the completed tensor product maps into a closed submodule as soon as
it maps every pure tensor into it. -/
theorem apply_mem_of_forall_apply_coe_tmul_mem {M : Type*} [AddCommGroup M] [Module 𝕜 M]
    [TopologicalSpace M] {T : Completion (E ⊗[𝕜] F) →L[𝕜] M} {S : Submodule 𝕜 M}
    (hS : IsClosed (S : Set M))
    (h : ∀ x y, T ((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ∈ S)
    (w : Completion (E ⊗[𝕜] F)) : T w ∈ S := by
  have hle : Submodule.span 𝕜 (Set.range fun p : E × F ↦
      ((p.1 ⊗ₜ[𝕜] p.2 : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F))) ≤ S.comap (T : _ →ₗ[𝕜] M) :=
    Submodule.span_le.2 <| Set.range_subset_iff.2 fun p ↦ h p.1 p.2
  have htop := Submodule.topologicalClosure_minimal _ hle (hS.preimage T.continuous)
  rw [dense_span_coe_tmul] at htop
  exact htop Submodule.mem_top

section Associator

variable (𝕜 E F) in
/-- The pure tensors `x ⊗ₜ y` with `x` in `E` have dense span in `Completion E ⊗[𝕜] F`, so the
algebraic tensor product `E ⊗[𝕜] F` is dense there. -/
theorem denseRange_rTensor_toComplₗᵢ :
    DenseRange ((Completion.toComplₗᵢ (𝕜 := 𝕜) (E := E)).rTensor F) := by
  have := ContinuousLinearMap.denseRange_rTensor F
    (f := (Completion.toComplₗᵢ (𝕜 := 𝕜) (E := E)).toContinuousLinearMap) Completion.denseRange_coe
  rwa [← LinearIsometry.toContinuousLinearMap_rTensor,
    LinearIsometry.coe_toContinuousLinearMap] at this

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

/-- On the algebraic tensor product, completing the left factor is
`LinearIsometry.rTensor` of the inclusion `E → Ê`. -/
@[simp]
theorem completionLeftIsometry_coe (u : E ⊗[𝕜] F) :
    completionLeftIsometry 𝕜 E F u =
      ((Completion.toComplₗᵢ.rTensor F u : Completion E ⊗[𝕜] F) :
        Completion (Completion E ⊗[𝕜] F)) :=
  LinearIsometry.completionEquivOfDenseRange_coe _ _ u

theorem completionLeftIsometry_coe_tmul (x : E) (y : F) :
    completionLeftIsometry 𝕜 E F (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) =
      ((x : Completion E) ⊗ₜ[𝕜] y : Completion E ⊗[𝕜] F) := by
  simp

theorem completionRightIsometry_coe_tmul (x : E) (y : F) :
    completionRightIsometry 𝕜 E F (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) =
      (x ⊗ₜ[𝕜] (y : Completion F) : E ⊗[𝕜] Completion F) := by
  simp [completionRightIsometry]

/-- On the algebraic tensor product, completing the right factor is
`LinearIsometry.lTensor` of the inclusion `F → F̂`. -/
@[simp]
theorem completionRightIsometry_coe (u : E ⊗[𝕜] F) :
    completionRightIsometry 𝕜 E F u =
      ((Completion.toComplₗᵢ.lTensor E u : E ⊗[𝕜] Completion F) :
        Completion (E ⊗[𝕜] Completion F)) := by
  induction u using TensorProduct.inductionOn with
  | tmul x y => simpa using completionRightIsometry_coe_tmul x y
  | add u v hu hv => simp only [Completion.coe_add, map_add, hu, hv]

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

/-- The inverse associator sends `x ⊗ₜ (y ⊗ₜ z)` to `(x ⊗ₜ y) ⊗ₜ z`. -/
@[simp]
theorem assocIsometryCompletion_symm_coe_tmul (x : E) (y : F) (z : G) :
    (assocIsometryCompletion 𝕜 E F G).symm
        (x ⊗ₜ[𝕜] ((y ⊗ₜ[𝕜] z : F ⊗[𝕜] G) : Completion (F ⊗[𝕜] G)) :
          E ⊗[𝕜] Completion (F ⊗[𝕜] G)) =
      (((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] z :
        Completion (E ⊗[𝕜] F) ⊗[𝕜] G) :=
  (LinearIsometryEquiv.symm_apply_eq _).2 (assocIsometryCompletion_coe_tmul x y z).symm

/-- Two bounded operators from the completed tensor product of `E ⊗̂ F` and `G` to a Hausdorff
space agree when they agree on the triple pure tensors `(x ⊗ₜ y) ⊗ₜ z`. -/
theorem completion_ext₃ {M : Type*} [AddCommGroup M] [Module 𝕜 M] [TopologicalSpace M]
    [T2Space M] {l l' : Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) →L[𝕜] M}
    (h : ∀ x y z, l (((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] z :
        Completion (E ⊗[𝕜] F) ⊗[𝕜] G) =
      l' (((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] z :
        Completion (E ⊗[𝕜] F) ⊗[𝕜] G)) :
    l = l' :=
  completion_ext fun c z ↦ by
    -- For fixed `z`, both sides are bounded operators in `c`, agreeing on pure tensors `x ⊗ₜ y`.
    have hz : l ∘L Completion.toComplL ∘L (mkL 𝕜 (Completion (E ⊗[𝕜] F)) G).flip z =
        l' ∘L Completion.toComplL ∘L (mkL 𝕜 (Completion (E ⊗[𝕜] F)) G).flip z :=
      completion_ext fun x y ↦ by simpa using h x y z
    simpa using congr($hz c)

/-- The associator is the only bounded operator sending `(x ⊗ₜ y) ⊗ₜ z` to `x ⊗ₜ (y ⊗ₜ z)`. -/
theorem eq_assocIsometryCompletion_iff
    {T : Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G) →L[𝕜]
      Completion (E ⊗[𝕜] Completion (F ⊗[𝕜] G))} :
    T = (assocIsometryCompletion 𝕜 E F G : _ →L[𝕜] _) ↔
      ∀ x y z, T (((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)) ⊗ₜ[𝕜] z :
          Completion (E ⊗[𝕜] F) ⊗[𝕜] G) =
        (x ⊗ₜ[𝕜] ((y ⊗ₜ[𝕜] z : F ⊗[𝕜] G) : Completion (F ⊗[𝕜] G)) :
          E ⊗[𝕜] Completion (F ⊗[𝕜] G)) :=
  ⟨fun h x y z ↦ by simp [h], fun h ↦ completion_ext₃ fun x y z ↦ by simp [h]⟩

end Associator

section mapL

/-- The tensor product `f ⊗ g : E ⊗̂ F →L[𝕜] E' ⊗̂ F'` of bounded operators `f : E →L[𝕜] E'` and
`g : F →L[𝕜] F'` on the completed tensor products: the extension of `TensorProduct.mapL` to the
completions, sending `x ⊗ₜ y` to `f x ⊗ₜ g y`. -/
def mapLCompletion (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F') :=
  (mapL f g).completion

/-- On the algebraic tensor product, `f ⊗ g` is `TensorProduct.mapL f g`. -/
@[simp]
theorem mapLCompletion_coe (f : E →L[𝕜] E') (g : F →L[𝕜] F') (u : E ⊗[𝕜] F) :
    mapLCompletion f g u = (mapL f g u : Completion (E' ⊗[𝕜] F')) :=
  ContinuousLinearMap.completion_apply_coe _ u

/-- The tensor product `f ⊗ g` sends `x ⊗ₜ y` to `f x ⊗ₜ g y`. -/
theorem mapLCompletion_tmul (f : E →L[𝕜] E') (g : F →L[𝕜] F') (x : E) (y : F) :
    mapLCompletion f g (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = (f x ⊗ₜ[𝕜] g y : E' ⊗[𝕜] F') := by
  simp

/-- The tensor product `f ⊗ g` is the only bounded operator sending `x ⊗ₜ y` to `f x ⊗ₜ g y`. -/
theorem eq_mapLCompletion_iff {f : E →L[𝕜] E'} {g : F →L[𝕜] F'}
    {T : Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F')} :
    T = mapLCompletion f g ↔
      ∀ x y, T (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = (f x ⊗ₜ[𝕜] g y : E' ⊗[𝕜] F') :=
  ⟨fun h x y ↦ h ▸ mapLCompletion_tmul f g x y,
    fun h ↦ completion_ext fun x y ↦ by rw [h, mapLCompletion_tmul]⟩

@[simp]
theorem mapLCompletion_add_left (f₁ f₂ : E →L[𝕜] E') (g : F →L[𝕜] F') :
    mapLCompletion (f₁ + f₂) g = mapLCompletion f₁ g + mapLCompletion f₂ g :=
  completion_ext fun _ _ ↦ by simp [add_tmul, Completion.coe_add]

@[simp]
theorem mapLCompletion_add_right (f : E →L[𝕜] E') (g₁ g₂ : F →L[𝕜] F') :
    mapLCompletion f (g₁ + g₂) = mapLCompletion f g₁ + mapLCompletion f g₂ :=
  completion_ext fun _ _ ↦ by simp [tmul_add, Completion.coe_add]

@[simp]
theorem mapLCompletion_smul_left (c : 𝕜) (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    mapLCompletion (c • f) g = c • mapLCompletion f g :=
  completion_ext fun _ _ ↦ by simp [← smul_tmul', Completion.coe_smul]

@[simp]
theorem mapLCompletion_smul_right (c : 𝕜) (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    mapLCompletion f (c • g) = c • mapLCompletion f g :=
  completion_ext fun _ _ ↦ by simp [tmul_smul, Completion.coe_smul]

@[simp]
theorem mapLCompletion_neg_left (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    mapLCompletion (-f) g = -mapLCompletion f g :=
  completion_ext fun _ _ ↦ by simp [neg_tmul, Completion.coe_neg]

@[simp]
theorem mapLCompletion_neg_right (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    mapLCompletion f (-g) = -mapLCompletion f g :=
  completion_ext fun _ _ ↦ by simp [tmul_neg, Completion.coe_neg]

@[simp]
theorem mapLCompletion_sub_left (f₁ f₂ : E →L[𝕜] E') (g : F →L[𝕜] F') :
    mapLCompletion (f₁ - f₂) g = mapLCompletion f₁ g - mapLCompletion f₂ g :=
  completion_ext fun _ _ ↦ by simp [sub_tmul, Completion.coe_sub]

@[simp]
theorem mapLCompletion_sub_right (f : E →L[𝕜] E') (g₁ g₂ : F →L[𝕜] F') :
    mapLCompletion f (g₁ - g₂) = mapLCompletion f g₁ - mapLCompletion f g₂ :=
  completion_ext fun _ _ ↦ by simp [tmul_sub, Completion.coe_sub]

@[simp]
theorem mapLCompletion_zero_left (g : F →L[𝕜] F') :
    mapLCompletion (0 : E →L[𝕜] E') g = 0 :=
  completion_ext fun _ _ ↦ by simp

@[simp]
theorem mapLCompletion_zero_right (f : E →L[𝕜] E') :
    mapLCompletion f (0 : F →L[𝕜] F') = 0 :=
  completion_ext fun _ _ ↦ by simp

/-- The tensor product `f ⊗ g` has norm at most `‖f‖ * ‖g‖`. -/
theorem norm_mapLCompletion_le (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    ‖mapLCompletion f g‖ ≤ ‖f‖ * ‖g‖ :=
  (ContinuousLinearMap.norm_completion _).trans_le (norm_mapL_le f g)

/-- The tensor product `f ⊗ g` has norm `‖f‖ * ‖g‖`. -/
@[simp]
theorem norm_mapLCompletion (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    ‖mapLCompletion f g‖ = ‖f‖ * ‖g‖ :=
  (ContinuousLinearMap.norm_completion _).trans (norm_mapL f g)

/-- The tensor product of the identities is the identity: `1 ⊗ 1 = 1`. -/
@[simp]
theorem mapLCompletion_id :
    mapLCompletion (.id 𝕜 E) (.id 𝕜 F) = .id 𝕜 (Completion (E ⊗[𝕜] F)) :=
  completion_ext fun _ _ ↦ by simp

/-- The tensor product of operators respects composition:
`(f₂ ∘ f₁) ⊗ (g₂ ∘ g₁) = (f₂ ⊗ g₂) ∘ (f₁ ⊗ g₁)`. -/
theorem mapLCompletion_comp (f₂ : E' →L[𝕜] E'') (f₁ : E →L[𝕜] E') (g₂ : F' →L[𝕜] F'')
    (g₁ : F →L[𝕜] F') :
    mapLCompletion (f₂ ∘L f₁) (g₂ ∘L g₁) = mapLCompletion f₂ g₂ ∘L mapLCompletion f₁ g₁ :=
  completion_ext fun _ _ ↦ by simp

/-- The tensor product `f† ⊗ g†` is the adjoint of `f ⊗ g`. -/
@[simp]
theorem adjoint_mapLCompletion [CompleteSpace E] [CompleteSpace E'] [CompleteSpace F]
    [CompleteSpace F'] (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    (mapLCompletion f g).adjoint = mapLCompletion f.adjoint g.adjoint :=
  ContinuousLinearMap.adjoint_completion <| inner_mapL_left
    (fun x y ↦ (f.adjoint_inner_right x y).symm) fun x y ↦ (g.adjoint_inner_right x y).symm

/-- The extension of the flip `E ⊗ F ≃ F ⊗ E` to the completions exchanges the factors of a
tensor product of operators: `(g ⊗ f) ∘ flip = flip ∘ (f ⊗ g)`. -/
theorem mapLCompletion_commIsometry_completion (f : E →L[𝕜] E')
    (g : F →L[𝕜] F') (u : Completion (E ⊗[𝕜] F)) :
    mapLCompletion g f ((commIsometry 𝕜 E F).completion u) =
      (commIsometry 𝕜 E' F').completion (mapLCompletion f g u) := by
  induction u using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih u =>
    simp only [LinearIsometryEquiv.completion_apply_coe, mapLCompletion_coe]
    exact congr(($(mapL_comp_commIsometry g f) u : Completion (F' ⊗[𝕜] E')))

/-- The associator of completed tensor products is natural in each factor:
`(f ⊗ (g ⊗ h)) ∘ assoc = assoc ∘ ((f ⊗ g) ⊗ h)`. -/
theorem mapLCompletion_mapLCompletion_assocIsometryCompletion (f : E →L[𝕜] E')
    (g : F →L[𝕜] F') (h : G →L[𝕜] G') (u : Completion (Completion (E ⊗[𝕜] F) ⊗[𝕜] G)) :
    mapLCompletion f (mapLCompletion g h) (assocIsometryCompletion 𝕜 E F G u) =
      assocIsometryCompletion 𝕜 E' F' G' (mapLCompletion (mapLCompletion f g) h u) := by
  have key : mapLCompletion f (mapLCompletion g h) ∘L
      (assocIsometryCompletion 𝕜 E F G : _ →L[𝕜] _) =
        (assocIsometryCompletion 𝕜 E' F' G' : _ →L[𝕜] _) ∘L
          mapLCompletion (mapLCompletion f g) h :=
    completion_ext₃ fun x y z ↦ by simp
  exact congr($key u)

end mapL

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

variable (F) in
/-- The amplification `f ⊗ 1` is the tensor product of `f` with the identity. -/
theorem rTensorCompletion_eq_mapLCompletion (f : E →L[𝕜] E') :
    f.rTensorCompletion F = mapLCompletion f (.id 𝕜 F) :=
  congrArg completion (f.rTensor_eq_mapL F)

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
    ‖f.rTensorCompletion F‖ = ‖f‖ :=
  (norm_completion _).trans (norm_rTensor _)

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

/-- The amplifications of the orthogonal projections onto a subspace and onto its orthogonal
complement add up to the identity: `Π ⊗ 1 + Πᗮ ⊗ 1 = 1`. -/
theorem rTensorCompletion_starProjection_add_rTensorCompletion_starProjection_orthogonal
    (K : Submodule 𝕜 E) [K.HasOrthogonalProjection] :
    K.starProjection.rTensorCompletion F + Kᗮ.starProjection.rTensorCompletion F =
      ContinuousLinearMap.id 𝕜 (Completion (E ⊗[𝕜] F)) := by
  rw [← rTensorCompletion_add, ← K.id_eq_sum_starProjection_self_orthogonalComplement,
    rTensorCompletion_id]

/-- Every amplification to the zero space is zero. -/
theorem rTensorCompletion_of_subsingleton [Subsingleton F] (f : E →L[𝕜] E') :
    f.rTensorCompletion F = 0 :=
  completion_ext fun x y ↦ by simp [Subsingleton.elim y 0]

variable (F) in
/-- The amplification `f† ⊗ 1` is the adjoint of `f ⊗ 1`. -/
@[simp]
theorem adjoint_rTensorCompletion [CompleteSpace E] [CompleteSpace E'] (f : E →L[𝕜] E') :
    adjoint (f.rTensorCompletion F) = (adjoint f).rTensorCompletion F := by
  rw [rTensorCompletion_eq_mapLCompletion, rTensorCompletion_eq_mapLCompletion]
  exact adjoint_completion <|
    inner_mapL_left (fun x y ↦ (f.adjoint_inner_right x y).symm) fun _ _ ↦ rfl

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

variable (E) in
/-- The amplification `1 ⊗ g` is the tensor product of the identity with `g`. -/
theorem lTensorCompletion_eq_mapLCompletion (g : F →L[𝕜] F') :
    g.lTensorCompletion E = mapLCompletion (.id 𝕜 E) g :=
  congrArg completion (g.lTensor_eq_mapL E)

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
    ‖g.lTensorCompletion E‖ = ‖g‖ :=
  (norm_completion _).trans (norm_lTensor _)

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

/-- The amplifications of the orthogonal projections onto a subspace and onto its orthogonal
complement add up to the identity: `1 ⊗ Π + 1 ⊗ Πᗮ = 1`. -/
theorem lTensorCompletion_starProjection_add_lTensorCompletion_starProjection_orthogonal
    (K : Submodule 𝕜 F) [K.HasOrthogonalProjection] :
    K.starProjection.lTensorCompletion E + Kᗮ.starProjection.lTensorCompletion E =
      ContinuousLinearMap.id 𝕜 (Completion (E ⊗[𝕜] F)) := by
  rw [← lTensorCompletion_add, ← K.id_eq_sum_starProjection_self_orthogonalComplement,
    lTensorCompletion_id]

/-- Every amplification from the zero space is zero. -/
theorem lTensorCompletion_of_subsingleton [Subsingleton E] (g : F →L[𝕜] F') :
    g.lTensorCompletion E = 0 :=
  completion_ext fun x y ↦ by simp [Subsingleton.elim x 0]

variable (E) in
/-- The amplification `1 ⊗ g†` is the adjoint of `1 ⊗ g`. -/
@[simp]
theorem adjoint_lTensorCompletion [CompleteSpace F] [CompleteSpace F'] (g : F →L[𝕜] F') :
    adjoint (g.lTensorCompletion E) = (adjoint g).lTensorCompletion E := by
  rw [lTensorCompletion_eq_mapLCompletion, lTensorCompletion_eq_mapLCompletion]
  exact adjoint_completion <|
    inner_mapL_left (fun _ _ ↦ rfl) fun x y ↦ (g.adjoint_inner_right x y).symm

end lTensor

/-- Amplifications on the two factors commute, with product the tensor product of the operators:
`(f ⊗ 1) ∘ (1 ⊗ g) = f ⊗ g`. -/
theorem rTensorCompletion_comp_lTensorCompletion (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    f.rTensorCompletion F' ∘L g.lTensorCompletion E = mapLCompletion f g :=
  completion_ext fun _ _ ↦ by simp

/-- Amplifications on the two factors commute, with product the tensor product of the operators:
`(1 ⊗ g) ∘ (f ⊗ 1) = f ⊗ g`. -/
theorem lTensorCompletion_comp_rTensorCompletion (f : E →L[𝕜] E') (g : F →L[𝕜] F') :
    g.lTensorCompletion E' ∘L f.rTensorCompletion F = mapLCompletion f g :=
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
  rw [lTensorCompletion_eq_mapLCompletion, rTensorCompletion_eq_mapLCompletion]
  exact mapLCompletion_commIsometry_completion f (.id 𝕜 F) u

/-- The extension of the flip `E ⊗ F ≃ F ⊗ E` to the completions exchanges the two
amplifications: `(g ⊗ 1) ∘ flip = flip ∘ (1 ⊗ g)`. -/
theorem rTensorCompletion_commIsometry_completion (g : F →L[𝕜] F') (u : Completion (E ⊗[𝕜] F)) :
    g.rTensorCompletion E ((commIsometry 𝕜 E F).completion u) =
      (commIsometry 𝕜 E F').completion (g.lTensorCompletion E u) := by
  rw [rTensorCompletion_eq_mapLCompletion, lTensorCompletion_eq_mapLCompletion]
  exact mapLCompletion_commIsometry_completion (.id 𝕜 E) g u

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

@[simp]
theorem rTensorCompletion_pow (f : E →L[𝕜] E) (n : ℕ) :
    (f ^ n).rTensorCompletion F = f.rTensorCompletion F ^ n := by
  induction n <;> simp [pow_succ, rTensorCompletion_mul, *]

@[simp]
theorem lTensorCompletion_pow (g : F →L[𝕜] F) (n : ℕ) :
    (g ^ n).lTensorCompletion E = g.lTensorCompletion E ^ n := by
  induction n <;> simp [pow_succ, lTensorCompletion_mul, *]

variable (𝕜 E E' F) in
/-- `f ↦ f.rTensorCompletion F` bundled as a linear isometry when `F` is nontrivial. -/
def rTensorCompletionₗᵢ [Nontrivial F] :
    (E →L[𝕜] E') →ₗᵢ[𝕜] (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E' ⊗[𝕜] F)) where
  toLinearMap := ⟨⟨rTensorCompletion F, rTensorCompletion_add⟩, rTensorCompletion_smul⟩
  norm_map' := norm_rTensorCompletion

@[simp]
theorem rTensorCompletionₗᵢ_apply [Nontrivial F] (f : E →L[𝕜] E') :
    rTensorCompletionₗᵢ 𝕜 E E' F f = f.rTensorCompletion F := (rfl)

variable (𝕜 E F F') in
/-- `g ↦ g.lTensorCompletion E` bundled as a linear isometry when `E` is nontrivial. -/
def lTensorCompletionₗᵢ [Nontrivial E] :
    (F →L[𝕜] F') →ₗᵢ[𝕜] (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F')) where
  toLinearMap := ⟨⟨lTensorCompletion E, lTensorCompletion_add⟩, lTensorCompletion_smul⟩
  norm_map' := norm_lTensorCompletion

@[simp]
theorem lTensorCompletionₗᵢ_apply [Nontrivial E] (g : F →L[𝕜] F') :
    lTensorCompletionₗᵢ 𝕜 E F F' g = g.lTensorCompletion E := (rfl)

@[simp]
theorem rTensorCompletion_inj [Nontrivial F] {f₁ f₂ : E →L[𝕜] E'} :
    f₁.rTensorCompletion F = f₂.rTensorCompletion F ↔ f₁ = f₂ :=
  (rTensorCompletionₗᵢ 𝕜 E E' F).injective.eq_iff

@[simp]
theorem lTensorCompletion_inj [Nontrivial E] {g₁ g₂ : F →L[𝕜] F'} :
    g₁.lTensorCompletion E = g₂.lTensorCompletion E ↔ g₁ = g₂ :=
  (lTensorCompletionₗᵢ 𝕜 E F F').injective.eq_iff

@[simp]
theorem star_rTensorCompletion [CompleteSpace E] (f : E →L[𝕜] E) :
    star (f.rTensorCompletion F) = (star f).rTensorCompletion F := by
  simp only [star_eq_adjoint, adjoint_rTensorCompletion]

@[simp]
theorem star_lTensorCompletion [CompleteSpace F] (g : F →L[𝕜] F) :
    star (g.lTensorCompletion E) = (star g).lTensorCompletion E := by
  simp only [star_eq_adjoint, adjoint_lTensorCompletion]

end ContinuousLinearMap

/-! ### Amplifications of representations -/

namespace NonUnitalStarAlgHom

variable {A B : Type*} [NonUnitalRing A] [StarRing A] [Module 𝕜 A] [NonUnitalRing B] [StarRing B]
  [Module 𝕜 B] [CompleteSpace E] [CompleteSpace F]

variable (F) in
/-- The **left amplification** `a ↦ π a ⊗ 1` of a representation `π : A → B(E)` to the completed
tensor product `E ⊗̂ F`. -/
def rTensorCompletion (π : A →⋆ₙₐ[𝕜] (E →L[𝕜] E)) :
    A →⋆ₙₐ[𝕜] (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F)) :=
  (ContinuousLinearMap.rTensorCompletionStarAlgHom 𝕜 E F).toNonUnitalStarAlgHom.comp π

variable (E) in
/-- The **right amplification** `b ↦ 1 ⊗ ρ b` of a representation `ρ : B → B(F)` to the completed
tensor product `E ⊗̂ F`. -/
def lTensorCompletion (ρ : B →⋆ₙₐ[𝕜] (F →L[𝕜] F)) :
    B →⋆ₙₐ[𝕜] (Completion (E ⊗[𝕜] F) →L[𝕜] Completion (E ⊗[𝕜] F)) :=
  (ContinuousLinearMap.lTensorCompletionStarAlgHom 𝕜 E F).toNonUnitalStarAlgHom.comp ρ

omit [CompleteSpace F] in
/-- The left amplification of `π` sends `a` to `π a ⊗ 1`. -/
@[simp]
theorem rTensorCompletion_apply (π : A →⋆ₙₐ[𝕜] (E →L[𝕜] E)) (a : A) :
    π.rTensorCompletion F a = (π a).rTensorCompletion F :=
  ContinuousLinearMap.rTensorCompletionStarAlgHom_apply (π a)

omit [CompleteSpace E] in
/-- The right amplification of `ρ` sends `b` to `1 ⊗ ρ b`. -/
@[simp]
theorem lTensorCompletion_apply (ρ : B →⋆ₙₐ[𝕜] (F →L[𝕜] F)) (b : B) :
    ρ.lTensorCompletion E b = (ρ b).lTensorCompletion E :=
  ContinuousLinearMap.lTensorCompletionStarAlgHom_apply (ρ b)

/-- The amplifications `π a ⊗ 1` and `1 ⊗ ρ b` commute. -/
theorem commute_rTensorCompletion_lTensorCompletion (π : A →⋆ₙₐ[𝕜] (E →L[𝕜] E))
    (ρ : B →⋆ₙₐ[𝕜] (F →L[𝕜] F)) (a : A) (b : B) :
    Commute (π.rTensorCompletion F a) (ρ.lTensorCompletion E b) := by
  rw [rTensorCompletion_apply, lTensorCompletion_apply]
  exact ContinuousLinearMap.commute_rTensorCompletion_lTensorCompletion (π a) (ρ b)

end NonUnitalStarAlgHom

namespace TensorProduct

/-! ### Inner-product extensionality, pure-tensor creation maps, and rank-one operators -/

/-- Vectors in `Completion (E ⊗[𝕜] F)` are determined by right inner products with pure tensors. -/
theorem ext_iff_completion_inner_tmul_right {u v : Completion (E ⊗[𝕜] F)} :
    u = v ↔ ∀ (x : E) (y : F), ⟪u, (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F)⟫_𝕜 = ⟪v, (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F)⟫_𝕜 := by
  rw [← innerSL_inj (𝕜 := 𝕜), completion_ext_iff]; simp

/-- Vectors in `Completion (E ⊗[𝕜] F)` are determined by left inner products with pure tensors. -/
theorem ext_iff_completion_inner_tmul_left {u v : Completion (E ⊗[𝕜] F)} :
    u = v ↔ ∀ (x : E) (y : F), ⟪((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)), u⟫_𝕜 =
      ⟪((x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) : Completion (E ⊗[𝕜] F)), v⟫_𝕜 := by
  simp_rw [ext_iff_completion_inner_tmul_right (𝕜 := 𝕜), ← inner_conj_symm u, ← inner_conj_symm v,
    (starRingEnd 𝕜).injective.eq_iff]

/-- `Completion (E ⊗[𝕜] F)` is nontrivial if and only if both `E` and `F` are nontrivial. -/
theorem nontrivial_completion_iff :
    Nontrivial (Completion (E ⊗[𝕜] F)) ↔ Nontrivial E ∧ Nontrivial F := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨_, _⟩ ↦ ?_⟩
  · contrapose! h; infer_instance
  · contrapose! h; infer_instance
  · obtain ⟨x, hx⟩ := exists_ne (0 : E)
    obtain ⟨y, hy⟩ := exists_ne (0 : F)
    have : Nontrivial (E ⊗[𝕜] F) :=
      nontrivial_of_ne (x ⊗ₜ[𝕜] y) 0 (norm_ne_zero_iff.mp <| by simp [hx, hy])
    infer_instance

variable (𝕜 E F) in
/-- The canonical bounded bilinear map `(x, y) ↦ ↑(x ⊗ₜ[𝕜] y)` into `Completion (E ⊗[𝕜] F)`. -/
def tmulCLM : E →L[𝕜] F →L[𝕜] Completion (E ⊗[𝕜] F) :=
  (ContinuousLinearMap.compL 𝕜 F (E ⊗[𝕜] F) _ Completion.toComplL).comp (mkL 𝕜 E F)

@[simp]
theorem tmulCLM_apply (x : E) (y : F) :
    tmulCLM 𝕜 E F x y = (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) := by simp [tmulCLM]

theorem norm_tmulCLM_apply_le (x : E) : ‖tmulCLM 𝕜 E F x‖ ≤ ‖x‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg x) fun _ ↦ by simp

theorem norm_flip_tmulCLM_apply_le (y : F) : ‖(tmulCLM 𝕜 E F).flip y‖ ≤ ‖y‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg y) fun _ ↦ by simp [mul_comm]

@[simp]
theorem adjoint_flip_tmulCLM_tmul [CompleteSpace E] (ξ y : F) (x : E) :
    ((tmulCLM 𝕜 E F).flip ξ).adjoint (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = ⟪ξ, y⟫_𝕜 • x :=
  ext_inner_left 𝕜 fun _ ↦ by
    simp [ContinuousLinearMap.adjoint_inner_right, inner_smul_right, mul_comm]

@[simp]
theorem adjoint_tmulCLM_tmul [CompleteSpace F] (e x : E) (y : F) :
    (tmulCLM 𝕜 E F e).adjoint (x ⊗ₜ[𝕜] y : E ⊗[𝕜] F) = ⟪e, x⟫_𝕜 • y :=
  ext_inner_left 𝕜 fun _ ↦ by simp [ContinuousLinearMap.adjoint_inner_right, inner_smul_right]

/-- Right pure-tensor creation composed with another's adjoint is `1 ⊗ |η⟩⟨ξ|`. -/
theorem flip_tmulCLM_comp_adjoint [CompleteSpace E] (ξ η : F) :
    (tmulCLM 𝕜 E F).flip η ∘L ((tmulCLM 𝕜 E F).flip ξ).adjoint =
      (InnerProductSpace.rankOne 𝕜 η ξ).lTensorCompletion E :=
  completion_ext fun _ _ ↦ by simp

/-- Left pure-tensor creation composed with another's adjoint is `|e₂⟩⟨e₁| ⊗ 1`. -/
theorem tmulCLM_comp_adjoint [CompleteSpace F] (e₁ e₂ : E) :
    tmulCLM 𝕜 E F e₂ ∘L (tmulCLM 𝕜 E F e₁).adjoint =
      (InnerProductSpace.rankOne 𝕜 e₂ e₁).rTensorCompletion F :=
  completion_ext fun _ _ ↦ by simp [← smul_tmul', Completion.coe_smul]

theorem mapLCompletion_mul (f₁ f₂ : E →L[𝕜] E) (g₁ g₂ : F →L[𝕜] F) :
    mapLCompletion (f₁ * f₂) (g₁ * g₂) = mapLCompletion f₁ g₁ * mapLCompletion f₂ g₂ :=
  mapLCompletion_comp f₁ f₂ g₁ g₂

@[simp]
theorem star_mapLCompletion [CompleteSpace E] [CompleteSpace F]
    (f : E →L[𝕜] E) (g : F →L[𝕜] F) :
    star (mapLCompletion f g) = mapLCompletion (star f) (star g) := by
  simp only [ContinuousLinearMap.star_eq_adjoint, adjoint_mapLCompletion]

/-! ### Conjugation along flip, scalar units, partial completions, and the associator -/

@[simp]
theorem conjStarAlgEquiv_commIsometry_completion_rTensorCompletion (f : E →L[𝕜] E) :
    (commIsometry 𝕜 E F).completion.conjStarAlgEquiv (f.rTensorCompletion F) =
      f.lTensorCompletion F :=
  completion_ext fun _ _ ↦ by
    simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.completion_apply_coe]

@[simp]
theorem conjStarAlgEquiv_commIsometry_completion_lTensorCompletion (g : F →L[𝕜] F) :
    (commIsometry 𝕜 E F).completion.conjStarAlgEquiv (g.lTensorCompletion E) =
      g.rTensorCompletion E :=
  completion_ext fun _ _ ↦ by
    simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.completion_apply_coe]

variable (𝕜 E) in
/-- Left scalar unit identification `Completion (𝕜 ⊗[𝕜] E) ≃ₗᵢ[𝕜] E` for complete `E`, extending
`TensorProduct.lidIsometry`. -/
def lidIsometryCompletion [CompleteSpace E] : Completion (𝕜 ⊗[𝕜] E) ≃ₗᵢ[𝕜] E :=
  (lidIsometry 𝕜 E).toLinearEquiv.extendOfIsometry Completion.toComplₗᵢ.toLinearMap LinearMap.id
    Completion.denseRange_coe Function.surjective_id.denseRange fun _ ↦ by simp

@[simp]
theorem lidIsometryCompletion_tmul [CompleteSpace E] (c : 𝕜) (x : E) :
    lidIsometryCompletion 𝕜 E (c ⊗ₜ[𝕜] x : 𝕜 ⊗[𝕜] E) = c • x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ (c ⊗ₜ[𝕜] x)

@[simp]
theorem lidIsometryCompletion_symm_apply [CompleteSpace E] (x : E) :
    (lidIsometryCompletion 𝕜 E).symm x = ((1 : 𝕜) ⊗ₜ[𝕜] x : 𝕜 ⊗[𝕜] E) :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ x

theorem lidIsometryCompletion_comp_lTensorCompletion [CompleteSpace E] [CompleteSpace F]
    (f : E →L[𝕜] F) : (lidIsometryCompletion 𝕜 F : _ →L[𝕜] F) ∘L f.lTensorCompletion 𝕜 =
      f ∘L (lidIsometryCompletion 𝕜 E : _ →L[𝕜] E) :=
  completion_ext fun _ _ ↦ by simp

@[simp]
theorem conjStarAlgEquiv_lidIsometryCompletion_lTensorCompletion [CompleteSpace E]
    (f : E →L[𝕜] E) :
    (lidIsometryCompletion 𝕜 E).conjStarAlgEquiv (f.lTensorCompletion 𝕜) = f := by
  ext; simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

variable (𝕜 E) in
/-- Right scalar unit identification `Completion (E ⊗[𝕜] 𝕜) ≃ₗᵢ[𝕜] E` for complete `E`, extending
`TensorProduct.ridIsometry`. -/
def ridIsometryCompletion [CompleteSpace E] : Completion (E ⊗[𝕜] 𝕜) ≃ₗᵢ[𝕜] E :=
  (ridIsometry 𝕜 E).toLinearEquiv.extendOfIsometry Completion.toComplₗᵢ.toLinearMap LinearMap.id
    Completion.denseRange_coe Function.surjective_id.denseRange fun _ ↦ by simp

@[simp]
theorem ridIsometryCompletion_tmul [CompleteSpace E] (x : E) (c : 𝕜) :
    ridIsometryCompletion 𝕜 E (x ⊗ₜ[𝕜] c : E ⊗[𝕜] 𝕜) = c • x :=
  LinearEquiv.extendOfIsometry_eq _ _ _ _ _ _ (x ⊗ₜ[𝕜] c)

@[simp]
theorem ridIsometryCompletion_symm_apply [CompleteSpace E] (x : E) :
    (ridIsometryCompletion 𝕜 E).symm x = (x ⊗ₜ[𝕜] (1 : 𝕜) : E ⊗[𝕜] 𝕜) :=
  LinearEquiv.extendOfIsometry_symm_eq _ _ _ _ _ _ x

theorem ridIsometryCompletion_comp_rTensorCompletion [CompleteSpace E] [CompleteSpace F]
    (f : E →L[𝕜] F) : (ridIsometryCompletion 𝕜 F : _ →L[𝕜] F) ∘L f.rTensorCompletion 𝕜 =
      f ∘L (ridIsometryCompletion 𝕜 E : _ →L[𝕜] E) :=
  completion_ext fun _ _ ↦ by simp

@[simp]
theorem conjStarAlgEquiv_ridIsometryCompletion_rTensorCompletion [CompleteSpace E]
    (f : E →L[𝕜] E) :
    (ridIsometryCompletion 𝕜 E).conjStarAlgEquiv (f.rTensorCompletion 𝕜) = f := by
  ext; simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

theorem completionLeftIsometry_comp_lTensorCompletion (g : F →L[𝕜] F') :
    (completionLeftIsometry 𝕜 E F' : _ →L[𝕜] _) ∘L g.lTensorCompletion E =
      g.lTensorCompletion (Completion E) ∘L (completionLeftIsometry 𝕜 E F : _ →L[𝕜] _) :=
  completion_ext fun _ _ ↦ by simp

theorem completionRightIsometry_comp_rTensorCompletion (f : E →L[𝕜] E') :
    (completionRightIsometry 𝕜 E' F : _ →L[𝕜] _) ∘L f.rTensorCompletion F =
      f.rTensorCompletion (Completion F) ∘L (completionRightIsometry 𝕜 E F : _ →L[𝕜] _) :=
  completion_ext fun _ _ ↦ by simp

theorem assocIsometryCompletion_comp_rTensorCompletion_rTensorCompletion (f : E →L[𝕜] E') :
    (assocIsometryCompletion 𝕜 E' F G : _ →L[𝕜] _) ∘L (f.rTensorCompletion F).rTensorCompletion G =
      f.rTensorCompletion (Completion (F ⊗[𝕜] G)) ∘L
        (assocIsometryCompletion 𝕜 E F G : _ →L[𝕜] _) :=
  completion_ext₃ fun _ _ _ ↦ by simp

theorem assocIsometryCompletion_comp_lTensorCompletion_rTensorCompletion (g : F →L[𝕜] F') :
    (assocIsometryCompletion 𝕜 E F' G : _ →L[𝕜] _) ∘L (g.lTensorCompletion E).rTensorCompletion G =
      (g.rTensorCompletion G).lTensorCompletion E ∘L
        (assocIsometryCompletion 𝕜 E F G : _ →L[𝕜] _) :=
  completion_ext₃ fun _ _ _ ↦ by simp

theorem assocIsometryCompletion_comp_lTensorCompletion (h : G →L[𝕜] G') :
    (assocIsometryCompletion 𝕜 E F G' : _ →L[𝕜] _) ∘L h.lTensorCompletion (Completion (E ⊗[𝕜] F)) =
      (h.lTensorCompletion F).lTensorCompletion E ∘L
        (assocIsometryCompletion 𝕜 E F G : _ →L[𝕜] _) :=
  completion_ext₃ fun _ _ _ ↦ by simp

@[simp]
theorem conjStarAlgEquiv_assocIsometryCompletion_rTensorCompletion_rTensorCompletion
    (f : E →L[𝕜] E) : (assocIsometryCompletion 𝕜 E F G).conjStarAlgEquiv
      ((f.rTensorCompletion F).rTensorCompletion G) =
      f.rTensorCompletion (Completion (F ⊗[𝕜] G)) := by
  ext w
  simpa [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] using
    congr($(assocIsometryCompletion_comp_rTensorCompletion_rTensorCompletion f)
      ((assocIsometryCompletion 𝕜 E F G).symm w))

@[simp]
theorem conjStarAlgEquiv_assocIsometryCompletion_lTensorCompletion_rTensorCompletion
    (g : F →L[𝕜] F) : (assocIsometryCompletion 𝕜 E F G).conjStarAlgEquiv
      ((g.lTensorCompletion E).rTensorCompletion G) =
      (g.rTensorCompletion G).lTensorCompletion E := by
  ext w
  simpa [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] using
    congr($(assocIsometryCompletion_comp_lTensorCompletion_rTensorCompletion g)
      ((assocIsometryCompletion 𝕜 E F G).symm w))

@[simp]
theorem conjStarAlgEquiv_assocIsometryCompletion_lTensorCompletion (h : G →L[𝕜] G) :
    (assocIsometryCompletion 𝕜 E F G).conjStarAlgEquiv
      (h.lTensorCompletion (Completion (E ⊗[𝕜] F))) =
      (h.lTensorCompletion F).lTensorCompletion E := by
  ext w
  simpa [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply] using
    congr($(assocIsometryCompletion_comp_lTensorCompletion h)
      ((assocIsometryCompletion 𝕜 E F G).symm w))

end TensorProduct

/-! ### Vector-valued `ℓ²` coordinates -/

namespace HilbertBasis

section Coordinates

variable {ι : Type*}

variable (E) in
/-- The `i`-th fiberwise isometric embedding `x ↦ ↑(x ⊗ₜ b i)` of `E` into `Completion (E ⊗[𝕜] F)`
associated to a Hilbert basis `b` of `F`. -/
def tensorCompletionFiber (b : HilbertBasis ι 𝕜 F) (i : ι) :
    E →ₗᵢ[𝕜] Completion (E ⊗[𝕜] F) :=
  { ((tmulCLM 𝕜 E F).flip (b i)).toLinearMap with norm_map' x := by simp [b.orthonormal.1 i] }

@[simp]
theorem tensorCompletionFiber_apply (b : HilbertBasis ι 𝕜 F) (i : ι) (x : E) :
    b.tensorCompletionFiber E i x = (x ⊗ₜ[𝕜] b i : E ⊗[𝕜] F) :=
  tmulCLM_apply x (b i)

variable [CompleteSpace E] [CompleteSpace E']

variable (E) in
/-- For a Hilbert basis `b` of `F`, the fiberwise embeddings `x ↦ ↑(x ⊗ₜ b i)` exhibit
`Completion (E ⊗[𝕜] F)` as the Hilbert sum of `ι`-indexed copies of `E`. -/
theorem isHilbertSum_tensorCompletionFiber (b : HilbertBasis ι 𝕜 F) :
    IsHilbertSum 𝕜 (fun _ : ι ↦ E) (b.tensorCompletionFiber E) := by
  refine IsHilbertSum.mk (fun _ _ hij _ _ ↦ by simp [b.orthonormal.2 hij]) ?_
  rw [← dense_span_coe_tmul 𝕜 E F]
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 ?_)
    (Submodule.isClosed_topologicalClosure _)
  rintro _ ⟨⟨x, y⟩, rfl⟩
  exact mem_closure_of_tendsto ((b.hasSum_repr y).mapL (tmulCLM 𝕜 E F x))
    (Eventually.of_forall fun _ ↦ sum_mem fun i _ ↦
      Submodule.mem_iSup_of_mem i ⟨b.repr y i • x, by simp⟩)

variable (E) in
/-- **Vector-valued `ℓ²` identification of a completed tensor product.** A Hilbert basis `b` of `F`
identifies `Completion (E ⊗[𝕜] F)` isometrically with `ℓ²(ι, E)`, sending `(x ⊗ₜ y : E ⊗[𝕜] F)` to
the sequence `i ↦ ⟪b i, y⟫ • x`. -/
def tensorCompletionEquiv (b : HilbertBasis ι 𝕜 F) :
    Completion (E ⊗[𝕜] F) ≃ₗᵢ[𝕜] ℓ²(ι, E) :=
  (b.isHilbertSum_tensorCompletionFiber E).linearIsometryEquiv

@[simp]
theorem tensorCompletionEquiv_symm_single [DecidableEq ι] (b : HilbertBasis ι 𝕜 F) (i : ι)
    (x : E) : (b.tensorCompletionEquiv E).symm (lp.single 2 i x) = (x ⊗ₜ[𝕜] b i : E ⊗[𝕜] F) :=
  ((b.isHilbertSum_tensorCompletionFiber E).linearIsometryEquiv_symm_apply_single x).trans
    (b.tensorCompletionFiber_apply i x)

@[simp]
theorem tensorCompletionEquiv_tmul_apply (b : HilbertBasis ι 𝕜 F) (x : E) (y : F) (i : ι) :
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

/-- Under `HilbertBasis.tensorCompletionEquiv`, left-factor amplification `f.rTensorCompletion F`
(`f ⊗ 1`) becomes the Hilbert-sum ampliation `lp.ampliation ι 2 f`. -/
theorem tensorCompletionEquiv_comp_rTensorCompletion (b : HilbertBasis ι 𝕜 F) (f : E →L[𝕜] E') :
    (b.tensorCompletionEquiv E' : _ →L[𝕜] _) ∘L f.rTensorCompletion F =
      lp.ampliation ι 2 f ∘L (b.tensorCompletionEquiv E : _ →L[𝕜] _) :=
  completion_ext fun _ _ ↦ by ext; simp

end Coordinates

end HilbertBasis

namespace TensorProduct

section lpTensor

/-- Canonical isometric identification `Completion (E ⊗[𝕜] ℓ²(ι, 𝕜)) ≃ₗᵢ[𝕜] ℓ²(ι, E)` for a
Hilbert space `E` and any index type `ι`. -/
def lpTensorCompletionEquiv (𝕜 ι E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E] : Completion (E ⊗[𝕜] ℓ²(ι, 𝕜)) ≃ₗᵢ[𝕜] ℓ²(ι, E) :=
  (HilbertBasis.ofRepr (.refl 𝕜 ℓ²(ι, 𝕜))).tensorCompletionEquiv E

variable {ι : Type*} [CompleteSpace E] [CompleteSpace F]

@[simp]
theorem lpTensorCompletionEquiv_tmul_apply (x : E) (ξ : ℓ²(ι, 𝕜)) (i : ι) :
    lpTensorCompletionEquiv 𝕜 ι E (x ⊗ₜ[𝕜] ξ : E ⊗[𝕜] ℓ²(ι, 𝕜)) i = ξ i • x :=
  (HilbertBasis.ofRepr (.refl 𝕜 ℓ²(ι, 𝕜))).tensorCompletionEquiv_tmul_apply x ξ i

@[simp]
theorem lpTensorCompletionEquiv_symm_single [DecidableEq ι] (i : ι) (x : E) :
    (lpTensorCompletionEquiv 𝕜 ι E).symm (lp.single 2 i x) =
      (x ⊗ₜ[𝕜] lp.single 2 i (1 : 𝕜) : E ⊗[𝕜] ℓ²(ι, 𝕜)) := by
  rw [lpTensorCompletionEquiv, HilbertBasis.tensorCompletionEquiv_symm_single]
  congr 2
  exact (HilbertBasis.ofRepr (.refl 𝕜 ℓ²(ι, 𝕜))).repr_self i

theorem lpTensorCompletionEquiv_comp_rTensorCompletion (f : E →L[𝕜] F) :
    (lpTensorCompletionEquiv 𝕜 ι F : _ →L[𝕜] _) ∘L f.rTensorCompletion ℓ²(ι, 𝕜) =
      lp.ampliation ι 2 f ∘L (lpTensorCompletionEquiv 𝕜 ι E : _ →L[𝕜] _) :=
  (HilbertBasis.ofRepr (.refl 𝕜 ℓ²(ι, 𝕜))).tensorCompletionEquiv_comp_rTensorCompletion f

end lpTensor

/-! ### Vector-functional slice maps (Fubini maps) -/

section Slice

variable {E₁ E₂ E₃ F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup E₁] [InnerProductSpace 𝕜 E₁] [NormedAddCommGroup E₂] [InnerProductSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [InnerProductSpace 𝕜 E₃] [NormedAddCommGroup F₁] [InnerProductSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace 𝕜 F₂] [NormedAddCommGroup F₃] [InnerProductSpace 𝕜 F₃]

/-- **Right slice map** `R_{ξ, η}` (for complete `E₂`): contracts the right tensor factor against
`ξ ∈ F₁` and `η ∈ F₂`, characterized by `⟪x₂, sliceRight ξ η T x₁⟫ = ⟪↑(x₂ ⊗ₜ η), T ↑(x₁ ⊗ₜ ξ)⟫`. -/
def sliceRight [CompleteSpace E₂] (ξ : F₁) (η : F₂) :
    (Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) →L[𝕜] (E₁ →L[𝕜] E₂) :=
  LinearMap.mkContinuous
    { toFun := fun T ↦ ((tmulCLM 𝕜 E₂ F₂).flip η).adjoint ∘L T ∘L (tmulCLM 𝕜 E₁ F₁).flip ξ
      map_add' := fun _ _ ↦ by ext; simp, map_smul' := fun _ _ ↦ by ext; simp }
    (‖ξ‖ * ‖η‖) fun T ↦ (ContinuousLinearMap.norm_adjoint_comp_comp_le _ T _).trans <| by
      rw [mul_comm ‖ξ‖, mul_right_comm]
      gcongr; exacts [norm_flip_tmulCLM_apply_le η, norm_flip_tmulCLM_apply_le ξ]

/-- **Left slice map** `L_{e₁, e₂}` (for complete `F₂`): contracts the left tensor factor against
`e₁ ∈ E₁` and `e₂ ∈ E₂`, characterized by
`⟪y₂, sliceLeft e₁ e₂ T y₁⟫ = ⟪↑(e₂ ⊗ₜ y₂), T ↑(e₁ ⊗ₜ y₁)⟫`. -/
def sliceLeft [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) :
    (Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) →L[𝕜] (F₁ →L[𝕜] F₂) :=
  LinearMap.mkContinuous
    { toFun := fun T ↦ (tmulCLM 𝕜 E₂ F₂ e₂).adjoint ∘L T ∘L tmulCLM 𝕜 E₁ F₁ e₁
      map_add' := fun _ _ ↦ by ext; simp, map_smul' := fun _ _ ↦ by ext; simp }
    (‖e₁‖ * ‖e₂‖) fun T ↦ (ContinuousLinearMap.norm_adjoint_comp_comp_le _ T _).trans <| by
      rw [mul_comm ‖e₁‖, mul_right_comm]
      gcongr; exacts [norm_tmulCLM_apply_le e₂, norm_tmulCLM_apply_le e₁]

section SliceLemmas

variable (T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂))

theorem sliceRight_apply [CompleteSpace E₂] (ξ : F₁) (η : F₂) :
    sliceRight ξ η T = ((tmulCLM 𝕜 E₂ F₂).flip η).adjoint ∘L T ∘L (tmulCLM 𝕜 E₁ F₁).flip ξ := (rfl)

theorem sliceLeft_apply [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) :
    sliceLeft e₁ e₂ T = (tmulCLM 𝕜 E₂ F₂ e₂).adjoint ∘L T ∘L tmulCLM 𝕜 E₁ F₁ e₁ := (rfl)

@[simp]
theorem inner_sliceRight_apply [CompleteSpace E₂] (ξ : F₁) (η : F₂) (x₁ : E₁) (x₂ : E₂) :
    ⟪x₂, sliceRight ξ η T x₁⟫_𝕜 =
      ⟪((x₂ ⊗ₜ[𝕜] η : E₂ ⊗[𝕜] F₂) : Completion (E₂ ⊗[𝕜] F₂)), T (x₁ ⊗ₜ[𝕜] ξ : E₁ ⊗[𝕜] F₁)⟫_𝕜 := by
  simp [sliceRight_apply, ContinuousLinearMap.adjoint_inner_right]

@[simp]
theorem inner_sliceLeft_apply [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) (y₁ : F₁) (y₂ : F₂) :
    ⟪y₂, sliceLeft e₁ e₂ T y₁⟫_𝕜 =
      ⟪((e₂ ⊗ₜ[𝕜] y₂ : E₂ ⊗[𝕜] F₂) : Completion (E₂ ⊗[𝕜] F₂)), T (e₁ ⊗ₜ[𝕜] y₁ : E₁ ⊗[𝕜] F₁)⟫_𝕜 := by
  simp [sliceLeft_apply, ContinuousLinearMap.adjoint_inner_right]

theorem norm_sliceRight_le [CompleteSpace E₂] (ξ : F₁) (η : F₂) :
    ‖(sliceRight ξ η : _ →L[𝕜] E₁ →L[𝕜] E₂)‖ ≤ ‖ξ‖ * ‖η‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

theorem norm_sliceLeft_le [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) :
    ‖(sliceLeft e₁ e₂ : _ →L[𝕜] F₁ →L[𝕜] F₂)‖ ≤ ‖e₁‖ * ‖e₂‖ :=
  LinearMap.mkContinuous_norm_le _ (by positivity) _

theorem norm_sliceRight_apply_le [CompleteSpace E₂] (ξ : F₁) (η : F₂) :
    ‖sliceRight ξ η T‖ ≤ ‖T‖ * ‖ξ‖ * ‖η‖ := by
  rw [sliceRight_apply, mul_right_comm, mul_comm ‖T‖]
  exact (ContinuousLinearMap.norm_adjoint_comp_comp_le _ T _).trans <| by
    gcongr; exacts [norm_flip_tmulCLM_apply_le η, norm_flip_tmulCLM_apply_le ξ]

theorem norm_sliceLeft_apply_le [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) :
    ‖sliceLeft e₁ e₂ T‖ ≤ ‖T‖ * ‖e₁‖ * ‖e₂‖ := by
  rw [sliceLeft_apply, mul_right_comm, mul_comm ‖T‖]
  exact (ContinuousLinearMap.norm_adjoint_comp_comp_le _ T _).trans <| by
    gcongr; exacts [norm_tmulCLM_apply_le e₂, norm_tmulCLM_apply_le e₁]

@[simp]
theorem adjoint_sliceRight [CompleteSpace E₁] [CompleteSpace E₂] (ξ : F₁) (η : F₂) :
    (sliceRight ξ η T).adjoint = sliceRight η ξ T.adjoint := by
  simp [sliceRight_apply, ContinuousLinearMap.comp_assoc]

@[simp]
theorem adjoint_sliceLeft [CompleteSpace F₁] [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) :
    (sliceLeft e₁ e₂ T).adjoint = sliceLeft e₂ e₁ T.adjoint := by
  simp [sliceLeft_apply, ContinuousLinearMap.comp_assoc]

end SliceLemmas

@[simp] theorem sliceRight_zero_left [CompleteSpace E₂] (η : F₂) :
    (sliceRight (0 : F₁) η : _ →L[𝕜] E₁ →L[𝕜] E₂) = 0 := by ext; simp [sliceRight_apply]
@[simp] theorem sliceRight_zero_right [CompleteSpace E₂] (ξ : F₁) :
    (sliceRight ξ (0 : F₂) : _ →L[𝕜] E₁ →L[𝕜] E₂) = 0 := by ext; simp [sliceRight_apply]
theorem sliceRight_add_left [CompleteSpace E₂] (ξ₁ ξ₂ : F₁) (η : F₂) :
    (sliceRight (ξ₁ + ξ₂) η : _ →L[𝕜] E₁ →L[𝕜] E₂) = sliceRight ξ₁ η + sliceRight ξ₂ η := by
  ext; simp [sliceRight_apply]
theorem sliceRight_add_right [CompleteSpace E₂] (ξ : F₁) (η₁ η₂ : F₂) :
    (sliceRight ξ (η₁ + η₂) : _ →L[𝕜] E₁ →L[𝕜] E₂) = sliceRight ξ η₁ + sliceRight ξ η₂ := by
  ext; simp [sliceRight_apply]
theorem sliceRight_smul_left [CompleteSpace E₂] (c : 𝕜) (ξ : F₁) (η : F₂) :
    (sliceRight (c • ξ) η : _ →L[𝕜] E₁ →L[𝕜] E₂) = c • sliceRight ξ η := by
  ext; simp [sliceRight_apply]
theorem sliceRight_smul_right [CompleteSpace E₂] (c : 𝕜) (ξ : F₁) (η : F₂) :
    (sliceRight ξ (c • η) : _ →L[𝕜] E₁ →L[𝕜] E₂) = star c • sliceRight ξ η := by
  ext; simp [sliceRight_apply, map_smulₛₗ]
theorem sliceRight_neg_left [CompleteSpace E₂] (ξ : F₁) (η : F₂) :
    (sliceRight (-ξ) η : _ →L[𝕜] E₁ →L[𝕜] E₂) = -sliceRight ξ η := by ext; simp [sliceRight_apply]
theorem sliceRight_neg_right [CompleteSpace E₂] (ξ : F₁) (η : F₂) :
    (sliceRight ξ (-η) : _ →L[𝕜] E₁ →L[𝕜] E₂) = -sliceRight ξ η := by ext; simp [sliceRight_apply]
theorem sliceRight_sub_left [CompleteSpace E₂] (ξ₁ ξ₂ : F₁) (η : F₂) :
    (sliceRight (ξ₁ - ξ₂) η : _ →L[𝕜] E₁ →L[𝕜] E₂) = sliceRight ξ₁ η - sliceRight ξ₂ η := by
  ext; simp [sliceRight_apply, sub_eq_add_neg]
theorem sliceRight_sub_right [CompleteSpace E₂] (ξ : F₁) (η₁ η₂ : F₂) :
    (sliceRight ξ (η₁ - η₂) : _ →L[𝕜] E₁ →L[𝕜] E₂) = sliceRight ξ η₁ - sliceRight ξ η₂ := by
  ext; simp [sliceRight_apply, sub_eq_add_neg]

@[simp] theorem sliceLeft_zero_left [CompleteSpace F₂] (e₂ : E₂) :
    (sliceLeft (0 : E₁) e₂ : _ →L[𝕜] F₁ →L[𝕜] F₂) = 0 := by ext; simp [sliceLeft_apply]
@[simp] theorem sliceLeft_zero_right [CompleteSpace F₂] (e₁ : E₁) :
    (sliceLeft e₁ (0 : E₂) : _ →L[𝕜] F₁ →L[𝕜] F₂) = 0 := by ext; simp [sliceLeft_apply]
theorem sliceLeft_add_left [CompleteSpace F₂] (e₁ e₁' : E₁) (e₂ : E₂) :
    (sliceLeft (e₁ + e₁') e₂ : _ →L[𝕜] F₁ →L[𝕜] F₂) = sliceLeft e₁ e₂ + sliceLeft e₁' e₂ := by
  ext; simp [sliceLeft_apply]
theorem sliceLeft_add_right [CompleteSpace F₂] (e₁ : E₁) (e₂ e₂' : E₂) :
    (sliceLeft e₁ (e₂ + e₂') : _ →L[𝕜] F₁ →L[𝕜] F₂) = sliceLeft e₁ e₂ + sliceLeft e₁ e₂' := by
  ext; simp [sliceLeft_apply]
theorem sliceLeft_smul_left [CompleteSpace F₂] (c : 𝕜) (e₁ : E₁) (e₂ : E₂) :
    (sliceLeft (c • e₁) e₂ : _ →L[𝕜] F₁ →L[𝕜] F₂) = c • sliceLeft e₁ e₂ := by
  ext; simp [sliceLeft_apply]
theorem sliceLeft_smul_right [CompleteSpace F₂] (c : 𝕜) (e₁ : E₁) (e₂ : E₂) :
    (sliceLeft e₁ (c • e₂) : _ →L[𝕜] F₁ →L[𝕜] F₂) = star c • sliceLeft e₁ e₂ := by
  ext; simp [sliceLeft_apply, map_smulₛₗ]
theorem sliceLeft_neg_left [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) :
    (sliceLeft (-e₁) e₂ : _ →L[𝕜] F₁ →L[𝕜] F₂) = -sliceLeft e₁ e₂ := by ext; simp [sliceLeft_apply]
theorem sliceLeft_neg_right [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂) :
    (sliceLeft e₁ (-e₂) : _ →L[𝕜] F₁ →L[𝕜] F₂) = -sliceLeft e₁ e₂ := by ext; simp [sliceLeft_apply]
theorem sliceLeft_sub_left [CompleteSpace F₂] (e₁ e₁' : E₁) (e₂ : E₂) :
    (sliceLeft (e₁ - e₁') e₂ : _ →L[𝕜] F₁ →L[𝕜] F₂) = sliceLeft e₁ e₂ - sliceLeft e₁' e₂ := by
  ext; simp [sliceLeft_apply, sub_eq_add_neg]
theorem sliceLeft_sub_right [CompleteSpace F₂] (e₁ : E₁) (e₂ e₂' : E₂) :
    (sliceLeft e₁ (e₂ - e₂') : _ →L[𝕜] F₁ →L[𝕜] F₂) = sliceLeft e₁ e₂ - sliceLeft e₁ e₂' := by
  ext; simp [sliceLeft_apply, sub_eq_add_neg]

@[simp] theorem sliceRight_mapLCompletion [CompleteSpace E₂] (ξ : F₁) (η : F₂)
    (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) :
    sliceRight ξ η (mapLCompletion f g) = ⟪η, g ξ⟫_𝕜 • f := by ext; simp [sliceRight_apply]
@[simp] theorem sliceLeft_mapLCompletion [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂)
    (f : E₁ →L[𝕜] E₂) (g : F₁ →L[𝕜] F₂) :
    sliceLeft e₁ e₂ (mapLCompletion f g) = ⟪e₂, f e₁⟫_𝕜 • g := by ext; simp [sliceLeft_apply]
@[simp] theorem sliceRight_rTensorCompletion [CompleteSpace E₂] (ξ η : F₁) (f : E₁ →L[𝕜] E₂) :
    sliceRight ξ η (f.rTensorCompletion F₁) = ⟪η, ξ⟫_𝕜 • f := by
  simp [ContinuousLinearMap.rTensorCompletion_eq_mapLCompletion]
@[simp] theorem sliceRight_lTensorCompletion [CompleteSpace E₁] (ξ : F₁) (η : F₂)
    (g : F₁ →L[𝕜] F₂) : sliceRight ξ η (g.lTensorCompletion E₁) = ⟪η, g ξ⟫_𝕜 • .id 𝕜 E₁ := by
  simp [ContinuousLinearMap.lTensorCompletion_eq_mapLCompletion]
@[simp] theorem sliceLeft_lTensorCompletion [CompleteSpace F₂] (e₁ e₂ : E₁) (g : F₁ →L[𝕜] F₂) :
    sliceLeft e₁ e₂ (g.lTensorCompletion E₁) = ⟪e₂, e₁⟫_𝕜 • g := by
  simp [ContinuousLinearMap.lTensorCompletion_eq_mapLCompletion]
@[simp] theorem sliceLeft_rTensorCompletion [CompleteSpace F₁] (e₁ : E₁) (e₂ : E₂)
    (f : E₁ →L[𝕜] E₂) : sliceLeft e₁ e₂ (f.rTensorCompletion F₁) = ⟪e₂, f e₁⟫_𝕜 • .id 𝕜 F₁ := by
  simp [ContinuousLinearMap.rTensorCompletion_eq_mapLCompletion]
theorem sliceRight_rTensorCompletion_of_norm_eq_one [CompleteSpace E₂] {ξ : F₁} (hξ : ‖ξ‖ = 1)
    (f : E₁ →L[𝕜] E₂) : sliceRight ξ ξ (f.rTensorCompletion F₁) = f := by simp [hξ]
theorem sliceLeft_lTensorCompletion_of_norm_eq_one [CompleteSpace F₂] {e : E₁} (he : ‖e‖ = 1)
    (g : F₁ →L[𝕜] F₂) : sliceLeft e e (g.lTensorCompletion E₁) = g := by simp [he]

/-- Flip transport swaps right and left slice maps across heterogeneous completed tensor factors. -/
theorem sliceRight_commIsometry_completion_comp_comp [CompleteSpace F₂] (e₁ : E₁) (e₂ : E₂)
    (T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) :
    sliceRight e₁ e₂ (((commIsometry 𝕜 E₂ F₂).completion : _ →L[𝕜] _) ∘L T ∘L
      ((commIsometry 𝕜 F₁ E₁).completion : _ →L[𝕜] _)) = sliceLeft e₁ e₂ T := by
  ext y₁
  refine ext_inner_left 𝕜 fun y₂ ↦ ?_
  simp only [inner_sliceRight_apply, inner_sliceLeft_apply, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_coe'', LinearIsometryEquiv.completion_apply_coe, commIsometry_apply,
    comm_tmul]
  have hcomm : ((y₂ ⊗ₜ[𝕜] e₂ : F₂ ⊗[𝕜] E₂) : Completion (F₂ ⊗[𝕜] E₂)) =
      (commIsometry 𝕜 E₂ F₂).completion (e₂ ⊗ₜ[𝕜] y₂ : E₂ ⊗[𝕜] F₂) := by simp
  rw [hcomm, LinearIsometryEquiv.inner_map_map]

theorem sliceLeft_commIsometry_completion_comp_comp [CompleteSpace E₂] (ξ : F₁) (η : F₂)
    (T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) :
    sliceLeft ξ η (((commIsometry 𝕜 E₂ F₂).completion : _ →L[𝕜] _) ∘L T ∘L
      ((commIsometry 𝕜 F₁ E₁).completion : _ →L[𝕜] _)) = sliceRight ξ η T := by
  ext x₁
  refine ext_inner_left 𝕜 fun x₂ ↦ ?_
  simp only [inner_sliceLeft_apply, inner_sliceRight_apply, ContinuousLinearMap.comp_apply,
    LinearIsometryEquiv.coe_coe'', LinearIsometryEquiv.completion_apply_coe, commIsometry_apply,
    comm_tmul]
  have hcomm : ((η ⊗ₜ[𝕜] x₂ : F₂ ⊗[𝕜] E₂) : Completion (F₂ ⊗[𝕜] E₂)) =
      (commIsometry 𝕜 E₂ F₂).completion (x₂ ⊗ₜ[𝕜] η : E₂ ⊗[𝕜] F₂) := by simp
  rw [hcomm, LinearIsometryEquiv.inner_map_map]

/-- Right slice maps are right module homomorphisms over operators on the left factor. -/
theorem sliceRight_comp_rTensorCompletion [CompleteSpace E₃] (ξ : F₁) (η : F₂)
    (T : Completion (E₂ ⊗[𝕜] F₁) →L[𝕜] Completion (E₃ ⊗[𝕜] F₂)) (f : E₁ →L[𝕜] E₂) :
    sliceRight ξ η (T ∘L f.rTensorCompletion F₁) = sliceRight ξ η T ∘L f := by
  ext; exact ext_inner_left 𝕜 fun _ ↦ by simp

/-- Right slice maps are left module homomorphisms over operators on the left factor. -/
theorem sliceRight_rTensorCompletion_comp [CompleteSpace E₂] [CompleteSpace E₃] (ξ : F₁) (η : F₂)
    (f : E₂ →L[𝕜] E₃) (T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) :
    sliceRight ξ η (f.rTensorCompletion F₂ ∘L T) = f ∘L sliceRight ξ η T := by
  ext; exact ext_inner_left 𝕜 fun _ ↦ by simp [← ContinuousLinearMap.adjoint_inner_left]

/-- Left slice maps are right module homomorphisms over operators on the right factor. -/
theorem sliceLeft_comp_lTensorCompletion [CompleteSpace F₃] (e₁ : E₁) (e₂ : E₂)
    (T : Completion (E₁ ⊗[𝕜] F₂) →L[𝕜] Completion (E₂ ⊗[𝕜] F₃)) (g : F₁ →L[𝕜] F₂) :
    sliceLeft e₁ e₂ (T ∘L g.lTensorCompletion E₁) = sliceLeft e₁ e₂ T ∘L g := by
  ext; exact ext_inner_left 𝕜 fun _ ↦ by simp

/-- Left slice maps are left module homomorphisms over operators on the right factor. -/
theorem sliceLeft_lTensorCompletion_comp [CompleteSpace F₂] [CompleteSpace F₃] (e₁ : E₁) (e₂ : E₂)
    (g : F₂ →L[𝕜] F₃) (T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)) :
    sliceLeft e₁ e₂ (g.lTensorCompletion E₂ ∘L T) = g ∘L sliceLeft e₁ e₂ T := by
  ext; exact ext_inner_left 𝕜 fun _ ↦ by simp [← ContinuousLinearMap.adjoint_inner_left]

section EndSlice

variable (T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₁ ⊗[𝕜] F₁))

@[simp]
theorem sliceRight_conjStarAlgEquiv_commIsometry_completion [CompleteSpace F₁]
    (e₁ e₂ : E₁) : sliceRight e₁ e₂ ((commIsometry 𝕜 E₁ F₁).completion.conjStarAlgEquiv T) =
      sliceLeft e₁ e₂ T := by
  rw [← sliceRight_commIsometry_completion_comp_comp]
  congr 1
  ext; simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

@[simp]
theorem sliceLeft_conjStarAlgEquiv_commIsometry_completion [CompleteSpace E₁] (ξ η : F₁) :
    sliceLeft ξ η ((commIsometry 𝕜 E₁ F₁).completion.conjStarAlgEquiv T) = sliceRight ξ η T := by
  rw [← sliceLeft_commIsometry_completion_comp_comp]
  congr 1
  ext; simp [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply]

theorem sliceRight_mul_rTensorCompletion [CompleteSpace E₁] (ξ η : F₁) (f : E₁ →L[𝕜] E₁) :
    sliceRight ξ η (T * f.rTensorCompletion F₁) = sliceRight ξ η T * f :=
  sliceRight_comp_rTensorCompletion ξ η T f

theorem sliceRight_rTensorCompletion_mul [CompleteSpace E₁] (ξ η : F₁) (f : E₁ →L[𝕜] E₁) :
    sliceRight ξ η (f.rTensorCompletion F₁ * T) = f * sliceRight ξ η T :=
  sliceRight_rTensorCompletion_comp ξ η f T

theorem sliceLeft_mul_lTensorCompletion [CompleteSpace F₁] (e₁ e₂ : E₁) (g : F₁ →L[𝕜] F₁) :
    sliceLeft e₁ e₂ (T * g.lTensorCompletion E₁) = sliceLeft e₁ e₂ T * g :=
  sliceLeft_comp_lTensorCompletion e₁ e₂ T g

theorem sliceLeft_lTensorCompletion_mul [CompleteSpace F₁] (e₁ e₂ : E₁) (g : F₁ →L[𝕜] F₁) :
    sliceLeft e₁ e₂ (g.lTensorCompletion E₁ * T) = g * sliceLeft e₁ e₂ T :=
  sliceLeft_lTensorCompletion_comp e₁ e₂ g T

@[simp]
theorem star_sliceRight [CompleteSpace E₁] (ξ η : F₁) :
    star (sliceRight ξ η T) = sliceRight η ξ (star T) := adjoint_sliceRight T ξ η

@[simp]
theorem star_sliceLeft [CompleteSpace F₁] (e₁ e₂ : E₁) :
    star (sliceLeft e₁ e₂ T) = sliceLeft e₂ e₁ (star T) := adjoint_sliceLeft T e₁ e₂

end EndSlice

/-- When `E₂` is complete, right slice maps separate all bounded operators between completed tensor
products. -/
theorem ext_of_sliceRight [CompleteSpace E₂]
    {S T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)}
    (h : ∀ (ξ : F₁) (η : F₂), sliceRight ξ η S = sliceRight ξ η T) : S = T :=
  completion_ext fun x₁ ξ ↦ ext_iff_completion_inner_tmul_left.2 fun x₂ η ↦ by
    rw [← inner_sliceRight_apply, ← inner_sliceRight_apply, h]

/-- When `F₂` is complete, left slice maps separate all bounded operators between completed tensor
products. -/
theorem ext_of_sliceLeft [CompleteSpace F₂]
    {S T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₂ ⊗[𝕜] F₂)}
    (h : ∀ (e₁ : E₁) (e₂ : E₂), sliceLeft e₁ e₂ S = sliceLeft e₁ e₂ T) : S = T :=
  completion_ext fun e₁ y₁ ↦ ext_iff_completion_inner_tmul_left.2 fun e₂ y₂ ↦ by
    rw [← inner_sliceLeft_apply, ← inner_sliceLeft_apply, h]

/-- An operator commuting with all `1 ⊗ |y⟩⟨ξ₀|` (`‖ξ₀‖ = 1`) equals `(sliceRight ξ₀ ξ₀ T) ⊗ 1`. -/
theorem eq_rTensorCompletion_sliceRight_of_commute_rankOne [CompleteSpace E₁]
    {T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₁ ⊗[𝕜] F₁)} {ξ₀ : F₁} (hξ₀ : ‖ξ₀‖ = 1)
    (hcomm : ∀ y : F₁, (InnerProductSpace.rankOne 𝕜 y ξ₀).lTensorCompletion E₁ * T =
      T * (InnerProductSpace.rankOne 𝕜 y ξ₀).lTensorCompletion E₁) :
    T = (sliceRight ξ₀ ξ₀ T).rTensorCompletion F₁ := by
  refine ContinuousLinearMap.eq_rTensorCompletion_iff.2 fun x y ↦ ?_
  have hy : ((x ⊗ₜ[𝕜] y : E₁ ⊗[𝕜] F₁) : Completion (E₁ ⊗[𝕜] F₁)) =
      (InnerProductSpace.rankOne 𝕜 y ξ₀).lTensorCompletion E₁ (x ⊗ₜ[𝕜] ξ₀ : E₁ ⊗[𝕜] F₁) := by
    simp [hξ₀]
  rw [hy, ← mul_apply_eq_comp, ← hcomm y, mul_apply_eq_comp, ← flip_tmulCLM_comp_adjoint]
  simp [sliceRight_apply]

/-- An operator commuting with all `|x⟩⟨e₀| ⊗ 1` (`‖e₀‖ = 1`) equals `1 ⊗ (sliceLeft e₀ e₀ T)`. -/
theorem eq_lTensorCompletion_sliceLeft_of_commute_rankOne [CompleteSpace F₁]
    {T : Completion (E₁ ⊗[𝕜] F₁) →L[𝕜] Completion (E₁ ⊗[𝕜] F₁)} {e₀ : E₁} (he₀ : ‖e₀‖ = 1)
    (hcomm : ∀ x : E₁, (InnerProductSpace.rankOne 𝕜 x e₀).rTensorCompletion F₁ * T =
      T * (InnerProductSpace.rankOne 𝕜 x e₀).rTensorCompletion F₁) :
    T = (sliceLeft e₀ e₀ T).lTensorCompletion E₁ := by
  refine ContinuousLinearMap.eq_lTensorCompletion_iff.2 fun x y ↦ ?_
  have hx : ((x ⊗ₜ[𝕜] y : E₁ ⊗[𝕜] F₁) : Completion (E₁ ⊗[𝕜] F₁)) =
      (InnerProductSpace.rankOne 𝕜 x e₀).rTensorCompletion F₁ (e₀ ⊗ₜ[𝕜] y : E₁ ⊗[𝕜] F₁) := by
    simp [he₀]
  rw [hx, ← mul_apply_eq_comp, ← hcomm x, mul_apply_eq_comp, ← tmulCLM_comp_adjoint]
  simp [sliceLeft_apply]

end Slice

end TensorProduct
