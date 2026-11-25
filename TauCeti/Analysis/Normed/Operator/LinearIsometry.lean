/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import TauCeti.Topology.Algebra.SeparationQuotient.Basic

/-!
# Linear independence, postcomposition, and separation-quotient lifts of linear isometries

A linear isometry is injective, so composing an indexed family or a pair of vectors with a linear
isometry preserves linear independence (`LinearIsometry.linearIndependent_iff` and
`LinearIsometry.linearIndependent_pair_iff`).

Postcomposition by a (semilinear) isometry `i` acts pointwise on continuous linear maps, and
its image consists precisely of the operators whose values lie in the range of `i`
(`LinearIsometry.range_postcomp`). Consequently, if the range of `i` is closed, the
postcomposition operator also has closed range (`LinearIsometry.isClosed_range_postcomp`).
This lets regularity of an operator-valued map be checked after a closed isometric embedding
of the codomain, for instance of alternating maps into multilinear maps. We also record
submodule codomain restriction (`LinearIsometry.codRestrict`) and dense-range surjectivity for
complete domains (`LinearIsometry.surjective_of_denseRange`, `LinearIsometry.equivOfDenseRange`).

Dually, precomposition with a linear isometric equivalence `e : E ≃ₗᵢ[𝕜] F` is a linear isometric
equivalence `LinearIsometryEquiv.precomp G e : (F →L[𝕜] G) ≃ₗᵢ[𝕜] (E →L[𝕜] G)` for any seminormed
target `G`. Taking `G = 𝕜` gives contravariant functoriality of the continuous dual on linear
isometric equivalences, used to pass between duals and biduals of submodules and quotients.
Conjugating an operator by a linear isometric equivalence preserves its distance to the identity
(`LinearIsometryEquiv.norm_comp_comp_symm_sub_id`).

Also defines `SeparationQuotient.liftₗᵢ`, descending any semilinear isometry `E →ₛₗᵢ[σ₁₂] F`
into a separated normed module `F` to `SeparationQuotient E →ₛₗᵢ[σ₁₂] F`, together with its
characteristic, uniqueness, and auxiliary scalar-equivariance lemmas.
-/

public section

open Set
open scoped Matrix

namespace LinearIsometry

section LinearIndependent

variable {R ι E F : Type*} [Semiring R] [NormedAddCommGroup E] [SeminormedAddCommGroup F]
  [Module R E] [Module R F] (l : E →ₗᵢ[R] F)

/-- A linear isometry preserves linear independence of an indexed family. -/
@[simp]
protected theorem linearIndependent_iff {v : ι → E} :
    LinearIndependent R (l ∘ v) ↔ LinearIndependent R v :=
  l.toLinearMap.linearIndependent_iff_of_injOn l.injective.injOn

/-- A linear isometry preserves linear independence of a pair. -/
@[simp]
theorem linearIndependent_pair_iff {u v : E} :
    LinearIndependent R ![l u, l v] ↔ LinearIndependent R ![u, v] := by
  have hcomp : (![l u, l v] : Fin 2 → F) = l ∘ ![u, v] :=
    funext <| Fin.forall_fin_two.mpr ⟨rfl, rfl⟩
  rw [hcomp, l.linearIndependent_iff]

end LinearIndependent

variable {𝕜 𝕜₂ 𝕜₃ D E F : Type*}
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [SeminormedAddCommGroup D] [NormedSpace 𝕜 D]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜₃ F]
  {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomIsometric σ₁₂] [RingHomIsometric σ₁₃]

/-- Postcomposition by a linear isometry evaluates by composing the two maps. -/
@[simp] theorem postcomp_apply [SeminormedAddCommGroup E] [NormedSpace 𝕜₂ E]
    (i : E →ₛₗᵢ[σ₂₃] F) (f : D →SL[σ₁₂] E) (x : D) :
    postcomp (σ₁₂ := σ₁₂) (σ₁₃ := σ₁₃) i f x = i (f x) := rfl

/-- Postcomposition by a linear isometry is composition with its underlying continuous linear
map. -/
theorem postcomp_eq_comp [SeminormedAddCommGroup E] [NormedSpace 𝕜₂ E]
    (i : E →ₛₗᵢ[σ₂₃] F) (f : D →SL[σ₁₂] E) :
    postcomp (σ₁₂ := σ₁₂) (σ₁₃ := σ₁₃) i f = i.toContinuousLinearMap.comp f := rfl

variable [NormedAddCommGroup E] [NormedSpace 𝕜₂ E]

/-- The range of postcomposition by a linear isometry consists exactly of the continuous linear
maps all of whose values lie in the range of that isometry. -/
@[simp] theorem range_postcomp (i : E →ₛₗᵢ[σ₂₃] F) :
    range (postcomp (σ₁₂ := σ₁₂) (σ₁₃ := σ₁₃) i) = {g : D →SL[σ₁₃] F | ∀ x, g x ∈ range i} := by
  ext g
  rw [mem_ofPred_eq]
  refine ⟨by rintro ⟨f, rfl⟩ x; exact ⟨f x, rfl⟩, fun hg ↦ ?_⟩
  choose f hf using hg
  let f' : D →ₛₗ[σ₁₂] E :=
    { toFun := f
      map_add' x y := i.injective (by simp [hf])
      map_smul' c x := i.injective <| by
        rw [i.map_smulₛₗ, RingHomCompTriple.comp_apply, hf, hf, g.map_smulₛₗ] }
  refine ⟨f'.mkContinuous ‖g‖ fun x ↦ ?_, by ext x; exact hf x⟩
  rw [← i.norm_map, LinearMap.coe_mk, AddHom.coe_mk, hf]
  exact g.le_opNorm x

/-- Postcomposition by a closed-range linear isometry has closed range on operators. -/
theorem isClosed_range_postcomp (i : E →ₛₗᵢ[σ₂₃] F) (hi : IsClosed (range i)) :
    IsClosed (range (postcomp i : (D →SL[σ₁₂] E) →ₛₗᵢ[σ₂₃] (D →SL[σ₁₃] F))) := by
  convert isClosed_iInter fun x : D ↦
    hi.preimage (continuous_eval_const (F := D →SL[σ₁₃] F) x) using 1
  ext g
  simp only [range_postcomp, mem_ofPred_eq, mem_iInter, mem_preimage]

section CodRestrict
variable {R R₂ E F : Type*} [Semiring R] [Ring R₂] {σ₁₂ : R →+* R₂}
  [SeminormedAddCommGroup E] [Module R E] [SeminormedAddCommGroup F] [Module R₂ F]

/-- Restrict the codomain of a (semilinear) isometry to a submodule containing its values. -/
def codRestrict (i : E →ₛₗᵢ[σ₁₂] F) (p : Submodule R₂ F) (h : ∀ x, i x ∈ p) : E →ₛₗᵢ[σ₁₂] p :=
  ⟨i.toLinearMap.codRestrict p h, fun x ↦ by simp [← Submodule.norm_coe]⟩

@[simp] theorem coe_codRestrict_apply (i : E →ₛₗᵢ[σ₁₂] F) (p : Submodule R₂ F) (h : ∀ x, i x ∈ p)
    (x : E) : (i.codRestrict p h x : F) = i x := (rfl)
end CodRestrict

section DenseRange
variable {R R₂ E F : Type*} [Semiring R] [Semiring R₂] {σ₁₂ : R →+* R₂} {σ₂₁ : R₂ →+* R}
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  [NormedAddCommGroup E] [Module R E] [CompleteSpace E] [NormedAddCommGroup F] [Module R₂ F]

/-- A (semilinear) isometry from a complete normed module is surjective when its range is dense. -/
theorem surjective_of_denseRange (i : E →ₛₗᵢ[σ₁₂] F) (hi : DenseRange i) :
    Function.Surjective i :=
  range_eq_univ.1 <| i.isometry.isUniformInducing.isComplete_range.isClosed.closure_eq ▸
    hi.closure_eq

/-- A (semilinear) isometry from a complete normed module with dense range upgrades to a linear
isometric equivalence. -/
noncomputable def equivOfDenseRange (i : E →ₛₗᵢ[σ₁₂] F) (hi : DenseRange i) : E ≃ₛₗᵢ[σ₁₂] F :=
  .ofSurjective i (i.surjective_of_denseRange hi)

@[simp] theorem coe_equivOfDenseRange (i : E →ₛₗᵢ[σ₁₂] F) (hi : DenseRange i) :
    ⇑(i.equivOfDenseRange hi) = i := (rfl)
end DenseRange

end LinearIsometry

namespace LinearIsometryEquiv

variable {𝕜 E F H : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
  (G : Type*) [SeminormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Precomposition with a linear isometric equivalence as a linear isometric equivalence between
spaces of continuous linear maps. -/
def precomp (e : E ≃ₗᵢ[𝕜] F) : (F →L[𝕜] G) ≃ₗᵢ[𝕜] (E →L[𝕜] G) where
  toFun f := f.comp e.toLinearIsometry.toContinuousLinearMap
  invFun g := g.comp e.symm.toLinearIsometry.toContinuousLinearMap
  left_inv f := by ext x; simp
  right_inv g := by ext x; simp
  map_add' _ _ := ContinuousLinearMap.add_comp _ _ _
  map_smul' _ _ := ContinuousLinearMap.smul_comp _ _ _
  norm_map' f := by
    apply le_antisymm
    · exact (f.opNorm_comp_le _).trans <|
        mul_le_of_le_one_right (norm_nonneg f) e.toLinearIsometry.norm_toContinuousLinearMap_le
    · have h : f = (f.comp e.toLinearIsometry.toContinuousLinearMap).comp
          e.symm.toLinearIsometry.toContinuousLinearMap := by ext x; simp
      exact (congrArg norm h).le.trans <| ((f.comp _).opNorm_comp_le _).trans <|
        mul_le_of_le_one_right (norm_nonneg _) e.symm.toLinearIsometry.norm_toContinuousLinearMap_le

/-- Precomposing an operator with `e` composes it on the right with `e` as a continuous linear
map. -/
@[simp]
theorem precomp_apply (e : E ≃ₗᵢ[𝕜] F) (f : F →L[𝕜] G) :
    e.precomp G f = f.comp e.toLinearIsometry.toContinuousLinearMap :=
  (rfl)

/-- As a continuous linear map, `e.precomp G` agrees with `ContinuousLinearMap.precomp G`. -/
theorem toContinuousLinearMap_precomp (e : E ≃ₗᵢ[𝕜] F) :
    (e.precomp G).toLinearIsometry.toContinuousLinearMap =
      ContinuousLinearMap.precomp G e.toLinearIsometry.toContinuousLinearMap := by
  ext f x
  simp

/-- The inverse of `LinearIsometryEquiv.precomp` is precomposition with `e.symm`. -/
@[simp]
theorem precomp_symm (e : E ≃ₗᵢ[𝕜] F) : (e.precomp G).symm = e.symm.precomp G :=
  (rfl)

/-- Precomposing with the identity isometric equivalence is the identity on continuous linear
maps. -/
@[simp]
theorem precomp_refl :
    (LinearIsometryEquiv.refl 𝕜 E).precomp G = LinearIsometryEquiv.refl 𝕜 (E →L[𝕜] G) := by
  ext f x
  simp

/-- Precomposing with a composition of linear isometric equivalences reverses the order of
composition. -/
@[simp]
theorem precomp_trans (e₁ : E ≃ₗᵢ[𝕜] F) (e₂ : F ≃ₗᵢ[𝕜] H) :
    (e₁.trans e₂).precomp G = (e₂.precomp G).trans (e₁.precomp G) := by
  ext f x
  simp

end LinearIsometryEquiv

namespace LinearIsometryEquiv

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Conjugating an operator by a linear isometric equivalence preserves its distance to the
identity: `‖e ∘ B ∘ e⁻¹ - 1‖ = ‖B - 1‖`. -/
theorem norm_comp_comp_symm_sub_id (e : E ≃ₗᵢ[𝕜] F) (B : E →L[𝕜] E) :
    ‖(e : E →L[𝕜] F) ∘L B ∘L (e.symm : F →L[𝕜] E) - ContinuousLinearMap.id 𝕜 F‖ =
      ‖B - ContinuousLinearMap.id 𝕜 E‖ := by
  have h : (e : E →L[𝕜] F) ∘L B ∘L (e.symm : F →L[𝕜] E) - ContinuousLinearMap.id 𝕜 F =
      (e : E →L[𝕜] F) ∘L (B - ContinuousLinearMap.id 𝕜 E) ∘L (e.symm : F →L[𝕜] E) := by
    ext x; simp
  rw [h, ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

end LinearIsometryEquiv

namespace SeparationQuotient

variable {R R₂ E F : Type*} [Semiring R] [Semiring R₂] {σ₁₂ : R →+* R₂}
  [SeminormedAddCommGroup E] [Module R E] [ContinuousConstSMul R E]
  [NormedAddCommGroup F] [Module R₂ F]

/-- Descend a semilinear isometry `f : E →ₛₗᵢ[σ₁₂] F` into a separated normed module `F` to
`SeparationQuotient E →ₛₗᵢ[σ₁₂] F`. -/
noncomputable def liftₗᵢ (f : E →ₛₗᵢ[σ₁₂] F) : SeparationQuotient E →ₛₗᵢ[σ₁₂] F :=
  { liftCLM f.toContinuousLinearMap fun _ _ h ↦ (h.map f.toContinuousLinearMap.continuous).eq with
    norm_map' := surjective_mk.forall.2 fun x ↦ by simp [norm_mk] }

@[simp] theorem liftₗᵢ_mk (f : E →ₛₗᵢ[σ₁₂] F) (x : E) : liftₗᵢ f (mk x) = f x := (rfl)
@[simp] theorem toContinuousLinearMap_liftₗᵢ (f : E →ₛₗᵢ[σ₁₂] F) :
    (liftₗᵢ f).toContinuousLinearMap = liftCLM f.toContinuousLinearMap
      fun _ _ h ↦ (h.map f.toContinuousLinearMap.continuous).eq := (rfl)

theorem eq_liftₗᵢ_iff (f : E →ₛₗᵢ[σ₁₂] F) (g : SeparationQuotient E →ₛₗᵢ[σ₁₂] F) :
    g = liftₗᵢ f ↔ ∀ x : E, g (mk x) = f x := by
  rw [← LinearIsometry.toContinuousLinearMap_inj, toContinuousLinearMap_liftₗᵢ, eq_liftCLM_iff]; rfl

theorem liftₗᵢ_smul {A B : Type*} [SMul A E] [ContinuousConstSMul A E] [SMul B F]
    (f : E →ₛₗᵢ[σ₁₂] F) {a : A} {b : B} (hf : ∀ x : E, f (a • x) = b • f x)
    (u : SeparationQuotient E) : liftₗᵢ f (a • u) = b • liftₗᵢ f u :=
  liftCLM_smul f.toContinuousLinearMap _ hf u

end SeparationQuotient
