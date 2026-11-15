/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.OpenQuotient
public import TauCeti.Algebra.Module.LinearMap.Snake
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.UpperTriangularBlock
public import TauCeti.Topology.Algebra.Module.Quotient
import TauCeti.LinearAlgebra.LinearMap.Ker

/-!
# Continuous snake sequences and the composition snake diagram

A commuting diagram of continuous linear maps between two exact three-term rows
```text
      E₁ --f₁--> E₂ --f₂--> E₃ ⟶ 0
      |          |          |
     T₁         T₂         T₃
      v          v          v
0 ⟶ F₁ --g₁--> F₂ --g₂--> F₃
```
induces continuous linear maps on kernels (`TauCeti.kerMapL`) and on topological quotient cokernels
(`TauCeti.cokerMapL`).

We bundle the algebraic connecting map `TauCeti.snakeδ : ker T₃ →ₗ[R] F₁ ⧸ range T₁` as a
continuous linear map in two settings:

* When `f₂` admits a continuous linear right inverse `σ` and `g₁` admits a continuous linear left
  inverse `ρ`, `TauCeti.snakeδL` equals `T₁.range.mkQL ∘L ρ ∘L T₂ ∘L σ ∘L T₃.ker.subtypeL`, which is
  independent of `(σ, ρ)` (`TauCeti.snakeδL_eq_snakeδL`).
* More generally, whenever `f₂` is an open quotient map and `g₁` is a topological embedding,
  `TauCeti.continuous_snakeδ_of_isOpenQuotientMap_of_isEmbedding` proves continuity of
  `TauCeti.snakeδ` directly without splittings, bundled as `TauCeti.snakeδLOfIsOpenQuotientMap`.

Specializing to `ContinuousLinearMap.upperTriangularBlock A B D` identifies its connecting map with
`y ↦ [B y]` (`ContinuousLinearMap.snakeδL_upperTriangularBlock_eq`), and specializing further to
`ContinuousLinearMap.compSnakeMiddle T S = upperTriangularBlock T (-id) S` realizes the composition
snake diagram with `(compSnakeMiddle T S).index = (S ∘L T).index`
(`ContinuousLinearMap.index_compSnakeMiddle`).

We also record `Function.Exact.isClosed_range`: in an exact pair `E₁ --f--> E₂ --g--> E₃` of
continuous semilinear maps with a `T₁` target `E₃`, `range f` equals `ker g` and is therefore
closed.

## References

* N. Bourbaki, *Algebra*, Chapter X (*Homological Algebra*), §1, Proposition 2.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §19.1,
  Theorem 19.1.2.
-/

public section

/-- If `E₁ --f--> E₂ --g--> E₃` is algebraically exact for continuous semilinear maps and `E₃` is
`T₁`, then `range f` is closed in `E₂`, being equal to the closed kernel of `g`. -/
theorem Function.Exact.isClosed_range {R₁ R₂ R₃ E₁ E₂ E₃ : Type*}
    [Semiring R₁] [Semiring R₂] [Semiring R₃]
    {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} [RingHomSurjective σ₁₂]
    [TopologicalSpace E₁] [AddCommMonoid E₁] [Module R₁ E₁]
    [TopologicalSpace E₂] [AddCommMonoid E₂] [Module R₂ E₂]
    [TopologicalSpace E₃] [AddCommMonoid E₃] [Module R₃ E₃] [T1Space E₃]
    {f : E₁ →SL[σ₁₂] E₂} {g : E₂ →SL[σ₂₃] E₃}
    (hfg : Function.Exact f g) : IsClosed (f.range : Set E₂) := by
  have hker : (f.range : Set E₂) = (g.ker : Set E₂) := by
    ext y
    simpa using (hfg y).symm
  rw [hker]
  exact g.isClosed_ker

namespace TauCeti

section KerMapL

variable {R E₁ E₂ E₃ F₁ F₂ F₃ : Type*} [Semiring R]
  [TopologicalSpace E₁] [AddCommMonoid E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommMonoid E₂] [Module R E₂]
  [TopologicalSpace E₃] [AddCommMonoid E₃] [Module R E₃]
  [TopologicalSpace F₁] [AddCommMonoid F₁] [Module R F₁]
  [TopologicalSpace F₂] [AddCommMonoid F₂] [Module R F₂]
  [TopologicalSpace F₃] [AddCommMonoid F₃] [Module R F₃]

/-- Continuous linear map `ker T₁ →L[R] ker T₂` induced by a commuting square
`g ∘L T₁ = T₂ ∘L f`. -/
def kerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂}
    (h : g ∘L T₁ = T₂ ∘L f) : T₁.ker →L[R] T₂.ker :=
  f.restrict fun _ ↦
    LinearMap.map_mem_ker_of_comp_eq f.toLinearMap (congrArg ContinuousLinearMap.toLinearMap h)

@[simp, norm_cast]
theorem toLinearMap_kerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) :
    (kerMapL h).toLinearMap = kerMap (congrArg ContinuousLinearMap.toLinearMap h) := by
  ext x
  exact (coe_kerMap_apply _ x).symm

@[simp]
theorem coe_kerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) :
    ⇑(kerMapL h) = kerMap (congrArg ContinuousLinearMap.toLinearMap h) :=
  congrArg DFunLike.coe (toLinearMap_kerMapL h)

theorem coe_kerMapL_apply {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) (x : T₁.ker) :
    (kerMapL h x : E₂) = f x :=
  (rfl)

@[simp]
theorem subtypeL_comp_kerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) :
    T₂.ker.subtypeL ∘L kerMapL h = f ∘L T₁.ker.subtypeL :=
  (rfl)

@[simp]
theorem kerMapL_zero {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {g : F₁ →L[R] F₂}
    (h : g ∘L T₁ = T₂ ∘L (0 : E₁ →L[R] E₂)) :
    kerMapL h = 0 := by
  ext
  simp

@[simp]
theorem kerMapL_id {T : E₁ →L[R] F₁}
    (h : ContinuousLinearMap.id R F₁ ∘L T = T ∘L ContinuousLinearMap.id R E₁ := rfl) :
    kerMapL h = ContinuousLinearMap.id R T.ker := by
  ext
  rfl

theorem kerMapL_comp {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (h₁₃ : (g₂ ∘L g₁) ∘L T₁ = T₃ ∘L (f₂ ∘L f₁) := by
      rw [ContinuousLinearMap.comp_assoc, h₁₂, ← ContinuousLinearMap.comp_assoc, h₂₃,
        ContinuousLinearMap.comp_assoc]) :
    kerMapL h₁₃ = kerMapL h₂₃ ∘L kerMapL h₁₂ := by
  ext
  rfl

/-- If `f` is injective, then the induced continuous linear map on kernels is injective. -/
theorem kerMapL_injective {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) (hf : Function.Injective f) :
    Function.Injective (kerMapL h) := fun _ _ hxy ↦
  Subtype.ext (hf (congrArg Subtype.val hxy))

/-- Exactness of the continuous snake sequence at `ker T₂`. -/
theorem exact_kerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    Function.Exact (kerMapL h₁₂) (kerMapL h₂₃) := by
  simpa only [coe_kerMapL] using exact_kerMap hf hg₁ _ _

end KerMapL

section CokerMapL

variable {R E₁ E₂ E₃ F₁ F₂ F₃ : Type*} [Ring R]
  [TopologicalSpace E₁] [AddCommMonoid E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommMonoid E₂] [Module R E₂]
  [TopologicalSpace E₃] [AddCommMonoid E₃] [Module R E₃]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module R F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module R F₂]
  [TopologicalSpace F₃] [AddCommGroup F₃] [Module R F₃]

/-- Continuous linear map `(F₁ ⧸ range T₁) →L[R] (F₂ ⧸ range T₂)` on quotient cokernels induced by
a commuting square `g ∘L T₁ = T₂ ∘L f`. -/
def cokerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂}
    (h : g ∘L T₁ = T₂ ∘L f) : (F₁ ⧸ T₁.range) →L[R] (F₂ ⧸ T₂.range) :=
  T₁.range.mapQL T₂.range g <| by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe] using
        (DFunLike.congr_fun h x).symm⟩

theorem cokerMapL_mk {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) (y : F₁) :
    cokerMapL h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (g y) := by
  simp [cokerMapL, Submodule.mapQL_mk]

@[simp, norm_cast]
theorem toLinearMap_cokerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) :
    (cokerMapL h).toLinearMap = cokerMap (congrArg ContinuousLinearMap.toLinearMap h) := by
  ext y
  exact (cokerMapL_mk h y).trans (cokerMap_mk _ y).symm

@[simp]
theorem coe_cokerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) :
    ⇑(cokerMapL h) = cokerMap (congrArg ContinuousLinearMap.toLinearMap h) :=
  congrArg DFunLike.coe (toLinearMap_cokerMapL h)

@[simp]
theorem cokerMapL_comp_mkQL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) :
    cokerMapL h ∘L T₁.range.mkQL = T₂.range.mkQL ∘L g := by
  simp [cokerMapL]

@[simp]
theorem cokerMapL_zero {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {f : E₁ →L[R] E₂}
    (h : (0 : F₁ →L[R] F₂) ∘L T₁ = T₂ ∘L f) :
    cokerMapL h = 0 := by
  ext
  simp

@[simp]
theorem cokerMapL_id {T : E₁ →L[R] F₁}
    (h : ContinuousLinearMap.id R F₁ ∘L T = T ∘L ContinuousLinearMap.id R E₁ := rfl) :
    cokerMapL h = ContinuousLinearMap.id R (F₁ ⧸ T.range) := by
  simp [cokerMapL]

theorem cokerMapL_comp {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (h₁₃ : (g₂ ∘L g₁) ∘L T₁ = T₃ ∘L (f₂ ∘L f₁) := by
      rw [ContinuousLinearMap.comp_assoc, h₁₂, ← ContinuousLinearMap.comp_assoc, h₂₃,
        ContinuousLinearMap.comp_assoc]) :
    cokerMapL h₁₃ = cokerMapL h₂₃ ∘L cokerMapL h₁₂ := by
  apply ContinuousLinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := T₁.range.mkQ_surjective x
  simp only [ContinuousLinearMap.comp_apply, Submodule.mkQ_apply, cokerMapL_mk]

/-- If `g` is surjective, then the induced continuous linear map on quotient cokernels is
surjective. -/
theorem cokerMapL_surjective {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂}
    {f : E₁ →L[R] E₂} {g : F₁ →L[R] F₂} (h : g ∘L T₁ = T₂ ∘L f) (hg : Function.Surjective g) :
    Function.Surjective (cokerMapL h) := by
  rw [coe_cokerMapL]
  exact cokerMap_surjective _ hg

/-- Exactness of the continuous snake sequence at `F₂ ⧸ range T₂`. -/
theorem exact_cokerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf₂ : Function.Surjective f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    Function.Exact (cokerMapL h₁₂) (cokerMapL h₂₃) := by
  simpa only [coe_cokerMapL] using exact_cokerMap hf₂ hg _ _

end CokerMapL

section ContinuousSnake

universe u u₁ u₂ u₃ v₁ v₂ v₃

variable {R : Type u} [Ring R]
  {E₁ : Type u₁} {E₂ : Type u₂} {E₃ : Type u₃}
  {F₁ : Type v₁} {F₂ : Type v₂} {F₃ : Type v₃}
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module R E₂]
  [TopologicalSpace E₃] [AddCommGroup E₃] [Module R E₃]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module R F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module R F₂]
  [TopologicalSpace F₃] [AddCommGroup F₃] [Module R F₃]

/-- Continuous connecting linear map `ker T₃ →L[R] F₁ ⧸ range T₁` of a snake diagram whose top
surjection `f₂` has a continuous linear right inverse `σ` and whose bottom injection `g₁` has a
continuous linear left inverse `ρ`. -/
def snakeδL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (_hf : Function.Exact f₁ f₂) (_hg : Function.Exact g₁ g₂)
    (_h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (_h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (_hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (_hρ : Function.LeftInverse ρ g₁) :
    T₃.ker →L[R] F₁ ⧸ T₁.range :=
  T₁.range.mkQL ∘L ρ ∘L T₂ ∘L σ ∘L T₃.ker.subtypeL

theorem snakeδL_def {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) :
    snakeδL hf hg h₁₂ h₂₃ hσ hρ = T₁.range.mkQL ∘L ρ ∘L T₂ ∘L σ ∘L T₃.ker.subtypeL :=
  (rfl)

@[simp]
theorem snakeδL_apply {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) (x₃ : T₃.ker) :
    snakeδL hf hg h₁₂ h₂₃ hσ hρ x₃ = Submodule.Quotient.mk (ρ (T₂ (σ x₃))) :=
  (rfl)

/-- The underlying linear map of `TauCeti.snakeδL` is the algebraic snake connecting map
`TauCeti.snakeδ`. -/
@[simp, norm_cast]
theorem toLinearMap_snakeδL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) :
    (snakeδL hf hg h₁₂ h₂₃ hσ hρ).toLinearMap =
      snakeδ hf hσ.surjective hg hρ.injective
        (congrArg ContinuousLinearMap.toLinearMap h₁₂)
        (congrArg ContinuousLinearMap.toLinearMap h₂₃) :=
  (snakeδ_eq_of_rightInverse_of_leftInverse hf hg
    (congrArg ContinuousLinearMap.toLinearMap h₁₂)
    (congrArg ContinuousLinearMap.toLinearMap h₂₃) hσ hρ).symm

theorem coe_snakeδL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) :
    ⇑(snakeδL hf hg h₁₂ h₂₃ hσ hρ) =
      snakeδ hf hσ.surjective hg hρ.injective
        (congrArg ContinuousLinearMap.toLinearMap h₁₂)
        (congrArg ContinuousLinearMap.toLinearMap h₂₃) :=
  congrArg DFunLike.coe (toLinearMap_snakeδL hf hg h₁₂ h₂₃ hσ hρ)

/-- Diagram-chase formula for `TauCeti.snakeδL`: if `f₂ x₂ = x₃` and `g₁ y₁ = T₂ x₂`, then
`snakeδL` sends `x₃` to the class of `y₁` modulo `range T₁`. -/
theorem snakeδL_eq {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁)
    (x₃ : T₃.ker) (x₂ : E₂) (y₁ : F₁) (hx₂ : f₂ x₂ = x₃) (hy₁ : g₁ y₁ = T₂ x₂) :
    snakeδL hf hg h₁₂ h₂₃ hσ hρ x₃ = Submodule.Quotient.mk y₁ := by
  rw [← ContinuousLinearMap.coe_coe, toLinearMap_snakeδL]
  exact snakeδ_eq hf hσ.surjective hg hρ.injective _ _ x₃ x₂ y₁ hx₂ hy₁

/-- **Splitting independence of `TauCeti.snakeδL`**: any two choices `(σ, ρ)` and `(σ', ρ')` of
continuous linear splittings induce the same continuous connecting map. -/
theorem snakeδL_eq_snakeδL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ σ' : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂) (hσ' : Function.RightInverse σ' f₂)
    {ρ ρ' : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) (hρ' : Function.LeftInverse ρ' g₁) :
    snakeδL hf hg h₁₂ h₂₃ hσ hρ = snakeδL hf hg h₁₂ h₂₃ hσ' hρ' :=
  ContinuousLinearMap.coe_injective <|
    (toLinearMap_snakeδL hf hg h₁₂ h₂₃ hσ hρ).trans
      (toLinearMap_snakeδL hf hg h₁₂ h₂₃ hσ' hρ').symm

/-- Exactness of the continuous snake sequence at `ker T₃`. -/
theorem exact_kerMapL_snakeδL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) :
    Function.Exact (kerMapL h₂₃) (snakeδL hf hg h₁₂ h₂₃ hσ hρ) := by
  rw [coe_kerMapL, coe_snakeδL]
  exact exact_kerMap_snakeδ hf hσ.surjective hg hρ.injective _ _

/-- Exactness of the continuous snake sequence at `F₁ ⧸ range T₁`. -/
theorem exact_snakeδL_cokerMapL {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) :
    Function.Exact (snakeδL hf hg h₁₂ h₂₃ hσ hρ) (cokerMapL h₁₂) := by
  rw [coe_snakeδL, coe_cokerMapL]
  exact exact_snakeδ_cokerMap hf hσ.surjective hg hρ.injective _ _

/-- **Automatic continuity of the snake connecting map**: if `f₂` is an open quotient map and `g₁`
is a topological embedding in a commuting diagram with exact rows, then `TauCeti.snakeδ` is
continuous, with no splitting hypotheses. -/
theorem continuous_snakeδ_of_isOpenQuotientMap_of_isEmbedding
    {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : IsOpenQuotientMap f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Topology.IsEmbedding g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    Continuous (snakeδ hf hf₂.surjective hg hg₁.injective
      (congrArg ContinuousLinearMap.toLinearMap h₁₂)
      (congrArg ContinuousLinearMap.toLinearMap h₂₃)) := by
  let A := ↥(T₃.ker.comap f₂.toLinearMap)
  let p : A → T₃.ker := fun x ↦ ⟨f₂ x.1, x.2⟩
  have hp_surj : Function.Surjective p := fun ⟨x₃, hx₃⟩ ↦
    let ⟨x₂, hx₂⟩ := hf₂.surjective x₃
    ⟨⟨x₂, by simpa [Submodule.mem_comap, hx₂] using hx₃⟩, Subtype.ext hx₂⟩
  have hp : Topology.IsQuotientMap p :=
    isQuotientMap_of_isOpenQuotientMap_of_isInducing Subtype.val Subtype.val p f₂ rfl
      Topology.IsInducing.subtypeVal hp_surj hf₂ Topology.IsEmbedding.subtypeVal
      (by
        rintro x₂ ⟨_, ⟨a, rfl⟩, hx₂⟩
        exact ⟨⟨x₂, by
          simpa only [Submodule.mem_comap, ContinuousLinearMap.coe_coe, ← hx₂] using a.2⟩, rfl⟩)
  have hmem : ∀ x : A, ∃ y₁ : F₁, g₁ y₁ = T₂ x.1 := fun x ↦
    (hg (T₂ x.1)).mp <| by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe] using
        (DFunLike.congr_fun h₂₃ x.1).trans (LinearMap.mem_ker.mp x.2)
  let φ : A → F₁ := fun x ↦ (hmem x).choose
  have hφ : ∀ x : A, g₁ (φ x) = T₂ x.1 := fun x ↦ (hmem x).choose_spec
  have hφ_cont : Continuous φ :=
    hg₁.isInducing.continuous_iff.mpr <| by
      simpa only [Function.comp_def, hφ] using T₂.continuous.comp continuous_subtype_val
  rw [hp.continuous_iff]
  have hcomp : snakeδ hf hf₂.surjective hg hg₁.injective
      (congrArg ContinuousLinearMap.toLinearMap h₁₂)
      (congrArg ContinuousLinearMap.toLinearMap h₂₃) ∘ p = T₁.range.mkQL ∘ φ :=
    funext fun x ↦ snakeδ_eq hf hf₂.surjective hg hg₁.injective _ _ (p x) x.1 (φ x) rfl (hφ x)
  rw [hcomp]
  exact T₁.range.mkQL.continuous.comp hφ_cont

/-- Continuous snake connecting map bundled without splittings whenever `f₂` is an open quotient map
and `g₁` is a topological embedding. -/
noncomputable def snakeδLOfIsOpenQuotientMap
    {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : IsOpenQuotientMap f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Topology.IsEmbedding g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    T₃.ker →L[R] F₁ ⧸ T₁.range :=
  { snakeδ hf hf₂.surjective hg hg₁.injective
      (congrArg ContinuousLinearMap.toLinearMap h₁₂)
      (congrArg ContinuousLinearMap.toLinearMap h₂₃) with
    cont := continuous_snakeδ_of_isOpenQuotientMap_of_isEmbedding hf hf₂ hg hg₁ h₁₂ h₂₃ }

@[simp, norm_cast]
theorem toLinearMap_snakeδLOfIsOpenQuotientMap
    {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : IsOpenQuotientMap f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Topology.IsEmbedding g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    (snakeδLOfIsOpenQuotientMap hf hf₂ hg hg₁ h₁₂ h₂₃).toLinearMap =
      snakeδ hf hf₂.surjective hg hg₁.injective
        (congrArg ContinuousLinearMap.toLinearMap h₁₂)
        (congrArg ContinuousLinearMap.toLinearMap h₂₃) :=
  (rfl)

@[simp]
theorem coe_snakeδLOfIsOpenQuotientMap
    {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : IsOpenQuotientMap f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Topology.IsEmbedding g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    ⇑(snakeδLOfIsOpenQuotientMap hf hf₂ hg hg₁ h₁₂ h₂₃) =
      snakeδ hf hf₂.surjective hg hg₁.injective
        (congrArg ContinuousLinearMap.toLinearMap h₁₂)
        (congrArg ContinuousLinearMap.toLinearMap h₂₃) :=
  (rfl)

/-- Diagram-chase formula for `TauCeti.snakeδLOfIsOpenQuotientMap`. -/
theorem snakeδLOfIsOpenQuotientMap_eq
    {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : IsOpenQuotientMap f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Topology.IsEmbedding g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (x₃ : T₃.ker) (x₂ : E₂) (y₁ : F₁) (hx₂ : f₂ x₂ = x₃) (hy₁ : g₁ y₁ = T₂ x₂) :
    snakeδLOfIsOpenQuotientMap hf hf₂ hg hg₁ h₁₂ h₂₃ x₃ = Submodule.Quotient.mk y₁ :=
  snakeδ_eq hf hf₂.surjective hg hg₁.injective _ _ x₃ x₂ y₁ hx₂ hy₁

/-- When continuous linear splittings `(σ, ρ)` also exist, `TauCeti.snakeδLOfIsOpenQuotientMap`
agrees with `TauCeti.snakeδL`. -/
theorem snakeδLOfIsOpenQuotientMap_eq_snakeδL
    {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : IsOpenQuotientMap f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Topology.IsEmbedding g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) :
    snakeδLOfIsOpenQuotientMap hf hf₂ hg hg₁ h₁₂ h₂₃ = snakeδL hf hg h₁₂ h₂₃ hσ hρ :=
  ContinuousLinearMap.coe_injective (toLinearMap_snakeδL hf hg h₁₂ h₂₃ hσ hρ).symm

/-- Exactness of `TauCeti.snakeδLOfIsOpenQuotientMap` at `ker T₃`. -/
theorem exact_kerMapL_snakeδLOfIsOpenQuotientMap
    {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : IsOpenQuotientMap f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Topology.IsEmbedding g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    Function.Exact (kerMapL h₂₃) (snakeδLOfIsOpenQuotientMap hf hf₂ hg hg₁ h₁₂ h₂₃) := by
  simpa only [coe_kerMapL, coe_snakeδLOfIsOpenQuotientMap] using
    exact_kerMap_snakeδ hf hf₂.surjective hg hg₁.injective _ _

/-- Exactness of `TauCeti.snakeδLOfIsOpenQuotientMap` at `F₁ ⧸ range T₁`. -/
theorem exact_snakeδLOfIsOpenQuotientMap_cokerMapL
    {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
    {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : IsOpenQuotientMap f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Topology.IsEmbedding g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    Function.Exact (snakeδLOfIsOpenQuotientMap hf hf₂ hg hg₁ h₁₂ h₂₃) (cokerMapL h₁₂) := by
  simpa only [coe_snakeδLOfIsOpenQuotientMap, coe_cokerMapL] using
    exact_snakeδ_cokerMap hf hf₂.surjective hg hg₁.injective _ _

end ContinuousSnake

end TauCeti

namespace ContinuousLinearMap

section BlockSnake

variable {R E₁ E₂ F₁ F₂ : Type*} [Ring R]
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module R E₂]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module R F₁] [ContinuousAdd F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module R F₂]

/-- In the split product snake diagram for `upperTriangularBlock A B D`, the continuous connecting
map `ker D →L[R] F₁ ⧸ range A` sends `y ∈ ker D` to the class of `B y` modulo `range A`. -/
theorem snakeδL_upperTriangularBlock_eq
    (A : E₁ →L[R] F₁) (B : E₂ →L[R] F₁) (D : E₂ →L[R] F₂)
    {σ : E₂ →L[R] E₁ × E₂} (hσ : Function.RightInverse σ (snd R E₁ E₂))
    {ρ : F₁ × F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ (inl R F₁ F₂)) :
    TauCeti.snakeδL .inl_snd .inl_snd
      (A.upperTriangularBlock_comp_inl B D).symm (A.snd_comp_upperTriangularBlock B D) hσ hρ =
        A.range.mkQL ∘L B ∘L D.ker.subtypeL := by
  refine (TauCeti.snakeδL_eq_snakeδL _ _ _ _ hσ (σ' := inr R E₁ E₂) (fun _ ↦ rfl)
    hρ (ρ' := fst R F₁ F₂) (fun _ ↦ rfl)).trans ?_
  ext y
  simp [TauCeti.snakeδL]

end BlockSnake

section CompSnake

variable {R E F G : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F] [IsTopologicalAddGroup F]
  [TopologicalSpace G] [AddCommGroup G] [Module R G]

/-- The middle vertical map `(x, y) ↦ (T x - y, S y)` of the composition snake diagram
```text
0 ⟶ E ⟶ E × F ⟶ F ⟶ 0
    |T     |φ    |S
    v      v     v
0 ⟶ F ⟶ F × G ⟶ G ⟶ 0
```
realizing `CategoryTheory.kernelCokernelCompSequence.φ` for continuous linear maps. -/
def compSnakeMiddle (T : E →L[R] F) (S : F →L[R] G) : E × F →L[R] F × G :=
  upperTriangularBlock T (-ContinuousLinearMap.id R F) S

theorem compSnakeMiddle_def (T : E →L[R] F) (S : F →L[R] G) :
    compSnakeMiddle T S = upperTriangularBlock T (-ContinuousLinearMap.id R F) S :=
  (rfl)

@[simp]
theorem compSnakeMiddle_apply (T : E →L[R] F) (S : F →L[R] G) (xy : E × F) :
    compSnakeMiddle T S xy = (T xy.1 - xy.2, S xy.2) := by
  simp [compSnakeMiddle, sub_eq_add_neg]

@[simp]
theorem compSnakeMiddle_comp_inl (T : E →L[R] F) (S : F →L[R] G) :
    compSnakeMiddle T S ∘L inl R E F = inl R F G ∘L T :=
  T.upperTriangularBlock_comp_inl (-ContinuousLinearMap.id R F) S

@[simp]
theorem compSnakeMiddle_comp_inr (T : E →L[R] F) (S : F →L[R] G) :
    compSnakeMiddle T S ∘L inr R E F = (-ContinuousLinearMap.id R F).prod S :=
  T.upperTriangularBlock_comp_inr (-ContinuousLinearMap.id R F) S

@[simp]
theorem fst_comp_compSnakeMiddle (T : E →L[R] F) (S : F →L[R] G) :
    fst R F G ∘L compSnakeMiddle T S = T.coprod (-ContinuousLinearMap.id R F) :=
  T.fst_comp_upperTriangularBlock (-ContinuousLinearMap.id R F) S

@[simp]
theorem snd_comp_compSnakeMiddle (T : E →L[R] F) (S : F →L[R] G) :
    snd R F G ∘L compSnakeMiddle T S = S ∘L snd R E F :=
  T.snd_comp_upperTriangularBlock (-ContinuousLinearMap.id R F) S

/-- In the composition snake diagram `(T, compSnakeMiddle T S, S)`, the continuous connecting map
`ker S →L[R] F ⧸ range T` equals `-(T.range.mkQL ∘L S.ker.subtypeL)`, matching
`CategoryTheory.kernelCokernelCompSequence.δ_fac`. -/
theorem snakeδL_compSnakeMiddle_eq (T : E →L[R] F) (S : F →L[R] G)
    {σ : F →L[R] E × F} (hσ : Function.RightInverse σ (snd R E F))
    {ρ : F × G →L[R] F} (hρ : Function.LeftInverse ρ (inl R F G)) :
    TauCeti.snakeδL .inl_snd .inl_snd
      (T.compSnakeMiddle_comp_inl S).symm (T.snd_comp_compSnakeMiddle S) hσ hρ =
        -(T.range.mkQL ∘L S.ker.subtypeL) := by
  refine (TauCeti.snakeδL_eq_snakeδL _ _ _ _ hσ (σ' := inr R E F) (fun _ ↦ rfl)
    hρ (ρ' := fst R F G) (fun _ ↦ rfl)).trans ?_
  ext y
  simp [TauCeti.snakeδL]

/-- `compSnakeMiddle T S` has the same index as the composite `S ∘L T`, with no finiteness or
topological-group assumptions on `E` or `G`. -/
@[simp]
theorem index_compSnakeMiddle (T : E →L[R] F) (S : F →L[R] G) :
    (compSnakeMiddle T S).index = (S ∘L T).index := by
  let eCod : (F × G) ≃ₗ[R] (F × G) :=
    (LinearEquiv.refl R F).skewProd (LinearEquiv.refl R G) S.toLinearMap
  let eDom : (F × E) ≃ₗ[R] (E × F) :=
    (LinearEquiv.prodComm R F E).trans
      ((LinearEquiv.refl R E).skewProd (LinearEquiv.neg R) T.toLinearMap)
  have hconj : eCod.toLinearMap ∘ₗ (compSnakeMiddle T S).toLinearMap ∘ₗ eDom.toLinearMap =
      LinearMap.id.prodMap (S ∘L T).toLinearMap := by
    apply LinearMap.ext
    rintro ⟨v, x⟩
    ext <;> simp [eCod, eDom, sub_eq_add_neg, add_comm]
  have hidx := congrArg LinearMap.index hconj
  rw [LinearMap.index_equiv_comp, LinearMap.index_comp_equiv] at hidx
  rw [index_def, hidx, index_eq_finrank_sub, LinearMap.index_eq_finrank_sub,
    LinearMap.ker_prodMap, LinearMap.ker_id, LinearMap.range_prodMap, LinearMap.range_id]
  have hker : Module.finrank R ((⊥ : Submodule R F).prod (S ∘L T).ker) =
      Module.finrank R (S ∘L T).ker := by
    let : Unique (⊥ : Submodule R F) := uniqueOfSubsingleton 0
    exact (Submodule.prodEquiv _ _ ≪≫ₗ LinearEquiv.uniqueProd).finrank_eq
  have hcoker : Module.finrank R ((F × G) ⧸ (⊤ : Submodule R F).prod (S ∘L T).range) =
      Module.finrank R (G ⧸ (S ∘L T).range) := by
    have : Subsingleton (F ⧸ (⊤ : Submodule R F)) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    let : Unique (F ⧸ (⊤ : Submodule R F)) := uniqueOfSubsingleton 0
    exact (Submodule.quotientProdEquiv _ _ ≪≫ₗ LinearEquiv.uniqueProd).finrank_eq
  rw [hker, hcoker]

end CompSnake

end ContinuousLinearMap
