/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.OpenQuotient
public import TauCeti.Algebra.Module.SnakeLemma
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import TauCeti.Topology.Algebra.Module.Quotient
import Mathlib.Topology.LocalAtTarget

/-!
# Continuous snake sequences

A commuting diagram `(T₁, T₂, T₃)` of continuous linear maps between exact rows
`E₁ --f₁--> E₂ --f₂--> E₃ → 0` and `0 → F₁ --g₁--> F₂ --g₂--> F₃` induces continuous linear maps
on kernels (`TauCeti.kerMapL`) and quotient cokernels (`TauCeti.cokerMapL`).

We bundle the algebraic connecting map `Function.Exact.snakeδ : ker T₃ →ₗ[R] F₁ ⧸ range T₁` as a
continuous linear map in two settings:

* Given a continuous linear right inverse `σ` of `f₂` and left inverse `ρ` of `g₁`,
  `Function.Exact.snakeδL` equals `T₁.range.mkQL ∘L ρ ∘L T₂ ∘L σ ∘L T₃.ker.subtypeL`, independent
  of `(σ, ρ)` (`Function.Exact.snakeδL_eq_snakeδL`). Its diagram-chase formula and exactness laws
  (`Function.Exact.snakeδL_eq`, `Function.Exact.exact_kerMapL_snakeδL`,
  `Function.Exact.exact_snakeδL_cokerMapL`) are transported from Mathlib's `SnakeLemma.δ` (over `ℤ`
  so general noncommutative rings remain supported).
* Over a commutative ring, whenever `f₂` is an open quotient map and `g₁` is a topological
  embedding, `TauCeti.continuous_snakeδ_of_isOpenQuotientMap_of_isEmbedding` proves continuity
  directly without splittings, bundled as `Function.Exact.snakeδLOfIsOpenQuotientMapOfIsEmbedding`.

## References

* N. Bourbaki, *Algebra*, Chapter X (*Homological Algebra*), §1, Proposition 2.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §19.1,
  Theorem 19.1.2.
-/

public section

namespace TauCeti

open ContinuousLinearMap (toLinearMap_comp_eq)

section KerMapL

variable {R E₁ E₂ E₃ F₁ F₂ F₃ : Type*} [Semiring R]
  [TopologicalSpace E₁] [AddCommMonoid E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommMonoid E₂] [Module R E₂]
  [TopologicalSpace E₃] [AddCommMonoid E₃] [Module R E₃]
  [TopologicalSpace F₁] [AddCommMonoid F₁] [Module R F₁]
  [TopologicalSpace F₂] [AddCommMonoid F₂] [Module R F₂]
  [TopologicalSpace F₃] [AddCommMonoid F₃] [Module R F₃]
  {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
  {f f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}

/-- Continuous linear map `ker T₁ →L[R] ker T₂` induced by `g ∘L T₁ = T₂ ∘L f`. -/
def kerMapL (h : g ∘L T₁ = T₂ ∘L f) : T₁.ker →L[R] T₂.ker :=
  f.restrict fun _ ↦ LinearMap.map_mem_ker_of_comp_eq f.toLinearMap (toLinearMap_comp_eq h)

@[simp, norm_cast] theorem toLinearMap_kerMapL (h : g ∘L T₁ = T₂ ∘L f) :
    (kerMapL h).toLinearMap =
      f.toLinearMap.restrict fun _ ↦
        LinearMap.map_mem_ker_of_comp_eq f.toLinearMap (toLinearMap_comp_eq h) := by
  ext x; rfl

@[simp] theorem coe_kerMapL (h : g ∘L T₁ = T₂ ∘L f) :
    ⇑(kerMapL h) =
      f.toLinearMap.restrict fun _ ↦
        LinearMap.map_mem_ker_of_comp_eq f.toLinearMap (toLinearMap_comp_eq h) :=
  congrArg DFunLike.coe (toLinearMap_kerMapL h)

theorem coe_kerMapL_apply (h : g ∘L T₁ = T₂ ∘L f) (x : T₁.ker) : (kerMapL h x : E₂) = f x := (rfl)

@[simp] theorem subtypeL_comp_kerMapL (h : g ∘L T₁ = T₂ ∘L f) :
    T₂.ker.subtypeL ∘L kerMapL h = f ∘L T₁.ker.subtypeL := (rfl)

@[simp] theorem kerMapL_zero (h : g ∘L T₁ = T₂ ∘L (0 : E₁ →L[R] E₂)) : kerMapL h = 0 := by ext; simp

@[simp] theorem kerMapL_id {T : E₁ →L[R] F₁}
    (h : ContinuousLinearMap.id R F₁ ∘L T = T ∘L ContinuousLinearMap.id R E₁ := rfl) :
    kerMapL h = ContinuousLinearMap.id R T.ker := by ext; rfl

theorem kerMapL_comp (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (h₁₃ : (g₂ ∘L g₁) ∘L T₁ = T₃ ∘L (f₂ ∘L f₁) := by
      rw [ContinuousLinearMap.comp_assoc, h₁₂, ← ContinuousLinearMap.comp_assoc, h₂₃,
        ContinuousLinearMap.comp_assoc]) :
    kerMapL h₁₃ = kerMapL h₂₃ ∘L kerMapL h₁₂ := by ext; rfl

/-- If `f` is injective, then the induced continuous linear map on kernels is injective. -/
theorem kerMapL_injective (h : g ∘L T₁ = T₂ ∘L f) (hf : Function.Injective f) :
    Function.Injective (kerMapL h) :=
  fun _ _ hxy ↦ Subtype.ext (hf (congrArg Subtype.val hxy))

/-- Exactness of the continuous snake sequence at `ker T₂`. -/
theorem exact_kerMapL (hf : Function.Exact f₁ f₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    Function.Exact (kerMapL h₁₂) (kerMapL h₂₃) := by
  rw [coe_kerMapL, coe_kerMapL]
  exact hf.restrict_ker hg₁ (toLinearMap_comp_eq h₁₂) (toLinearMap_comp_eq h₂₃)

end KerMapL

section CokerMapL

variable {R E₁ E₂ E₃ F₁ F₂ F₃ : Type*} [Ring R]
  [TopologicalSpace E₁] [AddCommMonoid E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommMonoid E₂] [Module R E₂]
  [TopologicalSpace E₃] [AddCommMonoid E₃] [Module R E₃]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module R F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module R F₂]
  [TopologicalSpace F₃] [AddCommGroup F₃] [Module R F₃]
  {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
  {f f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}

/-- Continuous linear map `(F₁ ⧸ range T₁) →L[R] (F₂ ⧸ range T₂)` on quotient cokernels induced by
a commuting square `g ∘L T₁ = T₂ ∘L f`. -/
def cokerMapL (h : g ∘L T₁ = T₂ ∘L f) : (F₁ ⧸ T₁.range) →L[R] (F₂ ⧸ T₂.range) :=
  T₁.range.mapQL T₂.range g
    (LinearMap.range_le_comap_range_of_comp_eq (toLinearMap_comp_eq h))

theorem cokerMapL_mk (h : g ∘L T₁ = T₂ ∘L f) (y : F₁) :
    cokerMapL h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (g y) := Submodule.mapQL_mk ..

@[simp, norm_cast] theorem toLinearMap_cokerMapL (h : g ∘L T₁ = T₂ ∘L f) :
    (cokerMapL h).toLinearMap =
      T₁.range.mapQ T₂.range g.toLinearMap
        (LinearMap.range_le_comap_range_of_comp_eq (toLinearMap_comp_eq h)) :=
  Submodule.toLinearMap_mapQL ..

@[simp] theorem coe_cokerMapL (h : g ∘L T₁ = T₂ ∘L f) :
    ⇑(cokerMapL h) =
      T₁.range.mapQ T₂.range g.toLinearMap
        (LinearMap.range_le_comap_range_of_comp_eq (toLinearMap_comp_eq h)) :=
  congrArg DFunLike.coe (toLinearMap_cokerMapL h)

@[simp] theorem cokerMapL_comp_mkQL (h : g ∘L T₁ = T₂ ∘L f) :
    cokerMapL h ∘L T₁.range.mkQL = T₂.range.mkQL ∘L g := by simp [cokerMapL]

@[simp] theorem cokerMapL_zero (h : (0 : F₁ →L[R] F₂) ∘L T₁ = T₂ ∘L f) : cokerMapL h = 0 := by
  ext; simp

@[simp] theorem cokerMapL_id {T : E₁ →L[R] F₁}
    (h : ContinuousLinearMap.id R F₁ ∘L T = T ∘L ContinuousLinearMap.id R E₁ := rfl) :
    cokerMapL h = ContinuousLinearMap.id R (F₁ ⧸ T.range) := by simp [cokerMapL]

theorem cokerMapL_comp (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    (h₁₃ : (g₂ ∘L g₁) ∘L T₁ = T₃ ∘L (f₂ ∘L f₁) := by
      rw [ContinuousLinearMap.comp_assoc, h₁₂, ← ContinuousLinearMap.comp_assoc, h₂₃,
        ContinuousLinearMap.comp_assoc]) :
    cokerMapL h₁₃ = cokerMapL h₂₃ ∘L cokerMapL h₁₂ :=
  T₁.range.mapQL_comp T₂.range T₃.range g₁ g₂ _ _

/-- If `g` is surjective, then the induced continuous linear map on quotient cokernels is
surjective. -/
theorem cokerMapL_surjective (h : g ∘L T₁ = T₂ ∘L f) (hg : Function.Surjective g) :
    Function.Surjective (cokerMapL h) := by
  rw [coe_cokerMapL]; exact Submodule.mapQ_surjective _ _ g.toLinearMap _ hg

/-- Exactness of the continuous snake sequence at `F₂ ⧸ range T₂`. -/
theorem exact_cokerMapL (hf₂ : Function.Surjective f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    Function.Exact (cokerMapL h₁₂) (cokerMapL h₂₃) := by
  rw [coe_cokerMapL, coe_cokerMapL]
  exact hg.mapQ_range hf₂ (toLinearMap_comp_eq h₁₂) (toLinearMap_comp_eq h₂₃)

end CokerMapL

end TauCeti

section ContinuousSnake

open TauCeti
open ContinuousLinearMap (toLinearMap_comp_eq)

universe u u₁ u₂ u₃ v₁ v₂ v₃

section Ring

variable {R : Type u} [Ring R]
  {E₁ : Type u₁} {E₂ : Type u₂} {E₃ : Type u₃} {F₁ : Type v₁} {F₂ : Type v₂} {F₃ : Type v₃}
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module R E₂]
  [TopologicalSpace E₃] [AddCommGroup E₃] [Module R E₃]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module R F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module R F₂]
  [TopologicalSpace F₃] [AddCommGroup F₃] [Module R F₃]
  {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
  {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}

private abbrev intLin {M N : Type*} [TopologicalSpace M] [AddCommGroup M] [Module R M]
    [TopologicalSpace N] [AddCommGroup N] [Module R N] (φ : M →L[R] N) : M →ₗ[ℤ] N :=
  φ.toAddMonoidHom.toIntLinearMap

private theorem intLin_comp_eq {M N P Q : Type*}
    [TopologicalSpace M] [AddCommGroup M] [Module R M]
    [TopologicalSpace N] [AddCommGroup N] [Module R N]
    [TopologicalSpace P] [AddCommGroup P] [Module R P]
    [TopologicalSpace Q] [AddCommGroup Q] [Module R Q]
    {a₁ : N →L[R] P} {b₁ : M →L[R] N} {a₂ : Q →L[R] P} {b₂ : M →L[R] Q}
    (h : a₁ ∘L b₁ = a₂ ∘L b₂) :
    (intLin a₁).comp (intLin b₁) = (intLin a₂).comp (intLin b₂) :=
  LinearMap.ext fun x ↦ DFunLike.congr_fun h x

private theorem exact_intLin_subtypeL {M N : Type*}
    [TopologicalSpace M] [AddCommGroup M] [Module R M]
    [TopologicalSpace N] [AddCommGroup N] [Module R N] (T : M →L[R] N) :
    Function.Exact (intLin T.ker.subtypeL) (intLin T) := by
  simp [Function.Exact, LinearMap.mem_ker]

private theorem exact_intLin_mkQL {M N : Type*}
    [TopologicalSpace M] [AddCommGroup M] [Module R M]
    [TopologicalSpace N] [AddCommGroup N] [Module R N] (T : M →L[R] N) :
    Function.Exact (intLin T) (intLin T.range.mkQL) := fun _ ↦ by
  simp [Submodule.Quotient.mk_eq_zero]

/-- Continuous connecting linear map `ker T₃ →L[R] F₁ ⧸ range T₁` of a snake diagram whose top
surjection `f₂` has a continuous linear right inverse `σ` and whose bottom injection `g₁` has a
continuous linear left inverse `ρ`. -/
def Function.Exact.snakeδL (_hf : Function.Exact f₁ f₂) (_hg : Function.Exact g₁ g₂)
    (_h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (_h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (_hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (_hρ : Function.LeftInverse ρ g₁) :
    T₃.ker →L[R] F₁ ⧸ T₁.range :=
  T₁.range.mkQL ∘L ρ ∘L T₂ ∘L σ ∘L T₃.ker.subtypeL

section
variable (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
  (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
  {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
  {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁)

theorem Function.Exact.snakeδL_def :
    hf.snakeδL hg h₁₂ h₂₃ hσ hρ = T₁.range.mkQL ∘L ρ ∘L T₂ ∘L σ ∘L T₃.ker.subtypeL := (rfl)

@[simp] theorem Function.Exact.snakeδL_apply (x₃ : T₃.ker) :
    hf.snakeδL hg h₁₂ h₂₃ hσ hρ x₃ = Submodule.Quotient.mk (ρ (T₂ (σ x₃))) := (rfl)

/-- Diagram-chase formula for `Function.Exact.snakeδL`: if `f₂ x₂ = x₃` and `g₁ y₁ = T₂ x₂`, then
`snakeδL` sends `x₃` to the class of `y₁` modulo `range T₁`. -/
theorem Function.Exact.snakeδL_eq (x₃ : T₃.ker) (x₂ : E₂) (y₁ : F₁) (hx₂ : f₂ x₂ = x₃)
    (hy₁ : g₁ y₁ = T₂ x₂) :
    hf.snakeδL hg h₁₂ h₂₃ hσ hρ x₃ = Submodule.Quotient.mk y₁ :=
  SnakeLemma.δ_eq (intLin T₁) (intLin T₂) (intLin T₃) (intLin f₁) (intLin f₂) hf
    (intLin g₁) (intLin g₂) hg (intLin_comp_eq h₁₂) (intLin_comp_eq h₂₃) σ (funext hσ) ρ
    (funext hρ) (intLin T₃.ker.subtypeL) (exact_intLin_subtypeL T₃) (intLin T₁.range.mkQL)
    (exact_intLin_mkQL T₁) x₃ x₂ hx₂ y₁ hy₁

/-- Exactness of the continuous snake sequence at `ker T₃`. -/
theorem Function.Exact.exact_kerMapL_snakeδL :
    Function.Exact (kerMapL h₂₃) (hf.snakeδL hg h₁₂ h₂₃ hσ hρ) :=
  SnakeLemma.exact_δ_right (intLin T₁) (intLin T₂) (intLin T₃) (intLin f₁) (intLin f₂) hf
    (intLin g₁) (intLin g₂) hg (intLin_comp_eq h₁₂) (intLin_comp_eq h₂₃) σ (funext hσ) ρ
    (funext hρ) (intLin T₂.ker.subtypeL) (exact_intLin_subtypeL T₂) (intLin T₃.ker.subtypeL)
    (exact_intLin_subtypeL T₃) (intLin T₁.range.mkQL) (exact_intLin_mkQL T₁)
    (intLin (kerMapL h₂₃)) rfl Subtype.coe_injective

/-- Exactness of the continuous snake sequence at `F₁ ⧸ range T₁`. -/
theorem Function.Exact.exact_snakeδL_cokerMapL :
    Function.Exact (hf.snakeδL hg h₁₂ h₂₃ hσ hρ) (cokerMapL h₁₂) :=
  SnakeLemma.exact_δ_left (intLin T₁) (intLin T₂) (intLin T₃) (intLin f₁) (intLin f₂) hf
    (intLin g₁) (intLin g₂) hg (intLin_comp_eq h₁₂) (intLin_comp_eq h₂₃) σ (funext hσ) ρ
    (funext hρ) (intLin T₃.ker.subtypeL) (exact_intLin_subtypeL T₃) (intLin T₁.range.mkQL)
    (exact_intLin_mkQL T₁) (intLin T₂.range.mkQL) (exact_intLin_mkQL T₂)
    (intLin (cokerMapL h₁₂)) (LinearMap.ext (cokerMapL_mk h₁₂))
    (Submodule.Quotient.mk_surjective _)

end

/-- **Splitting independence of `Function.Exact.snakeδL`**: any two choices `(σ, ρ)` and `(σ', ρ')`
of continuous linear splittings induce the same continuous connecting map. -/
theorem Function.Exact.snakeδL_eq_snakeδL (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ σ' : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂) (hσ' : Function.RightInverse σ' f₂)
    {ρ ρ' : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) (hρ' : Function.LeftInverse ρ' g₁) :
    hf.snakeδL hg h₁₂ h₂₃ hσ hρ = hf.snakeδL hg h₁₂ h₂₃ hσ' hρ' := by
  ext x₃
  have haux := SnakeLemma.δ_aux (intLin T₂) (intLin T₃) (intLin f₂) (intLin g₁) (intLin g₂) hg
    (intLin_comp_eq h₂₃) σ (funext hσ) ρ (funext hρ) (intLin T₃.ker.subtypeL)
    (exact_intLin_subtypeL T₃) x₃
  have haux' := SnakeLemma.δ_aux (intLin T₂) (intLin T₃) (intLin f₂) (intLin g₁) (intLin g₂) hg
    (intLin_comp_eq h₂₃) σ' (funext hσ') ρ' (funext hρ') (intLin T₃.ker.subtypeL)
    (exact_intLin_subtypeL T₃) x₃
  have hd := SnakeLemma.δ'_eq (intLin T₁) (intLin T₂) (intLin T₃) (intLin f₁) (intLin f₂) hf
    (intLin g₁) (intLin g₂) hg (intLin_comp_eq h₁₂) (intLin_comp_eq h₂₃) (intLin T₃.ker.subtypeL)
    (exact_intLin_subtypeL T₃) (intLin T₁.range.mkQL) (exact_intLin_mkQL T₁)
    hσ.surjective hρ.injective x₃ (σ x₃) (hσ x₃) (ρ (T₂ (σ x₃))) haux
  have hd' := SnakeLemma.δ'_eq (intLin T₁) (intLin T₂) (intLin T₃) (intLin f₁) (intLin f₂) hf
    (intLin g₁) (intLin g₂) hg (intLin_comp_eq h₁₂) (intLin_comp_eq h₂₃) (intLin T₃.ker.subtypeL)
    (exact_intLin_subtypeL T₃) (intLin T₁.range.mkQL) (exact_intLin_mkQL T₁)
    hσ.surjective hρ.injective x₃ (σ' x₃) (hσ' x₃) (ρ' (T₂ (σ' x₃))) haux'
  exact hd.symm.trans hd'

end Ring

section CommRing

variable {R : Type u} [CommRing R]
  {E₁ : Type u₁} {E₂ : Type u₂} {E₃ : Type u₃} {F₁ : Type v₁} {F₂ : Type v₂} {F₃ : Type v₃}
  [TopologicalSpace E₁] [AddCommGroup E₁] [Module R E₁]
  [TopologicalSpace E₂] [AddCommGroup E₂] [Module R E₂]
  [TopologicalSpace E₃] [AddCommGroup E₃] [Module R E₃]
  [TopologicalSpace F₁] [AddCommGroup F₁] [Module R F₁]
  [TopologicalSpace F₂] [AddCommGroup F₂] [Module R F₂]
  [TopologicalSpace F₃] [AddCommGroup F₃] [Module R F₃]
  {T₁ : E₁ →L[R] F₁} {T₂ : E₂ →L[R] F₂} {T₃ : E₃ →L[R] F₃}
  {f₁ : E₁ →L[R] E₂} {f₂ : E₂ →L[R] E₃} {g₁ : F₁ →L[R] F₂} {g₂ : F₂ →L[R] F₃}

/-- The underlying linear map of `Function.Exact.snakeδL` is the algebraic snake connecting map
`Function.Exact.snakeδ`. -/
@[simp, norm_cast] theorem Function.Exact.toLinearMap_snakeδL (hf : Function.Exact f₁ f₂)
    (hg : Function.Exact g₁ g₂) (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) :
    (hf.snakeδL hg h₁₂ h₂₃ hσ hρ).toLinearMap =
      hf.snakeδ hg hσ.surjective hρ.injective (toLinearMap_comp_eq h₁₂)
        (toLinearMap_comp_eq h₂₃) :=
  (hf.snakeδ_eq_of_rightInverse_of_leftInverse hg (toLinearMap_comp_eq h₁₂)
    (toLinearMap_comp_eq h₂₃) hσ hρ).symm

theorem Function.Exact.coe_snakeδL (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) :
    ⇑(hf.snakeδL hg h₁₂ h₂₃ hσ hρ) =
      hf.snakeδ hg hσ.surjective hρ.injective (toLinearMap_comp_eq h₁₂)
        (toLinearMap_comp_eq h₂₃) :=
  congrArg DFunLike.coe (hf.toLinearMap_snakeδL hg h₁₂ h₂₃ hσ hρ)

section
variable (hf : Function.Exact f₁ f₂) (hf₂ : IsOpenQuotientMap f₂)
  (hg : Function.Exact g₁ g₂) (hg₁ : Topology.IsEmbedding g₁)
  (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)

include hf hf₂ hg hg₁ h₁₂ h₂₃

/-- **Automatic continuity of the snake connecting map**: if `f₂` is an open quotient map and `g₁`
is a topological embedding in a commuting diagram with exact rows, then `Function.Exact.snakeδ` is
continuous, with no splitting hypotheses. -/
theorem TauCeti.continuous_snakeδ_of_isOpenQuotientMap_of_isEmbedding :
    Continuous (hf.snakeδ hg hf₂.surjective hg₁.injective
      (toLinearMap_comp_eq h₁₂) (toLinearMap_comp_eq h₂₃)) := by
  let p := (T₃.ker : Set E₃).restrictPreimage f₂
  have hp : Topology.IsQuotientMap p := (hf₂.restrictPreimage (T₃.ker : Set E₃)).isQuotientMap
  have hmem : ∀ x : f₂ ⁻¹' (T₃.ker : Set E₃), ∃ y₁ : F₁, g₁ y₁ = T₂ x.val := fun x ↦
    (hg (T₂ x.val)).mp <| by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_coe] using
        (DFunLike.congr_fun h₂₃ x.val).trans (LinearMap.mem_ker.mp x.property)
  let φ : f₂ ⁻¹' (T₃.ker : Set E₃) → F₁ := fun x ↦ (hmem x).choose
  have hφ : ∀ x, g₁ (φ x) = T₂ x.val := fun x ↦ (hmem x).choose_spec
  have hφ_cont : Continuous φ := hg₁.isInducing.continuous_iff.mpr <| by
    simpa only [Function.comp_def, hφ] using T₂.continuous.comp continuous_subtypeVal
  rw [hp.continuous_iff]
  have hcomp : hf.snakeδ hg hf₂.surjective hg₁.injective
      (toLinearMap_comp_eq h₁₂) (toLinearMap_comp_eq h₂₃) ∘ p = T₁.range.mkQL ∘ φ :=
    funext fun x ↦ hf.snakeδ_apply hg hf₂.surjective hg₁.injective _ _ (p x) x.val
      (Set.restrictPreimage_coe _ _ x).symm (φ x) (hφ x)
  exact hcomp ▸ T₁.range.mkQL.continuous.comp hφ_cont

/-- Continuous snake connecting map bundled without splittings whenever `f₂` is an open quotient map
and `g₁` is a topological embedding. -/
noncomputable def Function.Exact.snakeδLOfIsOpenQuotientMapOfIsEmbedding :
    T₃.ker →L[R] F₁ ⧸ T₁.range :=
  { hf.snakeδ hg hf₂.surjective hg₁.injective (toLinearMap_comp_eq h₁₂)
      (toLinearMap_comp_eq h₂₃) with
    cont := continuous_snakeδ_of_isOpenQuotientMap_of_isEmbedding hf hf₂ hg hg₁ h₁₂ h₂₃ }

@[simp, norm_cast] theorem Function.Exact.toLinearMap_snakeδLOfIsOpenQuotientMapOfIsEmbedding :
    (hf.snakeδLOfIsOpenQuotientMapOfIsEmbedding hf₂ hg hg₁ h₁₂ h₂₃).toLinearMap =
      hf.snakeδ hg hf₂.surjective hg₁.injective (toLinearMap_comp_eq h₁₂)
        (toLinearMap_comp_eq h₂₃) := (rfl)

@[simp] theorem Function.Exact.coe_snakeδLOfIsOpenQuotientMapOfIsEmbedding :
    ⇑(hf.snakeδLOfIsOpenQuotientMapOfIsEmbedding hf₂ hg hg₁ h₁₂ h₂₃) =
      hf.snakeδ hg hf₂.surjective hg₁.injective (toLinearMap_comp_eq h₁₂)
        (toLinearMap_comp_eq h₂₃) := (rfl)

/-- Diagram-chase formula for `Function.Exact.snakeδLOfIsOpenQuotientMapOfIsEmbedding`. -/
theorem Function.Exact.snakeδLOfIsOpenQuotientMapOfIsEmbedding_eq (x₃ : T₃.ker) (x₂ : E₂) (y₁ : F₁)
    (hx₂ : f₂ x₂ = x₃) (hy₁ : g₁ y₁ = T₂ x₂) :
    hf.snakeδLOfIsOpenQuotientMapOfIsEmbedding hf₂ hg hg₁ h₁₂ h₂₃ x₃ = Submodule.Quotient.mk y₁ :=
  hf.snakeδ_apply hg hf₂.surjective hg₁.injective _ _ x₃ x₂ hx₂ y₁ hy₁

/-- When continuous linear splittings `(σ, ρ)` also exist,
`Function.Exact.snakeδLOfIsOpenQuotientMapOfIsEmbedding` agrees with `Function.Exact.snakeδL`. -/
theorem Function.Exact.snakeδLOfIsOpenQuotientMapOfIsEmbedding_eq_snakeδL
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) :
    hf.snakeδLOfIsOpenQuotientMapOfIsEmbedding hf₂ hg hg₁ h₁₂ h₂₃ =
      hf.snakeδL hg h₁₂ h₂₃ hσ hρ :=
  ContinuousLinearMap.coe_injective (hf.toLinearMap_snakeδL hg h₁₂ h₂₃ hσ hρ).symm

/-- Exactness of `Function.Exact.snakeδLOfIsOpenQuotientMapOfIsEmbedding` at `ker T₃`. -/
theorem Function.Exact.exact_kerMapL_snakeδLOfIsOpenQuotientMapOfIsEmbedding :
    Function.Exact (kerMapL h₂₃)
      (hf.snakeδLOfIsOpenQuotientMapOfIsEmbedding hf₂ hg hg₁ h₁₂ h₂₃) := by
  simpa only [coe_kerMapL, coe_snakeδLOfIsOpenQuotientMapOfIsEmbedding] using
    hf.restrict_ker_snakeδ hg hf₂.surjective hg₁.injective
      (toLinearMap_comp_eq h₁₂) (toLinearMap_comp_eq h₂₃)

/-- Exactness of `Function.Exact.snakeδLOfIsOpenQuotientMapOfIsEmbedding` at `F₁ ⧸ range T₁`. -/
theorem Function.Exact.exact_snakeδLOfIsOpenQuotientMapOfIsEmbedding_cokerMapL :
    Function.Exact (hf.snakeδLOfIsOpenQuotientMapOfIsEmbedding hf₂ hg hg₁ h₁₂ h₂₃)
      (cokerMapL h₁₂) := by
  simpa only [coe_snakeδLOfIsOpenQuotientMapOfIsEmbedding, coe_cokerMapL] using
    hf.snakeδ_mapQ_range hg hf₂.surjective hg₁.injective
      (toLinearMap_comp_eq h₁₂) (toLinearMap_comp_eq h₂₃)

end

end CommRing

end ContinuousSnake
