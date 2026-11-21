/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.OpenQuotient
public import TauCeti.Algebra.Module.SnakeLemma
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Index
public import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.UpperTriangularBlock
public import TauCeti.Topology.Algebra.Module.Quotient
import Mathlib.Topology.LocalAtTarget

/-!
# Continuous snake sequences and the composition snake diagram

A commuting diagram `(T₁, T₂, T₃)` of continuous linear maps between exact rows
`E₁ --f₁--> E₂ --f₂--> E₃ → 0` and `0 → F₁ --g₁--> F₂ --g₂--> F₃` induces continuous linear maps
on kernels (`TauCeti.kerMapL`) and quotient cokernels (`TauCeti.cokerMapL`).

We bundle the algebraic connecting map `Function.Exact.snakeδ : ker T₃ →ₗ[R] F₁ ⧸ range T₁` as a
continuous linear map in two settings:

* Given a continuous linear right inverse `σ` of `f₂` and left inverse `ρ` of `g₁`,
  `TauCeti.snakeδL` equals `T₁.range.mkQL ∘L ρ ∘L T₂ ∘L σ ∘L T₃.ker.subtypeL`, independent of
  `(σ, ρ)` (`TauCeti.snakeδL_eq_snakeδL`).
* Over a commutative ring, whenever `f₂` is an open quotient map and `g₁` is a topological
  embedding, `TauCeti.continuous_snakeδ_of_isOpenQuotientMap_of_isEmbedding` proves continuity
  directly without splittings, bundled as `TauCeti.snakeδLOfIsOpenQuotientMap`.

Specializing to `ContinuousLinearMap.upperTriangularBlock A B D` yields
`ContinuousLinearMap.snakeδL_upperTriangularBlock_eq`, and specializing further to
`ContinuousLinearMap.compSnakeMiddle T S = upperTriangularBlock T (-id) S` gives the coordinate
factorization `ContinuousLinearMap.exists_compSnakeMiddle_eq_comp_prodMap_comp` and
`(compSnakeMiddle T S).index = (S ∘L T).index` (`ContinuousLinearMap.index_compSnakeMiddle`).

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
  rintro ⟨y, hy⟩
  constructor
  · intro h0
    obtain ⟨x, rfl⟩ := (hf y).1 (congrArg Subtype.val h0)
    refine ⟨⟨x, hg₁ ?_⟩, rfl⟩
    rw [map_zero, ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.comp_apply g₁ T₁, h₁₂,
      ContinuousLinearMap.comp_apply]
    exact hy
  · rintro ⟨⟨x, _⟩, hxy⟩
    ext
    rw [← hxy, coe_kerMapL_apply, coe_kerMapL_apply, hf.apply_apply_eq_zero,
      ZeroMemClass.coe_zero]

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
        (LinearMap.range_le_comap_range_of_comp_eq (toLinearMap_comp_eq h)) := by
  ext y; exact (cokerMapL_mk h y).trans rfl

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
    cokerMapL h₁₃ = cokerMapL h₂₃ ∘L cokerMapL h₁₂ := by
  refine T₁.range.comp_mkQL_injective ?_
  dsimp only
  rw [cokerMapL_comp_mkQL, ContinuousLinearMap.comp_assoc, cokerMapL_comp_mkQL,
    ← ContinuousLinearMap.comp_assoc (cokerMapL h₂₃), cokerMapL_comp_mkQL]
  rfl

/-- If `g` is surjective, then the induced continuous linear map on quotient cokernels is
surjective. -/
theorem cokerMapL_surjective (h : g ∘L T₁ = T₂ ∘L f) (hg : Function.Surjective g) :
    Function.Surjective (cokerMapL h) := by
  rw [coe_cokerMapL]; exact Submodule.mapQ_surjective _ _ g.toLinearMap _ hg

/-- Exactness of the continuous snake sequence at `F₂ ⧸ range T₂`. -/
theorem exact_cokerMapL (hf₂ : Function.Surjective f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂) :
    Function.Exact (cokerMapL h₁₂) (cokerMapL h₂₃) := by
  rw [coe_cokerMapL, coe_cokerMapL,
    (hg : Function.Exact g₁.toLinearMap g₂.toLinearMap).exact_mapQ_iff]
  rintro _ ⟨-, z, rfl⟩
  obtain ⟨w, rfl⟩ := hf₂ z
  exact ⟨T₂ w, ⟨w, rfl⟩, DFunLike.congr_fun h₂₃ w⟩

end CokerMapL

section ContinuousSnake

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

/-- Continuous connecting linear map `ker T₃ →L[R] F₁ ⧸ range T₁` of a snake diagram whose top
surjection `f₂` has a continuous linear right inverse `σ` and whose bottom injection `g₁` has a
continuous linear left inverse `ρ`. -/
def snakeδL (_hf : Function.Exact f₁ f₂) (_hg : Function.Exact g₁ g₂)
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

theorem snakeδL_def :
    snakeδL hf hg h₁₂ h₂₃ hσ hρ = T₁.range.mkQL ∘L ρ ∘L T₂ ∘L σ ∘L T₃.ker.subtypeL := (rfl)

@[simp] theorem snakeδL_apply (x₃ : T₃.ker) :
    snakeδL hf hg h₁₂ h₂₃ hσ hρ x₃ = Submodule.Quotient.mk (ρ (T₂ (σ x₃))) := (rfl)

/-- Diagram-chase formula for `TauCeti.snakeδL`: if `f₂ x₂ = x₃` and `g₁ y₁ = T₂ x₂`, then
`snakeδL` sends `x₃` to the class of `y₁` modulo `range T₁`. -/
theorem snakeδL_eq (x₃ : T₃.ker) (x₂ : E₂) (y₁ : F₁) (hx₂ : f₂ x₂ = x₃) (hy₁ : g₁ y₁ = T₂ x₂) :
    snakeδL hf hg h₁₂ h₂₃ hσ hρ x₃ = Submodule.Quotient.mk y₁ := by
  obtain ⟨x₁, hx₁⟩ := (hf (σ x₃ - x₂)).mp <| by rw [map_sub, hσ x₃, hx₂, sub_self]
  have hy : ρ (T₂ (σ x₃)) = y₁ + T₁ x₁ := by
    have hdiff : T₂ (σ x₃) - g₁ y₁ = g₁ (T₁ x₁) := by
      rw [hy₁, ← map_sub, ← hx₁, ← ContinuousLinearMap.comp_apply T₂ f₁, ← h₁₂,
        ContinuousLinearMap.comp_apply]
    calc
      ρ (T₂ (σ x₃)) = ρ (g₁ (y₁ + T₁ x₁)) := by
        rw [map_add, ← hdiff, add_sub_cancel]
      _ = y₁ + T₁ x₁ := hρ _
  simp only [snakeδL_apply, hy]
  exact (Submodule.Quotient.eq (p := T₁.range)).2 <| by simp [sub_eq_add_neg]

/-- Exactness of the continuous snake sequence at `ker T₃`. -/
theorem exact_kerMapL_snakeδL : Function.Exact (kerMapL h₂₃) (snakeδL hf hg h₁₂ h₂₃ hσ hρ) := by
  intro x₃
  constructor
  · intro hx
    obtain ⟨x₁, hx₁⟩ := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨y₁, hy₁⟩ := (hg (T₂ (σ x₃))).mp <| by
      rw [← ContinuousLinearMap.comp_apply g₂ T₂, h₂₃, ContinuousLinearMap.comp_apply, hσ x₃]
      exact LinearMap.mem_ker.mp x₃.property
    have hρy : y₁ = T₁ x₁ := by
      have hx₁' : ρ (T₂ (σ x₃)) = T₁ x₁ := by simpa [snakeδL_apply] using hx₁.symm
      rw [← hρ y₁, hy₁, hx₁']
    have hmem : σ x₃ - f₁ x₁ ∈ T₂.ker := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, map_sub,
        ← ContinuousLinearMap.comp_apply T₂ f₁, ← h₁₂, ContinuousLinearMap.comp_apply,
        ← hρy, hy₁, sub_self]
    refine ⟨⟨σ x₃ - f₁ x₁, hmem⟩, Subtype.ext ?_⟩
    change f₂ (σ x₃ - f₁ x₁) = x₃
    simp [hσ x₃, hf.apply_apply_eq_zero]
  · rintro ⟨x₂, rfl⟩
    have hx₂ : T₂ (x₂ : E₂) = 0 := LinearMap.mem_ker.mp x₂.property
    exact (snakeδL_eq hf hg h₁₂ h₂₃ hσ hρ (kerMapL h₂₃ x₂) x₂ 0 rfl (by simp [hx₂])).trans
      (Submodule.Quotient.mk_zero T₁.range)

/-- Exactness of the continuous snake sequence at `F₁ ⧸ range T₁`. -/
theorem exact_snakeδL_cokerMapL : Function.Exact (snakeδL hf hg h₁₂ h₂₃ hσ hρ) (cokerMapL h₁₂) := by
  intro q
  obtain ⟨y₁, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  constructor
  · intro hq
    rw [cokerMapL_mk, Submodule.Quotient.mk_eq_zero] at hq
    obtain ⟨x₂, hx₂⟩ := hq
    rw [ContinuousLinearMap.coe_coe] at hx₂
    have hx₃ : f₂ x₂ ∈ T₃.ker := by
      rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ← ContinuousLinearMap.comp_apply T₃ f₂,
        ← h₂₃, ContinuousLinearMap.comp_apply, hx₂, hg.apply_apply_eq_zero]
    exact ⟨⟨f₂ x₂, hx₃⟩, snakeδL_eq hf hg h₁₂ h₂₃ hσ hρ ⟨f₂ x₂, hx₃⟩ x₂ y₁ rfl hx₂.symm⟩
  · rintro ⟨x₃, hx₃⟩
    obtain ⟨y₁', hy₁'⟩ := (hg (T₂ (σ x₃))).mp <| by
      rw [← ContinuousLinearMap.comp_apply g₂ T₂, h₂₃, ContinuousLinearMap.comp_apply, hσ x₃]
      exact LinearMap.mem_ker.mp x₃.property
    have hq : (Submodule.Quotient.mk y₁ : F₁ ⧸ T₁.range) = Submodule.Quotient.mk y₁' :=
      hx₃.symm.trans (snakeδL_eq hf hg h₁₂ h₂₃ hσ hρ x₃ (σ x₃) y₁' (hσ x₃) hy₁')
    obtain ⟨x₁, hx₁⟩ := (Submodule.Quotient.eq (p := T₁.range)).1 hq
    rw [ContinuousLinearMap.coe_coe] at hx₁
    have hy₁_eq : y₁ = T₁ x₁ + y₁' := eq_add_of_sub_eq hx₁.symm
    rw [cokerMapL_mk, Submodule.Quotient.mk_eq_zero]
    refine ⟨σ x₃ + f₁ x₁, ?_⟩
    rw [ContinuousLinearMap.coe_coe, map_add, ← ContinuousLinearMap.comp_apply T₂ f₁, ← h₁₂,
      ContinuousLinearMap.comp_apply, ← hy₁', ← map_add, add_comm y₁' (T₁ x₁), ← hy₁_eq]

end

/-- **Splitting independence of `TauCeti.snakeδL`**: any two choices `(σ, ρ)` and `(σ', ρ')` of
continuous linear splittings induce the same continuous connecting map. -/
theorem snakeδL_eq_snakeδL (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ σ' : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂) (hσ' : Function.RightInverse σ' f₂)
    {ρ ρ' : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) (hρ' : Function.LeftInverse ρ' g₁) :
    snakeδL hf hg h₁₂ h₂₃ hσ hρ = snakeδL hf hg h₁₂ h₂₃ hσ' hρ' := by
  ext x₃
  obtain ⟨y₁', hy₁'⟩ := (hg (T₂ (σ' x₃))).mp <| by
    rw [← ContinuousLinearMap.comp_apply g₂ T₂, h₂₃, ContinuousLinearMap.comp_apply, hσ' x₃]
    exact LinearMap.mem_ker.mp x₃.property
  exact (snakeδL_eq hf hg h₁₂ h₂₃ hσ hρ x₃ (σ' x₃) y₁' (hσ' x₃) hy₁').trans
    (snakeδL_eq hf hg h₁₂ h₂₃ hσ' hρ' x₃ (σ' x₃) y₁' (hσ' x₃) hy₁').symm

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

/-- The underlying linear map of `TauCeti.snakeδL` is the algebraic snake connecting map
`Function.Exact.snakeδ`. -/
@[simp, norm_cast] theorem toLinearMap_snakeδL (hf : Function.Exact f₁ f₂)
    (hg : Function.Exact g₁ g₂) (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) :
    (snakeδL hf hg h₁₂ h₂₃ hσ hρ).toLinearMap =
      hf.snakeδ hg hσ.surjective hρ.injective (toLinearMap_comp_eq h₁₂)
        (toLinearMap_comp_eq h₂₃) :=
  (hf.snakeδ_eq_of_rightInverse_of_leftInverse hg (toLinearMap_comp_eq h₁₂)
    (toLinearMap_comp_eq h₂₃) hσ hρ).symm

theorem coe_snakeδL (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) :
    ⇑(snakeδL hf hg h₁₂ h₂₃ hσ hρ) =
      hf.snakeδ hg hσ.surjective hρ.injective (toLinearMap_comp_eq h₁₂)
        (toLinearMap_comp_eq h₂₃) :=
  congrArg DFunLike.coe (toLinearMap_snakeδL hf hg h₁₂ h₂₃ hσ hρ)

section
variable (hf : Function.Exact f₁ f₂) (hf₂ : IsOpenQuotientMap f₂)
  (hg : Function.Exact g₁ g₂) (hg₁ : Topology.IsEmbedding g₁)
  (h₁₂ : g₁ ∘L T₁ = T₂ ∘L f₁) (h₂₃ : g₂ ∘L T₂ = T₃ ∘L f₂)

include hf hf₂ hg hg₁ h₁₂ h₂₃

/-- **Automatic continuity of the snake connecting map**: if `f₂` is an open quotient map and `g₁`
is a topological embedding in a commuting diagram with exact rows, then `Function.Exact.snakeδ` is
continuous, with no splitting hypotheses. -/
theorem continuous_snakeδ_of_isOpenQuotientMap_of_isEmbedding :
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
noncomputable def snakeδLOfIsOpenQuotientMap : T₃.ker →L[R] F₁ ⧸ T₁.range :=
  { hf.snakeδ hg hf₂.surjective hg₁.injective (toLinearMap_comp_eq h₁₂)
      (toLinearMap_comp_eq h₂₃) with
    cont := continuous_snakeδ_of_isOpenQuotientMap_of_isEmbedding hf hf₂ hg hg₁ h₁₂ h₂₃ }

@[simp, norm_cast] theorem toLinearMap_snakeδLOfIsOpenQuotientMap :
    (snakeδLOfIsOpenQuotientMap hf hf₂ hg hg₁ h₁₂ h₂₃).toLinearMap =
      hf.snakeδ hg hf₂.surjective hg₁.injective (toLinearMap_comp_eq h₁₂)
        (toLinearMap_comp_eq h₂₃) := (rfl)

@[simp] theorem coe_snakeδLOfIsOpenQuotientMap :
    ⇑(snakeδLOfIsOpenQuotientMap hf hf₂ hg hg₁ h₁₂ h₂₃) =
      hf.snakeδ hg hf₂.surjective hg₁.injective (toLinearMap_comp_eq h₁₂)
        (toLinearMap_comp_eq h₂₃) := (rfl)

/-- Diagram-chase formula for `TauCeti.snakeδLOfIsOpenQuotientMap`. -/
theorem snakeδLOfIsOpenQuotientMap_eq (x₃ : T₃.ker) (x₂ : E₂) (y₁ : F₁)
    (hx₂ : f₂ x₂ = x₃) (hy₁ : g₁ y₁ = T₂ x₂) :
    snakeδLOfIsOpenQuotientMap hf hf₂ hg hg₁ h₁₂ h₂₃ x₃ = Submodule.Quotient.mk y₁ :=
  hf.snakeδ_apply hg hf₂.surjective hg₁.injective _ _ x₃ x₂ hx₂ y₁ hy₁

/-- When continuous linear splittings `(σ, ρ)` also exist, `TauCeti.snakeδLOfIsOpenQuotientMap`
agrees with `TauCeti.snakeδL`. -/
theorem snakeδLOfIsOpenQuotientMap_eq_snakeδL
    {σ : E₃ →L[R] E₂} (hσ : Function.RightInverse σ f₂)
    {ρ : F₂ →L[R] F₁} (hρ : Function.LeftInverse ρ g₁) :
    snakeδLOfIsOpenQuotientMap hf hf₂ hg hg₁ h₁₂ h₂₃ = snakeδL hf hg h₁₂ h₂₃ hσ hρ :=
  ContinuousLinearMap.coe_injective (toLinearMap_snakeδL hf hg h₁₂ h₂₃ hσ hρ).symm

/-- Exactness of `TauCeti.snakeδLOfIsOpenQuotientMap` at `ker T₃`. -/
theorem exact_kerMapL_snakeδLOfIsOpenQuotientMap :
    Function.Exact (kerMapL h₂₃) (snakeδLOfIsOpenQuotientMap hf hf₂ hg hg₁ h₁₂ h₂₃) := by
  simpa only [coe_kerMapL, coe_snakeδLOfIsOpenQuotientMap] using
    hf.restrict_ker_snakeδ hg hf₂.surjective hg₁.injective
      (toLinearMap_comp_eq h₁₂) (toLinearMap_comp_eq h₂₃)

/-- Exactness of `TauCeti.snakeδLOfIsOpenQuotientMap` at `F₁ ⧸ range T₁`. -/
theorem exact_snakeδLOfIsOpenQuotientMap_cokerMapL :
    Function.Exact (snakeδLOfIsOpenQuotientMap hf hf₂ hg hg₁ h₁₂ h₂₃) (cokerMapL h₁₂) := by
  simpa only [coe_snakeδLOfIsOpenQuotientMap, coe_cokerMapL] using
    hf.snakeδ_mapQ_range hg hf₂.surjective hg₁.injective
      (toLinearMap_comp_eq h₁₂) (toLinearMap_comp_eq h₂₃)

end

end CommRing

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
  ext y; simp [TauCeti.snakeδL]

end BlockSnake

section CompSnake

variable {R E F G : Type*} [Ring R]
  [TopologicalSpace E] [AddCommGroup E] [Module R E]
  [TopologicalSpace F] [AddCommGroup F] [Module R F] [IsTopologicalAddGroup F]
  [TopologicalSpace G] [AddCommGroup G] [Module R G]
  (T : E →L[R] F) (S : F →L[R] G)

/-- The middle vertical map `(x, y) ↦ (T x - y, S y)` of the composition snake diagram
`0 → E → E × F → F → 0` over `0 → F → F × G → G → 0`, realizing
`CategoryTheory.kernelCokernelCompSequence.φ` for continuous linear maps. -/
def compSnakeMiddle : E × F →L[R] F × G :=
  upperTriangularBlock T (-ContinuousLinearMap.id R F) S

theorem compSnakeMiddle_def :
    compSnakeMiddle T S = upperTriangularBlock T (-ContinuousLinearMap.id R F) S := (rfl)

@[simp] theorem compSnakeMiddle_apply (xy : E × F) :
    compSnakeMiddle T S xy = (T xy.1 - xy.2, S xy.2) := by simp [compSnakeMiddle, sub_eq_add_neg]

@[simp] theorem compSnakeMiddle_comp_inl :
    compSnakeMiddle T S ∘L inl R E F = inl R F G ∘L T :=
  T.upperTriangularBlock_comp_inl (-ContinuousLinearMap.id R F) S

@[simp] theorem compSnakeMiddle_comp_inr :
    compSnakeMiddle T S ∘L inr R E F = (-ContinuousLinearMap.id R F).prod S :=
  T.upperTriangularBlock_comp_inr (-ContinuousLinearMap.id R F) S

@[simp] theorem fst_comp_compSnakeMiddle :
    fst R F G ∘L compSnakeMiddle T S = T.coprod (-ContinuousLinearMap.id R F) :=
  T.fst_comp_upperTriangularBlock (-ContinuousLinearMap.id R F) S

@[simp] theorem snd_comp_compSnakeMiddle :
    snd R F G ∘L compSnakeMiddle T S = S ∘L snd R E F :=
  T.snd_comp_upperTriangularBlock (-ContinuousLinearMap.id R F) S

/-- In the composition snake diagram `(T, compSnakeMiddle T S, S)`, the continuous connecting map
`ker S →L[R] F ⧸ range T` equals `-(T.range.mkQL ∘L S.ker.subtypeL)`, matching
`CategoryTheory.kernelCokernelCompSequence.δ_fac`. -/
theorem snakeδL_compSnakeMiddle_eq
    {σ : F →L[R] E × F} (hσ : Function.RightInverse σ (snd R E F))
    {ρ : F × G →L[R] F} (hρ : Function.LeftInverse ρ (inl R F G)) :
    TauCeti.snakeδL .inl_snd .inl_snd
      (T.compSnakeMiddle_comp_inl S).symm (T.snd_comp_compSnakeMiddle S) hσ hρ =
        -(T.range.mkQL ∘L S.ker.subtypeL) :=
  (snakeδL_upperTriangularBlock_eq T (-ContinuousLinearMap.id R F) S hσ hρ).trans (by ext; simp)

/-- Up to continuous linear equivalences of its domain and codomain, `compSnakeMiddle T S` is
`(ContinuousLinearMap.id R F).prodMap (S ∘L T)`, allowing consumers to transport kernels,
cokernels, invertibility, and Fredholmness. -/
theorem exists_compSnakeMiddle_eq_comp_prodMap_comp [IsTopologicalAddGroup G] :
    ∃ (eCod : (F × G) ≃L[R] F × G) (eDom : (E × F) ≃L[R] F × E),
      compSnakeMiddle T S =
        (eCod : F × G →L[R] F × G) ∘L
          ((ContinuousLinearMap.id R F).prodMap (S ∘L T)) ∘L
            (eDom : E × F →L[R] F × E) := by
  let eCod : (F × G) ≃L[R] F × G :=
    (ContinuousLinearEquiv.refl R F).skewProd (ContinuousLinearEquiv.refl R G) (-S)
  let eDom : (E × F) ≃L[R] F × E :=
    ((ContinuousLinearEquiv.refl R E).skewProd (ContinuousLinearEquiv.neg R) T).trans
      (ContinuousLinearEquiv.prodComm R E F)
  refine ⟨eCod, eDom, ?_⟩
  apply ContinuousLinearMap.ext; rintro ⟨x, y⟩
  ext <;> simp [eCod, eDom, sub_eq_add_neg, add_comm]

/-- `compSnakeMiddle T S` has the same index as the composite `S ∘L T`, with no finiteness or
topological-group assumptions on `E` or `G`. -/
@[simp] theorem index_compSnakeMiddle : (compSnakeMiddle T S).index = (S ∘L T).index := by
  let eCod : (F × G) ≃ₗ[R] (F × G) :=
    (LinearEquiv.refl R F).skewProd (LinearEquiv.refl R G) S.toLinearMap
  let eDom : (F × E) ≃ₗ[R] (E × F) :=
    (LinearEquiv.prodComm R F E).trans
      ((LinearEquiv.refl R E).skewProd (LinearEquiv.neg R) T.toLinearMap)
  have hconj : eCod.toLinearMap ∘ₗ (compSnakeMiddle T S).toLinearMap ∘ₗ eDom.toLinearMap =
      LinearMap.id.prodMap (S ∘L T).toLinearMap := by
    apply LinearMap.ext; rintro ⟨v, x⟩; ext <;> simp [eCod, eDom, sub_eq_add_neg, add_comm]
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
    have : Subsingleton (F ⧸ (⊤ : Submodule R F)) := Submodule.Quotient.subsingleton_iff.mpr rfl
    let : Unique (F ⧸ (⊤ : Submodule R F)) := uniqueOfSubsingleton 0
    exact (Submodule.quotientProdEquiv _ _ ≪≫ₗ LinearEquiv.uniqueProd).finrank_eq
  rw [hker, hcoker]

end CompSnake

end ContinuousLinearMap
