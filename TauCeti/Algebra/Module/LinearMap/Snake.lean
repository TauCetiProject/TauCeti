/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Exact.Sequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.LinearMap.Index
public import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.LinearMap.Ker

/-!
# Snake sequence and index additivity for linear maps

A morphism between two exact three-term rows of modules
```text
      M₁ --f₁--> M₂ --f₂--> M₃ ⟶ 0
      |          |          |
     t₁         t₂         t₃
      v          v          v
0 ⟶ N₁ --g₁--> N₂ --g₂--> N₃
```
induces maps on kernels `ker t₁ → ker t₂ → ker t₃` (`TauCeti.kerMap`) and on cokernels
`coker t₁ → coker t₂ → coker t₃` (`TauCeti.cokerMap`), connected by a linear map
`TauCeti.snakeδ : ker t₃ →ₗ[R] N₁ ⧸ range t₁` into a six-term exact sequence.

When the six modules lie in a common universe, `TauCeti.moduleCatSnakeInput` packages the diagram
as a `CategoryTheory.ShortComplex.SnakeInput` in `ModuleCat R` with concrete kernel submodules and
range quotients as its outer rows, and `CategoryTheory.ShortComplex.SnakeInput.δ_apply` computes the
connecting morphism on elements. Conjugating along `ULift.moduleEquiv` extends `TauCeti.snakeδ` and
its exactness properties to modules in arbitrary independent universes.

When `f₂` admits a linear right inverse `σ` and `g₁` admits a linear left inverse `ρ`, the
connecting map equals `t₁.range.mkQ ∘ₗ ρ ∘ₗ t₂ ∘ₗ σ ∘ₗ t₃.ker.subtype`
(`TauCeti.snakeδ_eq_of_rightInverse_of_leftInverse`), showing in particular that this composite is
independent of the chosen splittings.

Over a division ring, exactness of the six-term sequence gives the two-out-of-three property for
finite-dimensional kernels and cokernels (`TauCeti.finiteDimensional_ker_middle` and its
companions) and additivity of `LinearMap.index` along short exact sequences
(`TauCeti.index_eq_add_of_shortExact`): `t₂.index = t₁.index + t₃.index`.

## References

* N. Bourbaki, *Algebra*, Chapter X (*Homological Algebra*), §1, Proposition 2.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §19.1,
  Theorem 19.1.2 and Corollary 19.1.7.
-/

public section

namespace TauCeti

section KerMap

variable {R M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [Semiring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
  [Module R M₁] [Module R M₂] [Module R M₃]
  [Module R N₁] [Module R N₂] [Module R N₃]

/-- A commuting square `g ∘ₗ t₁ = t₂ ∘ₗ f` restricts `f` to a linear map `ker t₁ →ₗ[R] ker t₂`. -/
def kerMap {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {f : M₁ →ₗ[R] M₂} {g : N₁ →ₗ[R] N₂}
    (h : g ∘ₗ t₁ = t₂ ∘ₗ f) : t₁.ker →ₗ[R] t₂.ker :=
  f.restrict fun _ ↦ LinearMap.map_mem_ker_of_comp_eq f h

@[simp]
theorem coe_kerMap_apply {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {f : M₁ →ₗ[R] M₂}
    {g : N₁ →ₗ[R] N₂} (h : g ∘ₗ t₁ = t₂ ∘ₗ f) (x : t₁.ker) :
    (kerMap h x : M₂) = f x :=
  (rfl)

@[simp]
theorem subtype_comp_kerMap {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {f : M₁ →ₗ[R] M₂}
    {g : N₁ →ₗ[R] N₂} (h : g ∘ₗ t₁ = t₂ ∘ₗ f) :
    t₂.ker.subtype ∘ₗ kerMap h = f ∘ₗ t₁.ker.subtype :=
  (rfl)

@[simp]
theorem kerMap_zero {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {g : N₁ →ₗ[R] N₂}
    (h : g ∘ₗ t₁ = t₂ ∘ₗ (0 : M₁ →ₗ[R] M₂)) :
    kerMap h = 0 := by
  ext
  simp

@[simp]
theorem kerMap_id {t : M₁ →ₗ[R] N₁} (h : LinearMap.id ∘ₗ t = t ∘ₗ LinearMap.id := rfl) :
    kerMap h = LinearMap.id := by
  ext
  rfl

theorem kerMap_comp {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {t₃ : M₃ →ₗ[R] N₃}
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂)
    (h₁₃ : (g₂ ∘ₗ g₁) ∘ₗ t₁ = t₃ ∘ₗ (f₂ ∘ₗ f₁) := by
      rw [LinearMap.comp_assoc, h₁₂, ← LinearMap.comp_assoc, h₂₃, LinearMap.comp_assoc]) :
    kerMap h₁₃ = kerMap h₂₃ ∘ₗ kerMap h₁₂ := by
  ext
  rfl

/-- If `f` is injective, then the induced map on kernels is injective. -/
theorem kerMap_injective {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {f : M₁ →ₗ[R] M₂}
    {g : N₁ →ₗ[R] N₂} (h : g ∘ₗ t₁ = t₂ ∘ₗ f) (hf : Function.Injective f) :
    Function.Injective (kerMap h) := fun _ _ hxy ↦
  Subtype.ext (hf (congrArg Subtype.val hxy))

/-- Left exactness on kernels: if `M₁ --f₁--> M₂ --f₂--> M₃` is exact and `g₁` is injective, then
`ker t₁ → ker t₂ → ker t₃` is exact. -/
theorem exact_kerMap {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {t₃ : M₃ →ₗ[R] N₃}
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (hf : Function.Exact f₁ f₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂) :
    Function.Exact (kerMap h₁₂) (kerMap h₂₃) := by
  rintro ⟨x₂, hx₂⟩
  refine ⟨fun hx ↦ ?_, ?_⟩
  · obtain ⟨x₁, rfl⟩ := (hf x₂).mp (congrArg Subtype.val hx)
    have hx₁ : x₁ ∈ t₁.ker := LinearMap.mem_ker.mpr <| hg₁ <| by
      rw [map_zero, ← LinearMap.comp_apply, h₁₂, LinearMap.comp_apply, LinearMap.mem_ker.mp hx₂]
    exact ⟨⟨x₁, hx₁⟩, rfl⟩
  · rintro ⟨⟨x₁, _⟩, h⟩
    have hx : f₁ x₁ = x₂ := congrArg Subtype.val h
    exact Subtype.ext (hx ▸ hf.apply_apply_eq_zero x₁)

end KerMap

section CokerMap

variable {R M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [Ring R]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
  [Module R M₁] [Module R M₂] [Module R M₃]
  [Module R N₁] [Module R N₂] [Module R N₃]

/-- A commuting square `g ∘ₗ t₁ = t₂ ∘ₗ f` descends `g` to a linear map
`(N₁ ⧸ range t₁) →ₗ[R] (N₂ ⧸ range t₂)` on cokernels. -/
def cokerMap {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {f : M₁ →ₗ[R] M₂} {g : N₁ →ₗ[R] N₂}
    (h : g ∘ₗ t₁ = t₂ ∘ₗ f) : (N₁ ⧸ t₁.range) →ₗ[R] (N₂ ⧸ t₂.range) :=
  t₁.range.mapQ t₂.range g <| by
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, by simpa only [LinearMap.comp_apply] using (LinearMap.congr_fun h x).symm⟩

@[simp]
theorem cokerMap_mk {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {f : M₁ →ₗ[R] M₂}
    {g : N₁ →ₗ[R] N₂} (h : g ∘ₗ t₁ = t₂ ∘ₗ f) (y : N₁) :
    cokerMap h (Submodule.Quotient.mk y) = Submodule.Quotient.mk (g y) :=
  (rfl)

@[simp]
theorem cokerMap_comp_mkQ {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {f : M₁ →ₗ[R] M₂}
    {g : N₁ →ₗ[R] N₂} (h : g ∘ₗ t₁ = t₂ ∘ₗ f) :
    cokerMap h ∘ₗ t₁.range.mkQ = t₂.range.mkQ ∘ₗ g :=
  (rfl)

@[simp]
theorem cokerMap_zero {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {f : M₁ →ₗ[R] M₂}
    (h : (0 : N₁ →ₗ[R] N₂) ∘ₗ t₁ = t₂ ∘ₗ f) :
    cokerMap h = 0 := by
  ext
  simp

@[simp]
theorem cokerMap_id {t : M₁ →ₗ[R] N₁} (h : LinearMap.id ∘ₗ t = t ∘ₗ LinearMap.id := rfl) :
    cokerMap h = LinearMap.id := by
  ext
  rfl

theorem cokerMap_comp {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {t₃ : M₃ →ₗ[R] N₃}
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂)
    (h₁₃ : (g₂ ∘ₗ g₁) ∘ₗ t₁ = t₃ ∘ₗ (f₂ ∘ₗ f₁) := by
      rw [LinearMap.comp_assoc, h₁₂, ← LinearMap.comp_assoc, h₂₃, LinearMap.comp_assoc]) :
    cokerMap h₁₃ = cokerMap h₂₃ ∘ₗ cokerMap h₁₂ := by
  ext
  rfl

/-- If `g` is surjective, then the induced map on cokernels is surjective. -/
theorem cokerMap_surjective {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {f : M₁ →ₗ[R] M₂}
    {g : N₁ →ₗ[R] N₂} (h : g ∘ₗ t₁ = t₂ ∘ₗ f) (hg : Function.Surjective g) :
    Function.Surjective (cokerMap h) := by
  intro q
  obtain ⟨y₂, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  obtain ⟨y₁, rfl⟩ := hg y₂
  exact ⟨Submodule.Quotient.mk y₁, rfl⟩

/-- Right exactness on cokernels: if `f₂` is surjective and `N₁ --g₁--> N₂ --g₂--> N₃` is exact,
then `coker t₁ → coker t₂ → coker t₃` is exact. -/
theorem exact_cokerMap {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {t₃ : M₃ →ₗ[R] N₃}
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (hf₂ : Function.Surjective f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂) :
    Function.Exact (cokerMap h₁₂) (cokerMap h₂₃) := by
  refine (hg.exact_mapQ_iff _ _).2 ?_
  rw [← LinearMap.range_comp, h₂₃,
    LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.2 hf₂)]
  exact inf_le_right

end CokerMap

section ModuleCat

open CategoryTheory CategoryTheory.Limits

universe u v

variable {R : Type u} [Ring R]
  {M₁ M₂ M₃ N₁ N₂ N₃ : Type v}
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
  [Module R M₁] [Module R M₂] [Module R M₃]
  [Module R N₁] [Module R N₂] [Module R N₃]

/-- Concrete `CategoryTheory.ShortComplex.SnakeInput` in `ModuleCat.{v} R` attached to a commuting
diagram with exact rows `M₁ --f₁--> M₂ --f₂--> M₃ → 0` and `0 → N₁ --g₁--> N₂ --g₂--> N₃`, using
the submodule kernels `tᵢ.ker` as `L₀` and the quotient cokernels `Nᵢ ⧸ tᵢ.range` as `L₃`. -/
@[expose]
noncomputable def moduleCatSnakeInput {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {t₃ : M₃ →ₗ[R] N₃}
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂) :
    ShortComplex.SnakeInput (ModuleCat.{v} R) where
  L₀ := ModuleCat.shortComplexOfCompEqZero (kerMap h₁₂) (kerMap h₂₃)
    (by ext x; simp [hf.apply_apply_eq_zero])
  L₁ := ModuleCat.shortComplexOfCompEqZero f₁ f₂ hf.linearMap_comp_eq_zero
  L₂ := ModuleCat.shortComplexOfCompEqZero g₁ g₂ hg.linearMap_comp_eq_zero
  L₃ := ModuleCat.shortComplexOfCompEqZero (cokerMap h₁₂) (cokerMap h₂₃)
    (by ext y; simp [hg.apply_apply_eq_zero])
  v₀₁ :=
    { τ₁ := ModuleCat.ofHom t₁.ker.subtype
      τ₂ := ModuleCat.ofHom t₂.ker.subtype
      τ₃ := ModuleCat.ofHom t₃.ker.subtype }
  v₁₂ :=
    { τ₁ := ModuleCat.ofHom t₁
      τ₂ := ModuleCat.ofHom t₂
      τ₃ := ModuleCat.ofHom t₃
      comm₁₂ := ModuleCat.hom_ext h₁₂
      comm₂₃ := ModuleCat.hom_ext h₂₃ }
  v₂₃ :=
    { τ₁ := ModuleCat.ofHom t₁.range.mkQ
      τ₂ := ModuleCat.ofHom t₂.range.mkQ
      τ₃ := ModuleCat.ofHom t₃.range.mkQ }
  w₀₂ := by ext x <;> exact x.2
  w₁₃ := by ext x <;> simp
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ <;>
      apply (KernelFork.isLimitMapConeEquiv _ _).2
    · exact ModuleCat.kernelIsLimit (ModuleCat.ofHom t₁)
    · exact ModuleCat.kernelIsLimit (ModuleCat.ofHom t₂)
    · exact ModuleCat.kernelIsLimit (ModuleCat.ofHom t₃)
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ <;>
      apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2
    · exact ModuleCat.cokernelIsColimit (ModuleCat.ofHom t₁)
    · exact ModuleCat.cokernelIsColimit (ModuleCat.ofHom t₂)
    · exact ModuleCat.cokernelIsColimit (ModuleCat.ofHom t₃)
  L₁_exact := ModuleCat.shortComplex_exact _ hf
  epi_L₁_g := (ModuleCat.epi_iff_surjective _).mpr hf₂
  L₂_exact := ModuleCat.shortComplex_exact _ hg
  mono_L₂_f := (ModuleCat.mono_iff_injective _).mpr hg₁

/-- Element-level formula for `(moduleCatSnakeInput ...).δ`: if `f₂ x₂ = x₃` and `g₁ y₁ = t₂ x₂`,
then `δ x₃` is the class of `y₁` modulo `range t₁`. -/
theorem moduleCatSnakeInput_δ_apply {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {t₃ : M₃ →ₗ[R] N₃}
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂)
    (x₃ : t₃.ker) (x₂ : M₂) (y₁ : N₁) (hx₂ : f₂ x₂ = x₃) (hy₁ : g₁ y₁ = t₂ x₂) :
    (moduleCatSnakeInput hf hf₂ hg hg₁ h₁₂ h₂₃).δ.hom x₃ = Submodule.Quotient.mk y₁ :=
  (moduleCatSnakeInput hf hf₂ hg hg₁ h₁₂ h₂₃).δ_apply x₃ x₂ y₁ hx₂ hy₁

end ModuleCat

section Snake

private abbrev uliftConj.{w, uR, uA, uB} {R : Type uR} [Ring R] {A : Type uA} {B : Type uB}
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B] (f : A →ₗ[R] B) :
    ULift.{w} A →ₗ[R] ULift.{w} B :=
  ULift.moduleEquiv.symm.toLinearMap ∘ₗ f ∘ₗ ULift.moduleEquiv.toLinearMap

private theorem uliftConj_comp_eq.{w, uR, uA, uB, uC, uD} {R : Type uR} [Ring R]
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D]
    [Module R A] [Module R B] [Module R C] [Module R D]
    {f : A →ₗ[R] B} {g : C →ₗ[R] D} {t₁ : A →ₗ[R] C} {t₂ : B →ₗ[R] D}
    (h : g ∘ₗ t₁ = t₂ ∘ₗ f) :
    uliftConj.{w} g ∘ₗ uliftConj.{w} t₁ = uliftConj.{w} t₂ ∘ₗ uliftConj.{w} f := by
  ext ⟨x⟩
  exact LinearMap.congr_fun h x

private def uliftKerEquiv.{w, uR, uA, uB} {R : Type uR} [Ring R] {A : Type uA} {B : Type uB}
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B] (t : A →ₗ[R] B) :
    t.ker ≃ₗ[R] (uliftConj.{w} t).ker :=
  ULift.moduleEquiv.symm.submoduleMap t.ker ≪≫ₗ
    LinearEquiv.ofEq _ _ (by ext ⟨x⟩; simp [uliftConj])

@[simp]
private theorem coe_uliftKerEquiv_apply.{w, uR, uA, uB} {R : Type uR} [Ring R]
    {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (t : A →ₗ[R] B) (x : t.ker) :
    (uliftKerEquiv.{w} t x : ULift.{w} A) = ULift.up (x : A) :=
  rfl

@[simp]
private theorem coe_uliftKerEquiv_symm_apply.{w, uR, uA, uB} {R : Type uR} [Ring R]
    {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (t : A →ₗ[R] B) (x : (uliftConj.{w} t).ker) :
    ((uliftKerEquiv.{w} t).symm x : A) = (x : ULift.{w} A).down :=
  rfl

private def uliftCokerEquiv.{w, uR, uA, uB} {R : Type uR} [Ring R] {A : Type uA} {B : Type uB}
    [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B] (t : A →ₗ[R] B) :
    (ULift.{w} B ⧸ (uliftConj.{w} t).range) ≃ₗ[R] B ⧸ t.range :=
  Submodule.Quotient.equiv _ _ ULift.moduleEquiv (by ext y; simp [uliftConj])

@[simp]
private theorem uliftCokerEquiv_mk.{w, uR, uA, uB} {R : Type uR} [Ring R]
    {A : Type uA} {B : Type uB} [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (t : A →ₗ[R] B) (y : ULift.{w} B) :
    uliftCokerEquiv.{w} t (Submodule.Quotient.mk y) = Submodule.Quotient.mk y.down :=
  rfl

universe u u₁ u₂ u₃ v₁ v₂ v₃

variable {R : Type u} [Ring R]
  {M₁ : Type u₁} {M₂ : Type u₂} {M₃ : Type u₃}
  {N₁ : Type v₁} {N₂ : Type v₂} {N₃ : Type v₃}
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
  [Module R M₁] [Module R M₂] [Module R M₃]
  [Module R N₁] [Module R N₂] [Module R N₃]

private noncomputable def uliftSnakeInput
    {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {t₃ : M₃ →ₗ[R] N₃}
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂) :
    CategoryTheory.ShortComplex.SnakeInput (ModuleCat.{max u₁ u₂ u₃ v₁ v₂ v₃} R) :=
  moduleCatSnakeInput
    (by simpa only [uliftConj, LinearEquiv.postcomp_exact_iff_exact,
      LinearEquiv.conj_symm_exact_iff_exact, LinearEquiv.precomp_exact_iff_exact] using hf)
    (by simpa [uliftConj] using hf₂)
    (by simpa only [uliftConj, LinearEquiv.postcomp_exact_iff_exact,
      LinearEquiv.conj_symm_exact_iff_exact, LinearEquiv.precomp_exact_iff_exact] using hg)
    (by simpa [uliftConj] using hg₁)
    (uliftConj_comp_eq.{max u₁ u₂ u₃ v₁ v₂ v₃} h₁₂)
    (uliftConj_comp_eq.{max u₁ u₂ u₃ v₁ v₂ v₃} h₂₃)

private noncomputable def uliftSnakeδ
    {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {t₃ : M₃ →ₗ[R] N₃}
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂) :
    (uliftConj.{max u₁ u₂ u₃ v₁ v₂ v₃} t₃).ker →ₗ[R]
      ULift.{max u₁ u₂ u₃ v₁ v₂ v₃} N₁ ⧸ (uliftConj.{max u₁ u₂ u₃ v₁ v₂ v₃} t₁).range :=
  (uliftSnakeInput hf hf₂ hg hg₁ h₁₂ h₂₃).δ.hom

/-- The **snake connecting linear map** `ker t₃ →ₗ[R] N₁ ⧸ range t₁` associated to a commuting
diagram with exact rows `M₁ --f₁--> M₂ --f₂--> M₃ → 0` and `0 → N₁ --g₁--> N₂ --g₂--> N₃`,
defined via `CategoryTheory.ShortComplex.SnakeInput` in `ModuleCat R` after lifting the six
modules to a common universe. -/
noncomputable def snakeδ {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {t₃ : M₃ →ₗ[R] N₃}
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂) :
    t₃.ker →ₗ[R] N₁ ⧸ t₁.range :=
  (uliftCokerEquiv.{max u₁ u₂ u₃ v₁ v₂ v₃} t₁).toLinearMap ∘ₗ
    uliftSnakeδ hf hf₂ hg hg₁ h₁₂ h₂₃ ∘ₗ
    (uliftKerEquiv.{max u₁ u₂ u₃ v₁ v₂ v₃} t₃).toLinearMap

/-- Diagram-chase formula for `TauCeti.snakeδ`: if `f₂ x₂ = x₃` and `g₁ y₁ = t₂ x₂`, then
`snakeδ` sends `x₃` to the class of `y₁` in `N₁ ⧸ range t₁`. -/
theorem snakeδ_eq {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {t₃ : M₃ →ₗ[R] N₃}
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂)
    (x₃ : t₃.ker) (x₂ : M₂) (y₁ : N₁) (hx₂ : f₂ x₂ = x₃) (hy₁ : g₁ y₁ = t₂ x₂) :
    snakeδ hf hf₂ hg hg₁ h₁₂ h₂₃ x₃ = Submodule.Quotient.mk y₁ := by
  have hδ : uliftSnakeδ hf hf₂ hg hg₁ h₁₂ h₂₃
      (uliftKerEquiv.{max u₁ u₂ u₃ v₁ v₂ v₃} t₃ x₃) =
      Submodule.Quotient.mk (ULift.up y₁) :=
    moduleCatSnakeInput_δ_apply _ _ _ _ _ _
      (uliftKerEquiv.{max u₁ u₂ u₃ v₁ v₂ v₃} t₃ x₃)
      (ULift.up x₂) (ULift.up y₁)
      (congrArg ULift.up hx₂)
      (congrArg ULift.up hy₁)
  simp [snakeδ, hδ]

/-- When all six modules lie in a single universe `u₁`, `TauCeti.snakeδ` agrees with the underlying
linear map of `(TauCeti.moduleCatSnakeInput ...).δ`. -/
@[simp]
theorem moduleCatSnakeInput_δ_hom {A₁ A₂ A₃ B₁ B₂ B₃ : Type u₁}
    [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]
    [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃]
    [Module R A₁] [Module R A₂] [Module R A₃]
    [Module R B₁] [Module R B₂] [Module R B₃]
    {t₁ : A₁ →ₗ[R] B₁} {t₂ : A₂ →ₗ[R] B₂} {t₃ : A₃ →ₗ[R] B₃}
    {f₁ : A₁ →ₗ[R] A₂} {f₂ : A₂ →ₗ[R] A₃} {g₁ : B₁ →ₗ[R] B₂} {g₂ : B₂ →ₗ[R] B₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂) :
    (moduleCatSnakeInput hf hf₂ hg hg₁ h₁₂ h₂₃).δ.hom = snakeδ hf hf₂ hg hg₁ h₁₂ h₂₃ := by
  ext (x₃ : t₃.ker)
  obtain ⟨x₂, hx₂⟩ := hf₂ x₃
  have hker : g₂ (t₂ x₂) = 0 := by
    rw [← LinearMap.comp_apply, h₂₃, LinearMap.comp_apply, hx₂, LinearMap.mem_ker.mp x₃.2]
  obtain ⟨y₁, hy₁⟩ := (hg (t₂ x₂)).mp hker
  exact (moduleCatSnakeInput_δ_apply hf hf₂ hg hg₁ h₁₂ h₂₃ x₃ x₂ y₁ hx₂ hy₁).trans
    (snakeδ_eq hf hf₂ hg hg₁ h₁₂ h₂₃ x₃ x₂ y₁ hx₂ hy₁).symm

/-- **Split formula for the connecting map**: if `σ` is a linear right inverse of `f₂` and `ρ` is a
linear left inverse of `g₁`, then `TauCeti.snakeδ` equals
`t₁.range.mkQ ∘ₗ ρ ∘ₗ t₂ ∘ₗ σ ∘ₗ t₃.ker.subtype`. In particular, that composite does not depend on
the chosen splittings `σ` and `ρ`. -/
theorem snakeδ_eq_of_rightInverse_of_leftInverse {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂}
    {t₃ : M₃ →ₗ[R] N₃} {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂}
    {g₂ : N₂ →ₗ[R] N₃} (hf : Function.Exact f₁ f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂)
    {σ : M₃ →ₗ[R] M₂} (hσ : Function.RightInverse σ f₂)
    {ρ : N₂ →ₗ[R] N₁} (hρ : Function.LeftInverse ρ g₁) :
    snakeδ hf hσ.surjective hg hρ.injective h₁₂ h₂₃ =
      t₁.range.mkQ ∘ₗ ρ ∘ₗ t₂ ∘ₗ σ ∘ₗ t₃.ker.subtype := by
  ext x₃
  have hker : g₂ (t₂ (σ x₃)) = 0 := by
    rw [← LinearMap.comp_apply, h₂₃, LinearMap.comp_apply, hσ x₃, LinearMap.mem_ker.mp x₃.2]
  obtain ⟨y₁, hy₁⟩ := (hg (t₂ (σ x₃))).mp hker
  have hρy : ρ (t₂ (σ x₃)) = y₁ := by rw [← hy₁, hρ y₁]
  simpa [hρy] using snakeδ_eq hf hσ.surjective hg hρ.injective h₁₂ h₂₃ x₃ (σ x₃) y₁ (hσ x₃) hy₁

/-- Exactness of the snake sequence at `ker t₃`:
`ker t₂ --kerMap h₂₃--> ker t₃ --snakeδ--> N₁ ⧸ range t₁` is exact. -/
theorem exact_kerMap_snakeδ {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {t₃ : M₃ →ₗ[R] N₃}
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂) :
    Function.Exact (kerMap h₂₃) (snakeδ hf hf₂ hg hg₁ h₁₂ h₂₃) := by
  have hex : Function.Exact (kerMap (uliftConj_comp_eq.{max u₁ u₂ u₃ v₁ v₂ v₃} h₂₃))
      (uliftSnakeδ hf hf₂ hg hg₁ h₁₂ h₂₃) :=
    (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (uliftSnakeInput hf hf₂ hg hg₁ h₁₂ h₂₃).L₁'_exact
  refine hex.of_ladder_linearEquiv_of_exact
    (e₁ := (uliftKerEquiv.{max u₁ u₂ u₃ v₁ v₂ v₃} t₂).symm)
    (e₂ := (uliftKerEquiv.{max u₁ u₂ u₃ v₁ v₂ v₃} t₃).symm)
    (e₃ := uliftCokerEquiv.{max u₁ u₂ u₃ v₁ v₂ v₃} t₁) ?_ ?_
  · ext x
    simp [uliftConj]
  · ext x
    simp [snakeδ]

/-- Exactness of the snake sequence at `N₁ ⧸ range t₁`:
`ker t₃ --snakeδ--> N₁ ⧸ range t₁ --cokerMap h₁₂--> N₂ ⧸ range t₂` is exact. -/
theorem exact_snakeδ_cokerMap {t₁ : M₁ →ₗ[R] N₁} {t₂ : M₂ →ₗ[R] N₂} {t₃ : M₃ →ₗ[R] N₃}
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂) :
    Function.Exact (snakeδ hf hf₂ hg hg₁ h₁₂ h₂₃) (cokerMap h₁₂) := by
  have hex : Function.Exact (uliftSnakeδ hf hf₂ hg hg₁ h₁₂ h₂₃)
      (cokerMap (uliftConj_comp_eq.{max u₁ u₂ u₃ v₁ v₂ v₃} h₁₂)) :=
    (CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
      (uliftSnakeInput hf hf₂ hg hg₁ h₁₂ h₂₃).L₂'_exact
  refine hex.of_ladder_linearEquiv_of_exact
    (e₁ := (uliftKerEquiv.{max u₁ u₂ u₃ v₁ v₂ v₃} t₃).symm)
    (e₂ := uliftCokerEquiv.{max u₁ u₂ u₃ v₁ v₂ v₃} t₁)
    (e₃ := uliftCokerEquiv.{max u₁ u₂ u₃ v₁ v₂ v₃} t₂) ?_ ?_
  · ext x
    simp [snakeδ]
  · ext y
    simp [uliftConj]

end Snake

section DivisionRing

variable {𝕜 M₁ M₂ M₃ N₁ N₂ N₃ : Type*} [DivisionRing 𝕜]
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
  [Module 𝕜 M₁] [Module 𝕜 M₂] [Module 𝕜 M₃]
  [Module 𝕜 N₁] [Module 𝕜 N₂] [Module 𝕜 N₃]

/-- If `f₁` is injective in `g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁` and `ker t₂` is finite-dimensional, then
`ker t₁` is finite-dimensional. -/
theorem finiteDimensional_ker_left {t₁ : M₁ →ₗ[𝕜] N₁} {t₂ : M₂ →ₗ[𝕜] N₂}
    {f₁ : M₁ →ₗ[𝕜] M₂} {g₁ : N₁ →ₗ[𝕜] N₂}
    (hf₁ : Function.Injective f₁) (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁)
    [FiniteDimensional 𝕜 t₂.ker] :
    FiniteDimensional 𝕜 t₁.ker :=
  Module.Finite.of_injective (kerMap h₁₂) (kerMap_injective h₁₂ hf₁)

/-- If `M₁ --f₁--> M₂ --f₂--> M₃` is exact, `g₁` is injective, and both `ker t₁` and `ker t₃` are
finite-dimensional, then `ker t₂` is finite-dimensional. -/
theorem finiteDimensional_ker_middle {t₁ : M₁ →ₗ[𝕜] N₁} {t₂ : M₂ →ₗ[𝕜] N₂} {t₃ : M₃ →ₗ[𝕜] N₃}
    {f₁ : M₁ →ₗ[𝕜] M₂} {f₂ : M₂ →ₗ[𝕜] M₃} {g₁ : N₁ →ₗ[𝕜] N₂} {g₂ : N₂ →ₗ[𝕜] N₃}
    (hf : Function.Exact f₁ f₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂)
    [FiniteDimensional 𝕜 t₁.ker] [FiniteDimensional 𝕜 t₃.ker] :
    FiniteDimensional 𝕜 t₂.ker :=
  finiteDimensional_of_exact (exact_kerMap hf hg₁ h₁₂ h₂₃)

/-- If `ker t₂` and `coker t₁` are finite-dimensional in a snake diagram, then `ker t₃` is
finite-dimensional. -/
theorem finiteDimensional_ker_right {t₁ : M₁ →ₗ[𝕜] N₁} {t₂ : M₂ →ₗ[𝕜] N₂} {t₃ : M₃ →ₗ[𝕜] N₃}
    {f₁ : M₁ →ₗ[𝕜] M₂} {f₂ : M₂ →ₗ[𝕜] M₃} {g₁ : N₁ →ₗ[𝕜] N₂} {g₂ : N₂ →ₗ[𝕜] N₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂)
    [FiniteDimensional 𝕜 t₂.ker] [FiniteDimensional 𝕜 (N₁ ⧸ t₁.range)] :
    FiniteDimensional 𝕜 t₃.ker :=
  finiteDimensional_of_exact (exact_kerMap_snakeδ hf hf₂ hg hg₁ h₁₂ h₂₃)

/-- If `ker t₃` and `coker t₂` are finite-dimensional in a snake diagram, then `coker t₁` is
finite-dimensional. -/
theorem finiteDimensional_coker_left {t₁ : M₁ →ₗ[𝕜] N₁} {t₂ : M₂ →ₗ[𝕜] N₂} {t₃ : M₃ →ₗ[𝕜] N₃}
    {f₁ : M₁ →ₗ[𝕜] M₂} {f₂ : M₂ →ₗ[𝕜] M₃} {g₁ : N₁ →ₗ[𝕜] N₂} {g₂ : N₂ →ₗ[𝕜] N₃}
    (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg : Function.Exact g₁ g₂) (hg₁ : Function.Injective g₁)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂)
    [FiniteDimensional 𝕜 t₃.ker] [FiniteDimensional 𝕜 (N₂ ⧸ t₂.range)] :
    FiniteDimensional 𝕜 (N₁ ⧸ t₁.range) :=
  finiteDimensional_of_exact (exact_snakeδ_cokerMap hf hf₂ hg hg₁ h₁₂ h₂₃)

/-- If `f₂` is surjective, `N₁ --g₁--> N₂ --g₂--> N₃` is exact, and both `coker t₁` and `coker t₃`
are finite-dimensional, then `coker t₂` is finite-dimensional. -/
theorem finiteDimensional_coker_middle {t₁ : M₁ →ₗ[𝕜] N₁} {t₂ : M₂ →ₗ[𝕜] N₂} {t₃ : M₃ →ₗ[𝕜] N₃}
    {f₁ : M₁ →ₗ[𝕜] M₂} {f₂ : M₂ →ₗ[𝕜] M₃} {g₁ : N₁ →ₗ[𝕜] N₂} {g₂ : N₂ →ₗ[𝕜] N₃}
    (hf₂ : Function.Surjective f₂) (hg : Function.Exact g₁ g₂)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂)
    [FiniteDimensional 𝕜 (N₁ ⧸ t₁.range)] [FiniteDimensional 𝕜 (N₃ ⧸ t₃.range)] :
    FiniteDimensional 𝕜 (N₂ ⧸ t₂.range) :=
  finiteDimensional_of_exact (exact_cokerMap hf₂ hg h₁₂ h₂₃)

/-- If `g₂` is surjective in `g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂` and `coker t₂` is finite-dimensional, then
`coker t₃` is finite-dimensional. -/
theorem finiteDimensional_coker_right {t₂ : M₂ →ₗ[𝕜] N₂} {t₃ : M₃ →ₗ[𝕜] N₃}
    {f₂ : M₂ →ₗ[𝕜] M₃} {g₂ : N₂ →ₗ[𝕜] N₃}
    (hg₂ : Function.Surjective g₂) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂)
    [FiniteDimensional 𝕜 (N₂ ⧸ t₂.range)] :
    FiniteDimensional 𝕜 (N₃ ⧸ t₃.range) :=
  Module.Finite.of_surjective (cokerMap h₂₃) (cokerMap_surjective h₂₃ hg₂)

/-- **Index additivity along a morphism of short exact sequences.** Given a commuting diagram of
vector spaces over a division ring with short exact rows
`0 → M₁ --f₁--> M₂ --f₂--> M₃ → 0` and `0 → N₁ --g₁--> N₂ --g₂--> N₃ → 0`, if the outer maps `t₁`
and `t₃` have finite-dimensional kernels and cokernels, then `t₂.index = t₁.index + t₃.index`.
Finite-dimensionality of `ker t₂` and `coker t₂` follows from the snake sequence. -/
theorem index_eq_add_of_shortExact {t₁ : M₁ →ₗ[𝕜] N₁} {t₂ : M₂ →ₗ[𝕜] N₂} {t₃ : M₃ →ₗ[𝕜] N₃}
    {f₁ : M₁ →ₗ[𝕜] M₂} {f₂ : M₂ →ₗ[𝕜] M₃} {g₁ : N₁ →ₗ[𝕜] N₂} {g₂ : N₂ →ₗ[𝕜] N₃}
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂)
    [FiniteDimensional 𝕜 t₁.ker] [FiniteDimensional 𝕜 t₃.ker]
    [FiniteDimensional 𝕜 (N₁ ⧸ t₁.range)] [FiniteDimensional 𝕜 (N₃ ⧸ t₃.range)] :
    t₂.index = t₁.index + t₃.index := by
  have : FiniteDimensional 𝕜 t₂.ker := finiteDimensional_ker_middle hf hg₁ h₁₂ h₂₃
  have : FiniteDimensional 𝕜 (N₂ ⧸ t₂.range) := finiteDimensional_coker_middle hf₂ hg h₁₂ h₂₃
  have hsum := Module.sum_neg_one_pow_finrank_eq_zero_of_exact_six
    (kerMap h₁₂) (kerMap h₂₃)
    (snakeδ hf hf₂ hg hg₁ h₁₂ h₂₃)
    (cokerMap h₁₂) (cokerMap h₂₃)
    (kerMap_injective h₁₂ hf₁)
    (exact_kerMap hf hg₁ h₁₂ h₂₃)
    (exact_kerMap_snakeδ hf hf₂ hg hg₁ h₁₂ h₂₃)
    (exact_snakeδ_cokerMap hf hf₂ hg hg₁ h₁₂ h₂₃)
    (exact_cokerMap hf₂ hg h₁₂ h₂₃)
    (cokerMap_surjective h₂₃ hg₂)
  simp only [LinearMap.index_eq_finrank_sub]
  omega

/-- Index additivity along short exact sequences when the left and middle vertical maps have
finite-dimensional kernels and cokernels. -/
theorem index_eq_add_of_shortExact_of_left_middle {t₁ : M₁ →ₗ[𝕜] N₁} {t₂ : M₂ →ₗ[𝕜] N₂}
    {t₃ : M₃ →ₗ[𝕜] N₃} {f₁ : M₁ →ₗ[𝕜] M₂} {f₂ : M₂ →ₗ[𝕜] M₃} {g₁ : N₁ →ₗ[𝕜] N₂}
    {g₂ : N₂ →ₗ[𝕜] N₃}
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂)
    [FiniteDimensional 𝕜 t₁.ker] [FiniteDimensional 𝕜 t₂.ker]
    [FiniteDimensional 𝕜 (N₁ ⧸ t₁.range)] [FiniteDimensional 𝕜 (N₂ ⧸ t₂.range)] :
    t₂.index = t₁.index + t₃.index := by
  have : FiniteDimensional 𝕜 t₃.ker := finiteDimensional_ker_right hf hf₂ hg hg₁ h₁₂ h₂₃
  have : FiniteDimensional 𝕜 (N₃ ⧸ t₃.range) := finiteDimensional_coker_right hg₂ h₂₃
  exact index_eq_add_of_shortExact hf₁ hf hf₂ hg₁ hg hg₂ h₁₂ h₂₃

/-- Index additivity along short exact sequences when the middle and right vertical maps have
finite-dimensional kernels and cokernels. -/
theorem index_eq_add_of_shortExact_of_middle_right {t₁ : M₁ →ₗ[𝕜] N₁} {t₂ : M₂ →ₗ[𝕜] N₂}
    {t₃ : M₃ →ₗ[𝕜] N₃} {f₁ : M₁ →ₗ[𝕜] M₂} {f₂ : M₂ →ₗ[𝕜] M₃} {g₁ : N₁ →ₗ[𝕜] N₂}
    {g₂ : N₂ →ₗ[𝕜] N₃}
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁₂ : g₁ ∘ₗ t₁ = t₂ ∘ₗ f₁) (h₂₃ : g₂ ∘ₗ t₂ = t₃ ∘ₗ f₂)
    [FiniteDimensional 𝕜 t₂.ker] [FiniteDimensional 𝕜 t₃.ker]
    [FiniteDimensional 𝕜 (N₂ ⧸ t₂.range)] [FiniteDimensional 𝕜 (N₃ ⧸ t₃.range)] :
    t₂.index = t₁.index + t₃.index := by
  have : FiniteDimensional 𝕜 t₁.ker := finiteDimensional_ker_left hf₁ h₁₂
  have : FiniteDimensional 𝕜 (N₁ ⧸ t₁.range) := finiteDimensional_coker_left hf hf₂ hg hg₁ h₁₂ h₂₃
  exact index_eq_add_of_shortExact hf₁ hf hf₂ hg₁ hg hg₂ h₁₂ h₂₃

end DivisionRing

end TauCeti
