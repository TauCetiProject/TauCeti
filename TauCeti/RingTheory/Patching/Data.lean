/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Tower
public import TauCeti.RingTheory.Patching.ExactSquare

/-!
# Patching data over a square of rings

Let `R → R₁, R₂ → L` be a commuting square of commutative rings. A *patching datum* over it
consists of an `R₁`-module `M₁`, an `R₂`-module `M₂` and an `L`-linear identification
`α : L ⊗[R₁] M₁ ≃ L ⊗[R₂] M₂` of their scalar extensions to the overlap. Its module of
*sections* is the equalizer `{(x₁, x₂) | α (1 ⊗ x₁) = 1 ⊗ x₂}`, an `R`-module.
Every `R`-module `N` gives the canonical datum `Can N = (R₁ ⊗[R] N, R₂ ⊗[R] N, can)`.

The sections are right adjoint to `Can`: `R`-linear maps `N → sections D` correspond to
morphisms of patching data `Can N ⟶ D`. When the square is exact (`TauCeti.ExactSquare`) and
`N` is flat, or the overlap `L` is flat, the unit `N → sections (Can N)` is an isomorphism, so
`Can` is fully faithful on flat modules, and on all modules when `L` is flat. These are the
formal foundations of patching finite projective modules over an exact square (Kedlaya–Liu,
Lemmas 1.3.8–1.3.9) and of Beauville–Laszlo gluing. No cocycle over `R₁ ⊗[R] R₁` is part of the
datum: the square replaces a descent datum.

This is the two-module presentation of a glueing datum `(M₁, M₂, M₁₂, ψ₁, ψ₂)`, with
`α = ψ₂⁻¹ ψ₁`; it has the same sections and morphisms.

## Main definitions

* `TauCeti.PatchingData R R₁ R₂ L`: patching data over the square, forming a category.
* `TauCeti.PatchingData.sections D`: the `R`-module of sections of a datum.
* `TauCeti.PatchingData.compareLeft`, `TauCeti.PatchingData.compareRight`: the comparison maps
  `R₁ ⊗[R] sections D → M₁` and `R₂ ⊗[R] sections D → M₂`.
* `TauCeti.PatchingData.can N`: the canonical datum of an `R`-module.
* `TauCeti.PatchingData.sectionsFunctor`, `TauCeti.PatchingData.canFunctor` and the adjunction
  `TauCeti.PatchingData.canAdjunction : canFunctor ⊣ sectionsFunctor`.

## Main results

* `TauCeti.PatchingData.mem_sections_can_iff`: the sections of `Can N` are the kernel of the
  difference map `(R₁ ⊗[R] N) × (R₂ ⊗[R] N) → L ⊗[R] N`.
* `TauCeti.ExactSquare.bijective_canUnit`: over an exact square, a module whose patching
  diagonal is injective (for instance a flat module, or any module when the overlap is flat) is
  recovered as the sections of its canonical datum.
* `TauCeti.ExactSquare.canHomEquiv`: over an exact square, morphisms of canonical data
  `Can M ⟶ Can N` are exactly the `R`-linear maps `M → N` when the patching diagonal of `N` is
  injective.

## References

* K. S. Kedlaya, R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Definition 1.3.7 and Lemmas 1.3.8–1.3.9 ([arXiv:1301.0792](https://arxiv.org/abs/1301.0792)).
* [The Stacks Project, Section 15.92](https://stacks.math.columbia.edu/tag/0BNI), the category
  of glueing data before Theorem 15.92.16.
-/

public section

universe u

open CategoryTheory TensorProduct

namespace TauCeti

variable (R R₁ R₂ L : Type u) [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing L]
  [Algebra R R₁] [Algebra R R₂] [Algebra R₁ L] [Algebra R₂ L]

/-- A patching datum over the square `R → R₁, R₂ → L`: an `R₁`-module `left`, an `R₂`-module
`right` and an `L`-linear identification of their scalar extensions to `L`. The restricted
`R`-module structures are part of the bundle, compatible with the algebra maps. -/
structure PatchingData where
  /-- The module over the first corner `R₁`. -/
  left : Type u
  /-- The module over the second corner `R₂`. -/
  right : Type u
  /-- The additive group structure of `left`. -/
  [addCommGroupLeft : AddCommGroup left]
  /-- The additive group structure of `right`. -/
  [addCommGroupRight : AddCommGroup right]
  /-- The `R₁`-module structure of `left`. -/
  [moduleLeft : Module R₁ left]
  /-- The `R₂`-module structure of `right`. -/
  [moduleRight : Module R₂ right]
  /-- The restricted `R`-module structure of `left`. -/
  [moduleBaseLeft : Module R left]
  /-- The restricted `R`-module structure of `right`. -/
  [moduleBaseRight : Module R right]
  /-- The `R`-action on `left` factors through `R₁`. -/
  [isScalarTowerLeft : IsScalarTower R R₁ left]
  /-- The `R`-action on `right` factors through `R₂`. -/
  [isScalarTowerRight : IsScalarTower R R₂ right]
  /-- The identification of the two pieces over the overlap `L`. -/
  transition : L ⊗[R₁] left ≃ₗ[L] L ⊗[R₂] right

attribute [instance] PatchingData.addCommGroupLeft PatchingData.addCommGroupRight
  PatchingData.moduleLeft PatchingData.moduleRight PatchingData.moduleBaseLeft
  PatchingData.moduleBaseRight PatchingData.isScalarTowerLeft PatchingData.isScalarTowerRight

namespace PatchingData

variable {R R₁ R₂ L}

/-- A morphism of patching data: linear maps of the two pieces that are compatible with the
identifications over the overlap. Compatibility is tested on the elements `1 ⊗ x`. -/
@[ext]
structure Hom (D E : PatchingData R R₁ R₂ L) where
  /-- The map of the pieces over `R₁`. -/
  left : D.left →ₗ[R₁] E.left
  /-- The map of the pieces over `R₂`. -/
  right : D.right →ₗ[R₂] E.right
  /-- The two maps agree over the overlap. -/
  comm : ∀ x : D.left,
    E.transition (1 ⊗ₜ left x) = right.baseChange L (D.transition (1 ⊗ₜ x))

/-- The compatibility of a morphism of patching data, as an equality of `L`-linear maps. -/
theorem Hom.transition_comp_baseChange {D E : PatchingData R R₁ R₂ L} (f : Hom D E) :
    E.transition.toLinearMap ∘ₗ f.left.baseChange L =
      f.right.baseChange L ∘ₗ D.transition.toLinearMap := by
  ext x
  simpa using f.comm x

instance : Category (PatchingData R R₁ R₂ L) where
  Hom := Hom
  id D := ⟨LinearMap.id, LinearMap.id, fun _ ↦ by simp⟩
  comp f g := ⟨g.left ∘ₗ f.left, g.right ∘ₗ f.right, fun x ↦ by
    rw [LinearMap.comp_apply, g.comm, f.comm, LinearMap.baseChange_comp, LinearMap.comp_apply]⟩

@[ext]
theorem hom_ext {D E : PatchingData R R₁ R₂ L} {f g : D ⟶ E}
    (hl : Hom.left f = Hom.left g) (hr : Hom.right f = Hom.right g) : f = g :=
  Hom.ext hl hr

@[simp]
theorem id_left (D : PatchingData R R₁ R₂ L) : Hom.left (𝟙 D) = LinearMap.id :=
  (rfl)

@[simp]
theorem id_right (D : PatchingData R R₁ R₂ L) : Hom.right (𝟙 D) = LinearMap.id :=
  (rfl)

@[simp]
theorem comp_left {D E F : PatchingData R R₁ R₂ L} (f : D ⟶ E) (g : E ⟶ F) :
    Hom.left (f ≫ g) = Hom.left g ∘ₗ Hom.left f :=
  (rfl)

@[simp]
theorem comp_right {D E F : PatchingData R R₁ R₂ L} (f : D ⟶ E) (g : E ⟶ F) :
    Hom.right (f ≫ g) = Hom.right g ∘ₗ Hom.right f :=
  (rfl)

variable [Algebra R L] [IsScalarTower R R₁ L] [IsScalarTower R R₂ L]

section Sections

variable (D : PatchingData R R₁ R₂ L)

/-- The module of sections of a patching datum: the pairs `(x₁, x₂)` whose images
`α (1 ⊗ x₁)` and `1 ⊗ x₂` agree over the overlap. It is the module of compatible pairs
`ker (F.coprod (-G))` of the two maps `F = α ∘ (1 ⊗ ·)` and `G = (1 ⊗ ·)` to the overlap. -/
def sections : Submodule R (D.left × D.right) :=
  LinearMap.ker ((D.transition.toLinearMap.restrictScalars R ∘ₗ
    (TensorProduct.mk R₁ L D.left 1).restrictScalars R).coprod
      (-(TensorProduct.mk R₂ L D.right 1).restrictScalars R))

@[simp]
theorem mem_sections_iff (x : D.left × D.right) :
    x ∈ D.sections ↔ D.transition (1 ⊗ₜ x.1) = 1 ⊗ₜ x.2 := by
  simp [sections, add_neg_eq_zero]

/-- Two sections agree when their two coordinates agree. -/
@[ext]
theorem sections_ext {x y : D.sections}
    (h₁ : (x : D.left × D.right).1 = (y : D.left × D.right).1)
    (h₂ : (x : D.left × D.right).2 = (y : D.left × D.right).2) : x = y :=
  Subtype.ext (Prod.ext h₁ h₂)

/-- The comparison map `R₁ ⊗[R] sections D → left`, the scalar extension of the first
projection. -/
def compareLeft : R₁ ⊗[R] D.sections →ₗ[R₁] D.left :=
  (LinearMap.fst R D.left D.right ∘ₗ D.sections.subtype).liftBaseChange R₁

/-- The comparison map `R₂ ⊗[R] sections D → right`, the scalar extension of the second
projection. -/
def compareRight : R₂ ⊗[R] D.sections →ₗ[R₂] D.right :=
  (LinearMap.snd R D.left D.right ∘ₗ D.sections.subtype).liftBaseChange R₂

@[simp]
theorem compareLeft_tmul (a : R₁) (x : D.sections) :
    D.compareLeft (a ⊗ₜ x) = a • (x : D.left × D.right).1 :=
  (rfl)

@[simp]
theorem compareRight_tmul (b : R₂) (x : D.sections) :
    D.compareRight (b ⊗ₜ x) = b • (x : D.left × D.right).2 :=
  (rfl)

end Sections

/-- A morphism of patching data maps sections to sections, coordinatewise. -/
def sectionsMap {D E : PatchingData R R₁ R₂ L} (f : D ⟶ E) : D.sections →ₗ[R] E.sections :=
  (LinearMap.prodMap ((Hom.left f).restrictScalars R) ((Hom.right f).restrictScalars R)).restrict
    fun x hx ↦ by
      rw [mem_sections_iff] at hx ⊢
      simp [f.comm, hx]

@[simp]
theorem coe_sectionsMap_apply {D E : PatchingData R R₁ R₂ L} (f : D ⟶ E) (x : D.sections) :
    (sectionsMap f x : E.left × E.right) =
      (Hom.left f (x : D.left × D.right).1, Hom.right f (x : D.left × D.right).2) :=
  (rfl)

variable (R R₁ R₂ L) in
/-- The module of sections, as a functor from patching data to `R`-modules. -/
-- Exposed so that its objects unfold to the module of sections, as the adjunction requires.
@[expose, simps]
def sectionsFunctor : PatchingData R R₁ R₂ L ⥤ ModuleCat.{u} R where
  obj D := ModuleCat.of R D.sections
  map f := ModuleCat.ofHom (sectionsMap f)

section Can

variable (N : Type u) [AddCommGroup N] [Module R N]

variable (R R₁ R₂ L) in
/-- The canonical patching datum `(R₁ ⊗[R] N, R₂ ⊗[R] N, can)` of an `R`-module `N`, whose
transition is the identification of both scalar extensions with `L ⊗[R] N`. -/
abbrev can : PatchingData R R₁ R₂ L where
  left := R₁ ⊗[R] N
  right := R₂ ⊗[R] N
  transition := (AlgebraTensorModule.cancelBaseChange R R₁ L L N).trans
    (AlgebraTensorModule.cancelBaseChange R R₂ L L N).symm

theorem can_transition_tmul (l : L) (a : R₁) (n : N) :
    (can R R₁ R₂ L N).transition (l ⊗ₜ (a ⊗ₜ[R] n)) = (a • l) ⊗ₜ ((1 : R₂) ⊗ₜ[R] n) :=
  (rfl)

/-- The sections of the canonical datum of `N` are the kernel of the difference map
`(R₁ ⊗[R] N) × (R₂ ⊗[R] N) → L ⊗[R] N`. -/
theorem mem_sections_can_iff (x : (R₁ ⊗[R] N) × (R₂ ⊗[R] N)) :
    x ∈ (can R R₁ R₂ L N).sections ↔ patchingDifference R R₁ R₂ L N x = 0 := by
  refine ((can R R₁ R₂ L N).mem_sections_iff x).trans ?_
  rw [patchingDifference_apply, sub_eq_zero, ← AlgebraTensorModule.cancelBaseChange_one_tmul,
    ← AlgebraTensorModule.cancelBaseChange_one_tmul]
  exact LinearEquiv.symm_apply_eq _

variable {N} in
/-- A morphism `Can N ⟶ D` from maps of the two pieces that are compatible on the elements
`1 ⊗ n`: compatibility on all of `R₁ ⊗[R] N` follows by linearity. -/
private def canHom {D : PatchingData R R₁ R₂ L} (f₁ : R₁ ⊗[R] N →ₗ[R₁] D.left)
    (f₂ : R₂ ⊗[R] N →ₗ[R₂] D.right)
    (hf : ∀ n : N, D.transition (1 ⊗ₜ f₁ (1 ⊗ₜ n)) = 1 ⊗ₜ f₂ (1 ⊗ₜ n)) :
    can R R₁ R₂ L N ⟶ D :=
  ⟨f₁, f₂, fun x ↦ by
    induction x using TensorProduct.inductionOn with
    | tmul a n =>
      -- Write `a ⊗ n = a • (1 ⊗ n)` and pull `a` through the `L`-linear transition.
      rw [can_transition_tmul, tmul_eq_smul_one_tmul a, map_smul, tmul_smul, ← algebraMap_smul L,
        map_smul, hf]
      simp [Algebra.smul_def, smul_tmul']
    | add y z hy hz => simp only [map_add, tmul_add, hy, hz]⟩

@[simp]
private theorem canHom_left {D : PatchingData R R₁ R₂ L} (f₁ : R₁ ⊗[R] N →ₗ[R₁] D.left)
    (f₂ : R₂ ⊗[R] N →ₗ[R₂] D.right)
    (hf : ∀ n : N, D.transition (1 ⊗ₜ f₁ (1 ⊗ₜ n)) = 1 ⊗ₜ f₂ (1 ⊗ₜ n)) :
    Hom.left (canHom f₁ f₂ hf) = f₁ :=
  (rfl)

@[simp]
private theorem canHom_right {D : PatchingData R R₁ R₂ L} (f₁ : R₁ ⊗[R] N →ₗ[R₁] D.left)
    (f₂ : R₂ ⊗[R] N →ₗ[R₂] D.right)
    (hf : ∀ n : N, D.transition (1 ⊗ₜ f₁ (1 ⊗ₜ n)) = 1 ⊗ₜ f₂ (1 ⊗ₜ n)) :
    Hom.right (canHom f₁ f₂ hf) = f₂ :=
  (rfl)

variable {N} (R₁ R₂ L) in
/-- The canonical morphism of patching data `Can N ⟶ Can N'` induced by a linear map. -/
def canMap {N' : Type u} [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') :
    can R R₁ R₂ L N ⟶ can R R₁ R₂ L N' :=
  canHom (g.baseChange R₁) (g.baseChange R₂) fun _ ↦ by simp

@[simp]
theorem canMap_left {N' : Type u} [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') :
    Hom.left (canMap R₁ R₂ L g) = g.baseChange R₁ :=
  (rfl)

@[simp]
theorem canMap_right {N' : Type u} [AddCommGroup N'] [Module R N'] (g : N →ₗ[R] N') :
    Hom.right (canMap R₁ R₂ L g) = g.baseChange R₂ :=
  (rfl)

variable (R R₁ R₂ L) in
/-- The canonical datum, as a functor from `R`-modules to patching data. -/
-- Exposed so that its objects unfold to the canonical data, as the adjunction requires.
@[expose, simps]
def canFunctor : ModuleCat.{u} R ⥤ PatchingData R R₁ R₂ L where
  obj N := can R R₁ R₂ L N
  map g := canMap R₁ R₂ L g.hom
  map_id N := by ext <;> simp
  map_comp f g := by ext <;> simp [LinearMap.baseChange_comp]

variable (R R₁ R₂ L) in
/-- The unit `n ↦ (1 ⊗ n, 1 ⊗ n)` from a module to the sections of its canonical datum. -/
def canUnit : N →ₗ[R] (can R R₁ R₂ L N).sections :=
  (patchingDiagonal R R₁ R₂ N).codRestrict _ fun n ↦ by
    rw [mem_sections_can_iff, ← LinearMap.comp_apply, patchingDifference_comp_patchingDiagonal,
      LinearMap.zero_apply]

@[simp]
theorem coe_canUnit_apply (n : N) :
    (canUnit R R₁ R₂ L N n : (R₁ ⊗[R] N) × (R₂ ⊗[R] N)) = (1 ⊗ₜ n, 1 ⊗ₜ n) := by
  simp [canUnit]

end Can

section Adjunction

variable (N : Type u) [AddCommGroup N] [Module R N] (D : PatchingData R R₁ R₂ L)

/-- Morphisms of patching data from a canonical datum correspond to linear maps into the
sections: the sections functor is right adjoint to the canonical datum. -/
def homEquiv : (can R R₁ R₂ L N ⟶ D) ≃ (N →ₗ[R] D.sections) where
  toFun f := ((((Hom.left f).restrictScalars R ∘ₗ TensorProduct.mk R R₁ N 1).prod
      ((Hom.right f).restrictScalars R ∘ₗ TensorProduct.mk R R₂ N 1))).codRestrict _
    fun n ↦ by
      rw [mem_sections_iff]
      simp [f.comm]
  invFun φ := canHom ((LinearMap.fst R _ _ ∘ₗ D.sections.subtype ∘ₗ φ).liftBaseChange R₁)
    ((LinearMap.snd R _ _ ∘ₗ D.sections.subtype ∘ₗ φ).liftBaseChange R₂) fun n ↦ by
      simpa using (D.mem_sections_iff _).mp (φ n).property
  left_inv f := by
    ext x <;> simp
  right_inv φ := by
    ext n <;> simp

@[simp]
theorem homEquiv_apply_coe (f : can R R₁ R₂ L N ⟶ D) (n : N) :
    (homEquiv N D f n : D.left × D.right) = (Hom.left f (1 ⊗ₜ n), Hom.right f (1 ⊗ₜ n)) :=
  (rfl)

@[simp]
theorem homEquiv_symm_left (φ : N →ₗ[R] D.sections) :
    Hom.left ((homEquiv N D).symm φ) =
      (LinearMap.fst R D.left D.right ∘ₗ D.sections.subtype ∘ₗ φ).liftBaseChange R₁ :=
  (rfl)

@[simp]
theorem homEquiv_symm_right (φ : N →ₗ[R] D.sections) :
    Hom.right ((homEquiv N D).symm φ) =
      (LinearMap.snd R D.left D.right ∘ₗ D.sections.subtype ∘ₗ φ).liftBaseChange R₂ :=
  (rfl)

/-- Naturality of `homEquiv` in the module. -/
theorem homEquiv_symm_comp {N' : Type u} [AddCommGroup N'] [Module R N'] (f : N' →ₗ[R] N)
    (φ : N →ₗ[R] D.sections) :
    (homEquiv N' D).symm (φ ∘ₗ f) = canMap R₁ R₂ L f ≫ (homEquiv N D).symm φ := by
  ext n <;> simp

/-- Naturality of `homEquiv` in the patching datum. -/
theorem homEquiv_comp {E : PatchingData R R₁ R₂ L} (f : can R R₁ R₂ L N ⟶ D) (g : D ⟶ E) :
    homEquiv N E (f ≫ g) = sectionsMap g ∘ₗ homEquiv N D f := by
  ext n <;> simp

variable (R R₁ R₂ L) in
/-- The canonical datum is left adjoint to the sections: `Can ⊣ sections`. -/
def canAdjunction : canFunctor R R₁ R₂ L ⊣ sectionsFunctor R R₁ R₂ L :=
  Adjunction.mkOfHomEquiv
    { homEquiv N D := (homEquiv N D).trans
        (ModuleCat.homEquiv (M := N) (N := ModuleCat.of R D.sections)).symm
      homEquiv_naturality_left_symm f g := homEquiv_symm_comp _ _ f.hom g.hom
      homEquiv_naturality_right f g := by
        ext1
        exact homEquiv_comp _ _ f g }

/-- The unit of the adjunction `Can ⊣ sections` is `n ↦ (1 ⊗ n, 1 ⊗ n)`. -/
theorem canAdjunction_unit_app (N : ModuleCat.{u} R) :
    (canAdjunction R R₁ R₂ L).unit.app N = ModuleCat.ofHom (canUnit R R₁ R₂ L N) := by
  rw [← Adjunction.homEquiv_id, canAdjunction, Adjunction.mkOfHomEquiv_homEquiv]
  ext n
  exact Subtype.ext ((homEquiv_apply_coe _ _ _ n).trans (coe_canUnit_apply N n).symm)

end Adjunction

end PatchingData

namespace ExactSquare

open PatchingData

variable {R R₁ R₂ L} [Algebra R L] [IsScalarTower R R₁ L] [IsScalarTower R R₂ L]
  (h : ExactSquare R R₁ R₂ L)
include h

/-- Over an exact square, a module whose patching diagonal is injective is recovered from its
canonical patching datum: the unit `N → sections (Can N)` is bijective. The diagonal is injective
when `N` is flat (`ExactSquare.injective_patchingDiagonal`) or when the overlap `L` is flat
(`ExactSquare.injective_patchingDiagonal_of_flat_overlap`). -/
theorem bijective_canUnit (N : Type u) [AddCommGroup N] [Module R N]
    (hN : Function.Injective (patchingDiagonal R R₁ R₂ N)) :
    Function.Bijective (canUnit R R₁ R₂ L N) := by
  refine ⟨fun x y hxy ↦ hN (congr_arg Subtype.val hxy), fun ⟨x, hx⟩ ↦ ?_⟩
  obtain ⟨n, rfl⟩ := (h.exact_patchingDiagonal_patchingDifference N x).mp
    ((mem_sections_can_iff N x).mp hx)
  exact ⟨n, rfl⟩

/-- Over an exact square, a module whose patching diagonal is injective, for instance a flat
module, is isomorphic to the sections of its canonical patching datum. -/
noncomputable def canUnitEquiv (N : Type u) [AddCommGroup N] [Module R N]
    (hN : Function.Injective (patchingDiagonal R R₁ R₂ N)) :
    N ≃ₗ[R] (can R R₁ R₂ L N).sections :=
  LinearEquiv.ofBijective _ (h.bijective_canUnit N hN)

@[simp]
theorem coe_canUnitEquiv_apply (N : Type u) [AddCommGroup N] [Module R N]
    (hN : Function.Injective (patchingDiagonal R R₁ R₂ N)) (n : N) :
    (h.canUnitEquiv N hN n : (R₁ ⊗[R] N) × (R₂ ⊗[R] N)) = (1 ⊗ₜ n, 1 ⊗ₜ n) :=
  coe_canUnit_apply N n

/-- Over an exact square, morphisms of canonical patching data `Can M ⟶ Can N` are exactly the
`R`-linear maps `M → N` when the patching diagonal of `N` is injective, for instance when `N` or
the overlap is flat: compatible maps of the two scalar extensions descend uniquely. The inverse is
`canMap` (`ExactSquare.canHomEquiv_symm_apply`). -/
noncomputable def canHomEquiv (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (hN : Function.Injective (patchingDiagonal R R₁ R₂ N)) :
    (can R R₁ R₂ L M ⟶ can R R₁ R₂ L N) ≃ (M →ₗ[R] N) :=
  (homEquiv M (can R R₁ R₂ L N)).trans
    { toFun φ := (h.canUnitEquiv N hN).symm.toLinearMap ∘ₗ φ
      invFun g := (h.canUnitEquiv N hN).toLinearMap ∘ₗ g
      left_inv φ := by ext x : 1; simp
      right_inv g := by ext x : 1; simp }

@[simp]
theorem canHomEquiv_symm_apply (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (hN : Function.Injective (patchingDiagonal R R₁ R₂ N)) (g : M →ₗ[R] N) :
    (h.canHomEquiv M N hN).symm g = canMap R₁ R₂ L g := by
  rw [Equiv.symm_apply_eq]
  ext m
  simp only [canHomEquiv, Equiv.trans_apply, Equiv.coe_fn_mk, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.eq_symm_apply]
  ext <;> rw [coe_canUnitEquiv_apply, homEquiv_apply_coe] <;> simp

end ExactSquare

end TauCeti
