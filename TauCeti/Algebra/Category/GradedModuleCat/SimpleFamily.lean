/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.CartanMap.Basic
public import TauCeti.CategoryTheory.Simple.Basic

/-!
# Exhaustive families of graded simple modules

A family is exhaustive up to internal shifts when every simple finite graded module is
isomorphic to a shift of a member. This property is used both to classify simple modules and
to construct their classes in the graded Grothendieck group.
-/

public section

namespace TauCeti

open CategoryTheory

universe uk uA uI

/-! ### Exhaustive families of graded simples -/

section Exhaustive

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI}

/-- A family of finite graded modules is an **exhaustive family of graded simples up to shift** if
every finite graded module which is a simple object of the graded module category is isomorphic to
an internal shift `(S i){d}` of a member of the family. -/
def IsExhaustiveGradedSimpleFamily (S : I → (gradedFiniteModules 𝒜).FullSubcategory) : Prop :=
  ∀ M : (gradedFiniteModules 𝒜).FullSubcategory, Simple M.obj →
    ∃ i d, Nonempty (M.obj ≅ (S i).obj.shiftObj d)

/-- Characterization of `IsExhaustiveGradedSimpleFamily`, for importing modules, to which the body
of the definition is not exposed. -/
theorem isExhaustiveGradedSimpleFamily_iff (S : I → (gradedFiniteModules 𝒜).FullSubcategory) :
    IsExhaustiveGradedSimpleFamily S ↔
      ∀ M : (gradedFiniteModules 𝒜).FullSubcategory, Simple M.obj →
        ∃ i d, Nonempty (M.obj ≅ (S i).obj.shiftObj d) :=
  Iff.rfl

/-- An exhaustive family up to shift is exhaustive without shifts among simple modules
concentrated in degree zero, provided the chosen representatives are also concentrated in degree
zero. -/
theorem IsExhaustiveGradedSimpleFamily.exists_iso_of_concentrated
    (S : I → (gradedFiniteModules 𝒜).FullSubcategory)
    (hS : IsExhaustiveGradedSimpleFamily S)
    (hSzero : ∀ i p, p ≠ 0 → (S i).obj.grading.piece p = ⊥)
    (N : (gradedFiniteModules 𝒜).FullSubcategory) (hNsimple : Simple N.obj)
    (hNzero : ∀ p, p ≠ 0 → N.obj.grading.piece p = ⊥) :
    ∃ i, Nonempty (N.obj ≅ (S i).obj) := by
  obtain ⟨i, d, ⟨e⟩⟩ := (isExhaustiveGradedSimpleFamily_iff S).1 hS N hNsimple
  have hd : d = 0 := by
    by_contra hd
    apply Simple.not_isZero N.obj
    rw [CategoryTheory.Limits.IsZero.iff_id_eq_zero]
    apply GradedModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    -- The categorical identity and zero morphisms act on the underlying module as `x` and `0`.
    change x = 0
    induction x using DirectSum.Decomposition.inductionOn N.obj.grading.piece with
    | zero => rfl
    | add x y hx hy => simp [hx, hy]
    | @homogeneous p x =>
        by_cases hp : p = 0
        · subst p
          apply (GradedModuleCat.mono_iff_injective e.hom).1 inferInstance
          have hx := GradedModuleCat.map_mem e.hom x.property
          rw [GradedModuleCat.mem_shiftObj_piece_iff] at hx
          simpa only [hSzero i (0 - d) (by omega), Submodule.mem_bot, map_zero] using hx
        · simpa only [hNzero p hp, Submodule.mem_bot] using x.property
  subst d
  exact ⟨i, ⟨e ≪≫ (GradedModuleCat.shiftFunctorZeroIso 𝒜).app (S i).obj⟩⟩

end Exhaustive

section Pairs

variable {k : Type uk} [Field k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {I : Type uI} [Module.Finite k A]

/-- A property of pairs which is invariant under isomorphisms and internal shifts and can be
tested on finite-dimensional simples in either variable is detected on an exhaustive family
of simples up to shift. -/
theorem IsExhaustiveGradedSimpleFamily.prop_on_pairs
    {S : I → (gradedFiniteModules 𝒜).FullSubcategory} (hS : IsExhaustiveGradedSimpleFamily S)
    (P : GradedModuleCat.{uA} 𝒜 → GradedModuleCat.{uA} 𝒜 → Prop)
    (hiso : ∀ {X X' Y Y'}, P X Y → (X ≅ X') → (Y ≅ Y') → P X' Y')
    (hshift : ∀ {X Y}, P X Y → ∀ d, P (X.shiftObj d) Y)
    (hshiftRight : ∀ {X Y}, P X Y → ∀ d, P X (Y.shiftObj d))
    (hleft : ∀ Y, (∀ T : GradedModuleCat.{uA} 𝒜, Module.Finite k T → Simple T → P T Y) →
      ∀ X : GradedModuleCat.{uA} 𝒜, Module.Finite k X → P X Y)
    (hright : ∀ X, (∀ T : GradedModuleCat.{uA} 𝒜, Module.Finite k T → Simple T → P X T) →
      ∀ Y : GradedModuleCat.{uA} 𝒜, Module.Finite k Y → P X Y)
    (h : ∀ i j, P (S i).obj (S j).obj)
    {X Y : GradedModuleCat.{uA} 𝒜} (hX : gradedFiniteModules 𝒜 X)
    (hY : gradedFiniteModules 𝒜 Y) : P X Y := by
  have hshiftSimple (T : GradedModuleCat.{uA} 𝒜) (hTfin : Module.Finite k T)
      (hT : Simple T) : ∃ i d, Nonempty (T ≅ (S i).obj.shiftObj d) := by
    have := hTfin
    exact (isExhaustiveGradedSimpleFamily_iff S).1 hS
      ⟨T, gradedFiniteModules_iff.2 (Module.Finite.of_restrictScalars_finite k A T)⟩ hT
  have : Module.Finite A X := gradedFiniteModules_iff.1 hX
  have : Module.Finite A Y := gradedFiniteModules_iff.1 hY
  have : Module.Finite k X := Module.Finite.trans A X
  have : Module.Finite k Y := Module.Finite.trans A Y
  refine hleft Y (fun T hTfin hT ↦ ?_) X inferInstance
  obtain ⟨i, d, ⟨φ⟩⟩ := hshiftSimple T hTfin hT
  refine hiso (hshift ?_ d) φ.symm (Iso.refl Y)
  refine hright (S i).obj (fun T' hT'fin hT' ↦ ?_) Y inferInstance
  obtain ⟨j, d', ⟨φ'⟩⟩ := hshiftSimple T' hT'fin hT'
  exact hiso (hshiftRight (h i j) d') (Iso.refl _) φ'.symm

end Pairs

end TauCeti
