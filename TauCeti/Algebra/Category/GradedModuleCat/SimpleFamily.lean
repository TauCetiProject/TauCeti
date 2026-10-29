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

end TauCeti
