/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.RingTheory.Coalgebra.GroupLike
import TauCeti.Algebra.Coalgebra.Subcoalgebra

/-!
# Subcoalgebras spanned by group-like elements

This file defines the subcoalgebra spanned by a set of group-like elements, together with the
singleton span and finite-generation instance used by the finite-subcoalgebra API.
-/

open scoped TensorProduct

namespace TauCeti

universe u v

variable (R : Type u) (C : Type v)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

namespace Subcoalgebra

variable {R C}

/-- The subcoalgebra spanned by a set of group-like elements. -/
def groupLikeSetSpan (s : Set (GroupLike R C)) : Subcoalgebra R C :=
  let D := Submodule.span R ((↑) '' s : Set C)
  { carrier := D
    comul_mem' := by
      intro c hc
      refine Submodule.span_induction
        (p := fun c _ =>
          Coalgebra.comul (R := R) (A := C) c ∈
            LinearMap.range (TensorProduct.map D.subtype D.subtype)) ?mem ?zero ?add ?smul hc
      · intro x hx
        rcases hx with ⟨g, hg, rfl⟩
        have hgD : (g : C) ∈ D := Submodule.subset_span ⟨g, hg, rfl⟩
        refine ⟨⟨g, hgD⟩ ⊗ₜ[R] ⟨g, hgD⟩, ?_⟩
        change (g : C) ⊗ₜ[R] (g : C) = Coalgebra.comul (R := R) (A := C) (g : C)
        exact g.isGroupLikeElem_val.comul_eq_tmul_self.symm
      · exact ⟨0, by simp⟩
      · intro x y hx hy hx' hy'
        rcases hx' with ⟨x', hx'⟩
        rcases hy' with ⟨y', hy'⟩
        refine ⟨x' + y', ?_⟩
        rw [LinearMap.map_add, hx', hy']
        exact ((Coalgebra.comul (R := R) (A := C)).map_add x y).symm
      · intro r x hx hx'
        rcases hx' with ⟨x', hx'⟩
        refine ⟨r • x', ?_⟩
        rw [LinearMap.map_smul, hx']
        exact ((Coalgebra.comul (R := R) (A := C)).map_smul r x).symm }

@[simp]
theorem groupLikeSetSpan_toSubmodule (s : Set (GroupLike R C)) :
    (groupLikeSetSpan (R := R) (C := C) s).toSubmodule =
      Submodule.span R ((↑) '' s : Set C) :=
  rfl

theorem mem_groupLikeSetSpan {s : Set (GroupLike R C)} {c : C} :
    c ∈ groupLikeSetSpan (R := R) (C := C) s ↔
      c ∈ Submodule.span R ((↑) '' s : Set C) :=
  Iff.rfl

/-- The subcoalgebra spanned by a group-like element. -/
def groupLikeSpan (g : GroupLike R C) : Subcoalgebra R C :=
  groupLikeSetSpan (R := R) (C := C) {g}

@[simp]
theorem groupLikeSpan_toSubmodule (g : GroupLike R C) :
    (groupLikeSpan (R := R) (C := C) g).toSubmodule = R ∙ (g : C) := by
  rw [groupLikeSpan, groupLikeSetSpan_toSubmodule]
  congr 1
  ext c
  simp

/-- A group-like element belongs to its span subcoalgebra. -/
@[simp]
theorem groupLike_mem_groupLikeSpan (g : GroupLike R C) :
    (g : C) ∈ groupLikeSpan (R := R) (C := C) g := by
  change (g : C) ∈ (groupLikeSpan (R := R) (C := C) g).toSubmodule
  rw [groupLikeSpan_toSubmodule]
  exact Submodule.mem_span_singleton_self (g : C)

/-- Membership in the subcoalgebra spanned by a group-like element. -/
theorem mem_groupLikeSpan {g : GroupLike R C} {c : C} :
    c ∈ groupLikeSpan (R := R) (C := C) g ↔ ∃ r : R, r • (g : C) = c := by
  rw [← mem_toSubmodule, groupLikeSpan_toSubmodule, Submodule.mem_span_singleton]

/-- The subcoalgebra spanned by a group-like element is finite. -/
instance groupLikeSpan_isFinite (g : GroupLike R C) :
    Module.Finite R (groupLikeSpan (R := R) (C := C) g).toSubmodule := by
  rw [groupLikeSpan_toSubmodule]
  exact Module.Finite.of_fg (Submodule.fg_span_singleton (g : C))

end Subcoalgebra

end TauCeti
