/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import TauCeti.GroupTheory.GroupAlgGeom.ChangeOfCoordinates

/-!
# Solutions of a generalised equation minimal with respect to a group of automorphisms

Let `M` be a group of automorphisms of the coordinate group `F_{R(Ω)}` of a generalised equation `Ω`
over `F(A)`. A solution `U₁` of `Ω` is *smaller* than a solution `U₂` with respect to `M`, written
`U₁ <_M U₂`, if `U₂ = U₁ ∘ σ` as homomorphisms `F_{R(Ω)} → F(A)` for some `σ ∈ M`, no item is longer
in `U₁` than in `U₂`, and some item is shorter. A solution is *`M`-minimal* if no solution is
smaller than it. Since the total length of a solution decreases strictly along `<_M`, every
solution is minimal or lies above a minimal one. In the Makanin–Razborov process the groups `M`
are built from groups of canonical automorphisms of the vertices of the solution tree, and the
paths of minimal solutions through the tree stay in a finite subtree.

The source differs as follows. Its condition is `U₂ = π ∘ U₁ ∘ σ` for an endomorphism `π` of
`F(A ∪ B)` fixing the letters of `A` and the parameters; for generalised equations with constants
in `A` and no parameters `π` is the identity, and it is omitted here. It compares only the lengths
of the active items; the two relations agree when every element of `M` fixes the other items. Its
automorphisms fix `F(A)`, while here `M` is any group of automorphisms; none of the results needs
more. Finally, it asserts a minimal solution strictly below every solution, which fails when the
solution is itself minimal; `exists_isAutMinimal` allows equality.

## Main definitions

* `TauCeti.GenEq.Solution.AutLT`: the relation `U₁ <_M U₂`.
* `TauCeti.GenEq.Solution.IsAutMinimal`: `M`-minimal solutions.

## Main results

* `TauCeti.GenEq.Solution.AutLT.trans`: `<_M` is transitive.
* `TauCeti.GenEq.Solution.wellFounded_autLT`: `<_M` is well founded.
* `TauCeti.GenEq.Solution.exists_isAutMinimal`: every solution is `M`-minimal or lies above an
  `M`-minimal solution.

## References

* [IFT] O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra
  290 (2005), §5.5.1.
-/

public section

open TauCeti.GroupAlgGeom

namespace TauCeti.GenEq.Solution

variable {A : Type*} {Ω : GenEq A} (M : Subgroup (MulAut Ω.coordGroup))

/-- `U₁ <_M U₂`: the homomorphism of `U₂` is that of `U₁` composed with an automorphism in `M`, no
item is longer in `U₁` than in `U₂`, and some item is shorter. -/
def AutLT (U₁ U₂ : Ω.Solution) : Prop :=
  (∃ σ ∈ M, ∀ g, U₂.toHom g = U₁.toHom (σ g)) ∧
    (∀ k, (U₁.word k).length ≤ (U₂.word k).length) ∧ ∃ k, (U₁.word k).length < (U₂.word k).length

/-- Unfolding `U₁ <_M U₂`. -/
theorem autLT_iff {U₁ U₂ : Ω.Solution} : AutLT M U₁ U₂ ↔
    (∃ σ ∈ M, ∀ g, U₂.toHom g = U₁.toHom (σ g)) ∧ (∀ k, (U₁.word k).length ≤ (U₂.word k).length) ∧
      ∃ k, (U₁.word k).length < (U₂.word k).length :=
  Iff.rfl

variable {M}

/-- The relation `<_M` is transitive. -/
theorem AutLT.trans {U₁ U₂ U₃ : Ω.Solution} (h₁₂ : AutLT M U₁ U₂) (h₂₃ : AutLT M U₂ U₃) :
    AutLT M U₁ U₃ := by
  obtain ⟨⟨σ, hσ, h⟩, hle, k, hk⟩ := h₁₂
  obtain ⟨⟨τ, hτ, h'⟩, hle', -⟩ := h₂₃
  exact ⟨⟨σ * τ, M.mul_mem hσ hτ, fun g ↦ (h' g).trans (h (τ g))⟩,
    fun j ↦ (hle j).trans (hle' j), k, hk.trans_le (hle' k)⟩

variable (M)

/-- The relation `<_M` is well founded: the total length of a solution decreases strictly along
it. -/
theorem wellFounded_autLT : WellFounded (AutLT M) :=
  Subrelation.wf (fun {_ _} h ↦ Fintype.sum_strictMono (Pi.lt_def.2 h.2))
    (measure fun U : Ω.Solution ↦ ∑ k, (U.word k).length).wf

/-- A solution is *`M`-minimal* when no solution is smaller than it with respect to `M`. -/
def IsAutMinimal (U : Ω.Solution) : Prop :=
  ∀ U' : Ω.Solution, ¬ AutLT M U' U

/-- Unfolding `M`-minimality. -/
theorem isAutMinimal_iff {U : Ω.Solution} : IsAutMinimal M U ↔ ∀ U', ¬ AutLT M U' U :=
  Iff.rfl

/-- Every solution is `M`-minimal or lies above an `M`-minimal solution. -/
theorem exists_isAutMinimal (U : Ω.Solution) :
    ∃ U₀ : Ω.Solution, IsAutMinimal M U₀ ∧ (U₀ = U ∨ AutLT M U₀ U) := by
  obtain ⟨U₀, hU₀, hmin⟩ := (wellFounded_autLT M).has_min {U' | U' = U ∨ AutLT M U' U} ⟨U, .inl rfl⟩
  refine ⟨U₀, fun U' h ↦ hmin U' ?_ h, hU₀⟩
  rcases hU₀ with rfl | hU₀
  exacts [.inr h, .inr (h.trans hU₀)]

/-! ### Example: one free item -/

section Example

open Monoid.Coprod

/-- The generalised equation over `F(a, b)` with a single item `h` and no bases, with `a = 0` and
`b = 1`. -/
private abbrev freeItem : GenEq (Fin 2) where
  numItems := 1
  numBases := 0
  left := Fin.elim0
  right := Fin.elim0
  left_lt_right := fun μ ↦ μ.elim0
  sign := Fin.elim0
  dual := Fin.elim0
  dual_involutive := fun μ ↦ μ.elim0
  constBases := ∅
  connections := ∅
  bounds_of_mem_connections := by simp
  dual_mem_connections := by simp

private theorem toSystem_freeItem : freeItem.toSystem = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun w hw ↦ ?_
  obtain ⟨e, he, -⟩ := (mem_toSystem_iff _).1 hw
  exact (forall_mem_equations (P := fun _ ↦ False) _).2
    ⟨fun μ ↦ μ.elim0, fun _ hb ↦ absurd hb (Finset.notMem_empty _),
      fun _ hc ↦ absurd hc (Finset.notMem_empty _)⟩ e he

/-- The automorphism `h ↦ h a` of `F(a, b)[h]`. -/
private noncomputable abbrev mulRightA : MulAut (GX (FreeGroup (Fin 2)) (Fin 1)) :=
  GX.transvection 0 1 (inl (FreeGroup.of 0)) (one_mem _) (GX.inl_mem_avoiding 0 _)

/-- The automorphism `h ↦ h a` of the coordinate group of `freeItem`. -/
private noncomputable def coordMulRightA : MulAut freeItem.coordGroup :=
  QuotientGroup.congr _ _ mulRightA (by
    rw [← Rad_image_mulEquiv _ mulRightA (GX.transvection_inl _ _), toSystem_freeItem,
      Set.image_empty])

/-- The solution `h = b`. -/
private def solB : freeItem.Solution :=
  ofNumBasesEqZero (Ω := freeItem) rfl rfl ![[(1, true)]]
    (by unfold FreeGroup.IsReduced; decide) (by decide)

/-- The solution `h = ba`. -/
private def solBA : freeItem.Solution :=
  ofNumBasesEqZero (Ω := freeItem) rfl rfl ![[(1, true), (0, true)]]
    (by unfold FreeGroup.IsReduced; decide) (by decide)

/-- `h = b` is smaller than `h = ba` with respect to the group generated by `h ↦ h a`. -/
private theorem autLT_solB_solBA : AutLT (Subgroup.zpowers coordMulRightA) solB solBA := by
  refine ⟨⟨coordMulRightA, Subgroup.mem_zpowers _, fun g ↦ ?_⟩, by simp [solB, solBA], 0,
    by simp [solB, solBA]⟩
  induction g using QuotientGroup.induction_on with
  | H w =>
    rw [coordMulRightA, QuotientGroup.congr_mk, toHom_mk, toHom_mk, GX.eval_transvection]
    congr 2
    funext k
    rw [Subsingleton.elim k 0]
    simp [solB, solBA, FreeGroup.of, FreeGroup.mul_mk]

/-- `h = ba` is not minimal with respect to the group generated by `h ↦ h a`. -/
example : ¬ IsAutMinimal (Subgroup.zpowers coordMulRightA) solBA :=
  fun h ↦ h solB autLT_solB_solBA

/-- `h = b` is minimal with respect to every group of automorphisms: no item of a solution is
empty. -/
example (M : Subgroup (MulAut freeItem.coordGroup)) : IsAutMinimal M solB := by
  rintro U ⟨-, -, k, hk⟩
  exact U.word_ne_nil k (by simpa [solB] using hk)

end Example

end TauCeti.GenEq.Solution
