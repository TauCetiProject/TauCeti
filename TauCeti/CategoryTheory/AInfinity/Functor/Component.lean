/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.AInfinity.Functor.Basic

/-!
# Components of A-infinity functors on composable strings

An `A∞` functor stores its components as multilinear maps between the total modules of
morphisms.  This file restricts those maps to a composable string of objects.  For
`X : Fin (n + 1) → C`, the resulting component has the familiar form

`fₙ : Hom(Xₙ₋₁, Xₙ) × ⋯ × Hom(X₀, X₁) ⟶ Hom(F X₀, F Xₙ)`.

It has cohomological degree `1 - n`.  Including its value in the total module recovers the
stored total-algebra component, so the path-level API loses no information.  In arity one it is
the map of the functor on a Hom module.  These components determine the functor once its object
map is fixed.

## Main definitions

* `TauCeti.AInfinityFunctor.component`: the component of an `A∞` functor on a composable string.

## Main results

* `TauCeti.AInfinityFunctor.homInclusion_component`: the path component recovers the stored
  component between total morphism modules.
* `TauCeti.AInfinityFunctor.component_mem_piece`: the arity-`n` component has degree `1 - n`.
* `TauCeti.AInfinityFunctor.component_one_apply`: the unary component is the Hom map.
* `TauCeti.AInfinityFunctor.ext_component`: path components and the object map determine a
  functor.

## References

* B. Keller, *Introduction to A-infinity algebras and modules*, Sections 3.4 and 7.
* V. Lyubashenko, *Category of A-infinity-categories*, Homology, Homotopy and Applications 5
  (2003), for functor components on composable strings.
-/

public section

namespace TauCeti

open GradedLinearQuiver GradedLinearQuiver.InducedQuiver

universe u₁ u₂ v₁ v₂ w

variable {R : Type w} [CommRing R] {C : Type u₁} {D : Type u₂}
  [GradedLinearQuiver.{u₁, v₁, w} R C] [GradedLinearQuiver.{u₂, v₂, w} R D]
  {𝒷 : AInfinityCategory R C} {𝒸 : AInfinityCategory R D}

namespace AInfinityFunctor

variable (ℱ : AInfinityFunctor 𝒷 𝒸)

/-- The **arity-`n` component of an `A∞` functor on a composable string**
`X₀, …, Xₙ`.  Its inputs are ordered
`Hom(Xₙ₋₁, Xₙ), …, Hom(X₀, X₁)`, as for the operations of an `A∞` category, and its
value is a morphism from `ℱ.obj (X 0)` to `ℱ.obj (X (Fin.last n))`. -/
noncomputable def component {n : ℕ} (X : Fin (n + 1) → C) :
    MultilinearMap R
      (fun i : Fin n ↦ homModule (R := R) (X i.rev.castSucc) (X i.rev.succ))
      (homModule (R := R) (ℱ.obj (X 0)) (ℱ.obj (X (Fin.last n)))) :=
  (homProjection (R := R) (C := InducedQuiver D ℱ.obj) ⟨X 0⟩ ⟨X (Fin.last n)⟩).compMultilinearMap
    ((ℱ.toAInfinityHom.component n).compLinearMap fun i ↦
      homInclusion (R := R) (X i.rev.castSucc) (X i.rev.succ))

/-- Evaluating a functor component means including every input into the source total module,
applying the stored total-algebra component, and projecting to the Hom module between the image
endpoints. -/
theorem component_apply {n : ℕ} (X : Fin (n + 1) → C)
    (f : ∀ i : Fin n, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ)) :
    ℱ.component X f =
      homProjection (R := R) (C := InducedQuiver D ℱ.obj) ⟨X 0⟩ ⟨X (Fin.last n)⟩
        (ℱ.toAInfinityHom.component n fun i ↦
          homInclusion (X i.rev.castSucc) (X i.rev.succ) (f i)) :=
  (rfl)

/-- **A path component is the stored total component.**  Including the value of the component on
a composable string into the total module of the induced target category recovers the component
of the `A∞` morphism of total algebras. -/
@[simp]
theorem homInclusion_component {n : ℕ} (X : Fin (n + 1) → C)
    (f : ∀ i : Fin n, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ)) :
    homInclusion (R := R) (C := InducedQuiver D ℱ.obj) ⟨X 0⟩ ⟨X (Fin.last n)⟩
        (ℱ.component X f) =
      ℱ.toAInfinityHom.component n fun i ↦
        homInclusion (X i.rev.castSucc) (X i.rev.succ) (f i) := by
  rw [component_apply]
  exact homInclusion_homProjection_of_mem_range
    ((ℱ.isPathCompatible_component n).mem_range_homInclusion X f)

/-- The component of a functor in arity zero is zero. -/
@[simp]
theorem component_zero (X : Fin 1 → C) : ℱ.component X = 0 := by
  apply MultilinearMap.ext
  intro f
  apply homInclusion_injective (C := InducedQuiver D ℱ.obj) ⟨X 0⟩ ⟨X (Fin.last 0)⟩
  rw [homInclusion_component, AInfinityHom.component_zero]
  simp

/-- The arity-`n` component of an `A∞` functor sends homogeneous inputs of degrees `dᵢ` to a
morphism of degree `∑ dᵢ + 1 - n`. -/
@[grind =>]
theorem component_mem_piece {n : ℕ} (X : Fin (n + 1) → C) (d : Fin n → ℤ)
    (f : ∀ i : Fin n, homModule (R := R) (X i.rev.castSucc) (X i.rev.succ))
    (hf : ∀ i, f i ∈ (grading (R := R) (X i.rev.castSucc) (X i.rev.succ)).piece (d i)) :
    ℱ.component X f ∈
      (grading (R := R) (ℱ.obj (X 0)) (ℱ.obj (X (Fin.last n)))).piece
        ((∑ i, d i) + (1 - n)) := by
  have hf' : ∀ i, homInclusion (X i.rev.castSucc) (X i.rev.succ) (f i) ∈
      𝒷.toAInfinityAlgebra.grading.piece (d i) := by
    intro i
    rw [𝒷.grading_eq]
    exact (homInclusion_mem_totalGrading_piece_iff _ _).2 (hf i)
  have h := ℱ.toAInfinityHom.isHomogeneous_component n |>.map_mem d
    (fun i ↦ homInclusion (X i.rev.castSucc) (X i.rev.succ) (f i))
    hf'
  rw [(𝒸.induced ℱ.obj).grading_eq] at h
  exact homProjection_mem_piece h ⟨X 0⟩ ⟨X (Fin.last n)⟩

/-- The arity-`n` component of an `A∞` functor is homogeneous of degree `1 - n` between
the gradings of the Hom modules along the source string and its image endpoints. -/
theorem isHomogeneous_component {n : ℕ} (X : Fin (n + 1) → C) :
    MultilinearMap.IsHomogeneous (ℱ.component X)
      (fun i ↦ (grading (R := R) (X i.rev.castSucc) (X i.rev.succ)).piece)
      (grading (R := R) (ℱ.obj (X 0)) (ℱ.obj (X (Fin.last n)))).piece (1 - n) := by
  rw [MultilinearMap.isHomogeneous_def]
  intro d f hf
  exact ℱ.component_mem_piece X d f hf

/-- The component of an `A∞` functor in arity one is its map on the corresponding Hom
module. -/
theorem component_one_apply (X Y : C) (f : homModule (R := R) X Y) :
    let x := Fin.cases (motive := fun i ↦ homModule (R := R)
      (![X, Y] i.rev.castSucc) (![X, Y] i.rev.succ)) f fun i ↦ i.elim0
    ℱ.component ![X, Y] x = ℱ.map X Y f := by
  dsimp only
  -- The input tuple is built with `Fin.cases`, so its endpoints compute without equality casts.
  apply homInclusion_injective (C := InducedQuiver D ℱ.obj) ⟨X⟩ ⟨Y⟩
  have h := ℱ.homInclusion_component ![X, Y]
    (Fin.cases (motive := fun i ↦ homModule (R := R)
      (![X, Y] i.rev.castSucc) (![X, Y] i.rev.succ)) f fun i ↦ i.elim0)
  rw [AInfinityHom.component_one, MultilinearMap.ofSubsingleton_apply_apply] at h
  exact h.trans (ℱ.homInclusion_map X Y f).symm

/-- Two `A∞` functors with the same object map are equal when their positive-arity components
on composable strings agree. -/
@[ext (iff := false)]
theorem ext_component {ℱ 𝒢 : AInfinityFunctor 𝒷 𝒸} (hobj : ℱ.obj = 𝒢.obj)
    (hcomponent : ∀ (n : ℕ), 0 < n → ∀ (X : Fin (n + 1) → C),
      HEq (ℱ.component X) (𝒢.component X)) : ℱ = 𝒢 := by
  cases ℱ with
  | mk F f hF =>
    cases 𝒢 with
    | mk G g hG =>
      dsimp only at hobj
      subst G
      refine AInfinityFunctor.ext
        (ℱ := AInfinityFunctor.mk F f hF) (𝒢 := AInfinityFunctor.mk F g hG) rfl ?_
      apply heq_of_eq
      apply AInfinityHom.ext_component
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn.ne'
        apply (AInfinityFunctor.mk F f hF).isPathCompatible_component (k + 1) |>.ext
          ((AInfinityFunctor.mk F g hG).isPathCompatible_component (k + 1))
        intro X x
        have h := MultilinearMap.congr_fun
          (eq_of_heq (hcomponent (k + 1) (Nat.succ_pos k) X)) x
        rw [← (AInfinityFunctor.mk F f hF).homInclusion_component X x,
          ← (AInfinityFunctor.mk F g hG).homInclusion_component X x]
        exact congrArg
          (homInclusion (R := R) (C := InducedQuiver D F) ⟨X 0⟩ ⟨X (Fin.last (k + 1))⟩) h

end AInfinityFunctor

end TauCeti
