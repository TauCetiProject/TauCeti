/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.Pullback
public import Mathlib.Topology.Covering.Basic
public import Mathlib.Data.Set.Card

/-!
# Cardinality of fibers under local covering charts

Fiber cardinalities can be checked on an open cover of the base. A pullback has the same fiber
cardinality as the original map over the corresponding base point.
-/

public noncomputable section

open TopologicalSpace

namespace TauCeti.Covering

private theorem ncard_fiber_eq_of_homeomorph {A X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y]
    {p : X → Y} {q : A → Y} (U : TopologicalSpace.Opens Y)
    (k : A ≃ₜ {x : X // p x ∈ U}) (hk : ∀ a, p (k a).1 = q a)
    {y : Y} (hy : y ∈ U) :
    (p ⁻¹' {y}).ncard = (q ⁻¹' {y}).ncard := by
  let e : (p ⁻¹' {y}) ≃ (q ⁻¹' {y}) := {
    toFun := fun z =>
      ⟨k.symm ⟨z.1, by rw [z.2]; exact hy⟩, by
        have h : p (k (k.symm ⟨z.1, by rw [z.2]; exact hy⟩)).1 = p z.1 :=
          congrArg (fun w : {x : X // p x ∈ U} ↦ p w.1)
            (k.apply_symm_apply ⟨z.1, by rw [z.2]; exact hy⟩)
        exact (hk _).symm.trans (h.trans z.2)⟩
    invFun := fun a => ⟨(k a.1).1, (hk a.1).trans a.2⟩
    left_inv := by
      intro z
      apply Subtype.ext
      change (k (k.symm ⟨z.1, by rw [z.2]; exact hy⟩)).1 = z.1
      exact congrArg Subtype.val
        (k.apply_symm_apply ⟨z.1, by rw [z.2]; exact hy⟩)
    right_inv := by
      intro a
      apply Subtype.ext
      exact k.symm_apply_apply a.1 }
  exact Set.ncard_congr' e

/-- Pullback fibers have the same cardinality as the corresponding original fibers. -/
theorem ncard_pullback_fiber {A B C : Type*} (f : A → B) (q : C → B)
    (a : A) :
    ((Function.Pullback.fst : f.Pullback q → A) ⁻¹' {a}).ncard =
      (q ⁻¹' {f a}).ncard := by
  let e : ((Function.Pullback.fst : f.Pullback q → A) ⁻¹' {a}) ≃ (q ⁻¹' {f a}) := {
    toFun := fun z ↦ ⟨z.1.1.2, by
      have h := z.1.2
      have ha : z.1.1.1 = a := z.2
      exact h.symm.trans (congrArg f ha)⟩
    invFun := fun c ↦ ⟨⟨(a, c.1), c.2.symm⟩, rfl⟩
    left_inv := by
      intro z
      apply Subtype.ext
      apply Subtype.ext
      change (a, z.1.1.2) = z.1.1
      exact Prod.ext z.2.symm rfl
    right_inv := by intro c; rfl }
  exact Set.ncard_congr' e

/-- A homeomorphism of the base preserves the cardinality of each fiber. -/
theorem ncard_fiber_homeomorph_comp {X Y Z : Type*}
    [TopologicalSpace Y] [TopologicalSpace Z]
    (p : X → Y) (e : Y ≃ₜ Z) (z : Z) :
    ((fun x ↦ e (p x)) ⁻¹' {z}).ncard = (p ⁻¹' {e.symm z}).ncard := by
  apply Set.ncard_congr'
  exact (Equiv.refl X).subtypeEquiv (fun x ↦ by
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      apply e.injective
      exact h.trans (e.apply_symm_apply z).symm
    · intro h
      have hp : p x = e.symm z := by simpa using h
      rw [hp]
      exact e.apply_symm_apply z)

/-- A map has two-point fibers if two open chart descriptions do. -/
theorem ncard_fiber_of_openCover {A B X Y : Type*}
    [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Y) (U V : Opens Y) (hcover : ∀ y, y ∈ U ∨ y ∈ V)
    (qA : A → Y) (kA : A ≃ₜ {x : X // p x ∈ U})
    (hkA : ∀ a, p (kA a).1 = qA a)
    (hcardA : ∀ y ∈ U, (qA ⁻¹' {y}).ncard = 2)
    (qB : B → Y) (kB : B ≃ₜ {x : X // p x ∈ V})
    (hkB : ∀ b, p (kB b).1 = qB b)
    (hcardB : ∀ y ∈ V, (qB ⁻¹' {y}).ncard = 2) :
    ∀ y, (p ⁻¹' {y}).ncard = 2 := by
  intro y
  rcases hcover y with hy | hy
  · exact (ncard_fiber_eq_of_homeomorph U kA hkA hy).trans (hcardA y hy)
  · exact (ncard_fiber_eq_of_homeomorph V kB hkB hy).trans (hcardB y hy)

end TauCeti.Covering
