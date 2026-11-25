/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# Lifting properties and limits of towers

Let `⋯ ⟶ X 2 ⟶ X 1 ⟶ X 0` be a tower given by morphisms `p n : X (n + 1) ⟶ X n`, and let `c` be a
limit cone of the functor `Functor.ofOpSequence p : ℕᵒᵖ ⥤ C`. If a morphism `i` has the left
lifting property with respect to every `p n`, then it has the left lifting property with respect
to the projection `c.π.app (op 0) : c.pt ⟶ X 0`
(`CategoryTheory.hasLiftingProperty_π_app_zero_of_isLimit`). The lifts are built one level of the
tower at a time and assembled by the limit.

This is the dual of the stability of left lifting properties under transfinite compositions. In a
model category it says that the limit of a tower of fibrations is a fibration over the bottom of
the tower; in particular a limit of a tower of fibrations between fibrant objects is fibrant.
-/

public section

namespace CategoryTheory

open Limits Opposite

variable {C : Type*} [Category* C] {A B : C} (i : A ⟶ B) {X : ℕ → C} (p : ∀ n, X (n + 1) ⟶ X n)

/-- **Lifting properties pass to limits of towers.** If `i` has the left lifting property with
respect to every morphism `p n : X (n + 1) ⟶ X n` of a tower, then it has the left lifting property
with respect to the projection from a limit of the tower to its bottom `X 0`. -/
theorem hasLiftingProperty_π_app_zero_of_isLimit [∀ n, HasLiftingProperty i (p n)]
    {c : Cone (Functor.ofOpSequence p)} (hc : IsLimit c) :
    HasLiftingProperty i (c.π.app (op 0)) where
  sq_hasLift {t b} sq := by
    -- the legs of the cone, as morphisms to the terms of the tower, are compatible with the
    -- transitions
    let π (n : ℕ) : c.pt ⟶ X n := c.π.app (op n)
    have hπ (n : ℕ) : π (n + 1) ≫ p n = π n := by
      have h := c.w (homOfLE (Nat.le_add_right n 1)).op
      rw [Functor.ofOpSequence_map_homOfLE_succ] at h
      exact h
    -- lifts `B ⟶ X n` of the square, built by induction on `n` using the lifting property
    -- of `p n`
    let l : (n : ℕ) → {l : B ⟶ X n // i ≫ l = t ≫ π n} := fun n ↦ by
      induction n with
      | zero => exact ⟨b, sq.w.symm⟩
      | succ n l =>
        have sq' : CommSq (t ≫ π (n + 1)) i (p n) l.val :=
          ⟨by rw [Category.assoc, hπ, l.property]⟩
        exact ⟨sq'.lift, sq'.fac_left⟩
    have hl (n : ℕ) : (l (n + 1)).val ≫ p n = (l n).val := CommSq.fac_right _
    let s : Cone (Functor.ofOpSequence p) :=
      ⟨B, NatTrans.ofOpSequence (F := (Functor.const _).obj B) (fun n ↦ (l n).val)
        fun n ↦ by
          rw [Functor.ofOpSequence_map_homOfLE_succ]
          exact (Category.id_comp _).trans (hl n).symm⟩
    exact ⟨⟨{
      l := hc.lift s
      fac_left := hc.hom_ext fun n ↦ by
        rw [Category.assoc, hc.fac]
        exact (l n.unop).property
      fac_right := hc.fac s (op 0) }⟩⟩

end CategoryTheory
