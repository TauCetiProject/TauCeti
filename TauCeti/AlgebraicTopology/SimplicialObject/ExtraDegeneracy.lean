/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import TauCeti.Algebra.Homology.ModuleCat.QuasiIso
public import TauCeti.AlgebraicTopology.DoldKan.ModuleCat

/-!
# Module homology of a simplicial augmentation with an extra degeneracy on sets

An extra degeneracy on the underlying sets of an augmented simplicial module suffices for
its alternating face complex to resolve the augmentation module. In positive degrees,
the Dold–Kan projector reduces the proof to cycles with every face zero. Applying the
extra degeneracy to such a cycle and subtracting its value at zero produces a primitive.
The extra degeneracy itself is not assumed to be linear.

This uses Mathlib's `AlternatingFaceMapComplex.ε` and `DoldKan.PInfty`. The standard
polynomial resolution of the Stacks Project, Tags 08PM and 08QI, is an application.
-/

public section

open CategoryTheory Opposite Simplicial AlgebraicTopology AlgebraicTopology.DoldKan

namespace CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy

universe u

variable {R : Type*} [Ring R] {X : Augmented (ModuleCat.{u} R)}

variable (ed : ExtraDegeneracy
  (((Augmented.whiskering _ _).obj (forget (ModuleCat R))).obj X))

include ed

private theorem exists_d_one_zero_eq_of_augmentation_eq_zero {x : X.left _⦋0⦌}
    (hx : X.hom.app (op ⦋0⦌) x = 0) :
    ∃ y : X.left _⦋1⦌, (AlternatingFaceMapComplex.obj X.left).d 1 0 y = x := by
  let s : X.left _⦋0⦌ → X.left _⦋1⦌ := ed.s 0
  let t : X.right → X.left _⦋0⦌ := ed.s'
  let y := s x - s 0
  have h₀ (z : X.left _⦋0⦌) : X.left.δ 0 (s z) = z := congr($(ed.s_comp_δ₀ 0) z)
  have h₁ (z : X.left _⦋0⦌) :
      X.left.δ 1 (s z) = t (X.hom.app (op ⦋0⦌) z) := congr($(ed.s₀_comp_δ₁) z)
  refine ⟨y, (X.left.alternatingFaceMapComplex_d_apply_of_δ_succ_eq_zero ?_).trans ?_⟩
  · intro i
    have hi : i = 0 := Fin.eq_zero i
    simp [y, hi, h₁, hx]
  · simp [y, h₀]

private theorem exists_d_succ_eq_of_faces_eq_zero {n : ℕ} {x : X.left _⦋n + 1⦌}
    (hx : ∀ i : Fin (n + 2), X.left.δ i x = 0) :
    ∃ y : X.left _⦋n + 2⦌, (AlternatingFaceMapComplex.obj X.left).d (n + 2) (n + 1) y = x := by
  let s : X.left _⦋n + 1⦌ → X.left _⦋n + 2⦌ := ed.s (n + 1)
  let t : X.left _⦋n⦌ → X.left _⦋n + 1⦌ := ed.s n
  let y := s x - s 0
  have h₀ (z : X.left _⦋n + 1⦌) : X.left.δ 0 (s z) = z :=
    congr($(ed.s_comp_δ₀ (n + 1)) z)
  have h (i : Fin (n + 2)) (z : X.left _⦋n + 1⦌) :
      X.left.δ i.succ (s z) = t (X.left.δ i z) := congr($(ed.s_comp_δ n i) z)
  refine ⟨y, (X.left.alternatingFaceMapComplex_d_apply_of_δ_succ_eq_zero ?_).trans ?_⟩
  · intro i
    simp [y, h, hx]
  · simp [y, h₀]

private theorem exactAt_succ (n : ℕ) : (AlternatingFaceMapComplex.obj X.left).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff_range_eq_ker _ (ChainComplex.prev ℕ (n + 1))
    (ChainComplex.next_nat_succ n)]
  refine le_antisymm (LinearMap.range_le_ker_iff.2 ?_) ?_
  · exact congr($((AlternatingFaceMapComplex.obj X.left).d_comp_d (n + 2) (n + 1) n).hom)
  · intro x hx
    have hx₀ : (AlternatingFaceMapComplex.obj X.left).d (n + 1) n x = 0 := hx
    let p := (PInfty (X := X.left)).f (n + 1) x
    have hp : ∀ i : Fin (n + 2), X.left.δ i p = 0 := by
      intro i
      cases i using Fin.cases with
      | zero =>
        rw [← X.left.alternatingFaceMapComplex_d_apply_of_δ_succ_eq_zero
          (X.left.δ_succ_PInfty_f_apply x), HomologicalComplex.Hom.comm_apply]
        rw [hx₀, map_zero]
      | succ i => exact X.left.δ_succ_PInfty_f_apply x i
    obtain ⟨y, hy⟩ := ed.exists_d_succ_eq_of_faces_eq_zero hp
    -- The homotopy changes the projected cycle back to the original cycle by a boundary.
    let H := homotopyPInftyToId X.left
    let z : (AlternatingFaceMapComplex.obj X.left).X (n + 2) := H.hom (n + 1) (n + 2) x
    have h := H.comm (n + 1)
    rw [dNext_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 1) n),
      prevD_eq _ (by simp : (ComplexShape.down ℕ).Rel (n + 2) (n + 1))] at h
    have he : p = (AlternatingFaceMapComplex.obj X.left).d (n + 2) (n + 1) z + x := by
      simpa only [ModuleCat.hom_add, LinearMap.add_apply, ModuleCat.comp_apply,
        hx₀, map_zero, zero_add, HomologicalComplex.id_f, ModuleCat.id_apply] using
        congr(($h).hom x)
    let y₀ : (AlternatingFaceMapComplex.obj X.left).X (n + 2) := y
    have hy₀ : (AlternatingFaceMapComplex.obj X.left).d (n + 2) (n + 1) y₀ = p := hy
    have hb : (AlternatingFaceMapComplex.obj X.left).d (n + 2) (n + 1) (y₀ - z) = x := by
      rw [map_sub, hy₀, he, add_sub_cancel_left]
    exact ⟨y₀ - z, hb⟩

/-- If the underlying augmented simplicial set admits an extra degeneracy, the augmentation of
its alternating face complex to the augmentation module in degree zero is a quasi-isomorphism. -/
theorem quasiIso_ε_of_forget : QuasiIso (AlternatingFaceMapComplex.ε.app X) := by
  rw [quasiIso_iff]
  intro n
  cases n with
  | zero =>
    rw [HomologicalComplex.moduleCat_quasiIsoAt_iff _ (ChainComplex.prev ℕ 0)
      ChainComplex.next_nat_zero]
    constructor
    · intro a _
      have h (z : X.right) : X.hom.app (op ⦋0⦌) (ed.s' z) = z := congr($(ed.s'_comp_ε) z)
      refine ⟨ed.s' a, ?_, 0, ?_⟩
      · rw [HomologicalComplex.shape _ 0 0 (by decide)]
        exact LinearMap.zero_apply _
      · simp [h]
    · intro x _ b hb
      apply ed.exists_d_one_zero_eq_of_augmentation_eq_zero
      rw [← AlternatingFaceMapComplex.ε_app_f_zero, ← hb]
      simp [HomologicalComplex.single_obj_d]
  | succ n =>
    exact (quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ n)).2
      (ed.exactAt_succ n)

end CategoryTheory.SimplicialObject.Augmented.ExtraDegeneracy
