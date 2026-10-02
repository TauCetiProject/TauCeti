/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import TauCeti.RepresentationTheory.Quiver.OneLoop.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Basic

/-!
# The path algebra of the one-loop quiver

This file identifies the path algebra of the quiver `TauCeti.Quiver.OneLoop` with one vertex and
one loop with the additive monoid algebra on `ℕ`, equivalently the polynomial algebra in one
variable. It also shows that this path algebra is not a finite module over any nontrivial
semiring; over a division ring, it is infinite-dimensional.

## Main declarations

* `TauCeti.PathAlgebra.oneLoopAlgEquiv`: its path algebra is `AddMonoidAlgebra k ℕ`, sending a
  path to the monomial of degree its length (`TauCeti.PathAlgebra.oneLoopAlgEquiv_single`).
* `TauCeti.not_module_finite_pathAlgebra_oneLoop`: the one-loop path algebra is not a finite
  module.
-/

public section

namespace TauCeti

open _root_.Quiver

universe w

namespace Quiver

namespace OneLoop

private def pathOfLength : ℕ → _root_.Quiver.Path (vertex : OneLoop) vertex
  | 0 => .nil
  | n + 1 => (pathOfLength n).cons loop

@[simp]
private theorem length_pathOfLength (n : ℕ) : (pathOfLength n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [pathOfLength, ih]

/-- Paths in the one-loop quiver are classified by their length. -/
private def totalPathEquivNat : Quiver.TotalPath OneLoop ≃ ℕ where
  toFun x := x.2.2.length
  invFun n := ⟨vertex, vertex, pathOfLength n⟩
  left_inv := by
    rintro ⟨a, b, p⟩
    induction p with
    | nil => cases a; rfl
    | @cons b c p e ih =>
      cases a; cases b; cases c
      simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at ih
      simp [pathOfLength, ih, eq_iff_true_of_subsingleton]
  right_inv := length_pathOfLength

end OneLoop

end Quiver

namespace PathAlgebra

variable (k : Type w) [CommSemiring k]

private noncomputable def oneLoopLinearEquiv :
    pathAlgebra k Quiver.OneLoop ≃ₗ[k] AddMonoidAlgebra k ℕ :=
  ((pathAlgebraBasis k Quiver.OneLoop).repr.trans
      (Finsupp.domLCongr Quiver.OneLoop.totalPathEquivNat)).trans
    (AddMonoidAlgebra.coeffLinearEquiv k).symm

private theorem oneLoopLinearEquiv_single (x : Quiver.TotalPath Quiver.OneLoop) (c : k) :
    oneLoopLinearEquiv k (single x c) = AddMonoidAlgebra.single x.2.2.length c := by
  simp [oneLoopLinearEquiv, Quiver.OneLoop.totalPathEquivNat]

private theorem oneLoopLinearEquiv_map_one :
    oneLoopLinearEquiv k (1 : pathAlgebra k Quiver.OneLoop) = 1 := by
  rw [one_def]
  simp [vertexIdempotent_eq_single, oneLoopLinearEquiv_single, ← AddMonoidAlgebra.one_def]

private theorem oneLoopLinearEquiv_map_mul (f g : pathAlgebra k Quiver.OneLoop) :
    oneLoopLinearEquiv k (f * g) = oneLoopLinearEquiv k f * oneLoopLinearEquiv k g := by
  induction f using induction_linear with
  | zero => simp
  | add f₁ f₂ ih₁ ih₂ => simp [ih₁, ih₂, add_mul]
  | single x a =>
    induction g using induction_linear with
    | zero => simp
    | add g₁ g₂ ih₁ ih₂ => simp [ih₁, ih₂, mul_add]
    | single y b =>
      obtain ⟨⟨⟩, ⟨⟩, p⟩ := x
      obtain ⟨⟨⟩, ⟨⟩, q⟩ := y
      simp [oneLoopLinearEquiv_single, _root_.Quiver.Path.length_comp, Nat.add_comm]

/-- The path algebra of the quiver with one vertex and one loop is the additive monoid algebra on
`ℕ` (equivalently, the polynomial algebra in one variable). -/
noncomputable def oneLoopAlgEquiv :
    pathAlgebra k Quiver.OneLoop ≃ₐ[k] AddMonoidAlgebra k ℕ :=
  AlgEquiv.ofLinearEquiv (oneLoopLinearEquiv k) (oneLoopLinearEquiv_map_one k)
    (oneLoopLinearEquiv_map_mul k)

/-- The isomorphism `oneLoopAlgEquiv` sends a path with coefficient `c` to the monomial of degree
its length with coefficient `c`. -/
@[simp]
theorem oneLoopAlgEquiv_single (x : Quiver.TotalPath Quiver.OneLoop) (c : k) :
    oneLoopAlgEquiv k (single x c) = AddMonoidAlgebra.single x.2.2.length c := by
  simp [oneLoopAlgEquiv, oneLoopLinearEquiv_single]

end PathAlgebra

/-- Over a nontrivial semiring, the path algebra of the one-loop quiver is not a finite module;
over a division ring this says it is infinite-dimensional. -/
theorem not_module_finite_pathAlgebra_oneLoop (k : Type w) [Semiring k] [Nontrivial k] :
    ¬ Module.Finite k (pathAlgebra k Quiver.OneLoop) := by
  rw [module_finite_pathAlgebra_iff, not_finite_iff_infinite,
    Quiver.OneLoop.totalPathEquivNat.infinite_iff]
  infer_instance

end TauCeti

end
