/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Opposite
public import TauCeti.LinearAlgebra.Submodule.CompleteFiltration
public import TauCeti.RingTheory.FilteredAlgebra.Basic

/-!
# The opposite filtration

A decreasing filtration `F` of a semiring `A` by two-sided ideals is also a filtration of the
opposite semiring `Aᵐᵒᵖ`, the opposite filtration `TauCeti.AlgFiltration.op F`, given by the same
ideals. Right ideals of `A` are left ideals of `Aᵐᵒᵖ`, so right-sided statements about filtered
rings follow from left-sided ones through the opposite filtration.

## Main definitions

* `TauCeti.AlgFiltration.op F`: the filtration of `Aᵐᵒᵖ` given by the same ideals.

## Main results

* `TauCeti.AlgFiltration.isCompleteFiltration_op`: the opposite of a complete separated
  filtration is complete and separated.
-/

public section

open MulOpposite

namespace TauCeti.AlgFiltration

section Semiring

variable {A : Type*} [Semiring A] (F : AlgFiltration A)

/-- The filtration of the opposite semiring `Aᵐᵒᵖ` by the same two-sided ideals. -/
def op : AlgFiltration Aᵐᵒᵖ where
  ideal k :=
    { carrier := {x | x.unop ∈ F.ideal k}
      add_mem' := add_mem
      zero_mem' := zero_mem (F.ideal k)
      smul_mem' a x hx := F.mul_mem (b := 0) hx (by simp) }
  isTwoSided k := ⟨fun b hx => (F.ideal k).smul_mem b.unop hx⟩
  antitone _ _ h _ hx := F.antitone h hx
  ideal_zero := by
    ext
    simp
  mul_mem {a b} _ _ hx hy := by
    have h := F.mul_mem hy hx
    rw [Nat.add_comm b a] at h
    exact h

variable {F}

/-- An element of `Aᵐᵒᵖ` lies in the opposite filtration exactly when its image in `A` lies in
the filtration. -/
@[simp]
theorem mem_op_ideal {k : ℕ} {x : Aᵐᵒᵖ} : x ∈ F.op.ideal k ↔ x.unop ∈ F.ideal k :=
  (Iff.rfl)

end Semiring

variable {A : Type*} [Ring A] {F : AlgFiltration A}

/-- The opposite of a complete separated filtration is complete and separated. -/
theorem isCompleteFiltration_op (hF : IsCompleteFiltration F.ideal) :
    IsCompleteFiltration F.op.ideal where
  antitone := F.op.antitone
  eq_zero_of_forall_mem x hx := unop_injective (hF.eq_zero_of_forall_mem x.unop fun n => by
    simpa using hx n)
  exists_limit x hx := by
    obtain ⟨L, hL⟩ := hF.exists_limit (fun n => (x n).unop) fun n => by simpa using hx n
    exact ⟨MulOpposite.op L, fun n => by simpa using hL n⟩

end TauCeti.AlgFiltration
