/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Toric.Algebraic.Lattice.Basic

/-!
# The integral dual lattice

The real extensions of integral characters form an actual integral lattice in the real dual
space: `TauCeti.Toric.IsIntegralLattice.realCharacter` is the lattice map of the dual. Evaluation
at a lattice vector `i n` is then the real extension, for the dual lattice, of integral evaluation
at `n`. This is the double-dual compatibility used to pass between a cone and its dual cone in
lattice terms.

## Attribution

Adapted from `Mei/Geometry/Toric/Algebraic/DualLattice.lean` in Mei at commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca`, keeping only the algebraic dual. Original copyright
and author credit are retained.

Source: https://github.com/yuma-mizuno-lean/Mei/blob/3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca/Mei/Geometry/Toric/Algebraic/DualLattice.lean
-/

public section

namespace TauCeti.Toric.IsIntegralLattice

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}

/-- The real extensions of integral characters form an integral lattice in the real dual space. -/
theorem dual (h : IsIntegralLattice i) : IsIntegralLattice h.realCharacter := by
  let _ := h.free
  let _ := h.finite
  have hd : IsIntegralLattice h.isBaseChange.toDual.toAddMonoidHom :=
    ⟨inferInstance, inferInstance, h.isBaseChange.dual⟩
  exact (isIntegralLattice_congr (addMonoidHomLequivInt ℤ).symm.toAddEquiv
    (LinearEquiv.refl ℝ _) fun φ => h.eq_realCharacter fun n => by
      simpa using h.isBaseChange.toDual_comp_apply φ n).mp hd

/-- Under the dual lattice, integral evaluation at `n` extends to real evaluation at `i n`. -/
@[simp]
theorem dual_realCharacter_eval (h : IsIntegralLattice i) (n : N) :
    h.dual.realCharacter (AddMonoidHom.eval n) = Module.Dual.eval ℝ V (i n) := by
  symm
  apply h.dual.eq_realCharacter
  intro m
  simp

end TauCeti.Toric.IsIntegralLattice
