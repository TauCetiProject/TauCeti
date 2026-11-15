/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Solvable

/-!
# Uniqueness of lifts from perfect Lie algebras

Two morphisms from a perfect Lie algebra into a central extension are equal if their
projections are equal. Their difference takes values in the central kernel, so they agree
on brackets, which span the source. This gives the uniqueness part of universal central
extension constructions without imposing any condition on the map of kernels.
-/

public section

namespace LieHom

variable {R L E Q : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing E] [LieAlgebra R E] [LieRing Q] [LieAlgebra R Q]

/-- Morphisms from a perfect Lie algebra into a Lie algebra with a central projection kernel
are determined by their composites with that projection. Surjectivity of the projection is
not required. -/
theorem eq_of_comp_eq_of_ker_le_center (f g : L →ₗ⁅R⁆ E) (p : E →ₗ⁅R⁆ Q)
    (hL : LieAlgebra.derivedSeries R L 1 = ⊤)
    (hp : p.ker ≤ LieAlgebra.center R E) (h : p.comp f = p.comp g) : f = g := by
  have hd (x : L) : f x - g x ∈ LieAlgebra.center R E := by
    apply hp
    simp only [LieHom.mem_ker, map_sub, sub_eq_zero]
    exact DFunLike.congr_fun h x
  have hb (x y : L) : f ⁅x, y⁆ = g ⁅x, y⁆ := by
    have hx := (LieModule.mem_maxTrivSubmodule R E E _).mp (hd x) (f y)
    have hy := (LieModule.mem_maxTrivSubmodule R E E _).mp (hd y) (g x)
    rw [lie_sub, sub_eq_zero] at hx hy
    have hx' := congrArg Neg.neg hx
    simp only [lie_skew] at hx'
    simpa only [map_lie] using hx'.trans hy
  apply LieHom.ext
  intro x
  have hx : x ∈ Submodule.span R {⁅a, b⁆ | (a : L) (b : L)} := by
    rw [← LieAlgebra.coe_derivedSeries_one_eq, hL]
    simp
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, b, rfl⟩ := hx
    exact hb a b
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => simp [hx]

end LieHom
