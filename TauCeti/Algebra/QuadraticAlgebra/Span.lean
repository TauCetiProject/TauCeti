/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.LinearAlgebra.Span.Defs

/-!
# Spanning families of a quadratic algebra

A family of elements of a quadratic algebra over a nontrivial commutative semiring that spans it
cannot have all imaginary coordinates vanishing.
-/

public section

namespace QuadraticAlgebra

/-- A family of elements of a quadratic algebra over a nontrivial commutative semiring whose span
is everything has an element with nonvanishing imaginary coordinate. -/
theorem exists_im_ne_zero_of_span_range_eq_top {R ι : Type*} [CommSemiring R] [Nontrivial R]
    {c d : R} (a : ι → QuadraticAlgebra R c d)
    (hspan : Submodule.span R (Set.range a) = ⊤) : ∃ i, (a i).im ≠ 0 := by
  by_contra! hzero
  let S : Submodule R (QuadraticAlgebra R c d) :=
    { carrier := {x | x.im = 0}
      add_mem' := fun {x y} hx hy ↦ by simp_all
      zero_mem' := by simp
      smul_mem' := fun r x hx ↦ by simp_all }
  have hle : Submodule.span R (Set.range a) ≤ S :=
    Submodule.span_le.2 (Set.range_subset_iff.2 hzero)
  have hω : (omega : QuadraticAlgebra R c d) ∈ S := by
    apply hle
    rw [hspan]
    exact Submodule.mem_top
  have him : (omega : QuadraticAlgebra R c d).im = 0 := hω
  rw [im_omega] at him
  exact one_ne_zero him

end QuadraticAlgebra
