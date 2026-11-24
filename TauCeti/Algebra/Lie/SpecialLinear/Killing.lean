/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.TraceForm

import TauCeti.Algebra.Lie.GeneralLinear.Finrank
import TauCeti.Algebra.Lie.GeneralLinear.Killing
import TauCeti.LinearAlgebra.Trace.Exact

/-!
# The Killing form of the special linear Lie algebra

The Killing form of `sl n R` is

`κ(X, Y) = 2 n trace (X * Y)`,

where `n` is the cardinality of the index type, over every commutative ring `R`.

When `n` is empty, `sl n R` is trivial and both sides vanish. When `n` is nonempty,
`0 → sl n R → gl n R --trace--> R → 0` is a short exact sequence of finite free `R`-modules
whose outer maps commute with `ad X ∘ ad Y` on `sl n R`, `ad X ∘ ad Y` on `gl n R`, and `0` on
`R` (since commutators are trace-free). Additivity of the trace along this short exact sequence
(`LinearMap.trace_eq_add_of_exact`) reduces `killingForm R (sl n R)` to `Matrix.killingForm_apply`,
where the trace-squared term vanishes on trace-free matrices.

## Main results

* `LieAlgebra.SpecialLinear.killingForm_apply`: `κ(X, Y) = 2 n trace (X * Y)` on `sl n R`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§1.2 and 5.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter I (the Killing forms of the classical Lie algebras).
-/

public section

namespace LieAlgebra.SpecialLinear

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- **The Killing form of `sl n R`**: `κ(X, Y) = 2 n trace (X * Y)`, over any commutative
ring `R`. -/
theorem killingForm_apply (X Y : sl n R) :
    killingForm R (sl n R) X Y =
      2 * Fintype.card n * ((X : Matrix n n R) * (Y : Matrix n n R)).trace := by
  rcases isEmpty_or_nonempty n with hn | ⟨⟨i₀⟩⟩
  · have := hn
    have hX : X = 0 := Subtype.ext (Subsingleton.elim _ _)
    simp [hX]
  · let i : sl n R →ₗ[R] Matrix n n R := (sl n R).incl.toLinearMap
    let π : Matrix n n R →ₗ[R] R := Matrix.traceLinearMap n R R
    have htrace_exact : Function.Exact i π := fun M ↦
      ⟨fun hM ↦ ⟨⟨M, mem_sl_iff.mpr hM⟩, rfl⟩,
       fun ⟨X, hX⟩ ↦ hX ▸ mem_sl_iff.mp X.property⟩
    have htrace_add := LinearMap.trace_eq_add_of_exact
      (i := i) (π := π)
      Subtype.val_injective
      (fun r ↦ ⟨Matrix.single i₀ i₀ r, by simp [π]⟩)
      htrace_exact
      (f := ad R (Matrix n n R) X ∘ₗ ad R (Matrix n n R) Y)
      (fN := ad R (sl n R) X ∘ₗ ad R (sl n R) Y)
      (fQ := 0)
      (by
        dsimp only [i]
        rw [LinearMap.comp_assoc, (sl n R).ad_comp_incl_eq Y, ← LinearMap.comp_assoc,
          (sl n R).ad_comp_incl_eq X, LinearMap.comp_assoc])
      (by
        ext M
        simp [π, LieAlgebra.matrix_trace_commutator_zero])
    rw [map_zero, add_zero, ← killingForm_apply_apply, ← killingForm_apply_apply] at htrace_add
    rw [← htrace_add, Matrix.killingForm_apply, mem_sl_iff.mp X.property,
      mem_sl_iff.mp Y.property]
    ring

end LieAlgebra.SpecialLinear
