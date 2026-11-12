/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Jacobson.Basic
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.FiniteType

/-!
# The Jacobson radical of a module-finite algebra

Let `A` be an algebra over a commutative ring `R`, finitely generated as an `R`-module; `A` need not
be commutative. The image of the Jacobson radical of `R` lies in the Jacobson radical of `A`: for
`r` in the radical of `R` and any `y : A`, left multiplication by `1 + y r` is an `R`-linear
endomorphism of `A` that is the identity modulo `r A`, so it is surjective by Nakayama's lemma, and
then bijective, a surjective endomorphism of a finite module over a commutative ring being
injective. Hence `1 + y r` is a unit.

## Main results

* `TauCeti.Ring.algebraMap_mem_jacobson`: the image of an element of the Jacobson radical of `R`
  lies in the Jacobson radical of a module-finite `R`-algebra.

## References

* T. Y. Lam, *A First Course in Noncommutative Rings*, 2nd ed., GTM 131, Springer (2001),
  Corollary (5.9).
-/

public section

namespace TauCeti

namespace Ring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [Module.Finite R A]

/-- **The radical of the base lies in the radical of a module-finite algebra.** If `A` is an
`R`-algebra that is finitely generated as an `R`-module and `r` lies in the Jacobson radical of `R`,
then `algebraMap R A r` lies in the Jacobson radical of `A`. -/
theorem algebraMap_mem_jacobson {r : R} (hr : r ∈ Ring.jacobson R) :
    algebraMap R A r ∈ Ring.jacobson A := by
  refine mem_jacobson_iff_isUnit_one_add_mul_left.mpr fun y ↦ ?_
  set u := 1 + y * algebraMap R A r
  -- Left multiplication by `u` is surjective by Nakayama's lemma, since `a = u a - r • (y a)`.
  have hsurj : Function.Surjective (Algebra.lmul R A u) := by
    rw [← LinearMap.range_eq_top, eq_top_iff]
    refine Submodule.le_of_le_smul_of_le_jacobson (I := Ideal.span {r}) Module.Finite.fg_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hr) fun a _ ↦ ?_
    have ha : a = Algebra.lmul R A u a - r • (y * a) := by
      simp [u, mul_assoc, Algebra.smul_def, Algebra.left_comm]
    rw [ha]
    exact Submodule.sub_mem_sup (LinearMap.mem_range_self _ a)
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self r) Submodule.mem_top)
  -- A surjective endomorphism of a finite module over a commutative ring is bijective.
  have hbij : Function.Bijective (Algebra.lmul R A u) :=
    ⟨OrzechProperty.injective_of_surjective_endomorphism _ hsurj, hsurj⟩
  exact Algebra.lmul_isUnit_iff.mp ((Module.End.isUnit_iff _).mpr hbij)

end Ring

end TauCeti
