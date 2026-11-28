/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
import Mathlib.RingTheory.Ideal.Nonunits
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Unit values of a monic polynomial over a ring with finitely many maximal ideals

Let `A` be a commutative ring with finitely many maximal ideals, for instance a finite product of
fields, and `f : E →+* A` a ring homomorphism from a field. A monic polynomial `p` over `A` takes a
unit value `p (f x)` at all but finitely many `x ∈ E`
(`Polynomial.Monic.finite_setOf_not_isUnit_eval`). Indeed an element of `A` is a unit exactly
when it lies in no maximal ideal `𝔪`, and modulo each `𝔪` the polynomial `p` stays monic, hence
has finitely many roots in the field `A ⧸ 𝔪`, while `E → A ⧸ 𝔪` is injective.

Applied to a characteristic polynomial, this says that a square matrix `M` over `A` has
`f x • 1 + M` invertible for all but finitely many `x ∈ E`. This is what lets a scalar translate
move any element of a unitary group into the domain of its Cayley transform
(`Matrix.mem_closure_range_map_unitaryGroupOf`).
-/

public section

namespace Polynomial

/-- **A monic polynomial over a ring with finitely many maximal ideals takes unit values at all
but finitely many points of a field.** For a ring homomorphism `f : E →+* A` from a field, the
`x ∈ E` with `p (f x)` not a unit form a finite set. -/
theorem Monic.finite_setOf_not_isUnit_eval {E A : Type*} [Field E] [CommRing A]
    [Finite (MaximalSpectrum A)] {p : A[X]} (hp : p.Monic) (f : E →+* A) :
    {x : E | ¬IsUnit (p.eval (f x))}.Finite := by
  -- A non-unit value lies in a maximal ideal, where `x` is a root of `p` read modulo that ideal.
  have hsub : {x : E | ¬IsUnit (p.eval (f x))} ⊆ ⋃ 𝔪 : MaximalSpectrum A,
      ((Ideal.Quotient.mk 𝔪.asIdeal).comp f) ⁻¹'
        {y | (p.map (Ideal.Quotient.mk 𝔪.asIdeal)).IsRoot y} := by
    intro x hx
    obtain ⟨I, hI, hxI⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hx)
    exact Set.mem_iUnion.2 ⟨⟨I, hI⟩, by
      simpa [IsRoot, eval_map_apply, Ideal.Quotient.eq_zero_iff_mem] using hxI⟩
  refine (Set.finite_iUnion fun 𝔪 : MaximalSpectrum A ↦ ?_).subset hsub
  -- Modulo a maximal ideal `p` is a monic polynomial over a field, with finitely many roots.
  have := 𝔪.isMaximal
  let := Ideal.Quotient.field 𝔪.asIdeal
  exact (finite_setOfPred_isRoot ((hp.map _).ne_zero)).preimage
    ((Ideal.Quotient.mk 𝔪.asIdeal).comp f).injective.injOn

end Polynomial
