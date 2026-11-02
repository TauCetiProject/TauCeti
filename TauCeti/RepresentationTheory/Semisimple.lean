/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RingTheory.Semisimple.Trace

/-!
# Semisimple representations are determined by their characters

Over a field of characteristic zero, two finite-dimensional semisimple representations of a monoid
with the same character are equivalent
(`Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation`). The monoid need
not be finite: for a finite group in characteristic zero every representation is semisimple by
Maschke's theorem, but the statement here is what applies to an infinite group such as `GL n ℂ`,
once complete reducibility is known by other means.

The character determines the trace of every element `a = ∑ a_g g` of the monoid algebra `k[G]`
acting on the representation, namely `∑ a_g χ(g)`. So the `k[G]`-modules of the two
representations are semisimple with equal trace functions, and
`IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq` identifies them.

## Main results

* `Representation.trace_asAlgebraHom_eq_of_character_eq`: representations with the same character
  have the same trace function on `k[G]`.
* `Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation`: **semisimple
  representations with the same character are equivalent.**

## References

* S. Lang, *Algebra*, revised third edition, Chapter XVII, Corollary 3.8.
-/

public section

open scoped MonoidAlgebra

namespace Representation

variable {k G V W : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- **The character determines the trace on the monoid algebra.** If two representations have the
same character, then every element of `k[G]` acts on them with the same trace. -/
theorem trace_asAlgebraHom_eq_of_character_eq {ρ : Representation k G V}
    {σ : Representation k G W} (h : ρ.character = σ.character) (a : k[G]) :
    LinearMap.trace k V (ρ.asAlgebraHom a) = LinearMap.trace k W (σ.asAlgebraHom a) := by
  have hlin : (LinearMap.trace k V).comp ρ.asAlgebraHom.toLinearMap =
      (LinearMap.trace k W).comp σ.asAlgebraHom.toLinearMap :=
    MonoidAlgebra.lhom_ext' fun g => LinearMap.ext_ring <| by
      simpa [character] using congrFun h g
  exact LinearMap.congr_fun hlin a

/-- **Semisimple representations are determined by their characters.** Over a field of
characteristic zero, two finite-dimensional semisimple representations of a monoid with the same
character are equivalent. The monoid need not be finite. -/
theorem nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation [CharZero k]
    [FiniteDimensional k V] [FiniteDimensional k W] (ρ : Representation k G V)
    (σ : Representation k G W) [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (h : ρ.character = σ.character) : Nonempty (ρ.Equiv σ) := by
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp ‹_›
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mp ‹_›
  refine TauCeti.Representation.nonempty_equiv_iff.mpr <|
    IsSemisimpleModule.nonempty_linearEquiv_of_trace_eq (k := k) _ _ fun a => ?_
  rw [← LinearMap.trace_conj' _ ρ.asModuleEquiv, ← LinearMap.trace_conj' _ σ.asModuleEquiv]
  exact trace_asAlgebraHom_eq_of_character_eq h a

end Representation
