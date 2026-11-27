/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.AsModule
public import TauCeti.RepresentationTheory.Charpoly
public import TauCeti.RingTheory.Semisimple.Charpoly

/-!
# The Brauer–Nesbitt theorem for representations

Over an algebraically closed field of any characteristic, two finite-dimensional semisimple
representations of a monoid `G` with the same characteristic polynomial at every `g ∈ G` are
equivalent (`Representation.nonempty_equiv_of_charpoly_eq_of_isSemisimpleRepresentation`). This is
`IsSemisimpleModule.nonempty_linearEquiv_of_charpoly_eq` for the `k[G]`-modules of the
representations, which `G` spans. The continuous version is in
`TauCeti.RepresentationTheory.Continuous.BrauerNesbitt`.

In characteristic zero the characters already determine semisimple representations
(`Representation.nonempty_equiv_of_character_eq_of_isSemisimpleRepresentation`). In characteristic
`p` they do not: over `𝔽₃` three copies of the trivial representation of `ℤ/2` and three copies of
its sign representation have equal characters, but the characteristic polynomials `(X - 1) ^ 3`
and `(X + 1) ^ 3` of the generator differ. Semisimplicity cannot be dropped: over `𝔽₂`, `ℤ/2`
acting trivially on `𝔽₂²` and by `!![1, 1; 0, 1]` has characteristic polynomial `(X - 1) ^ 2` at
every element, but only the first is semisimple.

## Main results

* `Representation.nonempty_equiv_of_charpoly_eq_of_isSemisimpleRepresentation`: **Brauer–Nesbitt.**

## References

* H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, Proposition 2.6.
* C. W. Curtis and I. Reiner, *Representation theory of finite groups and associative algebras*,
  Theorem 30.16.
-/

public section

open scoped MonoidAlgebra

namespace Representation

variable {k G V W : Type*} [Field k] [IsAlgClosed k] [Monoid G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- **Brauer–Nesbitt.** Over an algebraically closed field of any characteristic, two
finite-dimensional semisimple representations of a monoid with the same characteristic polynomial
at every element are equivalent. -/
theorem nonempty_equiv_of_charpoly_eq_of_isSemisimpleRepresentation (ρ : Representation k G V)
    (σ : Representation k G W) [ρ.IsSemisimpleRepresentation] [σ.IsSemisimpleRepresentation]
    (h : ∀ g, (ρ g).charpoly = (σ g).charpoly) : Nonempty (ρ.Equiv σ) := by
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp ‹_›
  have := (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule σ).mp ‹_›
  refine TauCeti.Representation.nonempty_equiv_iff.mpr <|
    IsSemisimpleModule.nonempty_linearEquiv_of_charpoly_eq (k := k) (g := MonoidAlgebra.of k G)
      (by
        have hrange : Set.range (MonoidAlgebra.of k G) = Set.range (MonoidAlgebra.basis G k) := by
          ext
          simp [MonoidAlgebra.basis_apply]
        rw [hrange, Module.Basis.span_eq]) fun g => ?_
  rw [charpoly_lsmul_asModule_of, charpoly_lsmul_asModule_of, h g]

end Representation
