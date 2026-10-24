/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Orthogonal.Pi

/-!
# Coordinate powers of integral lattices

For an integral lattice `L` in `V` and a finite type `ι`, the coordinate power `L^ι` is the
orthogonal sum of `ι` copies of `L`: its carrier consists of the functions `ι → V` all of whose
values lie in `L`, and its form is the sum of the coordinate pairings,

```text
B(x, y) = ∑ i, L(x i, y i).
```

It is the orthogonal sum `TauCeti.IntegralLattice.pi` of the constant family at `L`, and is
reducible to it, so the carrier, form, norm, nondegeneracy and evenness lemmas for `pi` apply
directly.

This is the lattice-level counterpart of the coordinate powers of finite bilinear and quadratic
modules: codes over the discriminant alphabet of `L` are glue subgroups for `L^ι`, as in the
constructions of lattices from copies of `A₂` or `D₄`. The coordinate power is
nondegenerate when `L` is, and even exactly when `L` is (for nonempty `ι`).

## Main declarations

* `TauCeti.IntegralLattice.coordinatePower`: the coordinate power lattice.
* `TauCeti.IntegralLattice.nondegenerate_coordinatePower_iff`: nondegeneracy is inherited from
  and, for nonempty `ι`, detected by the factor.
* `TauCeti.IntegralLattice.isEven_coordinatePower_iff`: the same for evenness.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §3.
* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} [AddCommGroup V] [Module ℚ V]
variable (L : IntegralLattice V) (ι : Type v) [Fintype ι]

/-- The coordinate power `L^ι` of an integral lattice: the orthogonal sum of `ι` copies of `L`,
with carrier the functions `ι → V` whose values all lie in `L`.

Reducible, so that the API of the orthogonal sum `TauCeti.IntegralLattice.pi` applies to it. -/
abbrev coordinatePower : IntegralLattice (ι → V) :=
  pi fun _ : ι ↦ L

/-- The coordinate-power form is nondegenerate when the factor form is, and conversely when the
index type is nonempty. -/
theorem nondegenerate_coordinatePower_iff [Nonempty ι] :
    (L.coordinatePower ι).form.Nondegenerate ↔ L.form.Nondegenerate :=
  (nondegenerate_pi_iff _).trans (forall_const ι)

/-- A coordinate power of an even lattice is even. -/
theorem IsEven.coordinatePower {L : IntegralLattice V} (hL : L.IsEven) :
    (L.coordinatePower ι).IsEven :=
  isEven_pi fun _ ↦ hL

/-- A coordinate power over a nonempty index type is even exactly when the factor is even. -/
theorem isEven_coordinatePower_iff [Nonempty ι] :
    (L.coordinatePower ι).IsEven ↔ L.IsEven :=
  (isEven_pi_iff _).trans (forall_const ι)

end TauCeti.IntegralLattice
