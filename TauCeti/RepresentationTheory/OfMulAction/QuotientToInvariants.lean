/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.OfMulAction
public import TauCeti.RepresentationTheory.CharacterTable.FixedPointCount
import TauCeti.RepresentationTheory.Invariants

/-!
# Equivalent permutation representations descend to orbit spaces

Let a group `D` act on finite types `X` and `Y`, and let `I` be a normal subgroup of `D`. Then
`D ⧸ I` permutes the `I`-orbits of `X` and of `Y`. This file shows that an equivalence of the
permutation representations `k[X] ≃ k[Y]` of `D` induces an equivalence `k[X/I] ≃ k[Y/I]` of the
permutation representations of `D ⧸ I` on the orbit spaces.

The equivalence is the composite of three maps. The orbit sums identify `k[X/I]` with the
representation of `D ⧸ I` on the `I`-invariants of `k[X]` (`TauCeti.orbitSumEquiv`). An
equivalence of representations of `D` restricts to the `I`-invariants and is an equivalence of
the quotient representations there (`Representation.Equiv.quotientToInvariants`, built from the
restriction `Representation.Equiv.res`). Finally the orbit sums of `Y` identify the
`I`-invariants of `k[Y]` with `k[Y/I]`.

Over a field of characteristic zero, equivalent permutation representations have the same
fixed-point counts. So if `k[X]` and `k[Y]` are equivalent, every element of `D ⧸ I` fixes as
many `I`-orbits of `X` as of `Y`. For a finite group `D`, equivalence of the permutation
representations is equality of the fixed-point counts of every element of `D`, so the
statement becomes purely combinatorial: if every element of `D` fixes as many points of `X` as
of `Y`, then every element of `D ⧸ I` fixes as many `I`-orbits of `X` as of `Y`.

The motivating instance is the arithmetic of Gassmann triples. There `D` and `I` are the
decomposition and inertia groups of a prime in a Galois group `G`, and `X` and `Y` are the coset
spaces `G ⧸ H` and `G ⧸ K` of two almost conjugate subgroups. The cycles of a Frobenius element
on the `I`-orbits correspond to the primes above, and their lengths are the residue degrees.
The fixed-point counts of the powers of Frobenius on the `I`-orbits determine these cycle
lengths, so equal counts give the same residue degrees, counted with multiplicity.

## Main definitions

* `Representation.Equiv.ofMulActionOrbitRelQuotient`: an equivalence of permutation
  representations of `D` induces one of the permutation representations of `D ⧸ I` on the
  `I`-orbits.

## Main results

* `Representation.Equiv.coeff_ofMulActionOrbitRelQuotient`: the coefficient of the induced
  equivalence at the orbit of `y` is the coefficient at `y` of the image of the corresponding
  orbit-constant vector.
* `TauCeti.natCard_fixedBy_orbitRelQuotient_eq_of_nonempty_equiv_ofMulAction`: in characteristic
  zero, equivalent permutation representations of `D` have orbit spaces with equal fixed-point
  counts under `D ⧸ I`.
* `TauCeti.natCard_fixedBy_orbitRelQuotient_eq`: for a finite group `D`, equal fixed-point counts
  on `X` and `Y` give equal fixed-point counts on the `I`-orbit spaces.

## References

* F. Gassmann, *Bemerkungen zur vorstehenden Arbeit von Hurwitz*, Math. Z. **25** (1926),
  665–675.
* R. Perlis, *On the equation `ζ_K(s) = ζ_K'(s)`*, J. Number Theory **9** (1977), 342–360.
-/

public section

open MulAction Representation

namespace Representation.Equiv

variable {k D X Y : Type*} [CommRing k] [Group D] [MulAction D X] [MulAction D Y]
  [Finite X] [Finite Y]

/-- **Equivalent permutation representations descend to orbit spaces.** For a normal subgroup `I`
of `D`, an equivalence `k[X] ≃ k[Y]` of permutation representations of `D` induces an equivalence
`k[X/I] ≃ k[Y/I]` of the permutation representations of `D ⧸ I` on the `I`-orbits. It sends a
function on the `I`-orbits of `X` to the orbit-constant vector of `k[X]` it defines, applies the
given equivalence, and reads the resulting `I`-invariant vector of `k[Y]` as a function on the
`I`-orbits of `Y`. -/
noncomputable def ofMulActionOrbitRelQuotient (e : (ofMulAction k D X).Equiv (ofMulAction k D Y))
    (I : Subgroup D) [I.Normal] :
    (ofMulAction k (D ⧸ I) (orbitRel.Quotient I X)).Equiv
      (ofMulAction k (D ⧸ I) (orbitRel.Quotient I Y)) :=
  (TauCeti.orbitSumEquiv k X I).trans
    ((e.quotientToInvariants I).trans (TauCeti.orbitSumEquiv k Y I).symm)

/-- The coefficient of `e.ofMulActionOrbitRelQuotient I v` at the orbit of `y` is the coefficient
at `y` of the image under `e` of the vector of `k[X]` whose coefficient at `x` is that of `v` at
the orbit of `x`. -/
@[simp]
theorem coeff_ofMulActionOrbitRelQuotient (e : (ofMulAction k D X).Equiv (ofMulAction k D Y))
    (I : Subgroup D) [I.Normal] (v : MonoidAlgebra k (orbitRel.Quotient I X)) (y : Y) :
    (e.ofMulActionOrbitRelQuotient I v).coeff ⟦y⟧ =
      (e (TauCeti.orbitSumEquiv k X I v : MonoidAlgebra k X)).coeff y := by
  simp [ofMulActionOrbitRelQuotient]

/-- The inverse of the induced equivalence is the one induced by the inverse. -/
@[simp]
theorem symm_ofMulActionOrbitRelQuotient (e : (ofMulAction k D X).Equiv (ofMulAction k D Y))
    (I : Subgroup D) [I.Normal] :
    (e.ofMulActionOrbitRelQuotient I).symm = e.symm.ofMulActionOrbitRelQuotient I := by
  refine Representation.Equiv.ext <| funext fun v ↦
    EquivLike.injective (e.ofMulActionOrbitRelQuotient I) ?_
  ext ω
  induction ω using Quotient.inductionOn with | h y => ?_
  rw [apply_symm_apply, coeff_ofMulActionOrbitRelQuotient]
  simp [ofMulActionOrbitRelQuotient]

end Representation.Equiv

namespace TauCeti

universe u

variable {D : Type*} {X Y : Type u} [Group D] [MulAction D X] [MulAction D Y] [Finite X] [Finite Y]

/-- **Fixed orbits of equivalent permutation representations.** Over a field `k` of
characteristic zero, if the permutation representations `k[X]` and `k[Y]` of `D` are equivalent,
then for every normal subgroup `I` each element of `D ⧸ I` fixes as many `I`-orbits of `X` as of
`Y`. -/
theorem natCard_fixedBy_orbitRelQuotient_eq_of_nonempty_equiv_ofMulAction (k : Type*) [Field k]
    [CharZero k] (h : Nonempty ((ofMulAction k D X).Equiv (ofMulAction k D Y)))
    (I : Subgroup D) [I.Normal] (d : D ⧸ I) :
    Nat.card (fixedBy (orbitRel.Quotient I X) d) = Nat.card (fixedBy (orbitRel.Quotient I Y) d) :=
  natCard_fixedBy_eq_of_nonempty_equiv_ofMulAction k (h.map (·.ofMulActionOrbitRelQuotient I)) d

/-- **Equal fixed-point counts pass to orbit spaces.** For a finite group `D` acting on finite
types `X` and `Y` such that every element of `D` fixes as many points of `X` as of `Y`, and for a
normal subgroup `I` of `D`, every element of `D ⧸ I` fixes as many `I`-orbits of `X` as of `Y`. -/
theorem natCard_fixedBy_orbitRelQuotient_eq [Finite D]
    (h : ∀ d : D, Nat.card (fixedBy X d) = Nat.card (fixedBy Y d)) (I : Subgroup D) [I.Normal]
    (d : D ⧸ I) :
    Nat.card (fixedBy (orbitRel.Quotient I X) d) = Nat.card (fixedBy (orbitRel.Quotient I Y) d) :=
  natCard_fixedBy_orbitRelQuotient_eq_of_nonempty_equiv_ofMulAction ℚ
    ((nonempty_equiv_ofMulAction_iff_forall_natCard_fixedBy_eq ℚ).2 h) I d

end TauCeti
