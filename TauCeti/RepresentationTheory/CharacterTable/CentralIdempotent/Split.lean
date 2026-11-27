/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.CharacterTable.IdempotentDecomposition
import Mathlib.RingTheory.AlgebraTower
import TauCeti.Algebra.MonoidAlgebra.Basic

/-!
# Primitive central idempotents of absolutely irreducible characters over any field

For a representation `ρ` of a finite group `G` over any field `k`, with character `χ`, the element

`e_χ = (χ(1) / |G|) ∑_g χ(g⁻¹) g`

of `k[G]` is `TauCeti.Representation.primitiveCentralIdempotent ρ`. It is compatible with scalar
extension: along any field extension `k → K` it maps to the element attached to the base change
`K ⊗[k] ρ` (`Representation.mapRingHom_primitiveCentralIdempotent`).

So when `ρ` stays irreducible over an algebraically closed extension `K` of `k` (it is absolutely
irreducible) and `|G|` is invertible in `k`, `e_χ` is the primitive central idempotent of
`K ⊗[k] ρ` read in `k[G]`, and the identities proved over `K` descend to `k[G]`, the map
`k[G] → K[G]` being injective: `e_χ` is a nonzero central idempotent, the elements attached to
representations whose base changes are not isomorphic are orthogonal, and for a family of
representations over `k` whose base changes form a complete list of irreducible representations
over `K` (the case of a field `k` that splits `G`), they sum to `1`. Compatibility with scalar
extension also lets `e_χ` be computed over a number field `F` and then mapped to a completion `F_v`
of `F`, where it is the element attached to the base change of `ρ` to `F_v`.

## Main results

* `Representation.mapRingHom_primitiveCentralIdempotent`: compatibility with scalar extension.
* `Representation.isIdempotentElem_primitiveCentralIdempotent_of_baseChange`,
  `Representation.primitiveCentralIdempotent_ne_zero_of_baseChange`,
  `Representation.primitiveCentralIdempotent_mul_primitiveCentralIdempotent_of_baseChange`,
  `TauCeti.Representation.sum_primitiveCentralIdempotent_of_baseChange`: idempotence,
  nonvanishing, orthogonality and completeness for absolutely irreducible representations.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, 2016, Theorem 3.6.2, p. 42.
-/

public section

open scoped MonoidAlgebra TensorProduct

namespace Representation

open TauCeti.Representation

variable {k : Type*} {G : Type*} [Field k] [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)
variable (K : Type*) [Field K] [Algebra k K]

/-- **Compatibility with scalar extension.** Along a field extension `k → K`, the element attached
to `ρ` maps to the element attached to the base change `K ⊗[k] ρ`. -/
@[simp]
theorem mapRingHom_primitiveCentralIdempotent :
    MonoidAlgebra.mapRingHom G (algebraMap k K) (primitiveCentralIdempotent ρ) =
      primitiveCentralIdempotent (ρ.baseChange K) := by
  ext g
  simp

variable [IsAlgClosed K] [(ρ.baseChange K).IsIrreducible]
variable [Invertible (Nat.card G : k)]

include K in
/-- **Idempotence.** If `|G|` is invertible in `k` and `ρ` stays irreducible over an algebraically
closed extension of `k`, then `primitiveCentralIdempotent ρ` is idempotent. -/
theorem isIdempotentElem_primitiveCentralIdempotent_of_baseChange :
    IsIdempotentElem (primitiveCentralIdempotent ρ) := by
  let := IsScalarTower.invertibleAlgebraCoeNat (R := k) (A := K) (Nat.card G)
  refine MonoidAlgebra.mapRingHom_injective (algebraMap k K).injective ?_
  rw [map_mul, mapRingHom_primitiveCentralIdempotent]
  exact (isIdempotentElem_primitiveCentralIdempotent _).eq

include K in
/-- **Nonvanishing.** If `|G|` is invertible in `k` and `ρ` stays irreducible over an
algebraically closed extension of `k`, then `primitiveCentralIdempotent ρ ≠ 0`. -/
theorem primitiveCentralIdempotent_ne_zero_of_baseChange : primitiveCentralIdempotent ρ ≠ 0 := by
  let := IsScalarTower.invertibleAlgebraCoeNat (R := k) (A := K) (Nat.card G)
  intro h
  apply primitiveCentralIdempotent_ne_zero (ρ.baseChange K)
  rw [← mapRingHom_primitiveCentralIdempotent, h, map_zero]

include K in
/-- **Orthogonality.** If `|G|` is invertible in `k` and `ρ`, `σ` stay irreducible over an
algebraically closed extension `K` of `k`, with `K ⊗[k] ρ` and `K ⊗[k] σ` not isomorphic, then
the elements attached to `ρ` and `σ` are orthogonal. -/
theorem primitiveCentralIdempotent_mul_primitiveCentralIdempotent_of_baseChange
    {W : Type*} [AddCommGroup W] [Module k W] (σ : Representation k G W)
    [(σ.baseChange K).IsIrreducible] (h : IsEmpty ((ρ.baseChange K).Equiv (σ.baseChange K))) :
    primitiveCentralIdempotent ρ * primitiveCentralIdempotent σ = 0 := by
  let := IsScalarTower.invertibleAlgebraCoeNat (R := k) (A := K) (Nat.card G)
  refine MonoidAlgebra.mapRingHom_injective (algebraMap k K).injective ?_
  rw [map_mul, map_zero, mapRingHom_primitiveCentralIdempotent,
    mapRingHom_primitiveCentralIdempotent,
    primitiveCentralIdempotent_mul_primitiveCentralIdempotent]
  simp [not_nonempty_iff.2 h]

end Representation

namespace TauCeti

section Family

namespace Representation

universe w

variable {k : Type*} {G : Type*} [Field k] [Group G] [Fintype G] [Invertible (Nat.card G : k)]
variable (K : Type*) [Field K] [Algebra k K] [IsAlgClosed K]
variable {ι : Type*} [Fintype ι] {V : ι → Type w} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  (ρ : ∀ i, Representation k G (V i)) [∀ i, ((ρ i).baseChange K).IsIrreducible]

include K in
/-- **The elements attached to a complete list of absolutely irreducible representations form a
complete family of orthogonal idempotents.** Let `ρ i` be representations over `k`, with `|G|`
invertible in `k`, whose base changes to an algebraically closed extension `K` are irreducible,
pairwise non-isomorphic and as many as the conjugacy classes of `G`: a complete list of the
irreducible representations over `K`, all defined over `k`. -/
theorem completeOrthogonalIdempotents_primitiveCentralIdempotent_of_baseChange
    (hind : Pairwise fun i j ↦ IsEmpty (((ρ i).baseChange K).Equiv ((ρ j).baseChange K)))
    (hcard : Nat.card ι = Nat.card (ConjClasses G)) :
    CompleteOrthogonalIdempotents fun i ↦ primitiveCentralIdempotent (ρ i) := by
  let := IsScalarTower.invertibleAlgebraCoeNat (R := k) (A := K) (Nat.card G)
  refine (CompleteOrthogonalIdempotents.map_injective_iff
    (MonoidAlgebra.mapRingHom G (algebraMap k K))
    (MonoidAlgebra.mapRingHom_injective (algebraMap k K).injective)).1 ?_
  simpa [Function.comp_def] using
    completeOrthogonalIdempotents_primitiveCentralIdempotent (fun i ↦ (ρ i).baseChange K) hind hcard

include K in
/-- **Completeness.** The elements attached to a complete list of absolutely irreducible
representations, as in `completeOrthogonalIdempotents_primitiveCentralIdempotent_of_baseChange`,
sum to `1`. -/
theorem sum_primitiveCentralIdempotent_of_baseChange
    (hind : Pairwise fun i j ↦ IsEmpty (((ρ i).baseChange K).Equiv ((ρ j).baseChange K)))
    (hcard : Nat.card ι = Nat.card (ConjClasses G)) :
    ∑ i, primitiveCentralIdempotent (ρ i) = 1 :=
  (completeOrthogonalIdempotents_primitiveCentralIdempotent_of_baseChange K ρ hind hcard).complete

end Representation

end Family

end TauCeti
