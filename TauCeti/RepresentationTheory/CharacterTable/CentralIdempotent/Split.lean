/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.CharacterTable.IdempotentDecomposition
import TauCeti.Algebra.MonoidAlgebra.Basic

/-!
# Primitive central idempotents of absolutely irreducible characters over any field

For a representation `ρ` of a finite group `G` over any field `k`, with character `χ`, the element

`e_χ = (χ(1) / |G|) ∑_g χ(g⁻¹) g`

of `k[G]` is `TauCeti.Representation.primitiveCentralIdempotent ρ`. It is compatible with scalar
extension: along any field extension `k → K` it maps to the element attached to the base change
`K ⊗[k] ρ` (`TauCeti.Representation.mapRingHom_primitiveCentralIdempotent`).

So when `ρ` stays irreducible over an algebraically closed extension `K` of `k` (it is absolutely
irreducible) and `|G|` is invertible in `k`, `e_χ` is the primitive central idempotent of
`K ⊗[k] ρ` read in `k[G]`, and the identities proved over `K` descend to `k[G]`, the map
`k[G] → K[G]` being injective: `e_χ` is a nonzero central idempotent, the elements attached to
representations whose base changes are not isomorphic are orthogonal, and for a family of
representations over `k` whose base changes form a complete list of irreducible representations
over `K` (the case of a field `k` that splits `G`), they sum to `1`. For a splitting modular system
`(K, O, k)`, this lets the idempotents `e_χ` be defined over a number field `F` and mapped to its
completion `K`.

## Main results

* `TauCeti.Representation.mapRingHom_primitiveCentralIdempotent`: compatibility with scalar
  extension.
* `TauCeti.Representation.isIdempotentElem_primitiveCentralIdempotent_of_baseChange`,
  `TauCeti.Representation.primitiveCentralIdempotent_ne_zero_of_baseChange`,
  `TauCeti.Representation.primitiveCentralIdempotent_mul_primitiveCentralIdempotent_of_baseChange`,
  `TauCeti.Representation.sum_primitiveCentralIdempotent_of_baseChange`: idempotence,
  nonvanishing, orthogonality and completeness for absolutely irreducible representations.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, 2016, Theorem 3.6.2, p. 42.
-/

public section

open scoped MonoidAlgebra TensorProduct

namespace TauCeti

namespace Representation

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

omit [Fintype G] in
/-- If `|G|` is invertible in `k`, it is invertible in any field extension `K` of `k`. -/
private noncomputable abbrev invertibleNatCard [Invertible (Nat.card G : k)] :
    Invertible (Nat.card G : K) :=
  (Invertible.map (algebraMap k K) _).copy _ (map_natCast _ _).symm

variable [IsAlgClosed K] [(ρ.baseChange K).IsIrreducible]
variable [Invertible (Nat.card G : k)]

include K in
/-- **Idempotence.** If `|G|` is invertible in `k` and `ρ` stays irreducible over an algebraically
closed extension of `k`, then `primitiveCentralIdempotent ρ` is idempotent. -/
theorem isIdempotentElem_primitiveCentralIdempotent_of_baseChange :
    IsIdempotentElem (primitiveCentralIdempotent ρ) := by
  let := invertibleNatCard (k := k) (G := G) K
  refine MonoidAlgebra.mapRingHom_injective (algebraMap k K).injective ?_
  rw [map_mul, mapRingHom_primitiveCentralIdempotent]
  exact (isIdempotentElem_primitiveCentralIdempotent _).eq

include K in
/-- **Nonvanishing.** If `|G|` is invertible in `k` and `ρ` stays irreducible over an
algebraically closed extension of `k`, then `primitiveCentralIdempotent ρ ≠ 0`. -/
theorem primitiveCentralIdempotent_ne_zero_of_baseChange : primitiveCentralIdempotent ρ ≠ 0 := by
  let := invertibleNatCard (k := k) (G := G) K
  intro h
  apply primitiveCentralIdempotent_ne_zero (ρ.baseChange K)
  rw [← mapRingHom_primitiveCentralIdempotent, h, map_zero]

include K in
/-- **Orthogonality.** If `|G|` is invertible in `k` and `ρ`, `σ` stay irreducible over an
algebraically closed extension `K` of `k`, with `K ⊗[k] ρ` and `K ⊗[k] σ` not isomorphic, then
the elements attached to `ρ` and `σ` are orthogonal. -/
theorem primitiveCentralIdempotent_mul_primitiveCentralIdempotent_of_baseChange
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W] (σ : Representation k G W)
    [(σ.baseChange K).IsIrreducible] (h : IsEmpty ((ρ.baseChange K).Equiv (σ.baseChange K))) :
    primitiveCentralIdempotent ρ * primitiveCentralIdempotent σ = 0 := by
  let := invertibleNatCard (k := k) (G := G) K
  refine MonoidAlgebra.mapRingHom_injective (algebraMap k K).injective ?_
  rw [map_mul, map_zero, mapRingHom_primitiveCentralIdempotent,
    mapRingHom_primitiveCentralIdempotent,
    primitiveCentralIdempotent_mul_primitiveCentralIdempotent]
  simp [not_nonempty_iff.2 h]

end Representation

section Family

namespace Representation

universe w

variable {k : Type*} {G : Type*} [Field k] [Group G] [Fintype G] [Invertible (Nat.card G : k)]
variable (K : Type*) [Field K] [Algebra k K] [IsAlgClosed K]
variable {ι : Type*} [Fintype ι] {V : ι → Type w} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]
  [∀ i, FiniteDimensional k (V i)] (ρ : ∀ i, Representation k G (V i))
  [∀ i, ((ρ i).baseChange K).IsIrreducible]

include K in
/-- **Completeness.** Let `ρ i` be representations over `k`, with `|G|` invertible in `k`, whose
base changes to an algebraically closed extension `K` are irreducible, pairwise non-isomorphic and
as many as the conjugacy classes of `G`: a complete list of the irreducible representations over
`K`, all defined over `k`. Then the elements attached to them sum to `1`. -/
theorem sum_primitiveCentralIdempotent_of_baseChange
    (hind : Pairwise fun i j ↦ IsEmpty (((ρ i).baseChange K).Equiv ((ρ j).baseChange K)))
    (hcard : Nat.card ι = Nat.card (ConjClasses G)) :
    ∑ i, primitiveCentralIdempotent (ρ i) = 1 := by
  let := invertibleNatCard (k := k) (G := G) K
  refine MonoidAlgebra.mapRingHom_injective (algebraMap k K).injective ?_
  simp only [map_sum, map_one, mapRingHom_primitiveCentralIdempotent]
  exact sum_primitiveCentralIdempotent (fun i ↦ (ρ i).baseChange K) hind hcard

include K in
/-- **The elements attached to a complete list of absolutely irreducible representations form a
complete family of orthogonal idempotents.** -/
theorem completeOrthogonalIdempotents_primitiveCentralIdempotent_of_baseChange
    (hind : Pairwise fun i j ↦ IsEmpty (((ρ i).baseChange K).Equiv ((ρ j).baseChange K)))
    (hcard : Nat.card ι = Nat.card (ConjClasses G)) :
    CompleteOrthogonalIdempotents fun i ↦ primitiveCentralIdempotent (ρ i) where
  idem i := isIdempotentElem_primitiveCentralIdempotent_of_baseChange (ρ i) K
  ortho i j hij :=
    primitiveCentralIdempotent_mul_primitiveCentralIdempotent_of_baseChange (ρ i) K (ρ j) (hind hij)
  complete := sum_primitiveCentralIdempotent_of_baseChange K ρ hind hcard

end Representation

end Family

end TauCeti
