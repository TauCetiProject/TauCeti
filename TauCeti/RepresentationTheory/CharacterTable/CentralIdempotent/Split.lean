/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange
public import TauCeti.RepresentationTheory.CharacterTable.IdempotentDecomposition

/-!
# Central idempotents of characters over a field that need not be algebraically closed

For a representation `ρ` of a finite group `G` over any field `k`, with character `χ`, the element

`e_χ = (χ(1) / |G|) ∑_g χ(g⁻¹) g`

of `k[G]` is `TauCeti.Representation.characterIdempotent ρ`. It is compatible with scalar
extension: along any field extension `k → K` it maps to the element attached to the base change
`K ⊗[k] ρ` (`TauCeti.Representation.mapRingHom_characterIdempotent`). Over an algebraically closed
field, for an irreducible `ρ`, it is the primitive central idempotent
`TauCeti.Representation.primitiveCentralIdempotent ρ`.

So when `ρ` stays irreducible over an algebraically closed extension `K` of `k` (it is absolutely
irreducible) and `|G|` is invertible in `k`, `e_χ` is the primitive central idempotent of
`K ⊗[k] ρ` read in `k[G]`, and the identities proved over `K` descend to `k[G]`, the map
`k[G] → K[G]` being injective: `e_χ` is a nonzero central idempotent, the elements attached to
representations whose base changes are not isomorphic are orthogonal, and for a family of
representations over `k` whose base changes form a complete list of irreducible representations
over `K` (the case of a field `k` that splits `G`), they sum to `1`.

This is ModularCharactersAndBlocks §4.1: for the splitting modular system of §1.1, the idempotents
`e_χ` are defined over the cyclotomic field `F` and mapped to its completion `K`.

## Main definitions

* `TauCeti.Representation.characterIdempotent`: the element `(χ(1) / |G|) ∑_g χ(g⁻¹) g`.

## Main results

* `TauCeti.Representation.mapRingHom_characterIdempotent`: compatibility with scalar extension.
* `TauCeti.Representation.characterIdempotent_eq_primitiveCentralIdempotent`: over an
  algebraically closed field it is the primitive central idempotent.
* `TauCeti.Representation.isIdempotentElem_characterIdempotent`,
  `TauCeti.Representation.characterIdempotent_ne_zero`,
  `TauCeti.Representation.characterIdempotent_mul_characterIdempotent_eq_zero`,
  `TauCeti.Representation.sum_characterIdempotent`: idempotence, nonvanishing, orthogonality and
  completeness for absolutely irreducible representations.

## References

* P. Webb, *A Course in Finite Group Representation Theory*, 2016, Theorem 3.6.2, p. 42.
-/

public section

open scoped MonoidAlgebra TensorProduct

namespace TauCeti

namespace Representation

variable {k : Type*} {G : Type*} [Field k] [Group G] [Fintype G]
variable {V : Type*} [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-- The element `e_χ = (χ(1) / |G|) ∑_g χ(g⁻¹) g` of `k[G]` attached to a representation `ρ` with
character `χ`, over any field. For an irreducible representation over an algebraically closed
field it is the primitive central idempotent
(`TauCeti.Representation.characterIdempotent_eq_primitiveCentralIdempotent`). -/
noncomputable def characterIdempotent : k[G] :=
  ((Nat.card G : k)⁻¹ * ρ.character 1) • characterSum ρ

/-- The coefficients of `characterIdempotent ρ`. -/
@[simp]
theorem characterIdempotent_coeff (g : G) :
    (characterIdempotent ρ).coeff g = (Nat.card G : k)⁻¹ * ρ.character 1 * ρ.character g⁻¹ := by
  simp [characterIdempotent]

/-- `characterIdempotent ρ` is central. -/
theorem characterIdempotent_mem_center : characterIdempotent ρ ∈ Subalgebra.center k k[G] :=
  Subalgebra.smul_mem _ (characterSum_mem_center ρ) _

/-- **Over an algebraically closed field**, the element attached to an irreducible representation
is its primitive central idempotent. -/
theorem characterIdempotent_eq_primitiveCentralIdempotent [FiniteDimensional k V] [IsAlgClosed k]
    [Invertible (Nat.card G : k)] [ρ.IsIrreducible] :
    characterIdempotent ρ = primitiveCentralIdempotent ρ := by
  ext g
  simp

variable (K : Type*) [Field K] [Algebra k K]

/-- **Compatibility with scalar extension.** Along a field extension `k → K`, the element attached
to `ρ` maps to the element attached to the base change `K ⊗[k] ρ`. -/
theorem mapRingHom_characterIdempotent :
    MonoidAlgebra.mapRingHom G (algebraMap k K) (characterIdempotent ρ) =
      characterIdempotent (ρ.baseChange K) := by
  ext g
  simp

omit [Fintype G] in
/-- The map `k[G] → K[G]` induced by a field extension is injective. -/
theorem mapRingHom_algebraMap_injective :
    Function.Injective (MonoidAlgebra.mapRingHom G (algebraMap k K)) :=
  MonoidAlgebra.map_injective (algebraMap k K).toAddMonoidHom (algebraMap k K).injective

variable [IsAlgClosed K] [FiniteDimensional k V] [(ρ.baseChange K).IsIrreducible]

/-- The element attached to `ρ`, read in `K[G]`, is the primitive central idempotent of the base
change of `ρ` to an algebraically closed field `K` in which it stays irreducible. -/
theorem mapRingHom_characterIdempotent_eq_primitiveCentralIdempotent
    [Invertible (Nat.card G : K)] :
    MonoidAlgebra.mapRingHom G (algebraMap k K) (characterIdempotent ρ) =
      primitiveCentralIdempotent (ρ.baseChange K) :=
  (mapRingHom_characterIdempotent ρ K).trans (characterIdempotent_eq_primitiveCentralIdempotent _)

include K in
/-- **Idempotence.** If `|G|` is invertible in `k` and `ρ` stays irreducible over an algebraically
closed extension of `k`, then `characterIdempotent ρ` is idempotent. -/
theorem isIdempotentElem_characterIdempotent [Invertible (Nat.card G : k)] :
    IsIdempotentElem (characterIdempotent ρ) := by
  have : Invertible (Nat.card G : K) :=
    (Invertible.map (algebraMap k K) _).copy _ (map_natCast _ _).symm
  refine mapRingHom_algebraMap_injective K ?_
  rw [map_mul, mapRingHom_characterIdempotent_eq_primitiveCentralIdempotent]
  exact (isIdempotentElem_primitiveCentralIdempotent _).eq

include K in
/-- **Nonvanishing.** If `|G|` is invertible in `k` and `ρ` stays irreducible over an
algebraically closed extension of `k`, then `characterIdempotent ρ ≠ 0`. -/
theorem characterIdempotent_ne_zero [Invertible (Nat.card G : k)] : characterIdempotent ρ ≠ 0 := by
  have : Invertible (Nat.card G : K) :=
    (Invertible.map (algebraMap k K) _).copy _ (map_natCast _ _).symm
  intro h
  apply primitiveCentralIdempotent_ne_zero (ρ.baseChange K)
  rw [← mapRingHom_characterIdempotent_eq_primitiveCentralIdempotent, h, map_zero]

include K in
/-- **Orthogonality.** If `|G|` is invertible in `k` and `ρ`, `σ` stay irreducible over an
algebraically closed extension `K` of `k`, with `K ⊗[k] ρ` and `K ⊗[k] σ` not isomorphic, then
the elements attached to `ρ` and `σ` are orthogonal. -/
theorem characterIdempotent_mul_characterIdempotent_eq_zero [Invertible (Nat.card G : k)]
    {W : Type*} [AddCommGroup W] [Module k W] [FiniteDimensional k W] (σ : Representation k G W)
    [(σ.baseChange K).IsIrreducible] (h : IsEmpty ((ρ.baseChange K).Equiv (σ.baseChange K))) :
    characterIdempotent ρ * characterIdempotent σ = 0 := by
  have : Invertible (Nat.card G : K) :=
    (Invertible.map (algebraMap k K) _).copy _ (map_natCast _ _).symm
  refine mapRingHom_algebraMap_injective K ?_
  rw [map_mul, map_zero, mapRingHom_characterIdempotent_eq_primitiveCentralIdempotent,
    mapRingHom_characterIdempotent_eq_primitiveCentralIdempotent,
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
theorem sum_characterIdempotent
    (hind : Pairwise fun i j ↦ IsEmpty (((ρ i).baseChange K).Equiv ((ρ j).baseChange K)))
    (hcard : Nat.card ι = Nat.card (ConjClasses G)) :
    ∑ i, characterIdempotent (ρ i) = 1 := by
  have : Invertible (Nat.card G : K) :=
    (Invertible.map (algebraMap k K) _).copy _ (map_natCast _ _).symm
  refine mapRingHom_algebraMap_injective K ?_
  simp only [map_sum, map_one, mapRingHom_characterIdempotent_eq_primitiveCentralIdempotent]
  exact sum_primitiveCentralIdempotent (fun i ↦ (ρ i).baseChange K) hind hcard

include K in
/-- **The elements attached to a complete list of absolutely irreducible representations form a
complete family of orthogonal idempotents.** -/
theorem completeOrthogonalIdempotents_characterIdempotent
    (hind : Pairwise fun i j ↦ IsEmpty (((ρ i).baseChange K).Equiv ((ρ j).baseChange K)))
    (hcard : Nat.card ι = Nat.card (ConjClasses G)) :
    CompleteOrthogonalIdempotents fun i ↦ characterIdempotent (ρ i) where
  idem i := isIdempotentElem_characterIdempotent (ρ i) K
  ortho i j hij := characterIdempotent_mul_characterIdempotent_eq_zero (ρ i) K (ρ j) (hind hij)
  complete := sum_characterIdempotent K ρ hind hcard

end Representation

end Family

end TauCeti
