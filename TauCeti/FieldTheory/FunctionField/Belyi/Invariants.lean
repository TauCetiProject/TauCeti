/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.GaloisAction
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Equiv

/-!
# The genus and the ramification partitions of an algebraic Belyi pair

Besides its degree, an algebraic Belyi pair `F / k(t)` carries two kinds of numerical invariants:
the genus of the function field `F / k`, and, over each of the three marked places `t = 0`,
`t = 1` and `t = ∞`, the multiset of pairs `(e, f)` of ramification indices and relative residue
degrees at the places above it (`TauCeti.Place.localData`). Repeating each `e` by its `f` gives
the weighted ramification partition of the degree (`TauCeti.Place.weightedRamificationPartition`).
Over an algebraically closed field every `f` is `1`, and these are the three ramification
partitions of the Belyi map: the multisets of ramification indices over `0`, `1` and `∞`.

This file descends the genus, the local data and the weighted ramification partitions to
isomorphism classes of pairs, and proves that Galois conjugation preserves all of them, both for
pairs and for classes. Conjugation is base change along an isomorphism `σ : k ≃+* k'` of the
constants. It carries the places of `F` bijectively onto those of the conjugate, fixes each marked
place of the projective line, and keeps ramification indices and relative degrees
(`TauCeti.Place.localData_markedPlace_of_mapRingEquiv`); it identifies the Riemann–Roch spaces
semilinearly, hence keeps the genus (`TauCeti.genus_eq_of_ringEquiv`). Conjugation nevertheless
moves isomorphism classes in general, so these invariants constrain the Galois orbit of a class
without determining it.

## Main definitions

* `TauCeti.AlgebraicBelyiPair.IsoClass.genus`: the genus of an isomorphism class.
* `TauCeti.AlgebraicBelyiPair.IsoClass.localData`: the local data `(e, f)` of a class over the
  marked place numbered `i`.
* `TauCeti.AlgebraicBelyiPair.IsoClass.weightedRamificationPartition`: the weighted ramification
  partition of the degree of a class over the marked place numbered `i`.

## Main results

* `TauCeti.AlgebraicBelyiPair.genus_conj`,
  `TauCeti.AlgebraicBelyiPair.localData_markedPlace_conj` and
  `TauCeti.AlgebraicBelyiPair.parts_weightedRamificationPartition_markedPlace_conj`: conjugating a
  pair keeps its genus, and its local data and weighted ramification partition over each marked
  place.
* `TauCeti.AlgebraicBelyiPair.IsoClass.parts_weightedRamificationPartition_of_isAlgClosed`: over
  an algebraically closed field, the weighted ramification partition of a class consists of the
  ramification indices, one for each place above the marked place.
* `TauCeti.AlgebraicBelyiPair.IsoClass.genus_smul`,
  `TauCeti.AlgebraicBelyiPair.IsoClass.localData_smul` and
  `TauCeti.AlgebraicBelyiPair.IsoClass.parts_weightedRamificationPartition_smul`: the Galois
  action on isomorphism classes preserves the genus and the three ramification partitions.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.4 and III.1.
-/

public section

universe u

namespace TauCeti

namespace AlgebraicBelyiPair

variable {k k' : Type u} [Field k] [CharZero k] [Field k'] [CharZero k']
  (σ : k ≃+* k') (X : AlgebraicBelyiPair k)

/-- **Conjugation preserves the genus** of an algebraic Belyi pair. -/
@[simp]
theorem genus_conj : genus k' (X.conj σ) = genus k X :=
  genus_eq_of_ringEquiv σ (conjRingEquiv σ X) (conjRingEquiv_algebraMap σ X)

/-- **Conjugation preserves the local data** of an algebraic Belyi pair: the pairs `(e, f)` of
ramification indices and relative degrees at the places over the marked place numbered `i` are
the same for the pair and for its conjugate. -/
@[simp↓]
theorem localData_markedPlace_conj (i : Fin 3) :
    Place.localData (k' := k') (F' := X.conj σ) k' (RatFunc k') (Place.markedPlace k' i) =
      Place.localData (k' := k) (F' := X) k (RatFunc k) (Place.markedPlace k i) :=
  Place.localData_markedPlace_of_mapRingEquiv σ (conjRingEquiv σ X)
    (conjRingEquiv_algebraMap_ratFunc σ X) i

/-- **Conjugation preserves the weighted ramification partitions** of an algebraic Belyi pair. The
two partitions are of the same number, by `TauCeti.AlgebraicBelyiPair.finrank_conj`, and have the
same parts. -/
@[simp↓]
theorem parts_weightedRamificationPartition_markedPlace_conj (i : Fin 3) :
    (Place.weightedRamificationPartition (k' := k') (F' := X.conj σ) k' (RatFunc k')
        (IsFunctionField.ratFunc k') (Place.markedPlace k' i)).parts =
      (Place.weightedRamificationPartition (k' := k) (F' := X) k (RatFunc k)
        (IsFunctionField.ratFunc k) (Place.markedPlace k i)).parts := by
  rw [Place.parts_weightedRamificationPartition, Place.parts_weightedRamificationPartition,
    localData_markedPlace_conj]

namespace IsoClass

/-- The **genus** of an isomorphism class of algebraic Belyi pairs: the genus of the function
field of any representative over `k`. -/
noncomputable def genus : IsoClass k → ℕ :=
  lift (fun X : AlgebraicBelyiPair k ↦ TauCeti.genus k X) fun _ _ e ↦
    (genus_eq_of_ringEquiv (RingEquiv.refl k) e.toRingEquiv fun c ↦
      (e.restrictScalars k).commutes c).symm

@[simp]
theorem genus_mk : (mk X).genus = TauCeti.genus k X :=
  lift_mk _ _ X

/-- The **local data** of an isomorphism class `c` of algebraic Belyi pairs over the marked place
numbered `i`: the multiset of pairs `(e, f)` of ramification indices and relative residue degrees
at the places above it, in any representative of `c`. -/
noncomputable def localData (c : IsoClass k) (i : Fin 3) : Multiset (ℕ × ℕ) :=
  lift (fun X : AlgebraicBelyiPair k ↦
      Place.localData (k' := k) (F' := X) k (RatFunc k) (Place.markedPlace k i))
    (fun _ _ e ↦ (Place.localData_markedPlace_of_mapRingEquiv (RingEquiv.refl k) e.toRingEquiv
      (fun x ↦ by simp [RatFunc.mapRingEquiv_refl]) i).symm) c

@[simp]
theorem localData_mk (i : Fin 3) :
    (mk X).localData i =
      Place.localData (k' := k) (F' := X) k (RatFunc k) (Place.markedPlace k i) :=
  lift_mk _ _ X

/-- The **weighted ramification partition** of an isomorphism class `c` of algebraic Belyi pairs
over the marked place numbered `i`: the partition of the degree of `c` in which the ramification
index at each place above the marked place is repeated by its relative residue degree. Over an
algebraically closed field the residue degrees are `1`
(`TauCeti.AlgebraicBelyiPair.IsoClass.parts_weightedRamificationPartition_of_isAlgClosed`). -/
noncomputable def weightedRamificationPartition (c : IsoClass k) (i : Fin 3) :
    c.degree.Partition where
  parts := (c.localData i).bind fun ef ↦ Multiset.replicate ef.2 ef.1
  parts_pos := by
    induction c using ind with
    | h X =>
      rw [localData_mk,
        ← Place.parts_weightedRamificationPartition (hF := IsFunctionField.ratFunc k)]
      exact Nat.Partition.parts_pos _
  parts_sum := by
    induction c using ind with
    | h X =>
      rw [localData_mk,
        ← Place.parts_weightedRamificationPartition (hF := IsFunctionField.ratFunc k), degree_mk]
      exact Nat.Partition.parts_sum _

/-- The parts of the weighted ramification partition are obtained by repeating each ramification
index by its relative residue degree. -/
theorem parts_weightedRamificationPartition (c : IsoClass k) (i : Fin 3) :
    (c.weightedRamificationPartition i).parts =
      (c.localData i).bind fun ef ↦ Multiset.replicate ef.2 ef.1 :=
  (rfl)

/-- The weighted ramification partition of the class of a pair is the weighted ramification
partition of the pair. -/
@[simp]
theorem parts_weightedRamificationPartition_mk (i : Fin 3) :
    ((mk X).weightedRamificationPartition i).parts =
      (Place.weightedRamificationPartition (k' := k) (F' := X) k (RatFunc k)
        (IsFunctionField.ratFunc k) (Place.markedPlace k i)).parts := by
  rw [parts_weightedRamificationPartition, localData_mk, Place.parts_weightedRamificationPartition]

/-- Over an algebraically closed field, the weighted ramification partition of a class over a
marked place consists of the ramification indices at the places above it, one for each place. -/
theorem parts_weightedRamificationPartition_of_isAlgClosed [IsAlgClosed k] (c : IsoClass k)
    (i : Fin 3) :
    (c.weightedRamificationPartition i).parts = (c.localData i).map Prod.fst := by
  induction c using ind with
  | h X =>
    rw [parts_weightedRamificationPartition_mk, localData_mk,
      Place.parts_weightedRamificationPartition_of_isAlgClosed]

/-! ### Galois invariance -/

/-- **Conjugation preserves the genus** of an isomorphism class. -/
@[simp]
theorem genus_conj (c : IsoClass k) : (c.conj σ).genus = c.genus := by
  induction c using ind with
  | h X => simp

/-- **Conjugation preserves the local data** of an isomorphism class over each marked place. -/
@[simp]
theorem localData_conj (c : IsoClass k) (i : Fin 3) : (c.conj σ).localData i = c.localData i := by
  induction c using ind with
  | h X => simp

/-- **Conjugation preserves the weighted ramification partitions** of an isomorphism class. The
two partitions are of the same number, by `TauCeti.AlgebraicBelyiPair.IsoClass.degree_conj`, and
have the same parts. -/
@[simp]
theorem parts_weightedRamificationPartition_conj (c : IsoClass k) (i : Fin 3) :
    ((c.conj σ).weightedRamificationPartition i).parts =
      (c.weightedRamificationPartition i).parts := by
  rw [parts_weightedRamificationPartition, parts_weightedRamificationPartition, localData_conj]

variable {G : Type*} [Group G] [MulSemiringAction G k]

/-- **The Galois action preserves the genus** of an isomorphism class. -/
@[simp]
theorem genus_smul (g : G) (c : IsoClass k) : (g • c).genus = c.genus := by
  rw [smul_def, genus_conj]

/-- **The Galois action preserves the local data** of an isomorphism class over each marked
place. -/
@[simp]
theorem localData_smul (g : G) (c : IsoClass k) (i : Fin 3) :
    (g • c).localData i = c.localData i := by
  rw [smul_def, localData_conj]

/-- **The Galois action preserves the weighted ramification partitions** of an isomorphism
class. -/
@[simp]
theorem parts_weightedRamificationPartition_smul (g : G) (c : IsoClass k) (i : Fin 3) :
    ((g • c).weightedRamificationPartition i).parts =
      (c.weightedRamificationPartition i).parts := by
  rw [parts_weightedRamificationPartition, parts_weightedRamificationPartition, localData_smul]

end IsoClass

end AlgebraicBelyiPair

end TauCeti
