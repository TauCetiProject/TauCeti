/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.Class
public import TauCeti.Combinatorics.PermutationTriple.Passport.OfTriple
public import TauCeti.GroupTheory.Perm.Cycle.Notation

/-!
# Belyi-map records and the translation of stored triples

The LMFDB table of Belyi maps stores, for each Galois orbit of Belyi maps, the monodromy triples
of the maps in the orbit. The database composes permutations from left to right, so a stored
triple `(σ0, σ1, σinf)` satisfies `σ0 * σ1 * σinf = 1` in Mathlib's multiplication, the opposite
of the relation `σinf * σ1 * σ0 = 1` imposed on a `TauCeti.PermutationTriple`. Such a stored
triple is a `TauCeti.PermutationTriple.LMFDB.StoredTriple`, and the triple it denotes is its
image `TauCeti.PermutationTriple.LMFDB.StoredTriple.toTriple` under the inverse of
`TauCeti.PermutationTriple.equivOppositeConvention`: the componentwise inverse.

The first part of this file proves that this translation preserves every invariant a record
asserts, each computed directly on the stored permutations: the ordered full cycle partitions,
the orders, the monodromy group, connectedness, the automorphism group, the Euler
characteristic and genus, and membership in a passport. It also commutes with relabeling the
sheets. Reading a stored triple without the translation is wrong as soon as its first two
components do not commute, by
`TauCeti.PermutationTriple.LMFDB.StoredTriple.mul_mul_eq_one_iff_commute`, so a stored triple
whose first two components commute cannot detect the convention.

The second part mirrors one row of the table as a `TauCeti.PermutationTriple.LMFDB.BelyiRecord`.
Its stored triples are listed position by position against the stored complex embeddings of the
base field, which is recorded by the field
`TauCeti.PermutationTriple.LMFDB.BelyiRecord.storedEmbeddingCount_eq_triplesLength`. The number of
embedding entries is the natural number
`TauCeti.PermutationTriple.LMFDB.BelyiRecord.storedEmbeddingCount`, and the stored orbit size is
asserted to equal it, not the size of a Galois orbit of isomorphism classes: several stored
triples may be simultaneously conjugate, so the isomorphism classes they represent,
`TauCeti.PermutationTriple.LMFDB.BelyiRecord.storedClasses`, may be fewer than the stored
entries. `TauCeti.PermutationTriple.LMFDB.BelyiRecord.IsValidFor` states what a row asserts about
a passport, and the theorems following it read the stored partitions, genus, and monodromy group
off the stored permutations, and bound the number of stored classes by the passport size.

The table also stores each triple in disjoint cycle notation, which omits fixed points and writes
the identity as the empty product. A row parses it into lists of cycles
(`TauCeti.PermutationTriple.LMFDB.CycleNotationTriple`), and validity asks that it be a disjoint
cycle notation (`Equiv.Perm.IsCycleNotation`) for the stored triple in the same position. The
notation is not translated: the stored notation of a component is reversed cycle by cycle to give
the notation of the corresponding component of the translated triple
(`TauCeti.PermutationTriple.LMFDB.StoredTriple.IsCycleNotation.isCycleNotation_toTriple_σ0`). The
listed lengths are the stored permutation's `Equiv.Perm.cycleType`, so the stored partitions are
the listed lengths padded by parts equal to one
(`TauCeti.PermutationTriple.LMFDB.BelyiRecord.IsValidFor.lambdas_eq_of_mem_triplesCyc`).

The stored base field, the defining equations of the curve and the map, the floating-point
values of the embeddings, and the labels are carried as data and are not interpreted here.

## Main definitions

* `TauCeti.PermutationTriple.LMFDB.StoredTriple`: a triple in the database's convention.
* `TauCeti.PermutationTriple.LMFDB.StoredTriple.toTriple`: the triple it denotes.
* `TauCeti.PermutationTriple.LMFDB.StoredTriple.IsCycleNotation`: a stored triple written in
  disjoint cycle notation.
* `TauCeti.PermutationTriple.LMFDB.BelyiRecord`: a parsed row of the Belyi-map table.
* `TauCeti.PermutationTriple.LMFDB.BelyiRecord.storedEmbeddingCount`: the number of stored
  embedding entries.
* `TauCeti.PermutationTriple.LMFDB.BelyiRecord.IsValidFor`: validity of a row for a passport.

## Main results

* `TauCeti.PermutationTriple.LMFDB.StoredTriple.toTriple_eq_iff`: the translation is the
  opposite-convention equivalence.
* `TauCeti.PermutationTriple.LMFDB.StoredTriple.genus_toTriple` and
  `TauCeti.PermutationTriple.LMFDB.StoredTriple.hasPassport_toTriple_iff`, with their companions:
  the invariants of the translated triple, read off the stored permutations.
* `TauCeti.PermutationTriple.LMFDB.BelyiRecord.IsValidFor.lambdas_eq_of_mem_triplesCyc`: the
  stored partitions of a valid row are the cycle lengths of its stored cycle notation, padded by
  fixed points.
* `TauCeti.PermutationTriple.LMFDB.BelyiRecord.IsValidFor.card_storedClasses_le_passportSize`:
  the stored triples of a valid row represent at most as many isomorphism classes as the passport
  has.

## References

* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*, Proceedings of the
  Thirteenth Algorithmic Number Theory Symposium, Open Book Series 2, 2019, §2.
* LMFDB, [Belyi maps](https://www.lmfdb.org/Belyi/).
-/

open Equiv MulAction

public section

namespace TauCeti
namespace PermutationTriple
namespace LMFDB

/-- A permutation triple as the LMFDB stores it. The database composes permutations from left to
right, so its stored triples satisfy `σ0 * σ1 * σinf = 1` in Mathlib's multiplication. -/
abbrev StoredTriple (n : ℕ) : Type :=
  {p : Perm (Fin n) × Perm (Fin n) × Perm (Fin n) // p.1 * p.2.1 * p.2.2 = 1}

/-- A triple of permutations of `Fin n` in disjoint cycle notation, as the database's cycle
notation is parsed: each component is a list of cycles, each cycle the list of its points in
order, where the stored point `i` is the element `i - 1` of `Fin n`. -/
abbrev CycleNotationTriple (n : ℕ) : Type :=
  List (List (Fin n)) × List (List (Fin n)) × List (List (Fin n))

namespace StoredTriple

variable {n : ℕ} (s : StoredTriple n)

/-- The permutation triple denoted by a stored triple: its image under the inverse of the
opposite-convention equivalence, which inverts every component. -/
def toTriple : PermutationTriple n :=
  (equivOppositeConvention n).symm s

@[simp] theorem toTriple_σ0 : s.toTriple.σ0 = s.1.1⁻¹ :=
  equivOppositeConvention_symm_apply_σ0 s

@[simp] theorem toTriple_σ1 : s.toTriple.σ1 = s.1.2.1⁻¹ :=
  equivOppositeConvention_symm_apply_σ1 s

@[simp] theorem toTriple_σinf : s.toTriple.σinf = s.1.2.2⁻¹ :=
  equivOppositeConvention_symm_apply_σinf s

/-- A stored triple denotes `t` exactly when it is the opposite-convention form of `t`. -/
theorem toTriple_eq_iff {t : PermutationTriple n} :
    s.toTriple = t ↔ s = equivOppositeConvention n t :=
  Equiv.symm_apply_eq _

@[simp] theorem toTriple_equivOppositeConvention (t : PermutationTriple n) :
    StoredTriple.toTriple (equivOppositeConvention n t) = t :=
  (equivOppositeConvention n).symm_apply_apply t

@[simp] theorem equivOppositeConvention_toTriple :
    equivOppositeConvention n s.toTriple = s :=
  (equivOppositeConvention n).apply_symm_apply s

/-- The stored components also satisfy this library's relation exactly when the first two of
them commute. A stored triple whose first two components do not commute is therefore not a
permutation triple when read without translation. -/
theorem mul_mul_eq_one_iff_commute :
    s.1.2.2 * s.1.2.1 * s.1.1 = 1 ↔ Commute s.1.1 s.1.2.1 := by
  have hinf : s.1.2.2 = (s.1.1 * s.1.2.1)⁻¹ := eq_inv_of_mul_eq_one_right s.2
  rw [hinf, mul_assoc, inv_mul_eq_one, Commute, SemiconjBy, eq_comm]

/-- Relabeling a stored triple relabels the triple it denotes. -/
@[simp] theorem toTriple_relabelOppositeConvention (τ : Perm (Fin n)) :
    StoredTriple.toTriple (relabelOppositeConvention τ s) = τ • s.toTriple := by
  rw [toTriple_eq_iff, equivOppositeConvention_smul, equivOppositeConvention_toTriple]

/-! ### Invariants of the translated triple -/

/-- The ordered full cycle partitions of the translated triple are those of the stored
components. -/
@[simp] theorem cycleData_toTriple :
    s.toTriple.cycleData = (s.1.1.partition.parts, s.1.2.1.partition.parts,
      s.1.2.2.partition.parts) := by
  rw [← cycleData_inv_components]
  simp

/-- The orders of the components of the translated triple are those of the stored
components. -/
@[simp] theorem orderTriple_toTriple :
    s.toTriple.orderTriple = (orderOf s.1.1, orderOf s.1.2.1, orderOf s.1.2.2) := by
  rw [← orderTriple_inv_components]
  simp

/-- The monodromy group of the translated triple is generated by the first two stored
components. -/
@[simp] theorem monodromyGroup_toTriple :
    s.toTriple.monodromyGroup = Subgroup.closure {s.1.1, s.1.2.1} := by
  rw [← closure_inv_pair_eq_monodromyGroup]
  simp

/-- The translated triple is connected exactly when there is a sheet and the first two stored
components generate a transitive group. -/
theorem isConnected_toTriple_iff :
    s.toTriple.IsConnected ↔
      n ≠ 0 ∧ IsPretransitive (Subgroup.closure {s.1.1, s.1.2.1}) (Fin n) := by
  rw [isConnected_iff, monodromyGroup_toTriple]

/-- The automorphism group of the translated triple is the simultaneous centralizer of the first
two stored components. -/
@[simp] theorem automorphismGroup_toTriple :
    s.toTriple.automorphismGroup = Subgroup.centralizer {s.1.1, s.1.2.1} := by
  rw [automorphismGroup_eq_centralizer_monodromyGroup, monodromyGroup_toTriple,
    Subgroup.centralizer_closure]

/-- The Euler characteristic of the translated triple, counted on the stored components. -/
@[simp] theorem eulerChar_toTriple :
    s.toTriple.eulerChar =
      (orbitCount s.1.1 : ℤ) + orbitCount s.1.2.1 + orbitCount s.1.2.2 - n := by
  simp [eulerChar_def]

/-- The genus of the translated triple, counted on the stored components. -/
theorem genus_toTriple :
    s.toTriple.genus =
      ((2 - ((orbitCount s.1.1 : ℤ) + orbitCount s.1.2.1 + orbitCount s.1.2.2 - n)) / 2).toNat := by
  rw [genus_def, eulerChar_toTriple]

/-- A connected translated triple has passport `P` exactly when the group generated by the
first two stored components is conjugate to the reference group of `P` and the stored components
have the partitions of `P`. -/
theorem hasPassport_toTriple_iff (hs : s.toTriple.IsConnected) (P : PassportSpec n) :
    PassportSpec.HasPassport ⟨s.toTriple, hs⟩ P ↔
      (∃ τ : Perm (Fin n),
        (Subgroup.closure {s.1.1, s.1.2.1}).map (MulAut.conj τ).toMonoidHom = P.G) ∧
      s.1.1.partition.parts = P.lam0 ∧ s.1.2.1.partition.parts = P.lam1 ∧
      s.1.2.2.partition.parts = P.laminf := by
  rw [PassportSpec.hasPassport_iff, monodromyGroup_toTriple, cycleData_toTriple]

/-! ### Stored cycle notation -/

/-- `c` writes each component of `s` in disjoint cycle notation, as the database stores it: fixed
points are omitted and the identity is the empty list of cycles. -/
structure IsCycleNotation (c : CycleNotationTriple n) : Prop where
  /-- `c.1` writes the first stored component. -/
  σ0 : s.1.1.IsCycleNotation c.1
  /-- `c.2.1` writes the second stored component. -/
  σ1 : s.1.2.1.IsCycleNotation c.2.1
  /-- `c.2.2` writes the third stored component. -/
  σinf : s.1.2.2.IsCycleNotation c.2.2

/-- Every stored triple can be written in disjoint cycle notation. -/
theorem exists_isCycleNotation : ∃ c : CycleNotationTriple n, s.IsCycleNotation c := by
  obtain ⟨p0, h0⟩ := s.1.1.exists_isCycleNotation
  obtain ⟨p1, h1⟩ := s.1.2.1.exists_isCycleNotation
  obtain ⟨pinf, hinf⟩ := s.1.2.2.exists_isCycleNotation
  exact ⟨(p0, p1, pinf), h0, h1, hinf⟩

namespace IsCycleNotation

variable {s} {c : CycleNotationTriple n}

/-- The stored cycle notation of the first component, reversed cycle by cycle, writes the first
component of the translated triple. -/
theorem isCycleNotation_toTriple_σ0 (h : s.IsCycleNotation c) :
    s.toTriple.σ0.IsCycleNotation (c.1.map List.reverse) := by
  simpa using h.σ0.inv

/-- The stored cycle notation of the second component, reversed cycle by cycle, writes the second
component of the translated triple. -/
theorem isCycleNotation_toTriple_σ1 (h : s.IsCycleNotation c) :
    s.toTriple.σ1.IsCycleNotation (c.2.1.map List.reverse) := by
  simpa using h.σ1.inv

/-- The stored cycle notation of the third component, reversed cycle by cycle, writes the third
component of the translated triple. -/
theorem isCycleNotation_toTriple_σinf (h : s.IsCycleNotation c) :
    s.toTriple.σinf.IsCycleNotation (c.2.2.map List.reverse) := by
  simpa using h.σinf.inv

/-- The ordered full cycle partitions of the translated triple are the cycle lengths of the stored
cycle notation, each padded by one part equal to one for every point it omits. -/
theorem cycleData_toTriple (h : s.IsCycleNotation c) :
    s.toTriple.cycleData =
      ((c.1.map List.length : Multiset ℕ) + Multiset.replicate (n - (c.1.map List.length).sum) 1,
        (c.2.1.map List.length : Multiset ℕ) +
          Multiset.replicate (n - (c.2.1.map List.length).sum) 1,
        (c.2.2.map List.length : Multiset ℕ) +
          Multiset.replicate (n - (c.2.2.map List.length).sum) 1) := by
  rw [StoredTriple.cycleData_toTriple, h.σ0.parts_partition_eq, h.σ1.parts_partition_eq,
    h.σinf.parts_partition_eq, Fintype.card_fin]

end IsCycleNotation

end StoredTriple

/-! ### Belyi-map records -/

/-- A row of the LMFDB table of Belyi maps in degree `n`, with its stored fields parsed into Lean
data. The row describes one Galois orbit of Belyi maps. Its stored degree is the field `deg`,
which validity identifies with `n`.

The stored triples are kept in the database's convention, as `StoredTriple`s, and are listed
position by position against the stored complex embeddings of the base field: the `i`-th triple
is the monodromy of the map under the `i`-th embedding. The remaining fields are carried as data
and are not interpreted here. -/
structure BelyiRecord (n : ℕ) where
  /-- The stored label of the Galois orbit. -/
  label : String
  /-- The stored label of the passport containing the orbit. -/
  plabel : String
  /-- The stored degree. -/
  deg : ℕ
  /-- The stored full cycle partitions at `0`, `1`, and `∞`, fixed points included. -/
  lambdas : Multiset ℕ × Multiset ℕ × Multiset ℕ
  /-- The stored genus. -/
  g : ℕ
  /-- The stored orbit size. -/
  orbitSize : ℕ
  /-- The stored coefficients, in increasing degree, of a defining polynomial of the base field
  over which the stored equations are written. This is a field of definition of each map in the
  orbit, and is not asserted to be its field of moduli. -/
  baseField : List ℚ
  /-- The stored floating-point values, as real and imaginary parts, of the complex embeddings
  of the base field. -/
  embeddings : List (Float × Float)
  /-- The stored triples, in the database's convention. -/
  triples : List (StoredTriple n)
  /-- The stored triples in cycle notation, parsed into lists of cycles. The notation omits fixed
  points and writes the identity as the empty list of cycles. -/
  triplesCyc : List (CycleNotationTriple n)
  /-- The stored equations of the curve. -/
  curve : String
  /-- The stored formula for the map. -/
  map : String
  /-- The stored plane model of the curve. -/
  planeModel : String
  /-- The stored constant attached to the plane model. -/
  planeConstant : String
  /-- The stored label of the associated curve, absent on rows that have none. -/
  curveLabel : Option String
  /-- The stored labels of related objects. -/
  friends : List String
  /-- The stored triples are indexed by the stored embeddings, position by position. -/
  storedEmbeddingCount_eq_triplesLength : embeddings.length = triples.length

namespace BelyiRecord

variable {n : ℕ} (r : BelyiRecord n)

/-- The number of stored embedding entries of a row. This is a count of stored entries, not the
size of a Galois orbit of isomorphism classes. -/
def storedEmbeddingCount : ℕ := r.embeddings.length

theorem storedEmbeddingCount_def : r.storedEmbeddingCount = r.embeddings.length := (rfl)

/-- The isomorphism classes of the triples denoted by the stored triples. -/
noncomputable def storedClasses : Finset (IsoClass n) := by
  classical
  exact (r.triples.map fun s ↦ IsoClass.mk s.toTriple).toFinset

theorem mem_storedClasses {c : IsoClass n} :
    c ∈ r.storedClasses ↔ ∃ s ∈ r.triples, IsoClass.mk s.toTriple = c := by
  classical
  simp [storedClasses]

/-- The stored triples represent at most as many isomorphism classes as there are stored
embedding entries. The inequality is strict when two stored triples are simultaneously
conjugate. -/
theorem card_storedClasses_le_storedEmbeddingCount :
    r.storedClasses.card ≤ r.storedEmbeddingCount := by
  classical
  rw [storedEmbeddingCount_def, storedEmbeddingCount_eq_triplesLength,
    ← List.length_map (fun s ↦ IsoClass.mk s.toTriple)]
  exact List.toFinset_card_le _

/-- A row is valid for the passport `P` when its stored degree is the degree, its stored orbit
size is its number of stored embedding entries, it stores at least one triple, every stored
triple denotes a connected triple with passport `P`, its stored cycle notation writes the stored
triples position by position, the stored partitions are those of `P`, and the stored genus is the
genus of every stored triple.

The labels, the base field, the equations, and the embedding values are not constrained. -/
structure IsValidFor (P : PassportSpec n) : Prop where
  /-- The stored degree is the degree. -/
  deg_eq : r.deg = n
  /-- The stored orbit size is the number of stored embedding entries. -/
  orbitSize_eq : r.orbitSize = r.storedEmbeddingCount
  /-- At least one triple is stored. -/
  triples_ne_nil : r.triples ≠ []
  /-- Every stored triple denotes a connected triple with passport `P`. -/
  hasPassport :
    ∀ s ∈ r.triples, ∃ hs : s.toTriple.IsConnected, PassportSpec.HasPassport ⟨s.toTriple, hs⟩ P
  /-- The stored cycle notation writes the stored triples, position by position. -/
  forall₂_isCycleNotation :
    List.Forall₂ (fun c s ↦ StoredTriple.IsCycleNotation s c) r.triplesCyc r.triples
  /-- The stored partitions are those of `P`. -/
  lambdas_eq : r.lambdas = (P.lam0, P.lam1, P.laminf)
  /-- The stored genus is the genus of every stored triple. -/
  g_eq : ∀ s ∈ r.triples, r.g = s.toTriple.genus

namespace IsValidFor

variable {r} {P : PassportSpec n} {s : StoredTriple n}

/-- Every stored triple of a valid row denotes a connected triple. -/
theorem isConnected_toTriple (h : r.IsValidFor P) (hs : s ∈ r.triples) :
    s.toTriple.IsConnected :=
  (h.hasPassport s hs).1

/-- The passport of a valid row is admissible. -/
theorem isAdmissible (h : r.IsValidFor P) : P.IsAdmissible := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ h.triples_ne_nil
  obtain ⟨_, hP⟩ := h.hasPassport s hs
  exact PassportSpec.isAdmissible_of_hasPassport hP

/-- The stored orbit size of a valid row is its number of stored triples. -/
theorem orbitSize_eq_length_triples (h : r.IsValidFor P) : r.orbitSize = r.triples.length := by
  rw [h.orbitSize_eq, storedEmbeddingCount_def, storedEmbeddingCount_eq_triplesLength]

/-- The stored orbit size of a valid row is positive. -/
theorem orbitSize_pos (h : r.IsValidFor P) : 0 < r.orbitSize := by
  rw [h.orbitSize_eq_length_triples]
  exact List.length_pos_iff.mpr h.triples_ne_nil

/-- The stored partitions of a valid row are the ordered cycle data of every stored triple. -/
theorem lambdas_eq_cycleData (h : r.IsValidFor P) (hs : s ∈ r.triples) :
    r.lambdas = s.toTriple.cycleData := by
  obtain ⟨hc, hP⟩ := h.hasPassport s hs
  obtain ⟨-, h0, h1, hinf⟩ := (PassportSpec.hasPassport_iff _ P).mp hP
  rw [h.lambdas_eq, ← h0, ← h1, ← hinf]

/-- The stored partitions of a valid row are the full cycle partitions of the stored components
of every stored triple, read in the database's convention. -/
theorem lambdas_eq_partition (h : r.IsValidFor P) (hs : s ∈ r.triples) :
    r.lambdas = (s.1.1.partition.parts, s.1.2.1.partition.parts, s.1.2.2.partition.parts) := by
  rw [h.lambdas_eq_cycleData hs, StoredTriple.cycleData_toTriple]

/-- The stored partitions of a valid row are the cycle types of the stored components, which omit
fixed points, padded by one part equal to one for each fixed point. -/
theorem lambdas_eq_cycleType_add (h : r.IsValidFor P) (hs : s ∈ r.triples) :
    r.lambdas =
      (s.1.1.cycleType + Multiset.replicate (n - s.1.1.support.card) 1,
        s.1.2.1.cycleType + Multiset.replicate (n - s.1.2.1.support.card) 1,
        s.1.2.2.cycleType + Multiset.replicate (n - s.1.2.2.support.card) 1) := by
  rw [h.lambdas_eq_partition hs]
  simp only [Perm.parts_partition, Fintype.card_fin]

/-- A valid row stores one cycle notation for each stored triple. -/
theorem length_triplesCyc (h : r.IsValidFor P) : r.triplesCyc.length = r.triples.length :=
  h.forall₂_isCycleNotation.length_eq

/-- Every stored cycle notation of a valid row writes one of its stored triples. -/
theorem exists_mem_triples_isCycleNotation (h : r.IsValidFor P) {c : CycleNotationTriple n}
    (hc : c ∈ r.triplesCyc) : ∃ s ∈ r.triples, s.IsCycleNotation c := by
  suffices ∀ {l₁ l₂}, List.Forall₂ (fun c s ↦ StoredTriple.IsCycleNotation s c) l₁ l₂ →
      c ∈ l₁ → ∃ s ∈ l₂, s.IsCycleNotation c from this h.forall₂_isCycleNotation hc
  intro l₁ l₂ hF hc
  induction hF with
  | nil => simp at hc
  | @cons c' s' _ _ hcs _ ih =>
    obtain rfl | hc := List.mem_cons.mp hc
    · exact ⟨s', List.mem_cons_self .., hcs⟩
    · obtain ⟨s, hs, hsc⟩ := ih hc
      exact ⟨s, List.mem_cons_of_mem _ hs, hsc⟩

/-- **The stored partitions from the stored cycle notation.** The stored partitions of a valid row
are the cycle lengths of each of its stored cycle notations, padded by one part equal to one for
every omitted fixed point. -/
theorem lambdas_eq_of_mem_triplesCyc (h : r.IsValidFor P) {c : CycleNotationTriple n}
    (hc : c ∈ r.triplesCyc) :
    r.lambdas =
      ((c.1.map List.length : Multiset ℕ) + Multiset.replicate (n - (c.1.map List.length).sum) 1,
        (c.2.1.map List.length : Multiset ℕ) +
          Multiset.replicate (n - (c.2.1.map List.length).sum) 1,
        (c.2.2.map List.length : Multiset ℕ) +
          Multiset.replicate (n - (c.2.2.map List.length).sum) 1) := by
  obtain ⟨s, hs, hsc⟩ := h.exists_mem_triples_isCycleNotation hc
  rw [h.lambdas_eq_cycleData hs, hsc.cycleData_toTriple]

/-- In a valid row, the group generated by the first two stored components of every stored
triple is conjugate to the reference group of the passport. -/
theorem exists_map_closure_eq (h : r.IsValidFor P) (hs : s ∈ r.triples) :
    ∃ τ : Perm (Fin n),
      (Subgroup.closure {s.1.1, s.1.2.1}).map (MulAut.conj τ).toMonoidHom = P.G := by
  obtain ⟨hc, hP⟩ := h.hasPassport s hs
  exact ((StoredTriple.hasPassport_toTriple_iff s hc P).mp hP).1

/-- The stored genus of a valid row, counted on the stored components of any stored triple. -/
theorem g_eq_toNat (h : r.IsValidFor P) (hs : s ∈ r.triples) :
    r.g = ((2 - ((orbitCount s.1.1 : ℤ) + orbitCount s.1.2.1 + orbitCount s.1.2.2 - n)) /
      2).toNat := by
  rw [h.g_eq s hs, StoredTriple.genus_toTriple]

/-- The stored genus of a valid row is the genus of every connected triple with its passport. -/
theorem g_eq_genus (h : r.IsValidFor P) {t : ConnectedTriple n}
    (ht : PassportSpec.HasPassport t P) : r.g = t.1.genus := by
  obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ h.triples_ne_nil
  obtain ⟨_, hP⟩ := h.hasPassport s hs
  rw [h.g_eq s hs]
  exact PassportSpec.genus_eq_of_hasPassport hP ht

/-- Every stored class of a valid row is the class of a connected triple in its passport. -/
theorem exists_mem_classSet_of_mem_storedClasses (h : r.IsValidFor P) {c : IsoClass n}
    (hc : c ∈ r.storedClasses) : ∃ d ∈ P.classSet, d.forget = c := by
  obtain ⟨s, hs, rfl⟩ := (r.mem_storedClasses).mp hc
  obtain ⟨hsc, hP⟩ := h.hasPassport s hs
  exact ⟨ConnectedIsoClass.mk ⟨s.toTriple, hsc⟩,
    PassportSpec.mem_classSet.mpr ((ConnectedIsoClass.hasPassport_mk _ P).mpr hP),
    ConnectedIsoClass.forget_mk _⟩

/-- The stored triples of a valid row represent at most as many isomorphism classes as its
passport contains. -/
theorem card_storedClasses_le_passportSize (h : r.IsValidFor P) :
    r.storedClasses.card ≤ P.passportSize := by
  classical
  calc r.storedClasses.card ≤ (P.classSet.image ConnectedIsoClass.forget).card := by
        refine Finset.card_le_card fun c hc ↦ ?_
        obtain ⟨d, hd, rfl⟩ := h.exists_mem_classSet_of_mem_storedClasses hc
        exact Finset.mem_image_of_mem _ hd
    _ ≤ P.passportSize := by
        rw [PassportSpec.passportSize_def]
        exact Finset.card_image_le

end IsValidFor

/-- Every connected triple is the stored triple of a formal row that is valid for its passport, so
`TauCeti.PermutationTriple.LMFDB.BelyiRecord.IsValidFor` is not vacuous. The row carries
placeholder data in the fields that validity leaves unconstrained: the base-field polynomial
`X - 1` with a single embedding entry, and empty labels and equations. Its cycle notation is some
disjoint cycle notation for the stored triple. It is not a certificate that
the corresponding Belyi map is defined over `ℚ`, which this theorem does not establish. -/
theorem exists_isValidFor (t : ConnectedTriple n) :
    ∃ r : BelyiRecord n,
      r.IsValidFor t.passportOf ∧ r.triples = [equivOppositeConvention n t.1] := by
  obtain ⟨c, hc⟩ := StoredTriple.exists_isCycleNotation (equivOppositeConvention n t.1)
  exact
    ⟨{ label := "", plabel := "", deg := n, lambdas := t.1.cycleData, g := t.1.genus,
        orbitSize := 1, baseField := [-1, 1], embeddings := [(1, 0)],
        triples := [equivOppositeConvention n t.1], triplesCyc := [c], curve := "", map := "",
        planeModel := "", planeConstant := "", curveLabel := none, friends := [],
        storedEmbeddingCount_eq_triplesLength := rfl },
      { deg_eq := rfl
        orbitSize_eq := rfl
        triples_ne_nil := List.cons_ne_nil _ _
        hasPassport := by
          simp only [List.mem_singleton, forall_eq, StoredTriple.toTriple_equivOppositeConvention]
          exact ⟨t.2, t.hasPassport_passportOf⟩
        forall₂_isCycleNotation := .cons hc .nil
        lambdas_eq := by
          rw [t.passportOf_lam0, t.passportOf_lam1, t.passportOf_laminf]
        g_eq := by simp },
    rfl⟩

end BelyiRecord

end LMFDB
end PermutationTriple
end TauCeti
