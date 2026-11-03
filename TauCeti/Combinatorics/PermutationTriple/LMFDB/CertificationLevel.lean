/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.LMFDB.BelyiRecord
public import TauCeti.Combinatorics.PermutationTriple.LMFDB.PassportRecord.Basic

/-!
# Certification levels of the stored fields of LMFDB Belyi records

A row of the LMFDB tables of Belyi passports or Belyi maps stores many fields, and they are not all
certified in the same way. This file classifies every stored field of a passport row
(`TauCeti.PermutationTriple.LMFDB.PassportRecord`) and of a map row
(`TauCeti.PermutationTriple.LMFDB.BelyiRecord`) into exactly one
`TauCeti.PermutationTriple.LMFDB.CertificationLevel`, so that no consumer reads more into a record
than it asserts:

* an *intrinsic theorem* is a value determined by the passport alone;
* a *finite certificate* is checked against finite data supplied with the row;
* an *orbit certificate* needs supplied Galois or descent data;
* a *frozen-table aggregation* is a statement about a set of stored rows, asserting nothing
  intrinsic about any one row;
* a *carrier-only* field has a described meaning but no certified value;
* *outside scope* is a computational or completeness claim that is not proved.

The stored fields are enumerated by `TauCeti.PermutationTriple.LMFDB.PassportRecord.StoredField`
and `TauCeti.PermutationTriple.LMFDB.BelyiRecord.StoredField`, each with the type it is parsed into
and its value in a row. The classification is backed by theorems: every valid row of one passport
stores the same value in each intrinsic field, and validity of a row reads only its intrinsic and
finite-certificate fields, together with the certificate data that no stored field carries.

The two aggregations of a passport row are certified against a list of map rows
(`TauCeti.PermutationTriple.LMFDB.PassportRecord.IsAggregatedFrom`): `num_orbits` is the number of
map rows carrying the passport label, and `maxdegbf` is the largest stored orbit size among them.
The stored orbit sizes count stored embedding entries rather than isomorphism classes, so their sum
is not asserted to be the passport size: the stored triples of these rows represent at most as many
classes as there are stored entries, and at most as many as the passport has, and either bound can
be strict.

## The classification tables

The classification is a table with one row per stored field and five columns, kept in Lean: each
constructor of `StoredField` is a row, `StoredField.Carrier` is the parsed carrier,
`StoredField.certificationLevel` the level, and the docstring of the constructor gives the
mathematical meaning, the exact certificate data, and the theorem relating the field to the
mathematics. A carrier-only field names no theorem, and that absence is the point.

The equality of the stored orbit size of a map row with the size of the Galois orbit of its
isomorphism classes is a separate orbit certificate, which a map row does not carry. The trailing
letter of a map label enumerates the Galois orbits of a passport in an order chosen by the database,
and is carrier only.

## Main definitions

* `TauCeti.PermutationTriple.LMFDB.CertificationLevel`: the six certification levels.
* `TauCeti.PermutationTriple.LMFDB.PassportRecord.StoredField.certificationLevel` and
  `TauCeti.PermutationTriple.LMFDB.BelyiRecord.StoredField.certificationLevel`: the
  classification of the stored fields.
* `TauCeti.PermutationTriple.LMFDB.PassportRecord.IsAggregatedFrom`: the aggregations of a passport
  row, computed from a list of map rows.

## Main results

* `TauCeti.PermutationTriple.LMFDB.PassportRecord.StoredField.get_eq_of_isValidAt` and
  `TauCeti.PermutationTriple.LMFDB.BelyiRecord.StoredField.get_eq_of_isValidFor`: valid rows of
  one passport agree on every intrinsic field.
* `TauCeti.PermutationTriple.LMFDB.PassportRecord.isValidAt_congr` and
  `TauCeti.PermutationTriple.LMFDB.BelyiRecord.isValidFor_congr`: validity reads only the intrinsic
  and finite-certificate fields, and the certificate data.
* `TauCeti.PermutationTriple.LMFDB.PassportRecord.card_mapRowClasses_le_sum_storedEmbeddingCount`
  and `TauCeti.PermutationTriple.LMFDB.PassportRecord.IsValidAt.card_mapRowClasses_le_passSize`:
  the classes stored in the map rows of a passport are at most the stored embedding entries, and
  at most the passport size.

## References

* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*, Proceedings of the
  Thirteenth Algorithmic Number Theory Symposium, Open Book Series 2, 2019, §2.
* LMFDB, [Belyi maps](https://www.lmfdb.org/Belyi/).
-/

open Equiv

public section

namespace TauCeti
namespace PermutationTriple
namespace LMFDB

/-- The level at which a stored field of an LMFDB Belyi record is certified. -/
inductive CertificationLevel : Type
  /-- The value is determined by the passport alone: every valid row of the passport stores it. -/
  | intrinsicTheorem
  /-- The value is checked against finite data supplied with the row, such as a conjugating
  permutation or a block of sheets. -/
  | finiteCertificate
  /-- The value needs supplied Galois or descent data. -/
  | orbitCertificate
  /-- The value is a statement about a set of stored rows: it is true of the table and asserts
  nothing intrinsic about any one row. -/
  | frozenTableAggregation
  /-- The meaning of the value is described, but no value is certified. -/
  | carrierOnly
  /-- The value is a computational or completeness claim that is not proved. -/
  | outsideScope
  deriving DecidableEq, Repr

namespace PassportRecord

/-- The stored fields of a row of the LMFDB table of Belyi passports. The stored search orders
`a_s`, `b_s`, `c_s` form the single field `sortedAbc`. -/
inductive StoredField : Type
  /-- `plabel`, the passport label. No value is certified; label semantics are separate. -/
  | plabel
  /-- `deg`, the degree. Theorem: `IsValidAt.deg_eq`. -/
  | deg
  /-- `group`, the number `j` of the transitive-group label `nTj` of the monodromy group.
  Certificate data: a permutation conjugating the monodromy group onto the reference group with
  index `j - 1`. Theorem: `IsValidAt.exists_transitiveGroupLabel_of_hasPassport`. -/
  | group
  /-- `abc`, the orders at `0`, `1`, and `∞`, in that order. Theorems:
  `IsValidAt.abc_eq_orderTriple` and `IsValidAt.abc_eq_lcm_lambdas`. -/
  | abc
  /-- `a_s`, `b_s`, `c_s`, the orders sorted ascending. Theorems: `IsValidAt.sortedAbc_perm` and
  `IsValidAt.sortedAbc_le`. -/
  | sortedAbc
  /-- `lambdas`, the full cycle partitions, fixed points included. Theorem:
  `IsValidAt.lambdas_eq_cycleData`. -/
  | lambdas
  /-- `g`, the genus. Theorem: `IsValidAt.g_eq_genus`. -/
  | g
  /-- `geomtype`, the geometry type, computed from `abc`. Theorem:
  `IsValidAt.geomtype_eq_geometryType`. -/
  | geomtype
  /-- `pass_size`, the number of isomorphism classes of connected triples in the passport.
  Theorems: `IsValidAt.passSize_eq_passportSize` and `IsValidAt.passSize_eq_natCard`. -/
  | passSize
  /-- `num_orbits`, the number of map rows carrying the passport label. Certificate data: the map
  rows. Theorem: `IsAggregatedFrom.numOrbits_eq`. -/
  | numOrbits
  /-- `maxdegbf`, the largest stored orbit size among the map rows carrying the passport label. It
  is not a degree of a field. Certificate data: the map rows. Theorem:
  `IsAggregatedFrom.maxdegbf_le_iff`. -/
  | maxdegbf
  /-- `is_primitive`, primitivity of the monodromy action. Theorem:
  `IsValidAt.isPrimitive_eq_true_iff_of_hasPassport`. -/
  | isPrimitive
  /-- `primitivization`, the label of a map row for the quotient by a maximal block system.
  Certificate data: the primitivization block, and a map row valid for the passport of the
  quotient. Theorem: `BelyiRecord.IsPrimitivizationOf`. -/
  | primitivization
  /-- `aut_group`, the name of the automorphism group. No value is certified: the name is not
  parsed into a group, so it is not related to the automorphism-group generators of the row. -/
  | autGroup
  /-- `triples`, triples in the passport. Certificate data: the stored triples themselves. Theorem:
  `IsValidAt.hasPassport_of_mem_triples`. -/
  | triples
  deriving DecidableEq, Repr

namespace StoredField

variable {n : ℕ}

/-- The type into which a stored field of a passport row of degree `n` is parsed. -/
@[expose] def Carrier (n : ℕ) : StoredField → Type
  | plabel | primitivization | autGroup => String
  | deg | group | g | passSize | numOrbits | maxdegbf => ℕ
  | abc | sortedAbc => ℕ × ℕ × ℕ
  | lambdas => Multiset ℕ × Multiset ℕ × Multiset ℕ
  | geomtype => GeometryType
  | isPrimitive => Bool
  | triples => List (PermutationTriple n)

/-- The value of a stored field in a passport row. -/
@[expose] def get : (f : StoredField) → PassportRecord n → f.Carrier n
  | plabel, r => r.plabel
  | deg, r => r.deg
  | group, r => r.group
  | abc, r => r.abc
  | sortedAbc, r => r.sortedAbc
  | lambdas, r => r.lambdas
  | g, r => r.g
  | geomtype, r => r.geomtype
  | passSize, r => r.passSize
  | numOrbits, r => r.numOrbits
  | maxdegbf, r => r.maxdegbf
  | isPrimitive, r => r.isPrimitive
  | primitivization, r => r.primitivization
  | autGroup, r => r.autGroup
  | triples, r => r.triples

/-- The certification level of each stored field of a passport row. The invariants of the passport
are intrinsic theorems; the transitive-group number, the primitivization and the stored triples are
finite certificates; the number of map rows and their largest orbit size are frozen-table
aggregations; and the passport label and the name of the automorphism group are carrier only. -/
@[expose] def certificationLevel : StoredField → CertificationLevel
  | deg | abc | sortedAbc | lambdas | g | geomtype | passSize | isPrimitive => .intrinsicTheorem
  | group | primitivization | triples => .finiteCertificate
  | numOrbits | maxdegbf => .frozenTableAggregation
  | plabel | autGroup => .carrierOnly

/-- **Intrinsic fields are passport invariants.** Two rows valid at triples sharing a passport store
the same value in every field whose certification level is an intrinsic theorem. -/
theorem get_eq_of_isValidAt {f : StoredField} (hf : f.certificationLevel = .intrinsicTheorem)
    {r r' : PassportRecord n} {t t' : ConnectedTriple n} {P : PassportSpec n}
    (hr : r.IsValidAt t) (hr' : r'.IsValidAt t') (hP : PassportSpec.HasPassport t P)
    (hP' : PassportSpec.HasPassport t' P) : f.get r = f.get r' := by
  have habc : r.abc = r'.abc := (hr.abc_eq_orderTriple hP hP').trans hr'.abc_eq.symm
  cases f <;> simp only [certificationLevel, reduceCtorEq] at hf <;> simp only [get]
  · exact hr.deg_eq.trans hr'.deg_eq.symm
  · exact habc
  · -- Both sorted triples are the sorting of the same stored orders.
    have h := hr.sortedAbc_eq
    rw [habc, ← hr'.sortedAbc_eq] at h
    simp only [List.cons.injEq, and_true] at h
    exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
  · exact (hr.lambdas_eq_cycleData hP hP').trans hr'.lambdas_eq.symm
  · exact (hr.g_eq_genus hP hP').trans hr'.g_eq.symm
  · exact (hr.geomtype_eq_geometryType hP hP').trans hr'.geomtype_eq.symm
  · exact (hr.passSize_eq_passportSize hP).trans (hr'.passSize_eq_passportSize hP').symm
  · exact Bool.eq_iff_iff.mpr
      ((hr.isPrimitive_eq_true_iff_of_hasPassport hP hP').trans hr'.isPrimitive_eq_true_iff.symm)

end StoredField

variable {n : ℕ}

/-- **Validity reads only certified fields.** Two passport rows that agree on every intrinsic and
finite-certificate field other than the primitivization label, and on the primitivization block and
the automorphism-group generators, are valid at the same triples: validity does not read the
aggregations, the carrier-only passport label, the name of the automorphism group, or the
primitivization label, which is certified separately by `BelyiRecord.IsPrimitivizationOf`. -/
theorem isValidAt_congr {r r' : PassportRecord n}
    (h : ∀ f : StoredField, f ≠ .primitivization → f.certificationLevel = .intrinsicTheorem ∨
      f.certificationLevel = .finiteCertificate → f.get r = f.get r')
    (hblock : r.primitivizationBlock = r'.primitivizationBlock)
    (hgen : r.autGroupGenerators = r'.autGroupGenerators) {t : ConnectedTriple n} :
    r.IsValidAt t ↔ r'.IsValidAt t := by
  have hdeg : r.deg = r'.deg := h .deg nofun (.inl rfl)
  have hgroup : r.group = r'.group := h .group nofun (.inr rfl)
  have habc : r.abc = r'.abc := h .abc nofun (.inl rfl)
  have hsorted : r.sortedAbc = r'.sortedAbc := h .sortedAbc nofun (.inl rfl)
  have hlambdas : r.lambdas = r'.lambdas := h .lambdas nofun (.inl rfl)
  have hg : r.g = r'.g := h .g nofun (.inl rfl)
  have hgeom : r.geomtype = r'.geomtype := h .geomtype nofun (.inl rfl)
  have hpass : r.passSize = r'.passSize := h .passSize nofun (.inl rfl)
  have hprim : r.isPrimitive = r'.isPrimitive := h .isPrimitive nofun (.inl rfl)
  have htriples : r.triples = r'.triples := h .triples nofun (.inr rfl)
  cases r
  cases r'
  dsimp only at hdeg hgroup habc hsorted hlambdas hg hgeom hpass hprim htriples hblock hgen
  subst hdeg hgroup habc hsorted hlambdas hg hgeom hpass hprim htriples hblock hgen
  -- The two rows now differ only in fields that validity does not read.
  exact ⟨fun hv ↦ { hv with }, fun hv ↦ { hv with }⟩

/-! ### Aggregations over the map rows of a passport -/

/-- The map rows among `rows` that carry the passport label of the passport row `r`. -/
def mapRows (r : PassportRecord n) (rows : List (BelyiRecord n)) : List (BelyiRecord n) :=
  rows.filter fun q ↦ q.plabel = r.plabel

@[simp] theorem mem_mapRows {r : PassportRecord n} {rows : List (BelyiRecord n)}
    {q : BelyiRecord n} : q ∈ r.mapRows rows ↔ q ∈ rows ∧ q.plabel = r.plabel := by
  simp [mapRows]

/-- The aggregations of the passport row `r` are computed from the map rows `rows` of the table:
the stored number of orbits is the number of map rows carrying the passport label, and `maxdegbf`
is the largest stored orbit size among them, or `0` if there are none. -/
structure IsAggregatedFrom (r : PassportRecord n) (rows : List (BelyiRecord n)) : Prop where
  /-- The stored number of orbits is the number of map rows carrying the passport label. -/
  numOrbits_eq : r.numOrbits = (r.mapRows rows).length
  /-- `maxdegbf` is the largest stored orbit size among the map rows carrying the passport label. -/
  maxdegbf_eq : r.maxdegbf = ((r.mapRows rows).map BelyiRecord.orbitSize).foldr max 0

namespace IsAggregatedFrom

variable {r : PassportRecord n} {rows : List (BelyiRecord n)}

/-- `maxdegbf` is the least upper bound of the stored orbit sizes of the map rows carrying the
passport label. -/
theorem maxdegbf_le_iff (h : r.IsAggregatedFrom rows) {a : ℕ} :
    r.maxdegbf ≤ a ↔ ∀ q ∈ r.mapRows rows, q.orbitSize ≤ a := by
  rw [h.maxdegbf_eq]
  refine ⟨fun ha q hq ↦ (List.le_max_of_le' 0 (List.mem_map_of_mem hq) le_rfl).trans ha,
    fun ha ↦ List.max_le_of_forall_le _ _ fun x hx ↦ ?_⟩
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  exact ha q hq

/-- The stored orbit size of every map row carrying the passport label is at most `maxdegbf`. -/
theorem orbitSize_le_maxdegbf (h : r.IsAggregatedFrom rows) {q : BelyiRecord n}
    (hq : q ∈ r.mapRows rows) : q.orbitSize ≤ r.maxdegbf :=
  (h.maxdegbf_le_iff.mp le_rfl) q hq

end IsAggregatedFrom

/-- The isomorphism classes denoted by the stored triples of the map rows among `rows` that carry
the passport label of `r`. -/
noncomputable def mapRowClasses (r : PassportRecord n) (rows : List (BelyiRecord n)) :
    Finset (IsoClass n) := by
  classical
  exact (((r.mapRows rows).flatMap BelyiRecord.triples).map fun s ↦ IsoClass.mk s.toTriple).toFinset

@[simp] theorem mem_mapRowClasses {r : PassportRecord n} {rows : List (BelyiRecord n)}
    {c : IsoClass n} : c ∈ r.mapRowClasses rows ↔ ∃ q ∈ r.mapRows rows, c ∈ q.storedClasses := by
  classical
  simp only [mapRowClasses, List.mem_toFinset, List.mem_map, List.mem_flatMap,
    BelyiRecord.mem_storedClasses]
  constructor
  · rintro ⟨s, ⟨q, hq, hs⟩, rfl⟩
    exact ⟨q, hq, s, hs, rfl⟩
  · rintro ⟨q, hq, s, hs, rfl⟩
    exact ⟨s, ⟨q, hq, hs⟩, rfl⟩

/-- The stored triples of the map rows of a passport represent at most as many isomorphism classes
as the rows have stored embedding entries in total. The inequality is strict when two stored
entries are simultaneously conjugate, so the sum of the stored orbit sizes is not a count of
classes. -/
theorem card_mapRowClasses_le_sum_storedEmbeddingCount (r : PassportRecord n)
    (rows : List (BelyiRecord n)) :
    (r.mapRowClasses rows).card ≤
      ((r.mapRows rows).map BelyiRecord.storedEmbeddingCount).sum := by
  classical
  refine (List.toFinset_card_le _).trans_eq ?_
  rw [List.length_map, List.length_flatMap]
  congr 1
  refine List.map_congr_left fun q _ ↦ ?_
  rw [BelyiRecord.storedEmbeddingCount_def, BelyiRecord.storedEmbeddingCount_eq_triplesLength]

/-- If the passport row `r` is valid at `t` and every map row carrying its label is valid for a
passport containing `t`, then the stored triples of these map rows represent at most `pass_size`
isomorphism classes. Equality would say that the table holds every class of the passport, which no
row asserts. -/
theorem IsValidAt.card_mapRowClasses_le_passSize {r : PassportRecord n}
    {rows : List (BelyiRecord n)} {t : ConnectedTriple n} {P : PassportSpec n}
    (hr : r.IsValidAt t) (hP : PassportSpec.HasPassport t P)
    (hrows : ∀ q ∈ r.mapRows rows, q.IsValidFor P) :
    (r.mapRowClasses rows).card ≤ r.passSize := by
  classical
  rw [hr.passSize_eq_passportSize hP, PassportSpec.passportSize_def]
  refine (Finset.card_le_card fun c hc ↦ ?_).trans
    (Finset.card_image_le (f := ConnectedIsoClass.forget))
  obtain ⟨q, hq, hc⟩ := mem_mapRowClasses.mp hc
  obtain ⟨d, hd, rfl⟩ := (hrows q hq).exists_mem_classSet_of_mem_storedClasses hc
  exact Finset.mem_image_of_mem ConnectedIsoClass.forget hd

end PassportRecord

namespace BelyiRecord

/-- The stored fields of a row of the LMFDB table of Belyi maps. -/
inductive StoredField : Type
  /-- `label`, the label of the Galois orbit. No value is certified: its trailing letter is an
  enumeration chosen by the database. -/
  | label
  /-- `plabel`, the passport label. No value is certified; label semantics are separate. -/
  | plabel
  /-- `deg`, the degree. Theorem: `IsValidFor.deg_eq`. -/
  | deg
  /-- `lambdas`, the full cycle partitions, fixed points included. Theorems:
  `IsValidFor.lambdas_eq_cycleData` and `IsValidFor.lambdas_eq_partition`. -/
  | lambdas
  /-- `g`, the genus. Theorem: `IsValidFor.g_eq_genus`. -/
  | g
  /-- `orbit_size`, the number of stored embedding entries, which may exceed the number of
  isomorphism classes in the Galois orbit. Certificate data: the stored embedding entries.
  Theorems: `IsValidFor.orbitSize_eq` and `IsValidFor.orbitSize_eq_length_triples`. -/
  | orbitSize
  /-- `base_field`, a field of definition of each map in the orbit, not asserted to be its field of
  moduli. Certificate data: a model over the field with its base-change isomorphisms, which the row
  does not carry. -/
  | baseField
  /-- `embeddings`, floating-point values of the complex embeddings of the base field. No value is
  certified; their number is read by the orbit size. -/
  | embeddings
  /-- `triples`, the monodromy triples under the stored embeddings, in the database's convention.
  Certificate data: the stored triples themselves. Theorems: `IsValidFor.hasPassport` and
  `IsValidFor.card_storedClasses_le_passportSize`. -/
  | triples
  /-- `triples_cyc`, the stored triples in disjoint cycle notation. Certificate data: the stored
  notation. Theorems: `IsValidFor.forall₂_isCycleNotation` and
  `IsValidFor.lambdas_eq_of_mem_triplesCyc`. -/
  | triplesCyc
  /-- `curve`, the equations of the curve. Without a parse into an algebraic Belyi pair, no value
  is certified. -/
  | curve
  /-- `map`, the formula for the map. Without a parse into an algebraic Belyi pair, no value is
  certified. -/
  | map
  /-- `plane_model`, a plane model of the curve. No value is certified. -/
  | planeModel
  /-- `plane_constant`, the constant attached to the plane model. No value is certified. -/
  | planeConstant
  /-- `curve_label`, the label of an associated curve, absent on rows that have none. No value is
  certified. -/
  | curveLabel
  /-- `friends`, the labels of related objects. No value is certified. -/
  | friends
  deriving DecidableEq, Repr

namespace StoredField

variable {n : ℕ}

/-- The type into which a stored field of a map row of degree `n` is parsed. -/
@[expose] def Carrier (n : ℕ) : StoredField → Type
  | label | plabel | curve | map | planeModel | planeConstant => String
  | deg | g | orbitSize => ℕ
  | lambdas => Multiset ℕ × Multiset ℕ × Multiset ℕ
  | baseField => List ℚ
  | embeddings => List (Float × Float)
  | triples => List (StoredTriple n)
  | triplesCyc => List (CycleNotationTriple n)
  | curveLabel => Option String
  | friends => List String

/-- The value of a stored field in a map row. -/
@[expose] def get : (f : StoredField) → BelyiRecord n → f.Carrier n
  | label, r => r.label
  | plabel, r => r.plabel
  | deg, r => r.deg
  | lambdas, r => r.lambdas
  | g, r => r.g
  | orbitSize, r => r.orbitSize
  | baseField, r => r.baseField
  | embeddings, r => r.embeddings
  | triples, r => r.triples
  | triplesCyc, r => r.triplesCyc
  | curve, r => r.curve
  | map, r => r.map
  | planeModel, r => r.planeModel
  | planeConstant, r => r.planeConstant
  | curveLabel, r => r.curveLabel
  | friends, r => r.friends

/-- The certification level of each stored field of a map row. The degree, partitions and genus are
intrinsic theorems; the orbit size, read as the number of stored embedding entries, and the stored
triples in both notations are finite certificates; the base field, a field of definition, is an
orbit certificate; and the labels, the embedding values, the equations and the links are carrier
only. -/
@[expose] def certificationLevel : StoredField → CertificationLevel
  | deg | lambdas | g => .intrinsicTheorem
  | orbitSize | triples | triplesCyc => .finiteCertificate
  | baseField => .orbitCertificate
  | label | plabel | embeddings | curve | map | planeModel | planeConstant | curveLabel | friends =>
    .carrierOnly

/-- **Intrinsic fields are passport invariants.** Two map rows valid for the same passport store the
same value in every field whose certification level is an intrinsic theorem. -/
theorem get_eq_of_isValidFor {f : StoredField} (hf : f.certificationLevel = .intrinsicTheorem)
    {r r' : BelyiRecord n} {P : PassportSpec n} (hr : r.IsValidFor P) (hr' : r'.IsValidFor P) :
    f.get r = f.get r' := by
  cases f <;> simp only [certificationLevel, reduceCtorEq] at hf <;> simp only [get]
  · exact hr.deg_eq.trans hr'.deg_eq.symm
  · exact hr.lambdas_eq.trans hr'.lambdas_eq.symm
  · obtain ⟨s, hs⟩ := List.exists_mem_of_ne_nil _ hr'.triples_ne_nil
    obtain ⟨hsc, hsP⟩ := hr'.hasPassport s hs
    exact (hr.g_eq_genus hsP).trans (hr'.g_eq_genus hsP).symm

end StoredField

variable {n : ℕ}

/-- **Validity reads only certified fields.** Two map rows that agree on every intrinsic and
finite-certificate field are valid for the same passports: validity does not read the base field,
the embedding values, or any carrier-only field. -/
theorem isValidFor_congr {r r' : BelyiRecord n}
    (h : ∀ f : StoredField, f.certificationLevel = .intrinsicTheorem ∨
      f.certificationLevel = .finiteCertificate → f.get r = f.get r')
    {P : PassportSpec n} : r.IsValidFor P ↔ r'.IsValidFor P := by
  have hdeg : r.deg = r'.deg := h .deg (.inl rfl)
  have hlambdas : r.lambdas = r'.lambdas := h .lambdas (.inl rfl)
  have hg : r.g = r'.g := h .g (.inl rfl)
  have horbit : r.orbitSize = r'.orbitSize := h .orbitSize (.inr rfl)
  have htriples : r.triples = r'.triples := h .triples (.inr rfl)
  have hcyc : r.triplesCyc = r'.triplesCyc := h .triplesCyc (.inr rfl)
  -- The embedding values may differ, but both rows have one entry per stored triple.
  have hcount : r.storedEmbeddingCount = r'.storedEmbeddingCount := by
    rw [storedEmbeddingCount_def, storedEmbeddingCount_def, storedEmbeddingCount_eq_triplesLength,
      storedEmbeddingCount_eq_triplesLength, htriples]
  constructor <;> rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩ <;>
    exact ⟨hdeg ▸ h1, horbit ▸ hcount ▸ h2, htriples ▸ h3, htriples ▸ h4, hcyc ▸ htriples ▸ h5,
      hlambdas ▸ h6, hg ▸ htriples ▸ h7⟩

end BelyiRecord

end LMFDB
end PermutationTriple
end TauCeti
