/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.Label
public import TauCeti.Data.Multiset.Sort

/-!
# Passport records

A passport record mirrors one row of the LMFDB table of Belyi passports: the stored fields
`plabel`, `deg`, `group`, `abc`, `a_s`/`b_s`/`c_s`, `lambdas`, `g`, `geomtype`, `pass_size`,
`num_orbits`, `maxdegbf`, `is_primitive`, `primitivization`, `aut_group` and `triples`, parsed
into Lean data. Two fields carry certificate data besides their stored strings: the
primitivization carries a block of sheets, and the automorphism group carries a list of
generators.

`TauCeti.PermutationTriple.LMFDB.PassportRecord.IsValidAt` states what such a row asserts about
the passport of a connected triple `t`, which must be one of the stored triples and on whose
sheets the certificate data are read. Each field is tied to the invariant it records:

* `deg` is the degree, which is also the index of the record type;
* `lambdas` is the ordered full cycle data of `t`, fixed points included;
* `abc` is the order triple of `t`, in the order `0`, `1`, `∞`, and is not sorted, while the
  search triple `(a_s, b_s, c_s)` is `abc` sorted ascending;
* `g` is the genus, and `geomtype` the geometry type, which is computed from `abc` and is not a
  function of the genus;
* `group` is the number `j` of a transitive-group label `nTj` of the monodromy group, so a valid
  record exists only in a degree with reference groups (`TauCeti.numTransitiveGroups`);
* `pass_size` is the passport size, the number of isomorphism classes of connected triples in the
  passport, rather than a count of stored rows;
* `is_primitive` records primitivity of the monodromy action;
* the primitivization block is a maximal proper block of the monodromy action of `t`;
* the automorphism-group generators generate the automorphism group of `t`;
* every stored triple lies in the passport of `t`.

The aggregations `num_orbits` and `maxdegbf` describe which map rows the table contains, and the
label and name strings are not interpreted here, so validity imposes no condition on them. The
stored primitivization label is tied to the map row it names, through the quotient by the
primitivization block, by `TauCeti.PermutationTriple.LMFDB.BelyiRecord.IsPrimitivizationOf`.

The certified fields other than the certificate data are passport invariants: the theorems below
read them from any connected triple sharing a passport with `t`.

## Main definitions

* `TauCeti.PermutationTriple.LMFDB.PassportRecord`: a parsed passport row.
* `TauCeti.PermutationTriple.LMFDB.PassportRecord.IsValidAt`: validity of a row for the passport
  of a stored reference triple.

## Main results

* `TauCeti.PermutationTriple.LMFDB.PassportRecord.IsValidAt.abc_eq_lcm_lambdas`: each stored order
  is the least common multiple of the corresponding stored partition.
* `TauCeti.PermutationTriple.LMFDB.PassportRecord.IsValidAt.passSize_eq_natCard`: the stored
  passport size counts isomorphism classes.
* `TauCeti.PermutationTriple.LMFDB.PassportRecord.IsValidAt.exists_hasLabel`: the stored group and
  partitions form a label of every passport containing the reference triple.
* `TauCeti.PermutationTriple.LMFDB.PassportRecord.IsValidAt.g_eq_genus` and its companions: the
  certified fields are invariants of the passport.

## References

* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*.
* LMFDB, [Belyi maps](https://www.lmfdb.org/Belyi/).
-/

open Equiv MulAction

public section

namespace TauCeti
namespace PermutationTriple
namespace LMFDB

/-- A row of the LMFDB table of Belyi passports in degree `n`, with its stored fields parsed into
Lean data. The stored degree is the field `deg`, which validity identifies with `n`.

Besides the stored fields, the primitivization and the automorphism group carry certificate data:
a block of sheets and a list of generators, read on the sheets of a stored triple. The stored
triples are recorded in this library's multiplication convention, in which a triple satisfies
`σinf * σ1 * σ0 = 1`. -/
structure PassportRecord (n : ℕ) where
  /-- The stored passport label. It is carried as a string and is not interpreted here. -/
  plabel : String
  /-- The stored degree. -/
  deg : ℕ
  /-- The number `j` of the stored transitive-group label `nTj` of the monodromy group. -/
  group : ℕ
  /-- The stored orders of the monodromy at `0`, `1`, and `∞`, in that order. -/
  abc : ℕ × ℕ × ℕ
  /-- The stored search triple `(a_s, b_s, c_s)` of orders, sorted ascending. -/
  sortedAbc : ℕ × ℕ × ℕ
  /-- The stored full cycle partitions at `0`, `1`, and `∞`, fixed points included. -/
  lambdas : Multiset ℕ × Multiset ℕ × Multiset ℕ
  /-- The stored genus. -/
  g : ℕ
  /-- The stored geometry type. -/
  geomtype : GeometryType
  /-- The stored passport size. -/
  passSize : ℕ
  /-- The stored number of map rows sharing the passport label. -/
  numOrbits : ℕ
  /-- The stored largest orbit size among the map rows sharing the passport label. -/
  maxdegbf : ℕ
  /-- The stored primitivity flag. -/
  isPrimitive : Bool
  /-- The stored label of the primitivization. It is carried as a string. -/
  primitivization : String
  /-- A block of sheets of the reference triple, certifying the primitivization: its translates
  form the block system whose quotient is the primitivization. -/
  primitivizationBlock : Finset (Fin n)
  /-- The stored name of the automorphism group. It is carried as a string. -/
  autGroup : String
  /-- Generators of the automorphism group of the reference triple, certifying `autGroup`. -/
  autGroupGenerators : List (Perm (Fin n))
  /-- The stored permutation triples, in this library's multiplication convention. -/
  triples : List (PermutationTriple n)

namespace PassportRecord

variable {n : ℕ}

/-- The record `r` is a valid row for the passport of the connected triple `t`: the triple `t` is
one of the stored triples, the certificate data of `r` are correct on the sheets of `t`, and every
other certified field is the corresponding invariant of `t`.

The aggregations `numOrbits` and `maxdegbf`, and the strings `plabel`, `primitivization` and
`autGroup`, are not constrained. -/
structure IsValidAt (r : PassportRecord n) (t : ConnectedTriple n) : Prop where
  /-- The stored degree is the degree. -/
  deg_eq : r.deg = n
  /-- The reference triple is one of the stored triples. -/
  mem_triples : t.1 ∈ r.triples
  /-- Every stored triple is connected and lies in the passport of the reference triple. -/
  hasPassport_of_mem_triples :
    ∀ s ∈ r.triples, ∃ hs : s.IsConnected, PassportSpec.HasPassport ⟨s, hs⟩ t.passportOf
  /-- The stored partitions are the ordered full cycle data. -/
  lambdas_eq : r.lambdas = t.1.cycleData
  /-- The stored orders are the order triple, positionally. -/
  abc_eq : r.abc = t.1.orderTriple
  /-- The stored search triple is the stored order triple sorted ascending. -/
  sortedAbc_eq :
    [r.sortedAbc.1, r.sortedAbc.2.1, r.sortedAbc.2.2] =
      ({r.abc.1, r.abc.2.1, r.abc.2.2} : Multiset ℕ).sort
  /-- The stored genus is the genus. -/
  g_eq : r.g = t.1.genus
  /-- The stored geometry type is the geometry type. -/
  geomtype_eq : r.geomtype = t.1.geometryType
  /-- The stored group number displays a transitive-group label of the monodromy group. -/
  exists_transitiveGroupLabel :
    ∃ j : TransitiveGroupIndex n, (j : ℕ) + 1 = r.group ∧
      TransitiveGroupLabel j t.1.monodromyGroup
  /-- The stored passport size is the passport size. -/
  passSize_eq : r.passSize = t.passportOf.passportSize
  /-- The stored primitivity flag is set exactly for a primitive triple. -/
  isPrimitive_eq_true_iff : r.isPrimitive = true ↔ t.1.IsPrimitive
  /-- The primitivization block is a block of the monodromy action. -/
  isBlock_primitivizationBlock :
    IsBlock t.1.monodromyGroup (r.primitivizationBlock : Set (Fin n))
  /-- The primitivization block is nonempty. -/
  primitivizationBlock_nonempty : r.primitivizationBlock.Nonempty
  /-- The primitivization block is proper, unless the degree is one. -/
  deg_eq_one_of_primitivizationBlock_eq_univ : r.primitivizationBlock = Finset.univ → n = 1
  /-- No block lies strictly between the primitivization block and the set of all sheets. -/
  eq_or_eq_univ_of_primitivizationBlock_subset :
    ∀ C : Set (Fin n), IsBlock t.1.monodromyGroup C →
      (r.primitivizationBlock : Set (Fin n)) ⊆ C →
        C = r.primitivizationBlock ∨ C = Set.univ
  /-- The automorphism-group generators generate the automorphism group. -/
  closure_autGroupGenerators :
    Subgroup.closure {τ | τ ∈ r.autGroupGenerators} = t.1.automorphismGroup

namespace IsValidAt

variable {r : PassportRecord n} {t : ConnectedTriple n}

/-- Each stored order is the least common multiple of the stored partition at the same branch
point. -/
theorem abc_eq_lcm_lambdas (h : r.IsValidAt t) :
    r.abc = (r.lambdas.1.lcm, r.lambdas.2.1.lcm, r.lambdas.2.2.lcm) := by
  rw [h.abc_eq, h.lambdas_eq, orderTriple_eq_lcm_cycleData]

/-- The stored search triple is weakly increasing. -/
theorem sortedAbc_le (h : r.IsValidAt t) :
    r.sortedAbc.1 ≤ r.sortedAbc.2.1 ∧ r.sortedAbc.2.1 ≤ r.sortedAbc.2.2 := by
  have hle := ((Multiset.eq_sort_iff _).mp h.sortedAbc_eq).1
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil] at hle
  exact ⟨hle.1.1, hle.2.1⟩

/-- The stored search triple is a rearrangement of the stored order triple. -/
theorem sortedAbc_perm (h : r.IsValidAt t) :
    ({r.sortedAbc.1, r.sortedAbc.2.1, r.sortedAbc.2.2} : Multiset ℕ) =
      {r.abc.1, r.abc.2.1, r.abc.2.2} :=
  ((Multiset.eq_sort_iff _).mp h.sortedAbc_eq).2

/-- The stored geometry type is spherical exactly when the reciprocals of the stored orders sum to
more than one. -/
theorem geomtype_eq_spherical_iff (h : r.IsValidAt t) :
    r.geomtype = .spherical ↔ 1 < (r.abc.1 : ℚ)⁻¹ + (r.abc.2.1 : ℚ)⁻¹ + (r.abc.2.2 : ℚ)⁻¹ := by
  rw [h.geomtype_eq, geometryType_eq_spherical_iff, h.abc_eq, orderTriple_σ0, orderTriple_σ1,
    orderTriple_σinf]

/-- The stored geometry type is Euclidean exactly when the reciprocals of the stored orders sum to
one. -/
theorem geomtype_eq_euclidean_iff (h : r.IsValidAt t) :
    r.geomtype = .euclidean ↔ (r.abc.1 : ℚ)⁻¹ + (r.abc.2.1 : ℚ)⁻¹ + (r.abc.2.2 : ℚ)⁻¹ = 1 := by
  rw [h.geomtype_eq, geometryType_eq_euclidean_iff, h.abc_eq, orderTriple_σ0, orderTriple_σ1,
    orderTriple_σinf]

/-- The stored geometry type is hyperbolic exactly when the reciprocals of the stored orders sum to
less than one. -/
theorem geomtype_eq_hyperbolic_iff (h : r.IsValidAt t) :
    r.geomtype = .hyperbolic ↔ (r.abc.1 : ℚ)⁻¹ + (r.abc.2.1 : ℚ)⁻¹ + (r.abc.2.2 : ℚ)⁻¹ < 1 := by
  rw [h.geomtype_eq, geometryType_eq_hyperbolic_iff, h.abc_eq, orderTriple_σ0, orderTriple_σ1,
    orderTriple_σinf]

/-- The stored passport size is the number of isomorphism classes of connected triples in the
passport. -/
theorem passSize_eq_natCard (h : r.IsValidAt t) :
    r.passSize = Nat.card {c : ConnectedIsoClass n // c.HasPassport t.passportOf} := by
  rw [h.passSize_eq, PassportSpec.passportSize_eq_card_hasPassport]

/-- The stored passport size is the size of every passport containing the reference triple. -/
theorem passSize_eq_passportSize (h : r.IsValidAt t) {P : PassportSpec n}
    (hP : PassportSpec.HasPassport t P) : r.passSize = P.passportSize := by
  obtain ⟨τ, rfl⟩ := (t.hasPassport_iff_exists_conjugate_passportOf P).mp hP
  rw [h.passSize_eq, PassportSpec.passportSize_conjugate]

/-- The stored passport size is positive. -/
theorem passSize_pos (h : r.IsValidAt t) : 0 < r.passSize := by
  rw [h.passSize_eq]
  exact t.passportSize_passportOf_pos

/-- The stored group number and partitions form a label of every passport containing the
reference triple. -/
theorem exists_hasLabel (h : r.IsValidAt t) {P : PassportSpec n}
    (hP : PassportSpec.HasPassport t P) :
    ∃ L : PassportLabel n, L.groupNumber = r.group ∧
      (L.lam0, L.lam1, L.laminf) = r.lambdas ∧ P.HasLabel L := by
  obtain ⟨j, hj, hlabel⟩ := h.exists_transitiveGroupLabel
  refine ⟨⟨j, r.lambdas.1, r.lambdas.2.1, r.lambdas.2.2⟩, ?_, rfl, ?_⟩
  · rw [PassportLabel.groupNumber_def]
    exact hj
  rw [PassportSpec.hasLabel_iff_of_hasPassport hP, h.lambdas_eq]
  exact ⟨hlabel, rfl, rfl, rfl⟩

/-! ### Passport invariance of the certified fields -/

variable {P : PassportSpec n} {t' : ConnectedTriple n}

/-- The stored partitions are the ordered full cycle data of every triple in a passport containing
the reference triple. -/
theorem lambdas_eq_cycleData (h : r.IsValidAt t) (hP : PassportSpec.HasPassport t P)
    (ht' : PassportSpec.HasPassport t' P) : r.lambdas = t'.1.cycleData :=
  h.lambdas_eq.trans (PassportSpec.cycleData_eq_of_hasPassport hP ht')

/-- The stored orders are the order triple of every triple in a passport containing the reference
triple. -/
theorem abc_eq_orderTriple (h : r.IsValidAt t) (hP : PassportSpec.HasPassport t P)
    (ht' : PassportSpec.HasPassport t' P) : r.abc = t'.1.orderTriple :=
  h.abc_eq.trans (PassportSpec.orderTriple_eq_of_hasPassport hP ht')

/-- The stored genus is the genus of every triple in a passport containing the reference triple. -/
theorem g_eq_genus (h : r.IsValidAt t) (hP : PassportSpec.HasPassport t P)
    (ht' : PassportSpec.HasPassport t' P) : r.g = t'.1.genus :=
  h.g_eq.trans (PassportSpec.genus_eq_of_hasPassport hP ht')

/-- The stored geometry type is the geometry type of every triple in a passport containing the
reference triple. -/
theorem geomtype_eq_geometryType (h : r.IsValidAt t) (hP : PassportSpec.HasPassport t P)
    (ht' : PassportSpec.HasPassport t' P) : r.geomtype = t'.1.geometryType :=
  h.geomtype_eq.trans (PassportSpec.geometryType_eq_of_hasPassport hP ht')

/-- The stored group number displays a transitive-group label of the monodromy group of every
triple in a passport containing the reference triple. -/
theorem exists_transitiveGroupLabel_of_hasPassport (h : r.IsValidAt t)
    (hP : PassportSpec.HasPassport t P) (ht' : PassportSpec.HasPassport t' P) :
    ∃ j : TransitiveGroupIndex n, (j : ℕ) + 1 = r.group ∧
      TransitiveGroupLabel j t'.1.monodromyGroup := by
  obtain ⟨L, hL, -, hlabel⟩ := h.exists_hasLabel hP
  rw [PassportLabel.groupNumber_def] at hL
  exact ⟨L.group, hL, ((PassportSpec.hasLabel_iff_of_hasPassport ht' L).mp hlabel).1⟩

/-- The stored primitivity flag is set exactly when a triple in a passport containing the reference
triple is primitive. -/
theorem isPrimitive_eq_true_iff_of_hasPassport (h : r.IsValidAt t)
    (hP : PassportSpec.HasPassport t P) (ht' : PassportSpec.HasPassport t' P) :
    r.isPrimitive = true ↔ t'.1.IsPrimitive :=
  h.isPrimitive_eq_true_iff.trans (PassportSpec.isPrimitive_iff_of_hasPassport hP ht')

end IsValidAt

end PassportRecord

end LMFDB
end PermutationTriple
end TauCeti
