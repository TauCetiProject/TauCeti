/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.Passport.Label
public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.String
import Std.Data.String.ToNat

/-!
# Parsing Belyi passport and map labels

A passport label has the form `nTj-lambda0_lambda1_lambdainf`, with dot-separated positive
cycle lengths in each partition. The three partitions are ordered by the branch points
`0`, `1`, and `∞`, and include fixed points. Parsing checks that each partition sums to the
degree and uses the transitive-group recognizer for the group component. Decimal tokens must
have their canonical spelling, without leading zeroes or whitespace. Parts may be written in
any order: the mathematical output is a multiset.

A map label appends a nonempty lowercase orbit identifier. This identifier is retained as
external data, not interpreted as a Galois invariant. Neither parser asserts existence of a
triple with the given passport.

## References

* LMFDB, *Belyi map labels*, https://www.lmfdb.org/knowledge/show/belyi.label.
* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*, §2.
-/

public section

namespace TauCeti.PermutationTriple.LMFDB

/-- Parse dot-separated cycle lengths, requiring positive parts summing to `n`.
The order of the parts is forgotten, but parts equal to one are retained. -/
def parseCyclePartition (n : ℕ) (s : String) : Option (Multiset ℕ) :=
  (((s.toList.splitOn '.').map String.ofList).mapM String.toNat?).bind fun parts =>
    if parts.sum = n ∧ (∀ a ∈ parts, 0 < a) ∧
        parts.map toString = (s.toList.splitOn '.').map String.ofList then
      some (parts : Multiset ℕ)
    else none

/-- A cycle partition is accepted exactly when its tokens are canonical decimal spellings
of positive parts summing to the degree. This includes both soundness and completeness. -/
@[simp] theorem parseCyclePartition_eq_some_iff {n : ℕ} {s : String} {m : Multiset ℕ} :
    parseCyclePartition n s = some m ↔
      ∃ parts : List ℕ,
        (s.toList.splitOn '.').map String.ofList = parts.map toString ∧
          parts.sum = n ∧ (∀ a ∈ parts, 0 < a) ∧ (parts : Multiset ℕ) = m := by
  simp only [parseCyclePartition, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨parts, -, h⟩
    split_ifs at h with hv
    exact ⟨parts, hv.2.2.symm, hv.1, hv.2.1, Option.some.inj h⟩
  · rintro ⟨parts, htokens, hs, hpos, rfl⟩
    have hparse (xs : List ℕ) : (xs.map toString).mapM String.toNat? = some xs := by
      simp only [List.mapM_map, Function.comp_def, Nat.toString_eq_repr, Nat.toNat?_repr]
      simpa only [List.map_id, Option.pure_def, id_eq] using
        (List.mapM_pure (m := Option) (l := xs) (f := id))
    exact ⟨parts, by rw [htokens, hparse],
      by rw [ite_eq_left ⟨hs, hpos, htokens.symm⟩]⟩

/-- A successfully parsed partition has positive parts and total degree `n`. -/
theorem sum_eq_and_pos_of_parseCyclePartition_eq_some {n : ℕ} {s : String}
    {m : Multiset ℕ} (h : parseCyclePartition n s = some m) :
    m.sum = n ∧ ∀ a ∈ m, 0 < a := by
  obtain ⟨parts, -, hs, hpos, rfl⟩ := parseCyclePartition_eq_some_iff.mp h
  exact ⟨hs, hpos⟩

/-- Parse the full passport label, not merely its `nTj` component.
The degree and group index must be supported by the reference transitive-group API. -/
def parsePassportLabel (n : ℕ) (s : String) : Option (PassportLabel n) :=
  match (s.toList.splitOn '-').map String.ofList with
  | [group, partitions] =>
    match (partitions.toList.splitOn '_').map String.ofList with
    | [s0, s1, sinf] =>
      (parseTransitiveGroupLabel n group).bind fun j =>
      (parseCyclePartition n s0).bind fun m0 =>
      (parseCyclePartition n s1).bind fun m1 =>
      (parseCyclePartition n sinf).map fun minf => ⟨j, m0, m1, minf⟩
    | _ => none
  | _ => none

/-- Exact grammar and componentwise acceptance criterion for a passport label. -/
@[simp] theorem parsePassportLabel_eq_some_iff {n : ℕ} {s : String} {L : PassportLabel n} :
    parsePassportLabel n s = some L ↔
      ∃ group partitions s0 s1 sinf,
        (s.toList.splitOn '-').map String.ofList = [group, partitions] ∧
        (partitions.toList.splitOn '_').map String.ofList = [s0, s1, sinf] ∧
        parseTransitiveGroupLabel n group = some L.group ∧
        parseCyclePartition n s0 = some L.lam0 ∧
        parseCyclePartition n s1 = some L.lam1 ∧
        parseCyclePartition n sinf = some L.laminf := by
  unfold parsePassportLabel
  split <;> try (solve | simp_all)
  simp_all only [List.cons.injEq, and_true, exists_and_left, ↓existsAndEq, true_and]
  split <;> try (solve | simp_all)
  simp_all only [Option.bind_eq_some_iff, Option.map_eq_some_iff, List.cons.injEq,
    and_true, ↓existsAndEq, true_and]
  constructor
  · rintro ⟨j, hj, m0, h0, m1, h1, minf, hinf, hL⟩
    cases hL
    exact ⟨hj, h0, h1, hinf⟩
  · rintro ⟨hj, h0, h1, hinf⟩
    exact ⟨L.group, hj, L.lam0, h0, L.lam1, h1, L.laminf, hinf, rfl⟩

/-- Each ordered partition of a parsed passport label is a partition of the degree. -/
theorem partitions_of_parsePassportLabel_eq_some {n : ℕ} {s : String}
    {L : PassportLabel n} (h : parsePassportLabel n s = some L) :
    ∀ m ∈ [L.lam0, L.lam1, L.laminf], m.sum = n ∧ ∀ a ∈ m, 0 < a := by
  obtain ⟨_, _, _, _, _, -, -, -, h0, h1, hinf⟩ := parsePassportLabel_eq_some_iff.mp h
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro m (rfl | rfl | rfl)
  · exact sum_eq_and_pos_of_parseCyclePartition_eq_some h0
  · exact sum_eq_and_pos_of_parseCyclePartition_eq_some h1
  · exact sum_eq_and_pos_of_parseCyclePartition_eq_some hinf

/-- Parse a map label into its mathematical passport data and its external orbit identifier.
No Galois-orbit meaning is assigned to the latter. -/
def parseMapLabel (n : ℕ) (s : String) : Option (PassportLabel n × String) :=
  match (s.toList.splitOn '-').map String.ofList with
  | [group, partitions, orbit] =>
    if orbit ≠ "" ∧ ∀ c ∈ orbit.toList, 'a' ≤ c ∧ c ≤ 'z' then
      (parsePassportLabel n (group ++ "-" ++ partitions)).map fun L => (L, orbit)
    else none
  | _ => none

/-- A map label is accepted exactly when its passport component is accepted and its external
orbit identifier is a nonempty string of lowercase letters. -/
@[simp] theorem parseMapLabel_eq_some_iff {n : ℕ} {s orbit : String} {L : PassportLabel n} :
    parseMapLabel n s = some (L, orbit) ↔
      ∃ group partitions,
        (s.toList.splitOn '-').map String.ofList = [group, partitions, orbit] ∧
        orbit ≠ "" ∧ (∀ c ∈ orbit.toList, 'a' ≤ c ∧ c ≤ 'z') ∧
        parsePassportLabel n (group ++ "-" ++ partitions) = some L := by
  unfold parseMapLabel
  split <;> simp_all [-parsePassportLabel_eq_some_iff, Option.map_eq_some_iff]
  grind

end TauCeti.PermutationTriple.LMFDB
