/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Lean requires this public import to compile the executable solver through its private helpers.
public import TauCeti.Data.FinEnum.Perm
import Mathlib.Data.List.NodupEquivFin
import TauCeti.Data.Array.OfFn
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.CentralCharacterCount
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Reduction
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Lift

/-!
# The assembled cyclotomic Dixon--Schneider solver

The modular phase of the Burnside--Dixon--Schneider algorithm returns the unordered set of
central-character rows over `ZMod p`.  For a character table with values in
`TauCeti.Cyclotomic e`, reconstructing one exact entry needs its residues at every conjugate
primitive `e`-th root modulo `p`, not just at one root.  Each conjugate of an exact central
character is again a central character, so every one of those residue rows belongs to the same
modular search.

This file performs the missing assembly.  For `q : TauCeti.DixonPrimeData G`, it enumerates the
possible alignments of the modular rows at all conjugate roots. It numbers the searched rows once,
fixes the first conjugate slice, and directly enumerates permutations of that numbering for each
remaining conjugate.  It applies
`TauCeti.Cyclotomic.lift` entrywise to obtain
candidate exact central-character rows, enumerates the possible positive degree vectors, and
computes the candidate ordinary table by coefficientwise exact division.  The executable
cyclotomic checker is the final gate: a candidate is returned only when the division-free
central-to-ordinary identity and all other character-table identities hold.

The assembled algorithm, `TauCeti.ClassData.characterTableDixon?`, chooses the prime itself: it
runs this solver at the Dixon prime data found by `TauCeti.DixonPrimeData.candidates`, in
increasing order of the prime, and returns the first table accepted.

The result is deliberately an `Option`.  `none` records that no alignment and degree vector passes
the exact checker; no unverified coefficient bound is used to claim success.  Soundness is
unconditional: every returned table satisfies `TauCeti.IsCharacterTableSpec` after the distinguished
embedding into `ℂ`.  Completeness of the search at a sufficiently large Dixon prime additionally
needs the coefficient bound discussed in the cyclotomic-lift module.

## Main definitions

* `TauCeti.ClassData.CyclotomicCharacterTableData`: numbered exact cyclotomic output data.
* `TauCeti.ClassData.dixonCyclotomicCharacterTable?`: the executable exact-cyclotomic solver.
* `TauCeti.ClassData.characterTableDixon?`: the solver run at searched Dixon primes, the assembled
  Burnside--Dixon--Schneider algorithm with a bounded prime search.

## Main results

* `TauCeti.ClassData.isSome_dixonCyclotomicCharacterTable_of_spec`: a certified exact table whose
  coefficients lie in the balanced residue window is found by the solver.
* `conjugateResidueRow_mem_centralCharacterSearch_of_dixonCyclotomicCharacterTable?_eq_some`:
  every conjugate residue row of a returned central table comes from the modular search.
* `TauCeti.ClassData.isCyclotomicCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some`:
  every returned output passes the exact cyclotomic certificate.
* `TauCeti.ClassData.isCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some`: after
  embedding, every returned table satisfies the complex character-table specification.
* `TauCeti.ClassData.isCharacterTableSpec_of_characterTableDixon?_eq_some`: **soundness of the
  assembled algorithm**, every table it returns is the character table up to the order of its rows.
* `TauCeti.ClassData.isSome_characterTableDixon?_of_isSome` and
  `TauCeti.ClassData.characterTableDixon?_eq_some_of_le`: the algorithm succeeds as soon as the
  solver does at a prime it reaches, and a larger budget does not change its answer.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik **10** (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, Journal of Symbolic Computation
  **9** (1990), 601--606.
* The character-theory roadmap, Layer 6, “The assembled solver”.
-/

public section

namespace TauCeti

open Matrix

namespace ClassData

universe u

variable {G : Type u} [Group G] (d : ClassData G)

/-- Candidate numbered data for the exact-cyclotomic Dixon--Schneider solver.  The fields are
certified only after the candidate passes `cyclotomicCharacterTableChecker`. -/
@[ext]
structure CyclotomicCharacterTableData (e : ℕ) where
  /-- A candidate exact central-character table. -/
  omega : Matrix (Fin d.numClasses) (Fin d.numClasses)
    (Cyclotomic e)
  /-- A candidate exact ordinary character table. -/
  table : Matrix (Fin d.numClasses) (Fin d.numClasses)
    (Cyclotomic e)
  /-- Candidate character degrees. -/
  degree : Fin d.numClasses → ℕ

variable [Fintype G] [DecidableEq G]

/-- The modular central-character rows as an executable list. -/
private def modularCentralRowsList (q : DixonPrimeData G) :
    List (Fin d.numClasses → ZMod q.p) :=
  letI : FinEnum (ZMod q.p) :=
    FinEnum.ofEquiv (Fin q.p) (ZMod.finEquiv q.p).symm.toEquiv
  let searchedRows : Finset (Fin d.numClasses → ZMod q.p) :=
    d.centralCharacterSearch
  (FinEnum.toList (Fin d.numClasses → ZMod q.p)).filter fun row ↦
    decide (row ∈ searchedRows)

/-- Membership in the executable row list is membership in the modular search. -/
@[simp]
private theorem mem_modularCentralRowsList (q : DixonPrimeData G)
    {row : Fin d.numClasses → ZMod q.p} :
    row ∈ d.modularCentralRowsList q ↔ row ∈ d.centralCharacterSearch := by
  let _ : FinEnum (ZMod q.p) :=
    FinEnum.ofEquiv (Fin q.p) (ZMod.finEquiv q.p).symm.toEquiv
  simp [modularCentralRowsList]

/-- The executable modular-row list has one row for each conjugacy class at a Dixon prime. -/
private theorem length_modularCentralRowsList (q : DixonPrimeData G) :
    (d.modularCentralRowsList q).length = d.numClasses := by
  let _ : FinEnum (ZMod q.p) :=
    FinEnum.ofEquiv (Fin q.p) (ZMod.finEquiv q.p).symm.toEquiv
  have hnodup : (d.modularCentralRowsList q).Nodup := by
    rw [modularCentralRowsList]
    exact FinEnum.nodup_toList.filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  have hrows : (d.modularCentralRowsList q).toFinset =
      d.centralCharacterSearch := by
    ext row
    simp [mem_modularCentralRowsList]
  rw [hrows, d.card_centralCharacterSearch_of_isGoodDixonPrime q.isGoodDixonPrime]

/-- The canonical enumeration used by the solver identifies its row indices with the modular
central-character search. -/
private def modularCentralRowsEquiv (q : DixonPrimeData G) :
    Fin d.numClasses ≃ {row // row ∈ d.centralCharacterSearch (F := ZMod q.p)} :=
  letI : FinEnum (ZMod q.p) :=
    FinEnum.ofEquiv (Fin q.p) (ZMod.finEquiv q.p).symm.toEquiv
  (finCongr (length_modularCentralRowsList d q).symm).trans
    (((FinEnum.nodup_toList.filter _).getEquiv (d.modularCentralRowsList q)).trans
      (Equiv.subtypeEquivRight fun _ ↦ mem_modularCentralRowsList d q))

/-- The canonical numbering of the modular central-character rows.  The default branch of
`List.getD` is unreachable because the row list has exactly `d.numClasses` entries. -/
private def canonicalModularRow (q : DixonPrimeData G)
    (i : Fin d.numClasses) : Fin d.numClasses → ZMod q.p :=
  (d.modularCentralRowsList q).getD i 0

/-- Every canonically numbered modular row belongs to the central-character search. -/
private theorem canonicalModularRow_mem (q : DixonPrimeData G) (i : Fin d.numClasses) :
    d.canonicalModularRow q i ∈ d.centralCharacterSearch := by
  rw [canonicalModularRow, List.getD_eq_getElem _ _
    (by simp [length_modularCentralRowsList d q, i.isLt])]
  exact (mem_modularCentralRowsList d q).mp (List.getElem_mem _)

/-- The canonical modular row is the value of the equivalence enumerating the modular search. -/
private theorem modularCentralRowsEquiv_apply (q : DixonPrimeData G) (i : Fin d.numClasses) :
    (d.modularCentralRowsEquiv q i).1 = d.canonicalModularRow q i := by
  let _ : FinEnum (ZMod q.p) :=
    FinEnum.ofEquiv (Fin q.p) (ZMod.finEquiv q.p).symm.toEquiv
  simp only [modularCentralRowsEquiv, Equiv.trans_apply, Equiv.subtypeEquivRight_apply]
  rw [canonicalModularRow, List.getD_eq_getElem _ _ (by
    simp [length_modularCentralRowsList d q, i.isLt])]
  congr 1

/-- Divide every power-basis coordinate by a positive integer.  Candidate ordinary-character
entries use this computable quotient; the exact checker subsequently verifies that the division
was exact, so truncating integer division can never enter a returned result. -/
private def cyclotomicQuotient (e : ℕ) (x : Cyclotomic e) (n : ℕ) : Cyclotomic e :=
  Cyclotomic.ofCoeffList e (x.coeffs.map fun c ↦ c / (n : ℤ))

/-- Coefficientwise division by a positive constant undoes multiplication by that constant:
a constant multiple scales every coordinate, and the integer quotients are then exact. -/
private theorem cyclotomicQuotient_natCast_mul (e : ℕ) (x : Cyclotomic e) {n : ℕ}
    (hn : 0 < n) : cyclotomicQuotient e ((n : Cyclotomic e) * x) n = x := by
  have hn' : (n : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hcoeffs :
      (((n : Cyclotomic e) * x).coeffs.map fun c ↦ c / (n : ℤ)) = x.coeffs := by
    rw [← Int.cast_natCast (R := Cyclotomic e) n, Cyclotomic.coeffs_intCast_mul,
      List.map_map]
    calc
      _ = List.map id x.coeffs := by
        apply List.map_congr_left
        intro c _
        simpa only [Function.comp_apply, id_eq] using Int.mul_ediv_cancel_left c hn'
      _ = x.coeffs := List.map_id _
  rw [cyclotomicQuotient, hcoeffs, Cyclotomic.ofCoeffList_coeffs]

/-- **The certified ordinary table is the solver's coefficientwise quotient.**  The
division-free conversion identity of the specification makes every coordinate division exact,
so the candidate entries computed by `TauCeti.ClassData.cyclotomicQuotient` are determined. -/
private theorem table_eq_cyclotomicQuotient (e : ℕ)
    {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e)}
    {degree : Fin d.numClasses → ℕ}
    (hspec : d.IsCyclotomicCharacterTableSpec e omega table degree)
    (i k : Fin d.numClasses) :
    cyclotomicQuotient e ((degree i : Cyclotomic e) * omega i k) (d.classFinset k).card =
      table i k := by
  rw [hspec.degree_mul_central i k]
  exact cyclotomicQuotient_natCast_mul e (table i k)
    (Finset.card_pos.mpr ⟨d.rep k, d.rep_mem_classFinset k⟩)

omit [Fintype G] [DecidableEq G] in
/-- Enumerate only bijective row alignments, with the first conjugate fixed before searching.
The remaining conjugates independently choose a permutation of the canonical modular rows. -/
private def residuePermutations (e : ℕ) (first : Fin e.totient) :
    List (Fin e.totient → Fin d.numClasses → Fin d.numClasses) :=
  (List.Pi.enum fun _ : {j : Fin e.totient // j ≠ first} ↦
    Equiv.Perm (Fin d.numClasses)).map
    fun perms j i ↦ if hj : j = first then i else perms ⟨j, hj⟩ i

omit [Fintype G] [DecidableEq G] in
/-- An alignment is enumerated exactly when it fixes the distinguished conjugate and is
injective at every conjugate. -/
@[simp]
private theorem mem_residuePermutations (e : ℕ) (first : Fin e.totient)
    {perms : Fin e.totient → Fin d.numClasses → Fin d.numClasses} :
    perms ∈ d.residuePermutations e first ↔
      (∀ i, perms first i = i) ∧ ∀ j, Function.Injective (perms j) := by
  simp only [residuePermutations, List.mem_map, List.Pi.mem_enum, true_and]
  constructor
  · rintro ⟨ps, rfl⟩
    exact ⟨fun i ↦ by simp, fun j ↦ by
      by_cases hj : j = first
      · intro a b hab
        simpa only [dite_eq_left hj] using hab
      · simpa [hj] using (ps ⟨j, hj⟩).injective⟩
  · rintro ⟨hfirst, hinj⟩
    refine ⟨fun j ↦ Equiv.ofBijective (perms j)
      ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj j, rfl⟩), ?_⟩
    funext j i
    by_cases hj : j = first
    · simp [hj, hfirst]
    · simp [hj, Equiv.ofBijective_apply]

/-- Enumerate the exact-cyclotomic candidates inspected by the solver.

For every Galois-conjugate root, a permutation chooses how its modular rows align with the
canonical numbering.  The first conjugate uses the identity permutation, removing the irrelevant
simultaneous permutation of the output rows. -/
private def dixonCyclotomicCharacterTableCandidates (e : ℕ)
    (he : e = Monoid.exponent G) (q : DixonPrimeData G) :
    List (d.CyclotomicCharacterTableData e) :=
  let firstConjugate : Fin e.totient :=
    ⟨0, Nat.totient_pos.mpr (Nat.pos_of_ne_zero (he ▸ Monoid.exponent_ne_zero_of_finite))⟩
  let modularRows := d.modularCentralRowsList q
  let canonicalRows := Array.ofFn fun i : Fin d.numClasses ↦ modularRows.getD i 0
  let alignments := d.residuePermutations e firstConjugate
  let Degree :=
    {n : Fin (Fintype.card G + 1) // n ≠ 0 ∧ (n : ℕ) ∣ Fintype.card G}
  let degreeAssignments :=
    (FinEnum.toList (Fin d.numClasses → Degree)).filter fun degree ↦
      decide (∑ i, (degree i : ℕ) ^ 2 = Fintype.card G)
  alignments.flatMap fun perms ↦
    let omegaEntries := Array.ofFn fun i ↦ Array.ofFn fun k ↦
      Cyclotomic.lift e q.root fun j ↦
        (canonicalRows[(perms j i).val]'(by simp [canonicalRows])) k
    let omega : Matrix (Fin d.numClasses) (Fin d.numClasses)
        (Cyclotomic e) :=
      fun i k ↦
        (omegaEntries[i.val]'(by simp [omegaEntries]))[k.val]'(by simp [omegaEntries])
    degreeAssignments.map fun degrees ↦
      let degree : Fin d.numClasses → ℕ := fun i ↦ degrees i
      let table : Matrix (Fin d.numClasses) (Fin d.numClasses)
          (Cyclotomic e) :=
        fun i k ↦ cyclotomicQuotient e
          ((degree i : Cyclotomic e) * omega i k)
          (d.classFinset k).card
      { omega := omega, table := table, degree := degree }

/-- Every conjugate residue row of an enumerated candidate belongs to the modular
central-character search. -/
private theorem conjugateResidueRow_mem_of_mem_candidates (e : ℕ) (he : e = Monoid.exponent G)
    (q : DixonPrimeData G) {output : d.CyclotomicCharacterTableData e}
    (houtput : output ∈ d.dixonCyclotomicCharacterTableCandidates e he q)
    (i : Fin d.numClasses) (j : Fin e.totient) :
    (fun k ↦ Cyclotomic.conjugateResidues q.root (output.omega i k) j) ∈
      d.centralCharacterSearch := by
  let _ : FinEnum (ZMod q.p) :=
    FinEnum.ofEquiv (Fin q.p) (ZMod.finEquiv q.p).symm.toEquiv
  simp only [dixonCyclotomicCharacterTableCandidates, List.mem_flatMap, List.mem_map,
    List.mem_filter, FinEnum.mem_toList, true_and, decide_eq_true_eq,
    mem_residuePermutations] at houtput
  obtain ⟨perms, _, degrees, _, rfl⟩ := houtput
  have hrow :
      (fun k ↦ Cyclotomic.conjugateResidues q.root
        (Cyclotomic.lift e q.root fun l ↦
          d.canonicalModularRow q (perms l i) k) j) =
        d.canonicalModularRow q (perms j i) := by
    funext k
    have hroot : IsPrimitiveRoot q.root e := by simpa [he] using q.isPrimitiveRoot_root
    exact congrFun
      (Cyclotomic.conjugateResidues_lift hroot
        (fun l ↦ d.canonicalModularRow q (perms l i) k)) j
  simp only [canonicalModularRow] at hrow
  -- Read the outer pair of lookups first. `simp only [Array.getElem_ofFn]` alone would also
  -- descend into the outer array and rewrite the lookups inside its entries, where the resulting
  -- definitional check is prohibitively expensive.
  simp only [Array.getElem_getElem_ofFn_ofFn]
  simp only [Array.getElem_ofFn]
  rw [hrow]
  simpa only [canonicalModularRow] using canonicalModularRow_mem d q (perms j i)

/-- Run the exact-cyclotomic stage of the Dixon--Schneider character-table algorithm.

The function aligns the modular rows at all conjugate roots, applies the structured cyclotomic
lift, searches the possible character degrees, computes candidate ordinary-character entries,
and returns the first candidate accepted by the exact cyclotomic checker.  The conductor `e` is
passed explicitly, together with its equality to the group exponent, so evaluating the solver
does not attempt to compute Mathlib's noncomputable `Monoid.exponent`. -/
def dixonCyclotomicCharacterTable? (e : ℕ) (he : e = Monoid.exponent G)
    (q : DixonPrimeData G) :
    Option (d.CyclotomicCharacterTableData e) :=
  (d.dixonCyclotomicCharacterTableCandidates e he q).find? fun output ↦
    d.cyclotomicCharacterTableChecker e
      output.omega output.table output.degree

/-- The Galois-conjugate reductions of a certified table with injective residue rows renumber the
solver's canonical modular rows: after a permutation `base` of the table's rows, the reduction at
the `j`-th conjugate root gives the canonical rows in the order `perms j`, with `perms` the
identity at the first conjugate. -/
private theorem exists_perms_canonicalModularRow_eq_conjugateResidues (e : ℕ)
    (he : e = Monoid.exponent G) (q : DixonPrimeData G)
    {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e)}
    {degree : Fin d.numClasses → ℕ} (hspec : d.IsCyclotomicCharacterTableSpec e omega table degree)
    (hresidue_injective : ∀ j, Function.Injective fun i k ↦
      Cyclotomic.conjugateResidues q.root (omega i k) j) :
    ∃ (base : Equiv.Perm (Fin d.numClasses))
      (perms : Fin e.totient → Fin d.numClasses → Fin d.numClasses),
      (∀ (h : 0 < e.totient) i, perms ⟨0, h⟩ i = i) ∧ (∀ j, Function.Injective (perms j)) ∧
      ∀ j i, d.canonicalModularRow q (perms j i) =
        fun k ↦ Cyclotomic.conjugateResidues q.root (omega (base i) k) j := by
  have _ : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  have hmem (j : Fin e.totient) (i : Fin d.numClasses) :
      (fun k ↦ Cyclotomic.conjugateResidues q.root (omega i k) j) ∈
        d.centralCharacterSearch := by
    simpa only [Cyclotomic.reduceRingHom_apply, Cyclotomic.conjugateResidues_apply] using
      hspec.map_mem_centralCharacterSearch (Cyclotomic.reduceRingHom q.p _
        (Cyclotomic.isPrimitiveRoot_conjugateRoot (he ▸ q.isPrimitiveRoot_root) j)) i
  let residueEquiv (j : Fin e.totient) :
      Fin d.numClasses ≃ {row // row ∈ d.centralCharacterSearch (F := ZMod q.p)} :=
    Equiv.ofBijective (Subtype.coind _ (hmem j))
      ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨Subtype.coind_injective _ (hresidue_injective j), by
          rw [Fintype.card_fin, Fintype.card_coe,
            d.card_centralCharacterSearch_of_isGoodDixonPrime q.isGoodDixonPrime]⟩)
  let base : Equiv.Perm (Fin d.numClasses) := (d.modularCentralRowsEquiv q).trans
    (residueEquiv ⟨0, Nat.totient_pos.mpr (NeZero.pos e)⟩).symm
  refine ⟨base, fun j ↦ base.trans ((residueEquiv j).trans (d.modularCentralRowsEquiv q).symm),
    fun _ i ↦ by simp [base], fun j ↦ Equiv.injective _, fun j i ↦ ?_⟩
  simp [← d.modularCentralRowsEquiv_apply q, residueEquiv]

/-- A certified table is enumerated by the solver once its rows are aligned with the canonical
modular rows by permutations `perms`, the identity at the first conjugate, and its coefficients lie
in the balanced residue window. -/
private theorem mem_dixonCyclotomicCharacterTableCandidates (e : ℕ) (he : e = Monoid.exponent G)
    (q : DixonPrimeData G)
    {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e)}
    {degree : Fin d.numClasses → ℕ} (hspec : d.IsCyclotomicCharacterTableSpec e omega table degree)
    (hcoeff : ∀ i k (l : Fin e.totient), 2 * ((omega i k).coeff l).natAbs < q.p)
    {perms : Fin e.totient → Fin d.numClasses → Fin d.numClasses}
    (hfirst : ∀ (h : 0 < e.totient) i, perms ⟨0, h⟩ i = i)
    (hinjective : ∀ j, Function.Injective (perms j))
    (hrows : ∀ j i, d.canonicalModularRow q (perms j i) =
      fun k ↦ Cyclotomic.conjugateResidues q.root (omega i k) j) :
    ⟨omega, table, degree⟩ ∈ d.dixonCyclotomicCharacterTableCandidates e he q := by
  let _ : FinEnum (ZMod q.p) :=
    FinEnum.ofEquiv (Fin q.p) (ZMod.finEquiv q.p).symm.toEquiv
  -- `canonicalModularRow` unfolds by `rfl` to the `List.getD` form used by the solver.
  have homega (i k : Fin d.numClasses) : Cyclotomic.lift e q.root
      (fun j ↦ (d.modularCentralRowsList q).getD (perms j i) 0 k) = omega i k :=
    Cyclotomic.lift_eq_of_conjugateResidues_eq (he ▸ q.isPrimitiveRoot_root) (hcoeff i k) <|
      funext fun j ↦ (congrFun (hrows j i) k).symm
  simp only [dixonCyclotomicCharacterTableCandidates, List.mem_flatMap, List.mem_map,
    List.mem_filter, FinEnum.mem_toList, true_and, decide_eq_true_eq,
    mem_residuePermutations]
  -- The searched degree `⟨degree i, _⟩` has value `degree i` by `rfl`, which gives its
  -- nonvanishing and discharges the sum-of-squares condition and the `degree` field below.
  refine ⟨perms, ⟨hfirst _, hinjective⟩, fun i ↦ ⟨⟨degree i, Nat.lt_succ_of_le
    (Nat.le_of_dvd Fintype.card_pos (hspec.degree_dvd i))⟩, Fin.ne_of_gt (hspec.degree_pos i),
      hspec.degree_dvd i⟩, hspec.sum_degree_sq, ?_⟩
  refine CyclotomicCharacterTableData.ext (funext₂ fun i k ↦ ?_) (funext₂ fun i k ↦ ?_) rfl <;>
    simp only [Array.getElem_ofFn, Fin.eta, homega, d.table_eq_cyclotomicQuotient e hspec]

/-- **Completeness criterion for the exact-cyclotomic solver.** An exact certified table whose
central coefficients lie within the balanced residue window is found by the solver. Distinctness
of every Galois-conjugate reduction follows from the certificate and the good-prime hypotheses.

The theorem hides the solver's arbitrary canonical ordering of modular rows.  Internally, the
reduction at the first primitive root aligns the supplied rows with that ordering; the remaining
reductions determine the permutations enumerated by the solver. -/
theorem isSome_dixonCyclotomicCharacterTable_of_spec (e : ℕ)
    (he : e = Monoid.exponent G) (q : DixonPrimeData G)
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e))
    (degree : Fin d.numClasses → ℕ)
    (hspec : d.IsCyclotomicCharacterTableSpec e omega table degree)
    (hcoeff : ∀ i k (l : Fin e.totient),
      2 * ((omega i k).coeff l).natAbs < q.p) :
    (d.dixonCyclotomicCharacterTable? e he q).isSome = true := by
  have : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  have hresidue_injective := hspec.conjugateResidueRow_injective
    (he ▸ q.isPrimitiveRoot_root) (by simpa using q.isGoodDixonPrime.natCast_natCard_ne_zero)
  obtain ⟨base, perms, hfirst, hinjective, hrows⟩ :=
    d.exists_perms_canonicalModularRow_eq_conjugateResidues e he q hspec hresidue_injective
  rw [dixonCyclotomicCharacterTable?, List.find?_isSome]
  -- `Matrix.submatrix_apply` holds by `rfl`, so `hcoeff` and `hrows` apply to the permuted rows.
  exact ⟨⟨omega.submatrix base id, table.submatrix base id, degree ∘ base⟩,
    d.mem_dixonCyclotomicCharacterTableCandidates e he q (hspec.submatrix base)
      (fun i k ↦ hcoeff (base i) k) hfirst hinjective hrows,
    (d.cyclotomicCharacterTableChecker_eq_true_iff e _ _ _).mpr (hspec.submatrix base)⟩

/-- Every conjugate residue row of a successful exact-cyclotomic output is one of the rows
returned by the modular central-character search. -/
theorem conjugateResidueRow_mem_centralCharacterSearch_of_dixonCyclotomicCharacterTable?_eq_some
    {d : ClassData G} (e : ℕ) (he : e = Monoid.exponent G) (q : DixonPrimeData G)
    {output : d.CyclotomicCharacterTableData e}
    (h : d.dixonCyclotomicCharacterTable? e he q = some output)
    (i : Fin d.numClasses) (j : Fin e.totient) :
    (fun k ↦ Cyclotomic.conjugateResidues q.root (output.omega i k) j) ∈
      d.centralCharacterSearch := by
  simp only [dixonCyclotomicCharacterTable?] at h
  exact conjugateResidueRow_mem_of_mem_candidates d e he q (List.mem_of_find?_eq_some h) i j

/-- Every successful exact-cyclotomic Dixon--Schneider output passes the exact cyclotomic
character-table specification. -/
theorem isCyclotomicCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some
    {d : ClassData G} (e : ℕ) (he : e = Monoid.exponent G) (q : DixonPrimeData G)
    {output : d.CyclotomicCharacterTableData e}
    (h : d.dixonCyclotomicCharacterTable? e he q = some output) :
    d.IsCyclotomicCharacterTableSpec e
      output.omega output.table output.degree := by
  simp only [dixonCyclotomicCharacterTable?] at h
  have hcheck := List.find?_some h
  exact (d.cyclotomicCharacterTableChecker_eq_true_iff
    e output.omega output.table output.degree).mp hcheck

/-- Every successful exact-cyclotomic Dixon--Schneider output, embedded in `ℂ` and reindexed by
conjugacy classes, satisfies the complex character-table specification. -/
theorem isCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some
    {d : ClassData G} (e : ℕ) [NeZero e] (he : e = Monoid.exponent G) (q : DixonPrimeData G)
    {output : d.CyclotomicCharacterTableData e}
    (h : d.dixonCyclotomicCharacterTable? e he q = some output) :
    IsCharacterTableSpec G
      (d.complexTableOfCyclotomic e output.table) :=
  (d.isCyclotomicCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some
    e he q h).isCharacterTableSpec

/-! ### Searching for the prime

The solver above runs at one given Dixon prime. The assembled algorithm chooses the prime itself:
it walks through the Dixon prime data found by `TauCeti.DixonPrimeData.candidates` and returns the
first table the solver accepts there. -/

/-- **The Burnside--Dixon--Schneider algorithm, with its own choice of prime.** The Dixon prime
data at the good primes among `e + 1, 2e + 1, …, fuel · e + 1` is tried in increasing order, and
the first table that `TauCeti.ClassData.dixonCyclotomicCharacterTable?` returns is the result. The
exponent `e` is passed with its equality to the group exponent, so evaluation never computes
Mathlib's noncomputable `Monoid.exponent`; the order of the group is `Fintype.card G`. -/
def characterTableDixon? (e : ℕ) (he : e = Monoid.exponent G) (fuel : ℕ) :
    Option (d.CyclotomicCharacterTableData e) :=
  (DixonPrimeData.candidates e he (Fintype.card G) Nat.card_eq_fintype_card.symm fuel).findSome?
    (d.dixonCyclotomicCharacterTable? e he)

/-- **The algorithm succeeds exactly when the solver does at some searched prime.** -/
theorem isSome_characterTableDixon?_iff (e : ℕ) (he : e = Monoid.exponent G) (fuel : ℕ) :
    (d.characterTableDixon? e he fuel).isSome ↔
      ∃ q ∈ DixonPrimeData.candidates e he (Fintype.card G) Nat.card_eq_fintype_card.symm fuel,
        (d.dixonCyclotomicCharacterTable? e he q).isSome := by
  rw [characterTableDixon?]
  exact List.findSome?_isSome_iff

/-- Every table the algorithm returns is returned by the solver at one of the searched primes. -/
theorem exists_mem_candidates_of_characterTableDixon?_eq_some (e : ℕ)
    (he : e = Monoid.exponent G) {fuel : ℕ} {output : d.CyclotomicCharacterTableData e}
    (h : d.characterTableDixon? e he fuel = some output) :
    ∃ q ∈ DixonPrimeData.candidates e he (Fintype.card G) Nat.card_eq_fintype_card.symm fuel,
      d.dixonCyclotomicCharacterTable? e he q = some output := by
  rw [characterTableDixon?] at h
  exact List.exists_of_findSome?_eq_some h

/-- **The algorithm succeeds once the solver succeeds at a prime it reaches.** If the solver
returns a table at the Dixon prime data `q`, the search computes `q` at its prime, and that prime
is at most `e · fuel + 1`, then the algorithm returns a table, possibly found at a smaller prime. -/
theorem isSome_characterTableDixon?_of_isSome (e : ℕ) (he : e = Monoid.exponent G) {fuel : ℕ}
    (q : DixonPrimeData G)
    (hq : DixonPrimeData.ofPrime? e he (Fintype.card G) Nat.card_eq_fintype_card.symm q.p = some q)
    (hfuel : q.p ≤ e * fuel + 1) (hsolve : (d.dixonCyclotomicCharacterTable? e he q).isSome) :
    (d.characterTableDixon? e he fuel).isSome :=
  (d.isSome_characterTableDixon?_iff e he fuel).mpr
    ⟨q, DixonPrimeData.mem_candidates_iff.mpr ⟨hq, hfuel⟩, hsolve⟩

/-- **Running the algorithm longer does not change its answer**: once it has returned a table, it
returns the same table with any larger budget, because the search only appends primes. -/
theorem characterTableDixon?_eq_some_of_le (e : ℕ) (he : e = Monoid.exponent G)
    {fuel fuel' : ℕ} (hle : fuel ≤ fuel') {output : d.CyclotomicCharacterTableData e}
    (h : d.characterTableDixon? e he fuel = some output) :
    d.characterTableDixon? e he fuel' = some output := by
  obtain ⟨l, hl⟩ := DixonPrimeData.candidates_prefix (he := he) (n := Fintype.card G)
    (hn := Nat.card_eq_fintype_card.symm) hle
  rw [characterTableDixon?] at h ⊢
  rw [← hl, List.findSome?_append, h, Option.some_or]

/-- Every table the algorithm returns passes the exact cyclotomic certificate. -/
theorem isCyclotomicCharacterTableSpec_of_characterTableDixon?_eq_some (e : ℕ)
    (he : e = Monoid.exponent G) {fuel : ℕ} {output : d.CyclotomicCharacterTableData e}
    (h : d.characterTableDixon? e he fuel = some output) :
    d.IsCyclotomicCharacterTableSpec e output.omega output.table output.degree := by
  obtain ⟨q, -, hq⟩ := d.exists_mem_candidates_of_characterTableDixon?_eq_some e he h
  exact isCyclotomicCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some e he q hq

/-- **Soundness of the Burnside--Dixon--Schneider algorithm.** Every table the algorithm returns,
embedded in `ℂ` and reindexed by the conjugacy classes, satisfies the complex character-table
specification, so it is the character table of `G` up to the order of its rows. The exponent
of a finite group is nonzero, so the statement supplies the `NeZero e` instance the embedding needs
from `he`. -/
theorem isCharacterTableSpec_of_characterTableDixon?_eq_some (e : ℕ)
    (he : e = Monoid.exponent G) {fuel : ℕ} {output : d.CyclotomicCharacterTableData e}
    (h : d.characterTableDixon? e he fuel = some output) :
    haveI : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
    IsCharacterTableSpec G (d.complexTableOfCyclotomic e output.table) :=
  haveI : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  (d.isCyclotomicCharacterTableSpec_of_characterTableDixon?_eq_some e he h).isCharacterTableSpec

end ClassData

end TauCeti
