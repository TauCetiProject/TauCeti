/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Lean requires this public import to compile the executable solver through its private helpers.
public import Mathlib.Data.FinEnum
import Mathlib.Data.List.NodupEquivFin
import TauCeti.Data.Array.OfFn
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.CentralCharacterCount
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Rows
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.PowerMap
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Lift

/-!
# The assembled cyclotomic Dixon--Schneider solver

The modular phase of the Burnside--Dixon--Schneider algorithm returns the unordered set of
central-character rows over `ZMod p`.  For a character table with values in
`TauCeti.Cyclotomic e`, reconstructing one exact entry needs its residues at every conjugate
primitive `e`-th root modulo `p`, not just at one root.  Each conjugate of an exact central
character is again a central character, so every one of those residue rows belongs to the same
modular search.

For `q : TauCeti.DixonPrimeData G`, the solver numbers the searched rows once. A conjugate root
`α ^ n` uses the entry of the same modular row at the class of `g ^ n`: the Galois power-map
identity determines every alignment. The solver applies `TauCeti.Cyclotomic.lift` entrywise to
obtain one candidate exact central table, enumerates the possible positive degree vectors, and
computes the candidate ordinary table by coefficientwise exact division.  The executable
cyclotomic checker is the final gate: a candidate is returned only when the division-free
central-to-ordinary identity and all other character-table identities hold.

The assembled algorithm, `TauCeti.ClassData.characterTableDixon?`, chooses the prime itself: it
runs this solver at the Dixon prime data found by `TauCeti.DixonPrimeData.candidates`, in
increasing order of the prime, and returns the first table accepted.

The result is deliberately an `Option`.  `none` records that no degree vector passes
the exact checker; no unverified coefficient bound is used to claim success.  Soundness is
unconditional: every returned table satisfies `TauCeti.IsCharacterTableSpec` after the distinguished
embedding into `ℂ`.  Completeness of the search at a sufficiently large Dixon prime additionally
requires `e = Monoid.exponent G` and the coefficient bound discussed in the cyclotomic-lift module.

## Main definitions

* `TauCeti.ClassData.CyclotomicCharacterTableData`: numbered exact cyclotomic output data.
* `TauCeti.ClassData.dixonCyclotomicCharacterTable?`: the executable exact-cyclotomic solver.
* `TauCeti.ClassData.characterTableDixon?`: the solver run at searched Dixon primes, the assembled
  Burnside--Dixon--Schneider algorithm with a bounded prime search.

## Main results

* `TauCeti.ClassData.isSome_dixonCyclotomicCharacterTable_of_spec`: a certified exact table whose
  coefficients lie in the balanced residue window is found by the solver when
  `e = Monoid.exponent G`.
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
* J.-P. Serre, *Linear Representations of Finite Groups*, §12.4.
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
  d.centralCharacterRows

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
    exact d.nodup_centralCharacterRows
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
    (((d.nodup_centralCharacterRows).getEquiv (d.modularCentralRowsList q)).trans
      (Equiv.subtypeEquivRight fun _ ↦ mem_modularCentralRowsList d q))

/-- The canonical numbering of the modular central-character rows.  The default branch of
`List.getD` is unreachable because the row list has exactly `d.numClasses` entries. -/
private def canonicalModularRow (q : DixonPrimeData G)
    (i : Fin d.numClasses) : Fin d.numClasses → ZMod q.p :=
  (d.modularCentralRowsList q).getD i 0

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

/-- Enumerate exact-cyclotomic candidates using power maps to determine every conjugate
residue from a single modular row. Only the character degrees are searched. -/
private def dixonCyclotomicCharacterTableCandidates (e : ℕ) (q : DixonPrimeData G) :
    List (d.CyclotomicCharacterTableData e) :=
  let modularRows := d.modularCentralRowsList q
  let canonicalRows := Array.ofFn fun i : Fin d.numClasses ↦ modularRows.getD i 0
  let powerIndices := Array.ofFn fun j : Fin e.totient ↦ Array.ofFn fun k : Fin d.numClasses ↦
    d.index (d.rep k ^ Cyclotomic.primitiveExponent e j)
  let omegaEntries := Array.ofFn fun i : Fin d.numClasses ↦ Array.ofFn fun k : Fin d.numClasses ↦
    Cyclotomic.lift e q.root fun j ↦
      (canonicalRows[i.val]'(by simp [canonicalRows]))
        ((powerIndices[j.val]'(by simp [powerIndices]))[k.val]'(by simp [powerIndices]))
  let omega : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e) :=
    fun i k ↦ (omegaEntries[i.val]'(by simp [omegaEntries]))[k.val]'(by simp [omegaEntries])
  let Degree :=
    {n : Fin (Fintype.card G + 1) // n ≠ 0 ∧ (n : ℕ) ∣ Fintype.card G}
  let degreeAssignments :=
    (FinEnum.toList (Fin d.numClasses → Degree)).filter fun degree ↦
      decide (∑ i, (degree i : ℕ) ^ 2 = Fintype.card G)
  degreeAssignments.map fun degrees ↦
    let degree : Fin d.numClasses → ℕ := fun i ↦ degrees i
    let table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e) :=
      fun i k ↦ cyclotomicQuotient e
        ((degree i : Cyclotomic e) * omega i k) (d.classFinset k).card
    { omega := omega, table := table, degree := degree }

/-- Run the exact-cyclotomic stage of the Dixon--Schneider character-table algorithm.

The function uses power maps to align the modular residues at all conjugate roots, applies the
structured cyclotomic lift, searches the possible character degrees, computes candidate ordinary
character entries, and returns the first candidate accepted by the exact cyclotomic checker.
The conductor `e` is passed explicitly, so evaluating the solver does not attempt to compute
Mathlib's noncomputable `Monoid.exponent`. Soundness holds for any conductor; the completeness
criterion requires it to equal the group exponent. -/
def dixonCyclotomicCharacterTable? (e : ℕ) (q : DixonPrimeData G) :
    Option (d.CyclotomicCharacterTableData e) :=
  (d.dixonCyclotomicCharacterTableCandidates e q).find? fun output ↦
    d.cyclotomicCharacterTableChecker e
      output.omega output.table output.degree

/-- Reduction at the chosen primitive root identifies a certified table's rows with the
canonical numbering of the modular central-character search. -/
private theorem exists_base_canonicalModularRow_eq_reduce (e : ℕ)
    (he : e = Monoid.exponent G) (q : DixonPrimeData G)
    {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e)}
    {degree : Fin d.numClasses → ℕ}
    (hspec : d.IsCyclotomicCharacterTableSpec e omega table degree) :
    ∃ base : Equiv.Perm (Fin d.numClasses), ∀ i,
      d.canonicalModularRow q i = fun k ↦ Cyclotomic.reduce q.p q.root (omega (base i) k) := by
  have _ : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  let φ := Cyclotomic.reduceRingHom q.p q.root (he ▸ q.isPrimitiveRoot_root)
  have hmem (i : Fin d.numClasses) : (fun k ↦ φ (omega i k)) ∈ d.centralCharacterSearch :=
    hspec.map_mem_centralCharacterSearch φ i
  have hinj := hspec.map_central_injective φ
    (by simpa using q.isGoodDixonPrime.natCast_natCard_ne_zero)
  let residueEquiv :
      Fin d.numClasses ≃
        {row // row ∈ d.centralCharacterSearch (F := ZMod q.p)} :=
    Equiv.ofBijective (Subtype.coind _ hmem)
      ((Fintype.bijective_iff_injective_and_card _).mpr
        ⟨Subtype.coind_injective _ hinj, by
          rw [Fintype.card_fin, Fintype.card_coe,
            d.card_centralCharacterSearch_of_isGoodDixonPrime q.isGoodDixonPrime]⟩)
  refine ⟨(d.modularCentralRowsEquiv q).trans residueEquiv.symm, fun i ↦ ?_⟩
  rw [← d.modularCentralRowsEquiv_apply q i]
  simpa only [residueEquiv, φ, Equiv.trans_apply, Equiv.ofBijective_apply,
    Subtype.coind, Cyclotomic.reduceRingHom_apply] using
    congrArg Subtype.val (residueEquiv.apply_symm_apply (d.modularCentralRowsEquiv q i)).symm

/-- A certified table whose reduction follows the canonical row numbering and whose central
coefficients lie in the balanced window is among the power-aligned candidates. -/
private theorem mem_dixonCyclotomicCharacterTableCandidates (e : ℕ) (he : e = Monoid.exponent G)
    (q : DixonPrimeData G)
    {omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e)}
    {degree : Fin d.numClasses → ℕ} (hspec : d.IsCyclotomicCharacterTableSpec e omega table degree)
    (hcoeff : ∀ i k (l : Fin e.totient), 2 * ((omega i k).coeff l).natAbs < q.p)
    (hrows : ∀ i, d.canonicalModularRow q i =
      fun k ↦ Cyclotomic.reduce q.p q.root (omega i k)) :
    ⟨omega, table, degree⟩ ∈ d.dixonCyclotomicCharacterTableCandidates e q := by
  have _ : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  have hroot : IsPrimitiveRoot q.root e := he ▸ q.isPrimitiveRoot_root
  have homega (i k : Fin d.numClasses) : Cyclotomic.lift e q.root
      (fun j ↦ (d.modularCentralRowsList q).getD i 0
        (d.index (d.rep k ^ Cyclotomic.primitiveExponent e j))) = omega i k := by
    apply Cyclotomic.lift_eq_of_conjugateResidues_eq hroot (hcoeff i k)
    funext j
    -- The list lookup is the defining value of `canonicalModularRow`.
    rw [← canonicalModularRow, hrows]
    exact hspec.conjugateResidues_omega hroot i k j
      (he ▸ Monoid.pow_exponent_eq_one (d.rep k))
  simp only [dixonCyclotomicCharacterTableCandidates, List.mem_map,
    List.mem_filter, FinEnum.mem_toList, true_and, decide_eq_true_eq]
  refine ⟨fun i ↦ ⟨⟨degree i, Nat.lt_succ_of_le
    (Nat.le_of_dvd Fintype.card_pos (hspec.degree_dvd i))⟩, Fin.ne_of_gt (hspec.degree_pos i),
      hspec.degree_dvd i⟩, hspec.sum_degree_sq, ?_⟩
  refine CyclotomicCharacterTableData.ext (funext₂ fun i k ↦ ?_) (funext₂ fun i k ↦ ?_) rfl <;>
    simp only [Array.getElem_ofFn, Fin.eta, homega, d.table_eq_cyclotomicQuotient e hspec]

/-- **Completeness criterion for the exact-cyclotomic solver.** An exact certified table whose
central coefficients lie within the balanced residue window is found by the solver when
`e = Monoid.exponent G`. Distinctness of every Galois-conjugate reduction follows from the
certificate and the good-prime hypotheses.

The theorem hides the solver's arbitrary canonical ordering of modular rows. Reduction at the
chosen primitive root aligns the supplied rows with that ordering, and powering class
representatives determines all remaining conjugate reductions. -/
theorem isSome_dixonCyclotomicCharacterTable_of_spec (e : ℕ)
    (he : e = Monoid.exponent G) (q : DixonPrimeData G)
    (omega table : Matrix (Fin d.numClasses) (Fin d.numClasses) (Cyclotomic e))
    (degree : Fin d.numClasses → ℕ)
    (hspec : d.IsCyclotomicCharacterTableSpec e omega table degree)
    (hcoeff : ∀ i k (l : Fin e.totient),
      2 * ((omega i k).coeff l).natAbs < q.p) :
    (d.dixonCyclotomicCharacterTable? e q).isSome = true := by
  have : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨base, hrows⟩ := d.exists_base_canonicalModularRow_eq_reduce e he q hspec
  rw [dixonCyclotomicCharacterTable?, List.find?_isSome]
  -- Row permutation preserves the specification and the coefficient bound.
  exact ⟨⟨omega.submatrix base id, table.submatrix base id, degree ∘ base⟩,
    d.mem_dixonCyclotomicCharacterTableCandidates e he q (hspec.submatrix base)
      (fun i k ↦ hcoeff (base i) k) hrows,
    (d.cyclotomicCharacterTableChecker_eq_true_iff e _ _ _).mpr (hspec.submatrix base)⟩

/-- Every successful exact-cyclotomic Dixon--Schneider output passes the exact cyclotomic
character-table specification. -/
theorem isCyclotomicCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some
    {d : ClassData G} (e : ℕ) (q : DixonPrimeData G)
    {output : d.CyclotomicCharacterTableData e}
    (h : d.dixonCyclotomicCharacterTable? e q = some output) :
    d.IsCyclotomicCharacterTableSpec e
      output.omega output.table output.degree := by
  simp only [dixonCyclotomicCharacterTable?] at h
  have hcheck := List.find?_some h
  exact (d.cyclotomicCharacterTableChecker_eq_true_iff
    e output.omega output.table output.degree).mp hcheck

/-- Every conjugate residue row of a successful exact-cyclotomic output is one of the rows
returned by the modular central-character search. -/
theorem conjugateResidueRow_mem_centralCharacterSearch_of_dixonCyclotomicCharacterTable?_eq_some
    {d : ClassData G} (e : ℕ) (he : e = Monoid.exponent G) (q : DixonPrimeData G)
    {output : d.CyclotomicCharacterTableData e}
    (h : d.dixonCyclotomicCharacterTable? e q = some output)
    (i : Fin d.numClasses) (j : Fin e.totient) :
    (fun k ↦ Cyclotomic.conjugateResidues q.root (output.omega i k) j) ∈
      d.centralCharacterSearch := by
  have _ : NeZero e := ⟨he ▸ Monoid.exponent_ne_zero_of_finite⟩
  have hspec := d.isCyclotomicCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some e q h
  simpa only [Cyclotomic.reduceRingHom_apply, Cyclotomic.conjugateResidues_apply] using
    hspec.map_mem_centralCharacterSearch
      (Cyclotomic.reduceRingHom q.p _
        (Cyclotomic.isPrimitiveRoot_conjugateRoot (he ▸ q.isPrimitiveRoot_root) j)) i

/-- Every successful exact-cyclotomic Dixon--Schneider output, embedded in `ℂ` and reindexed by
conjugacy classes, satisfies the complex character-table specification. -/
theorem isCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some
    {d : ClassData G} (e : ℕ) [NeZero e] (q : DixonPrimeData G)
    {output : d.CyclotomicCharacterTableData e}
    (h : d.dixonCyclotomicCharacterTable? e q = some output) :
    IsCharacterTableSpec G
      (d.complexTableOfCyclotomic e output.table) :=
  (d.isCyclotomicCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some
    e q h).isCharacterTableSpec

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
    (d.dixonCyclotomicCharacterTable? e)

/-- **The algorithm succeeds exactly when the solver does at some searched prime.** -/
theorem isSome_characterTableDixon?_iff (e : ℕ) (he : e = Monoid.exponent G) (fuel : ℕ) :
    (d.characterTableDixon? e he fuel).isSome ↔
      ∃ q ∈ DixonPrimeData.candidates e he (Fintype.card G) Nat.card_eq_fintype_card.symm fuel,
        (d.dixonCyclotomicCharacterTable? e q).isSome := by
  rw [characterTableDixon?]
  exact List.findSome?_isSome_iff

/-- Every table the algorithm returns is returned by the solver at one of the searched primes. -/
theorem exists_mem_candidates_of_characterTableDixon?_eq_some (e : ℕ)
    (he : e = Monoid.exponent G) {fuel : ℕ} {output : d.CyclotomicCharacterTableData e}
    (h : d.characterTableDixon? e he fuel = some output) :
    ∃ q ∈ DixonPrimeData.candidates e he (Fintype.card G) Nat.card_eq_fintype_card.symm fuel,
      d.dixonCyclotomicCharacterTable? e q = some output := by
  rw [characterTableDixon?] at h
  exact List.exists_of_findSome?_eq_some h

/-- **The algorithm succeeds once the solver succeeds at a prime it reaches.** If the solver
returns a table at the Dixon prime data `q`, the search computes `q` at its prime, and that prime
is at most `e · fuel + 1`, then the algorithm returns a table, possibly found at a smaller prime. -/
theorem isSome_characterTableDixon?_of_isSome (e : ℕ) (he : e = Monoid.exponent G) {fuel : ℕ}
    (q : DixonPrimeData G)
    (hq : DixonPrimeData.ofPrime? e he (Fintype.card G) Nat.card_eq_fintype_card.symm q.p = some q)
    (hfuel : q.p ≤ e * fuel + 1) (hsolve : (d.dixonCyclotomicCharacterTable? e q).isSome) :
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
  exact isCyclotomicCharacterTableSpec_of_dixonCyclotomicCharacterTable?_eq_some e q hq

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
