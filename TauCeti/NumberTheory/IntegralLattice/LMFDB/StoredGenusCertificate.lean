/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.ClassNumber
public import TauCeti.LinearAlgebra.IntegralLattice.Level
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Minimum
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.RepresentationNumber
import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Covolume

/-!
# Certificates for the stored columns of an LMFDB lattice record

A record of the LMFDB table of positive definite integral lattices stores a Gram matrix `G`, the
label components `dim`, `det` and `level`, the minimum, the kissing number, the order of the
automorphism group, a prefix of the theta series, and a list of Gram matrices of genus
representatives. A `TauCeti.IntegralLattice.StoredGenusCertificate` bundles these stored values
with the statements the record makes about them, each phrased through the lattice invariant it
names: the stored matrix `G` is symmetric and positive definite, so it defines the lattice `L` on
`Fin n → ℚ` with Gram matrix `G` in the standard basis, and

* the stored determinant is `L.determinant`, and the stored level is `L.level`;
* the stored minimum is `L.minimum`, the stored kissing number is `L.kissingNumber`, and the
  stored automorphism group order is the number of isometries of `L`;
* the stored theta series is a list whose `k`-th entry is the representation number `r_L(k)`, the
  number of vectors of norm `k`; it is a statement about shell counts, not about `q`-expansions;
* every stored representative is symmetric and defines a lattice in the genus of `L`, and the
  stored representatives are pairwise non-isometric.

The certificate makes no claim that the stored representatives exhaust the genus. Distinct
classes in one genus need not be all of them, so the class number is not a field: the theorem
`TauCeti.IntegralLattice.StoredGenusCertificate.length_reps_le_classNumber` bounds it below by
the number of stored representatives, and
`TauCeti.IntegralLattice.StoredGenusCertificate.length_reps_eq_classNumber_iff` identifies
equality with completeness of the list. Proving completeness needs an input such as an exact mass
formula, which is outside the scope of this file.

The theorems below also derive the consistency conditions between the stored columns: the
determinant and level are positive and the level divides twice the determinant, the minimum and
kissing number are positive in positive rank, and the theta series starts with `1`, vanishes
strictly between `0` and the minimum, and takes the value of the kissing number at the minimum.

## Main definitions

* `TauCeti.IntegralLattice.StoredGenusCertificate`: the stored columns of an LMFDB lattice record,
  with the statements identifying them with lattice invariants.
* `TauCeti.IntegralLattice.StoredGenusCertificate.lattice`: the lattice of the stored Gram matrix.

## Main results

* `TauCeti.IntegralLattice.StoredGenusCertificate.ext`: a certificate is determined by its stored
  Gram matrix, theta series prefix and representatives.
* `TauCeti.IntegralLattice.StoredGenusCertificate.finrank_lattice` and
  `TauCeti.IntegralLattice.StoredGenusCertificate.determinant_eq_det`: the label components `dim`
  and `det` are the rank and the Gram determinant.
* `TauCeti.IntegralLattice.StoredGenusCertificate.length_reps_le_classNumber` and
  `TauCeti.IntegralLattice.StoredGenusCertificate.length_reps_eq_classNumber_iff`: the class
  number bounds the number of stored representatives, with equality exactly when every lattice in
  the genus is isometric to a stored representative.

## References

* The LMFDB Collaboration, *The L-functions and modular forms database*, section *Integral
  lattices*, https://www.lmfdb.org/Lattice/.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15.
-/

public section

open Module

namespace TauCeti.IntegralLattice

/-- **The stored columns of an LMFDB lattice record, with what they assert.** The record stores a
Gram matrix `gram` of size `n`, and the lattice it defines is the lattice on `Fin n → ℚ` whose
Gram matrix in the standard basis is `gram`. Each stored numerical column is a data field paired
with the statement that it is the corresponding invariant of that lattice. The theta series is
stored as a finite prefix, whose entries are representation numbers.

There is deliberately no class number field and no completeness field: the stored
representatives are asserted to lie in the genus and to be pairwise non-isometric, which does not
make them a complete set of classes of the genus. -/
structure StoredGenusCertificate (n : ℕ) where
  /-- The stored Gram matrix. -/
  gram : Matrix (Fin n) (Fin n) ℤ
  /-- The stored Gram matrix is symmetric, so it is the Gram matrix of an integral lattice. -/
  gram_isSymm : gram.IsSymm
  /-- The lattice of the stored Gram matrix is positive definite. -/
  isPosDef : (ofGramMatrix (Pi.basisFun ℚ (Fin n)) gram gram_isSymm).IsPosDef
  /-- The label component `det`. -/
  determinant : ℤ
  /-- The stored determinant is the determinant of the lattice. -/
  determinant_eq :
    determinant = (ofGramMatrix (Pi.basisFun ℚ (Fin n)) gram gram_isSymm).determinant
  /-- The label component `level`. -/
  level : ℕ
  /-- The stored level is the level of the lattice. -/
  level_eq : level = (ofGramMatrix (Pi.basisFun ℚ (Fin n)) gram gram_isSymm).level
  /-- The stored minimum. -/
  minimum : ℕ
  /-- The stored minimum is the minimum of the lattice. -/
  minimum_eq : minimum = (ofGramMatrix (Pi.basisFun ℚ (Fin n)) gram gram_isSymm).minimum
  /-- The stored kissing number. -/
  kissingNumber : ℕ
  /-- The stored kissing number is the kissing number of the lattice. -/
  kissingNumber_eq :
    kissingNumber = (ofGramMatrix (Pi.basisFun ℚ (Fin n)) gram gram_isSymm).kissingNumber
  /-- The stored order of the automorphism group. -/
  autOrder : ℕ
  /-- The stored automorphism group order is the number of isometries of the lattice. -/
  autOrder_eq :
    autOrder = Nat.card (Isometry (ofGramMatrix (Pi.basisFun ℚ (Fin n)) gram gram_isSymm)
      (ofGramMatrix (Pi.basisFun ℚ (Fin n)) gram gram_isSymm))
  /-- The stored prefix of the theta series. -/
  thetaSeries : List ℕ
  /-- The `k`-th stored theta series coefficient is the number of lattice vectors of norm `k`. -/
  thetaSeries_eq : ∀ (k : ℕ) (hk : k < thetaSeries.length),
    thetaSeries[k] =
      (ofGramMatrix (Pi.basisFun ℚ (Fin n)) gram gram_isSymm).representationNumber k
  /-- The stored Gram matrices of genus representatives, each with its symmetry. -/
  reps : List {H : Matrix (Fin n) (Fin n) ℤ // H.IsSymm}
  /-- Every stored representative defines a lattice in the genus of the stored lattice. -/
  sameGenus_reps : ∀ H ∈ reps,
    (ofGramMatrix (Pi.basisFun ℚ (Fin n)) gram gram_isSymm).SameGenus
      (ofGramMatrix (Pi.basisFun ℚ (Fin n)) H.1 H.2)
  /-- The lattices of the stored representatives are pairwise non-isometric. -/
  pairwise_isEmpty_isometry_reps : reps.Pairwise fun H H' ↦
    IsEmpty (Isometry (ofGramMatrix (Pi.basisFun ℚ (Fin n)) H.1 H.2)
      (ofGramMatrix (Pi.basisFun ℚ (Fin n)) H'.1 H'.2))

namespace StoredGenusCertificate

variable {n : ℕ}

/-- A certificate is determined by its stored Gram matrix, its stored theta series prefix and its
stored representatives: every other stored value is pinned down by the lattice invariant it is
asserted to be. -/
@[ext]
theorem ext {c c' : StoredGenusCertificate n} (hgram : c.gram = c'.gram)
    (htheta : c.thetaSeries = c'.thetaSeries) (hreps : c.reps = c'.reps) : c = c' := by
  revert hgram htheta hreps
  obtain ⟨G, hG, -, d, hd, l, hl, m, hm, k, hk, a, ha, θ, -, R, -, -⟩ := c
  obtain ⟨G', hG', -, d', hd', l', hl', m', hm', k', hk', a', ha', θ', -, R', -, -⟩ := c'
  intro hgram htheta hreps
  dsimp only at hgram htheta hreps
  subst hgram htheta hreps hd hl hm hk ha hd' hl' hm' hk' ha'
  rfl

variable (c : StoredGenusCertificate n)

/-- The lattice of the stored Gram matrix: the integral lattice on `Fin n → ℚ` whose Gram matrix
in the standard basis is `c.gram`. -/
-- This is reducible so that the fields of the certificate, which name this lattice through
-- `ofGramMatrix`, apply to `c.lattice` without an unfolding lemma.
noncomputable abbrev lattice : IntegralLattice (Fin n → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin n)) c.gram c.gram_isSymm

/-- The label component `dim` is the rank of the stored lattice. -/
@[simp]
theorem finrank_lattice : finrank ℤ c.lattice = n := by
  rw [c.lattice.finrank_carrier, Module.finrank_fin_fun]

/-- The stored determinant is the determinant of the stored Gram matrix. -/
theorem determinant_eq_det : c.determinant = c.gram.det := by
  classical
  rw [c.determinant_eq, determinant_ofGramMatrix]

/-- The stored determinant is positive. -/
theorem determinant_pos : 0 < c.determinant := by
  rw [c.determinant_eq]
  exact c.isPosDef.determinant_pos

/-- The stored level divides twice the stored determinant. -/
theorem level_dvd_two_mul_determinant : (c.level : ℤ) ∣ 2 * c.determinant := by
  rw [c.level_eq, c.determinant_eq]
  exact c.lattice.level_dvd_two_mul_determinant

/-- The stored level is positive. -/
theorem level_pos : 0 < c.level := by
  have : c.lattice.IsNondegenerate :=
    ⟨(c.lattice.isPosDef_iff_isPosSemidef_and_nondegenerate.mp c.isPosDef).2⟩
  rw [c.level_eq]
  exact c.lattice.level_pos

/-- In positive rank the stored lattice has a nonzero vector. -/
theorem nontrivial_lattice (hn : 0 < n) : Nontrivial c.lattice :=
  Module.nontrivial_of_finrank_pos (R := ℤ) (by rw [c.finrank_lattice]; exact hn)

/-- In positive rank the stored minimum is positive. -/
theorem minimum_pos (hn : 0 < n) : 0 < c.minimum := by
  have := c.nontrivial_lattice hn
  rw [c.minimum_eq]
  exact c.isPosDef.minimum_pos

/-- In positive rank the stored kissing number is positive. -/
theorem kissingNumber_pos (hn : 0 < n) : 0 < c.kissingNumber := by
  have := c.nontrivial_lattice hn
  rw [c.kissingNumber_eq]
  exact c.isPosDef.kissingNumber_pos

/-- The stored automorphism group order is positive: the isometry group of a positive definite
lattice is finite and contains the identity. -/
theorem autOrder_pos : 0 < c.autOrder := by
  have := c.isPosDef.finite_isometry (L := c.lattice)
  rw [c.autOrder_eq]
  exact Nat.card_pos_iff.mpr ⟨⟨Isometry.refl c.lattice⟩, this⟩

/-- The stored theta series starts with `1`: only the zero vector has norm `0`. -/
theorem thetaSeries_getElem_zero (h : 0 < c.thetaSeries.length) : c.thetaSeries[0] = 1 := by
  rw [c.thetaSeries_eq 0 h, Nat.cast_zero]
  exact representationNumber_zero_of_anisotropic (by rw [norm_def]; exact c.isPosDef.anisotropic)

/-- The stored theta series vanishes strictly between `0` and the stored minimum. -/
theorem thetaSeries_getElem_eq_zero {k : ℕ} (hk : k < c.thetaSeries.length) (hk₀ : k ≠ 0)
    (hkm : k < c.minimum) : c.thetaSeries[k] = 0 := by
  rw [c.thetaSeries_eq k hk, representationNumber_def,
    c.isPosDef.isPosSemidef.vectorsOfNorm_eq_empty_of_lt_minimum (by exact_mod_cast hk₀)
      (by rw [← c.minimum_eq]; exact_mod_cast hkm), Set.ncard_empty]

/-- In positive rank the entry of the stored theta series at the stored minimum is the stored
kissing number. -/
theorem thetaSeries_getElem_minimum (hn : 0 < n) (h : c.minimum < c.thetaSeries.length) :
    c.thetaSeries[c.minimum] = c.kissingNumber := by
  have hmin := c.minimum_pos hn
  rw [c.thetaSeries_eq _ h, c.kissingNumber_eq, kissingNumber_eq_representationNumber
    (by rw [← c.minimum_eq]; exact hmin.ne'), c.minimum_eq]

/-! ### The stored representatives -/

/-- The lattice of each stored representative is positive definite. -/
theorem isPosDef_of_mem_reps {H : {H : Matrix (Fin n) (Fin n) ℤ // H.IsSymm}} (hH : H ∈ c.reps) :
    (ofGramMatrix (Pi.basisFun ℚ (Fin n)) H.1 H.2).IsPosDef :=
  (c.sameGenus_reps H hH).isPosDef_iff.mp c.isPosDef

/-- Each stored representative has the stored determinant. -/
theorem det_of_mem_reps {H : {H : Matrix (Fin n) (Fin n) ℤ // H.IsSymm}} (hH : H ∈ c.reps) :
    H.1.det = c.determinant := by
  classical
  rw [c.determinant_eq, (c.sameGenus_reps H hH).determinant_eq, determinant_ofGramMatrix]

/-- The lattice of the `i`-th stored representative. -/
private noncomputable def repLattice (i : Fin c.reps.length) : IntegralLattice (Fin n → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin n)) c.reps[i].1 c.reps[i].2

/-- The lattice of each stored representative lies in the genus of the stored lattice. -/
private theorem sameGenus_repLattice (i : Fin c.reps.length) :
    c.lattice.SameGenus (c.repLattice i) :=
  c.sameGenus_reps _ (List.getElem_mem _)

/-- Distinct positions of the list of stored representatives carry non-isometric lattices. -/
private theorem pairwise_isEmpty_isometry_repLattice :
    Pairwise fun i j ↦ IsEmpty (Isometry (c.repLattice i) (c.repLattice j)) := by
  have h := List.pairwise_iff_getElem.mp c.pairwise_isEmpty_isometry_reps
  intro i j hij
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hlt
  · exact h i j i.2 j.2 hlt
  · exact ⟨fun e ↦ (h j i j.2 i.2 hlt).false e.symm⟩

/-- **The class number bounds the number of stored representatives**, which are pairwise
non-isometric lattices in the genus of the stored lattice. -/
theorem length_reps_le_classNumber : c.reps.length ≤ c.lattice.classNumber := by
  simpa using card_le_classNumber_of_pairwise_isEmpty_isometry c.isPosDef.finite_genusClasses
    c.sameGenus_repLattice c.pairwise_isEmpty_isometry_repLattice

/-- **The stored representatives are a complete set of classes exactly when their number is the
class number**: equality holds if and only if every lattice on `Fin n → ℚ` in the genus of the
stored lattice is isometric to the lattice of a stored representative. -/
theorem length_reps_eq_classNumber_iff :
    c.reps.length = c.lattice.classNumber ↔ ∀ M : IntegralLattice (Fin n → ℚ),
      c.lattice.SameGenus M → ∃ H ∈ c.reps,
        Nonempty (Isometry (ofGramMatrix (Pi.basisFun ℚ (Fin n)) H.1 H.2) M) := by
  have h := card_eq_classNumber_iff_of_pairwise_isEmpty_isometry c.isPosDef.finite_genusClasses
    c.sameGenus_repLattice c.pairwise_isEmpty_isometry_repLattice
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  rw [h]
  refine forall₂_congr fun M _ ↦ ⟨fun ⟨i, hi⟩ ↦ ⟨_, List.getElem_mem _, hi⟩, ?_⟩
  rintro ⟨H, hH, hHM⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hH
  exact ⟨⟨i, hi⟩, hHM⟩

/-- When the number of stored representatives is the class number, every lattice in the genus of
the stored lattice, in any rational vector space, is isometric to the lattice of a stored
representative. -/
theorem exists_mem_reps_nonempty_isometry_of_length_eq {W : Type*} [AddCommGroup W] [Module ℚ W]
    (h : c.reps.length = c.lattice.classNumber) {M : IntegralLattice W}
    (hM : c.lattice.SameGenus M) :
    ∃ H ∈ c.reps, Nonempty (Isometry (ofGramMatrix (Pi.basisFun ℚ (Fin n)) H.1 H.2) M) := by
  obtain ⟨N, hN, ⟨e⟩⟩ := hM.exists_isometry
  obtain ⟨H, hH, ⟨f⟩⟩ := c.length_reps_eq_classNumber_iff.mp h N hN
  exact ⟨H, hH, ⟨f.trans e.symm⟩⟩

end StoredGenusCertificate

end TauCeti.IntegralLattice
