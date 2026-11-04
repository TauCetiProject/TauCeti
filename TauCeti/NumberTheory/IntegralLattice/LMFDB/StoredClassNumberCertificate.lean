/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.IntegralLattice.LMFDB.StoredGenusCertificate
public import TauCeti.NumberTheory.IntegralLattice.Mass

/-!
# Certificates for the class number column of an LMFDB lattice record

The label `dim.det.level.class_number.index` of an LMFDB lattice record contains the class number
of the genus, and the record lists one Gram matrix for each class of the genus. A
`TauCeti.IntegralLattice.StoredGenusCertificate` certifies that the listed lattices are pairwise
non-isometric lattices in the genus, but that alone does not show that they exhaust it. A
`TauCeti.IntegralLattice.StoredClassNumberCertificate` adds the stored class number, equal to the
number of listed representatives, and the input that makes the list complete:

* a rational number `mass` with the hypothesis `mass_eq` that it is the mass of the genus
  (`TauCeti.IntegralLattice.mass`). This is an imported hypothesis: no theorem of this file
  evaluates the mass, and it is discharged by an exact mass formula or by another proof that the
  genus has been enumerated;
* the finite check `sum_inv_natCard_isometry_reps_eq_mass` that the reciprocal orders of the
  isometry groups of the listed representatives sum to `mass`.

Completeness is a theorem and not a field. The listed lattices are distinct classes of the genus,
and every class of a positive definite genus contributes a positive term `1 / |O(M)|` to the mass,
so a list missing a class would sum to strictly less than the mass
(`TauCeti.IntegralLattice.sum_inv_natCard_isometry_eq_mass_iff`). Hence the stored class number is
the class number of the stored lattice, and every lattice in the genus is isometric to exactly one
listed representative.

## Main definitions

* `TauCeti.IntegralLattice.StoredClassNumberCertificate`: a certificate of the stored columns
  together with the stored class number and the mass hypothesis that makes the list complete.

## Main results

* `TauCeti.IntegralLattice.StoredClassNumberCertificate.ext`: a certificate is determined by its
  certificate of the stored columns.
* `TauCeti.IntegralLattice.StoredClassNumberCertificate.classNumber_eq_classNumber_lattice`: the
  stored class number is the class number of the stored lattice.
* `TauCeti.IntegralLattice.StoredClassNumberCertificate.existsUnique_mem_reps_nonempty_isometry`:
  every lattice in the genus of the stored lattice, in any rational vector space, is isometric to
  exactly one stored representative.

## References

* The LMFDB Collaboration, *The L-functions and modular forms database*, section *Integral
  lattices*, https://www.lmfdb.org/Lattice/.
* J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*,
  Proc. R. Soc. Lond. A 419 (1988), §2, for the use of the mass to check a list of classes.
-/

public section

namespace TauCeti.IntegralLattice

/-- **The class number column of an LMFDB lattice record, with the mass that certifies it.** It
extends the certificate of the stored columns by the stored class number, which is the number of
stored representatives, and by a rational number `mass` together with

* the imported hypothesis `mass_eq` that `mass` is the mass of the genus of the stored lattice,
  and
* the finite check `sum_inv_natCard_isometry_reps_eq_mass` that the stored representatives
  already carry the whole mass.

Completeness of the list of representatives is not a field: it is the theorem
`TauCeti.IntegralLattice.StoredClassNumberCertificate.classNumber_eq_classNumber_lattice`. -/
structure StoredClassNumberCertificate (n : ℕ) extends StoredGenusCertificate n where
  /-- The mass of the genus, as supplied by a source outside the certificate. -/
  mass : ℚ
  /-- **The imported hypothesis**: `mass` is the mass of the genus of the stored lattice. It is
  supplied by an exact mass formula, or by another proof that the genus has been enumerated. -/
  mass_eq : mass = (ofGramMatrix (Pi.basisFun ℚ (Fin n)) gram gram_isSymm).mass
  /-- The reciprocal orders of the isometry groups of the stored representatives sum to the
  mass. -/
  sum_inv_natCard_isometry_reps_eq_mass :
    (reps.map fun H ↦ ((Nat.card (Isometry (ofGramMatrix (Pi.basisFun ℚ (Fin n)) H.1 H.2)
      (ofGramMatrix (Pi.basisFun ℚ (Fin n)) H.1 H.2)) : ℚ))⁻¹).sum = mass
  /-- The label component `class_number`. -/
  classNumber : ℕ
  /-- The stored class number is the number of stored representatives. -/
  classNumber_eq_length_reps : classNumber = reps.length

namespace StoredClassNumberCertificate

variable {n : ℕ}

/-- A certificate of the class number column is determined by its certificate of the stored
columns: the mass and the class number are pinned down by `mass_eq` and
`classNumber_eq_length_reps`. -/
@[ext]
theorem ext {c c' : StoredClassNumberCertificate n}
    (h : c.toStoredGenusCertificate = c'.toStoredGenusCertificate) : c = c' := by
  revert h
  obtain ⟨g, m, hm, -, k, hk⟩ := c
  obtain ⟨g', m', hm', -, k', hk'⟩ := c'
  intro h
  dsimp only at h
  subst h hm hk hm' hk'
  rfl

variable (c : StoredClassNumberCertificate n)

/-- **The stored class number is the class number of the stored lattice.** The stored
representatives are pairwise non-isometric lattices in a positive definite genus whose reciprocal
isometry group orders sum to the mass of the genus, so they represent every class. -/
theorem classNumber_eq_classNumber_lattice : c.classNumber = c.lattice.classNumber := by
  have hsum := (Fin.sum_univ_fun_getElem c.reps _).trans
    (c.sum_inv_natCard_isometry_reps_eq_mass.trans c.mass_eq)
  have h := (sum_inv_natCard_isometry_eq_mass_iff c.isPosDef.finite_genusClasses
    (fun M hM ↦ (hM.isPosDef_iff.mp c.isPosDef).finite_isometry) c.sameGenus_repLattice
    c.pairwise_isEmpty_isometry_repLattice).mp hsum
  rwa [Nat.card_eq_fintype_card, Fintype.card_fin, ← c.classNumber_eq_length_reps] at h

/-- **The stored representatives exhaust the genus**: every lattice in the genus of the stored
lattice, in any rational vector space, is isometric to the lattice of a stored representative. -/
theorem exists_mem_reps_nonempty_isometry {W : Type*} [AddCommGroup W] [Module ℚ W]
    {M : IntegralLattice W} (hM : c.lattice.SameGenus M) :
    ∃ H ∈ c.reps, Nonempty (Isometry (ofGramMatrix (Pi.basisFun ℚ (Fin n)) H.1 H.2) M) :=
  c.exists_mem_reps_nonempty_isometry_of_length_eq
    (c.classNumber_eq_length_reps.symm.trans c.classNumber_eq_classNumber_lattice) hM

/-- **The stored representatives are a set of representatives for the classes of the genus**:
every lattice in the genus of the stored lattice, in any rational vector space, is isometric to
the lattice of exactly one stored representative. -/
theorem existsUnique_mem_reps_nonempty_isometry {W : Type*} [AddCommGroup W] [Module ℚ W]
    {M : IntegralLattice W} (hM : c.lattice.SameGenus M) :
    ∃! H, H ∈ c.reps ∧ Nonempty (Isometry (ofGramMatrix (Pi.basisFun ℚ (Fin n)) H.1 H.2) M) := by
  obtain ⟨H, hH, ⟨e⟩⟩ := c.exists_mem_reps_nonempty_isometry hM
  refine ⟨H, ⟨hH, ⟨e⟩⟩, fun H' ⟨hH', ⟨e'⟩⟩ ↦ ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hH'
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hH
  by_contra hne
  have hij : (⟨i, hi⟩ : Fin c.reps.length) ≠ ⟨j, hj⟩ := fun h ↦ hne (by simp_all)
  exact (c.pairwise_isEmpty_isometry_repLattice hij).false (e'.trans e.symm)

end StoredClassNumberCertificate

end TauCeti.IntegralLattice
