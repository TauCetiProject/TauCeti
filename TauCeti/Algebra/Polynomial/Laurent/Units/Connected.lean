/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Laurent.Units
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Clopen

/-!
# Laurent units over connected rings

The coefficients of a Laurent unit define a disjoint open cover of the prime spectrum:
modulo each prime ideal the unit is a single monomial. Thus each coefficient's nonvanishing
locus is clopen. Over a ring with connected spectrum, one coefficient is a unit and all the
others are nilpotent. Unlike the domain case, the other coefficients need not vanish.

This supplies the coefficient argument for finding homogeneous generators of graded free
modules of rank one.
-/

public section

open scoped LaurentPolynomial

namespace LaurentPolynomial

variable {R : Type*} [CommRing R]

/-- Modulo a prime ideal, exactly one coefficient of a Laurent unit is nonzero. -/
theorem existsUnique_coeff_notMem_prime_of_isUnit (f : R[T;T⁻¹]) (hf : IsUnit f)
    (p : PrimeSpectrum R) : ∃! n : ℤ, f.coeff n ∉ p.asIdeal := by
  let := p.isPrime
  obtain ⟨r, hr, n, hn⟩ := isUnit_iff.mp
    (hf.map (AddMonoidAlgebra.mapRingHom ℤ (Ideal.Quotient.mk p.asIdeal)))
  have hc (i : ℤ) : Ideal.Quotient.mk p.asIdeal (f.coeff i) =
      if n = i then r else 0 := by
    have h := congrArg (fun g : (R ⧸ p.asIdeal)[T;T⁻¹] ↦ g.coeff i) hn
    simpa [← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply] using h.symm
  refine ⟨n, ?_, fun i hi ↦ ?_⟩
  · simpa [← Ideal.Quotient.eq_zero_iff_mem, hc] using hr.ne_zero
  · by_contra h
    exact hi (Ideal.Quotient.eq_zero_iff_mem.mp (by simp [hc, Ne.symm h]))

/-- The nonvanishing locus of any coefficient of a Laurent unit is clopen. -/
theorem isClopen_basicOpen_coeff_of_isUnit (f : R[T;T⁻¹]) (hf : IsUnit f) (n : ℤ) :
    IsClopen (PrimeSpectrum.basicOpen (f.coeff n) : Set (PrimeSpectrum R)) := by
  let U (i : ℤ) : Set (PrimeSpectrum R) := PrimeSpectrum.basicOpen (f.coeff i)
  have hopen (i : ℤ) : IsOpen (U i) := PrimeSpectrum.isOpen_basicOpen
  apply isClopen_of_disjoint_cover_open (b := ⋃ i : {i : ℤ // i ≠ n}, U i)
  · intro p _
    obtain ⟨i, hi, -⟩ := f.existsUnique_coeff_notMem_prime_of_isUnit hf p
    by_cases h : i = n
    · exact Or.inl ((PrimeSpectrum.mem_basicOpen _ _).mpr (h ▸ hi))
    · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨i, h⟩, (PrimeSpectrum.mem_basicOpen _ _).mpr hi⟩)
  · exact hopen n
  · exact isOpen_iUnion fun i ↦ hopen i
  · rw [Set.disjoint_left]
    intro p hn hp
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hp
    obtain ⟨j, _, huniq⟩ := f.existsUnique_coeff_notMem_prime_of_isUnit hf p
    exact i.2 ((huniq i ((PrimeSpectrum.mem_basicOpen _ _).mp hi)).trans
      (huniq n ((PrimeSpectrum.mem_basicOpen _ _).mp hn)).symm)

/-- Over a ring with preconnected spectrum, a Laurent unit has a unit coefficient and all
other coefficients are nilpotent. No nontriviality or reducedness assumption is needed. -/
theorem exists_isUnit_coeff_of_isUnit [PreconnectedSpace (PrimeSpectrum R)]
    (f : R[T;T⁻¹]) (hf : IsUnit f) :
    ∃ n : ℤ, IsUnit (f.coeff n) ∧ ∀ i ≠ n, IsNilpotent (f.coeff i) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, isUnit_of_subsingleton _, fun i _ ↦ ⟨1, Subsingleton.elim _ _⟩⟩
  · obtain ⟨p⟩ := (PrimeSpectrum.nonempty_iff_nontrivial (R := R)).mpr inferInstance
    obtain ⟨n, hn, -⟩ := f.existsUnique_coeff_notMem_prime_of_isUnit hf p
    have htop := (f.isClopen_basicOpen_coeff_of_isUnit hf n).eq_univ
      ⟨p, (PrimeSpectrum.mem_basicOpen _ _).mpr hn⟩
    have hall (q : PrimeSpectrum R) : f.coeff n ∉ q.asIdeal := by
      apply (PrimeSpectrum.mem_basicOpen _ _).mp
      rw [← SetLike.mem_coe, htop]
      exact Set.mem_univ q
    refine ⟨n, ?_, fun i hi ↦ ?_⟩
    · rw [← Ideal.span_singleton_eq_top, ← PrimeSpectrum.zeroLocus_empty_iff_eq_top,
        PrimeSpectrum.zeroLocus_span]
      exact Set.eq_empty_iff_forall_notMem.mpr fun q hq ↦ hall q (hq (by simp))
    · rw [nilpotent_iff_mem_prime]
      intro I hI
      let q : PrimeSpectrum R := ⟨I, hI⟩
      by_contra h
      obtain ⟨j, _, huniq⟩ := f.existsUnique_coeff_notMem_prime_of_isUnit hf q
      exact hi ((huniq i h).trans (huniq n (hall q)).symm)

end LaurentPolynomial
