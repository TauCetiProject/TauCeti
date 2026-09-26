/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.Card.BoundedCoeff
public import TauCeti.NumberTheory.NumberField.Units.Regulator
import TauCeti.NumberTheory.NumberField.Minpoly
import TauCeti.NumberTheory.NumberField.Units.PrimeDegree

/-!
# Candidate minimal polynomials for units in rank one

A unit whose value at a real infinite place lies between `1` and `B` has bounded logarithmic
embedding when the unit rank is one. The bounds on every complex embedding then give an explicit
bound on every coefficient of its minimal polynomial. `unitCandidates` enumerates all monic
integer polynomials of the field degree within that coefficient bound; every unit in the interval
whose minimal polynomial has the field degree belongs to this finite list, in particular every such
unit when the degree is prime.

The enumeration uses the existing finite set of bounded integer polynomials. It is intentionally
an overapproximation: a later root test and field test eliminate candidates that cannot be units
in the given field.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, §5.7.
-/

public section

open NumberField NumberField.InfinitePlace NumberField.Units Polynomial
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- The integer coefficient bound used for units in a rank-one field whose selected real value
satisfies `1 < w(v) ≤ B`. -/
noncomputable def candidateCoeffBound (K : Type*) [Field K] [NumberField K] (B : ℝ) : ℕ :=
  Nat.ceil ((max (B ^ 2) 1) ^ Module.finrank ℚ K *
    (Module.finrank ℚ K).choose (Module.finrank ℚ K / 2))

/-- The formula for the candidate coefficient bound. -/
@[simp]
theorem candidateCoeffBound_def (K : Type*) [Field K] [NumberField K] (B : ℝ) :
    candidateCoeffBound K B = Nat.ceil ((max (B ^ 2) 1) ^ Module.finrank ℚ K *
      (Module.finrank ℚ K).choose (Module.finrank ℚ K / 2)) := by
  rfl

/-- The explicit finite list of monic integer polynomials of field degree whose coefficients
lie within the bound supplied by `candidateCoeffBound`. -/
noncomputable def unitCandidates (K : Type*) [Field K] [NumberField K] (B : ℝ) :
    Finset ℤ[X] := by
  classical
  have hfinite : {f : ℤ[X] | f.Monic ∧ f.natDegree = Module.finrank ℚ K ∧
      ∀ i, |f.coeff i| ≤ (candidateCoeffBound K B : ℤ)}.Finite :=
    (TauCeti.Polynomial.finite_setOf_natDegree_le_abs_intCoeff_le
      (Module.finrank ℚ K) (candidateCoeffBound K B)).subset (by
      intro f hf
      exact ⟨hf.2.1.le, hf.2.2⟩)
  exact hfinite.toFinset

/-- Membership in the candidate list is exactly monicity, field degree, and the integer
coefficient bound. -/
@[simp]
theorem mem_unitCandidates_iff (f : ℤ[X]) (B : ℝ) :
    f ∈ unitCandidates K B ↔
      f.Monic ∧ f.natDegree = Module.finrank ℚ K ∧
        ∀ i, |f.coeff i| ≤ (candidateCoeffBound K B : ℤ) := by
  classical
  simp only [unitCandidates, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- Every unit in the selected real interval whose minimal polynomial has the field degree has
its minimal polynomial in `unitCandidates` when the unit rank is one. -/
theorem minpoly_mem_unitCandidates_of_natDegree_eq (hr : rank K = 1)
    {w : InfinitePlace K} (hw : w.IsReal) (v : (𝓞 K)ˣ) {B : ℝ}
    (hdeg : (minpoly ℤ (v : 𝓞 K)).natDegree = Module.finrank ℚ K)
    (hlo : 1 < w.embedding_of_isReal hw (v : K))
    (hhi : w.embedding_of_isReal hw (v : K) ≤ B) :
    minpoly ℤ (v : 𝓞 K) ∈ unitCandidates K B := by
  classical
  apply (mem_unitCandidates_iff (K := K) _ B).mpr
  refine ⟨minpoly.monic (v : 𝓞 K).isIntegral, hdeg, fun i => ?_⟩
  have hB : 0 ≤ Real.log B := by
    exact (Real.log_pos (lt_of_lt_of_le hlo hhi)).le
  have hBpos : 0 < B := lt_of_lt_of_le (lt_trans zero_lt_one hlo) hhi
  have hnorm := norm_logEmbedding_le_log_of_interval hr hw v hlo hhi
  have hemb : ∀ φ : K →+* ℂ, ‖φ ((v : 𝓞 K) : K)‖ ≤
      B ^ 2 := by
    apply (InfinitePlace.le_iff_le _ _).mp
    intro w'
    rw [← Real.log_le_log_iff (Units.pos_at_place v w') (pow_pos hBpos 2), Real.log_pow]
    have h := NumberField.Units.dirichletUnitTheorem.log_le_of_logEmbedding_le
      (K := K) hB hnorm w'
    have hcard : Fintype.card (InfinitePlace K) = 2 := by
      have hnonempty : 0 < Fintype.card (InfinitePlace K) := Fintype.card_pos
      dsimp [rank] at hr
      omega
    rw [hcard] at h
    exact (le_abs_self _).trans h
  have hcoeff := NumberField.Embeddings.coeff_bdd_of_norm_le
    (K := K) (A := ℂ) hemb i
  have hmin : (minpoly ℤ (v : 𝓞 K)).map (algebraMap ℤ ℚ) =
      minpoly ℚ ((v : 𝓞 K) : K) :=
    (_root_.NumberField.RingOfIntegers.minpoly_rat_coe (v : 𝓞 K)).symm
  rw [← hmin, coeff_map] at hcoeff
  have hcoeff' : (|(minpoly ℤ (v : 𝓞 K)).coeff i| : ℝ) ≤
      max (B ^ 2) 1 ^ Module.finrank ℚ K *
        (Module.finrank ℚ K).choose (Module.finrank ℚ K / 2) := by
    simpa only [eq_intCast, Int.norm_cast_rat, Int.norm_eq_abs, Int.cast_abs] using hcoeff
  exact_mod_cast hcoeff'.trans (Nat.le_ceil _)

/-- Every unit in the selected real interval has a minimal polynomial in `unitCandidates`
when the unit rank is one and the field degree is prime. -/
theorem minpoly_mem_unitCandidates (hr : rank K = 1)
    (hp : Nat.Prime (Module.finrank ℚ K)) {w : InfinitePlace K} (hw : w.IsReal)
    (v : (𝓞 K)ˣ) {B : ℝ}
    (hlo : 1 < w.embedding_of_isReal hw (v : K))
    (hhi : w.embedding_of_isReal hw (v : K) ≤ B) :
    minpoly ℤ (v : 𝓞 K) ∈ unitCandidates K B := by
  have hnot : v ∉ torsion K := by
    intro hv
    have hvone := (NumberField.Units.mem_torsion (x := v)).mp hv w
    have hval : w v = w.embedding_of_isReal hw (v : K) := by
      rw [← InfinitePlace.norm_embedding_of_isReal hw, Real.norm_eq_abs,
        abs_of_pos (lt_trans zero_lt_one hlo)]
    exact (ne_of_gt hlo) (hval ▸ hvone)
  have hgen := adjoin_eq_top_of_finrank_prime hp hnot
  have hdeg : (minpoly ℤ (v : 𝓞 K)).natDegree = Module.finrank ℚ K := by
    have hrat := (Field.primitive_element_iff_minpoly_natDegree_eq ℚ ((v : 𝓞 K) : K)).mp
      ((IntermediateField.adjoin_eq_top_iff_of_isAlgebraic
        fun x _ => IsAlgebraic.of_finite ℚ x).mpr hgen)
    rw [_root_.NumberField.RingOfIntegers.minpoly_rat_coe,
      (minpoly.monic (v : 𝓞 K).isIntegral).natDegree_map] at hrat
    exact hrat
  exact minpoly_mem_unitCandidates_of_natDegree_eq hr hw v hdeg hlo hhi

end TauCeti.NumberField.Units
