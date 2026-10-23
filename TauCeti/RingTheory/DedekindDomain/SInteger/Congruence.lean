/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.SInteger.Quotient
public import TauCeti.RingTheory.DedekindDomain.Ideal.Congruence

/-!
# The finite multiplicative congruence quotient

Let `R` be a Dedekind domain with fraction field `K`, and let `m` be a nonzero ideal.
Reduction modulo `m` on the elements integral at its prime divisors sends a unit to one
exactly when its image in `Kˣ` belongs to `Ideal.congruenceSubgroup m K hm`.
Consequently the units of this locally integral ring, modulo multiplicative congruence,
are canonically isomorphic to `(R ⧸ m)ˣ`.

This identifies the finite-congruence quotient used in the ray-class exact sequence.
Neither finiteness of the residue rings nor a number-field hypothesis is needed.
The unit ideal is included: both sides of the quotient equivalence are then trivial.

The valuation argument generalizes `TauCeti.GlobalNumberFields.residue_eq_one_iff`.
Reduction and its surjectivity are supplied by `Ideal.sIntegerToQuotient`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- Reduction to one is equivalent to the local valuation bounds for multiplicative
congruence, even for elements not assumed to be units. -/
theorem sIntegerToQuotient_eq_one_iff (m : Ideal R) (hm : m ≠ ⊥)
    (x : ({v : HeightOneSpectrum R | v.asIdeal ∣ m}ᶜ).integer K) :
    m.sIntegerToQuotient x = 1 ↔ ∀ v : HeightOneSpectrum R, v.asIdeal ∣ m →
      v.valuation K ((x : K) - 1) ≤
        WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk m).factors : ℤ)) := by
  obtain ⟨a, b, hb, hab⟩ :=
    m.exists_algebraMap_eq_mul_and_sub_one_mem_of_valuation_le_one
      (fun v hv ↦ x.2 v (by simpa using hv))
  have hnum : m.sIntegerToQuotient x = 1 ↔ a - 1 ∈ m := by
    rw [m.sIntegerToQuotient_eq x hb hab]
    exact Ideal.Quotient.mk_eq_one_iff_sub_mem a
  -- A denominator congruent to one is a local unit at each prime divisor of m.
  have hval (v : HeightOneSpectrum R) (hv : v.asIdeal ∣ m) :
      v.valuation K ((x : K) - 1) = v.intValuation (a - b) := by
    have hbv : b ∉ v.asIdeal := by
      intro hbv
      apply v.isPrime.ne_top
      apply (Ideal.eq_top_iff_one _).mpr
      simpa using v.asIdeal.sub_mem hbv (Ideal.le_of_dvd hv hb)
    have hbval : v.valuation K (algebraMap R K b) = 1 :=
      v.valuation_eq_one_iff_notMem.mpr hbv
    have hb0 : algebraMap R K b ≠ 0 := by
      intro h
      simp [h] at hbval
    have hxsub : (x : K) - 1 = algebraMap R K (a - b) / algebraMap R K b := by
      rw [map_sub, hab]
      field_simp
    rw [hxsub, map_div₀, valuation_of_algebraMap, hbval, div_one]
  -- Assemble the prime-power conditions back into membership in the finite ideal.
  have hlocal : a - b ∈ m ↔ ∀ v : HeightOneSpectrum R, v.asIdeal ∣ m →
      v.intValuation (a - b) ≤
        WithZero.exp (-((Associates.mk v.asIdeal).count (Associates.mk m).factors : ℤ)) := by
    conv_lhs => rw [← Ideal.iInf_maxPowDividing_eq hm, Submodule.mem_iInf]
    constructor
    · intro h v _
      exact (v.intValuation_le_pow_iff_mem _ _).mpr (h v)
    · intro h v
      by_cases hv : v.asIdeal ∣ m
      · exact (v.intValuation_le_pow_iff_mem _ _).mp (h v hv)
      · have hz : (Associates.mk v.asIdeal).count (Associates.mk m).factors = 0 := by
          by_contra hne
          exact hv ((Associates.count_ne_zero_iff_dvd hm v.irreducible).mp hne)
        rw [maxPowDividing, hz, pow_zero, Ideal.one_eq_top]
        exact Submodule.mem_top
  rw [hnum, ← m.sub_mem_iff_left hb, sub_sub_sub_cancel_right]
  refine hlocal.trans (forall_congr' fun v ↦ forall_congr' fun hv ↦ ?_)
  rw [hval v hv]

/-- The kernel of reduction on locally integral units is precisely multiplicative
congruence in the fraction field, pulled back along the inclusion into `Kˣ`. -/
@[simp]
theorem ker_units_map_sIntegerToQuotient (m : Ideal R) (hm : m ≠ ⊥) :
    (Units.map (m.sIntegerToQuotient (K := K) :
        ({v : HeightOneSpectrum R | v.asIdeal ∣ m}ᶜ).integer K →* R ⧸ m)).ker =
      (m.congruenceSubgroup K hm).comap
        (Units.map ((({v : HeightOneSpectrum R | v.asIdeal ∣ m}ᶜ).integer K).val :
          ({v : HeightOneSpectrum R | v.asIdeal ∣ m}ᶜ).integer K →* K)) := by
  ext u
  simp only [MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one,
    Subgroup.mem_comap, mem_congruenceSubgroup_iff]
  exact m.sIntegerToQuotient_eq_one_iff hm u.val

/-- The units integral at the prime divisors of `m`, modulo multiplicative congruence,
are the residue units modulo `m`. -/
def unitsIntegerCongruenceQuotientEquiv (m : Ideal R) (hm : m ≠ ⊥) :
    (({v : HeightOneSpectrum R | v.asIdeal ∣ m}ᶜ).integer K)ˣ ⧸
      (m.congruenceSubgroup K hm).comap
        (Units.map ((({v : HeightOneSpectrum R | v.asIdeal ∣ m}ᶜ).integer K).val :
          ({v : HeightOneSpectrum R | v.asIdeal ∣ m}ᶜ).integer K →* K)) ≃*
      (R ⧸ m)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (m.ker_units_map_sIntegerToQuotient hm).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ m.units_map_sIntegerToQuotient_surjective)

/-- The quotient equivalence sends the class of a locally integral unit to its reduction. -/
@[simp]
theorem unitsIntegerCongruenceQuotientEquiv_mk (m : Ideal R) (hm : m ≠ ⊥)
    (u : (({v : HeightOneSpectrum R | v.asIdeal ∣ m}ᶜ).integer K)ˣ) :
    m.unitsIntegerCongruenceQuotientEquiv hm (QuotientGroup.mk u) =
      Units.map (m.sIntegerToQuotient (K := K) :
        ({v : HeightOneSpectrum R | v.asIdeal ∣ m}ᶜ).integer K →* R ⧸ m) u := by
  rfl

end Ideal
