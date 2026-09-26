/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Different
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.RamificationIndex

/-!
# Tame ramification and the global different exponent

At a finite prime of a number-field extension, the coefficient of the different equals `e - 1`
exactly when the residue characteristic does not divide `e`; it reaches `e` exactly in the wild
case. These are the ideal-theoretic versions of the tame and wild parts of Dedekind's different
theorem. The residue fields are finite, so their extension is separable.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, Theorem 2.6.
* J.-P. Serre, *Local Fields*, Chapter III, §6, Proposition 13.
-/

public section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel
open scoped AdicCompletionExtension NumberField

namespace IsDedekindDomain.HeightOneSpectrum

attribute [local instance] Ideal.Quotient.field

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
  [w.asIdeal.LiesOver v.asIdeal]

private theorem pow_dvd_differentIdeal_iff_le_multiplicity {n : ℕ} :
    w.asIdeal ^ n ∣ differentIdeal (𝓞 K) (𝓞 L) ↔
      n ≤ multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) :=
  (FiniteMultiplicity.of_prime_left
    (Ideal.prime_of_isPrime w.ne_bot w.isPrime)
    differentIdeal_ne_bot).pow_dvd_iff_le_multiplicity

/-- At a finite prime of a number-field extension, the different exponent is at least the
ramification index exactly when the ramification index vanishes in the base residue field. -/
theorem ramificationIdx_le_multiplicity_differentIdeal_iff :
    w.asIdeal.ramificationIdx (𝓞 K) ≤
      multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) ↔
    ((w.asIdeal.ramificationIdx (𝓞 K) : ℕ) : (𝓞 K) ⧸ v.asIdeal) = 0 := by
  rw [← pow_dvd_differentIdeal_iff_le_multiplicity w,
    TauCeti.pow_ramificationIdx_dvd_differentIdeal_iff (𝓞 K) v.ne_bot w.asIdeal]
  have : Algebra.IsSeparable ((𝓞 K) ⧸ v.asIdeal) ((𝓞 L) ⧸ w.asIdeal) := inferInstance
  simp only [this, not_true_eq_false, false_or]

/-- The exponent of the different at a finite prime is at least one less than its
ramification index. -/
theorem ramificationIdx_sub_one_le_multiplicity_differentIdeal
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 L))
    [w.asIdeal.LiesOver v.asIdeal] :
    w.asIdeal.ramificationIdx (𝓞 K) - 1 ≤
      multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) := by
  rw [← pow_dvd_differentIdeal_iff_le_multiplicity w,
    ← Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
  exact pow_sub_one_dvd_differentIdeal (𝓞 K) w.asIdeal _ v.ne_bot
    (Ideal.dvd_iff_le.mpr (Ideal.le_pow_ramificationIdx'
      (p := v.asIdeal) (P := w.asIdeal)))

/-- At a finite prime of a number-field extension, the different exponent is `e - 1` exactly
when the ramification index is nonzero in the base residue field. -/
theorem multiplicity_differentIdeal_eq_ramificationIdx_sub_one_iff :
    multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) =
      w.asIdeal.ramificationIdx (𝓞 K) - 1 ↔
    ((w.asIdeal.ramificationIdx (𝓞 K) : ℕ) : (𝓞 K) ⧸ v.asIdeal) ≠ 0 := by
  have hle := ramificationIdx_sub_one_le_multiplicity_differentIdeal v w
  have hpos : 0 < w.asIdeal.ramificationIdx (𝓞 K) :=
    Ideal.ramificationIdx_pos w.asIdeal (𝓞 K)
  constructor
  · intro heq hzero
    have := (ramificationIdx_le_multiplicity_differentIdeal_iff v w).mpr hzero
    omega
  · intro hnzero
    have hlt : ¬ w.asIdeal.ramificationIdx (𝓞 K) ≤
        multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) := by
      intro h
      exact hnzero ((ramificationIdx_le_multiplicity_differentIdeal_iff v w).mp h)
    omega

/-- The global different exponent at `w` is `e(w/v) - 1` precisely when the canonical
completed extension is tamely ramified. -/
@[simp]
theorem multiplicity_differentIdeal_eq_ramificationIdx_sub_one_iff_isTamelyRamified :
    multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) =
      w.asIdeal.ramificationIdx (𝓞 K) - 1 ↔
    TauCeti.IsTamelyRamified (v.adicCompletion K) (w.adicCompletion L) := by
  rw [multiplicity_differentIdeal_eq_ramificationIdx_sub_one_iff v w,
    TauCeti.isTamelyRamified_iff_natCast_ne_zero, v.ramificationIndex_adicCompletion w]
  simpa only [map_natCast] using
    (map_ne_zero (v.residueFieldEquivAdicCompletion (K := K))
      (a := (w.asIdeal.ramificationIdx (𝓞 K) : (𝓞 K) ⧸ v.asIdeal))).symm

/-- The global different exponent at `w` reaches `e(w/v)` precisely when the canonical
completed extension is wildly ramified. -/
@[simp]
theorem ramificationIdx_le_multiplicity_differentIdeal_iff_isWildlyRamified :
    w.asIdeal.ramificationIdx (𝓞 K) ≤
      multiplicity w.asIdeal (differentIdeal (𝓞 K) (𝓞 L)) ↔
    TauCeti.IsWildlyRamified (v.adicCompletion K) (w.adicCompletion L) := by
  rw [← TauCeti.not_isTamelyRamified_iff,
    ← multiplicity_differentIdeal_eq_ramificationIdx_sub_one_iff_isTamelyRamified v w,
    multiplicity_differentIdeal_eq_ramificationIdx_sub_one_iff v w,
    ramificationIdx_le_multiplicity_differentIdeal_iff v w, not_ne_iff]

end IsDedekindDomain.HeightOneSpectrum

end
