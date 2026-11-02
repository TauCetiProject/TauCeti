/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.SupSeminorm

import Mathlib.FieldTheory.Minpoly.Finite
import Mathlib.RingTheory.Polynomial.RationalRoot
import TauCeti.RingTheory.Affinoid.MaximumModulus
import TauCeti.RingTheory.Affinoid.MinimalPolynomial
import TauCeti.RingTheory.Affinoid.NoetherNormalization
import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.UniqueFactorization

/-!
# The value group of the supremum seminorm

For an affinoid algebra `A` over a complete nonarchimedean field `K`, a single positive
integer `m`, depending only on `A`, makes every `supSeminorm K f ^ m` the norm of a scalar
in `K`. Consequently the same exponent permits normalizing every element of positive
supremum seminorm: some unit scalar multiple of `f ^ m` has supremum seminorm one.

For a domain, finite Noether normalization bounds the degrees of all minimal polynomials
by the number of module generators. The minimal-polynomial formula for the supremum
seminorm and a coefficient attaining the Gauss norm then give a denominator bounded by
that number. Its factorial clears all denominators. For a general algebra, a product of
the exponents of its finitely many minimal-prime quotients works simultaneously.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.2.1.
-/

public section

namespace TauCeti.IsAffinoidAlgebra

open _root_.MvPowerSeries Polynomial

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A]

private theorem exists_supSeminorm_pow_eq_norm_of_isDomain [IsDomain A]
    (hA : IsAffinoidAlgebra K A) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ f : A, ∃ c : K, supSeminorm K f ^ m = ‖c‖ := by
  classical
  obtain ⟨n, g, hg, hfin⟩ := hA.exists_finite_injective
  let T := IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)
  let := g.toRingHom.toAlgebra
  have : IsScalarTower K T A := IsScalarTower.of_algebraMap_eq fun c ↦ (g.commutes c).symm
  have : Module.Finite T A := hfin
  have : Algebra.IsIntegral T A := Algebra.IsIntegral.of_finite T A
  have : FaithfulSMul T A := (faithfulSMul_iff_algebraMap_injective T A).mpr hg
  let N := (⊤ : Submodule T A).spanFinrank
  refine ⟨N.factorial, Nat.factorial_pos N, fun f ↦ ?_⟩
  have hf := Algebra.IsIntegral.isIntegral (R := T) f
  have hpos := minpoly.natDegree_pos hf
  have : Nonempty (Fin (minpoly T f).natDegree) := ⟨⟨0, hpos⟩⟩
  obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i : Fin (minpoly T f).natDegree ↦
    supSeminorm K ((minpoly T f).coeff i) ^ (1 / ((minpoly T f).natDegree - i : ℝ)))
  obtain ⟨t, ht⟩ := exists_norm_coeff_eq_norm ((minpoly T f).coeff i)
  have hdvd : (minpoly T f).natDegree - i ∣ N.factorial :=
    Nat.dvd_factorial (Nat.sub_pos_of_lt i.2)
      ((Nat.sub_le _ _).trans (minpoly.natDegree_le_spanFinrank T f))
  obtain ⟨q, hq⟩ := hdvd
  refine ⟨coeff t (((minpoly T f).coeff i : T) : MvPowerSeries (Fin n) K) ^ q, ?_⟩
  have heq : supSeminorm K f ^ ((minpoly T f).natDegree - i) =
      ‖coeff t (((minpoly T f).coeff i : T) : MvPowerSeries (Fin n) K)‖ := by
    rw [hA.supSeminorm_eq_iSup_minpoly_coeff_rpow (A := T), ← hi,
      ← Nat.cast_sub i.2.le, one_div,
      Real.rpow_inv_natCast_pow (supSeminorm_nonneg _) (Nat.sub_ne_zero_of_lt i.2),
      TauCeti.MvPowerSeries.supSeminorm_eq_norm, ht]
  rw [hq, pow_mul, heq, norm_pow]

/-- A single positive exponent, depending only on the affinoid algebra, sends every
supremum seminorm into the value group of the base field (with zero included). -/
theorem exists_supSeminorm_pow_eq_norm (hA : IsAffinoidAlgebra K A) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ f : A, ∃ c : K, supSeminorm K f ^ m = ‖c‖ := by
  classical
  cases subsingleton_or_nontrivial A with
  | inl h =>
    exact ⟨1, le_rfl, fun f ↦ ⟨0, by simp [supSeminorm_eq_zero_of_subsingleton]⟩⟩
  | inr h =>
    have := hA.isNoetherianRing
    have : Finite (minimalPrimes A) := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
    let := Fintype.ofFinite (minimalPrimes A)
    have hcomp (𝔭 : minimalPrimes A) :
        ∃ m : ℕ, 1 ≤ m ∧ ∀ f : A ⧸ 𝔭.1, ∃ c : K, supSeminorm K f ^ m = ‖c‖ := by
      have : 𝔭.1.IsPrime := Ideal.IsMinimalPrime.isPrime 𝔭.2
      exact (hA.quotient 𝔭.1).exists_supSeminorm_pow_eq_norm_of_isDomain
    choose m hmpos hm using hcomp
    refine ⟨∏ 𝔭, m 𝔭, Finset.one_le_prod fun 𝔭 _ ↦ hmpos 𝔭, fun f ↦ ?_⟩
    obtain ⟨𝔭, h𝔭, hsup⟩ := hA.exists_mem_minimalPrimes_supSeminorm_eq f
    obtain ⟨c, hc⟩ := hm ⟨𝔭, h𝔭⟩ (Ideal.Quotient.mk 𝔭 f)
    obtain ⟨q, hq⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ (⟨𝔭, h𝔭⟩ : minimalPrimes A))
    refine ⟨c ^ q, ?_⟩
    rw [hq, pow_mul, ← hsup, hc, norm_pow]

/-- A single positive exponent permits normalizing every element of positive supremum
seminorm by a unit scalar from the base field. -/
theorem exists_supSeminorm_smul_pow_eq_one (hA : IsAffinoidAlgebra K A) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ f : A, 0 < supSeminorm K f →
      ∃ c : Kˣ, supSeminorm K ((c : K) • f ^ m) = 1 := by
  obtain ⟨m, hm, h⟩ := hA.exists_supSeminorm_pow_eq_norm
  refine ⟨m, hm, fun f hf ↦ ?_⟩
  obtain ⟨c, hc⟩ := h f
  have hc0 : c ≠ 0 := norm_pos_iff.mp (hc ▸ pow_pos hf m)
  refine ⟨(Units.mk0 c hc0)⁻¹, ?_⟩
  rw [hA.supSeminorm_smul, hA.supSeminorm_pow f (by omega), hc]
  simp [norm_ne_zero_iff.mpr hc0]

end TauCeti.IsAffinoidAlgebra
