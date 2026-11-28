/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ComplexConjugation.Basic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Compositum
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius
import TauCeti.FieldTheory.Galois.Basic
import TauCeti.FieldTheory.Galois.Restriction
import TauCeti.NumberTheory.NumberField.AutomorphismAction
import TauCeti.NumberTheory.NumberField.ComplexConjugation.Cyclotomic
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import TauCeti.NumberTheory.NumberField.Frobenius.DecompositionGroup
import TauCeti.NumberTheory.NumberField.Frobenius.Restriction
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.NumberField.RamifiedPrimes
import TauCeti.NumberTheory.RamificationInertia.Tower

/-!
# Decomposition groups in cyclotomic composita

In `E = K(μₙ)`, a prime above `p` away from the level and base discriminant is fixed by
an automorphism precisely when its restriction and cyclotomic exponent are the same power
of the two Frobenius coordinates. Over an imaginary quadratic base at an inert prime, the
translates that fix the prime or take it to its conjugate correspond to even or odd powers
of the unit `−p mod n`, respectively.

The signed convention is that of `New.Parameters.smul_eq_self_iff_of_inert` and
`New.Parameters.smul_eq_star_iff_of_inert` in `New/Derivatives/Field/PrimeDecomposition.lean`
of [lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead1/grh).
-/

public section

open scoped NumberField Pointwise
open NumberField
open TauCeti.NumberField (complexConjugationAt complexConjugationAt_ne_one
  complexConjugationAt_restrictNormal_of_isComplex orderOf_complexConjugationAt)

namespace Ideal

variable {K E : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
  [Algebra K E] [IsScalarTower ℚ K E] [IsGalois ℚ K]
  {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} K E] {ζ : E}
  {p : ℕ} (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})]

/-- An automorphism of a cyclotomic compositum fixes a prime above `p` exactly when its two
coordinates are a common power of the two Frobenius coordinates. Here `τ` is an arithmetic
Frobenius at the contracted prime and `p` is prime to the level and base discriminant. -/
theorem smul_eq_self_iff_exists_pow_restrictNormal_and_autToPow (hζ : IsPrimitiveRoot ζ n)
    (hp : p.Prime) (hn : p.Coprime n) (hdisc : (discr K).natAbs.Coprime p)
    {τ : K ≃ₐ[ℚ] K} (hτ : IsArithFrobAt ℤ τ (Q.under (𝓞 K))) (σ : E ≃ₐ[ℚ] E) :
    σ • Q = Q ↔ ∃ j : ℕ, σ.restrictNormal K = τ ^ j ∧
      hζ.autToPow ℚ σ = ZMod.unitOfCoprime p hn ^ j := by
  have : IsGalois ℚ E :=
    IsCyclotomicExtension.isGalois_of_isGalois_of_isCyclotomicExtension ℚ K E {n}
  have hQ : Q ≠ ⊥ := ne_bot_of_liesOver_of_ne_bot (p := span {(p : ℤ)})
    (by simpa using hp.ne_zero) Q
  -- The cyclotomic extension can add ramification only at primes dividing the level.
  have hpd : (discr E).natAbs.Coprime p := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro h
    rcases IsCyclotomicExtension.prime_dvd_natAbs_discr_or_dvd_of_dvd_natAbs_discr K E n hp h
      with hd | hd
    · exact (hp.coprime_iff_not_dvd.mp hdisc.symm) hd
    · exact (hp.coprime_iff_not_dvd.mp hn) hd
  have : Algebra.IsUnramifiedAt (𝓞 ℚ) Q := by
    rw [← ramificationIdx_eq_one_iff, ramificationIdx_ringOfIntegers_rat_eq_int]
    exact ((coprime_natAbs_discr_iff_isUnramifiedIn (K := E) hp).mp hpd).ramificationIdx_eq_one
      ‹_›
  have : (Q.under (𝓞 K)).LiesOver (span {(p : ℤ)}) :=
    ⟨by rw [under_under, ← Q.over_def (span {(p : ℤ)})]⟩
  have : Algebra.IsUnramifiedAt (𝓞 ℚ) (Q.under (𝓞 K)) := by
    rw [← ramificationIdx_eq_one_iff, ramificationIdx_ringOfIntegers_rat_eq_int]
    exact ((coprime_natAbs_discr_iff_isUnramifiedIn (K := K) hp).mp hdisc).ramificationIdx_eq_one
      ‹_›
  obtain ⟨φ, hφ⟩ := NumberField.exists_isArithFrobAt ℚ Q hQ
  have hrest : AlgEquiv.restrictNormalHom K φ = τ :=
    NumberField.isArithFrobAt_eq_of_isUnramifiedAt hφ.restrictNormal
      ((isArithFrobAt_ringOfIntegers_rat_iff _ _).mpr hτ)
  have hcyc := ((isArithFrobAt_ringOfIntegers_rat_iff _ _).mp hφ).autToPow_eq_unitOfCoprime
    hζ hp hn
  have hj (j : ℕ) : AlgEquiv.restrictNormalHom K (φ ^ j) = τ ^ j := by
    rw [map_pow, hrest]
  rw [← MulAction.mem_stabilizer_iff, ← Q.zpowers_eq_stabilizer_of_isArithFrobAt hφ,
    ← (isOfFinOrder_of_finite φ).mem_powers_iff_mem_zpowers]
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨j, hj j, by rw [map_pow, hcyc]⟩
  · rintro ⟨j, h₁, h₂⟩
    refine ⟨j, IsCyclotomicExtension.restrictNormalHom_prod_autToPow_injective ℚ K E n hζ ?_⟩
    exact Prod.ext ((hj j).trans h₁.symm)
      (((map_pow _ _ _).trans (congrArg (· ^ j) hcyc)).trans h₂.symm)

variable [Algebra.IsQuadraticExtension ℚ K] [IsGalois ℚ E]

/-- At an inert prime of an imaginary quadratic base, the restriction of complex conjugation
of the host is arithmetic Frobenius at the base prime. -/
private theorem isArithFrobAt_restrictNormal_conj_of_inert (hp : p.Prime)
    (hdeg : (Q.under (𝓞 K)).inertiaDeg ℤ = 2) (w : InfinitePlace E) (hw : w.IsRamified ℚ)
    (hv : (w.comap (algebraMap K E)).IsComplex) :
    IsArithFrobAt ℤ ((complexConjugationAt ℚ w hw).restrictNormal K) (Q.under (𝓞 K)) := by
  let c := (complexConjugationAt ℚ w hw).restrictNormal K
  have hc : c ≠ 1 := by
    dsimp only [c]
    rw [complexConjugationAt_restrictNormal_of_isComplex ℚ w hw hv]
    exact complexConjugationAt_ne_one ℚ _ _
  have hP : Q.under (𝓞 K) ≠ ⊥ :=
    Ideal.IsIntegral.under_ne_bot _ (ne_bot_of_liesOver_of_ne_bot (p := span {(p : ℤ)})
      (by simpa using hp.ne_zero) Q)
  obtain ⟨τ, hτ⟩ := NumberField.exists_isArithFrobAt ℚ (Q.under (𝓞 K)) hP
  have hne : τ ≠ 1 := by
    intro h
    have hdvd := inertiaDeg_dvd_orderOf _ ((isArithFrobAt_ringOfIntegers_rat_iff _ _).mp hτ)
    rw [h, orderOf_one, hdeg] at hdvd
    exact (by decide : ¬ 2 ∣ 1) hdvd
  have heq : τ = c := (Algebra.IsQuadraticExtension.algEquiv_eq_one_or_eq ℚ K hc τ).resolve_left hne
  exact (isArithFrobAt_ringOfIntegers_rat_iff _ _).mp (heq ▸ hτ : IsArithFrobAt _ c _)

/-- At an inert prime of an imaginary quadratic base, an automorphism over the base fixes `Q`
when its cyclotomic exponent is an even power of `−p`, and sends `Q` to its conjugate when it
is an odd power. The right side specifies the parity by the exponent `i` on conjugation. -/
theorem smul_eq_complexConjugationAt_pow_smul_iff_of_inert (hζ : IsPrimitiveRoot ζ n)
    (hp : p.Prime) (hn : p.Coprime n) (hdeg : (Q.under (𝓞 K)).inertiaDeg ℤ = 2)
    (w : InfinitePlace E) (hw : w.IsRamified ℚ)
    (hv : (w.comap (algebraMap K E)).IsComplex) (σ : E ≃ₐ[K] E) (i : ℕ) :
    σ • Q = (complexConjugationAt ℚ w hw) ^ i • Q ↔
      ∃ j : ℕ, j ≡ i [MOD 2] ∧ hζ.autToPow ℚ (σ.restrictScalars ℚ) =
        (-ZMod.unitOfCoprime p hn) ^ j := by
  set c := complexConjugationAt ℚ w hw
  let r := AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := E) K
  set g := σ.restrictScalars ℚ
  have hrg : r g = 1 := (AlgEquiv.mem_range_restrictScalarsHom_iff_restrictNormal_eq_one
    ℚ K E g).mp ⟨σ, rfl⟩
  have hr (a : E ≃ₐ[ℚ] E) : r a = a.restrictNormal K :=
    AlgEquiv.restrictNormalHom_apply_eq_restrictNormal ℚ K E a
  have hrc : orderOf (r c) = 2 := by
    rw [hr, complexConjugationAt_restrictNormal_of_isComplex ℚ w hw hv,
      orderOf_complexConjugationAt]
  have hc : hζ.autToPow ℚ c = -1 := hζ.autToPow_complexConjugationAt w hw
  have hact : g • Q = σ • Q := AlgEquiv.restrictScalars_smul_ideal σ Q
  have hdisc : (discr K).natAbs.Coprime p := by
    have : (Q.under (𝓞 K)).LiesOver (span {(p : ℤ)}) :=
      ⟨by rw [under_under, ← Q.over_def (span {(p : ℤ)})]⟩
    have hle := TauCeti.RamificationInertia.ramificationIdx_mul_inertiaDeg_le_finrank
      ℤ (Q.under (𝓞 K))
    rw [hdeg, RingOfIntegers.rank, Algebra.IsQuadraticExtension.finrank_eq_two ℚ K] at hle
    have hpos := Ideal.ramificationIdx_pos ℤ (Q.under (𝓞 K))
    apply (coprime_natAbs_discr_iff_isUnramifiedIn hp).mpr
    rw [Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
    intro P _ hP
    rw [ramificationIdx_eq_of_isGaloisGroup (span {(p : ℤ)}) P (Q.under (𝓞 K)) Gal(K/ℚ)]
    omega
  have hfrob : IsArithFrobAt ℤ (c.restrictNormal K) (Q.under (𝓞 K)) :=
    Q.isArithFrobAt_restrictNormal_conj_of_inert hp hdeg w hw hv
  rw [← hact, ← inv_smul_eq_iff, ← mul_smul,
    Q.smul_eq_self_iff_exists_pow_restrictNormal_and_autToPow hζ hp hn hdisc hfrob]
  simp only [← hr, map_mul, map_inv, map_pow, hrg, mul_one, hc]
  refine exists_congr fun j ↦ ?_
  -- The base restriction has order two, so the same exponent controls the sign.
  have hpar : ((r c) ^ i)⁻¹ = (r c) ^ j ↔ j ≡ i [MOD 2] := by
    have h2 : (r c) ^ 2 = 1 := hrc ▸ pow_orderOf_eq_one (r c)
    rw [pow_two] at h2
    have hinv : (r c)⁻¹ = r c := inv_eq_of_mul_eq_one_left h2
    rw [← inv_pow, hinv, eq_comm, pow_eq_pow_iff_modEq, hrc]
  rw [hpar]
  refine and_congr_right fun hj ↦ ?_
  have hsign : (-1 : (ZMod n)ˣ) ^ i = (-1) ^ j := by
    have hd : orderOf (-1 : (ZMod n)ˣ) ∣ 2 := orderOf_dvd_of_pow_eq_one (by simp [pow_two])
    exact pow_eq_pow_iff_modEq.mpr (hj.of_dvd hd).symm
  rw [inv_mul_eq_iff_eq_mul, hsign, ← mul_pow, neg_one_mul]

end Ideal
