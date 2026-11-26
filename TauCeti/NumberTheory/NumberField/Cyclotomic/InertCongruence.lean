/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.Basic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.Unramified.Locus
import TauCeti.NumberTheory.NumberField.Cyclotomic.Compositum
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import TauCeti.NumberTheory.NumberField.Frobenius.Congruence
import TauCeti.NumberTheory.NumberField.Frobenius.Restriction
import TauCeti.NumberTheory.NumberField.Frobenius
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.RamificationInertia.Tower

/-!
# The inert-prime congruence in a cyclotomic compositum

Let `E = K(ζ)` for an imaginary quadratic field `K`, and let `p` be inert in `K` and
prime to the cyclotomic level. For odd `n`, the `n`th power of Frobenius restricts to conjugation
on `K` and raises `ζ` to `p ^ n`. Composing with conjugation makes it a `K`-automorphism and
negates its cyclotomic exponent. This identifies the signed cyclotomic automorphism used to
compare a power of an algebraic integer with the conjugate at its partner embedding.

The congruence is modulo the rational prime itself, not just one prime above it. For this
form of the congruence, see `New.Parameters.natCast_dvd_pow_sub_galOfPlaceInt_star` in
`New/Derivatives/Field/PrimeDecomposition.lean` of lsernau/grh-lean at `72fead1`.
-/

public section

open scoped NumberField
open Ideal NumberField NumberField.IsCMField

namespace TauCeti.NumberField

section

variable {K E : Type*} [Field K] [NumberField K] [IsCMField K] [Algebra.IsQuadraticExtension ℚ K]
  [Field E] [NumberField E] [IsCMField E] [Algebra K E] [IsScalarTower ℚ K E]
  {m p : ℕ} [NeZero m] [IsCyclotomicExtension {m} K E] [Fact p.Prime]

omit [IsCMField E] in
/-- For odd `n`, the `n`th power of a Frobenius over an inert rational prime restricts to
complex conjugation on the imaginary quadratic subfield. -/
private theorem restrictNormal_pow_eq_complexConj (Q : Ideal (𝓞 E)) [Q.IsPrime]
    {φ : E ≃ₐ[ℚ] E} (hφ : IsArithFrobAt ℤ φ Q)
    (hf : (Q.under (𝓞 K)).inertiaDeg ℤ = 2) {n : ℕ} (hn : Odd n) :
    (φ ^ n).restrictNormal K = (complexConj K).restrictScalars ℚ := by
  have hφK := (Ideal.isArithFrobAt_ringOfIntegers_rat_iff (φ.restrictNormal K) (Q.under (𝓞 K))).mp
    ((Ideal.isArithFrobAt_ringOfIntegers_rat_iff φ Q).mpr hφ).restrictNormal
  have hdiv := Ideal.inertiaDeg_dvd_orderOf (Q.under (𝓞 K)) hφK
  rw [hf] at hdiv
  apply AlgEquiv.eq_complexConj_of_ne_one
  intro h
  let r : (E ≃ₐ[ℚ] E) →* (K ≃ₐ[ℚ] K) := AlgEquiv.restrictNormalHom K
  have hpow : r (φ ^ n) = 1 := h
  rw [map_pow] at hpow
  have he := hdiv.trans (orderOf_dvd_iff_pow_eq_one.mpr hpow)
  obtain ⟨k, hk⟩ := hn
  omega

omit [NumberField E] [IsCMField K] [IsCMField E] [Algebra.IsQuadraticExtension ℚ K] in
/-- The prime of the quadratic subfield below a prime above an inert `p` is `(p)` itself. -/
private theorem under_eq_span_of_inertiaDeg_eq_two
    (hf : (Ideal.span {(p : 𝓞 K)}).inertiaDeg ℤ = 2)
    (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    Q.under (𝓞 K) = span {(p : 𝓞 K)} := by
  have hprime : (span {(p : 𝓞 K)} : Ideal (𝓞 K)).IsPrime := by
    by_contra h
    simp [inertiaDeg_of_not_isPrime _ _ h] at hf
  have hmax := hprime.isMaximal (by simpa using (Fact.out : p.Prime).ne_zero)
  have hQprime : (Q.under (𝓞 K)).IsPrime := inferInstance
  refine (hmax.eq_of_le hQprime.ne_top ?_).symm
  rw [span_singleton_le_iff_mem, mem_under, map_natCast]
  simpa using (liesOver_span_iff (IsPrime.ne_top ‹Q.IsPrime›)
    (Nat.prime_iff_prime_int.mp Fact.out)).mp (inferInstance : Q.LiesOver (span {(p : ℤ)}))

omit [IsCMField K] [IsCMField E] [IsScalarTower ℚ K E] [NeZero m] in
/-- If the ideal `(p)` has residue degree two in a quadratic number field, then every prime of
its cyclotomic extension of level prime to `p` above `p` is unramified. -/
theorem isUnramifiedAt_of_inertiaDeg_span_natCast_eq_two
    (hf : (Ideal.span {(p : 𝓞 K)}).inertiaDeg ℤ = 2) (hp : ¬ p ∣ m)
    (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
    Algebra.IsUnramifiedAt (𝓞 ℚ) Q := by
  let P := Q.under (𝓞 K)
  have hPf : (Q.under (𝓞 K)).inertiaDeg ℤ = 2 :=
    (under_eq_span_of_inertiaDeg_eq_two hf Q).symm ▸ hf
  have : P.IsPrime := inferInstanceAs (Q.under (𝓞 K)).IsPrime
  have : Q.LiesOver P := Ideal.over_under Q
  have hPo : P.LiesOver (span {(p : ℤ)}) := Ideal.LiesOver.tower_bot Q P _
  have hP1 : P.ramificationIdx ℤ = 1 := by
    have hb := TauCeti.RamificationInertia.ramificationIdx_mul_inertiaDeg_le_finrank ℤ P
    rw [hPf, RingOfIntegers.rank, Algebra.IsQuadraticExtension.finrank_eq_two] at hb
    have hpos := Ideal.ramificationIdx_pos ℤ P
    omega
  have hm : (m : 𝓞 K) ∉ P := fun h ↦ hp (by
    have hi := (Ideal.mem_of_liesOver P (span {(p : ℤ)}) (m : ℤ)).mpr (by simpa using h)
    exact Int.natCast_dvd_natCast.mp (Ideal.mem_span_singleton.mp hi))
  have := IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem E m hm Q
  apply Ideal.ramificationIdx_eq_one_iff.mp
  rw [Ideal.ramificationIdx_ringOfIntegers_rat_eq_int, Ideal.ramificationIdx_tower P Q,
    hP1, one_mul, Ideal.ramificationIdx_eq_one_of_isUnramifiedAt]

/-- If `p` is inert in `K`, then for odd `n` the conjugate of an algebraic integer followed by
the `K`-automorphism of exponent `−p ^ n` is congruent to its `p ^ n`th power modulo the rational
prime `p`. Inertness is expressed by the residue degree of the ideal `(p)` in `𝓞 K`.
The existence of `σ` forces the level to be prime to `p`. -/
theorem natCast_dvd_pow_sub_smul_complexConj_of_inert {ζ : E} (hζ : IsPrimitiveRoot ζ m)
    (hf : (Ideal.span {(p : 𝓞 K)}).inertiaDeg ℤ = 2) {n : ℕ} (hn : Odd n)
    (σ : E ≃ₐ[K] E) (hσ : σ ζ = (ζ ^ (p ^ n))⁻¹) (x : 𝓞 E) :
    (p : 𝓞 E) ∣ x ^ (p ^ n) -
      ((σ.restrictScalars ℚ * (complexConj E).restrictScalars ℚ) • x) := by
  let τ := σ.restrictScalars ℚ * (complexConj E).restrictScalars ℚ
  have hτK : τ.restrictNormal K = (complexConj K).restrictScalars ℚ := by
    ext a
    apply (algebraMap K E).injective
    rw [τ.restrictNormal_commutes, AlgEquiv.mul_apply]
    simp [complexConj_algebraMap]
  have hτζ : τ ζ = ζ ^ (p ^ n) := by
    have hconj : complexConj E ζ = ζ⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [mul_comm]
      exact mul_complexConj_eq_one_of_pow_eq (NeZero.ne m) hζ.pow_eq_one (by simp)
    simp [τ, AlgEquiv.mul_apply, hconj, hσ]
  have hn0 : 0 < n := by obtain ⟨k, hk⟩ := hn; omega
  have hp : ¬ p ∣ m := by
    have hprim := hζ.map_of_injective τ.injective
    rw [hτζ, hζ.pow_iff_coprime (NeZero.pos m), Nat.coprime_pow_left_iff hn0] at hprim
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hprim
  have : IsGalois ℚ E :=
    IsCyclotomicExtension.isGalois_of_isGalois_of_isCyclotomicExtension ℚ K E {m}
  refine (natCast_dvd_iff_forall_mem_primesOver
    (isUnramifiedAt_of_inertiaDeg_span_natCast_eq_two hf hp) _).mpr fun Q ⟨hQ, hQo⟩ ↦ ?_
  have hP := under_eq_span_of_inertiaDeg_eq_two hf Q
  obtain ⟨φ, hφ⟩ := NumberField.exists_isArithFrobAt_int_of_liesOver Q (p := p)
  have hφζ : φ ζ = ζ ^ p := by
    have hm : (m : 𝓞 E) ∉ Q := fun h ↦ hp (by
      have hi := (Ideal.mem_of_liesOver Q (span {(p : ℤ)}) (m : ℤ)).mpr (by simpa using h)
      exact Int.natCast_dvd_natCast.mp (Ideal.mem_span_singleton.mp hi))
    have hi := hφ.apply_of_pow_eq_one hζ.toInteger_isPrimitiveRoot.pow_eq_one hm
    rw [← Q.over_def (span {(p : ℤ)}), Int.card_ideal_quot] at hi
    simpa [MulSemiringAction.toAlgHom_apply, NumberField.algebraMap_smul_eq_apply,
      ← RingOfIntegers.coe_eq_algebraMap, hζ.coe_toInteger] using
      congrArg (algebraMap (𝓞 E) E) hi
  have hpw (j : ℕ) : (φ ^ j) ζ = ζ ^ (p ^ j) := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hφζ, ← pow_mul, pow_succ']
  have heq : φ ^ n = τ := hζ.algEquiv_eq_of_restrictNormal_eq_of_apply_eq
    ((restrictNormal_pow_eq_complexConj Q hφ (hP.symm ▸ hf) hn).trans hτK.symm)
    ((hpw n).trans hτζ.symm)
  have h := hφ.quotient_mk_pow_smul n x
  rw [← Q.over_def (span {(p : ℤ)}), Int.card_ideal_quot, heq, ← map_pow] at h
  exact Ideal.Quotient.eq.mp h.symm

end

end TauCeti.NumberField
