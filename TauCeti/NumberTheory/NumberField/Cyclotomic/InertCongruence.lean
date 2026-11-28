/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.CMField.Basic
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.RingTheory.RamificationInertia.Inertia
import TauCeti.NumberTheory.NumberField.CMField.Frobenius
import TauCeti.NumberTheory.NumberField.Cyclotomic.Compositum
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import TauCeti.NumberTheory.NumberField.Frobenius
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.NumberField.PrimeIdeal
import TauCeti.NumberTheory.RamificationInertia.Tower
import TauCeti.RingTheory.Frobenius
import TauCeti.RingTheory.Ideal.LiesOver

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

namespace IsPrimitiveRoot

variable {K E : Type*} [Field K] [CharZero K] [IsCMField K] [Algebra.IsQuadraticExtension ℚ K]
  [Field E] [NumberField E] [IsCMField E] [Algebra K E] [IsScalarTower ℚ K E]
  {m p : ℕ} [NeZero m] [IsCyclotomicExtension {m} K E] [Fact p.Prime]

open TauCeti.RamificationInertia in
/-- If `p` is inert in `K`, then for odd `n` the conjugate of an algebraic integer followed by
the `K`-automorphism of exponent `−p ^ n` is congruent to its `p ^ n`th power modulo the rational
prime `p`. Inertness is expressed by the residue degree of the ideal `(p)` in `𝓞 K`.
The existence of `σ` forces the level to be prime to `p`. -/
theorem natCast_dvd_pow_sub_smul_complexConj_of_inert {ζ : E} (hζ : IsPrimitiveRoot ζ m)
    (hf : (Ideal.span {(p : 𝓞 K)}).inertiaDeg ℤ = 2) {n : ℕ} (hn : Odd n)
    (σ : E ≃ₐ[K] E) (hσ : σ ζ = (ζ ^ (p ^ n))⁻¹) (x : 𝓞 E) :
    (p : 𝓞 E) ∣ x ^ (p ^ n) -
      ((σ.restrictScalars ℚ * (complexConj E).restrictScalars ℚ) • x) := by
  have : NumberField K := ⟨⟩
  let τ := σ.restrictScalars ℚ * (complexConj E).restrictScalars ℚ
  have hτK : τ.restrictNormal K = (complexConj K).restrictScalars ℚ := by
    ext a
    apply (algebraMap K E).injective
    rw [τ.restrictNormal_commutes, AlgEquiv.mul_apply]
    simp [complexConj_algebraMap]
  have hτζ : τ ζ = ζ ^ (p ^ n) := by
    have hconj := eq_inv_of_mul_eq_one_right
      (mul_complexConj_eq_one_of_pow_eq (NeZero.ne m) hζ.pow_eq_one (by simp))
    simp [τ, AlgEquiv.mul_apply, hconj, hσ]
  have hp : ¬ p ∣ m := by
    have hprim := hζ.map_of_injective τ.injective
    rw [hτζ, hζ.pow_iff_coprime (NeZero.pos m), Nat.coprime_pow_left_iff hn.pos] at hprim
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mp hprim
  have hm (Q : Ideal (𝓞 E)) [Q.LiesOver (span {(p : ℤ)})] : (m : 𝓞 E) ∉ Q := by
    simpa using (Q.algebraMap_mem_iff_dvd_of_liesOver (m : ℤ)).not.mpr
      (Int.natCast_dvd_natCast.not.mpr hp)
  have hfQ (Q : Ideal (𝓞 E)) [Q.LiesOver (span {(p : ℤ)})] :
      (Q.under (𝓞 K)).inertiaDeg ℤ = 2 := by
    rwa [Q.under_eq_span_natCast_of_inertiaDeg_ne_zero (hf.trans_ne (by decide))]
  have hun (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})] :
      Algebra.IsUnramifiedAt (𝓞 ℚ) Q := by
    have : Algebra.IsUnramifiedAt ℤ (Q.under (𝓞 K)) := by
      apply Ideal.ramificationIdx_eq_one_iff.mp
      have hb := ramificationIdx_mul_inertiaDeg_le_finrank ℤ (Q.under (𝓞 K))
      rw [hfQ Q, RingOfIntegers.rank, Algebra.IsQuadraticExtension.finrank_eq_two] at hb
      have hpos := Ideal.ramificationIdx_pos ℤ (Q.under (𝓞 K))
      omega
    have := Q.isUnramifiedAt_int_of_isCyclotomicExtension (K := K) (hm Q)
    exact Algebra.IsUnramifiedAt.of_restrictScalars ℤ Q
  have := IsCyclotomicExtension.isGalois_of_isGalois_of_isCyclotomicExtension ℚ K E {m}
  refine (TauCeti.NumberField.natCast_dvd_iff_forall_mem_primesOver hun _).mpr fun Q ⟨hQ, hQo⟩ ↦ ?_
  obtain ⟨φ, hφ⟩ := NumberField.exists_isArithFrobAt_int_of_liesOver Q (p := p)
  have hφζ : φ ζ = ζ ^ p := by
    have hi := hφ.apply_of_pow_eq_one hζ.toInteger_isPrimitiveRoot.pow_eq_one (hm Q)
    rw [Q.natCard_quotient_under_of_liesOver (n := p)] at hi
    simpa [MulSemiringAction.toAlgHom_apply, NumberField.algebraMap_smul_eq_apply,
      ← RingOfIntegers.coe_eq_algebraMap, hζ.coe_toInteger] using
      congrArg (algebraMap (𝓞 E) E) hi
  have hpw (j : ℕ) : (φ ^ j) ζ = ζ ^ (p ^ j) := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', AlgEquiv.mul_apply, ih, map_pow, hφζ, ← pow_mul, pow_succ']
  have heq : φ ^ n = τ := hζ.algEquiv_eq_of_restrictNormal_eq_of_apply_eq
    ((hφ.restrictNormal_pow_eq_complexConj (hfQ Q) hn).trans hτK.symm)
    ((hpw n).trans hτζ.symm)
  have h := hφ.mk_pow_smul n x
  rw [Q.natCard_quotient_under_of_liesOver (n := p), heq, ← map_pow] at h
  exact Ideal.Quotient.eq.mp h.symm

end IsPrimitiveRoot
