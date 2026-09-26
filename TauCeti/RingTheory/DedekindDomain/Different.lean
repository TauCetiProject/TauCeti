/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Different.Basic
public import TauCeti.RingTheory.Trace.QuotientPow

/-!
# Dedekind's different theorem: tame and wild primes

Let `B` be a Dedekind domain, module-finite over a Dedekind domain `A` with `Frac B / Frac A`
separable, let `p` be a maximal ideal of `A` and `P` a maximal ideal of `B` over it with
ramification index `e = e(P ∣ p)`.  Mathlib's `pow_sub_one_dvd_differentIdeal` gives the universal
half of Dedekind's different theorem, `P ^ (e - 1) ∣ 𝔡(B/A)`.  This file decides whether the next
power `P ^ e` divides the different as well: it does exactly when `P` is *not tame*, that is, when
the residue extension `(B ⧸ P) / (A ⧸ p)` is inseparable or the residue characteristic divides
`e`.  So the different exponent at `P` is exactly `e - 1` at the tame primes and at least `e` at
the others.

The criterion used is the trace criterion `TauCeti.dvd_differentIdeal_iff_forall_intTrace_mem`:
if `I * Q = p · B`, then `I` divides `𝔡(B/A)` exactly when the integral trace carries `Q` into
`p`.  Taking `I = P ^ e`
and `Q` the prime-to-`P` part of `p · B`, the Chinese remainder theorem turns the question into
whether the trace form of the `A ⧸ p`-algebra `B ⧸ P ^ e` vanishes, and
`Algebra.trace_quotient_pow_mk` evaluates it: the trace of a residue is `e` times its trace in
`B ⧸ P`.  Separability of the residue extension makes the latter trace nonzero somewhere, and
tameness keeps the factor `e` from killing it; in the wild case `e` is zero in `A ⧸ p`, and without
residue separability the residue trace is zero (`Algebra.trace_eq_zero_of_not_isSeparable`).

## Main results

* `TauCeti.pow_dvd_differentIdeal_iff_of_isCoprime`: the answer in the form that names a
  complement `Q` of `P ^ e` in `p · B`.
* `TauCeti.pow_ramificationIdx_dvd_differentIdeal_iff`: **Dedekind's different theorem, second
  part** — `P ^ e(P ∣ p) ∣ 𝔡(B/A)` exactly when the residue extension is inseparable or
  `e(P ∣ p)` vanishes in `A ⧸ p`.
* `TauCeti.multiplicity_differentIdeal_eq_ramificationIdx_sub_one_iff` and
  `TauCeti.ramificationIdx_le_multiplicity_differentIdeal_iff`: the multiplicity of `P` in the
  different is `e(P ∣ p) - 1` exactly when the residue extension is separable and `e(P ∣ p)` is
  nonzero in `A ⧸ p`, and it is at least `e(P ∣ p)` otherwise.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.5.1(b) and Corollary 3.5.5.
-/

public section

open Module

open scoped nonZeroDivisors

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

namespace TauCeti

variable (A : Type*) {B : Type*} [CommRing A] [CommRing B] [Algebra A B]
variable [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B] [Module.Finite A B]

attribute [local instance] Ideal.Quotient.field

/-- **Dedekind's different theorem at a prime power with a coprime complement.** If
`p · B = P ^ e * Q` with `P ^ e` and `Q` coprime and `p ≠ ⊥`, then `P ^ e` divides
`differentIdeal A B` exactly when the residue extension at `P` is inseparable or `e` vanishes in
the residue field `A ⧸ p`. -/
theorem pow_dvd_differentIdeal_iff_of_isCoprime
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥) (P Q : Ideal B) [P.IsMaximal] [P.LiesOver p] {e : ℕ}
    (hPQ : IsCoprime (P ^ e) Q) (hmul : P ^ e * Q = Ideal.map (algebraMap A B) p) :
    P ^ e ∣ differentIdeal A B ↔ ¬ Algebra.IsSeparable (A ⧸ p) (B ⧸ P) ∨ (e : A ⧸ p) = 0 := by
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp P
  have hQle : p ≤ Ideal.comap (algebraMap A B) Q := by
    rw [← Ideal.map_le_iff_le_comap, ← hmul]; exact Ideal.mul_le_right
  have hPle : p ≤ Ideal.comap (algebraMap A B) (P ^ e) := by
    rw [← Ideal.map_le_iff_le_comap, ← hmul]; exact Ideal.mul_le_left
  let instQ : Algebra (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.algebraQuotientOfLEComap hQle
  have : IsScalarTower A (A ⧸ p) (B ⧸ Q) := .of_algebraMap_eq' rfl
  let instPe : Algebra (A ⧸ p) (B ⧸ P ^ e) := Ideal.Quotient.algebraQuotientOfLEComap hPle
  have : IsScalarTower A (A ⧸ p) (B ⧸ P ^ e) := .of_algebraMap_eq' rfl
  have : Module.Finite (A ⧸ p) (B ⧸ Q) := .of_restrictScalars_finite A _ _
  have : Module.Finite (A ⧸ p) (B ⧸ P ^ e) := .of_restrictScalars_finite A _ _
  have : Module.Finite (A ⧸ p) (B ⧸ P) := .of_restrictScalars_finite A _ _
  -- the Chinese remainder decomposition of `B ⧸ pB`
  let ee : (B ⧸ Ideal.map (algebraMap A B) p) ≃ₐ[A ⧸ p] ((B ⧸ P ^ e) × B ⧸ Q) :=
    { __ := (Ideal.quotEquivOfEq hmul.symm).trans
        (Ideal.quotientMulEquivQuotientProd (P ^ e) Q hPQ)
      commutes' := Quotient.ind fun _ ↦ rfl }
  -- modulo `p`, the integral trace of an element of `Q` is `e` times its residue trace
  have htr (x : B) (hx : x ∈ Q) : Ideal.Quotient.mk p (Algebra.intTrace A B x) =
      e • Algebra.trace (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk P x) := by
    have hx₁ : (ee (Ideal.Quotient.mk _ x)).1 = Ideal.Quotient.mk (P ^ e) x := by simp [ee]
    have hx₂ : (ee (Ideal.Quotient.mk _ x)).2 = 0 := by
      simpa [ee, Ideal.Quotient.eq_zero_iff_mem] using hx
    rw [← Algebra.trace_quotient_eq_of_isDedekindDomain, ← Algebra.trace_eq_of_algEquiv ee,
      Algebra.trace_prod_apply, hx₁, hx₂, map_zero, add_zero,
      Algebra.trace_quotient_pow_mk hPbot e x]
  rw [dvd_differentIdeal_iff_forall_intTrace_mem A hp _ Q hmul]
  refine ⟨fun h ↦ ?_, fun h x hx ↦ ?_⟩
  · by_contra! hc
    obtain ⟨hsep, he⟩ := hc
    have he₀ : e ≠ 0 := by rintro rfl; simp at he
    -- a residue with nonzero trace, lifted to an element of `Q`
    obtain ⟨w, hw⟩ : ∃ w, Algebra.trace (A ⧸ p) (B ⧸ P) w ≠ 0 := by
      simpa [LinearMap.ext_iff] using Algebra.trace_ne_zero (A ⧸ p) (B ⧸ P)
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (ee.symm (Ideal.Quotient.mk _ z, 0))
    have hy' := congrArg ee hy
    rw [AlgEquiv.apply_symm_apply] at hy'
    have hyQ : y ∈ Q := by
      simpa [ee, Ideal.Quotient.eq_zero_iff_mem] using congrArg Prod.snd hy'
    have hyP : Ideal.Quotient.mk P y = Ideal.Quotient.mk P z := by
      have : Ideal.Quotient.mk (P ^ e) y = Ideal.Quotient.mk (P ^ e) z := by
        simpa [ee] using congrArg Prod.fst hy'
      exact Ideal.Quotient.eq.mpr (Ideal.pow_le_self he₀ (Ideal.Quotient.eq.mp this))
    have := htr y hyQ
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (h y hyQ), hyP, nsmul_eq_mul] at this
    exact mul_ne_zero he hw this.symm
  · rw [← Ideal.Quotient.eq_zero_iff_mem, htr x hx]
    rcases h with h | h
    · rw [Algebra.trace_eq_zero_of_not_isSeparable h, LinearMap.zero_apply, smul_zero]
    · rw [nsmul_eq_mul, h, zero_mul]

/-- **Dedekind's different theorem, second part** (Stichtenoth, Theorem 3.5.1(b) and
Corollary 3.5.5): for a maximal ideal `P` of `B` over a nonzero maximal ideal `p` of `A`, the power
`P ^ e(P ∣ p)` divides the different ideal exactly when `P` is not tame, that is, when the residue
extension at `P` is inseparable or `e(P ∣ p)` vanishes in the residue field `A ⧸ p`.

Together with Mathlib's `pow_sub_one_dvd_differentIdeal`, the different exponent at `P` is
therefore `e(P ∣ p) - 1` at the tame primes and at least `e(P ∣ p)` at all others. -/
theorem pow_ramificationIdx_dvd_differentIdeal_iff
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal B) [P.IsMaximal] [P.LiesOver p] :
    P ^ P.ramificationIdx A ∣ differentIdeal A B ↔
      ¬ Algebra.IsSeparable (A ⧸ p) (B ⧸ P) ∨ ((P.ramificationIdx A : ℕ) : A ⧸ p) = 0 := by
  have hp' : Ideal.map (algebraMap A B) p ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  obtain ⟨Q, h₁, h₂⟩ := Ideal.eq_prime_pow_mul_coprime hp' P
  rw [← Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count p P hp'] at h₂
  exact pow_dvd_differentIdeal_iff_of_isCoprime A hp P Q
    (Ideal.isCoprime_iff_sup_eq.mpr h₁).pow_left h₂.symm

section Multiplicity

variable [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

variable {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
include hp

/-- **Dedekind's different theorem, second part, as a bound on the exponent**: the multiplicity
of `P` in the different ideal is at least `e(P ∣ p)` exactly when the residue extension is
inseparable or `e(P ∣ p)` vanishes in the residue field `A ⧸ p`. -/
theorem ramificationIdx_le_multiplicity_differentIdeal_iff :
    P.ramificationIdx A ≤ multiplicity P (differentIdeal A B) ↔
      ¬ Algebra.IsSeparable (A ⧸ p) (B ⧸ P) ∨ ((P.ramificationIdx A : ℕ) : A ⧸ p) = 0 := by
  rw [← pow_dvd_differentIdeal_iff_le_multiplicity A (Ideal.ne_bot_of_liesOver_of_ne_bot hp P),
    pow_ramificationIdx_dvd_differentIdeal_iff A hp P]

/-- **Dedekind's different theorem, the tame case, as an exponent**: the multiplicity of `P` in
the different ideal is exactly `e(P ∣ p) - 1` when the residue extension is separable and
`e(P ∣ p)` is nonzero in the residue field `A ⧸ p`. -/
theorem multiplicity_differentIdeal_eq_ramificationIdx_sub_one_iff :
    multiplicity P (differentIdeal A B) = P.ramificationIdx A - 1 ↔
      Algebra.IsSeparable (A ⧸ p) (B ⧸ P) ∧ ((P.ramificationIdx A : ℕ) : A ⧸ p) ≠ 0 := by
  have hle := ramificationIdx_sub_one_le_multiplicity_differentIdeal A hp P
  have hpos := Ideal.ramificationIdx_pos P A
  rw [← not_not (a := Algebra.IsSeparable (A ⧸ p) (B ⧸ P)), ne_eq, ← not_or,
    ← ramificationIdx_le_multiplicity_differentIdeal_iff A hp P]
  omega

end Multiplicity

end TauCeti
