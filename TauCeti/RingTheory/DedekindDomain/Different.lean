/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Different
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

The criterion used is the trace criterion: if `I * Q = p · B`, then `I` divides `𝔡(B/A)` exactly
when the integral trace carries `Q` into `p`.  One direction is Mathlib's
`not_dvd_differentIdeal_of_intTrace_not_mem`; the other, stated here as
`TauCeti.dvd_differentIdeal_iff_forall_intTrace_mem`, is the argument Mathlib runs inline for
`pow_sub_one_dvd_differentIdeal` and `dvd_differentIdeal_of_not_isSeparable`.  Taking `I = P ^ e`
and `Q` the prime-to-`P` part of `p · B`, the Chinese remainder theorem turns the question into
whether the trace form of the `A ⧸ p`-algebra `B ⧸ P ^ e` vanishes, and
`Algebra.trace_quotient_pow_mk` evaluates it: the trace of a residue is `e` times its trace in
`B ⧸ P`.  Separability of the residue extension makes the latter trace nonzero somewhere, and
tameness keeps the factor `e` from killing it; in the wild case `e` is zero in `A ⧸ p`, and without
residue separability the residue trace is zero (`Algebra.trace_eq_zero_of_not_isSeparable`).

## Main results

* `TauCeti.dvd_differentIdeal_iff_forall_intTrace_mem`: the trace criterion for divisibility of
  the different ideal.
* `TauCeti.pow_dvd_differentIdeal_iff_of_isCoprime`: the answer in the form that names a
  complement `Q` of `P ^ e` in `p · B`.
* `TauCeti.pow_ramificationIdx_dvd_differentIdeal_iff`: **Dedekind's different theorem, second
  part** — `P ^ e(P ∣ p) ∣ 𝔡(B/A)` exactly when the residue extension is inseparable or
  `e(P ∣ p)` vanishes in `A ⧸ p`.
* `TauCeti.not_pow_ramificationIdx_dvd_differentIdeal`: its tame direction — for a tame `P` with
  separable residue extension, `P ^ e(P ∣ p) ∤ 𝔡(B/A)`.

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

/-- **The trace criterion for divisibility of the different ideal.** If `I * Q = p · B` for a
nonzero ideal `p` of `A`, then `I` divides `differentIdeal A B` exactly when the integral trace
carries the complement `Q` into `p`.

The implication from a trace outside `p` to non-divisibility is Mathlib's
`not_dvd_differentIdeal_of_intTrace_not_mem`; the converse identifies `I⁻¹` with `Q / p · B`, the
argument Mathlib runs inline for `pow_sub_one_dvd_differentIdeal` and
`dvd_differentIdeal_of_not_isSeparable`. -/
theorem dvd_differentIdeal_iff_forall_intTrace_mem
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} (hp : p ≠ ⊥) (I Q : Ideal B) (hIQ : I * Q = Ideal.map (algebraMap A B) p) :
    I ∣ differentIdeal A B ↔ ∀ x ∈ Q, Algebra.intTrace A B x ∈ p := by
  refine ⟨fun hdvd x hx ↦ ?_, fun htr ↦ ?_⟩
  · by_contra hx'
    exact not_dvd_differentIdeal_of_intTrace_not_mem A I Q hIQ x hx hx' hdvd
  let K := FractionRing A
  let L := FractionRing B
  have hp' : Ideal.map (algebraMap A B) p ≠ ⊥ :=
    (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective A B)).not.mpr hp
  have hQ : Q ≠ ⊥ := fun h ↦ hp' (by rw [← hIQ, h, Ideal.mul_bot])
  have hI : I ≠ ⊥ := fun h ↦ hp' (by rw [← hIQ, h, Ideal.bot_mul])
  -- `I⁻¹ = Q / p · B` as fractional ideals of `B`
  have hIinv : ((I : FractionalIdeal B⁰ L))⁻¹ = Q / p.map (algebraMap A B) := by
    apply inv_involutive.injective
    simp only [← hIQ, FractionalIdeal.coeIdeal_mul, inv_div, mul_div_assoc]
    rw [div_self (by simpa), mul_one, inv_inv]
  rw [Ideal.dvd_iff_le, differentialIdeal_le_iff (K := K) (L := L) hI, hIinv,
    Submodule.map_le_iff_le_comap]
  intro x hx
  rw [Submodule.restrictScalars_mem, FractionalIdeal.mem_coe,
    FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp')] at hx
  rw [Submodule.mem_comap, LinearMap.coe_restrictScalars, ← FractionalIdeal.coe_one,
    ← div_self (G₀ := FractionalIdeal A⁰ K) (a := p) (by simpa using hp),
    FractionalIdeal.mem_coe, FractionalIdeal.mem_div_iff_of_ne_zero (by simpa using hp)]
  simp only [FractionalIdeal.mem_coeIdeal, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hx
  intro y hy'
  obtain ⟨y, hy, rfl : algebraMap A K _ = _⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy'
  obtain ⟨z, hz, hz'⟩ := hx _ (Ideal.mem_map_of_mem _ hy)
  have : Algebra.trace K L (algebraMap B L z) ∈ (p : FractionalIdeal A⁰ K) := by
    rw [← Algebra.algebraMap_intTrace (A := A)]
    exact ⟨Algebra.intTrace A B z, htr z hz, rfl⟩
  rwa [mul_comm, ← smul_eq_mul, ← map_smul, Algebra.smul_def, mul_comm,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A B L, ← hz']

/-- **Dedekind's different theorem at a prime power with a coprime complement.** If
`p · B = P ^ e * Q` with `P ^ e` and `Q` coprime and `p ≠ ⊥`, then `P ^ e` divides
`differentIdeal A B` exactly when the residue extension at `P` is inseparable or `e` vanishes in
the residue field `A ⧸ p`.

Modulo `p`, the integral trace of an element of `Q` is the trace of its residue in `B ⧸ P ^ e`,
which is `e` times its trace in the residue field `B ⧸ P` (`Algebra.trace_quotient_pow_mk`); the
trace criterion `TauCeti.dvd_differentIdeal_iff_forall_intTrace_mem` then reads off the answer. -/
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
therefore `e(P ∣ p) - 1` at the tame primes and at least `e(P ∣ p)` at all others.  The complement
of `P ^ e(P ∣ p)` in `p · B` is produced by `Ideal.eq_prime_pow_mul_coprime`, whose exponent is the
ramification index by `Ideal.IsDedekindDomain.ramificationIdx_eq_normalizedFactors_count`. -/
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

/-- **Dedekind's different theorem, the tame half** (Stichtenoth, Theorem 3.5.1(b)): at a prime
`P` whose residue extension is separable and whose ramification index is invertible in the residue
field of `p`, the different ideal is divisible by `P ^ (e - 1)` — Mathlib's
`pow_sub_one_dvd_differentIdeal` — but not by `P ^ e`. -/
theorem not_pow_ramificationIdx_dvd_differentIdeal
    [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    {p : Ideal A} [p.IsMaximal] (hp : p ≠ ⊥) (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    [hsep : Algebra.IsSeparable (A ⧸ p) (B ⧸ P)]
    (he : ((P.ramificationIdx A : ℕ) : A ⧸ p) ≠ 0) :
    ¬ P ^ P.ramificationIdx A ∣ differentIdeal A B := by
  rw [pow_ramificationIdx_dvd_differentIdeal_iff A hp P, not_or, not_not]
  exact ⟨hsep, he⟩

end TauCeti
