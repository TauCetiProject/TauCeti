/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
public import TauCeti.NumberTheory.Padics.RingHoms
public import TauCeti.RingTheory.Iwasawa.Delta
public import TauCeti.RingTheory.Iwasawa.EulerQuotient

import Mathlib.RingTheory.AdjoinRoot
import TauCeti.Algebra.Module.Torsion.EulerQuotient
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Iwasawa.CyclotomicGrowth
import TauCeti.RingTheory.Length
import TauCeti.RingTheory.Norm.Cokernel
import TauCeti.RingTheory.Polynomial.Cyclotomic.PrimePow
import TauCeti.RingTheory.Polynomial.Distinguished
import TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot
import TauCeti.RingTheory.Polynomial.Resultant.Basic
import TauCeti.RingTheory.PowerSeries.AdicComplete
import TauCeti.RingTheory.PowerSeries.Weierstrass.Norm
import TauCeti.RingTheory.QuotSMulTop
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# The cyclotomic cutoff and Iwasawa's growth formula

Let `O` be a discrete valuation ring, complete for its maximal ideal `𝔪`, with finite residue field
`κ` of cardinality `q` and characteristic `p`, let `Λ = O⟦X⟧`, and let `M` be a finitely generated
`Λ`-module with Iwasawa invariants `μ = μ(M)`, `λ = λ(M)`, and characteristic polynomial `F_M`.
For integers `n₀` and `n`, define the *cyclotomic transition polynomial*

```text
ν_{n, n₀} = ∏_{n₀ ≤ j ≤ n} Φ_{p ^ j}(X + 1) ∈ O[X].
```

When `n₀ = 0` this is `ω_n = (1 + X) ^ p ^ n - 1`; when `1 ≤ n₀ ≤ n + 1` it satisfies
`ω_{n₀ - 1} · ν_{n, n₀} = ω_n`; and when `n < n₀` it is the empty product `1`.

## The cyclotomic cutoff

If `F_M` shares a root with some `ω_n`, the quotients `M ⧸ ω_n M` are infinite for all sufficiently
large `n`; stripping off the first `n₀` cyclotomic factors replaces `ω_n` by `ν_{n, n₀}`. Over any
complete discrete valuation ring `O` with finite residue field and `(p : O) ≠ 0`, a finitely
generated torsion `Λ`-module `M` has finite quotients `M ⧸ ν_{n, n₀} M` for all `n` if and only if
the complementary product `∏_{j < n₀} Φ_{p ^ j}(X + 1)` carries the delta submodule
`M_δ = ⋃_k M[ω_k]` to a finite submodule
(`TauCeti.Iwasawa.finite_quotSMulTop_growthTransition_iff`). In particular, since `M` is
noetherian, `M_δ = M[ω_m]` for some `m`, so choosing `n₀ = m + 1` always makes `M ⧸ ν_{n, n₀} M`
finite for every `n` (`TauCeti.Iwasawa.exists_finite_quotSMulTop_growthTransition`).

The hypothesis `(p : O) ≠ 0` is sharp: in equal characteristic `p` (`O = 𝔽_p⟦t⟧`), every shifted
cyclotomic polynomial `Φ_{p ^ j}(X + 1)` is a power of `X`, so `X` kills the delta submodule of
`Λ ⧸ (X)` yet `Λ ⧸ (X, ν_{n, n₀})` is infinite for every `n₀` and every `n ≥ n₀`.

## Iwasawa's growth formula

When `O` has mixed characteristic with absolute ramification index `e = v_O(p) > 0`, suppose
`M ⧸ ν_{n, n₀} M` is finite for every `n`. Then there exist an integer `ν` and a threshold `N` such
that for every `k ≥ N`,

```text
#(M ⧸ ν_{k, n₀} M) = q ^ (μ · p ^ k + e · λ · k + ν).
```

If `q = p ^ f`, this reads `p ^ (f μ p ^ k + e f λ k + ν')`; over `O = ℤ_p` (`e = f = 1`), it is
Iwasawa's classical formula `p ^ (μ p ^ k + λ k + ν)`. The proof combines four ingredients:

* the Euler quotient
  `#(M ⧸ ν_{k, n₀} M) / #M[ν_{k, n₀}] = q ^ (μ deg ν_{k, n₀}) · #(O ⧸ Res(F_M, ν_{k, n₀}))`
  (`TauCeti.Iwasawa.natCard_quotSMulTop_div_natCard_torsionBy`);
* stabilization of the increasing chain of finite kernels `M[ν_{k, n₀}]` on the noetherian module
  `M`, whose stable cardinality is a power of `q` by
  `IsFiniteLength.natCard_eq_natCard_residueField_pow_length`;
* the degree identity `deg ν_{k, n₀} = p ^ k - c₀`;
* the asymptotic norm formula `Res(F_M, ν_{k, n₁ + 1}) ~ p ^ (λ (k - n₁))` for `n₁ > λ e`
  (`Polynomial.IsDistinguishedAt.associated_norm_mk_prod_cyclotomic_prime_pow_comp_X_add_one`),
  which contributes `q ^ (e λ (k - n₁))` per step.

## Main definitions

* `TauCeti.Iwasawa.growthTransition`: the cyclotomic transition polynomial
  `ν_{n, n₀} = ∏_{n₀ ≤ j ≤ n} Φ_{p ^ j}(X + 1)` in `O[X]`.

## Main results

* `TauCeti.Iwasawa.finite_quotSMulTop_growthTransition_iff_forall_resultant_ne_zero`:
  `M ⧸ ν_{n, n₀} M` is finite for all `n` iff `Res(F_M, Φ_{p ^ j}(X + 1)) ≠ 0` for all `j ≥ n₀`.
* `TauCeti.Iwasawa.finite_quotSMulTop_growthTransition_iff`: the cyclotomic cutoff criterion
  (Neukirch–Schmidt–Wingberg, Proposition 5.3.17).
* `TauCeti.Iwasawa.finite_quotSMulTop_one_add_X_pow_sub_one_iff`: `M ⧸ ω_n M` is finite for all `n`
  iff the delta submodule `M_δ` is finite.
* `TauCeti.Iwasawa.exists_finite_quotSMulTop_growthTransition`: every finitely generated torsion
  `Λ`-module admits a cyclotomic cutoff `n₀` when `(p : O) ≠ 0`.
* `TauCeti.Iwasawa.natCard_quotSMulTop_growthTransition`: Iwasawa's growth formula over a complete
  discrete valuation ring of mixed characteristic with ramification index `e` and residue
  cardinality `q` (Neukirch–Schmidt–Wingberg, Theorem 5.3.18; Washington, Theorem 13.13).
* `TauCeti.Iwasawa.natCard_quotSMulTop_growthTransition_pow`,
  `TauCeti.Iwasawa.natCard_quotSMulTop_growthTransition_padicInt`,
  `TauCeti.Iwasawa.natCard_quotSMulTop_one_add_X_pow_sub_one`, and
  `TauCeti.Iwasawa.exists_natCard_quotSMulTop_growthTransition`: the prime-power, `ℤ_p`, `n₀ = 0`,
  and unconditional specializations.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  Grundlehren 323, (5.3.17)–(5.3.18).
* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §13.3.
-/

public section

open IsLocalRing PowerSeries Submodule
open scoped Pointwise Polynomial PowerSeries

namespace TauCeti.Iwasawa

section GrowthTransition

variable (p : ℕ) (O : Type*) [CommRing O]

/-- The *cyclotomic transition polynomial*
`ν_{n, n₀} = ∏_{n₀ ≤ j ≤ n} Φ_{p ^ j}(X + 1)` in `O[X]`.
When `n₀ = 0` and `p` is prime this is `ω_n = (1 + X) ^ p ^ n - 1`; when `n < n₀` it is the empty
product `1`. -/
noncomputable def growthTransition (n₀ n : ℕ) : O[X] :=
  ∏ j ∈ Finset.Ico n₀ (n + 1), (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)

theorem growthTransition_def (n₀ n : ℕ) :
    growthTransition p O n₀ n =
      ∏ j ∈ Finset.Ico n₀ (n + 1), (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1) :=
  (rfl)

/-- For `n < n₀`, the cyclotomic transition polynomial is the empty product `1`. -/
@[simp]
theorem growthTransition_of_lt {n₀ n : ℕ} (h : n < n₀) :
    growthTransition p O n₀ n = 1 := by
  rw [growthTransition_def, Finset.Ico_eq_empty (by omega), Finset.prod_empty]

/-- At `n = n₀`, the cyclotomic transition polynomial is the single shifted cyclotomic factor
`Φ_{p ^ n}(X + 1)`. -/
@[simp]
theorem growthTransition_self (n : ℕ) :
    growthTransition p O n n = (Polynomial.cyclotomic (p ^ n) O).comp (Polynomial.X + 1) := by
  rw [growthTransition_def, Nat.Ico_succ_singleton, Finset.prod_singleton]

/-- Starting at `n₀ = 0`, the cyclotomic transition polynomial is `ω_n = (1 + X) ^ p ^ n - 1`. -/
theorem growthTransition_zero (hp : p.Prime) (n : ℕ) :
    growthTransition p O 0 n = (1 + Polynomial.X) ^ p ^ n - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [growthTransition_def, Nat.Ico_zero_eq_range,
    Polynomial.prod_range_cyclotomic_prime_pow_comp_X_add_one]

/-- Transition polynomials compose multiplicatively along adjacent intervals:
`ν_{m, n₀} · ν_{n, m + 1} = ν_{n, n₀}` for `n₀ ≤ m + 1` and `m ≤ n`. -/
theorem growthTransition_mul {n₀ m n : ℕ} (h₁ : n₀ ≤ m + 1) (h₂ : m ≤ n) :
    growthTransition p O n₀ m * growthTransition p O (m + 1) n = growthTransition p O n₀ n := by
  simpa only [growthTransition_def] using
    Finset.prod_Ico_consecutive
      (fun j ↦ (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) h₁
      (Nat.add_le_add_right h₂ 1)

/-- Appending the next cyclotomic factor: `ν_{n + 1, n₀} = ν_{n, n₀} · Φ_{p ^ (n + 1)}(X + 1)`. -/
theorem growthTransition_succ {n₀ n : ℕ} (h : n₀ ≤ n + 1) :
    growthTransition p O n₀ (n + 1) =
      growthTransition p O n₀ n * (Polynomial.cyclotomic (p ^ (n + 1)) O).comp (Polynomial.X + 1) :=
  by rw [← growthTransition_mul p O h (Nat.le_succ n), growthTransition_self]

/-- Divisibility monotonicity: `ν_{m, n₀} ∣ ν_{n, n₀}` whenever `m ≤ n`. -/
theorem growthTransition_dvd_of_le {n₀ m n : ℕ} (h : m ≤ n) :
    growthTransition p O n₀ m ∣ growthTransition p O n₀ n :=
  Finset.prod_dvd_prod_of_subset _ _ _ (Finset.Ico_subset_Ico_right (Nat.add_le_add_right h 1))

/-- Every shifted cyclotomic factor `Φ_{p ^ j}(X + 1)` with `n₀ ≤ j ≤ n` divides `ν_{n, n₀}`. -/
theorem cyclotomic_comp_X_add_one_dvd_growthTransition {n₀ n j : ℕ} (hj₁ : n₀ ≤ j)
    (hj₂ : j ≤ n) :
    (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1) ∣ growthTransition p O n₀ n :=
  Finset.dvd_prod_of_mem _ (Finset.mem_Ico.mpr ⟨hj₁, Nat.lt_succ_of_le hj₂⟩)

/-- Multiplying `ν_{n, n₀}` by the first `n₀` shifted cyclotomic factors recovers `ω_n`. -/
theorem prod_range_mul_growthTransition (hp : p.Prime) {n₀ n : ℕ} (h : n₀ ≤ n + 1) :
    (∏ j ∈ Finset.range n₀, (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) *
        growthTransition p O n₀ n = (1 + Polynomial.X) ^ p ^ n - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← Nat.Ico_zero_eq_range, growthTransition_def,
    Finset.prod_Ico_consecutive _ (Nat.zero_le n₀) h, Nat.Ico_zero_eq_range,
    Polynomial.prod_range_cyclotomic_prime_pow_comp_X_add_one]

/-- For `1 ≤ n₀ ≤ n + 1`, `ω_{n₀ - 1} · ν_{n, n₀} = ω_n`. -/
theorem one_add_X_pow_sub_one_mul_growthTransition (hp : p.Prime) {n₀ n : ℕ} (hn₀ : 0 < n₀)
    (h : n₀ ≤ n + 1) :
    ((1 + Polynomial.X) ^ p ^ (n₀ - 1) - 1) * growthTransition p O n₀ n =
      (1 + Polynomial.X) ^ p ^ n - 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← Polynomial.prod_range_cyclotomic_prime_pow_comp_X_add_one p (n₀ - 1),
    Nat.sub_add_cancel hn₀]
  exact prod_range_mul_growthTransition p O hp h

/-- Every cyclotomic transition polynomial is monic. -/
theorem monic_growthTransition (n₀ n : ℕ) : (growthTransition p O n₀ n).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ ↦ Polynomial.monic_cyclotomic_comp_X_add_one _

/-- Every cyclotomic transition polynomial is distinguished at any ideal containing `p`. -/
theorem isDistinguishedAt_growthTransition (hp : p.Prime) {I : Ideal O} (hpI : (p : O) ∈ I)
    (n₀ n : ℕ) : (growthTransition p O n₀ n).IsDistinguishedAt I := by
  have : Fact p.Prime := ⟨hp⟩
  exact Polynomial.isDistinguishedAt_prod fun j _ ↦
    Polynomial.cyclotomic_prime_pow_comp_X_add_one_isDistinguishedAt p hpI j

/-- The degree of `ν_{n, 0} = ω_n` is `p ^ n`. -/
@[simp]
theorem natDegree_growthTransition_zero [Nontrivial O] (hp : p.Prime) (n : ℕ) :
    (growthTransition p O 0 n).natDegree = p ^ n := by
  rw [growthTransition_zero p O hp, TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one]

/-- For `1 ≤ n₀ ≤ n + 1`, the degree of `ν_{n, n₀}` is `p ^ n - p ^ (n₀ - 1)`. -/
theorem natDegree_growthTransition_of_pos [Nontrivial O] (hp : p.Prime) {n₀ n : ℕ} (hn₀ : 0 < n₀)
    (h : n₀ ≤ n + 1) :
    (growthTransition p O n₀ n).natDegree = p ^ n - p ^ (n₀ - 1) := by
  have hmul := one_add_X_pow_sub_one_mul_growthTransition p O hp hn₀ h
  have hmon₁ : ((1 + Polynomial.X) ^ p ^ (n₀ - 1) - 1 : O[X]).Monic :=
    TauCeti.Polynomial.monic_one_add_X_pow_sub_one (pow_ne_zero _ hp.ne_zero)
  have hdeg := congrArg Polynomial.natDegree hmul
  rw [hmon₁.natDegree_mul (monic_growthTransition p O n₀ n),
    TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one,
    TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one] at hdeg
  omega

/-- Unified degree formula for `n₀ ≤ n + 1`:
`deg ν_{n, n₀} = p ^ n - (if n₀ = 0 then 0 else p ^ (n₀ - 1))`. -/
theorem natDegree_growthTransition [Nontrivial O] (hp : p.Prime) {n₀ n : ℕ} (h : n₀ ≤ n + 1) :
    (growthTransition p O n₀ n).natDegree = p ^ n - if n₀ = 0 then 0 else p ^ (n₀ - 1) := by
  rcases Nat.eq_zero_or_pos n₀ with rfl | hn₀
  · simp [natDegree_growthTransition_zero p O hp]
  · simp [hn₀.ne', natDegree_growthTransition_of_pos p O hp hn₀ h]

/-- Cyclotomic transition polynomials commute with ring homomorphisms. -/
theorem map_growthTransition {R : Type*} [CommRing R] (f : O →+* R) (n₀ n : ℕ) :
    (growthTransition p O n₀ n).map f = growthTransition p R n₀ n := by
  simp [growthTransition_def, Polynomial.map_prod, Polynomial.map_comp]

end GrowthTransition

section Separability

/-- Over an integral domain `O`, if `(m : O) ≠ 0`, then `(1 + X) ^ m - 1` is not divisible by the
square of any non-unit polynomial `F`. -/
private theorem not_sq_dvd_one_add_X_pow_sub_one {O : Type*} [CommRing O] [IsDomain O] {m : ℕ}
    (hm : (m : O) ≠ 0) {F : O[X]} (hF : ¬ IsUnit F) :
    ¬ F ^ 2 ∣ (1 + Polynomial.X) ^ m - 1 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  rintro ⟨Q, hQ⟩
  set ω : O[X] := (1 + Polynomial.X) ^ m - 1
  -- `(1 + X) · ω' - m · ω = m`, and `F` divides both `ω` and `ω'`.
  have hderiv_ω : Polynomial.derivative ω =
      Polynomial.C (m : O) * (1 + Polynomial.X) ^ (m - 1) := by
    simp [ω, Polynomial.derivative_pow]
  have hid : (1 + Polynomial.X) * Polynomial.derivative ω - Polynomial.C (m : O) * ω =
      Polynomial.C (m : O) := by
    rw [hderiv_ω]
    have hpow : (1 + Polynomial.X : O[X]) * (1 + Polynomial.X) ^ (m - 1) =
        (1 + Polynomial.X) ^ m := by
      rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]
    calc (1 + Polynomial.X) * (Polynomial.C (m : O) * (1 + Polynomial.X) ^ (m - 1)) -
          Polynomial.C (m : O) * ω
        = Polynomial.C (m : O) * ((1 + Polynomial.X) * (1 + Polynomial.X) ^ (m - 1)) -
          Polynomial.C (m : O) * ω := by ring
      _ = Polynomial.C (m : O) * (1 + Polynomial.X) ^ m -
          Polynomial.C (m : O) * ((1 + Polynomial.X) ^ m - 1) := by rw [hpow]
      _ = Polynomial.C (m : O) := by ring
  have hFdvd_ω : F ∣ ω := ⟨F * Q, by rw [hQ, sq, mul_assoc]⟩
  have hFdvd_dω : F ∣ Polynomial.derivative ω := by
    refine ⟨2 * Polynomial.derivative F * Q + F * Polynomial.derivative Q, ?_⟩
    rw [hQ, sq, Polynomial.derivative_mul, Polynomial.derivative_mul]
    ring
  have hFdvd_C : F ∣ Polynomial.C (m : O) :=
    hid ▸ dvd_sub (dvd_mul_of_dvd_right hFdvd_dω _) (dvd_mul_of_dvd_right hFdvd_ω _)
  have hC0 : Polynomial.C (m : O) ≠ 0 := Polynomial.C_ne_zero.mpr hm
  have hdeg0 : F.natDegree = 0 :=
    Nat.eq_zero_of_le_zero ((Polynomial.natDegree_le_of_dvd hFdvd_C hC0).trans (by simp))
  have hFC : F = Polynomial.C (F.coeff 0) := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
  obtain ⟨R, hR⟩ := hFdvd_ω
  have hmon : ω.Monic := TauCeti.Polynomial.monic_one_add_X_pow_sub_one hm0
  have hlc : F.coeff 0 * R.coeff m = 1 := by
    have := congrArg (fun P : O[X] ↦ P.coeff m) hR
    rw [hFC, Polynomial.coeff_C_mul] at this
    have hcoeff : ω.coeff m = 1 := by
      rw [← TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one (R := O) m]
      exact hmon.leadingCoeff
    exact this.symm.trans hcoeff
  exact hF (hFC ▸ (IsUnit.of_mul_eq_one (R.coeff m) hlc).map Polynomial.C)

/-- Over an integral domain `O` with `(p : O) ≠ 0`, a non-unit polynomial `F` divides at most one
shifted prime-power cyclotomic polynomial `Φ_{p ^ j}(X + 1)`. -/
private theorem eq_of_dvd_cyclotomic_prime_pow_comp_X_add_one {O : Type*} [CommRing O] [IsDomain O]
    {p : ℕ} (hp : p.Prime) (hp0 : (p : O) ≠ 0) {F : O[X]} (hF : ¬ IsUnit F) {i j : ℕ}
    (hi : F ∣ (Polynomial.cyclotomic (p ^ i) O).comp (Polynomial.X + 1))
    (hj : F ∣ (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) : i = j := by
  by_contra hij
  have : Fact p.Prime := ⟨hp⟩
  let n := max i j
  have hsub : ({i, j} : Finset ℕ) ⊆ Finset.range (n + 1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rw [Finset.mem_range]
    rcases hk with rfl | rfl <;> omega
  have hprod :
      ((Polynomial.cyclotomic (p ^ i) O).comp (Polynomial.X + 1)) *
        ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ∣
        (1 + Polynomial.X) ^ p ^ n - 1 := by
    rw [← Polynomial.prod_range_cyclotomic_prime_pow_comp_X_add_one p n,
      ← Finset.prod_pair
        (f := fun k ↦ (Polynomial.cyclotomic (p ^ k) O).comp (Polynomial.X + 1)) hij]
    exact Finset.prod_dvd_prod_of_subset _ _ _ hsub
  have hsq : F ^ 2 ∣ (1 + Polynomial.X) ^ p ^ n - 1 :=
    (sq F ▸ mul_dvd_mul hi hj).trans hprod
  exact not_sq_dvd_one_add_X_pow_sub_one (m := p ^ n) (by simpa using pow_ne_zero n hp0) hF hsq

/-- For a monic prime polynomial `F` over an integral domain `O`, `Res(F, G) = 0 ↔ F ∣ G`. -/
private theorem resultant_eq_zero_iff_dvd {O : Type*} [CommRing O] [IsDomain O] {F : O[X]}
    (hF : F.Monic) (hprime : Prime F) (G : O[X]) :
    F.resultant G = 0 ↔ F ∣ G := by
  have : (Ideal.span {F}).IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have : IsDomain (AdjoinRoot F) := Ideal.Quotient.isDomain (Ideal.span {F})
  let pb := AdjoinRoot.powerBasis' hF
  have : Module.Free O (AdjoinRoot F) := Module.Free.of_basis pb.basis
  have : Module.Finite O (AdjoinRoot F) := pb.finite
  rw [← AdjoinRoot.norm_mk_eq_resultant hF, Algebra.norm_apply,
    LinearMap.det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff, ← AdjoinRoot.mk_eq_zero]
  refine ⟨fun ⟨x, hx, hx0⟩ ↦ ?_, fun h0 ↦ ⟨1, ?_, one_ne_zero⟩⟩
  · change AdjoinRoot.mk F G * x = 0 at hx
    exact (mul_eq_zero.mp hx).resolve_right hx0
  · change AdjoinRoot.mk F G * 1 = 0
    rw [h0, zero_mul]

end Separability

section DeltaElementary

/-- Over a domain with prime `ϖ`, a vertical block `O⟦X⟧ ⧸ (ϖ ^ m)` has trivial delta submodule
whenever `p ≠ 0`. -/
theorem deltaSubmodule_quotient_span_C_pow {O : Type*} [CommRing O] [IsDomain O]
    {ϖ : O} (hϖ : Prime ϖ) {p : ℕ} (hp : p ≠ 0) (m : ℕ) :
    deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {C (ϖ ^ m)}) = ⊥ := by
  rw [eq_bot_iff, deltaSubmodule_le_iff]
  intro n
  rw [le_bot_iff, ← isSMulRegular_iff_torsionBy_eq_bot, map_pow]
  refine (prime_C_iff.2 hϖ).isSMulRegular_quotient_span_pow (fun ⟨k, hk⟩ ↦ hϖ.not_isUnit ?_) m
  have hcoeff := congrArg (coeff (p ^ n)) hk
  have hcoe : (((1 + Polynomial.X) ^ p ^ n - 1 : O[X]) : O⟦X⟧) = (1 + X) ^ p ^ n - 1 := by simp
  have hlead :=
    (TauCeti.Polynomial.monic_one_add_X_pow_sub_one (R := O) (pow_ne_zero n hp)).leadingCoeff
  rw [Polynomial.leadingCoeff, TauCeti.Polynomial.natDegree_one_add_X_pow_sub_one] at hlead
  rw [← hcoe, Polynomial.coeff_coe, hlead, coeff_C_mul] at hcoeff
  exact IsUnit.of_mul_eq_one _ hcoeff.symm

/-- For a distinguished polynomial `F` over an `I`-adically complete ring `O`, divisibility in
`O⟦X⟧` between polynomials reflects divisibility in `O[X]`. -/
private theorem dvd_of_coe_dvd_coe {O : Type*} [CommRing O] {I : Ideal O} [IsAdicComplete I O]
    {F G : O[X]} (hF : F.IsDistinguishedAt I) (h : (F : O⟦X⟧) ∣ (G : O⟦X⟧)) : F ∣ G := by
  have H := hF.isWeierstrassFactorizationAt
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem] at h ⊢
  apply H.algEquivQuotient.injective
  simpa [map_zero] using h

/-- Over an infinite `I`-adically complete domain `O`, any `O⟦X⟧`-submodule of a Weierstrass
quotient `O⟦X⟧ ⧸ (F)` is finite iff it is trivial, since the quotient is free over `O`. -/
private theorem finite_submodule_quotient_span_iff_eq_bot {O : Type*} [CommRing O] [IsDomain O]
    [Infinite O] {I : Ideal O} [IsAdicComplete I O] {F : O[X]} (hF : F.IsDistinguishedAt I)
    (S : Submodule O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {(F : O⟦X⟧)})) :
    Finite S ↔ S = ⊥ := by
  refine ⟨fun hfin ↦ ?_, fun h ↦ by rw [h]; infer_instance⟩
  by_contra hne
  obtain ⟨x, hxS, hx0⟩ := (Submodule.ne_bot_iff S).mp hne
  have H := hF.isWeierstrassFactorizationAt
  have := H.free_quotient
  let f : O → S := fun c ↦ ⟨C c • x, S.smul_mem (C c) hxS⟩
  have hsmul (c : O) : C c • x = c • x := algebraMap_smul O⟦X⟧ c x
  have hinj : Function.Injective f := fun c₁ c₂ hc ↦ by
    have hval : c₁ • x = c₂ • x := by
      have := congrArg Subtype.val hc
      simpa [f, hsmul] using this
    have hsub : (c₁ - c₂) • x = 0 := by rw [sub_smul, hval, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hx0)
  exact not_finite_iff_infinite.mpr (Infinite.of_injective f hinj) hfin

/-- Membership of a quotient class in the cyclic `O⟦X⟧`-submodule generated by `mk (F ^ (n - 1))`
inside `O⟦X⟧ ⧸ (F ^ n)` reduces to divisibility by `F ^ (n - 1)`. -/
private theorem mem_span_mk_pow_sub_one_iff {R : Type*} [CommRing R] (f : R) (n : ℕ) (a : R) :
    Ideal.Quotient.mk (Ideal.span {f ^ n}) a ∈
      Submodule.span R {Ideal.Quotient.mk (Ideal.span {f ^ n}) (f ^ (n - 1))} ↔
      f ^ (n - 1) ∣ a := by
  rw [Submodule.mem_span_singleton]
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun ⟨r, hr⟩ ↦ ⟨r, ?_⟩⟩
  · rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul,
      Ideal.Quotient.mk_eq_mk, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
    obtain ⟨s, hs⟩ := hc
    have h1 : f ^ (n - 1) ∣ f ^ n := pow_dvd_pow f (Nat.sub_le n 1)
    have h2 : f ^ (n - 1) ∣ c * f ^ (n - 1) - a := h1.trans ⟨s, hs⟩
    simpa [sub_sub_cancel] using dvd_sub (dvd_mul_left _ c) h2
  · rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_comm, ← hr,
      Ideal.Quotient.mk_eq_mk]

/-- If `F ∣ Φ_{p ^ j}(X + 1)`, then for every `k ≥ j` the `ω_k`-torsion of `O⟦X⟧ ⧸ (F ^ n)`
(`n ≠ 0`) is the cyclic submodule generated by `F ^ (n - 1)`. -/
private theorem torsionBy_one_add_X_pow_sub_one_quotient_span_pow {O : Type*} [CommRing O]
    [IsDomain O] {I : Ideal O} [IsAdicComplete I O] {p : ℕ} (hp : p.Prime) (hp0 : (p : O) ≠ 0)
    {F : O[X]} (hF : F.IsDistinguishedAt I) (hprime : Prime F) {n : ℕ} (hn : n ≠ 0) {j k : ℕ}
    (hj : F ∣ (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) (hk : j ≤ k) :
    torsionBy O⟦X⟧ (O⟦X⟧ ⧸ Ideal.span {((F ^ n : O[X]) : O⟦X⟧)}) ((1 + X) ^ p ^ k - 1) =
      Submodule.span O⟦X⟧
        {Ideal.Quotient.mk (Ideal.span {((F ^ n : O[X]) : O⟦X⟧)}) ((F : O⟦X⟧) ^ (n - 1))} := by
  have : Fact p.Prime := ⟨hp⟩
  have hprimeF' : Prime (F : O⟦X⟧) := hF.prime_coe_iff.mpr hprime
  set ω : O[X] := (1 + Polynomial.X) ^ p ^ k - 1
  have hcoe : (ω : O⟦X⟧) = (1 + X) ^ p ^ k - 1 := by simp [ω]
  have hdvd₁ : F ∣ ω := hj.trans (by
    dsimp only [ω]
    rw [← Polynomial.prod_range_cyclotomic_prime_pow_comp_X_add_one p k]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)))
  have hndvd₂ : ¬ (F : O⟦X⟧) ^ 2 ∣ (ω : O⟦X⟧) := fun h2 ↦
    not_sq_dvd_one_add_X_pow_sub_one (m := p ^ k) (by simpa using pow_ne_zero k hp0)
      hprime.not_isUnit
      (dvd_of_coe_dvd_coe (hF.pow 2) (by simpa only [Polynomial.coe_pow] using h2))
  obtain ⟨q, hq⟩ := map_dvd Polynomial.coeToPowerSeries.ringHom hdvd₁
  simp only [Polynomial.coeToPowerSeries.ringHom_apply] at hq
  have hq' : ¬ (F : O⟦X⟧) ∣ q := fun ⟨r, hr⟩ ↦ hndvd₂ ⟨r, by rw [hq, hr, sq, mul_assoc]⟩
  ext x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [mem_torsionBy_iff, ← hcoe, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
    Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mem_span_singleton,
    Ideal.Quotient.mk_eq_mk, Polynomial.coe_pow, mem_span_mk_pow_sub_one_iff, hq, mul_assoc]
  have hpow : (F : O⟦X⟧) ^ n = (F : O⟦X⟧) * (F : O⟦X⟧) ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
  rw [hpow, mul_dvd_mul_iff_left hprimeF'.ne_zero]
  exact ⟨hprimeF'.pow_dvd_of_dvd_mul_left (n - 1) hq', fun hd ↦ dvd_mul_of_dvd_right hd q⟩

/-- When `F` divides some shifted cyclotomic polynomial `Φ_{p ^ j}(X + 1)`, the delta submodule of
`O⟦X⟧ ⧸ (F ^ n)` (`n ≠ 0`) is the cyclic submodule generated by `F ^ (n - 1)`. -/
private theorem deltaSubmodule_quotient_span_pow_of_dvd {O : Type*} [CommRing O] [IsDomain O]
    {I : Ideal O} [IsAdicComplete I O] {p : ℕ} (hp : p.Prime) (hp0 : (p : O) ≠ 0) {F : O[X]}
    (hF : F.IsDistinguishedAt I) (hprime : Prime F) {n : ℕ} (hn : n ≠ 0) {j : ℕ}
    (hj : F ∣ (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) :
    deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {((F ^ n : O[X]) : O⟦X⟧)}) =
      Submodule.span O⟦X⟧
        {Ideal.Quotient.mk (Ideal.span {((F ^ n : O[X]) : O⟦X⟧)}) ((F : O⟦X⟧) ^ (n - 1))} := by
  refine le_antisymm ?_ ?_
  · rw [deltaSubmodule_le_iff]
    intro k
    exact (monotone_torsionBy_one_add_X_pow_sub_one p O _ (le_max_right j k)).trans
      (torsionBy_one_add_X_pow_sub_one_quotient_span_pow hp hp0 hF hprime hn hj
        (le_max_left j k)).le
  · rw [← torsionBy_one_add_X_pow_sub_one_quotient_span_pow hp hp0 hF hprime hn hj le_rfl]
    exact torsionBy_le_deltaSubmodule p O _ j

/-- When `F` divides no shifted cyclotomic polynomial `Φ_{p ^ j}(X + 1)`, the delta submodule of
`O⟦X⟧ ⧸ (F ^ n)` is trivial. -/
private theorem deltaSubmodule_quotient_span_pow_of_not_dvd {O : Type*} [CommRing O] [IsDomain O]
    {I : Ideal O} [IsAdicComplete I O] {p : ℕ} (hp : p.Prime) {F : O[X]}
    (hF : F.IsDistinguishedAt I) (hprime : Prime F) (n : ℕ)
    (hndvd : ∀ j, ¬ F ∣ (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) :
    deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {((F ^ n : O[X]) : O⟦X⟧)}) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  rw [eq_bot_iff, deltaSubmodule_le_iff]
  intro k
  have H := (hF.pow n).isWeierstrassFactorizationAt
  set ω : O[X] := (1 + Polynomial.X) ^ p ^ k - 1
  have hcoe : (ω : O⟦X⟧) = (1 + X) ^ p ^ k - 1 := by simp [ω]
  rw [← hcoe, (H.torsionBy_eq_bot_iff (ω : O⟦X⟧)).mpr]
  rw [H.norm_mk_coe_eq_resultant,
    Polynomial.resultant_pow_left F ω n ω.natDegree
      (by rw [hF.monic.leadingCoeff, one_pow]; exact one_ne_zero) le_rfl]
  refine pow_ne_zero n fun h0 ↦ ?_
  have hdvd : F ∣ ω := (resultant_eq_zero_iff_dvd hF.monic hprime ω).mp h0
  rw [show ω = ∏ i ∈ Finset.range (k + 1),
      (Polynomial.cyclotomic (p ^ i) O).comp (Polynomial.X + 1) from
    (Polynomial.prod_range_cyclotomic_prime_pow_comp_X_add_one p k).symm] at hdvd
  obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hprime _).mp hdvd
  exact hndvd i hi

/-- For a prime `p` with `(p : O) ≠ 0` and a prime distinguished polynomial `F` over an infinite
`I`-adically complete domain `O`, the cyclotomic-torsion computation on a horizontal block
`O⟦X⟧ ⧸ (F ^ n)` (`n ≠ 0`): `g • M_δ` is finite iff every shifted cyclotomic factor divisible by
`F` implies `F ∣ g`. -/
theorem finite_smul_deltaSubmodule_quotient_span_pow_iff {O : Type*} [CommRing O] [IsDomain O]
    [Infinite O] {I : Ideal O} [IsAdicComplete I O] {p : ℕ} (hp : p.Prime)
    (hp0 : (p : O) ≠ 0) {F : O[X]} (hF : F.IsDistinguishedAt I) (hprime : Prime F) {n : ℕ}
    (hn : n ≠ 0) (g : O[X]) :
    Finite ↥((g : O⟦X⟧) •
      deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {((F ^ n : O[X]) : O⟦X⟧)})) ↔
      ∀ j, F ∣ (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1) → F ∣ g := by
  rw [finite_submodule_quotient_span_iff_eq_bot (hF.pow n)]
  have hprimeF' : Prime (F : O⟦X⟧) := hF.prime_coe_iff.mpr hprime
  by_cases hex : ∃ j, F ∣ (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)
  · obtain ⟨j, hj⟩ := hex
    rw [deltaSubmodule_quotient_span_pow_of_dvd hp hp0 hF hprime hn hj, Submodule.eq_bot_iff]
    constructor
    · intro hbot _ _
      have h0 : (g : O⟦X⟧) • Ideal.Quotient.mk (Ideal.span {((F ^ n : O[X]) : O⟦X⟧)})
          ((F : O⟦X⟧) ^ (n - 1)) = 0 :=
        hbot _ (Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.subset_span rfl))
      rw [← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mem_span_singleton,
        Polynomial.coe_pow] at h0
      have hpow : (F : O⟦X⟧) ^ n = (F : O⟦X⟧) ^ (n - 1) * (F : O⟦X⟧) := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
      rw [hpow, mul_comm (g : O⟦X⟧), mul_dvd_mul_iff_left (pow_ne_zero _ hprimeF'.ne_zero)] at h0
      exact dvd_of_coe_dvd_coe hF h0
    · intro hg x hx
      rw [Submodule.pointwise_smul_def, Submodule.mem_map] at hx
      rcases hx with ⟨y, hy, rfl⟩
      rw [Submodule.mem_span_singleton] at hy
      rcases hy with ⟨c, rfl⟩
      obtain ⟨r, hr⟩ := map_dvd Polynomial.coeToPowerSeries.ringHom (hg j hj)
      simp only [Polynomial.coeToPowerSeries.ringHom_apply] at hr
      rw [DistribSMul.toLinearMap_apply, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
        ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        smul_eq_mul, smul_eq_mul, Ideal.mem_span_singleton, Polynomial.coe_pow]
      have hpow : (F : O⟦X⟧) ^ n = (F : O⟦X⟧) * (F : O⟦X⟧) ^ (n - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
      refine ⟨r * c, ?_⟩
      calc (g : O⟦X⟧) * (c * (F : O⟦X⟧) ^ (n - 1))
          = (F : O⟦X⟧) * r * (c * (F : O⟦X⟧) ^ (n - 1)) := by rw [hr]
        _ = (F : O⟦X⟧) * (F : O⟦X⟧) ^ (n - 1) * (r * c) := by ring
        _ = (F : O⟦X⟧) ^ n * (r * c) := by rw [hpow]
  · push Not at hex
    rw [deltaSubmodule_quotient_span_pow_of_not_dvd hp hF hprime n hex,
      Submodule.pointwise_smul_def, Submodule.map_bot]
    exact ⟨fun _ j hj ↦ (hex j hj).elim, fun _ ↦ rfl⟩

/-- `r • (⊤ : Submodule R S)` inside a submodule `S` has the same cardinality as `r • S`. -/
private theorem finite_smul_top_subtype_iff {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    (r : R) (S : Submodule R P) :
    Finite ↥(r • (⊤ : Submodule R S)) ↔ Finite ↥(r • S) := by
  have hmap : (r • (⊤ : Submodule R S)).map S.subtype = r • S := by
    ext x
    simp only [Submodule.mem_map, Submodule.pointwise_smul_def, Submodule.coe_subtype,
      Submodule.mem_top, true_and, exists_exists_eq_and]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨y.1, y.2, hy⟩, fun ⟨y, hy, hyx⟩ ↦ ⟨⟨y, hy⟩, hyx⟩⟩
  exact Equiv.finite_iff
    ((Submodule.equivMapOfInjective S.subtype S.subtype_injective _).trans
      (LinearEquiv.ofEq _ _ hmap)).toEquiv

/-- Over a complete local noetherian ring `O` with finite residue field and `dim O⟦X⟧ = 2`, a
pseudo-isomorphism preserves the finiteness of `r • M_δ` for every scalar `r`. -/
theorem IsPseudoIsomorphism.finite_smul_deltaSubmodule_iff {O M N : Type*} [CommRing O]
    [IsLocalRing O] [IsNoetherianRing O] [Finite (ResidueField O)]
    (hdim : ringKrullDim O⟦X⟧ = 2) [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]
    [AddCommGroup N] [Module O⟦X⟧ N] [Module.Finite O⟦X⟧ N]
    {f : M →ₗ[O⟦X⟧] N} (hf : IsPseudoIsomorphism f) (p : ℕ) (r : O⟦X⟧) :
    Finite ↥(r • deltaSubmodule p O M) ↔ Finite ↥(r • deltaSubmodule p O N) := by
  have : IsNoetherian O⟦X⟧ M := isNoetherian_of_isNoetherianRing_of_finite O⟦X⟧ M
  have : IsNoetherian O⟦X⟧ N := isNoetherian_of_isNoetherianRing_of_finite O⟦X⟧ N
  obtain ⟨k₁, hk₁⟩ := Filter.eventually_atTop.mp (eventually_deltaSubmodule_eq_torsionBy p O M)
  obtain ⟨k₂, hk₂⟩ := Filter.eventually_atTop.mp (eventually_deltaSubmodule_eq_torsionBy p O N)
  set k := max k₁ k₂
  have hM : deltaSubmodule p O M = torsionBy O⟦X⟧ M ((1 + X) ^ p ^ k - 1) :=
    hk₁ k (le_max_left k₁ k₂)
  have hN : deltaSubmodule p O N = torsionBy O⟦X⟧ N ((1 + X) ^ p ^ k - 1) :=
    hk₂ k (le_max_right k₁ k₂)
  have := ((isPseudoIsomorphism_iff_finite hdim).1 hf).1
  have := ((isPseudoIsomorphism_iff_finite hdim).1 hf).2
  set ω : O⟦X⟧ := (1 + X) ^ p ^ k - 1
  let φ := torsionByMap ω f
  have : Finite (LinearMap.ker φ) := finite_ker_torsionByMap ω f
  have : Finite (torsionBy O⟦X⟧ N ω ⧸ LinearMap.range φ) := finite_coker_torsionByMap ω f
  have hiff := finite_smul_top_iff_of_finite_ker_of_finite_coker r φ
  rw [hM, hN, ← finite_smul_top_subtype_iff r (torsionBy O⟦X⟧ M ω),
    ← finite_smul_top_subtype_iff r (torsionBy O⟦X⟧ N ω)]
  exact hiff

private theorem pointwise_smul_prod {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (r : R) (S : Submodule R M) (T : Submodule R N) :
    r • S.prod T = (r • S).prod (r • T) := by
  ext ⟨x, y⟩
  simp only [Submodule.pointwise_smul_def, Submodule.mem_map, Submodule.mem_prod,
    DistribSMul.toLinearMap_apply, Prod.ext_iff, Prod.smul_fst, Prod.smul_snd]
  exact ⟨fun ⟨⟨a, b⟩, ⟨ha, hb⟩, hxa, hyb⟩ ↦ ⟨⟨a, ha, hxa⟩, ⟨b, hb, hyb⟩⟩,
    fun ⟨⟨a, ha, hxa⟩, ⟨b, hb, hyb⟩⟩ ↦ ⟨⟨a, b⟩, ⟨ha, hb⟩, hxa, hyb⟩⟩

private theorem pointwise_smul_pi {R : Type*} [CommRing R] {ι : Type*} {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (r : R) (S : ∀ i, Submodule R (M i)) :
    r • Submodule.pi Set.univ S = Submodule.pi Set.univ fun i ↦ r • S i := by
  ext f
  simp only [Submodule.pointwise_smul_def, Submodule.mem_map, Submodule.mem_pi, Set.mem_univ,
    forall_true_left, DistribSMul.toLinearMap_apply, funext_iff, Pi.smul_apply]
  refine ⟨fun ⟨g, hg, hgf⟩ i ↦ ⟨g i, hg i, hgf i⟩, fun hf ↦ ?_⟩
  choose g hg hgf using hf
  exact ⟨g, hg, hgf⟩

private theorem finite_submodule_pi_iff {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (S : ∀ i, Submodule R (M i)) :
    Finite ↥(Submodule.pi Set.univ S) ↔ ∀ i, Finite (S i) := by
  have : ∀ j, Nonempty (S j) := fun j ↦ ⟨0⟩
  change Finite ↥(Set.univ.pi fun i ↦ (S i : Set (M i))) ↔ _
  rw [Equiv.finite_iff (Equiv.Set.univPi fun i ↦ (S i : Set (M i)))]
  exact ⟨fun _ i ↦ Finite.of_surjective (fun f : ∀ j, S j ↦ f i) (Function.surjective_eval i),
    fun _ ↦ inferInstance⟩

end DeltaElementary

section CyclotomicCutoff

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
  {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]

/-- **Resultant criterion for finiteness along all levels `n ≥ n₀`.** For a finitely generated
torsion `O⟦X⟧`-module `M`, the quotients `M ⧸ ν_{n, n₀} M` are finite for every `n` if and only if
`Res(F_M, Φ_{p ^ j}(X + 1)) ≠ 0` for every `j ≥ n₀`. -/
theorem finite_quotSMulTop_growthTransition_iff_forall_resultant_ne_zero
    (hM : Module.IsTorsion O⟦X⟧ M) (p n₀ : ℕ) :
    (∀ n, Finite (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M)) ↔
      ∀ j, n₀ ≤ j →
        (charPoly O M).resultant ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 :=
  by
  have hiff (n : ℕ) : Finite (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M) ↔
      ∏ j ∈ Finset.Ico n₀ (n + 1),
        (charPoly O M).resultant ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) ≠ 0 :=
    by
    rw [finite_quotSMulTop_iff_resultant_charPoly_ne_zero hM
      ((monic_growthTransition p O n₀ n).map _).ne_zero, growthTransition_def]
    have hlc : ∏ j ∈ Finset.Ico n₀ (n + 1),
        ((Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)).leadingCoeff ≠ 0 := by
      rw [Finset.prod_eq_one fun j _ ↦
        (Polynomial.monic_cyclotomic_comp_X_add_one (R := O) (p ^ j)).leadingCoeff]
      exact one_ne_zero
    rw [Polynomial.resultant_prod_right (Finset.Ico n₀ (n + 1)) (charPoly O M)
      (fun j ↦ (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1))
      (charPoly O M).natDegree le_rfl hlc]
  simp_rw [hiff, Finset.prod_ne_zero_iff, Finset.mem_Ico]
  exact ⟨fun h j hj ↦ h j j ⟨hj, Nat.lt_succ_self j⟩, fun h _ j hj ↦ h j hj.1⟩

omit [Finite (ResidueField O)] in
/-- Helper: finiteness of `g • M_δ` on a torsion elementary module `Elementary O ϖ 0 m F n`. -/
private theorem finite_smul_deltaSubmodule_elementary_iff {p : ℕ} (hp : p.Prime)
    (hp0 : (p : O) ≠ 0) {ϖ : O} (hϖ : Irreducible ϖ) {a b : ℕ} (m : Fin a → ℕ)
    {F : Fin b → O[X]} {n : Fin b → ℕ}
    (hF : ∀ j, (F j).IsDistinguishedAt (maximalIdeal O)) (hirr : ∀ j, Irreducible (F j))
    (hn : ∀ j, n j ≠ 0) (g : O[X]) :
    Finite ↥((g : O⟦X⟧) • deltaSubmodule p O (Elementary O ϖ 0 m F n)) ↔
      ∀ j : Fin b, ∀ k,
        F j ∣ (Polynomial.cyclotomic (p ^ k) O).comp (Polynomial.X + 1) → F j ∣ g := by
  have : Infinite O := TauCeti.IsDiscreteValuationRing.infinite
  dsimp only [Elementary]
  rw [deltaSubmodule_prod, deltaSubmodule_prod, deltaSubmodule_pi, deltaSubmodule_pi,
    deltaSubmodule_pi, pointwise_smul_prod, pointwise_smul_prod, pointwise_smul_pi,
    pointwise_smul_pi, pointwise_smul_pi, Equiv.finite_iff (Submodule.prodEquiv _ _).toEquiv,
    Prod.finite_iff, Equiv.finite_iff (Submodule.prodEquiv _ _).toEquiv, Prod.finite_iff,
    finite_submodule_pi_iff, finite_submodule_pi_iff, finite_submodule_pi_iff]
  have hvert : ∀ i : Fin a, Finite ↥((g : O⟦X⟧) •
      deltaSubmodule p O (O⟦X⟧ ⧸ Ideal.span {C (ϖ ^ m i)})) := fun i ↦ by
    rw [deltaSubmodule_quotient_span_C_pow hϖ.prime hp.ne_zero (m i),
      Submodule.pointwise_smul_def, Submodule.map_bot]
    infer_instance
  simp_rw [finite_smul_deltaSubmodule_quotient_span_pow_iff hp hp0 (hF _) (hirr _).prime (hn _)]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨fun i ↦ i.elim0, hvert, h⟩⟩

omit [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] in
/-- Helper: `Res(∏ F_j ^ n_j, G) ≠ 0` iff no monic prime factor `F_j` divides `G`. -/
private theorem resultant_prod_pow_ne_zero_iff {b : ℕ} {F : Fin b → O[X]} {n : Fin b → ℕ}
    (hF : ∀ j, (F j).Monic) (hprime : ∀ j, Prime (F j)) (hn : ∀ j, n j ≠ 0) (G : O[X]) :
    (∏ j : Fin b, F j ^ n j).resultant G ≠ 0 ↔ ∀ j : Fin b, ¬ F j ∣ G := by
  rw [Polynomial.resultant_prod_left_of_monic _ fun j _ ↦ (hF j).pow _, Finset.prod_ne_zero_iff]
  refine ⟨fun h j hdvd ↦ ?_, fun h j _ h0 ↦ ?_⟩
  · have hj := h j (Finset.mem_univ j)
    rw [Polynomial.resultant_pow_left (F j) G (n j) G.natDegree
      (by rw [(hF j).leadingCoeff, one_pow]; exact one_ne_zero) le_rfl] at hj
    exact hj (by rw [(resultant_eq_zero_iff_dvd (hF j) (hprime j) G).mpr hdvd, zero_pow (hn j)])
  · rw [Polynomial.resultant_pow_left (F j) G (n j) G.natDegree
      (by rw [(hF j).leadingCoeff, one_pow]; exact one_ne_zero) le_rfl] at h0
    exact h j ((resultant_eq_zero_iff_dvd (hF j) (hprime j) G).mp (eq_zero_of_pow_eq_zero h0))

/-- **The cyclotomic cutoff criterion** (Neukirch–Schmidt–Wingberg, Proposition 5.3.17).
Let `O` be a complete discrete valuation ring with finite residue field and `(p : O) ≠ 0`, and let
`M` be a finitely generated torsion `O⟦X⟧`-module. Then `M ⧸ ν_{n, n₀} M` is finite for every `n`
if and only if `(∏_{j < n₀} Φ_{p ^ j}(X + 1)) • M_δ` is finite. -/
theorem finite_quotSMulTop_growthTransition_iff {p : ℕ} (hp : p.Prime) (hp0 : (p : O) ≠ 0)
    (hM : Module.IsTorsion O⟦X⟧ M) (n₀ : ℕ) :
    (∀ n, Finite (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M)) ↔
      Finite ↥(((∏ j ∈ Finset.range n₀,
        (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1) : O[X]) : O⟦X⟧) •
          deltaSubmodule p O M) := by
  set g : O[X] := ∏ j ∈ Finset.range n₀, (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨a, b, m, F, n, -, hFn, f, hf⟩ :=
    exists_isPseudoIsomorphism_elementary_of_isTorsion (M := M) hϖ hM
  have hF (j : Fin b) := (hFn j).1
  have hirr (j : Fin b) := (hFn j).2.1
  have hn (j : Fin b) := (hFn j).2.2
  have hdim := TauCeti.PowerSeries.ringKrullDim_of_isDiscreteValuationRing (R := O)
  rw [finite_quotSMulTop_growthTransition_iff_forall_resultant_ne_zero hM p n₀,
    hf.charPoly_eq_prod hϖ hF hirr, hf.finite_smul_deltaSubmodule_iff hdim p (g : O⟦X⟧),
    finite_smul_deltaSubmodule_elementary_iff hp hp0 hϖ m hF hirr hn g]
  simp_rw [resultant_prod_pow_ne_zero_iff (fun j ↦ (hF j).monic) (fun j ↦ (hirr j).prime) hn]
  refine ⟨fun h j k hk ↦ ?_, fun h k hk j hjk ↦ ?_⟩
  · have hklt : k < n₀ := by
      by_contra hge
      exact h k (not_lt.mp hge) j hk
    exact hk.trans (Finset.dvd_prod_of_mem _ (Finset.mem_range.mpr hklt))
  · obtain ⟨i, hi, hij⟩ := (Prime.dvd_finsetProd_iff (hirr j).prime _).mp (h j k hjk)
    have heq := eq_of_dvd_cyclotomic_prime_pow_comp_X_add_one hp hp0 (hirr j).not_isUnit hjk hij
    rw [heq] at hk
    exact (Finset.mem_range.mp hi).not_ge hk

/-- At `n₀ = 0`, `M ⧸ ω_n M` is finite for every `n` iff the delta submodule `M_δ` is finite. -/
theorem finite_quotSMulTop_one_add_X_pow_sub_one_iff {p : ℕ} (hp : p.Prime) (hp0 : (p : O) ≠ 0)
    (hM : Module.IsTorsion O⟦X⟧ M) :
    (∀ n, Finite (QuotSMulTop ((1 + X) ^ p ^ n - 1 : O⟦X⟧) M)) ↔
      Finite (deltaSubmodule p O M) := by
  have h0 := finite_quotSMulTop_growthTransition_iff hp hp0 hM 0
  have hcoe (n : ℕ) : (growthTransition p O 0 n : O⟦X⟧) = (1 + X) ^ p ^ n - 1 := by
    rw [growthTransition_zero p O hp n]; simp
  simpa only [hcoe, Finset.range_zero, Finset.prod_empty, Polynomial.coe_one, one_smul] using h0

/-- At `n₀ = m + 1`, `M ⧸ ν_{n, m + 1} M` is finite for every `n` iff `ω_m • M_δ` is finite. -/
theorem finite_quotSMulTop_growthTransition_succ_iff {p : ℕ} (hp : p.Prime) (hp0 : (p : O) ≠ 0)
    (hM : Module.IsTorsion O⟦X⟧ M) (m : ℕ) :
    (∀ n, Finite (QuotSMulTop (growthTransition p O (m + 1) n : O⟦X⟧) M)) ↔
      Finite ↥(((1 + X) ^ p ^ m - 1 : O⟦X⟧) • deltaSubmodule p O M) := by
  have : Fact p.Prime := ⟨hp⟩
  have h := finite_quotSMulTop_growthTransition_iff hp hp0 hM (m + 1)
  simpa only [Polynomial.prod_range_cyclotomic_prime_pow_comp_X_add_one p m, Polynomial.coe_sub,
    Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X] using h

/-- **Existence of a cyclotomic cutoff.** Every finitely generated torsion `O⟦X⟧`-module over a
complete discrete valuation ring with finite residue field and `(p : O) ≠ 0` admits a level `n₀`
from which all quotients `M ⧸ ν_{n, n₀} M` are finite. -/
theorem exists_finite_quotSMulTop_growthTransition {p : ℕ} (hp : p.Prime) (hp0 : (p : O) ≠ 0)
    (hM : Module.IsTorsion O⟦X⟧ M) :
    ∃ n₀ : ℕ, ∀ n, Finite (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M) := by
  have : IsNoetherian O⟦X⟧ M := isNoetherian_of_isNoetherianRing_of_finite O⟦X⟧ M
  obtain ⟨m, hm⟩ := exists_deltaSubmodule_eq_torsionBy p O M
  refine ⟨m + 1, (finite_quotSMulTop_growthTransition_succ_iff hp hp0 hM m).mpr ?_⟩
  have hbot : ((1 + X) ^ p ^ m - 1 : O⟦X⟧) • deltaSubmodule p O M = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.pointwise_smul_def, Submodule.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    rw [hm, mem_torsionBy_iff] at hy
    simpa using hy
  rw [hbot]
  infer_instance

end CyclotomicCutoff

section GrowthFormula

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)]
  {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]

omit [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] in
/-- Helper: in a DVR with `addVal O p = e > 0`, the ideal `(p)` equals `𝔪 ^ e`, and `p` is nonzero
and lies in `𝔪` and in the Jacobson radical of `⊥`. -/
private theorem span_natCast_eq_maximalIdeal_pow {p e : ℕ} (he : 0 < e)
    (hpe : IsDiscreteValuationRing.addVal O (p : O) = e) :
    (p : O) ≠ 0 ∧ (p : O) ∈ maximalIdeal O ∧ (p : O) ∈ (⊥ : Ideal O).jacobson ∧
      Ideal.span {(p : O)} = maximalIdeal O ^ e := by
  have hp0 : (p : O) ≠ 0 := by
    rintro h
    rw [h, AddValuation.map_zero] at hpe
    exact ENat.top_ne_natCast e hpe
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, hpu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have hme : m = e := by
    have hval := IsDiscreteValuationRing.addVal_def' u hϖ m
    rw [← hpu, hpe] at hval
    exact Nat.cast_injective hval.symm
  subst hme
  have hspan : Ideal.span {(p : O)} = maximalIdeal O ^ m := by
    rw [hpu, Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq]
  have hp𝔪 : (p : O) ∈ maximalIdeal O := by
    rw [← pow_one (maximalIdeal O)]
    exact Ideal.pow_le_pow_right he (hspan ▸ Ideal.mem_span_singleton_self _)
  have hpjac : (p : O) ∈ (⊥ : Ideal O).jacobson := by
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
  exact ⟨hp0, hp𝔪, hpjac, hspan⟩

/-- Helper: stabilization of the finite kernels `M[ν_{k, n₀}]` yields a power of `q`. -/
private theorem exists_natCard_torsionBy_growthTransition {p n₀ : ℕ}
    (hfin : ∀ n, Finite (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M)) :
    ∃ (t N : ℕ), ∀ k ≥ N,
      Nat.card (torsionBy O⟦X⟧ M (growthTransition p O n₀ k : O⟦X⟧)) =
        Nat.card (ResidueField O) ^ t := by
  have : IsNoetherian O⟦X⟧ M := isNoetherian_of_isNoetherianRing_of_finite O⟦X⟧ M
  let T : ℕ → Submodule O⟦X⟧ M := fun k ↦ torsionBy O⟦X⟧ M (growthTransition p O n₀ k : O⟦X⟧)
  have hmono : Monotone T := fun k₁ k₂ hk ↦
    Submodule.torsionBy_le_torsionBy_of_dvd _ _
      (map_dvd Polynomial.coeToPowerSeries.ringHom (growthTransition_dvd_of_le p O hk))
  obtain ⟨N, hN⟩ :=
    (IsNoetherian.noetherian (⨆ k, T k)).stabilizes_of_iSup_eq ⟨T, hmono⟩ rfl
  dsimp only [OrderHom.coe_mk] at hN
  have hstab : ∀ k ≥ N, T k = T N := fun k hk ↦ le_antisymm
    (by rw [← hN]; exact le_iSup T k) (hmono hk)
  have : Finite (T N) :=
    finite_torsionBy_of_finite_quotSMulTop (monic_growthTransition p O n₀ N) (hfin N)
  -- View `T N` as a finite `O`-module via `PowerSeries.C`; its cardinality is a power of `#κ(O)`.
  let : Module O (T N) := Module.compHom (T N) PowerSeries.C
  have hfl : IsFiniteLength O (T N) :=
    isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_of_finite O (T N), isArtinian_of_finite⟩
  refine ⟨(Module.length O (T N)).toNat, N, fun k hk ↦ ?_⟩
  rw [show torsionBy O⟦X⟧ M (growthTransition p O n₀ k : O⟦X⟧) = T N from hstab k hk]
  exact hfl.natCard_eq_natCard_residueField_pow_length

/-- Helper: asymptotic cardinality of `O ⧸ (Res(F_M, ν_{k, n₀}))` for `k ≥ n₁`. -/
private theorem natCard_quotient_span_resultant_growthTransition {p e n₀ : ℕ} (hp : p.Prime)
    (he : 0 < e) (hpe : IsDiscreteValuationRing.addVal O (p : O) = e)
    (hfin : ∀ n, Finite (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M)) :
    let n₁ := max n₀ (lambdaInvariant O M * e + 1)
    ∃ a₁ : ℕ, ∀ k ≥ n₁,
      Nat.card (O ⧸ Ideal.span {(charPoly O M).resultant (growthTransition p O n₀ k)}) =
        Nat.card (ResidueField O) ^ (a₁ + e * lambdaInvariant O M * (k - n₁)) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, hpjac, hspan⟩ := span_natCast_eq_maximalIdeal_pow (O := O) he hpe
  set n₁ := max n₀ (lambdaInvariant O M * e + 1)
  have hr₁ : (charPoly O M).resultant (growthTransition p O n₀ n₁) ≠ 0 :=
    resultant_charPoly_ne_zero_of_finite_quotSMulTop (hfin n₁)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨a₁, u₁, hu₁⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr₁ hϖ
  have hspan₁ : Ideal.span {(charPoly O M).resultant (growthTransition p O n₀ n₁)} =
      maximalIdeal O ^ a₁ := by
    rw [hu₁, Ideal.span_singleton_mul_left_unit u₁.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq]
  refine ⟨a₁, fun k hk ↦ ?_⟩
  -- Split `ν_{k, n₀} = ν_{n₁, n₀} · ν_{k, n₁ + 1}` and apply multiplicativity of the resultant.
  have hmul := growthTransition_mul p O (n₀ := n₀) (m := n₁) (n := k)
    (Nat.le_succ_of_le (le_max_left _ _)) hk
  have hres_mul : (charPoly O M).resultant (growthTransition p O n₀ k) =
      (charPoly O M).resultant (growthTransition p O n₀ n₁) *
        (charPoly O M).resultant (growthTransition p O (n₁ + 1) k) := by
    have hmon₁ := monic_growthTransition p O n₀ n₁
    have hmon₂ := monic_growthTransition p O (n₁ + 1) k
    rw [← hmul, hmon₁.natDegree_mul hmon₂,
      Polynomial.resultant_mul_right _ _ _ _ le_rfl]
  -- Evaluate `Res(F_M, ν_{k, n₁ + 1}) ~ p ^ (λ (k - n₁))` via `CyclotomicGrowth`.
  have hF : (charPoly O M).IsDistinguishedAt (maximalIdeal O) := isDistinguishedAt_charPoly
  have hreidx : (growthTransition p O (n₁ + 1) k : O⟦X⟧) =
      ∏ j ∈ Finset.Ico n₁ k,
        ((Polynomial.cyclotomic (p ^ (j + 1)) O).comp (Polynomial.X + 1) : O⟦X⟧) := by
    rw [growthTransition_def, ← Finset.prod_Ico_add'
      (fun j ↦ (Polynomial.cyclotomic (p ^ j) O).comp (Polynomial.X + 1)) n₁ k 1,
      ← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    rfl
  have hassoc : Associated ((charPoly O M).resultant (growthTransition p O (n₁ + 1) k))
      ((p : O) ^ (lambdaInvariant O M * (k - n₁))) := by
    have H := hF.isWeierstrassFactorizationAt
    have hn₁_gt : (charPoly O M).natDegree * e < n₁ := by
      rw [← lambdaInvariant_def]
      exact (Nat.lt_succ_self _).trans_le (le_max_right n₀ _)
    rw [← H.norm_mk_coe_eq_resultant, hreidx, lambdaInvariant_def]
    exact hF.associated_norm_mk_prod_cyclotomic_prime_pow_comp_X_add_one hspan.ge hpjac hn₁_gt k
  have hspan₂ : Ideal.span {(charPoly O M).resultant (growthTransition p O (n₁ + 1) k)} =
      maximalIdeal O ^ (e * lambdaInvariant O M * (k - n₁)) := by
    rw [Ideal.span_singleton_eq_span_singleton.mpr hassoc, ← Ideal.span_singleton_pow, hspan,
      ← pow_mul, mul_assoc]
  rw [hres_mul, ← Ideal.span_singleton_mul_span_singleton, hspan₁, hspan₂, ← pow_add,
    TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow]

/-- **Iwasawa's growth formula** (Neukirch–Schmidt–Wingberg, Theorem 5.3.18; Washington,
Theorem 13.13). Let `O` be a complete discrete valuation ring with finite residue field of
cardinality `q`, mixed characteristic `(0, p)` and absolute ramification index `e = v_O(p) > 0`,
and let `M` be a finitely generated `O⟦X⟧`-module. If `M ⧸ ν_{n, n₀} M` is finite for every `n`,
then there exist an integer `ν` and a threshold `N` such that for all `k ≥ N`,
`μ · p ^ k + e · λ · k + ν ≥ 0` and `#(M ⧸ ν_{k, n₀} M) = q ^ (μ · p ^ k + e · λ · k + ν)`. -/
theorem natCard_quotSMulTop_growthTransition {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hpe : IsDiscreteValuationRing.addVal O (p : O) = e) {n₀ : ℕ}
    (hfin : ∀ n, Finite (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M)) :
    ∃ (ν : ℤ) (N : ℕ), ∀ k ≥ N,
      0 ≤ (muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℤ) + ν ∧
      Nat.card (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M) =
        Nat.card (ResidueField O) ^
          ((muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℤ) + ν).toNat := by
  obtain ⟨-, hp𝔪, -, -⟩ := span_natCast_eq_maximalIdeal_pow (O := O) he hpe
  obtain ⟨t, N₀, hT⟩ := exists_natCard_torsionBy_growthTransition (O := O) (M := M) hfin
  obtain ⟨a₁, hR⟩ := natCard_quotient_span_resultant_growthTransition (O := O) (M := M) hp he hpe
    hfin
  set n₁ := max n₀ (lambdaInvariant O M * e + 1)
  set c₀ := if n₀ = 0 then 0 else p ^ (n₀ - 1)
  set μ := muInvariant O M
  set l := lambdaInvariant O M
  refine ⟨(t + a₁ : ℤ) - (μ * c₀ : ℤ) - (e * l * n₁ : ℤ), max N₀ n₁, fun k hk ↦ ?_⟩
  have hk₀ : N₀ ≤ k := (le_max_left N₀ n₁).trans hk
  have hk₁ : n₁ ≤ k := (le_max_right N₀ n₁).trans hk
  have hn₀k : n₀ ≤ k := (le_max_left n₀ _).trans hk₁
  have hc₀_le : c₀ ≤ p ^ k := by
    dsimp only [c₀]
    split_ifs with h0
    · exact Nat.zero_le _
    · exact Nat.pow_le_pow_right hp.pos (by omega)
  have hE : ((t + μ * (p ^ k - c₀) + a₁ + e * l * (k - n₁) : ℕ) : ℤ) =
      (μ * p ^ k + e * l * k : ℤ) + ((t + a₁ : ℤ) - (μ * c₀ : ℤ) - (e * l * n₁ : ℤ)) := by
    push_cast [Nat.cast_sub hc₀_le, Nat.cast_sub hk₁]
    ring
  refine ⟨hE ▸ Int.natCast_nonneg _, ?_⟩
  rw [← hE, Int.toNat_natCast]
  -- Combine the Euler quotient with the stabilized kernel and asymptotic resultant order.
  have heuler := natCard_quotSMulTop_div_natCard_torsionBy (O := O) (M := M)
    (isDistinguishedAt_growthTransition p O hp hp𝔪 n₀ k) (hfin k)
  rw [hT k hk₀, hR k hk₁, natDegree_growthTransition p O hp (by omega)] at heuler
  have hqt : ((Nat.card (ResidueField O) ^ t : ℕ) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (pow_ne_zero t Nat.card_pos.ne')
  have hq_eq : (Nat.card (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M) : ℚ) =
      ((Nat.card (ResidueField O) ^ (t + μ * (p ^ k - c₀) + a₁ + e * l * (k - n₁)) : ℕ) : ℚ) := by
    rw [div_eq_iff hqt] at heuler
    rw [heuler]
    push_cast
    simp only [pow_add]
    ring
  exact_mod_cast hq_eq

/-- **Iwasawa's growth formula in powers of `p`.** When the residue field has cardinality `p ^ f`,
`#(M ⧸ ν_{k, n₀} M) = p ^ (f μ p ^ k + e f λ k + ν)` for all sufficiently large `k`. -/
theorem natCard_quotSMulTop_growthTransition_pow {p e f : ℕ} (hp : p.Prime) (he : 0 < e)
    (hpe : IsDiscreteValuationRing.addVal O (p : O) = e)
    (hq : Nat.card (ResidueField O) = p ^ f) {n₀ : ℕ}
    (hfin : ∀ n, Finite (QuotSMulTop (growthTransition p O n₀ n : O⟦X⟧) M)) :
    ∃ (ν : ℤ) (N : ℕ), ∀ k ≥ N,
      0 ≤ (f * muInvariant O M * p ^ k + e * f * lambdaInvariant O M * k : ℤ) + ν ∧
      Nat.card (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M) =
        p ^ ((f * muInvariant O M * p ^ k + e * f * lambdaInvariant O M * k : ℤ) + ν).toNat := by
  obtain ⟨ν, N, hN⟩ := natCard_quotSMulTop_growthTransition (O := O) (M := M) hp he hpe hfin
  refine ⟨(f : ℤ) * ν, N, fun k hk ↦ ?_⟩
  obtain ⟨hnn, hcard⟩ := hN k hk
  have hmul : (f : ℤ) * ((muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℤ) + ν) =
      (f * muInvariant O M * p ^ k + e * f * lambdaInvariant O M * k : ℤ) + (f : ℤ) * ν := by
    ring
  have hnn' : 0 ≤ (f * muInvariant O M * p ^ k + e * f * lambdaInvariant O M * k : ℤ) +
      (f : ℤ) * ν := hmul ▸ mul_nonneg (Int.natCast_nonneg f) hnn
  refine ⟨hnn', ?_⟩
  rw [hcard, hq, ← pow_mul]
  congr 1
  exact Nat.cast_injective (R := ℤ) <| by
    rw [Nat.cast_mul, Int.toNat_of_nonneg hnn, Int.toNat_of_nonneg hnn']
    exact hmul

/-- **Iwasawa's growth formula at `n₀ = 0`** for `ω_k = (1 + X) ^ p ^ k - 1`: if `M ⧸ ω_n M` is
finite for every `n`, then `#(M ⧸ ω_k M) = q ^ (μ p ^ k + e λ k + ν)` for all sufficiently large
`k`. -/
theorem natCard_quotSMulTop_one_add_X_pow_sub_one {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hpe : IsDiscreteValuationRing.addVal O (p : O) = e)
    (hfin : ∀ n, Finite (QuotSMulTop ((1 + X) ^ p ^ n - 1 : O⟦X⟧) M)) :
    ∃ (ν : ℤ) (N : ℕ), ∀ k ≥ N,
      0 ≤ (muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℤ) + ν ∧
      Nat.card (QuotSMulTop ((1 + X) ^ p ^ k - 1 : O⟦X⟧) M) =
        Nat.card (ResidueField O) ^
          ((muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℤ) + ν).toNat := by
  have hcoe (k : ℕ) : (growthTransition p O 0 k : O⟦X⟧) = (1 + X) ^ p ^ k - 1 := by
    rw [growthTransition_zero p O hp k]; simp
  simpa only [hcoe] using natCard_quotSMulTop_growthTransition (O := O) (M := M) hp he hpe
    (n₀ := 0) (by simpa only [hcoe] using hfin)

/-- **Unconditional existence of Iwasawa's growth formula.** Every finitely generated torsion
`O⟦X⟧`-module over a complete discrete valuation ring of mixed characteristic with finite residue
field admits a cutoff `n₀`, an integer `ν`, and a threshold `N` such that
`#(M ⧸ ν_{k, n₀} M) = q ^ (μ p ^ k + e λ k + ν)` for all `k ≥ N`. -/
theorem exists_natCard_quotSMulTop_growthTransition {p e : ℕ} (hp : p.Prime) (he : 0 < e)
    (hpe : IsDiscreteValuationRing.addVal O (p : O) = e) (hM : Module.IsTorsion O⟦X⟧ M) :
    ∃ (n₀ : ℕ) (ν : ℤ) (N : ℕ), ∀ k ≥ N,
      0 ≤ (muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℤ) + ν ∧
      Nat.card (QuotSMulTop (growthTransition p O n₀ k : O⟦X⟧) M) =
        Nat.card (ResidueField O) ^
          ((muInvariant O M * p ^ k + e * lambdaInvariant O M * k : ℤ) + ν).toNat := by
  obtain ⟨hp0, -, -, -⟩ := span_natCast_eq_maximalIdeal_pow (O := O) he hpe
  obtain ⟨n₀, hfin⟩ := exists_finite_quotSMulTop_growthTransition (O := O) (M := M) hp hp0 hM
  obtain ⟨ν, N, hN⟩ := natCard_quotSMulTop_growthTransition (O := O) (M := M) hp he hpe hfin
  exact ⟨n₀, ν, N, hN⟩

/-- **Iwasawa's growth formula over `ℤ_p`.** For a finitely generated `ℤ_p⟦X⟧`-module `M`, if
`M ⧸ ν_{n, n₀} M` is finite for every `n`, then `#(M ⧸ ν_{k, n₀} M) = p ^ (μ p ^ k + λ k + ν)` for
all sufficiently large `k`. -/
theorem natCard_quotSMulTop_growthTransition_padicInt (p : ℕ) [Fact p.Prime] {M : Type*}
    [AddCommGroup M] [Module ℤ_[p]⟦X⟧ M] [Module.Finite ℤ_[p]⟦X⟧ M] {n₀ : ℕ}
    (hfin : ∀ n, Finite (QuotSMulTop (growthTransition p ℤ_[p] n₀ n : ℤ_[p]⟦X⟧) M)) :
    ∃ (ν : ℤ) (N : ℕ), ∀ k ≥ N,
      0 ≤ (muInvariant ℤ_[p] M * p ^ k + lambdaInvariant ℤ_[p] M * k : ℤ) + ν ∧
      Nat.card (QuotSMulTop (growthTransition p ℤ_[p] n₀ k : ℤ_[p]⟦X⟧) M) =
        p ^ ((muInvariant ℤ_[p] M * p ^ k + lambdaInvariant ℤ_[p] M * k : ℤ) + ν).toNat := by
  have hpe : IsDiscreteValuationRing.addVal ℤ_[p] (p : ℤ_[p]) = (1 : ℕ) := by
    simpa using IsDiscreteValuationRing.addVal_uniformizer (PadicInt.irreducible_p (p := p))
  simpa only [Nat.cast_one, one_mul, PadicInt.card_residueField] using
    natCard_quotSMulTop_growthTransition (O := ℤ_[p]) (M := M) Fact.out Nat.one_pos hpe hfin

end GrowthFormula

/-! ### Sharpness checks and concrete examples

1. **Equal characteristic breaks the cyclotomic cutoff.** Over `O = (ZMod p)⟦t⟧` and
   `M = O⟦X⟧ ⧸ (X)`, `ω_0 = X` kills `M_δ = M`, yet `ν_{1, 1} = X ^ (p - 1)` acts as `0` on `M`,
   so `M ⧸ ν_{1, 1} M ≃ O` is infinite.
2. **Equal characteristic breaks linear `λ`-growth.** Over `O = (ZMod p)⟦t⟧` and
   `M = O⟦X⟧ ⧸ (X - t)` (`μ = 0, λ = 1`), `ω_n = X ^ p ^ n` acts by `t ^ p ^ n`, giving
   `#(M ⧸ ω_n M) = p ^ (p ^ n)` instead of linear growth in `n`.
3. **Ramified `p = 2, π² = 2` small-index check.** In a discrete valuation ring with residue field
   of cardinality `2` and uniformiser `π` satisfying `π² = 2`, `(1 + π)² - 1 = π² (1 + π)` has
   unit factor `1 + π` and quotient cardinality `4 = 2 ^ 2`.
4. **Explicit `ℤ_p` cutoff.** On `M = ℤ_p⟦X⟧ ⧸ (X)` (`μ = 0, λ = 1`), `M ⧸ ω_k M` is infinite for
   every `k`, while stripping `ξ_0 = X` gives `#(M ⧸ ν_{k, 1} M) = p ^ k` for all `k`. -/

section Examples

-- 1. Equal characteristic breaks the cyclotomic cutoff (`(p : O) = 0`).
example (p : ℕ) [Fact p.Prime] :
    let O := PowerSeries (ZMod p)
    let M := O⟦X⟧ ⧸ Ideal.span {(X : O⟦X⟧)}
    ((1 + X) ^ p ^ 0 - 1 : O⟦X⟧) • deltaSubmodule p O M = ⊥ ∧
      Infinite (QuotSMulTop (growthTransition p O 1 1 : O⟦X⟧) M) := by
  intro O M
  have hp : p.Prime := Fact.out
  have : CharP O p :=
    charP_of_injective_ringHom (Function.LeftInverse.injective (constantCoeff_C (R := ZMod p))) p
  refine ⟨?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    rw [Submodule.pointwise_smul_def, Submodule.mem_map] at hx
    rcases hx with ⟨y, -, rfl⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [DistribSMul.toLinearMap_apply, pow_zero, pow_one, add_sub_cancel_left]
    rw [Submodule.mem_bot, ← Ideal.Quotient.mk_eq_mk, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · -- In char `p`, `ν_{1, 1} = Φ_p(X + 1) = X ^ (p - 1)` kills `M`, so `M ⧸ ν_{1, 1} M ≃ M`.
    have hν : (growthTransition p O 1 1 : O⟦X⟧) = X ^ (p - 1) := by
      rw [growthTransition_self, Polynomial.cyclotomic_prime_pow_comp_X_add_one_eq_X_pow,
        pow_one, Nat.totient_prime hp, Polynomial.coe_pow, Polynomial.coe_X]
    have hsmul : (growthTransition p O 1 1 : O⟦X⟧) • (⊤ : Submodule O⟦X⟧ M) = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.pointwise_smul_def, Submodule.mem_map] at hx
      rcases hx with ⟨y, -, rfl⟩
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [DistribSMul.toLinearMap_apply, hν, Submodule.mem_bot, ← Ideal.Quotient.mk_eq_mk,
        ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
        Ideal.mem_span_singleton]
      exact (dvd_pow_self _ (Nat.sub_pos_of_lt hp.one_lt).ne').trans (dvd_mul_right _ _)
    have : Infinite O := TauCeti.IsDiscreteValuationRing.infinite
    have hM : Infinite M := Infinite.of_injective (fun c : O ↦ Ideal.Quotient.mk _ (C c))
      fun c₁ c₂ h ↦ by
        rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h
        obtain ⟨r, hr⟩ := h
        have hc := congrArg constantCoeff hr
        simp only [map_sub, constantCoeff_C, map_mul, constantCoeff_X, zero_mul] at hc
        exact sub_eq_zero.mp hc
    exact (Equiv.infinite_iff (Submodule.quotEquivOfEqBot _ hsmul).toEquiv).mpr hM

-- 2. Equal characteristic breaks linear `λ`-growth:
-- `M = O⟦X⟧ ⧸ (X - t)` has `#(M / ω_n M) = p ^ p ^ n`.
example (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let O := PowerSeries (ZMod p)
    let M := O⟦X⟧ ⧸ Ideal.span {((Polynomial.X - Polynomial.C (X : O) : O[X]) : O⟦X⟧)}
    Nat.card (QuotSMulTop ((1 + X) ^ p ^ n - 1 : O⟦X⟧) M) = p ^ p ^ n := by
  intro O M
  change Nat.card (QuotSMulTop ((1 + X) ^ p ^ n - 1 : ((ZMod p)⟦X⟧)⟦X⟧)
    (((ZMod p)⟦X⟧)⟦X⟧ ⧸ Ideal.span
      {((Polynomial.X - Polynomial.C (X : (ZMod p)⟦X⟧) : ((ZMod p)⟦X⟧)[X]) :
        ((ZMod p)⟦X⟧)⟦X⟧)})) = p ^ p ^ n
  have : CharP (ZMod p)⟦X⟧ p :=
    charP_of_injective_ringHom (Function.LeftInverse.injective (constantCoeff_C (R := ZMod p))) p
  have : IsAdicComplete (maximalIdeal (ZMod p)) (ZMod p) := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  have : IsAdicComplete (maximalIdeal (ZMod p)⟦X⟧) (ZMod p)⟦X⟧ :=
    PowerSeries.isAdicComplete_maximalIdeal
  have hF : (Polynomial.X - Polynomial.C (X : (ZMod p)⟦X⟧)).IsDistinguishedAt
      (maximalIdeal (ZMod p)⟦X⟧) := by
    refine ⟨⟨fun {k} hk ↦ ?_⟩, Polynomial.monic_X_sub_C _⟩
    rw [Polynomial.natDegree_X_sub_C, Nat.lt_one_iff] at hk
    subst hk
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub,
      neg_mem_iff]
    exact (PowerSeries.irreducible_X (R := ZMod p)).maximalIdeal_eq ▸
      Ideal.mem_span_singleton_self _
  have H := hF.isWeierstrassFactorizationAt
  have hcoe : (((1 + Polynomial.X) ^ p ^ n - 1 : ((ZMod p)⟦X⟧)[X]) : ((ZMod p)⟦X⟧)⟦X⟧) =
      (1 + X) ^ p ^ n - 1 := by simp
  have hnorm := H.norm_mk_coe_eq_resultant ((1 + Polynomial.X) ^ p ^ n - 1)
  rw [hcoe, Polynomial.natDegree_X_sub_C,
    Polynomial.resultant_X_sub_C_left _ _ (X : (ZMod p)⟦X⟧) le_rfl] at hnorm
  simp only [Polynomial.eval_pow, Polynomial.eval_X, add_pow_char_pow, one_pow,
    add_sub_cancel_left] at hnorm
  have hne : (X : (ZMod p)⟦X⟧) ^ p ^ n ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  rw [H.natCard_quotSMulTop (hnorm ▸ hne), hnorm, ← Ideal.span_singleton_pow,
    ← (PowerSeries.irreducible_X (R := ZMod p)).maximalIdeal_eq,
    TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow]
  have hres : Nat.card (ResidueField (ZMod p)⟦X⟧) = p := by
    have hker : RingHom.ker (constantCoeff (R := ZMod p)) = maximalIdeal (ZMod p)⟦X⟧ := by
      rw [PowerSeries.ker_constantCoeff,
        ← (PowerSeries.irreducible_X (R := ZMod p)).maximalIdeal_eq]
    have e : ResidueField (ZMod p)⟦X⟧ ≃+* ZMod p :=
      (Ideal.quotEquivOfEq hker.symm).trans
        (RingHom.quotientKerEquivOfSurjective (f := constantCoeff (R := ZMod p)) fun c ↦
          ⟨C c, constantCoeff_C c⟩)
    rw [Nat.card_congr e.toEquiv, Nat.card_zmod]
  rw [hres]

-- 3. Ramified `p = 2, π² = 2` small-index check: `(1 + π)² - 1 = π² (1 + π)` has index `4`.
example {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hq : Nat.card (ResidueField O) = 2) {π : O} (hπ : Irreducible π) (h2 : π ^ 2 = 2) :
    (1 + π) ^ 2 - 1 = π ^ 2 * (1 + π) ∧ IsUnit (1 + π) ∧
      Nat.card (O ⧸ Ideal.span {(1 + π) ^ 2 - 1}) = 4 := by
  have heq : (1 + π) ^ 2 - 1 = π ^ 2 * (1 + π) := by
    calc (1 + π) ^ 2 - 1 = 2 * π + π ^ 2 := by ring
      _ = π ^ 2 * π + π ^ 2 := by rw [← h2]
      _ = π ^ 2 * (1 + π) := by ring
  have hu : IsUnit (1 + π) := by
    rw [← notMem_maximalIdeal]
    intro hmem
    have h1 : (1 : O) ∈ maximalIdeal O := by
      have hsub := sub_mem hmem (hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
      rwa [add_sub_cancel_right] at hsub
    exact (maximalIdeal.isMaximal O).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  refine ⟨heq, hu, ?_⟩
  rw [heq, Ideal.span_singleton_mul_right_unit hu, ← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq,
    TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow, hq]
  norm_num

-- 4. Explicit `ℤ_p` cutoff on `M = ℤ_p⟦X⟧ ⧸ (X)`: `n₀ = 0` fails, while `n₀ = 1` gives `p ^ k`.
example (p : ℕ) [Fact p.Prime] (k : ℕ) :
    let M := ℤ_[p]⟦X⟧ ⧸ Ideal.span {(X : ℤ_[p]⟦X⟧)}
    Infinite (QuotSMulTop (growthTransition p ℤ_[p] 0 k : ℤ_[p]⟦X⟧) M) ∧
      Nat.card (QuotSMulTop (growthTransition p ℤ_[p] 1 k : ℤ_[p]⟦X⟧) M) = p ^ k := by
  intro M
  have hp : p.Prime := Fact.out
  have hX : (Polynomial.X : ℤ_[p][X]).IsDistinguishedAt (maximalIdeal ℤ_[p]) := by
    refine ⟨⟨fun {i} hi ↦ ?_⟩, Polynomial.monic_X⟩
    rw [Polynomial.natDegree_X, Nat.lt_one_iff] at hi
    simp [hi]
  have H := hX.isWeierstrassFactorizationAt
  have hres_eval (P : ℤ_[p][X]) : (Polynomial.X : ℤ_[p][X]).resultant P = P.eval 0 := by
    have h := Polynomial.resultant_X_sub_C_left P P.natDegree (0 : ℤ_[p]) le_rfl
    rwa [map_zero, sub_zero, ← Polynomial.natDegree_X (R := ℤ_[p])] at h
  have hXcoe : (X : ℤ_[p]⟦X⟧) = ((Polynomial.X : ℤ_[p][X]) : ℤ_[p]⟦X⟧) := Polynomial.coe_X.symm
  dsimp only [M]
  rw [hXcoe]
  refine ⟨?_, ?_⟩
  · refine TauCeti.Algebra.infinite_quotSMulTop_of_norm_eq_zero (A := ℤ_[p]) ?_
    rw [Ideal.Quotient.algebraMap_eq, H.norm_mk_coe_eq_resultant, hres_eval,
      growthTransition_zero p ℤ_[p] hp k]
    simp
  · have hnorm : Algebra.norm ℤ_[p]
        (Ideal.Quotient.mk (Ideal.span {((Polynomial.X : ℤ_[p][X]) : ℤ_[p]⟦X⟧)})
          (growthTransition p ℤ_[p] 1 k : ℤ_[p]⟦X⟧)) = (p : ℤ_[p]) ^ k := by
      rw [H.norm_mk_coe_eq_resultant, hres_eval, growthTransition_def, Polynomial.eval_prod]
      have hval : ∀ j ∈ Finset.Ico 1 (k + 1),
          ((Polynomial.cyclotomic (p ^ j) ℤ_[p]).comp (Polynomial.X + 1)).eval 0 =
            (p : ℤ_[p]) := by
        intro j hj
        rw [Finset.mem_Ico] at hj
        obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
        rw [← Polynomial.coeff_zero_eq_eval_zero,
          Polynomial.coeff_zero_cyclotomic_prime_pow_comp_X_add_one]
      rw [Finset.prod_congr rfl hval, Finset.prod_const, Nat.card_Ico, Nat.add_sub_cancel]
    have hne : ((p : ℤ_[p]) ^ k) ≠ 0 :=
      pow_ne_zero k (PadicInt.irreducible_p (p := p)).ne_zero
    rw [H.natCard_quotSMulTop (hnorm ▸ hne), hnorm, ← Ideal.span_singleton_pow,
      ← (PadicInt.irreducible_p (p := p)).maximalIdeal_eq,
      TauCeti.IsDiscreteValuationRing.natCard_quotient_maximalIdeal_pow, PadicInt.card_residueField]

end Examples

end TauCeti.Iwasawa
