/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.PowerSeries.Inverse
public import TauCeti.Algebra.Module.Presentation.Lift
public import TauCeti.RingTheory.FittingIdeal.Continuity

import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Nat.Multiplicity
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.Henselian.Semiperfect
import TauCeti.RingTheory.Idempotents.Semiperfect
import TauCeti.RingTheory.Jacobson.Finite
import TauCeti.RingTheory.PowerSeries.AdicComplete
import TauCeti.RingTheory.PowerSeries.Ideal
import TauCeti.RingTheory.PowerSeries.OneAddXPow
import TauCeti.RingTheory.RegularLocalRing.PowerSeries

/-!
# Closed-ideal Fitting continuity and square presentation lifting over `O⟦X⟧`

Let `p` be a prime and `O` a commutative module-finite `ℤ_[p]`-algebra (for instance a finite free
`ℤ_[p]`-algebra, possibly non-local or nonreduced, such as `ℤ₂[C₂]` or a dual-number order). Set
`R = O⟦X⟧`, and consider the Iwasawa tower ideals `I_n = ((1 + X) ^ pⁿ - 1)` and joint ideals
`J_{a,n} = (p^a, (1 + X) ^ pⁿ - 1)`.

## Cofinality and closed-ideal detection

For any ideal `I` of `O` containing `p` with `I ^ k ≤ (p)` (for instance `I = Ring.jacobson O`
for any commutative finite `ℤ_[p]`-algebra `O`, or `I = maximalIdeal O` when `O` is local), the
joint ideals `J_{a,n}` are cofinal in both directions with powers of `I.comap constantCoeff`:
* `J_{a,n} ≤ I.comap constantCoeff ^ N` whenever `N ≤ a` and `N ≤ n + 1`
  (`TauCeti.Iwasawa.jointIdeal_le_comap_constantCoeff_pow`), and
* `I.comap constantCoeff ^ (k * (a + a * p ^ n)) ≤ J_{a,n}`
  (`TauCeti.Iwasawa.comap_constantCoeff_pow_le_jointIdeal_of_pow_le`), proved using prime
  divisibility of the middle binomial coefficients `p ∣ choose (p ^ n) j`.

Since `O⟦X⟧` is Noetherian and `Ring.jacobson O⟦X⟧ = (Ring.jacobson O).comap constantCoeff`
(`PowerSeries.jacobson_eq_comap_constantCoeff`), Krull's intersection theorem implies closed-ideal
detection: two ideals of `O⟦X⟧` with the same image modulo `J_{a,n}` for a cofinal family of
`a > 0` and `n` are equal (`TauCeti.Iwasawa.ideal_eq_of_cofinal_map_jointIdeal`). Combining this
with arbitrary base change of Fitting ideals yields closed-ideal Fitting continuity from quotients
by `J_{a,n}` (`TauCeti.Iwasawa.controlledFitting_modCoefficient`) or by `I_n`
(`TauCeti.Iwasawa.controlledFitting_continuity`), as well as the specialization to principal
determinant ideals and finite products of coefficient orders.

## Lifting square presentations

Since `ℤ_[p]` is complete and therefore Henselian, every commutative finite `ℤ_[p]`-algebra `O` is
semiperfect (`TauCeti.IsSemiperfectRing.of_henselianRing`) and decomposes via a complete orthogonal
family of idempotents `eᵢ` into finitely many local finite `ℤ_[p]`-algebras `Oᵢ = O ⧸ (1 - eᵢ)`.
Passing to `O⟦X⟧ ⧸ (1 - C eᵢ) ≃+* Oᵢ⟦X⟧`, each factor is a Noetherian local ring in which the
tower ideals satisfy `I_n ≤ 𝔪 ^ (n + 1)`. If a finite `O⟦X⟧`-module `M` has quadratically presented
quotients `M ⧸ I_n M` over `O⟦X⟧ ⧸ I_n` for cofinally many `n` (with arbitrary, possibly varying
finite presentation sizes), then `M` is quadratically presented over `O⟦X⟧`
(`TauCeti.Iwasawa.controlledSquarePresentation`), admits a componentwise minimal finite projective
square presentation retaining its locally constant ranks
(`TauCeti.Iwasawa.controlledSquarePresentation_projective_cofinal`), and satisfies
`Fitt₀(M) = (det φ)` (`TauCeti.Iwasawa.controlledSquare_detFitting`). Whenever `Fitt₀(M)` contains
a non-zero-divisor, the relation determinant is a non-zero-divisor, the relation map is injective,
and `pd_{O⟦X⟧}(M) ≤ 1` (`TauCeti.Iwasawa.controlledSquare_hasProjectiveDimensionLE_one`).

## Main definitions

* `TauCeti.Iwasawa.towerIdeal`: the tower ideal `I_n = ((1 + X) ^ pⁿ - 1)` in `O⟦X⟧`.
* `TauCeti.Iwasawa.jointIdeal`: the joint ideal `J_{a,n} = (p^a, (1 + X) ^ pⁿ - 1)` in `O⟦X⟧`.

## Main results

* `TauCeti.Iwasawa.jointIdeal_le_comap_constantCoeff_pow`,
  `TauCeti.Iwasawa.comap_constantCoeff_pow_le_jointIdeal_of_pow_le`: both cofinality inclusions
  between `J_{a,n}` and powers of `I.comap constantCoeff`.
* `TauCeti.Iwasawa.controlledFitting_modCoefficient`,
  `TauCeti.Iwasawa.controlledFitting_continuity`,
  `TauCeti.Iwasawa.controlledFitting_continuity_span_singleton`,
  `TauCeti.Iwasawa.controlledFitting_continuity_pi`: closed-ideal Fitting continuity.
* `TauCeti.Iwasawa.controlledSquarePresentation`,
  `TauCeti.Iwasawa.controlledSquarePresentation_projective_cofinal`,
  `TauCeti.Iwasawa.controlledSquare_detFitting`,
  `TauCeti.Iwasawa.controlledSquare_hasProjectiveDimensionLE_one`: lifting square presentations
  from cofinal tower quotients over commutative finite `ℤ_[p]`-algebras.

## References

* M. Kurihara, *Iwasawa theory and Fitting ideals*, J. Reine Angew. Math. 561 (2003), Theorem 2.12
  and Lemma 4.2(2).
* H. Matsumura, *Commutative Ring Theory*, Cambridge University Press (1986), §§8–9.
-/

public section

noncomputable section

open CategoryTheory IsLocalRing PowerSeries TensorProduct

open scoped Matrix

namespace TauCeti.Iwasawa

section TowerAndJointIdeals

variable (p : ℕ) (O : Type*) [CommRing O]

/-- The `n`-th Iwasawa tower ideal `I_n = ((1 + X) ^ pⁿ - 1)` in `O⟦X⟧`. -/
def towerIdeal (n : ℕ) : Ideal O⟦X⟧ :=
  Ideal.span {(1 + X : O⟦X⟧) ^ p ^ n - 1}

/-- The joint Iwasawa ideal `J_{a,n} = (p^a, (1 + X) ^ pⁿ - 1)` in `O⟦X⟧`. -/
def jointIdeal (a n : ℕ) : Ideal O⟦X⟧ :=
  Ideal.span {C (p : O) ^ a, (1 + X : O⟦X⟧) ^ p ^ n - 1}

@[simp]
theorem towerIdeal_zero : towerIdeal p O 0 = Ideal.span {(X : O⟦X⟧)} := by
  simp [towerIdeal]

@[simp]
theorem jointIdeal_zero_left (n : ℕ) : jointIdeal p O 0 n = ⊤ := by
  rw [jointIdeal, pow_zero, Ideal.eq_top_iff_one]
  exact Ideal.subset_span (by simp)

@[simp]
theorem jointIdeal_one_zero : jointIdeal p O 1 0 = Ideal.span {C (p : O), X} := by
  simp [jointIdeal]

theorem jointIdeal_eq_sup (a n : ℕ) :
    jointIdeal p O a n = Ideal.span {C (p : O) ^ a} ⊔ towerIdeal p O n := by
  rw [jointIdeal, towerIdeal, ← Ideal.span_union, Set.singleton_union]

theorem towerIdeal_le_jointIdeal (a n : ℕ) : towerIdeal p O n ≤ jointIdeal p O a n := by
  rw [jointIdeal_eq_sup]
  exact le_sup_right

theorem span_C_pow_le_jointIdeal (a n : ℕ) :
    Ideal.span {C (p : O) ^ a} ≤ jointIdeal p O a n := by
  rw [jointIdeal_eq_sup]
  exact le_sup_left

theorem towerIdeal_antitone : Antitone (towerIdeal p O) := by
  refine antitone_nat_of_succ_le fun n ↦ ?_
  rw [towerIdeal, towerIdeal, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
  conv_rhs => rw [pow_succ p n, pow_mul, ← geom_sum_mul]
  exact ⟨∑ i ∈ Finset.range p, ((1 + X : O⟦X⟧) ^ p ^ n) ^ i, mul_comm _ _⟩

theorem jointIdeal_antitone {a a' n n' : ℕ} (ha : a ≤ a') (hn : n ≤ n') :
    jointIdeal p O a' n' ≤ jointIdeal p O a n := by
  rw [jointIdeal_eq_sup, jointIdeal_eq_sup]
  refine sup_le_sup ?_ (towerIdeal_antitone p O hn)
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
  exact pow_dvd_pow _ ha

theorem map_towerIdeal {S : Type*} [CommRing S] (φ : O →+* S) (n : ℕ) :
    (towerIdeal p O n).map (PowerSeries.map φ) = towerIdeal p S n := by
  rw [towerIdeal, towerIdeal, Ideal.map_span, Set.image_singleton]
  simp

theorem map_jointIdeal {S : Type*} [CommRing S] (φ : O →+* S) (a n : ℕ) :
    (jointIdeal p O a n).map (PowerSeries.map φ) = jointIdeal p S a n := by
  rw [jointIdeal, jointIdeal, Ideal.map_span]
  simp

end TowerAndJointIdeals

section Cofinality

variable {p : ℕ} {O : Type*} [CommRing O]

/-- The tower ideal `I_n` lies in `(I.comap constantCoeff) ^ (n + 1)` whenever `p ∈ I`. -/
theorem towerIdeal_le_comap_constantCoeff_pow {I : Ideal O} (hI : (p : O) ∈ I) (n : ℕ) :
    towerIdeal p O n ≤ I.comap constantCoeff ^ (n + 1) := by
  rw [towerIdeal, Ideal.span_singleton_le_iff_mem]
  exact PowerSeries.one_add_X_pow_sub_one_mem_comap_constantCoeff_pow hI n

/-- Over a local ring with `p ∈ 𝔪_O`, the tower ideal `I_n` lies in `𝔪_{O⟦X⟧} ^ (n + 1)`. -/
theorem towerIdeal_le_maximalIdeal_pow [IsLocalRing O] (hp : (p : O) ∈ maximalIdeal O) (n : ℕ) :
    towerIdeal p O n ≤ maximalIdeal O⟦X⟧ ^ (n + 1) := by
  rw [TauCeti.PowerSeries.maximalIdeal_eq_comap_constantCoeff]
  exact towerIdeal_le_comap_constantCoeff_pow hp n

/-- **Upper cofinality bound for joint ideals.** If `p ∈ I`, `N ≤ a`, and `N ≤ n + 1`, then
`J_{a,n} ≤ (I.comap constantCoeff) ^ N`. -/
theorem jointIdeal_le_comap_constantCoeff_pow {I : Ideal O} (hI : (p : O) ∈ I) {a n N : ℕ}
    (ha : N ≤ a) (hn : N ≤ n + 1) :
    jointIdeal p O a n ≤ I.comap constantCoeff ^ N := by
  rw [jointIdeal_eq_sup]
  refine sup_le ?_ ((towerIdeal_le_comap_constantCoeff_pow hI n).trans (Ideal.pow_le_pow_right hn))
  rw [Ideal.span_singleton_le_iff_mem]
  have hCp : C (p : O) ∈ I.comap constantCoeff := by
    rw [Ideal.mem_comap]
    simpa using hI
  exact Ideal.pow_le_pow_right ha (Ideal.pow_mem_pow hCp a)

/-- Over a local ring with `p ∈ 𝔪_O`, `J_{a,n} ≤ 𝔪_{O⟦X⟧} ^ N` whenever `N ≤ a` and `N ≤ n + 1`. -/
theorem jointIdeal_le_maximalIdeal_pow [IsLocalRing O] (hp : (p : O) ∈ maximalIdeal O)
    {a n N : ℕ} (ha : N ≤ a) (hn : N ≤ n + 1) :
    jointIdeal p O a n ≤ maximalIdeal O⟦X⟧ ^ N := by
  rw [TauCeti.PowerSeries.maximalIdeal_eq_comap_constantCoeff]
  exact jointIdeal_le_comap_constantCoeff_pow hp ha hn

/-- For a prime `p`, the binomial expansion gives `(1 + X) ^ pⁿ - 1 - X ^ pⁿ ∈ (C p)`. -/
theorem one_add_X_pow_sub_one_sub_X_pow_mem_span_C (hp : p.Prime) (n : ℕ) :
    (1 + X : O⟦X⟧) ^ p ^ n - 1 - X ^ p ^ n ∈ Ideal.span {C (p : O)} := by
  have hpos : 0 < p ^ n := pow_pos hp.pos n
  -- Expand `(X + 1) ^ pⁿ` and split off the top (`k = pⁿ`) and bottom (`k = 0`) terms.
  have hexp : (1 + X : O⟦X⟧) ^ p ^ n =
      ∑ k ∈ Finset.range (p ^ n + 1), X ^ k * ((p ^ n).choose k : O⟦X⟧) := by
    rw [add_comm, add_pow]
    refine Finset.sum_congr rfl fun k _ ↦ by simp
  have hsplit : (1 + X : O⟦X⟧) ^ p ^ n - 1 - X ^ p ^ n =
      ∑ k ∈ Finset.range (p ^ n - 1), X ^ (k + 1) * ((p ^ n).choose (k + 1) : O⟦X⟧) := by
    rw [hexp, Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one]
    have hsum : ∑ k ∈ Finset.range (p ^ n), X ^ k * ((p ^ n).choose k : O⟦X⟧) =
        1 + ∑ k ∈ Finset.range (p ^ n - 1), X ^ (k + 1) * ((p ^ n).choose (k + 1) : O⟦X⟧) := by
      conv_lhs => arg 1; rw [← Nat.sub_add_cancel hpos]
      rw [Finset.sum_range_succ', add_comm]
      simp
    rw [hsum]
    ring
  rw [hsplit]
  refine Ideal.sum_mem _ fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  have hdvd : p ∣ (p ^ n).choose (k + 1) :=
    hp.dvd_choose_pow (Nat.succ_ne_zero k) (by omega)
  obtain ⟨m, hm⟩ := hdvd
  have hcast : ((p ^ n).choose (k + 1) : O⟦X⟧) = C (p : O) * (m : O⟦X⟧) := by
    rw [hm, Nat.cast_mul, map_natCast]
  rw [hcast, ← mul_assoc, mul_comm (X ^ (k + 1)), mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- For a prime `p`, the monomial `X ^ (a * pⁿ)` lies in `J_{a,n} = (p^a, (1 + X) ^ pⁿ - 1)`. -/
theorem X_pow_mul_mem_jointIdeal (hp : p.Prime) (a n : ℕ) :
    (X : O⟦X⟧) ^ (a * p ^ n) ∈ jointIdeal p O a n := by
  have hcong := one_add_X_pow_sub_one_sub_X_pow_mem_span_C (O := O) hp n
  rw [Ideal.mem_span_singleton] at hcong
  obtain ⟨g, hg⟩ := hcong
  set ω : O⟦X⟧ := (1 + X) ^ p ^ n - 1
  have hX : (X : O⟦X⟧) ^ p ^ n = ω + -(C (p : O) * g) := by
    have : ω - X ^ p ^ n = C (p : O) * g := hg
    linear_combination -this
  rw [mul_comm, pow_mul, hX, add_pow]
  refine Ideal.sum_mem _ fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
    rw [← mul_neg, mul_pow]
    have hmem : C (p : O) ^ a ∈ jointIdeal p O a n :=
      span_C_pow_le_jointIdeal p O a n (Ideal.mem_span_singleton_self _)
    exact Ideal.mul_mem_right _ _ hmem
  · have hω : ω ∈ jointIdeal p O a n :=
      towerIdeal_le_jointIdeal p O a n (Ideal.mem_span_singleton_self _)
    have hpow : ω ^ k ∈ jointIdeal p O a n :=
      Ideal.pow_mem_of_mem _ hω k hkpos
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hpow)

/-- **Lower cofinality bound for `(p, X)`.** For a prime `p`,
`((p).comap constantCoeff) ^ (a + a * pⁿ) ≤ J_{a,n}`. -/
theorem comap_constantCoeff_span_pow_le_jointIdeal (hp : p.Prime) (a n : ℕ) :
    (Ideal.span {(p : O)}).comap constantCoeff ^ (a + a * p ^ n) ≤ jointIdeal p O a n := by
  intro f hf
  rw [PowerSeries.mem_comap_constantCoeff_pow_iff] at hf
  set M := a * p ^ n
  let t : O⟦X⟧ := ∑ j ∈ Finset.range M, C (coeff j f) * X ^ j
  -- The tail `f - t` is divisible by `X ^ M ∈ J_{a,n}`.
  have htail : f - t ∈ jointIdeal p O a n := by
    have hdvd : (X : O⟦X⟧) ^ M ∣ f - t := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro j hj
      rw [map_sub, map_sum]
      have hsum : ∑ k ∈ Finset.range M, coeff j (C (coeff k f) * X ^ k) = coeff j f := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro k _ hkj
          simp [hkj.symm]
        · intro h
          exact absurd (Finset.mem_range.mpr hj) h
      rw [hsum, sub_self]
    obtain ⟨q, hq⟩ := hdvd
    rw [hq]
    exact Ideal.mul_mem_right q _ (X_pow_mul_mem_jointIdeal hp a n)
  -- Each term of the truncation `t` has coefficient in `(p) ^ a`, so `t ∈ J_{a,n}`.
  have htrunc : t ∈ jointIdeal p O a n := by
    refine Ideal.sum_mem _ fun j hj ↦ ?_
    rw [Finset.mem_range] at hj
    have hcoeff : coeff j f ∈ Ideal.span {(p : O)} ^ a :=
      Ideal.pow_le_pow_right (by omega : a ≤ a + M - j) (hf j)
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hcoeff
    obtain ⟨c, hc⟩ := hcoeff
    have hC : C (coeff j f) = C (p : O) ^ a * C c := by
      rw [hc, map_mul, map_pow]
    rw [hC, mul_assoc]
    exact Ideal.mul_mem_right _ _
      (span_C_pow_le_jointIdeal p O a n (Ideal.mem_span_singleton_self _))
  have hEq : f = (f - t) + t := by abel
  rw [hEq]
  exact add_mem htail htrunc

/-- **Lower cofinality bound for any ideal `I` with `I ^ k ≤ (p)`.** If `p` is prime, `0 < k`,
and `I ^ k ≤ (p)`, then `(I.comap constantCoeff) ^ (k * (a + a * pⁿ)) ≤ J_{a,n}`. -/
theorem comap_constantCoeff_pow_le_jointIdeal_of_pow_le (hp : p.Prime) {I : Ideal O} {k : ℕ}
    (hk : 0 < k) (hIk : I ^ k ≤ Ideal.span {(p : O)}) (a n : ℕ) :
    I.comap constantCoeff ^ (k * (a + a * p ^ n)) ≤ jointIdeal p O a n := by
  refine le_trans ?_ (comap_constantCoeff_span_pow_le_jointIdeal hp a n)
  intro f hf
  rw [PowerSeries.mem_comap_constantCoeff_pow_iff] at hf ⊢
  intro j
  set N := a + a * p ^ n
  by_cases hj : N ≤ j
  · simp [Nat.sub_eq_zero_of_le hj]
  · have hle : k * (N - j) ≤ k * N - j := by
      have : j ≤ k * j := Nat.le_mul_of_pos_left j hk
      rw [Nat.mul_sub]
      omega
    have h1 : coeff j f ∈ I ^ (k * (N - j)) := Ideal.pow_le_pow_right hle (hf j)
    rw [pow_mul] at h1
    exact pow_le_pow_left' hIk (N - j) h1

/-- Over a local ring `O` with `𝔪_O ^ k ≤ (p)` (`k > 0`), powers of `𝔪_{O⟦X⟧}` are contained in
every joint ideal `J_{a,n}`. -/
theorem maximalIdeal_pow_le_jointIdeal_of_pow_le [IsLocalRing O] (hp : p.Prime) {k : ℕ}
    (hk : 0 < k) (hmk : maximalIdeal O ^ k ≤ Ideal.span {(p : O)}) (a n : ℕ) :
    maximalIdeal O⟦X⟧ ^ (k * (a + a * p ^ n)) ≤ jointIdeal p O a n := by
  rw [TauCeti.PowerSeries.maximalIdeal_eq_comap_constantCoeff]
  exact comap_constantCoeff_pow_le_jointIdeal_of_pow_le hp hk hmk a n

/-- Over a local module-finite `ℤ_[p]`-algebra `O`, the joint ideals `J_{a,n}` are cofinal in both
directions with powers of `𝔪_{O⟦X⟧}`. -/
theorem jointIdeal_cofinal_maximalIdeal_pow [Fact p.Prime] [IsLocalRing O]
    [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    (∀ N : ℕ, ∃ a n : ℕ, 0 < a ∧ jointIdeal p O a n ≤ maximalIdeal O⟦X⟧ ^ N) ∧
    (∀ a n : ℕ, ∃ M : ℕ, maximalIdeal O⟦X⟧ ^ M ≤ jointIdeal p O a n) := by
  have hp_mem : (p : O) ∈ maximalIdeal O := by
    have hpZ : (p : ℤ_[p]) ∈ Ring.jacobson ℤ_[p] := by
      rw [ringJacobson_eq_maximalIdeal, PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    have hJ := TauCeti.Ring.algebraMap_mem_jacobson (A := O) hpZ
    rwa [map_natCast, ringJacobson_eq_maximalIdeal] at hJ
  constructor
  · intro N
    refine ⟨max 1 N, N, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
    exact jointIdeal_le_maximalIdeal_pow hp_mem (le_max_right 1 N) (Nat.le_succ N)
  · intro a n
    obtain ⟨k, hk, hmk⟩ := TauCeti.Ring.exists_jacobson_pow_le_map_maximalIdeal ℤ_[p] O
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast,
      ringJacobson_eq_maximalIdeal] at hmk
    exact ⟨k * (a + a * p ^ n), maximalIdeal_pow_le_jointIdeal_of_pow_le Fact.out hk hmk a n⟩

end Cofinality

section FittingContinuity

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O] [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O]

private theorem natCast_prime_mem_jacobson : (p : O) ∈ Ring.jacobson O := by
  have hpZ : (p : ℤ_[p]) ∈ Ring.jacobson ℤ_[p] := by
    rw [ringJacobson_eq_maximalIdeal, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  simpa using TauCeti.Ring.algebraMap_mem_jacobson (A := O) hpZ

private theorem isNoetherianRing_powerSeries (R O : Type*) [CommRing R] [IsNoetherianRing R]
    [CommRing O] [Algebra R O] [Module.Finite R O] : IsNoetherianRing O⟦X⟧ := by
  have : Algebra.FiniteType R O := Module.Finite.finiteType O
  have : IsNoetherianRing O := Algebra.FiniteType.isNoetherianRing R O
  infer_instance

/-- **Closed-ideal detection in `O⟦X⟧` (cofinal subsystem form).** Let `O` be a commutative
module-finite `ℤ_[p]`-algebra. If two ideals `I, L` of `O⟦X⟧` have the same image modulo `J_{a,n}`
for cofinally large `a > 0` and `n`, then `I = L`. -/
theorem ideal_eq_of_cofinal_map_jointIdeal {I L : Ideal O⟦X⟧}
    (hcof : ∀ N : ℕ, ∃ a n : ℕ, 0 < a ∧ N ≤ a ∧ N ≤ n ∧
      I.map (Ideal.Quotient.mk (jointIdeal p O a n)) =
        L.map (Ideal.Quotient.mk (jointIdeal p O a n))) :
    I = L := by
  have : IsNoetherianRing O⟦X⟧ := isNoetherianRing_powerSeries ℤ_[p] O
  choose a n _ ha hn heq using hcof
  let J : Ideal O⟦X⟧ := (Ring.jacobson O).comap constantCoeff
  have hJ : J ≤ Ring.jacobson O⟦X⟧ := (PowerSeries.jacobson_eq_comap_constantCoeff O).ge
  exact Ideal.eq_of_forall_map_quotientMk_eq (K := fun N ↦ jointIdeal p O (a N) (n N)) hJ
    (fun N ↦ ⟨N, jointIdeal_le_comap_constantCoeff_pow natCast_prime_mem_jacobson (ha N)
      ((hn N).trans (Nat.le_succ (n N)))⟩)
    heq

/-- **Closed-ideal detection in `O⟦X⟧`.** Two ideals of `O⟦X⟧` having the same image modulo every
joint ideal `J_{a,n}` with `a > 0` are equal. -/
theorem ideal_eq_of_forall_map_jointIdeal {I L : Ideal O⟦X⟧}
    (h : ∀ a n : ℕ, 0 < a →
      I.map (Ideal.Quotient.mk (jointIdeal p O a n)) =
        L.map (Ideal.Quotient.mk (jointIdeal p O a n))) :
    I = L :=
  ideal_eq_of_cofinal_map_jointIdeal (p := p) fun N ↦
    ⟨max 1 N, N, lt_of_lt_of_le one_pos (le_max_left _ _), le_max_right 1 N, le_rfl,
      h _ _ (lt_of_lt_of_le one_pos (le_max_left _ _))⟩

/-- **Fitting continuity modulo joint coefficient ideals (cofinal form).** If a finite
`O⟦X⟧`-module `M` has the same `k`-th Fitting ideal as the image of `L` modulo `J_{a,n}` for
cofinally large `a > 0` and `n`, then `Fitt_k(M) = L`. -/
theorem controlledFitting_modCoefficient_cofinal {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M]
    [Module.Finite O⟦X⟧ M] {k : ℕ} {L : Ideal O⟦X⟧}
    (hcof : ∀ N : ℕ, ∃ a n : ℕ, 0 < a ∧ N ≤ a ∧ N ≤ n ∧
      fittingIdeal (O⟦X⟧ ⧸ jointIdeal p O a n)
        (M ⧸ (jointIdeal p O a n • (⊤ : Submodule O⟦X⟧ M))) k =
        L.map (Ideal.Quotient.mk (jointIdeal p O a n))) :
    fittingIdeal O⟦X⟧ M k = L := by
  refine ideal_eq_of_cofinal_map_jointIdeal (p := p) fun N ↦ ?_
  obtain ⟨a, n, ha_pos, ha, hn, hfit⟩ := hcof N
  refine ⟨a, n, ha_pos, ha, hn, ?_⟩
  simpa only [TauCeti.fittingIdeal_quotientSMulTop] using hfit

/-- **Fitting continuity modulo all joint coefficient ideals.** -/
theorem controlledFitting_modCoefficient {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M]
    [Module.Finite O⟦X⟧ M] {k : ℕ} {L : Ideal O⟦X⟧}
    (h : ∀ a n : ℕ, 0 < a →
      fittingIdeal (O⟦X⟧ ⧸ jointIdeal p O a n)
        (M ⧸ (jointIdeal p O a n • (⊤ : Submodule O⟦X⟧ M))) k =
        L.map (Ideal.Quotient.mk (jointIdeal p O a n))) :
    fittingIdeal O⟦X⟧ M k = L :=
  controlledFitting_modCoefficient_cofinal (p := p) fun N ↦
    ⟨max 1 N, N, lt_of_lt_of_le one_pos (le_max_left _ _), le_max_right 1 N, le_rfl,
      h _ _ (lt_of_lt_of_le one_pos (le_max_left _ _))⟩

/-- **Closed-ideal Fitting continuity from a cofinal subsystem of tower quotients.** If `M ⧸ I_n M`
has `k`-th Fitting ideal equal to the image of `L` over `O⟦X⟧ ⧸ I_n` for cofinally large `n`, then
further coefficient reductions agree modulo every cofinal `J_{a,n}`, hence `Fitt_k(M) = L`. -/
theorem controlledFitting_continuity_cofinal {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M]
    [Module.Finite O⟦X⟧ M] {k : ℕ} {L : Ideal O⟦X⟧}
    (hcof : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      fittingIdeal (O⟦X⟧ ⧸ towerIdeal p O n)
        (M ⧸ (towerIdeal p O n • (⊤ : Submodule O⟦X⟧ M))) k =
        L.map (Ideal.Quotient.mk (towerIdeal p O n))) :
    fittingIdeal O⟦X⟧ M k = L := by
  refine controlledFitting_modCoefficient_cofinal (p := p) fun N ↦ ?_
  obtain ⟨n, hn, hfit⟩ := hcof N
  rw [TauCeti.fittingIdeal_quotientSMulTop] at hfit
  set a := max 1 N
  have ha_pos : 0 < a := lt_of_lt_of_le one_pos (le_max_left _ _)
  have ha : N ≤ a := le_max_right 1 N
  refine ⟨a, n, ha_pos, ha, hn, ?_⟩
  rw [TauCeti.fittingIdeal_quotientSMulTop]
  have hfac := congrArg (Ideal.map (Ideal.Quotient.factor (towerIdeal_le_jointIdeal p O a n))) hfit
  simpa only [Ideal.map_map, Ideal.Quotient.factor_comp_mk] using hfac

/-- **Closed-ideal Fitting continuity from all tower quotients `M ⧸ I_n M`.** -/
theorem controlledFitting_continuity {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M]
    [Module.Finite O⟦X⟧ M] {k : ℕ} {L : Ideal O⟦X⟧}
    (h : ∀ n : ℕ,
      fittingIdeal (O⟦X⟧ ⧸ towerIdeal p O n)
        (M ⧸ (towerIdeal p O n • (⊤ : Submodule O⟦X⟧ M))) k =
        L.map (Ideal.Quotient.mk (towerIdeal p O n))) :
    fittingIdeal O⟦X⟧ M k = L :=
  controlledFitting_continuity_cofinal (p := p) fun N ↦ ⟨N, le_rfl, h N⟩

/-- **Closed-ideal Fitting continuity (tensor-quotient form).** -/
theorem controlledFitting_continuity_baseChange {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M]
    [Module.Finite O⟦X⟧ M] {k : ℕ} {L : Ideal O⟦X⟧}
    (hcof : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      fittingIdeal (O⟦X⟧ ⧸ towerIdeal p O n) ((O⟦X⟧ ⧸ towerIdeal p O n) ⊗[O⟦X⟧] M) k =
        L.map (Ideal.Quotient.mk (towerIdeal p O n))) :
    fittingIdeal O⟦X⟧ M k = L := by
  refine controlledFitting_continuity_cofinal (p := p) fun N ↦ ?_
  obtain ⟨n, hn, hfit⟩ := hcof N
  refine ⟨n, hn, ?_⟩
  rw [← fittingIdeal_congr (TauCeti.quotTensorEquivQuotSMulQuot (towerIdeal p O n)) k]
  exact hfit

/-- **Determinant-ideal specialization of closed-ideal Fitting continuity.** If for cofinally many
`n`, the zeroth Fitting ideal of `M ⧸ I_n M` over `O⟦X⟧ ⧸ I_n` is generated by the image of
`d : O⟦X⟧`, then `Fitt₀(M) = (d)`. -/
theorem controlledFitting_continuity_span_singleton {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M]
    [Module.Finite O⟦X⟧ M] {d : O⟦X⟧}
    (hcof : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      fittingIdeal (O⟦X⟧ ⧸ towerIdeal p O n)
        (M ⧸ (towerIdeal p O n • (⊤ : Submodule O⟦X⟧ M))) 0 =
        Ideal.span {Ideal.Quotient.mk (towerIdeal p O n) d}) :
    fittingIdeal O⟦X⟧ M 0 = Ideal.span {d} := by
  refine controlledFitting_continuity_cofinal (p := p) fun N ↦ ?_
  obtain ⟨n, hn, hfit⟩ := hcof N
  exact ⟨n, hn, by simpa only [Ideal.map_span, Set.image_singleton] using hfit⟩

/-- **Closed-ideal Fitting continuity over a finite product of coefficient orders.** Let `{Oᵢ}` be
a finite family of commutative module-finite `ℤ_[p]`-algebras and let `M` be a finite module over
`R = ∀ i, (Oᵢ)⟦X⟧`. If on each component `i` the base-changed module `Mᵢ = (Oᵢ)⟦X⟧ ⊗_R M`
satisfies the cofinal tower Fitting equality with respect to the projection of `L`, then
`Fitt_k(M) = L`. -/
theorem controlledFitting_continuity_pi {ι : Type*} [Finite ι] {O : ι → Type*}
    [∀ i, CommRing (O i)] [∀ i, Algebra ℤ_[p] (O i)] [∀ i, Module.Finite ℤ_[p] (O i)]
    {M : Type*} [AddCommGroup M] [Module (∀ i, (O i)⟦X⟧) M] [Module.Finite (∀ i, (O i)⟦X⟧) M]
    {k : ℕ} {L : Ideal (∀ i, (O i)⟦X⟧)}
    (hcomp : ∀ i,
      letI : Algebra (∀ j, (O j)⟦X⟧) (O i)⟦X⟧ := (Pi.evalRingHom (fun j ↦ (O j)⟦X⟧) i).toAlgebra
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        fittingIdeal ((O i)⟦X⟧ ⧸ towerIdeal p (O i) n)
          (((O i)⟦X⟧ ⊗[∀ j, (O j)⟦X⟧] M) ⧸
            (towerIdeal p (O i) n •
              (⊤ : Submodule (O i)⟦X⟧ ((O i)⟦X⟧ ⊗[∀ j, (O j)⟦X⟧] M)))) k =
          (L.map (Pi.evalRingHom (fun j ↦ (O j)⟦X⟧) i)).map
            (Ideal.Quotient.mk (towerIdeal p (O i) n))) :
    fittingIdeal (∀ i, (O i)⟦X⟧) M k = L := by
  refine TauCeti.fittingIdeal_eq_of_pi fun i ↦ ?_
  let : Algebra (∀ j, (O j)⟦X⟧) (O i)⟦X⟧ := (Pi.evalRingHom (fun j ↦ (O j)⟦X⟧) i).toAlgebra
  exact controlledFitting_continuity_cofinal (p := p) (O := O i) (hcomp i)

end FittingContinuity

section SquarePresentationLift

variable {p : ℕ}

/-- **Base change of tower-quotient quadratic presentations along a coefficient homomorphism.**
Given any ring homomorphism `φ : O →+* S`, if `M ⧸ I_n M` is quadratically presented over
`O⟦X⟧ ⧸ I_n`, then `(S⟦X⟧ ⊗_{O⟦X⟧} M) ⧸ I_n (S⟦X⟧ ⊗_{O⟦X⟧} M)` is quadratically presented over
`S⟦X⟧ ⧸ I_n`. -/
theorem isQuadraticallyPresented_towerQuotient_baseChange {O S : Type*} [CommRing O] [CommRing S]
    (φ : O →+* S) {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M] {n : ℕ}
    (hQP : TauCeti.IsQuadraticallyPresented (O⟦X⟧ ⧸ towerIdeal p O n)
      (M ⧸ (towerIdeal p O n • (⊤ : Submodule O⟦X⟧ M)))) :
    letI : Algebra O⟦X⟧ S⟦X⟧ := (PowerSeries.map φ).toAlgebra
    TauCeti.IsQuadraticallyPresented (S⟦X⟧ ⧸ towerIdeal p S n)
      ((S⟦X⟧ ⊗[O⟦X⟧] M) ⧸ (towerIdeal p S n • (⊤ : Submodule S⟦X⟧ (S⟦X⟧ ⊗[O⟦X⟧] M)))) := by
  let : Algebra O⟦X⟧ S⟦X⟧ := (PowerSeries.map φ).toAlgebra
  set I := towerIdeal p O n
  set I' := towerIdeal p S n
  let Φ : O⟦X⟧ →+* S⟦X⟧ := PowerSeries.map φ
  -- Descend `mk I' ∘ Φ` to a ring homomorphism `O⟦X⟧ ⧸ I →+* S⟦X⟧ ⧸ I'`.
  have hle : I ≤ RingHom.ker ((Ideal.Quotient.mk I').comp Φ) := by
    dsimp only [I]
    rw [towerIdeal, Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    have hmap : Φ ((1 + X : O⟦X⟧) ^ p ^ n - 1) = (1 + X : S⟦X⟧) ^ p ^ n - 1 := by simp [Φ]
    rw [hmap]
    exact Ideal.mem_span_singleton_self _
  let ψ : (O⟦X⟧ ⧸ I) →+* (S⟦X⟧ ⧸ I') := Ideal.Quotient.lift I ((Ideal.Quotient.mk I').comp Φ) hle
  let : Algebra (O⟦X⟧ ⧸ I) (S⟦X⟧ ⧸ I') := ψ.toAlgebra
  have : IsScalarTower O⟦X⟧ (O⟦X⟧ ⧸ I) (S⟦X⟧ ⧸ I') :=
    ⟨fun f x y ↦ by
      obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective y
      change Ideal.Quotient.mk I' (Φ (f * g)) * Ideal.Quotient.mk I' h =
        Ideal.Quotient.mk I' (Φ f * (Φ g * h))
      rw [← map_mul (Ideal.Quotient.mk I'), map_mul Φ, mul_assoc]⟩
  -- Base-change `hQP` along `ψ`, cancel both base changes, and identify with the module quotient.
  have h1 : TauCeti.IsQuadraticallyPresented (O⟦X⟧ ⧸ I) ((O⟦X⟧ ⧸ I) ⊗[O⟦X⟧] M) :=
    hQP.of_equiv (TauCeti.quotTensorEquivQuotSMulQuot I).symm
  have h2 : TauCeti.IsQuadraticallyPresented (S⟦X⟧ ⧸ I')
      ((S⟦X⟧ ⧸ I') ⊗[O⟦X⟧ ⧸ I] ((O⟦X⟧ ⧸ I) ⊗[O⟦X⟧] M)) :=
    h1.baseChange (S⟦X⟧ ⧸ I')
  have h3 : TauCeti.IsQuadraticallyPresented (S⟦X⟧ ⧸ I') ((S⟦X⟧ ⧸ I') ⊗[O⟦X⟧] M) :=
    h2.of_equiv (AlgebraTensorModule.cancelBaseChange O⟦X⟧ (O⟦X⟧ ⧸ I) (S⟦X⟧ ⧸ I') (S⟦X⟧ ⧸ I') M)
  have h4 : TauCeti.IsQuadraticallyPresented (S⟦X⟧ ⧸ I')
      ((S⟦X⟧ ⧸ I') ⊗[S⟦X⟧] (S⟦X⟧ ⊗[O⟦X⟧] M)) :=
    h3.of_equiv (AlgebraTensorModule.cancelBaseChange O⟦X⟧ S⟦X⟧ (S⟦X⟧ ⧸ I') (S⟦X⟧ ⧸ I') M).symm
  exact h4.of_equiv (TauCeti.quotTensorEquivQuotSMulQuot I')

variable [Fact p.Prime] {O : Type*} [CommRing O] [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O]

/-- **Minimal square presentation over a local finite `ℤ_[p]`-algebra.** If `O` is local and a
finite `O⟦X⟧`-module `M` has quadratically presented tower quotients `M ⧸ I_n M` for cofinally
large `n`, then `M` admits a minimal square presentation `Rʳ →B Rʳ →π M → 0` of size
`r = dim_κ (κ ⊗ M)`. -/
theorem controlledSquarePresentation_local_minimal [IsLocalRing O] {M : Type*} [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]
    (hcof : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      TauCeti.IsQuadraticallyPresented (O⟦X⟧ ⧸ towerIdeal p O n)
        (M ⧸ (towerIdeal p O n • (⊤ : Submodule O⟦X⟧ M)))) :
    ∃ (π : (Fin (Module.finrank (ResidueField O⟦X⟧)
        (ResidueField O⟦X⟧ ⊗[O⟦X⟧] M)) → O⟦X⟧) →ₗ[O⟦X⟧] M)
      (B : Matrix (Fin (Module.finrank (ResidueField O⟦X⟧) (ResidueField O⟦X⟧ ⊗[O⟦X⟧] M)))
        (Fin (Module.finrank (ResidueField O⟦X⟧) (ResidueField O⟦X⟧ ⊗[O⟦X⟧] M))) O⟦X⟧),
      Function.Surjective π ∧
      LinearMap.ker π ≤ maximalIdeal O⟦X⟧ • (⊤ : Submodule O⟦X⟧ _) ∧
      LinearMap.range (Matrix.toLin' B) = LinearMap.ker π := by
  have : IsNoetherianRing O⟦X⟧ := isNoetherianRing_powerSeries ℤ_[p] O
  have hp_mem : (p : O) ∈ maximalIdeal O := by
    have h := natCast_prime_mem_jacobson (p := p) (O := O)
    rwa [ringJacobson_eq_maximalIdeal] at h
  refine TauCeti.exists_minimalSquarePresentation_of_cofinal_quotientSMulTop
    (I := towerIdeal p O) fun N ↦ ?_
  obtain ⟨n, hn, hQP⟩ := hcof N
  exact ⟨n, (towerIdeal_le_maximalIdeal_pow hp_mem n).trans
    (Ideal.pow_le_pow_right (hn.trans (Nat.le_succ n))), hQP⟩

/-- **Lifting a quadratic presentation over a local finite `ℤ_[p]`-algebra.** -/
theorem controlledSquarePresentation_of_isLocalRing [IsLocalRing O] {M : Type*} [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]
    (hcof : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      TauCeti.IsQuadraticallyPresented (O⟦X⟧ ⧸ towerIdeal p O n)
        (M ⧸ (towerIdeal p O n • (⊤ : Submodule O⟦X⟧ M)))) :
    TauCeti.IsQuadraticallyPresented O⟦X⟧ M := by
  obtain ⟨π, B, hπ, _, hrange⟩ := controlledSquarePresentation_local_minimal (p := p) hcof
  exact TauCeti.IsQuadraticallyPresented.of_exact (Pi.basisFun O⟦X⟧ _) (Pi.basisFun O⟦X⟧ _)
    (LinearMap.exact_iff.2 hrange.symm) hπ

/-- **Lifting a quadratic presentation over any commutative finite `ℤ_[p]`-algebra (cofinal form).**
Let `O` be a commutative module-finite `ℤ_[p]`-algebra (not necessarily local, free, or reduced)
and `M` a finite `O⟦X⟧`-module. If `M ⧸ I_n M` is quadratically presented over `O⟦X⟧ ⧸ I_n` for
cofinally many `n` (with no compatibility assumption on the finite presentation sizes or bases),
then `M` is quadratically presented over `O⟦X⟧`. -/
theorem controlledSquarePresentation_cofinal {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M]
    [Module.Finite O⟦X⟧ M]
    (hcof : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      TauCeti.IsQuadraticallyPresented (O⟦X⟧ ⧸ towerIdeal p O n)
        (M ⧸ (towerIdeal p O n • (⊤ : Submodule O⟦X⟧ M)))) :
    TauCeti.IsQuadraticallyPresented O⟦X⟧ M := by
  -- `O` is finite over the Henselian local ring `ℤ_[p]`, hence semiperfect.
  have : TauCeti.IsSemiperfectRing O := TauCeti.IsSemiperfectRing.of_henselianRing ℤ_[p] O
  obtain ⟨m, e, he, hloc⟩ :=
    TauCeti.IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_quotient O
  have heC : CompleteOrthogonalIdempotents (C ∘ e) := he.map C
  refine TauCeti.IsQuadraticallyPresented.of_completeOrthogonalIdempotents heC fun i ↦ ?_
  -- Identify `O⟦X⟧ ⧸ (1 - C (e i))` with `(O ⧸ (1 - e i))⟦X⟧`, a power series ring over a local
  -- finite `ℤ_[p]`-algebra.
  let Oᵢ := O ⧸ Ideal.span {1 - e i}
  let qᵢ : O →+* Oᵢ := Ideal.Quotient.mk (Ideal.span {1 - e i})
  have : IsLocalRing Oᵢ := hloc i
  have : Module.Finite ℤ_[p] Oᵢ :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] _).toLinearMap
      Ideal.Quotient.mk_surjective
  let : Algebra O⟦X⟧ Oᵢ⟦X⟧ := (PowerSeries.map qᵢ).toAlgebra
  have hQP_local : TauCeti.IsQuadraticallyPresented Oᵢ⟦X⟧ (Oᵢ⟦X⟧ ⊗[O⟦X⟧] M) := by
    refine controlledSquarePresentation_of_isLocalRing (p := p) (O := Oᵢ) fun N ↦ ?_
    obtain ⟨n, hn, hQP⟩ := hcof N
    exact ⟨n, hn, isQuadraticallyPresented_towerQuotient_baseChange qᵢ hQP⟩
  -- Transport along the ring isomorphism `Oᵢ⟦X⟧ ≃+* O⟦X⟧ ⧸ (1 - C (e i))`.
  let Rᵢ := O⟦X⟧ ⧸ Ideal.span {1 - (C ∘ e) i}
  have hspan : Ideal.span {1 - (C ∘ e) i} = Ideal.span {C (1 - e i)} := by
    simp [Function.comp_apply, map_sub, map_one]
  let eqR : Rᵢ ≃+* Oᵢ⟦X⟧ :=
    (Ideal.quotEquivOfEq hspan).trans (PowerSeries.quotientSpanCRingEquiv (1 - e i))
  let : Algebra Oᵢ⟦X⟧ Rᵢ := eqR.symm.toRingHom.toAlgebra
  have : IsScalarTower O⟦X⟧ Oᵢ⟦X⟧ Rᵢ :=
    IsScalarTower.of_algebraMap_eq fun f ↦ eqR.injective <| by
      change eqR (Ideal.Quotient.mk _ f) = eqR (eqR.symm (PowerSeries.map qᵢ f))
      rw [eqR.apply_symm_apply]
      dsimp only [eqR, RingEquiv.trans_apply]
      rw [Ideal.quotEquivOfEq_mk]
      exact PowerSeries.quotientSpanCRingEquiv_mk (1 - e i) f
  exact (hQP_local.baseChange Rᵢ).of_equiv
    (AlgebraTensorModule.cancelBaseChange O⟦X⟧ Oᵢ⟦X⟧ Rᵢ Rᵢ M)

/-- **Lifting a quadratic presentation over any commutative finite `ℤ_[p]`-algebra.** If `M ⧸ I_n M`
is quadratically presented over `O⟦X⟧ ⧸ I_n` for all sufficiently large `n`, then `M` is
quadratically presented over `O⟦X⟧`. -/
theorem controlledSquarePresentation {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M]
    [Module.Finite O⟦X⟧ M]
    (h : ∃ N₀ : ℕ, ∀ n ≥ N₀,
      TauCeti.IsQuadraticallyPresented (O⟦X⟧ ⧸ towerIdeal p O n)
        (M ⧸ (towerIdeal p O n • (⊤ : Submodule O⟦X⟧ M)))) :
    TauCeti.IsQuadraticallyPresented O⟦X⟧ M := by
  obtain ⟨N₀, hN₀⟩ := h
  exact controlledSquarePresentation_cofinal (p := p) fun N ↦
    ⟨max N₀ N, le_max_right _ _, hN₀ _ (le_max_left _ _)⟩

/-- **Componentwise projective square presentation retaining locally constant ranks.** Under the
cofinal tower-quotient hypothesis, decomposing `O` via a complete orthogonal idempotent family
into local factors yields a finite projective square presentation `P →Φ P →g M → 0` whose
component ranks `rᵢ` are the minimal numbers of generators on each local factor. -/
theorem controlledSquarePresentation_projective_cofinal {M : Type*} [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]
    (hcof : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      TauCeti.IsQuadraticallyPresented (O⟦X⟧ ⧸ towerIdeal p O n)
        (M ⧸ (towerIdeal p O n • (⊤ : Submodule O⟦X⟧ M)))) :
    ∃ (m : ℕ) (e : Fin m → O) (_ : CompleteOrthogonalIdempotents e) (r : Fin m → ℕ),
      let P := ∀ i : Fin m, Fin (r i) → (O⟦X⟧ ⧸ Ideal.span {1 - C (e i)})
      Module.Finite O⟦X⟧ P ∧ Module.Projective O⟦X⟧ P ∧
      ∃ (Φ : P →ₗ[O⟦X⟧] P) (g : P →ₗ[O⟦X⟧] M),
        Function.Surjective g ∧ LinearMap.range Φ = LinearMap.ker g := by
  have : TauCeti.IsSemiperfectRing O := TauCeti.IsSemiperfectRing.of_henselianRing ℤ_[p] O
  obtain ⟨m, e, he, hloc⟩ :=
    TauCeti.IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_quotient O
  have heC : CompleteOrthogonalIdempotents (C ∘ e) := he.map C
  have hcomp : ∀ i : Fin m,
      ∃ (rᵢ : ℕ)
        (A : Matrix (Fin rᵢ) (Fin rᵢ) (O⟦X⟧ ⧸ Ideal.span {1 - (C ∘ e) i}))
        (π : (Fin rᵢ → O⟦X⟧ ⧸ Ideal.span {1 - (C ∘ e) i}) →ₗ[O⟦X⟧ ⧸ Ideal.span {1 - (C ∘ e) i}]
          ((O⟦X⟧ ⧸ Ideal.span {1 - (C ∘ e) i}) ⊗[O⟦X⟧] M)),
        Function.Surjective π ∧ LinearMap.range (Matrix.toLin' A) = LinearMap.ker π := by
    intro i
    let Oᵢ := O ⧸ Ideal.span {1 - e i}
    let qᵢ : O →+* Oᵢ := Ideal.Quotient.mk (Ideal.span {1 - e i})
    have : IsLocalRing Oᵢ := hloc i
    have : Module.Finite ℤ_[p] Oᵢ :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] _).toLinearMap
        Ideal.Quotient.mk_surjective
    let : Algebra O⟦X⟧ Oᵢ⟦X⟧ := (PowerSeries.map qᵢ).toAlgebra
    obtain ⟨πᵢ, Bᵢ, hπᵢ, _, hrangeᵢ⟩ :=
      controlledSquarePresentation_local_minimal (p := p) (O := Oᵢ) (M := Oᵢ⟦X⟧ ⊗[O⟦X⟧] M)
        fun N ↦ by
          obtain ⟨n, hn, hQP⟩ := hcof N
          exact ⟨n, hn, isQuadraticallyPresented_towerQuotient_baseChange qᵢ hQP⟩
    -- Transport the minimal local presentation along `eqR : Rᵢ ≃+* Oᵢ⟦X⟧`.
    let Rᵢ := O⟦X⟧ ⧸ Ideal.span {1 - (C ∘ e) i}
    have hspan : Ideal.span {1 - (C ∘ e) i} = Ideal.span {C (1 - e i)} := by
      simp [Function.comp_apply, map_sub, map_one]
    let eqR : Rᵢ ≃+* Oᵢ⟦X⟧ :=
      (Ideal.quotEquivOfEq hspan).trans (PowerSeries.quotientSpanCRingEquiv (1 - e i))
    let : Algebra Oᵢ⟦X⟧ Rᵢ := eqR.symm.toRingHom.toAlgebra
    have : IsScalarTower O⟦X⟧ Oᵢ⟦X⟧ Rᵢ :=
      IsScalarTower.of_algebraMap_eq fun f ↦ eqR.injective <| by
        change eqR (Ideal.Quotient.mk _ f) = eqR (eqR.symm (PowerSeries.map qᵢ f))
        rw [eqR.apply_symm_apply]
        dsimp only [eqR, RingEquiv.trans_apply]
        rw [Ideal.quotEquivOfEq_mk]
        exact PowerSeries.quotientSpanCRingEquiv_mk (1 - e i) f
    let eMod : (Rᵢ ⊗[Oᵢ⟦X⟧] (Oᵢ⟦X⟧ ⊗[O⟦X⟧] M)) ≃ₗ[Rᵢ] (Rᵢ ⊗[O⟦X⟧] M) :=
      AlgebraTensorModule.cancelBaseChange O⟦X⟧ Oᵢ⟦X⟧ Rᵢ Rᵢ M
    set rᵢ := Module.finrank (ResidueField Oᵢ⟦X⟧) (ResidueField Oᵢ⟦X⟧ ⊗[Oᵢ⟦X⟧] (Oᵢ⟦X⟧ ⊗[O⟦X⟧] M))
    rcases Nat.eq_zero_or_pos rᵢ with hr0 | hrpos
    · have hsubM : Subsingleton (Oᵢ⟦X⟧ ⊗[O⟦X⟧] M) := by
        refine subsingleton_of_forall_eq 0 fun x ↦ ?_
        obtain ⟨v, rfl⟩ := hπᵢ x
        have hv : v = 0 := funext fun j ↦ (Fin.cast hr0 j).elim0
        rw [hv, map_zero]
      have hsub : Subsingleton (Rᵢ ⊗[O⟦X⟧] M) := eMod.symm.injective.subsingleton
      refine ⟨0, 0, 0, fun x ↦ ⟨0, Subsingleton.elim _ _⟩, ?_⟩
      ext v
      exact ⟨fun _ ↦ by simp [Subsingleton.elim v 0], fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
    · let Pᵢ : TauCeti.QuadraticPresentation Oᵢ⟦X⟧ (Oᵢ⟦X⟧ ⊗[O⟦X⟧] M) :=
        TauCeti.QuadraticPresentation.ofExact hrpos (Pi.basisFun Oᵢ⟦X⟧ (Fin rᵢ))
          (Pi.basisFun Oᵢ⟦X⟧ (Fin rᵢ)) (LinearMap.exact_iff.2 hrangeᵢ.symm) hπᵢ
      let Qᵢ : TauCeti.QuadraticPresentation Rᵢ (Rᵢ ⊗[Oᵢ⟦X⟧] (Oᵢ⟦X⟧ ⊗[O⟦X⟧] M)) :=
        Pᵢ.baseChange Rᵢ
      have hker : LinearMap.ker (eMod.toLinearMap ∘ₗ Qᵢ.gen) = LinearMap.ker Qᵢ.gen :=
        LinearMap.ker_comp_of_ker_eq_bot _ eMod.ker
      exact ⟨Qᵢ.size, Qᵢ.rel, eMod.toLinearMap ∘ₗ Qᵢ.gen,
        eMod.surjective.comp Qᵢ.gen_surjective, Qᵢ.range_rel_eq_ker.trans hker.symm⟩
  choose r A π hπ hrange using hcomp
  refine ⟨m, e, he, r, ?_⟩
  exact TauCeti.exists_projectiveSquarePresentation_of_completeOrthogonalIdempotents heC r
    fun i ↦ ⟨A i, π i, hπ i, hrange i⟩

/-- **Determinant Fitting identity for lifted square presentations.** Under the cofinal
tower-quotient hypothesis, `M` admits a quadratic presentation `P` over `O⟦X⟧` with
`Fitt₀(M) = (det P.rel)`. -/
theorem controlledSquare_detFitting {M : Type*} [AddCommGroup M] [Module O⟦X⟧ M]
    [Module.Finite O⟦X⟧ M]
    (hcof : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      TauCeti.IsQuadraticallyPresented (O⟦X⟧ ⧸ towerIdeal p O n)
        (M ⧸ (towerIdeal p O n • (⊤ : Submodule O⟦X⟧ M)))) :
    ∃ P : TauCeti.QuadraticPresentation O⟦X⟧ M,
      fittingIdeal O⟦X⟧ M 0 = Ideal.span {P.rel.det} := by
  obtain ⟨P⟩ := (controlledSquarePresentation_cofinal (p := p) hcof).nonempty
  exact ⟨P, P.fittingIdeal_eq⟩

/-- **Lifting square presentations over a finite product of coefficient orders.** -/
theorem controlledSquarePresentation_pi {ι : Type*} [Finite ι] {O : ι → Type*}
    [∀ i, CommRing (O i)] [∀ i, Algebra ℤ_[p] (O i)] [∀ i, Module.Finite ℤ_[p] (O i)]
    {M : Type*} [AddCommGroup M] [Module (∀ i, (O i)⟦X⟧) M] [Module.Finite (∀ i, (O i)⟦X⟧) M]
    (hcomp : ∀ i,
      letI : Algebra (∀ j, (O j)⟦X⟧) (O i)⟦X⟧ := (Pi.evalRingHom (fun j ↦ (O j)⟦X⟧) i).toAlgebra
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        TauCeti.IsQuadraticallyPresented ((O i)⟦X⟧ ⧸ towerIdeal p (O i) n)
          (((O i)⟦X⟧ ⊗[∀ j, (O j)⟦X⟧] M) ⧸
            (towerIdeal p (O i) n •
              (⊤ : Submodule (O i)⟦X⟧ ((O i)⟦X⟧ ⊗[∀ j, (O j)⟦X⟧] M))))) :
    TauCeti.IsQuadraticallyPresented (∀ i, (O i)⟦X⟧) M := by
  refine TauCeti.IsQuadraticallyPresented.of_pi fun i ↦ ?_
  let : Algebra (∀ j, (O j)⟦X⟧) (O i)⟦X⟧ := (Pi.evalRingHom (fun j ↦ (O j)⟦X⟧) i).toAlgebra
  exact controlledSquarePresentation_cofinal (p := p) (O := O i) (hcomp i)

end SquarePresentationLift

section ProjectiveDimension

universe u

/-- **Regular Fitting element implies injectivity and `pd ≤ 1` for lifted presentations.** Under
the cofinal tower-quotient hypothesis over a commutative module-finite `ℤ_[p]`-algebra `O`, if
`Fitt₀(M)` contains a non-zero-divisor of `O⟦X⟧` (for instance `Fitt₀(M) = (d)` with
`d ∈ nonZeroDivisors O⟦X⟧`), then `M` has projective dimension at most one and admits a quadratic
presentation `P` with `Fitt₀(M) = (det P.rel)`, regular determinant, and injective relation map. -/
theorem controlledSquare_hasProjectiveDimensionLE_one {p : ℕ} [Fact p.Prime] {O : Type u}
    [CommRing O] [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] {M : Type u} [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]
    (hcof : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      TauCeti.IsQuadraticallyPresented (O⟦X⟧ ⧸ towerIdeal p O n)
        (M ⧸ (towerIdeal p O n • (⊤ : Submodule O⟦X⟧ M))))
    {d : O⟦X⟧} (hd : d ∈ fittingIdeal O⟦X⟧ M 0) (hreg : d ∈ nonZeroDivisors O⟦X⟧) :
    HasProjectiveDimensionLE (ModuleCat.of O⟦X⟧ M) 1 ∧
    ∃ P : TauCeti.QuadraticPresentation O⟦X⟧ M,
      fittingIdeal O⟦X⟧ M 0 = Ideal.span {P.rel.det} ∧
      P.rel.det ∈ nonZeroDivisors O⟦X⟧ ∧
      Function.Injective (Matrix.toLin' P.rel) := by
  obtain ⟨P⟩ := (controlledSquarePresentation_cofinal (p := p) hcof).nonempty
  have hdet : P.rel.det ∈ nonZeroDivisors O⟦X⟧ :=
    P.det_mem_nonZeroDivisors_of_mem_fittingIdeal hd hreg
  exact ⟨P.hasProjectiveDimensionLE_one_of_det_mem_nonZeroDivisors hdet,
    P, P.fittingIdeal_eq, hdet, P.injective_toLin'_of_det_mem_nonZeroDivisors hdet⟩

end ProjectiveDimension

section Examples

/-! ### Edge-case sanity checks -/

-- Check 1: `J_{1,0} = (2, X) ≠ (X)` over `ℤ_[2]`, while `J_{0,n} = ⊤`.
example : C (2 : ℤ_[2]) ∈ jointIdeal 2 ℤ_[2] 1 0 ∧
    C (2 : ℤ_[2]) ∉ Ideal.span {(X : ℤ_[2]⟦X⟧)} ∧
    jointIdeal 2 ℤ_[2] 1 0 ≠ Ideal.span {(X : ℤ_[2]⟦X⟧)} ∧
    jointIdeal 2 ℤ_[2] 0 3 = ⊤ := by
  have hmem : C (2 : ℤ_[2]) ∈ jointIdeal 2 ℤ_[2] 1 0 := by
    rw [jointIdeal_one_zero]
    exact Ideal.subset_span (by simp)
  have hnotmem : C (2 : ℤ_[2]) ∉ Ideal.span {(X : ℤ_[2]⟦X⟧)} := by
    rw [Ideal.mem_span_singleton]
    rintro ⟨g, hg⟩
    have hc := congrArg constantCoeff hg
    simp only [constantCoeff_C, map_mul, constantCoeff_X, zero_mul] at hc
    exact two_ne_zero hc
  exact ⟨hmem, hnotmem, fun h ↦ hnotmem (h ▸ hmem), jointIdeal_zero_left 2 ℤ_[2] 3⟩

-- Check 2: Over `ℤ_[2]`, `ω₁ = (1 + X)^2 - 1 = 2 * X + X ^ 2 ≠ X ^ 2`.
example : (1 + X : ℤ_[2]⟦X⟧) ^ 2 ^ 1 - 1 = 2 * X + X ^ 2 ∧
    (1 + X : ℤ_[2]⟦X⟧) ^ 2 ^ 1 - 1 ≠ X ^ 2 := by
  have heq : (1 + X : ℤ_[2]⟦X⟧) ^ 2 ^ 1 - 1 = 2 * X + X ^ 2 := by ring
  refine ⟨heq, fun h ↦ ?_⟩
  have h1 := congrArg (coeff 1) (heq.symm.trans h)
  have hC : (2 : ℤ_[2]⟦X⟧) = C (2 : ℤ_[2]) := (map_ofNat C 2).symm
  rw [map_add, hC, coeff_C_mul, coeff_X_pow] at h1
  norm_num at h1

-- Check 3: `(2, X) ≠ ⊤` in `ℤ_[2]⟦X⟧`, detected by `J_{1,0}`.
example : Ideal.span {C (2 : ℤ_[2]), (X : ℤ_[2]⟦X⟧)} ≠ ⊤ := by
  intro h
  have h1 : (1 : ℤ_[2]⟦X⟧) ∈ Ideal.span {C (2 : ℤ_[2]), (X : ℤ_[2]⟦X⟧)} := h ▸ Submodule.mem_top
  have hle : Ideal.span {C (2 : ℤ_[2]), (X : ℤ_[2]⟦X⟧)} ≤ maximalIdeal ℤ_[2]⟦X⟧ := by
    have h2 : (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) := by norm_num
    rw [h2, ← jointIdeal_one_zero]
    have hp : ((2 : ℕ) : ℤ_[2]) ∈ maximalIdeal ℤ_[2] := by
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    simpa only [pow_one] using jointIdeal_le_maximalIdeal_pow hp (a := 1) (n := 0) le_rfl le_rfl
  exact (maximalIdeal.isMaximal ℤ_[2]⟦X⟧).ne_top ((Ideal.eq_top_iff_one _).mpr (hle h1))

-- Check 4: `M = 0` (`Subsingleton`) has `Fitt₀ = ⊤` and determinant `1`; `M = R` has `Fitt₀ = ⊥`
-- and a `1 × 1` zero presentation.
example {O : Type*} [CommRing O] :
    fittingIdeal O⟦X⟧ Unit 0 = ⊤ ∧
    (TauCeti.QuadraticPresentation.ofSubsingleton (R := O⟦X⟧) (N := Unit)).rel.det = 1 ∧
    fittingIdeal O⟦X⟧ O⟦X⟧ 0 = ⊥ ∧
    (TauCeti.QuadraticPresentation.ofBasis (R := O⟦X⟧) one_pos
      (Pi.basisFun O⟦X⟧ (Fin 1))).rel.det = 0 := by
  have h1 : (TauCeti.QuadraticPresentation.ofSubsingleton (R := O⟦X⟧) (N := Unit)).rel.det = 1 :=
    Matrix.det_one (n := Fin 1)
  have h0 : (TauCeti.QuadraticPresentation.ofBasis (R := O⟦X⟧) one_pos
      (Pi.basisFun O⟦X⟧ (Fin 1))).rel.det = 0 :=
    Matrix.det_zero (n := Fin 1)
  refine ⟨?_, h1, ?_, h0⟩
  · have hP :=
      (TauCeti.QuadraticPresentation.ofSubsingleton (R := O⟦X⟧) (N := Unit)).fittingIdeal_eq
    rw [hP, h1, Ideal.span_singleton_one]
  · have hP := (TauCeti.QuadraticPresentation.ofBasis (R := O⟦X⟧) one_pos
      (Module.Basis.singleton (Fin 1) O⟦X⟧)).fittingIdeal_eq
    have h0' : (TauCeti.QuadraticPresentation.ofBasis (R := O⟦X⟧) one_pos
        (Module.Basis.singleton (Fin 1) O⟦X⟧)).rel.det = 0 :=
      Matrix.det_zero (n := Fin 1)
    rw [hP, h0', Ideal.span_singleton_zero]

-- Check 5: `ℤ₂[C₂]` is a commutative finite `ℤ_[2]`-algebra to which `controlledFitting_continuity`
-- and `controlledSquarePresentation` apply directly.
example : Module.Finite ℤ_[2] (MonoidAlgebra ℤ_[2] (Multiplicative (ZMod 2))) :=
  Module.Finite.of_basis (MonoidAlgebra.basis (Multiplicative (ZMod 2)) ℤ_[2])

-- Check 6: Over the nonreduced finite free `ℤ_[2]`-algebra `DualNumber ℤ_[2]`, `ε ≠ 0` yet
-- `C ε ∉ nonZeroDivisors (DualNumber ℤ_[2])⟦X⟧`.
example : (C (DualNumber.eps : DualNumber ℤ_[2]) : (DualNumber ℤ_[2])⟦X⟧) ≠ 0 ∧
    (C (DualNumber.eps : DualNumber ℤ_[2]) : (DualNumber ℤ_[2])⟦X⟧) ∉
      nonZeroDivisors (DualNumber ℤ_[2])⟦X⟧ := by
  have hne : (DualNumber.eps : DualNumber ℤ_[2]) ≠ 0 := by
    intro h
    have := congrArg TrivSqZeroExt.snd h
    simp at this
  refine ⟨fun h ↦ hne (C_injective (by simpa using h)), fun hreg ↦ ?_⟩
  have hmul : C (DualNumber.eps : DualNumber ℤ_[2]) *
      C (DualNumber.eps : DualNumber ℤ_[2]) = 0 := by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  have h0 : (C (DualNumber.eps : DualNumber ℤ_[2]) : (DualNumber ℤ_[2])⟦X⟧) = 0 :=
    (mem_nonZeroDivisors_iff.mp hreg).1 _ hmul
  exact hne (C_injective (by simpa using h0))

end Examples

end TauCeti.Iwasawa

