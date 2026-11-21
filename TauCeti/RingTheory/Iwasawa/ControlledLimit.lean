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
  exact Ideal.pow_le_pow_right ha (Ideal.pow_mem_pow (by simpa using hI) a)

/-- Over a local ring with `p ∈ 𝔪_O`, `J_{a,n} ≤ 𝔪_{O⟦X⟧} ^ N` whenever `N ≤ a` and `N ≤ n + 1`. -/
theorem jointIdeal_le_maximalIdeal_pow [IsLocalRing O] (hp : (p : O) ∈ maximalIdeal O)
    {a n N : ℕ} (ha : N ≤ a) (hn : N ≤ n + 1) :
    jointIdeal p O a n ≤ maximalIdeal O⟦X⟧ ^ N := by
  rw [TauCeti.PowerSeries.maximalIdeal_eq_comap_constantCoeff]
  exact jointIdeal_le_comap_constantCoeff_pow hp ha hn

/-- For a prime `p`, the binomial expansion gives `(1 + X) ^ pⁿ - 1 - X ^ pⁿ ∈ (C p)`. -/
theorem one_add_X_pow_sub_one_sub_X_pow_mem_span_C (hp : p.Prime) (n : ℕ) :
    (1 + X : O⟦X⟧) ^ p ^ n - 1 - X ^ p ^ n ∈ Ideal.span {C (p : O)} := by
  have hsplit : (1 + X : O⟦X⟧) ^ p ^ n - 1 - X ^ p ^ n =
      ∑ k ∈ Finset.range (p ^ n - 1), X ^ (k + 1) * ((p ^ n).choose (k + 1) : O⟦X⟧) := by
    have hsum : (1 + X : O⟦X⟧) ^ p ^ n =
        (1 + ∑ k ∈ Finset.range (p ^ n - 1), X ^ (k + 1) * ((p ^ n).choose (k + 1) : O⟦X⟧)) +
          X ^ p ^ n := by
      rw [add_comm, add_pow, Finset.sum_range_succ, Nat.choose_self]
      have hbody : ∑ k ∈ Finset.range (p ^ n), X ^ k * 1 ^ (p ^ n - k) * ((p ^ n).choose k : O⟦X⟧) =
          1 + ∑ k ∈ Finset.range (p ^ n - 1), X ^ (k + 1) * ((p ^ n).choose (k + 1) : O⟦X⟧) := by
        conv_lhs => arg 1; rw [← Nat.sub_add_cancel (pow_pos hp.pos n)]
        rw [Finset.sum_range_succ', add_comm]
        simp
      simpa using hbody
    linear_combination hsum
  rw [hsplit]
  refine Ideal.sum_mem _ fun k hk ↦ ?_
  obtain ⟨m, hm⟩ := hp.dvd_choose_pow (n := n) (Nat.succ_ne_zero k)
    (by have := Finset.mem_range.mp hk; omega)
  rw [hm, Nat.cast_mul, ← map_natCast C p, ← mul_assoc, mul_comm (X ^ (k + 1)), mul_assoc]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- For a prime `p`, the monomial `X ^ (a * pⁿ)` lies in `J_{a,n} = (p^a, (1 + X) ^ pⁿ - 1)`. -/
theorem X_pow_mul_mem_jointIdeal (hp : p.Prime) (a n : ℕ) :
    (X : O⟦X⟧) ^ (a * p ^ n) ∈ jointIdeal p O a n := by
  obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp
    (one_add_X_pow_sub_one_sub_X_pow_mem_span_C (O := O) hp n)
  set ω : O⟦X⟧ := (1 + X) ^ p ^ n - 1
  rw [mul_comm, pow_mul, show (X : O⟦X⟧) ^ p ^ n = ω + -(C (p : O) * g) by linear_combination -hg,
    add_pow]
  refine Ideal.sum_mem _ fun k _ ↦ ?_
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
      ← mul_neg, mul_pow]
    exact Ideal.mul_mem_right _ _
      (span_C_pow_le_jointIdeal p O a n (Ideal.mem_span_singleton_self _))
  · exact Ideal.mul_mem_right _ _ <| Ideal.mul_mem_right _ _ <| Ideal.pow_mem_of_mem _
      (towerIdeal_le_jointIdeal p O a n (Ideal.mem_span_singleton_self _)) k hkpos

/-- **Lower cofinality bound for `(p, X)`.** For a prime `p`,
`((p).comap constantCoeff) ^ (a + a * pⁿ) ≤ J_{a,n}`. -/
theorem comap_constantCoeff_span_pow_le_jointIdeal (hp : p.Prime) (a n : ℕ) :
    (Ideal.span {(p : O)}).comap constantCoeff ^ (a + a * p ^ n) ≤ jointIdeal p O a n := by
  intro f hf
  rw [PowerSeries.mem_comap_constantCoeff_pow_iff] at hf
  set M := a * p ^ n
  let t : O⟦X⟧ := ∑ j ∈ Finset.range M, C (coeff j f) * X ^ j
  have htail : f - t ∈ jointIdeal p O a n := by
    obtain ⟨q, hq⟩ : (X : O⟦X⟧) ^ M ∣ f - t := PowerSeries.X_pow_dvd_iff.mpr fun j hj ↦ by
      rw [map_sub, map_sum, Finset.sum_eq_single j]
      · simp
      · intro b _ hbj; simp [Ne.symm hbj]
      · simp [Finset.mem_range.mpr hj]
    exact hq ▸ Ideal.mul_mem_right q _ (X_pow_mul_mem_jointIdeal hp a n)
  have htrunc : t ∈ jointIdeal p O a n := Ideal.sum_mem _ fun j hj ↦ by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp <| Ideal.span_singleton_pow (p : O) a ▸
      Ideal.pow_le_pow_right (by have := Finset.mem_range.mp hj; omega : a ≤ a + M - j) (hf j)
    rw [hc, map_mul, map_pow, mul_assoc]
    exact Ideal.mul_mem_right _ _
      (span_C_pow_le_jointIdeal p O a n (Ideal.mem_span_singleton_self _))
  exact (show f = (f - t) + t by abel) ▸ add_mem htail htrunc

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
      rw [Nat.mul_sub]; omega
    exact pow_le_pow_left' hIk (N - j) (pow_mul I k (N - j) ▸ Ideal.pow_le_pow_right hle (hf j))

/-- Over a local ring `O` with `𝔪_O ^ k ≤ (p)` (`k > 0`), powers of `𝔪_{O⟦X⟧}` are contained in
every joint ideal `J_{a,n}`. -/
theorem maximalIdeal_pow_le_jointIdeal_of_pow_le [IsLocalRing O] (hp : p.Prime) {k : ℕ}
    (hk : 0 < k) (hmk : maximalIdeal O ^ k ≤ Ideal.span {(p : O)}) (a n : ℕ) :
    maximalIdeal O⟦X⟧ ^ (k * (a + a * p ^ n)) ≤ jointIdeal p O a n := by
  rw [TauCeti.PowerSeries.maximalIdeal_eq_comap_constantCoeff]
  exact comap_constantCoeff_pow_le_jointIdeal_of_pow_le hp hk hmk a n

private theorem natCast_prime_mem_jacobson [Fact p.Prime] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] : (p : O) ∈ Ring.jacobson O := by
  have hpZ : (p : ℤ_[p]) ∈ Ring.jacobson ℤ_[p] := by
    rw [ringJacobson_eq_maximalIdeal, PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  simpa using TauCeti.Ring.algebraMap_mem_jacobson (A := O) hpZ

/-- Over a local module-finite `ℤ_[p]`-algebra `O`, the joint ideals `J_{a,n}` are cofinal in both
directions with powers of `𝔪_{O⟦X⟧}`. -/
theorem jointIdeal_cofinal_maximalIdeal_pow [Fact p.Prime] [IsLocalRing O]
    [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O] :
    (∀ N : ℕ, ∃ a n : ℕ, 0 < a ∧ jointIdeal p O a n ≤ maximalIdeal O⟦X⟧ ^ N) ∧
    (∀ a n : ℕ, ∃ M : ℕ, maximalIdeal O⟦X⟧ ^ M ≤ jointIdeal p O a n) := by
  have hp_mem : (p : O) ∈ maximalIdeal O :=
    ringJacobson_eq_maximalIdeal O ▸ natCast_prime_mem_jacobson (p := p) (O := O)
  refine ⟨fun N ↦ ⟨max 1 N, N, lt_of_lt_of_le one_pos (le_max_left _ _),
    jointIdeal_le_maximalIdeal_pow hp_mem (le_max_right 1 N) (Nat.le_succ N)⟩, fun a n ↦ ?_⟩
  obtain ⟨k, hk, hmk⟩ := TauCeti.Ring.exists_jacobson_pow_le_map_maximalIdeal ℤ_[p] O
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast,
    ringJacobson_eq_maximalIdeal] at hmk
  exact ⟨k * (a + a * p ^ n), maximalIdeal_pow_le_jointIdeal_of_pow_le Fact.out hk hmk a n⟩

end Cofinality

section FittingContinuity

variable {p : ℕ} [Fact p.Prime] {O : Type*} [CommRing O] [Algebra ℤ_[p] O] [Module.Finite ℤ_[p] O]

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
  exact Ideal.eq_of_forall_map_quotientMk_eq (K := fun N ↦ jointIdeal p O (a N) (n N))
    (PowerSeries.jacobson_eq_comap_constantCoeff O).ge
    (fun N ↦ ⟨N, jointIdeal_le_comap_constantCoeff_pow natCast_prime_mem_jacobson (ha N)
      ((hn N).trans (Nat.le_succ (n N)))⟩) heq

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
  have hle : I ≤ RingHom.ker ((Ideal.Quotient.mk I').comp Φ) := by
    dsimp only [I, towerIdeal]
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem]
    simp [Φ, I', towerIdeal]
  let : Algebra (O⟦X⟧ ⧸ I) (S⟦X⟧ ⧸ I') :=
    (Ideal.Quotient.lift I ((Ideal.Quotient.mk I').comp Φ) hle).toAlgebra
  have : IsScalarTower O⟦X⟧ (O⟦X⟧ ⧸ I) (S⟦X⟧ ⧸ I') := ⟨fun f x y ↦ by
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk I' (Φ (f * g)) * Ideal.Quotient.mk I' h =
      Ideal.Quotient.mk I' (Φ f * (Φ g * h))
    rw [← map_mul (Ideal.Quotient.mk I'), map_mul Φ, mul_assoc]⟩
  exact (((((hQP.of_equiv (TauCeti.quotTensorEquivQuotSMulQuot I).symm).baseChange
    (S⟦X⟧ ⧸ I')).of_equiv
    (AlgebraTensorModule.cancelBaseChange O⟦X⟧ (O⟦X⟧ ⧸ I) (S⟦X⟧ ⧸ I') (S⟦X⟧ ⧸ I') M)).of_equiv
    (AlgebraTensorModule.cancelBaseChange O⟦X⟧ S⟦X⟧ (S⟦X⟧ ⧸ I') (S⟦X⟧ ⧸ I') M).symm).of_equiv
    (TauCeti.quotTensorEquivQuotSMulQuot I'))

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
  have hp_mem : (p : O) ∈ maximalIdeal O :=
    ringJacobson_eq_maximalIdeal O ▸ natCast_prime_mem_jacobson (p := p) (O := O)
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

private theorem isLocalRing_quotient_span_one_sub_C {O : Type*} [CommRing O] {e : O}
    (hloc : IsLocalRing (O ⧸ Ideal.span {1 - e})) :
    IsLocalRing (O⟦X⟧ ⧸ Ideal.span {1 - C e}) := by
  have hspan : Ideal.span {1 - C e} = Ideal.span {C (1 - e)} := by simp [map_sub, map_one]
  exact ((Ideal.quotEquivOfEq hspan).trans
    (PowerSeries.quotientSpanCRingEquiv (1 - e))).symm.isLocalRing

private theorem finrank_residueField_tensorProduct_eq_of_minimalCover {A N : Type*}
    [CommRing A] [IsLocalRing A] [AddCommGroup N] [Module A N] {r : ℕ}
    (π : (Fin r → A) →ₗ[A] N) (hπ : Function.Surjective π)
    (hmin : LinearMap.ker π ≤ maximalIdeal A • (⊤ : Submodule A (Fin r → A))) :
    Module.finrank (ResidueField A) (ResidueField A ⊗[A] N) = r := by
  let κ := ResidueField A
  let b : Fin r → κ ⊗[A] N := fun j ↦ 1 ⊗ₜ[A] π (Pi.single j 1)
  have hspan : Submodule.span κ (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    refine TensorProduct.inductionOn y (fun c n ↦ ?_) fun _ _ hx hy ↦ add_mem hx hy
    obtain ⟨x, rfl⟩ := hπ n
    have hx : x = ∑ j : Fin r, x j • Pi.single j (1 : A) := by
      ext l; simp [Finset.sum_apply, Pi.single_apply]
    have hcm : c ⊗ₜ[A] π x = ∑ j : Fin r, (c * residue A (x j)) • b j := by
      conv_lhs => rw [hx, map_sum]
      simp only [map_smul, TensorProduct.tmul_sum, b]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        Algebra.smul_def, IsLocalRing.ResidueField.algebraMap_eq, mul_comm]
    rw [hcm]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hli : LinearIndependent κ b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    choose x hx using fun i ↦ IsLocalRing.residue_surjective (c i)
    have htmul : (1 : κ) ⊗ₜ[A] π x = 0 := by
      have hx' : x = ∑ i : Fin r, x i • Pi.single i (1 : A) := by
        ext l; simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [hx', map_sum]
      simp only [map_smul, TensorProduct.tmul_sum]
      rw [← hc]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      dsimp only [b]
      rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul', Algebra.smul_def,
        IsLocalRing.ResidueField.algebraMap_eq, smul_eq_mul, mul_one, mul_one, hx i]
    have hmem : π x ∈ maximalIdeal A • (⊤ : Submodule A N) := by
      have h0 := congrArg (TauCeti.quotTensorEquivQuotSMulQuot (maximalIdeal A))
        (show (1 : A ⧸ maximalIdeal A) ⊗ₜ[A] π x = 0 from htmul)
      rw [TauCeti.quotTensorEquivQuotSMulQuot_one_tmul, map_zero,
        Submodule.Quotient.mk_eq_zero] at h0
      exact h0
    have hmem' : π x ∈ (maximalIdeal A • (⊤ : Submodule A (Fin r → A))).map π := by
      rwa [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr hπ]
    obtain ⟨w, hw, hwx⟩ := hmem'
    have hx_mem : x ∈ maximalIdeal A • (⊤ : Submodule A (Fin r → A)) := by
      rw [show x = w + (x - w) by abel]
      exact add_mem hw (hmin (by rw [LinearMap.mem_ker, map_sub, hwx, sub_self]))
    have hxj : x j ∈ maximalIdeal A := by
      refine Submodule.smul_induction_on hx_mem (fun a ha y _ ↦ ?_) fun _ _ hy hz ↦ ?_
      · exact (maximalIdeal A).mul_mem_right (y j) ha
      · exact (maximalIdeal A).add_mem hy hz
    rw [← hx j, IsLocalRing.residue_eq_zero_iff]
    exact hxj
  exact (Module.finrank_eq_card_basis (Module.Basis.mk hli hspan.ge)).trans (Fintype.card_fin r)

/-- Transport a minimal lifted square presentation from `(O ⧸ (1 - e))⟦X⟧` to
`O⟦X⟧ ⧸ (1 - C e)` for a local factor `O ⧸ (1 - e)`, preserving locality, the minimal
residue-field generator rank, and the minimal-cover kernel bound. -/
private theorem controlledSquarePresentation_local_factor {M : Type*} [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]
    (hcof : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      TauCeti.IsQuadraticallyPresented (O⟦X⟧ ⧸ towerIdeal p O n)
        (M ⧸ (towerIdeal p O n • (⊤ : Submodule O⟦X⟧ M))))
    (e : O) (hloc : IsLocalRing (O ⧸ Ideal.span {1 - e})) :
    letI : IsLocalRing (O⟦X⟧ ⧸ Ideal.span {1 - C e}) :=
      isLocalRing_quotient_span_one_sub_C hloc
    ∃ (r : ℕ),
      r = Module.finrank (ResidueField (O⟦X⟧ ⧸ Ideal.span {1 - C e}))
        (ResidueField (O⟦X⟧ ⧸ Ideal.span {1 - C e}) ⊗[O⟦X⟧ ⧸ Ideal.span {1 - C e}]
          ((O⟦X⟧ ⧸ Ideal.span {1 - C e}) ⊗[O⟦X⟧] M)) ∧
      ∃ (A : Matrix (Fin r) (Fin r) (O⟦X⟧ ⧸ Ideal.span {1 - C e}))
        (π : (Fin r → O⟦X⟧ ⧸ Ideal.span {1 - C e}) →ₗ[O⟦X⟧ ⧸ Ideal.span {1 - C e}]
          ((O⟦X⟧ ⧸ Ideal.span {1 - C e}) ⊗[O⟦X⟧] M)),
        Function.Surjective π ∧
        LinearMap.ker π ≤ maximalIdeal (O⟦X⟧ ⧸ Ideal.span {1 - C e}) •
          (⊤ : Submodule (O⟦X⟧ ⧸ Ideal.span {1 - C e})
            (Fin r → (O⟦X⟧ ⧸ Ideal.span {1 - C e}))) ∧
        LinearMap.range (Matrix.toLin' A) = LinearMap.ker π := by
  let Oᵢ := O ⧸ Ideal.span {1 - e}
  let qᵢ : O →+* Oᵢ := Ideal.Quotient.mk (Ideal.span {1 - e})
  have : IsLocalRing Oᵢ := hloc
  have : Module.Finite ℤ_[p] Oᵢ :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] _).toLinearMap
      Ideal.Quotient.mk_surjective
  let : Algebra O⟦X⟧ Oᵢ⟦X⟧ := (PowerSeries.map qᵢ).toAlgebra
  set r := Module.finrank (ResidueField Oᵢ⟦X⟧) (ResidueField Oᵢ⟦X⟧ ⊗[Oᵢ⟦X⟧] (Oᵢ⟦X⟧ ⊗[O⟦X⟧] M))
  obtain ⟨πᵢ, Bᵢ, hπᵢ, hminᵢ, hrangeᵢ⟩ :=
    controlledSquarePresentation_local_minimal (p := p) (O := Oᵢ) (M := Oᵢ⟦X⟧ ⊗[O⟦X⟧] M)
      fun N ↦ by
        obtain ⟨n, hn, hQP⟩ := hcof N
        exact ⟨n, hn, isQuadraticallyPresented_towerQuotient_baseChange qᵢ hQP⟩
  let Rᵢ := O⟦X⟧ ⧸ Ideal.span {1 - C e}
  have hspan : Ideal.span {1 - C e} = Ideal.span {C (1 - e)} := by simp [map_sub, map_one]
  let eqR : Rᵢ ≃+* Oᵢ⟦X⟧ :=
    (Ideal.quotEquivOfEq hspan).trans (PowerSeries.quotientSpanCRingEquiv (1 - e))
  let : Algebra Oᵢ⟦X⟧ Rᵢ := eqR.symm.toRingHom.toAlgebra
  have : IsScalarTower O⟦X⟧ Oᵢ⟦X⟧ Rᵢ :=
    IsScalarTower.of_algebraMap_eq fun f ↦ eqR.injective <| by
      change eqR (Ideal.Quotient.mk _ f) = eqR (eqR.symm (PowerSeries.map qᵢ f))
      rw [eqR.apply_symm_apply]
      dsimp only [eqR, RingEquiv.trans_apply]
      rw [Ideal.quotEquivOfEq_mk, PowerSeries.quotientSpanCRingEquiv_mk]
  let eMod := AlgebraTensorModule.cancelBaseChange O⟦X⟧ Oᵢ⟦X⟧ Rᵢ Rᵢ M
  let unbase : Rᵢ ⊗[Oᵢ⟦X⟧] (Oᵢ⟦X⟧ ⊗[O⟦X⟧] M) →ₗ[Oᵢ⟦X⟧] (Oᵢ⟦X⟧ ⊗[O⟦X⟧] M) :=
    TensorProduct.lift <|
      LinearMap.mk₂ Oᵢ⟦X⟧ (fun c y ↦ eqR c • y)
        (fun _ _ _ ↦ by simp [add_smul])
        (fun a c y ↦ by
          simp [Algebra.smul_def, mul_smul, RingHom.algebraMap_toAlgebra])
        (fun _ _ _ ↦ smul_add _ _ _)
        (fun _ _ _ ↦ smul_comm _ _ _)
  have hunbase_tmul (y : Oᵢ⟦X⟧ ⊗[O⟦X⟧] M) : unbase (1 ⊗ₜ[Oᵢ⟦X⟧] y) = y := by
    simp [unbase]
  have htmul_unbase (w : Rᵢ ⊗[Oᵢ⟦X⟧] (Oᵢ⟦X⟧ ⊗[O⟦X⟧] M)) : 1 ⊗ₜ[Oᵢ⟦X⟧] unbase w = w := by
    refine TensorProduct.inductionOn w (fun c y ↦ ?_) fun x y hx hy ↦ by
      rw [map_add, TensorProduct.tmul_add, hx, hy]
    dsimp only [unbase]
    rw [TensorProduct.lift.tmul, LinearMap.mk₂_apply, ← TensorProduct.smul_tmul,
      Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]
    exact congrArg (· ⊗ₜ[Oᵢ⟦X⟧] y) (eqR.symm_apply_apply c)
  let A : Matrix (Fin r) (Fin r) Rᵢ := Bᵢ.map eqR.symm
  let π : (Fin r → Rᵢ) →ₗ[Rᵢ] (Rᵢ ⊗[O⟦X⟧] M) :=
    { toFun := fun v ↦ eMod (1 ⊗ₜ[Oᵢ⟦X⟧] πᵢ (fun j ↦ eqR (v j)))
      map_add' := fun u v ↦ by
        have hadd : (fun j ↦ eqR ((u + v) j)) = (fun j ↦ eqR (u j)) + (fun j ↦ eqR (v j)) :=
          funext fun j ↦ map_add eqR (u j) (v j)
        rw [hadd, map_add, TensorProduct.tmul_add, map_add]
      map_smul' := fun c v ↦ by
        have hsmul : (fun j ↦ eqR ((c • v) j)) = eqR c • (fun j ↦ eqR (v j)) :=
          funext fun j ↦ map_mul eqR c (v j)
        rw [hsmul, map_smul, ← TensorProduct.smul_tmul,
          show eqR c • (1 : Rᵢ) = c by
            rw [Algebra.smul_def, mul_one, RingHom.algebraMap_toAlgebra]
            exact eqR.symm_apply_apply c,
          TensorProduct.tmul_eq_smul_one_tmul]
        exact eMod.map_smul c (1 ⊗ₜ[Oᵢ⟦X⟧] πᵢ (fun j ↦ eqR (v j))) }
  have hπ : Function.Surjective π := fun z ↦ by
    obtain ⟨w, hw⟩ := hπᵢ (unbase (eMod.symm z))
    refine ⟨fun j ↦ eqR.symm (w j), ?_⟩
    change eMod (1 ⊗ₜ[Oᵢ⟦X⟧] πᵢ (fun j ↦ eqR (eqR.symm (w j)))) = z
    simp_rw [eqR.apply_symm_apply]
    rw [hw, htmul_unbase, eMod.apply_symm_apply]
  have hker_iff (v : Fin r → Rᵢ) :
      v ∈ LinearMap.ker π ↔ (fun j ↦ eqR (v j)) ∈ LinearMap.ker πᵢ := by
    simp only [LinearMap.mem_ker, π, LinearMap.coe_mk, AddHom.coe_mk]
    constructor
    · intro hv
      have h0 := congrArg unbase (eMod.injective (hv.trans eMod.map_zero.symm))
      simpa only [hunbase_tmul, map_zero] using h0
    · intro hv
      rw [hv, TensorProduct.tmul_zero, map_zero]
  let : IsLocalRing Rᵢ := isLocalRing_quotient_span_one_sub_C hloc
  have hmin : LinearMap.ker π ≤ maximalIdeal Rᵢ • (⊤ : Submodule Rᵢ (Fin r → Rᵢ)) := by
    intro v hv
    have hv' := hminᵢ ((hker_iff v).mp hv)
    have hmem_coord : ∀ w ∈ maximalIdeal Oᵢ⟦X⟧ • (⊤ : Submodule Oᵢ⟦X⟧ (Fin r → Oᵢ⟦X⟧)),
        ∀ j : Fin r, w j ∈ maximalIdeal Oᵢ⟦X⟧ := fun w hw j ↦ by
      refine Submodule.smul_induction_on hw (fun a ha y _ ↦ ?_) fun _ _ hy hz ↦ ?_
      · exact (maximalIdeal Oᵢ⟦X⟧).mul_mem_right (y j) ha
      · exact (maximalIdeal Oᵢ⟦X⟧).add_mem hy hz
    have hcoord : ∀ j : Fin r, v j ∈ maximalIdeal Rᵢ := fun j ↦ by
      have hj : eqR (v j) ∈ maximalIdeal Oᵢ⟦X⟧ := hmem_coord _ hv' j
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hj ⊢
      exact fun hu ↦ hj (eqR.toRingHom.isUnit_map hu)
    rw [show v = ∑ j : Fin r, v j • Pi.single j (1 : Rᵢ) by
      ext l; simp [Finset.sum_apply, Pi.single_apply]]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem_smul (hcoord j) Submodule.mem_top
  have hrange : LinearMap.range (Matrix.toLin' A) = LinearMap.ker π := by
    ext v
    rw [hker_iff, ← hrangeᵢ, LinearMap.mem_range, LinearMap.mem_range]
    have hmulVec (w : Fin r → Rᵢ) :
        (fun j ↦ eqR (Matrix.toLin' A w j)) = Matrix.toLin' Bᵢ (fun j ↦ eqR (w j)) := by
      funext j
      simp only [A, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by
        simp [map_mul, eqR.apply_symm_apply]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨fun j ↦ eqR (w j), (hmulVec w).symm⟩
    · rintro ⟨w, hw⟩
      refine ⟨fun j ↦ eqR.symm (w j), funext fun j ↦ eqR.injective ?_⟩
      have h1 := congrFun (hmulVec (fun k ↦ eqR.symm (w k))) j
      simpa only [eqR.apply_symm_apply, hw] using h1
  exact ⟨r, (finrank_residueField_tensorProduct_eq_of_minimalCover π hπ hmin).symm,
    A, π, hπ, hmin, hrange⟩

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
  have : TauCeti.IsSemiperfectRing O := TauCeti.IsSemiperfectRing.of_henselianRing ℤ_[p] O
  obtain ⟨m, e, he, hloc⟩ :=
    TauCeti.IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_quotient O
  refine TauCeti.IsQuadraticallyPresented.of_completeOrthogonalIdempotents (he.map C) fun i ↦ ?_
  obtain ⟨r, _, A, π, hπ, _, hrange⟩ :=
    controlledSquarePresentation_local_factor (p := p) hcof (e i) (hloc i)
  exact TauCeti.IsQuadraticallyPresented.of_exact (Pi.basisFun _ (Fin r)) (Pi.basisFun _ (Fin r))
    (LinearMap.exact_iff.2 hrange.symm) hπ

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
component factors `O ⧸ (1 - eᵢ)` and `O⟦X⟧ ⧸ (1 - C eᵢ)` are local rings, whose component
ranks `rᵢ` equal the minimal numbers of generators `dim_κ (κ ⊗ (O⟦X⟧ ⧸ (1 - C eᵢ)) ⊗ M)` on each
local factor, and whose surjection `g` is a minimal cover on each component. -/
theorem controlledSquarePresentation_projective_cofinal {M : Type*} [AddCommGroup M]
    [Module O⟦X⟧ M] [Module.Finite O⟦X⟧ M]
    (hcof : ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      TauCeti.IsQuadraticallyPresented (O⟦X⟧ ⧸ towerIdeal p O n)
        (M ⧸ (towerIdeal p O n • (⊤ : Submodule O⟦X⟧ M)))) :
    ∃ (m : ℕ) (e : Fin m → O) (_ : CompleteOrthogonalIdempotents e)
      (_ : ∀ i, IsLocalRing (O ⧸ Ideal.span {1 - e i}))
      (hlocR : ∀ i, IsLocalRing (O⟦X⟧ ⧸ Ideal.span {1 - C (e i)}))
      (r : Fin m → ℕ),
      (∀ i, letI := hlocR i
        r i = Module.finrank (ResidueField (O⟦X⟧ ⧸ Ideal.span {1 - C (e i)}))
          (ResidueField (O⟦X⟧ ⧸ Ideal.span {1 - C (e i)}) ⊗[O⟦X⟧ ⧸ Ideal.span {1 - C (e i)}]
            ((O⟦X⟧ ⧸ Ideal.span {1 - C (e i)}) ⊗[O⟦X⟧] M))) ∧
      let P := ∀ i : Fin m, Fin (r i) → (O⟦X⟧ ⧸ Ideal.span {1 - C (e i)})
      Module.Finite O⟦X⟧ P ∧ Module.Projective O⟦X⟧ P ∧
      ∃ (Φ : P →ₗ[O⟦X⟧] P) (g : P →ₗ[O⟦X⟧] M),
        Function.Surjective g ∧ LinearMap.range Φ = LinearMap.ker g ∧
        ∀ i, letI := hlocR i
          ∀ x ∈ LinearMap.ker g,
            x i ∈ maximalIdeal (O⟦X⟧ ⧸ Ideal.span {1 - C (e i)}) •
              (⊤ : Submodule (O⟦X⟧ ⧸ Ideal.span {1 - C (e i)})
                (Fin (r i) → (O⟦X⟧ ⧸ Ideal.span {1 - C (e i)}))) := by
  have : TauCeti.IsSemiperfectRing O := TauCeti.IsSemiperfectRing.of_henselianRing ℤ_[p] O
  obtain ⟨m, e, he, hloc⟩ :=
    TauCeti.IsSemiperfectRing.exists_completeOrthogonalIdempotents_isLocalRing_quotient O
  let hlocR : ∀ i, IsLocalRing (O⟦X⟧ ⧸ Ideal.span {1 - C (e i)}) :=
    fun i ↦ isLocalRing_quotient_span_one_sub_C (hloc i)
  choose r hr A π hπ hmin hrange using fun i ↦
    controlledSquarePresentation_local_factor (p := p) hcof (e i) (hloc i)
  obtain ⟨hfin, hproj, Φ, g, hg_surj, hrange_eq, hker_g⟩ :=
    TauCeti.exists_projectiveSquarePresentation_of_completeOrthogonalIdempotents (he.map C) r
      A π hπ hrange
  exact ⟨m, e, he, hloc, hlocR, r, hr, hfin, hproj, Φ, g, hg_surj, hrange_eq,
    fun i x hx ↦ hmin i ((hker_g x).mp hx i)⟩

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
  have hdet := P.det_mem_nonZeroDivisors_of_mem_fittingIdeal hd hreg
  exact ⟨P.hasProjectiveDimensionLE_one_of_det_mem_nonZeroDivisors hdet,
    P, P.fittingIdeal_eq, hdet, P.injective_toLin'_of_det_mem_nonZeroDivisors hdet⟩

end ProjectiveDimension

section Examples

/-! ### Edge-case sanity checks -/

-- `p = 2`: `J_{1,0} = (2, X) ≠ (X)`, `J_{0,3} = ⊤`, `(2, X) ≠ ⊤`, and `ω₁ = 2X + X² ≠ X²`.
example : C (2 : ℤ_[2]) ∈ jointIdeal 2 ℤ_[2] 1 0 ∧
    C (2 : ℤ_[2]) ∉ Ideal.span {(X : ℤ_[2]⟦X⟧)} ∧
    jointIdeal 2 ℤ_[2] 1 0 ≠ Ideal.span {(X : ℤ_[2]⟦X⟧)} ∧
    jointIdeal 2 ℤ_[2] 0 3 = ⊤ := by
  have hmem : C (2 : ℤ_[2]) ∈ jointIdeal 2 ℤ_[2] 1 0 :=
    jointIdeal_one_zero 2 ℤ_[2] ▸ Ideal.subset_span (by simp)
  have hnotmem : C (2 : ℤ_[2]) ∉ Ideal.span {(X : ℤ_[2]⟦X⟧)} := fun h ↦ by
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp h
    exact two_ne_zero (by simpa using congrArg constantCoeff hg)
  exact ⟨hmem, hnotmem, fun h ↦ hnotmem (h ▸ hmem), jointIdeal_zero_left 2 ℤ_[2] 3⟩

example : (1 + X : ℤ_[2]⟦X⟧) ^ 2 ^ 1 - 1 = 2 * X + X ^ 2 ∧
    (1 + X : ℤ_[2]⟦X⟧) ^ 2 ^ 1 - 1 ≠ X ^ 2 := by
  have heq : (1 + X : ℤ_[2]⟦X⟧) ^ 2 ^ 1 - 1 = 2 * X + X ^ 2 := by ring
  refine ⟨heq, fun h ↦ ?_⟩
  have h1 := congrArg (coeff 1) (heq.symm.trans h)
  rw [map_add, (map_ofNat C 2).symm, coeff_C_mul, coeff_X_pow] at h1
  norm_num at h1

example : Ideal.span {C (2 : ℤ_[2]), (X : ℤ_[2]⟦X⟧)} ≠ ⊤ := fun h ↦ by
  have hle : Ideal.span {C (2 : ℤ_[2]), (X : ℤ_[2]⟦X⟧)} ≤ maximalIdeal ℤ_[2]⟦X⟧ := by
    rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, ← jointIdeal_one_zero]
    have hp : ((2 : ℕ) : ℤ_[2]) ∈ maximalIdeal ℤ_[2] :=
      PadicInt.maximalIdeal_eq_span_p (p := 2) ▸ Ideal.mem_span_singleton_self _
    simpa only [pow_one] using jointIdeal_le_maximalIdeal_pow hp (a := 1) (n := 0) le_rfl le_rfl
  exact (maximalIdeal.isMaximal ℤ_[2]⟦X⟧).ne_top ((Ideal.eq_top_iff_one _).mpr (hle (h ▸ trivial)))

-- `M = 0` (`Subsingleton`) and `M = R` (`Fin 1` free) Fitting/determinant edge cases.
example {O : Type*} [CommRing O] :
    fittingIdeal O⟦X⟧ Unit 0 = ⊤ ∧
    (TauCeti.QuadraticPresentation.ofSubsingleton (R := O⟦X⟧) (N := Unit)).rel.det = 1 ∧
    fittingIdeal O⟦X⟧ O⟦X⟧ 0 = ⊥ ∧
    (TauCeti.QuadraticPresentation.ofBasis (R := O⟦X⟧) one_pos
      (Pi.basisFun O⟦X⟧ (Fin 1))).rel.det = 0 := by
  refine ⟨?_, Matrix.det_one, ?_, Matrix.det_zero (n := Fin 1)⟩
  · rw [(TauCeti.QuadraticPresentation.ofSubsingleton (R := O⟦X⟧) (N := Unit)).fittingIdeal_eq,
      show (TauCeti.QuadraticPresentation.ofSubsingleton (R := O⟦X⟧) (N := Unit)).rel.det = 1
        from Matrix.det_one, Ideal.span_singleton_one]
  · rw [(TauCeti.QuadraticPresentation.ofBasis (R := O⟦X⟧) one_pos
      (Module.Basis.singleton (Fin 1) O⟦X⟧)).fittingIdeal_eq,
      show (TauCeti.QuadraticPresentation.ofBasis (R := O⟦X⟧) one_pos
        (Module.Basis.singleton (Fin 1) O⟦X⟧)).rel.det = 0 from Matrix.det_zero (n := Fin 1),
      Ideal.span_singleton_zero]

-- Non-local / nonreduced finite `ℤ_[2]`-algebras: `ℤ₂[C₂]` and `DualNumber ℤ_[2]`.
example : Module.Finite ℤ_[2] (MonoidAlgebra ℤ_[2] (Multiplicative (ZMod 2))) :=
  Module.Finite.of_basis (MonoidAlgebra.basis (Multiplicative (ZMod 2)) ℤ_[2])

example : (C (DualNumber.eps : DualNumber ℤ_[2]) : (DualNumber ℤ_[2])⟦X⟧) ≠ 0 ∧
    (C (DualNumber.eps : DualNumber ℤ_[2]) : (DualNumber ℤ_[2])⟦X⟧) ∉
      nonZeroDivisors (DualNumber ℤ_[2])⟦X⟧ := by
  have hne : (DualNumber.eps : DualNumber ℤ_[2]) ≠ 0 := fun h ↦ by
    simpa using congrArg TrivSqZeroExt.snd h
  refine ⟨fun h ↦ hne (C_injective (by simpa using h)), fun hreg ↦ hne <| C_injective <| by
    simpa using (mem_nonZeroDivisors_iff.mp hreg).1 _ (by
      rw [← map_mul, DualNumber.eps_mul_eps, map_zero])⟩

end Examples

end TauCeti.Iwasawa
