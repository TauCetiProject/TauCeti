/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Polynomial.Taylor
public import TauCeti.FieldTheory.Minpoly.PowDvd

import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.RingTheory.Polynomial.HasseWronskian
import TauCeti.RingTheory.Polynomial.Wronskian

/-!
# Nonvanishing derivatives of Thue's auxiliary polynomials

Let `α` be algebraic of degree `d ≥ 2` over a field `K` of characteristic zero, and let
`P, Q ∈ K[X]`, not both zero, of degree at most `N < d r`, be such that `(X - α) ^ r` divides
`P - α Q`. Thue's auxiliary polynomials (`TauCeti.exists_thue_auxiliary_polynomials`) are of this
form. For every pair of points `ξ₁, ξ₂ ∈ K` there is then a Hasse derivative order
`k ≤ 2 N - d (r - 1)` with `Dᵏ P (ξ₁) ≠ ξ₂ Dᵏ Q (ξ₁)`. For Thue's polynomials, where
`N = ⌊(1 / 2 + ε) d r⌋`, this order is at most `d (2 ε r + 1)`.

In Thue's proof, `ξ₁` and `ξ₂` are two good rational approximations of `α`. The nonzero rational
number `Dᵏ P (ξ₁) - ξ₂ Dᵏ Q (ξ₁)` has bounded denominator, hence is not too small, whereas it is
small because `ξ₁` and `ξ₂` are close to `α`; the order `k` is small enough for the two estimates
to clash.

The proof considers the Wronskian `W = Q P' - Q' P`. It is nonzero, because `P` and `Q` are
linearly independent (a dependence would make `minpoly K α ^ r` divide `P` or `Q`, contradicting
`N < d r`). Since `W` is also the Wronskian of `Q` and `P - α Q`, it is divisible by
`(X - α) ^ (r - 1)` and hence, by `minpoly.pow_dvd_iff`, by `minpoly K α ^ (r - 1)`. Similarly,
if `ξ₁` is a root of multiplicity `m` of `P - ξ₂ Q`, then `(X - ξ₁) ^ (m - 1)` divides `W`. Since
`W` has degree less than `2 N`, comparing degrees gives `m + d (r - 1) ≤ 2 N`, and the Hasse
derivative of `P - ξ₂ Q` of order `m` does not vanish at `ξ₁`.

## Main results

* `TauCeti.exists_hasseDeriv_eval_ne_mul_of_dvd`: the general statement over a field `K` of
  characteristic zero, with `k + d (r - 1) ≤ 2 N`.
* `TauCeti.exists_hasseDeriv_aeval_ne_mul_of_natDegree_le`: the integer-polynomial form,
  retaining the natural-degree bound and `k ≤ N`.
* `TauCeti.exists_hasseDeriv_aeval_ne_mul_of_dvd`: the form used in Thue's theorem, for integer
  polynomials of degree at most `⌊(1 / 2 + ε) d r⌋`, rational points `ξ₁, ξ₂` and
  `k ≤ d (2 ε r + 1)`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, Lemma 6.12.
-/

public section

open Polynomial

namespace TauCeti

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- If `(X - α) ^ r` divides `P - α Q` for polynomials `P, Q ∈ K[X]` of degree less than `d r`,
where `d ≥ 2` is the degree of `α`, then `Q ≠ 0` and `P` is not a scalar multiple of `Q`. -/
private theorem ne_zero_and_forall_smul_ne_of_dvd {α : L} (hd : 2 ≤ (minpoly K α).natDegree)
    (hα : IsSeparable K α) {P Q : K[X]} (hPQ : P ≠ 0 ∨ Q ≠ 0) {r : ℕ}
    (hP : P.natDegree < (minpoly K α).natDegree * r)
    (hQ : Q.natDegree < (minpoly K α).natDegree * r)
    (hdvd : (X - C α) ^ r ∣ P.map (algebraMap K L) - C α * Q.map (algebraMap K L)) :
    Q ≠ 0 ∧ ∀ a : K, a • Q ≠ P := by
  -- A nonzero polynomial of degree less than `d r` is not divisible by `(X - α) ^ r`.
  have key {F : K[X]} (hF : F ≠ 0) (hFd : F.natDegree < (minpoly K α).natDegree * r) :
      ¬(X - C α) ^ r ∣ F.map (algebraMap K L) := fun h ↦ by
    have := natDegree_le_of_dvd ((minpoly.pow_dvd_iff hα).2 h) hF
    rw [natDegree_pow, mul_comm] at this
    omega
  have hQ₀ : Q ≠ 0 := by
    rintro rfl
    exact key (hPQ.resolve_right (by simp)) hP (by simpa using hdvd)
  refine ⟨hQ₀, fun a ha ↦ key hQ₀ hQ ?_⟩
  -- `α` is not in `K`, because it has degree at least `2`.
  have hne : algebraMap K L a - α ≠ 0 := sub_ne_zero.2 fun h ↦ by
    rw [← h, minpoly.eq_X_sub_C, natDegree_X_sub_C] at hd
    omega
  have heq : P.map (algebraMap K L) - C α * Q.map (algebraMap K L) =
      C (algebraMap K L a - α) * Q.map (algebraMap K L) := by
    simp [← ha, smul_eq_C_mul, sub_mul]
  exact (isUnit_C.2 hne.isUnit).dvd_mul_left.1 (heq ▸ hdvd)

/-- **Nonvanishing derivatives of Thue's polynomials.** Let `α` be algebraic of degree `d ≥ 2`
over a field `K` of characteristic zero, and let `P, Q ∈ K[X]`, not both zero, of degree at most
`N < d r`, be such that `(X - α) ^ r` divides `P - α Q`. For all `ξ₁, ξ₂ ∈ K` there is a `k` with
`k + d (r - 1) ≤ 2 N` such that the `k`-th Hasse derivatives satisfy `Dᵏ P (ξ₁) ≠ ξ₂ Dᵏ Q (ξ₁)`. -/
theorem exists_hasseDeriv_eval_ne_mul_of_dvd [CharZero K] {α : L}
    (hd : 2 ≤ (minpoly K α).natDegree) {P Q : K[X]} (hPQ : P ≠ 0 ∨ Q ≠ 0) {N r : ℕ}
    (hP : P.natDegree ≤ N) (hQ : Q.natDegree ≤ N) (hN : N < (minpoly K α).natDegree * r)
    (hdvd : (X - C α) ^ r ∣ P.map (algebraMap K L) - C α * Q.map (algebraMap K L))
    (ξ₁ ξ₂ : K) :
    ∃ k, k + (minpoly K α).natDegree * (r - 1) ≤ 2 * N ∧
      (hasseDeriv k P).eval ξ₁ ≠ ξ₂ * (hasseDeriv k Q).eval ξ₁ := by
  set f := minpoly K α
  have hint : IsIntegral K α := by
    by_contra h
    simp [f, minpoly.eq_zero h] at hd
  have hirr : Irreducible f := minpoly.irreducible hint
  obtain ⟨hQ₀, hind⟩ := ne_zero_and_forall_smul_ne_of_dvd hd hirr.separable hPQ (hP.trans_lt hN)
    (hQ.trans_lt hN) hdvd
  -- The Wronskian `Q P' - Q' P` is nonzero, since `Q` and `P` are linearly independent.
  have hW : wronskian Q P ≠ 0 := by
    have h := linearIndependent_iff_hasseWronskian_ne_zero.1
      ((LinearIndependent.pair_iff' hQ₀).2 hind)
    simpa using h
  -- `minpoly K α ^ (r - 1)` divides the Wronskian.
  have hfW : f ^ (r - 1) ∣ wronskian Q P := by
    rw [minpoly.pow_dvd_iff hirr.separable]
    have h := pow_sub_one_dvd_wronskian_right (a := Q.map (algebraMap K L)) hdvd
    rwa [wronskian_sub_C_mul_right, ← map_wronskian] at h
  -- `ξ₁` is a root of multiplicity `m` of `A = P - ξ₂ Q`, and `(X - ξ₁) ^ (m - 1)` divides the
  -- Wronskian.
  set A := P - C ξ₂ * Q
  have hA : A ≠ 0 := fun h ↦ hind ξ₂ (by rw [smul_eq_C_mul, eq_comm, ← sub_eq_zero]; exact h)
  obtain ⟨m, hm_def⟩ : ∃ m, m = A.rootMultiplicity ξ₁ := ⟨_, rfl⟩
  have hXW : (X - C ξ₁) ^ (m - 1) ∣ wronskian Q P := by
    rw [← wronskian_sub_C_mul_right Q P ξ₂]
    exact pow_sub_one_dvd_wronskian_right (hm_def ▸ pow_rootMultiplicity_dvd A ξ₁)
  -- The irreducible `f` has degree at least `2`, so it is coprime to `X - ξ₁`.
  have hcop : IsCoprime (f ^ (r - 1)) ((X - C ξ₁) ^ (m - 1)) := by
    refine (hirr.coprime_iff_not_dvd.2 fun h ↦ ?_).pow
    have := natDegree_le_of_dvd h (X_sub_C_ne_zero ξ₁)
    rw [natDegree_X_sub_C] at this
    omega
  have hdeg := natDegree_le_of_dvd (hcop.mul_dvd hfW hXW) hW
  simp [natDegree_mul, hirr.ne_zero, X_sub_C_ne_zero, mul_comm (r - 1)] at hdeg
  have hWlt := natDegree_wronskian_lt_add hW
  -- The Hasse derivative of `A` of order `m` does not vanish at `ξ₁`.
  have hm : (hasseDeriv m A).eval ξ₁ ≠ 0 := hm_def ▸ eval_hasseDeriv_rootMultiplicity_ne_zero hA ξ₁
  refine ⟨m, by omega, fun h ↦ hm ?_⟩
  simp [A, ← smul_eq_C_mul, h]

/-- The integer-polynomial form of derivative nonvanishing, retaining the natural-degree
bound `k + d (r - 1) ≤ 2 N`. The nonzero derivative also forces `k ≤ N`. -/
theorem exists_hasseDeriv_aeval_ne_mul_of_natDegree_le {F : Type*} [Field F] [CharZero F]
    {α : F} (hd : 2 ≤ (minpoly ℚ α).natDegree) {P Q : ℤ[X]}
    (hPQ : P ≠ 0 ∨ Q ≠ 0) {N r : ℕ} (hP : P.natDegree ≤ N) (hQ : Q.natDegree ≤ N)
    (hN : N < (minpoly ℚ α).natDegree * r)
    (hdvd : (X - C α) ^ r ∣ P.map (Int.castRingHom F) - C α * Q.map (Int.castRingHom F))
    (ξ₁ ξ₂ : ℚ) :
    ∃ k : ℕ, k ≤ N ∧ k + (minpoly ℚ α).natDegree * (r - 1) ≤ 2 * N ∧
      aeval ξ₁ (hasseDeriv k P) ≠ ξ₂ * aeval ξ₁ (hasseDeriv k Q) := by
  have hmap (p : ℤ[X]) : p.map (Int.castRingHom F) =
      (p.map (Int.castRingHom ℚ)).map (algebraMap ℚ F) := by
    rw [Polynomial.map_map, RingHom.ext_int ((algebraMap ℚ F).comp _) (Int.castRingHom F)]
  obtain ⟨k, hk, hne⟩ := exists_hasseDeriv_eval_ne_mul_of_dvd
    (P := P.map (Int.castRingHom ℚ)) (Q := Q.map (Int.castRingHom ℚ)) hd
    (hPQ.imp (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2
      (Polynomial.map_ne_zero_iff (RingHom.injective_int _)).2)
    (natDegree_map_le.trans hP) (natDegree_map_le.trans hQ) hN
    (by simpa only [← hmap] using hdvd) ξ₁ ξ₂
  have hne' : aeval ξ₁ (hasseDeriv k P) ≠ ξ₂ * aeval ξ₁ (hasseDeriv k Q) := by
    simpa only [hasseDeriv_map, ← algebraMap_int_eq, eval_map_algebraMap] using hne
  refine ⟨k, ?_, hk, hne'⟩
  by_contra! h
  have hPk := hasseDeriv_eq_zero_of_lt_natDegree P k (hP.trans_lt h)
  have hQk := hasseDeriv_eq_zero_of_lt_natDegree Q k (hQ.trans_lt h)
  simp [hPk, hQk] at hne'

/-- Convert the natural-degree order bound into the real order bound used in Thue's
construction, whenever the auxiliary degree is at most `(1 / 2 + ε) d r`. -/
theorem thue_order_le_of_add_mul_le {d r k N : ℕ} {ε : ℝ} (hr : 0 < r)
    (hN : (N : ℝ) ≤ (1 / 2 + ε) * d * r) (hk : k + d * (r - 1) ≤ 2 * N) :
    (k : ℝ) ≤ d * (2 * ε * r + 1) := by
  have hk' : (k : ℝ) + d * ((r : ℝ) - 1) ≤ 2 * N := by
    have : ((k + d * (r - 1) : ℕ) : ℝ) ≤ ((2 * N : ℕ) : ℝ) := by exact_mod_cast hk
    push_cast [Nat.cast_sub hr] at this
    exact this
  nlinarith

/-- **Nonvanishing derivatives of Thue's polynomials**, in the form used in Thue's theorem. Let
`α` be algebraic of degree `d ≥ 2` over `ℚ`, let `0 ≤ ε < 1 / 2` and `r ≥ 1`, and let `P, Q` be
integer polynomials, not both zero, of degree at most `⌊(1 / 2 + ε) d r⌋`, such that `(X - α) ^ r`
divides `P - α Q`. For all rational numbers `ξ₁, ξ₂` there is a `k ≤ d (2 ε r + 1)` such that the
`k`-th Hasse derivatives satisfy `Dᵏ P (ξ₁) ≠ ξ₂ Dᵏ Q (ξ₁)`. -/
theorem exists_hasseDeriv_aeval_ne_mul_of_dvd {F : Type*} [Field F] [CharZero F] {α : F}
    (hd : 2 ≤ (minpoly ℚ α).natDegree) {ε : ℝ} (hε₀ : 0 ≤ ε) (hε : ε < 1 / 2) {r : ℕ}
    (hr : 0 < r) {P Q : ℤ[X]} (hPQ : P ≠ 0 ∨ Q ≠ 0)
    (hP : P.natDegree ≤ ⌊(1 / 2 + ε) * (minpoly ℚ α).natDegree * r⌋₊)
    (hQ : Q.natDegree ≤ ⌊(1 / 2 + ε) * (minpoly ℚ α).natDegree * r⌋₊)
    (hdvd : (X - C α) ^ r ∣ P.map (Int.castRingHom F) - C α * Q.map (Int.castRingHom F))
    (ξ₁ ξ₂ : ℚ) :
    ∃ k : ℕ, (k : ℝ) ≤ (minpoly ℚ α).natDegree * (2 * ε * r + 1) ∧
      aeval ξ₁ (hasseDeriv k P) ≠ ξ₂ * aeval ξ₁ (hasseDeriv k Q) := by
  set d := (minpoly ℚ α).natDegree
  set N := ⌊(1 / 2 + ε) * d * r⌋₊
  have hdr : (0 : ℝ) < d * r := by
    have : 0 < d * r := Nat.mul_pos (by omega) hr
    exact_mod_cast this
  have hNle : (N : ℝ) ≤ (1 / 2 + ε) * d * r := Nat.floor_le (by positivity)
  have hN : N < d * r := by
    rw [Nat.floor_lt (by positivity)]
    push_cast
    nlinarith
  obtain ⟨k, _, hk, hne⟩ :=
    exists_hasseDeriv_aeval_ne_mul_of_natDegree_le hd hPQ hP hQ hN hdvd ξ₁ ξ₂
  exact ⟨k, thue_order_le_of_add_mul_le hr hNle hk, hne⟩

end TauCeti
