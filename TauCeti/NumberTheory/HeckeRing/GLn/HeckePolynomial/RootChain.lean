/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import TauCeti.NumberTheory.HeckeRing.GLn.HeckePolynomial.Basic

import Mathlib.Algebra.Star.BigOperators
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import TauCeti.Data.Nat.Choose.Basic

/-!
# Root chains of `GL n` Hecke polynomials

This file isolates the linear-algebraic and polynomial core of the root-chain lemma for
spherical Hecke polynomials of `GL_N` in unitary representations (cf. Tadić's classification of
the unitary dual and Bernstein's inequality at the ends of segments).

Given a positive-definite sesquilinear form `B` on a complex vector space `V`, mutually adjoint
endomorphisms `U, U' : Module.End ℂ V`, a real scale `q > 1`, and vectors `T₀, …, Tₙ` satisfying
the two hyperplane-count recursions attached to `P = glnHeckePolynomial (n + 1) (q : ℂ) t`:

* `TauCeti.glnHeckePolynomial_root_chain_of_adjoint` proves:
  1. **Top-root lower bound**: every root `c` of `P` such that `q * c` is not a root satisfies
     `q ^ (n + 1) / q ^ 2 ≤ ‖c‖ ^ 2`;
  2. **Chain cancellation**: if `d ≠ 0`, `q ^ k / d` is a root of `P`, and
     `P = (∏ i < k, (C d * X - C (q ^ i))) * R`, then `aeval U' (R.map (starRingEnd ℂ)) (T 0) = 0`.
* `TauCeti.isRoot_of_glnHeckePolynomial_star_mul_eq` derives the root symmetry
  `y ↦ q ^ (N - 1) / star y` from coefficient duality `star (t d) * b₀ = t d.rev * z`.
* `TauCeti.isRoot_mul_pow_of_norm_sq_mul_pow_eq` combines that root symmetry with the top-root
  lower bound: any root `c` with `‖c‖ ^ 2 * q ^ k = q ^ N` generates the full root chain
  `c, c * q, …, c * q ^ (k - 1)`.

## Main declarations

* `TauCeti.glnHeckePolynomial_succ`
* `TauCeti.sesquilinear_aeval_map_starRingEnd`
* `TauCeti.glnHeckePolynomial_root_chain_of_adjoint`
* `TauCeti.isRoot_of_glnHeckePolynomial_star_mul_eq`
* `TauCeti.isRoot_mul_pow_of_norm_sq_mul_pow_eq`
-/

public section

open ComplexOrder Finset Module Polynomial

namespace TauCeti

/-- Recursive formula for the `GL n` Hecke polynomial:
`glnHeckePolynomial (n + 1) q T = X * glnHeckePolynomial n q (T ∘ Fin.castSucc) +
C ((-1) ^ (n + 1) * q ^ (n + 1).choose 2 * T (Fin.last (n + 1)))`. -/
theorem glnHeckePolynomial_succ {A : Type*} [Ring A] (n : ℕ) (q : A) (T : Fin (n + 2) → A) :
    glnHeckePolynomial (n + 1) q T =
      X * glnHeckePolynomial n q (fun i ↦ T i.castSucc) +
        C ((-1) ^ (n + 1) * q ^ (n + 1).choose 2 * T (Fin.last (n + 1))) := by
  rw [glnHeckePolynomial_def, Fin.sum_univ_castSucc, glnHeckePolynomial_def, mul_sum]
  congr 1
  · refine sum_congr rfl fun i _ ↦ ?_
    have hi : n + 1 - (i : ℕ) = (n - (i : ℕ)) + 1 := by omega
    rw [Fin.val_castSucc, hi, pow_succ', ← mul_assoc, ← mul_assoc, (commute_X _).eq]
  · simp [Fin.val_last]

/-- If `U'` is left-adjoint to `U` on a `U`-invariant set `S` for a sesquilinear form `B`, then
`aeval U' (G.map (starRingEnd R))` is left-adjoint to `aeval U G` on `S`. -/
theorem sesquilinear_aeval_map_starRingEnd {R V : Type*} [CommSemiring R] [StarRing R]
    [AddCommMonoid V] [Module R V] (B : V →ₛₗ[starRingEnd R] V →ₗ[R] R) {U U' : End R V}
    (S : Set V) (adj : ∀ y ∈ S, U y ∈ S ∧ ∀ a : V, B (U' a) y = B a (U y)) (G : R[X]) (a : V) :
    ∀ y ∈ S, B (aeval U' (G.map (starRingEnd R)) a) y = B a (aeval U G y) := by
  induction G using recOnHorner generalizing a with
  | M0 => simp
  | MC G c _ _ ih => simp_all
  | MX G _ ih =>
    intro y hy
    rw [Polynomial.map_mul, Polynomial.map_X, mul_comm _ X, map_mul, aeval_X,
      mul_apply_eq_comp, (adj y hy).2, map_mul, aeval_X, mul_apply_eq_comp,
      ih a (U y) (adj y hy).1]

section RootChain

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- If `P (U)` kills `y` and `(P / (X - c)) (U)` still kills `y` whenever `c ≠ 0` and `q * c` are
both roots of `P`, then any chain `q ^ i / d` (`i < k`) ending below a root `q ^ k / d` cancels. -/
private lemma aeval_cofactor_eq_zero {U : End ℂ V} {y : V} {P : ℂ[X]} {q : ℝ} {d : ℂ}
    (hq : 1 < q) (aeval_P : aeval U P y = 0)
    (two_roots :
      ∀ {c : ℂ} (F : ℂ[X]), (X - C c) * F = P → P.IsRoot ((q : ℂ) * c) → c ≠ 0 →
        aeval U F y = 0)
    (hd : d ≠ 0) (k : ℕ) (R : ℂ[X]) (hroot : P.IsRoot ((q : ℂ) ^ k / d))
    (hP : P = (∏ i ∈ range k, (C d * X - C ((q : ℂ) ^ i))) * R) :
    aeval U R y = 0 := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq).ne'
  induction k generalizing R with
  | zero => simpa [hP] using aeval_P
  | succ k ih =>
    simp only [prod_range_succ, mul_assoc, pow_succ', mul_div_assoc] at hP hroot
    have h_root_k : P.IsRoot ((q : ℂ) ^ k / d) := by simp [hP, field]
    have eigen_R : U (aeval U R y) = (d⁻¹ * (q : ℂ) ^ k) • aeval U R y := by
      simpa [sub_eq_zero, ← eq_inv_smul_iff₀ hd, smul_smul, -map_pow] using ih _ h_root_k hP
    set Q : ℂ[X] := ∏ i ∈ range k, (C d * X - C ((q : ℂ) ^ i))
    have cancel : (X - C ((q : ℂ) ^ k / d)) * (d • Q * R) = P :=
      Polynomial.funext fun a ↦ by simp [hP, field]
    have killed : aeval U Q (aeval U R y) = 0 := by
      simpa [hd] using two_roots _ cancel hroot (div_ne_zero (pow_ne_zero k hq0) hd)
    have eval_ne : Q.eval (d⁻¹ * (q : ℂ) ^ k) ≠ 0 := by
      intro h0
      rw [eval_prod, Finset.prod_eq_zero_iff] at h0
      obtain ⟨i, hi, h_eq⟩ := h0
      simp only [mem_range, eval_sub, eval_mul, eval_C, eval_X, sub_eq_zero] at hi h_eq
      have h_pow : (q : ℂ) ^ k = (q : ℂ) ^ i := by
        simpa [← mul_assoc, mul_inv_cancel₀ hd] using h_eq
      have h_powR : q ^ k = q ^ i := by exact_mod_cast h_pow
      exact (pow_lt_pow_right₀ hq hi).ne' h_powR
    rwa [Module.End.aeval_apply_of_mem_apply_eq_smul (p := Q) eigen_R,
      smul_eq_zero_iff_right eval_ne] at killed

/-- If `R (U)` kills every `T j` (`j : Fin (n + 1)`) and the adjoint `U'` preserves their span,
then `aeval U' (R.map (starRingEnd ℂ)) (T 0) = 0`. -/
private lemma aeval_conj_eq_zero {B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ} {U U' : End ℂ V} {n : ℕ}
    {T : Fin (n + 1) → V} {R : ℂ[X]} {a : ℂ} {b c : Fin n → ℂ}
    (hB : ∀ f ≠ (0 : V), 0 < B f f) (adj : ∀ y z : V, B (U' y) z = B y (U z))
    (kills_T : ∀ j : Fin (n + 1), aeval U R (T j) = 0) (U'_first : U' (T 0) = a • T (Fin.last n))
    (rec_U' : ∀ i : Fin n, U' (T i.succ) = b i • (c i • U' (T 0) - T i.castSucc)) :
    aeval U' (R.map (starRingEnd ℂ)) (T 0) = 0 := by
  have kills_span (F : ℂ[X]) : ∀ j : Fin (n + 1), aeval U R (aeval U' F (T j)) = 0 := by
    induction F using recOnHorner with
    | M0 => simp
    | MC F s _ _ ih => simp +contextual [ih, kills_T]
    | MX F _ ih =>
      intro j
      refine Fin.cases ?_ ?_ j
      · simp [U'_first, ih]
      · intro i
        simp [rec_U' i, U'_first, ih (Fin.last n), ih i.castSucc]
  refine by_contra fun hne ↦ (hB _ hne).ne' ?_
  rw [sesquilinear_aeval_map_starRingEnd B Set.univ (fun y _ ↦ ⟨trivial, fun z ↦ adj z y⟩)
    R _ _ trivial, kills_span _ 0, map_zero]

/-- Prefix evaluation of `glnHeckePolynomial` at `U` along the `U`-recursion. -/
private lemma aeval_glnHeckePolynomial_prefix {U : End ℂ V} {n : ℕ} {q : ℂ} {t : Fin (n + 2) → ℂ}
    {T : Fin (n + 1) → V} (ht_zero : t 0 • T 0 = T 0)
    (rec_U : ∀ j : Fin n,
      U (T j.castSucc) = q ^ (j : ℕ) • (t j.succ.castSucc • T 0 - T j.succ))
    (m : ℕ) (hm : m ≤ n) :
    aeval U (glnHeckePolynomial m q (fun i ↦ t ⟨i, by omega⟩)) (T 0) =
      ((-1) ^ m * q ^ m.choose 2) • T ⟨m, by omega⟩ := by
  induction m with
  | zero => simpa [glnHeckePolynomial_zero] using ht_zero
  | succ m ih =>
    have hm_lt : m < n := by omega
    have hrec : U (T ⟨m, by omega⟩) =
        q ^ m • (t ⟨m + 1, by omega⟩ • T 0 - T ⟨m + 1, by omega⟩) := rec_U ⟨m, hm_lt⟩
    have hstep := glnHeckePolynomial_succ m q (fun i : Fin (m + 2) ↦ t ⟨i, by omega⟩)
    simp only [Fin.val_castSucc, Fin.val_last] at hstep
    have hih := ih hm_lt.le
    rw [hstep, map_add, LinearMap.add_apply, map_mul, aeval_X, mul_apply_eq_comp, hih,
      map_smul, hrec, aeval_C, Module.algebraMap_end_apply]
    simp only [Nat.choose_succ_succ, Nat.choose_one_right]
    module

/-- Action of `U'` on the quotient of a prefix Hecke polynomial by `X - c`. -/
private lemma exists_mul_eq_sub_eval_and_apply {U U' : End ℂ V} {n : ℕ} {q : ℂ}
    {t : Fin (n + 2) → ℂ} {T : Fin (n + 1) → V} (hq : q ≠ 0) (ht_last : t (Fin.last (n + 1)) ≠ 0)
    (rec_U' : ∀ i : Fin n,
      U' (T i.succ) =
        q ^ (n - (i : ℕ) - 1) • ((t i.succ.castSucc / q ^ n) • U' (T 0) - T i.castSucc))
    (U'_first : U' (T 0) = q ^ n • (t (Fin.last (n + 1)))⁻¹ • T (Fin.last n))
    (aeval_p : ∀ (m : ℕ) (hm : m ≤ n),
      aeval U (glnHeckePolynomial m q (fun i ↦ t ⟨i, by omega⟩)) (T 0) =
        ((-1) ^ m * q ^ m.choose 2) • T ⟨m, by omega⟩)
    (aeval_top : aeval U (glnHeckePolynomial (n + 1) q t) (T 0) = 0)
    (m : ℕ) (hm : m ≤ n + 1) (c : ℂ) :
    let Pm : ℂ[X] := glnHeckePolynomial m q (fun i ↦ t ⟨i, by omega⟩)
    ∃ D : ℂ[X], (X - C c) * D = Pm - C (Pm.eval c) ∧
      U' (aeval U (c • D + Pm) (T 0)) =
        (Pm.eval (q * c) / q ^ m) • U' (T 0) + (q ^ n / q) • aeval U D (T 0) := by
  induction m with
  | zero => exact ⟨0, by simp [glnHeckePolynomial_zero]⟩
  | succ m ih =>
    obtain ⟨D, hD, hU'⟩ := ih (Nat.lt_of_succ_le hm).le
    have hstep := glnHeckePolynomial_succ m q (fun i : Fin (m + 2) ↦ t ⟨i, by omega⟩)
    simp only [Fin.val_castSucc, Fin.val_last] at hstep
    refine ⟨c • D + glnHeckePolynomial m q (fun i ↦ t ⟨i, by omega⟩), ?_, ?_⟩
    · rw [hstep]
      have h_poly :
          (X - C c) * (C c * D + glnHeckePolynomial m q (fun i ↦ t ⟨i, by omega⟩)) =
            X * glnHeckePolynomial m q (fun i ↦ t ⟨i, by omega⟩) -
              C c * C ((glnHeckePolynomial m q (fun i ↦ t ⟨i, by omega⟩)).eval c) := by
        linear_combination C c * hD
      simpa [smul_eq_C_mul] using h_poly
    · rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_add, map_smul, hU']
      rcases eq_or_lt_of_le (Nat.le_of_succ_le_succ hm) with hmn | hmlt
      · subst hmn
        have htop : aeval U (glnHeckePolynomial (m + 1) q fun i ↦ t ⟨i, by omega⟩) (T 0) = 0 :=
          aeval_top
        have ht_last' : t ⟨m + 1, by omega⟩ ≠ 0 := ht_last
        have hT_last : T ⟨m, by omega⟩ = (q ^ m)⁻¹ • t ⟨m + 1, by omega⟩ • U' (T 0) := by
          rw [U'_first, Fin.last, Fin.last]
          have h1 : (q ^ m)⁻¹ * t ⟨m + 1, by omega⟩ * q ^ m * (t ⟨m + 1, by omega⟩)⁻¹ = 1 := by
            field_simp [hq, ht_last']
          simp only [smul_smul, ← mul_assoc, h1, one_smul]
        rw [htop, map_zero, add_zero, hstep, eval_add, eval_mul, eval_X, eval_C,
          map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, aeval_p m le_rfl, hT_last]
        simp only [Nat.choose_succ_succ, Nat.choose_one_right]
        match_scalars <;> field
      · have hrec : U' (T ⟨m + 1, by omega⟩) =
            q ^ (n - m - 1) • ((t ⟨m + 1, by omega⟩ / q ^ n) • U' (T 0) - T ⟨m, by omega⟩) :=
          rec_U' ⟨m, hmlt⟩
        have hpow : q ^ (n - m - 1) = q ^ n / q ^ (m + 1) := by
          rw [eq_div_iff (pow_ne_zero _ hq), ← pow_add, show n - m - 1 + (m + 1) = n by omega]
        rw [aeval_p (m + 1) hmlt, map_smul, hrec, hpow, hstep, eval_add, eval_mul, eval_X, eval_C,
          map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, aeval_p m hmlt.le]
        simp only [Nat.choose_succ_succ, Nat.choose_one_right]
        match_scalars <;> field

/-- Pairing estimate behind `glnHeckePolynomial_root_chain_of_adjoint`. -/
private lemma le_norm_sq_of_pairing {B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ} {U U' : End ℂ V}
    {x z : V} {c a : ℂ} {q : ℝ} {n : ℕ} (hB : ∀ f ≠ (0 : V), 0 < B f f)
    (adj : ∀ y w : V, B (U' y) w = B y (U w)) (hq : 1 < q) (hx_ne : x ≠ 0) (ha : a ≠ 0)
    (U_z : U z = c • z)
    (U'_z : c • U' z = (a / (q : ℂ) ^ (n + 1)) • U' x + ((q : ℂ) ^ n / q) • z)
    (pair_x : c * B x z * ((q : ℂ) ^ (n + 1) - 1) = a * B x x) :
    q ^ (n + 1) / q ^ 2 ≤ ‖c‖ ^ 2 := by
  have hqC : (1 : ℂ) < (q : ℂ) := by exact_mod_cast hq
  have pow_sub_pos : (0 : ℂ) < (q : ℂ) ^ (n + 1) - 1 := sub_pos.mpr (one_lt_pow₀ hqC n.succ_ne_zero)
  have x_pos : 0 < B x x := hB x hx_ne
  have z_pos : 0 < B z z := hB z fun hz ↦ ha (by simpa [hz, x_pos.ne'] using pair_x)
  have pair_z : (‖c‖ ^ 2 - (q : ℂ) ^ n / q) * B z z =
      starRingEnd ℂ a / (q : ℂ) ^ (n + 1) * (c * B x z) := by
    have paired : starRingEnd ℂ c * (c * B z z) =
        starRingEnd ℂ a / (q : ℂ) ^ (n + 1) * (c * B x z) + (q : ℂ) ^ n / q * B z z := by
      simpa [adj, U_z] using congrArg (fun y : V ↦ B y z) U'_z
    linear_combination paired - B z z * Complex.mul_conj' c
  have gap : ((‖c‖ ^ 2 : ℂ) - (q : ℂ) ^ (n + 1) / (q : ℂ) ^ 2) =
      ‖a‖ ^ 2 * B x x / (q : ℂ) ^ (n + 1) / (((q : ℂ) ^ (n + 1) - 1) * B z z) := by
    rw [eq_div_iff (mul_pos pow_sub_pos z_pos).ne', ← Complex.mul_conj' a]
    linear_combination (norm := field) ((q : ℂ) ^ (n + 1) - 1) * pair_z +
      starRingEnd ℂ a / (q : ℂ) ^ (n + 1) * pair_x
  have : (0 : ℂ) < (q : ℂ) := zero_lt_one.trans hqC
  have gap_nonneg : (0 : ℂ) ≤ ((‖c‖ ^ 2 : ℂ) - (q : ℂ) ^ (n + 1) / (q : ℂ) ^ 2) :=
    gap.ge.trans' (by positivity)
  exact Complex.real_le_real.mp (by simpa using gap_nonneg)

/-- Top-degree evaluation of `glnHeckePolynomial` vanishes when `U (T n)` closes the recursion. -/
private lemma aeval_glnHeckePolynomial_top_eq_zero {U : End ℂ V} {n : ℕ} {q : ℂ}
    {t : Fin (n + 2) → ℂ} {T : Fin (n + 1) → V}
    (hn : aeval U (glnHeckePolynomial n q (fun i ↦ t i.castSucc)) (T 0) =
      ((-1) ^ n * q ^ n.choose 2) • T (Fin.last n))
    (U_last : U (T (Fin.last n)) = q ^ n • t (Fin.last (n + 1)) • T 0) :
    aeval U (glnHeckePolynomial (n + 1) q t) (T 0) = 0 := by
  rw [glnHeckePolynomial_succ, map_add, LinearMap.add_apply, map_mul, aeval_X,
    mul_apply_eq_comp, hn, map_smul, U_last, aeval_C, Module.algebraMap_end_apply]
  simp only [Nat.choose_succ_succ, Nat.choose_one_right]
  module

/-- If `z` is an `U'`-eigenvector orthogonal to `x`, then `z` is orthogonal to `G (U) x` for
every polynomial `G`. -/
private lemma sesquilinear_aeval_eq_zero_of_eigen {B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ}
    {U U' : End ℂ V} {x z : V} {μ : ℂ}
    (adj' : ∀ a y : V, B (U a) y = B a (U' y)) (eigen_z : U' z = μ • z) (orth_x : B x z = 0)
    (G : ℂ[X]) : B (aeval U G x) z = 0 := by
  induction G using recOnHorner with
  | M0 => simp
  | MC G a _ _ ih => simp [ih, orth_x]
  | MX G _ ih => simp [← X_mul, adj', eigen_z, ih]

/-- The linear-algebraic core of the `GL_N` root-chain lemma.

Let `B` be a positive-definite sesquilinear form on `V`, `U` and `U'` mutually adjoint for `B`,
`q > 1` real, `P = glnHeckePolynomial (n + 1) (q : ℂ) t`, and `T : Fin (n + 1) → V` with
`T 0 ≠ 0`, `t 0 • T 0 = T 0`, `t (Fin.last (n + 1)) ≠ 0`, satisfying the forward recursion for `U`
and backward recursion for `U'`. Then:
1. every root `c` of `P` for which `q * c` is not a root satisfies `q ^ (n + 1) / q ^ 2 ≤ ‖c‖ ^ 2`;
2. if `d ≠ 0`, `q ^ k / d` is a root of `P`, and `P = (∏ i < k, (C d * X - C (q ^ i))) * R`, then
   `aeval U' (R.map (starRingEnd ℂ)) (T 0) = 0`. -/
theorem glnHeckePolynomial_root_chain_of_adjoint {B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ}
    (U U' : End ℂ V) {n : ℕ} {q : ℝ} {t : Fin (n + 2) → ℂ} (T : Fin (n + 1) → V)
    (hB : ∀ f ≠ (0 : V), 0 < B f f)
    (adj : ∀ a y : V, B (U' a) y = B a (U y)) (adj' : ∀ a y : V, B (U a) y = B a (U' y))
    (hq : 1 < q) (hT_ne : T 0 ≠ 0) (ht_zero : t 0 • T 0 = T 0)
    (ht_last : t (Fin.last (n + 1)) ≠ 0)
    (rec_U : ∀ j : Fin n,
      U (T j.castSucc) = (q : ℂ) ^ (j : ℕ) • (t j.succ.castSucc • T 0 - T j.succ))
    (rec_U' : ∀ i : Fin n,
      U' (T i.succ) =
        (q : ℂ) ^ (n - (i : ℕ) - 1) •
          ((t i.succ.castSucc / (q : ℂ) ^ n) • U' (T 0) - T i.castSucc))
    (U'_first : U' (T 0) = (q : ℂ) ^ n • (t (Fin.last (n + 1)))⁻¹ • T (Fin.last n))
    (U_last : U (T (Fin.last n)) = (q : ℂ) ^ n • t (Fin.last (n + 1)) • T 0) :
    let P := glnHeckePolynomial (n + 1) (q : ℂ) t
    (∀ c : ℂ, P.IsRoot c → ¬ P.IsRoot ((q : ℂ) * c) → q ^ (n + 1) / q ^ 2 ≤ ‖c‖ ^ 2) ∧
    ∀ d ≠ (0 : ℂ), ∀ (k : ℕ) (R : ℂ[X]), P.IsRoot ((q : ℂ) ^ k / d) →
      P = (∏ i ∈ range k, (C d * X - C ((q : ℂ) ^ i))) * R →
      aeval U' (R.map (starRingEnd ℂ)) (T 0) = 0 := by
  intro P
  have hqC : (1 : ℂ) < (q : ℂ) := by exact_mod_cast hq
  have q_ne : (q : ℂ) ≠ 0 := (zero_lt_one.trans hqC).ne'
  have pow_sub_pos : (0 : ℂ) < (q : ℂ) ^ (n + 1) - 1 := sub_pos.mpr (one_lt_pow₀ hqC n.succ_ne_zero)
  have aeval_p := aeval_glnHeckePolynomial_prefix ht_zero rec_U
  have aeval_P : aeval U P (T 0) = 0 :=
    aeval_glnHeckePolynomial_top_eq_zero (aeval_p n le_rfl) U_last
  have quot (c : ℂ) : ∃ D : ℂ[X], (X - C c) * D = P - C (P.eval c) ∧
      U' (aeval U (c • D + P) (T 0)) =
        (P.eval ((q : ℂ) * c) / (q : ℂ) ^ (n + 1)) • U' (T 0) +
          ((q : ℂ) ^ n / q) • aeval U D (T 0) :=
    exists_mul_eq_sub_eval_and_apply q_ne ht_last rec_U' U'_first aeval_p aeval_P (n + 1) le_rfl c
  choose D hD hU' using quot
  let z (c : ℂ) : V := aeval U (D c) (T 0)
  have U'_z (c : ℂ) :
      c • U' (z c) =
        (P.eval ((q : ℂ) * c) / (q : ℂ) ^ (n + 1)) • U' (T 0) + ((q : ℂ) ^ n / q) • z c := by
    simpa [aeval_P] using hU' c
  have U_z (c : ℂ) (hc : P.IsRoot c) : U (z c) = c • z c := by
    simpa [aeval_P, hc.eq_zero, sub_eq_zero] using congrArg (aeval U · (T 0)) (hD c)
  have pair_U' (y : V) : B (U' (T 0)) (U' y) = (q : ℂ) ^ n * (q : ℂ) ^ n * B (T 0) y := by
    simp [← adj', U'_first, U_last]
    field_simp [ht_last]
  have pair_x (c : ℂ) (hc : P.IsRoot c) :
      c * B (T 0) (z c) * ((q : ℂ) ^ (n + 1) - 1) = P.eval ((q : ℂ) * c) * B (T 0) (T 0) := by
    have paired : B (U' (T 0)) (c • U' (z c)) =
        B (U' (T 0)) ((P.eval ((q : ℂ) * c) / (q : ℂ) ^ (n + 1)) • U' (T 0) +
          ((q : ℂ) ^ n / q) • z c) := by rw [U'_z c]
    simp only [map_add, map_smul, pair_U', adj _ (z c), U_z c hc, smul_eq_mul] at paired
    linear_combination (norm := field) (q : ℂ) / (q : ℂ) ^ n * paired
  refine ⟨fun c hc hqc ↦
    le_norm_sq_of_pairing hB adj hq hT_ne hqc (U_z c hc) (U'_z c) (pair_x c hc), ?_⟩
  have two_roots {c : ℂ} (F : ℂ[X]) (hF : (X - C c) * F = P) (hqc : P.IsRoot ((q : ℂ) * c))
      (hc : c ≠ 0) : aeval U F (T 0) = 0 := by
    have root : P.IsRoot c := by simp [← hF]
    obtain rfl : F = D c :=
      mul_left_cancel₀ (X_sub_C_ne_zero c) (by simp [hF, hD, root.eq_zero])
    have eigen_z : U' (z c) = (c⁻¹ * ((q : ℂ) ^ n / q)) • z c := by
      rw [← smul_smul]; exact (eq_inv_smul_iff₀ hc).mpr (by simpa [hqc.eq_zero] using U'_z c)
    have orth_x : B (T 0) (z c) = 0 := by
      simpa [hqc.eq_zero, hc, pow_sub_pos.ne'] using pair_x c root
    exact by_contra fun hz ↦
      (hB _ hz).ne' (sesquilinear_aeval_eq_zero_of_eigen adj' eigen_z orth_x (D c))
  intro d hd k R hroot hP
  have kills_x : aeval U R (T 0) = 0 := aeval_cofactor_eq_zero hq aeval_P two_roots hd k R hroot hP
  refine aeval_conj_eq_zero hB adj (fun j ↦ ?_) (U'_first.trans (smul_smul _ _ _)) rec_U'
  simpa [aeval_p j.val j.is_le, kills_x, q_ne] using
    congrArg (aeval U · (T 0))
      (mul_comm R (glnHeckePolynomial j.val (q : ℂ) fun i ↦ t ⟨i, by omega⟩))

end RootChain

section RootSymmetry

/-- Root symmetry of a `GL_N` Hecke polynomial under Hermitian coefficient duality:
if `star (t d) * b₀ = t d.rev * z` with `b₀ ≠ 0` and `q ≠ 0`, then `P(y') = 0` and
`star y * y' * q = q ^ N` imply `P(y) = 0`. -/
theorem isRoot_of_glnHeckePolynomial_star_mul_eq {N : ℕ} {q : ℝ} {t : Fin (N + 1) → ℂ}
    {b₀ z y y' : ℂ} (hq : q ≠ 0) (hb₀ : b₀ ≠ 0)
    (h_dual : ∀ d : Fin (N + 1), star (t d) * b₀ = t d.rev * z)
    (hy : star y * y' * (q : ℂ) = (q : ℂ) ^ N)
    (hy' : (glnHeckePolynomial N (q : ℂ) t).IsRoot y') :
    (glnHeckePolynomial N (q : ℂ) t).IsRoot y := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  set P := glnHeckePolynomial N (q : ℂ) t
  have h_star_eval :
      star (P.eval y) * (b₀ * (q : ℂ) ^ N.choose 2) = (-star y) ^ N * z * P.eval y' := by
    simp only [P, glnHeckePolynomial_def, eval_finsetSum, mul_sum, star_sum, sum_mul]
    conv_rhs => rw [← Equiv.sum_comp Fin.revPerm]
    refine sum_congr rfl fun d _ ↦ mul_right_cancel₀ (pow_ne_zero d.val hqC) ?_
    have hN : N = d.val + d.rev.val := by simp [Fin.val_rev]; omega
    have h_exp : N.choose 2 + d.val.choose 2 + d.val = d.rev.val.choose 2 + N * d.val := by
      have h2a : ∀ a : ℕ, 2 * a.choose 2 + a = a * a := fun a ↦ by
        induction a with
        | zero => simp
        | succ k ih => simp [Nat.choose_succ_succ]; linarith
      have hadd := Nat.add_choose_two d.val d.rev.val
      have hsq := h2a d.val
      have hNc : N.choose 2 = (d.val + d.rev.val).choose 2 := congrArg (·.choose 2) hN
      have hNm : N * d.val = (d.val + d.rev.val) * d.val := congrArg (· * d.val) hN
      nlinarith
    have hsub1 : N - d.val = d.rev.val := by omega
    have hsub2 : N - d.rev.val = d.val := by omega
    calc
      _ = (-1) ^ d.val * star y ^ d.rev.val * (star (t d) * b₀) *
            (q : ℂ) ^ (N.choose 2 + d.val.choose 2 + d.val) := by
        simp only [eval_mul, eval_C, eval_pow, eval_X, star_mul', star_pow, Complex.star_def,
          Complex.conj_ofReal, map_neg, map_one, hsub1]
        rw [pow_add, pow_add]
        ring
      _ = (-1) ^ d.val * star y ^ d.rev.val * (t d.rev * z) *
            ((q : ℂ) ^ d.rev.val.choose 2 * (star y * y' * (q : ℂ)) ^ d.val) := by
        rw [h_dual d, h_exp, hy, pow_add, pow_mul]
      _ = _ := by
        have h_sign : (-1 : ℂ) ^ d.rev.val * (-1) ^ d.rev.val = 1 := by simp [← mul_pow]
        have hneg : (-star y) ^ N = (-1) ^ (d.val + d.rev.val) * star y ^ (d.val + d.rev.val) := by
          calc (-star y) ^ N = (-star y) ^ (d.val + d.rev.val) := congrArg ((-star y) ^ ·) hN
            _ = (-1) ^ (d.val + d.rev.val) * star y ^ (d.val + d.rev.val) := neg_pow (star y) _
        simp only [Fin.revPerm_apply, eval_mul, eval_C, eval_pow, eval_X, hsub2, hneg]
        linear_combination -((-1) ^ d.val * star y ^ (d.val + d.rev.val) * t d.rev * z *
          (q : ℂ) ^ d.rev.val.choose 2 * y' ^ d.val * (q : ℂ) ^ d.val) * h_sign
  simpa [hy'.eq_zero, hqC, hb₀] using h_star_eval

/-- Root-chain propagation for a `GL_N` Hecke polynomial: combining the top-root lower bound with
Hermitian coefficient duality, any root `c` satisfying `‖c‖ ^ 2 * q ^ k = q ^ N` generates the
full chain of roots `c * q ^ i` for `i < k`. -/
theorem isRoot_mul_pow_of_norm_sq_mul_pow_eq {N k : ℕ} {q : ℝ} {t : Fin (N + 1) → ℂ}
    {b₀ z c : ℂ} (hq : 1 < q) (hb₀ : b₀ ≠ 0)
    (h_dual : ∀ d : Fin (N + 1), star (t d) * b₀ = t d.rev * z)
    (h_top : ∀ r : ℂ, (glnHeckePolynomial N (q : ℂ) t).IsRoot r →
      ¬ (glnHeckePolynomial N (q : ℂ) t).IsRoot ((q : ℂ) * r) → q ^ N / q ^ 2 ≤ ‖r‖ ^ 2)
    (hc : (glnHeckePolynomial N (q : ℂ) t).IsRoot c)
    (h_norm : ‖c‖ ^ 2 * q ^ k = q ^ N) {i : ℕ} (hi : i < k) :
    (glnHeckePolynomial N (q : ℂ) t).IsRoot (c * (q : ℂ) ^ i) := by
  have hq0 : q ≠ 0 := (zero_lt_one.trans hq).ne'
  induction i using Nat.strongRec with | ind i ih => ?_
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, i + 1 + j = k := Nat.le.dest hi
  obtain hji | hij : j < i ∨ i ≤ j := lt_or_ge j i
  · refine isRoot_of_glnHeckePolynomial_star_mul_eq hq0 hb₀ h_dual ?_ (ih j hji (by omega))
    have hC : (‖c‖ : ℂ) ^ 2 * (q : ℂ) ^ (i + 1 + j) = (q : ℂ) ^ N := by exact_mod_cast h_norm
    have hcm : (starRingEnd ℂ) c * c = (‖c‖ : ℂ) ^ 2 := Complex.conj_mul' c
    rw [← hC]
    simp only [star_mul', star_pow, Complex.star_def, Complex.conj_ofReal]
    linear_combination (q : ℂ) ^ (i + 1 + j) * hcm
  · obtain _ | i := i
    · simpa using hc
    by_contra h_not
    have h_not' : ¬ (glnHeckePolynomial N (q : ℂ) t).IsRoot ((q : ℂ) * (c * (q : ℂ) ^ i)) := by
      rwa [show (q : ℂ) * (c * (q : ℂ) ^ i) = c * (q : ℂ) ^ (i + 1) by ring]
    have h_prev := ih i (Nat.lt_succ_self i) (by omega)
    have h_big := h_top (c * (q : ℂ) ^ i) h_prev h_not'
    have hq_pos : 0 < q := zero_lt_one.trans hq
    rw [div_le_iff₀ (sq_pos_of_pos hq_pos), norm_mul, norm_pow,
      Complex.norm_real, Real.norm_of_nonneg hq_pos.le] at h_big
    have h_pow : q ^ N * q ^ (i + 1 + 1 + j) ≤ q ^ N * q ^ (2 * i + 2) := by
      calc q ^ N * q ^ (i + 1 + 1 + j)
          ≤ (‖c‖ * q ^ i) ^ 2 * q ^ 2 * q ^ (i + 1 + 1 + j) := by gcongr
        _ = (‖c‖ ^ 2 * q ^ (i + 1 + 1 + j)) * q ^ (2 * i + 2) := by ring
        _ = q ^ N * q ^ (2 * i + 2) := by rw [h_norm]
    have h_exp : i + 1 + 1 + j ≤ 2 * i + 2 :=
      (pow_le_pow_iff_right₀ hq).mp (le_of_mul_le_mul_left h_pow (pow_pos hq_pos N))
    omega

end RootSymmetry

end TauCeti
