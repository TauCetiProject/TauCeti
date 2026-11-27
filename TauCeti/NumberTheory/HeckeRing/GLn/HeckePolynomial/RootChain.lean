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
import TauCeti.LinearAlgebra.SesquilinearForm.Complex
import TauCeti.LinearAlgebra.SesquilinearForm.Polynomial

/-!
# Root chains of `GL n` Hecke polynomials

This file isolates the linear-algebraic and polynomial core of the root-chain lemma for
spherical Hecke polynomials of `GL_N` in unitary representations (cf. Tadić's classification of
the unitary dual and Bernstein's inequality at the ends of segments).

Given a positive-definite sesquilinear form `B` on a complex vector space `V`, an endomorphism
`U : Module.End ℂ V` with left adjoint `U'`, a real scale `q > 1`, and vectors `T₀, …, Tₙ`
satisfying the two hyperplane-count recursions attached to
`P = glnHeckePolynomial (n + 1) (q : ℂ) t`:

* `Module.End.div_sq_le_norm_sq_of_isRoot_glnHeckePolynomial`: every root `c` of `P` such that
  `q * c` is not a root satisfies `q ^ (n + 1) / q ^ 2 ≤ ‖c‖ ^ 2`.
* `Module.End.aeval_map_starRingEnd_apply_eq_zero_of_isRoot_glnHeckePolynomial`: if `d ≠ 0`,
  `q ^ k / d` is a root of `P`, and `P = (∏ i < k, (C d * X - C (q ^ i))) * R`, then
  `aeval U' (R.map (starRingEnd ℂ)) (T 0) = 0`.
* `TauCeti.isRoot_of_glnHeckePolynomial_star_mul_eq` derives the root symmetry
  `y ↦ q ^ (N - 1) / star y` from coefficient duality `star (t d) * b₀ = t d.rev * z`.
* `TauCeti.isRoot_mul_pow_of_norm_sq_mul_pow_eq` combines that root symmetry with the top-root
  lower bound: any root `c` with `‖c‖ ^ 2 * q ^ k = q ^ N` generates the full root chain
  `c, c * q, …, c * q ^ (k - 1)`.

## Main declarations

* `Module.End.div_sq_le_norm_sq_of_isRoot_glnHeckePolynomial`
* `Module.End.aeval_map_starRingEnd_apply_eq_zero_of_isRoot_glnHeckePolynomial`
* `TauCeti.isRoot_of_glnHeckePolynomial_star_mul_eq`
* `TauCeti.isRoot_mul_pow_of_norm_sq_mul_pow_eq`
-/

public section

open ComplexOrder Finset Module Polynomial TauCeti

section RootChain

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Applying `glnHeckePolynomial (m + 1)` at `U` unfolds via `glnHeckePolynomial_succ`. -/
private lemma aeval_glnHeckePolynomial_succ_apply (U : End ℂ V) (m : ℕ) (q : ℂ)
    (T : Fin (m + 2) → ℂ) (y : V) :
    aeval U (glnHeckePolynomial (m + 1) q T) y =
      U (aeval U (glnHeckePolynomial m q (T ∘ Fin.castSucc)) y) +
        ((-1) ^ (m + 1) * q ^ (m + 1).choose 2 * T (Fin.last (m + 1))) • y := by
  rw [glnHeckePolynomial_succ]
  simp only [map_add, LinearMap.add_apply, map_mul, aeval_X, mul_apply_eq_comp,
    aeval_C, Module.algebraMap_end_apply, smul_smul, ← mul_assoc, Function.comp_def]

/-- `Fin.castLE` sends `Fin.last k` to `⟨k, h⟩`. -/
private lemma castLE_last {k m : ℕ} (h : k + 1 ≤ m) :
    Fin.castLE h (Fin.last k) = ⟨k, h⟩ :=
  Fin.ext (by simp)

/-- For real `q > 1`, `0 < (q : ℂ) ^ (n + 1) - 1`. -/
private lemma pow_succ_sub_one_pos {q : ℝ} (hq : 1 < q) (n : ℕ) :
    (0 : ℂ) < (q : ℂ) ^ (n + 1) - 1 :=
  sub_pos.mpr (one_lt_pow₀ (by exact_mod_cast hq) n.succ_ne_zero)

/-- If `P (U)` kills `y` and `(P / (X - c)) (U)` still kills `y` whenever `c ≠ 0` and `q * c` are
both roots of `P`, then any geometric chain `q ^ i / d` (`i < k`) ending below a root `q ^ k / d`
cancels from `P`. -/
private lemma aeval_apply_eq_zero_of_eq_prod_mul {U : End ℂ V} {y : V} {P : ℂ[X]} {q : ℝ} {d : ℂ}
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
    have cancel : (X - C ((q : ℂ) ^ k / d)) * (d • Q * R) = P := by
      rw [hP, smul_eq_C_mul]
      have h1 : (X - C ((q : ℂ) ^ k / d)) * C d = C d * X - C ((q : ℂ) ^ k) := by
        rw [sub_mul, ← map_mul, div_mul_cancel₀ _ hd, mul_comm X]
      linear_combination (Q * R) * h1
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
  rw [B.apply_aeval_map_starRingEnd_apply adj R, kills_span _ 0, map_zero]

/-- Prefix evaluation of `glnHeckePolynomial` at `U` along the `U`-recursion. -/
private lemma aeval_glnHeckePolynomial_prefix {U : End ℂ V} {n : ℕ} {q : ℂ} {t : Fin (n + 2) → ℂ}
    {T : Fin (n + 1) → V} (ht_zero : t 0 • T 0 = T 0)
    (rec_U : ∀ j : Fin n,
      U (T j.castSucc) = q ^ (j : ℕ) • (t j.succ.castSucc • T 0 - T j.succ))
    (m : ℕ) (hm : m ≤ n) :
    aeval U (glnHeckePolynomial m q (t ∘ Fin.castLE (by omega))) (T 0) =
      ((-1) ^ m * q ^ m.choose 2) • T ⟨m, by omega⟩ := by
  induction m with
  | zero => simpa [glnHeckePolynomial_zero] using ht_zero
  | succ m ih =>
    have hm_lt : m < n := by omega
    have hrec : U (T ⟨m, by omega⟩) =
        q ^ m • (t ⟨m + 1, by omega⟩ • T 0 - T ⟨m + 1, by omega⟩) := by
      simpa [Fin.castSucc_mk, Fin.succ_mk] using rec_U ⟨m, hm_lt⟩
    rw [aeval_glnHeckePolynomial_succ_apply, Function.comp_assoc, Fin.castLE_comp_castSucc,
      ih hm_lt.le, map_smul, hrec]
    simp only [Function.comp_apply, castLE_last, Nat.choose_succ_succ, Nat.choose_one_right]
    module

/-- Action of `U'` on the quotient of a prefix Hecke polynomial by `X - c`. -/
private lemma exists_mul_eq_sub_eval_and_apply {U U' : End ℂ V} {n : ℕ} {q : ℂ}
    {t : Fin (n + 2) → ℂ} {T : Fin (n + 1) → V} (hq : q ≠ 0) (ht_last : t (Fin.last (n + 1)) ≠ 0)
    (rec_U' : ∀ i : Fin n,
      U' (T i.succ) =
        q ^ (n - (i : ℕ) - 1) • ((t i.succ.castSucc / q ^ n) • U' (T 0) - T i.castSucc))
    (U'_first : U' (T 0) = q ^ n • (t (Fin.last (n + 1)))⁻¹ • T (Fin.last n))
    (aeval_p : ∀ (m : ℕ) (hm : m ≤ n),
      aeval U (glnHeckePolynomial m q (t ∘ Fin.castLE (by omega))) (T 0) =
        ((-1) ^ m * q ^ m.choose 2) • T ⟨m, by omega⟩)
    (aeval_top : aeval U (glnHeckePolynomial (n + 1) q t) (T 0) = 0)
    (m : ℕ) (hm : m ≤ n + 1) (c : ℂ) :
    let Pm : ℂ[X] := glnHeckePolynomial m q (t ∘ Fin.castLE (by omega))
    ∃ D : ℂ[X], (X - C c) * D = Pm - C (Pm.eval c) ∧
      U' (aeval U (c • D + Pm) (T 0)) =
        (Pm.eval (q * c) / q ^ m) • U' (T 0) + (q ^ n / q) • aeval U D (T 0) := by
  induction m with
  | zero => exact ⟨0, by simp [glnHeckePolynomial_zero]⟩
  | succ m ih =>
    obtain ⟨D, hD, hU'⟩ := ih (Nat.lt_of_succ_le hm).le
    have hstep := glnHeckePolynomial_succ m q (t ∘ Fin.castLE (by omega : m + 2 ≤ n + 2))
    have hcomp : (fun i : Fin (m + 1) ↦ (t ∘ Fin.castLE (by omega : m + 2 ≤ n + 2)) i.castSucc) =
        t ∘ Fin.castLE (by omega) := funext fun i ↦ by simp
    rw [hcomp] at hstep
    refine ⟨c • D + glnHeckePolynomial m q (t ∘ Fin.castLE (by omega)), ?_, ?_⟩
    · rw [hstep]
      have h_poly :
          (X - C c) * (C c * D + glnHeckePolynomial m q (t ∘ Fin.castLE (by omega))) =
            X * glnHeckePolynomial m q (t ∘ Fin.castLE (by omega)) -
              C c * C ((glnHeckePolynomial m q (t ∘ Fin.castLE (by omega))).eval c) := by
        linear_combination C c * hD
      simpa [smul_eq_C_mul] using h_poly
    · rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, map_add, map_smul, hU']
      rcases eq_or_lt_of_le (Nat.le_of_succ_le_succ hm) with hmn | hmlt
      · subst hmn
        have htop : aeval U (glnHeckePolynomial (m + 1) q (t ∘ Fin.castLE le_rfl)) (T 0) = 0 := by
          simpa using aeval_top
        have hT_last : T (Fin.last m) = (q ^ m)⁻¹ • t (Fin.last (m + 1)) • U' (T 0) := by
          rw [U'_first]
          have h1 : (q ^ m)⁻¹ * t (Fin.last (m + 1)) * q ^ m * (t (Fin.last (m + 1)))⁻¹ = 1 := by
            field_simp [hq, ht_last]
          simp only [smul_smul, ← mul_assoc, h1, one_smul]
        rw [htop, hstep]
        simp only [map_zero, add_zero, eval_add, eval_mul, eval_X, eval_C, map_add,
          LinearMap.add_apply, map_smul, LinearMap.smul_apply, Nat.choose_succ_succ,
          Nat.choose_one_right, Function.comp_apply, Fin.castLE_refl]
        have hlast_m : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
        rw [aeval_p m le_rfl, hlast_m, hT_last]
        match_scalars <;> field
      · have hrec : U' (T ⟨m + 1, by omega⟩) =
            q ^ (n - m - 1) • ((t ⟨m + 1, by omega⟩ / q ^ n) • U' (T 0) - T ⟨m, by omega⟩) := by
          simpa [Fin.castSucc_mk, Fin.succ_mk] using rec_U' ⟨m, hmlt⟩
        have hexp : n - m - 1 + (m + 1) = n := by omega
        have hpow : q ^ (n - m - 1) = q ^ n / q ^ (m + 1) := by
          rw [eq_div_iff (pow_ne_zero _ hq), ← pow_add, hexp]
        rw [aeval_p (m + 1) hmlt, hstep]
        simp only [map_smul, eval_add, eval_mul, eval_X, eval_C, map_add, LinearMap.add_apply,
          LinearMap.smul_apply, Nat.choose_succ_succ, Nat.choose_one_right, Function.comp_apply,
          castLE_last]
        rw [hrec, hpow, aeval_p m hmlt.le]
        match_scalars <;> field

/-- Pairing estimate behind `div_sq_le_norm_sq_of_isRoot_glnHeckePolynomial`. -/
private lemma le_norm_sq_of_pairing {B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ} {U U' : End ℂ V}
    {x z : V} {c a : ℂ} {q : ℝ} {n : ℕ} (hB : ∀ f ≠ (0 : V), 0 < B f f)
    (adj : ∀ y w : V, B (U' y) w = B y (U w)) (hq : 1 < q) (hx_ne : x ≠ 0) (ha : a ≠ 0)
    (U_z : U z = c • z)
    (U'_z : c • U' z = (a / (q : ℂ) ^ (n + 1)) • U' x + ((q : ℂ) ^ n / q) • z)
    (pair_x : c * B x z * ((q : ℂ) ^ (n + 1) - 1) = a * B x x) :
    q ^ (n + 1) / q ^ 2 ≤ ‖c‖ ^ 2 := by
  have pow_sub_pos := pow_succ_sub_one_pos hq n
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
  have : (0 : ℂ) < (q : ℂ) := by exact_mod_cast zero_lt_one.trans hq
  have gap_nonneg : (0 : ℂ) ≤ ((‖c‖ ^ 2 : ℂ) - (q : ℂ) ^ (n + 1) / (q : ℂ) ^ 2) :=
    gap.ge.trans' (by positivity)
  exact Complex.real_le_real.mp (by simpa using gap_nonneg)

/-- Pairing `U' x` with `c • U' z` yields `c * B x z * (q ^ (n + 1) - 1) = a * B x x`. -/
private lemma mul_pair_eq_of_adjoint {B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ} {U U' : End ℂ V}
    {n : ℕ} {q : ℝ} {x z : V} {c a : ℂ} (hq : 1 < q)
    (adj : ∀ y w : V, B (U' y) w = B y (U w)) (adj' : ∀ y w : V, B (U y) w = B y (U' w))
    (hUU' : U (U' x) = ((q : ℂ) ^ n * (q : ℂ) ^ n) • x) (U_z : U z = c • z)
    (U'_z : c • U' z = (a / (q : ℂ) ^ (n + 1)) • U' x + ((q : ℂ) ^ n / q) • z) :
    c * B x z * ((q : ℂ) ^ (n + 1) - 1) = a * B x x := by
  have q_ne : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq).ne'
  have pair_U' (y : V) : B (U' x) (U' y) = (q : ℂ) ^ n * (q : ℂ) ^ n * B x y := by
    rw [← adj', hUU']
    simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, map_mul, map_pow, Complex.conj_ofReal]
  have paired : B (U' x) (c • U' z) =
      B (U' x) ((a / (q : ℂ) ^ (n + 1)) • U' x + ((q : ℂ) ^ n / q) • z) := by rw [U'_z]
  simp only [map_add, map_smul, pair_U', adj _ z, U_z, smul_eq_mul] at paired
  linear_combination (norm := field) (q : ℂ) / (q : ℂ) ^ n * paired

/-- If `c ≠ 0` and `q * c` are both roots of `P`, then `(P / (X - c)) (U)` kills `T 0`. -/
private lemma aeval_quot_eq_zero_of_two_roots {B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ}
    {U U' : End ℂ V} {n : ℕ} {q : ℝ} {P D F : ℂ[X]} {x : V} {c : ℂ}
    (hB : ∀ f ≠ (0 : V), 0 < B f f) (adj' : ∀ a y : V, B (U a) y = B a (U' y))
    (hq : 1 < q) (hD : (X - C c) * D = P - C (P.eval c)) (hF : (X - C c) * F = P)
    (hqc : P.IsRoot ((q : ℂ) * c)) (hc : c ≠ 0)
    (U'_z : c • U' (aeval U D x) =
      (P.eval ((q : ℂ) * c) / (q : ℂ) ^ (n + 1)) • U' x + ((q : ℂ) ^ n / q) • aeval U D x)
    (pair_x : c * B x (aeval U D x) * ((q : ℂ) ^ (n + 1) - 1) = P.eval ((q : ℂ) * c) * B x x) :
    aeval U F x = 0 := by
  have pow_sub_pos := pow_succ_sub_one_pos hq n
  have root : P.IsRoot c := by simp [← hF]
  obtain rfl : F = D := mul_left_cancel₀ (X_sub_C_ne_zero c) (by simp [hF, hD, root.eq_zero])
  have eigen_z : U' (aeval U F x) = (c⁻¹ * ((q : ℂ) ^ n / q)) • aeval U F x := by
    rw [← smul_smul]; exact (eq_inv_smul_iff₀ hc).mpr (by simpa [hqc.eq_zero] using U'_z)
  have orth_x : B x (aeval U F x) = 0 := by
    simpa [hqc.eq_zero, hc, pow_sub_pos.ne'] using pair_x
  have hF_conj : (F.map (starRingEnd ℂ)).map (starRingEnd ℂ) = F := by
    rw [Polynomial.map_map]; simp
  have hself : B (aeval U ((F.map (starRingEnd ℂ)).map (starRingEnd ℂ)) x) (aeval U F x) = 0 := by
    rw [B.apply_aeval_map_starRingEnd_apply adj',
      Module.End.aeval_apply_of_mem_apply_eq_smul eigen_z, map_smul, orth_x, smul_zero]
  rw [hF_conj] at hself
  exact by_contra fun hz ↦ (hB _ hz).ne' hself

/-- Shared pairing and two-root vanishing setup for the `GL_N` Hecke polynomial adjoint lemma. -/
private lemma glnHeckePolynomial_adjoint_core {B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ}
    (U U' : End ℂ V) {n : ℕ} {q : ℝ} {t : Fin (n + 2) → ℂ} (T : Fin (n + 1) → V)
    (hB : ∀ f ≠ (0 : V), 0 < B f f) (adj : ∀ a y : V, B (U' a) y = B a (U y))
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
  have hB_symm : B.IsSymm := (LinearMap.IsNonneg.mk fun x ↦ by
    by_cases hx : x = 0 <;> [simp [hx]; exact (hB x hx).le]).isSymm
  have adj' (a y : V) : B (U a) y = B a (U' y) := by rw [← hB_symm.eq, ← adj y a, hB_symm.eq]
  have q_ne : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq).ne'
  have aeval_p := aeval_glnHeckePolynomial_prefix ht_zero rec_U
  have aeval_P : aeval U P (T 0) = 0 := by
    have hcast : t ∘ Fin.castSucc = t ∘ Fin.castLE (by omega) :=
      funext fun i ↦ congrArg t (Fin.ext (by simp))
    have hlast : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp)
    dsimp only [P]
    rw [aeval_glnHeckePolynomial_succ_apply, hcast, aeval_p n le_rfl, hlast, map_smul, U_last]
    simp only [Nat.choose_succ_succ, Nat.choose_one_right]; module
  choose D hD hU' using fun c : ℂ ↦
    exists_mul_eq_sub_eval_and_apply q_ne ht_last rec_U' U'_first aeval_p aeval_P (n + 1) le_rfl c
  have hUU' : U (U' (T 0)) = ((q : ℂ) ^ n * (q : ℂ) ^ n) • T 0 := by
    rw [U'_first, map_smul, map_smul, U_last, smul_smul, smul_smul, smul_smul]
    congr 1; field_simp [ht_last]
  have U'_z (c : ℂ) : c • U' (aeval U (D c) (T 0)) =
      (P.eval ((q : ℂ) * c) / (q : ℂ) ^ (n + 1)) • U' (T 0) +
        ((q : ℂ) ^ n / q) • aeval U (D c) (T 0) := by simpa [P, aeval_P] using hU' c
  have U_z (c : ℂ) (hc : P.IsRoot c) : U (aeval U (D c) (T 0)) = c • aeval U (D c) (T 0) := by
    simpa [P, aeval_P, hc.eq_zero, sub_eq_zero] using congrArg (aeval U · (T 0)) (hD c)
  have pair_x (c : ℂ) (hc : P.IsRoot c) :=
    mul_pair_eq_of_adjoint hq adj adj' hUU' (U_z c hc) (U'_z c)
  refine ⟨fun c hc hqc ↦
    le_norm_sq_of_pairing hB adj hq hT_ne hqc (U_z c hc) (U'_z c) (pair_x c hc), ?_⟩
  have two_roots {c : ℂ} (F : ℂ[X]) (hF : (X - C c) * F = P) (hqc : P.IsRoot ((q : ℂ) * c))
      (hc : c ≠ 0) : aeval U F (T 0) = 0 :=
    aeval_quot_eq_zero_of_two_roots hB adj' hq (by simpa [P] using hD c) hF hqc hc (U'_z c)
      (pair_x c (by simp [← hF]))
  intro d hd k R hroot hP
  have kills_x : aeval U R (T 0) = 0 :=
    aeval_apply_eq_zero_of_eq_prod_mul hq aeval_P two_roots hd k R hroot hP
  refine aeval_conj_eq_zero hB adj (fun j ↦ ?_) (U'_first.trans (smul_smul _ _ _)) rec_U'
  set Pj := glnHeckePolynomial j.val (q : ℂ) (t ∘ Fin.castLE (by omega))
  have hcomm : aeval U R (aeval U Pj (T 0)) = aeval U Pj (aeval U R (T 0)) := by
    rw [← mul_apply_eq_comp, ← map_mul, mul_comm, map_mul, mul_apply_eq_comp]
  have haeval_j : aeval U Pj (T 0) = ((-1) ^ j.val * (q : ℂ) ^ j.val.choose 2) • T j := by
    simpa [Pj, Fin.eta] using aeval_p j.val j.is_le
  have hscalar_ne : (-1 : ℂ) ^ j.val * (q : ℂ) ^ j.val.choose 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ q_ne)
  rw [haeval_j, map_smul, kills_x, map_zero] at hcomm
  exact (smul_eq_zero_iff_right hscalar_ne).mp hcomm

/-- **Top-root lower bound for `GL_N` Hecke polynomials.** Let `B` be a positive-definite
sesquilinear form on `V`, `U'` left-adjoint to `U` for `B`, `q > 1` real,
`P = glnHeckePolynomial (n + 1) (q : ℂ) t`, and `T : Fin (n + 1) → V` satisfying the forward and
backward hyperplane-count recursions. Then every root `c` of `P` such that `q * c` is not a root
satisfies `q ^ (n + 1) / q ^ 2 ≤ ‖c‖ ^ 2`. -/
theorem Module.End.div_sq_le_norm_sq_of_isRoot_glnHeckePolynomial
    {B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ}
    (U U' : End ℂ V) {n : ℕ} {q : ℝ} {t : Fin (n + 2) → ℂ} (T : Fin (n + 1) → V)
    (hB : ∀ f ≠ (0 : V), 0 < B f f) (adj : ∀ a y : V, B (U' a) y = B a (U y))
    (hq : 1 < q) (hT_ne : T 0 ≠ 0) (ht_zero : t 0 • T 0 = T 0)
    (ht_last : t (Fin.last (n + 1)) ≠ 0)
    (rec_U : ∀ j : Fin n,
      U (T j.castSucc) = (q : ℂ) ^ (j : ℕ) • (t j.succ.castSucc • T 0 - T j.succ))
    (rec_U' : ∀ i : Fin n,
      U' (T i.succ) =
        (q : ℂ) ^ (n - (i : ℕ) - 1) •
          ((t i.succ.castSucc / (q : ℂ) ^ n) • U' (T 0) - T i.castSucc))
    (U'_first : U' (T 0) = (q : ℂ) ^ n • (t (Fin.last (n + 1)))⁻¹ • T (Fin.last n))
    (U_last : U (T (Fin.last n)) = (q : ℂ) ^ n • t (Fin.last (n + 1)) • T 0)
    {c : ℂ} (hc : (glnHeckePolynomial (n + 1) (q : ℂ) t).IsRoot c)
    (hqc : ¬ (glnHeckePolynomial (n + 1) (q : ℂ) t).IsRoot ((q : ℂ) * c)) :
    q ^ (n + 1) / q ^ 2 ≤ ‖c‖ ^ 2 :=
  (glnHeckePolynomial_adjoint_core U U' T hB adj hq hT_ne ht_zero ht_last rec_U rec_U'
    U'_first U_last).1 c hc hqc

/-- **Chain cancellation for `GL_N` Hecke polynomials.** Under the same adjoint-recursion
hypotheses as `Module.End.div_sq_le_norm_sq_of_isRoot_glnHeckePolynomial`, if `d ≠ 0`, `q ^ k / d`
is a root of `P = glnHeckePolynomial (n + 1) (q : ℂ) t`, and
`P = (∏ i < k, (C d * X - C (q ^ i))) * R`, then `aeval U' (R.map (starRingEnd ℂ)) (T 0) = 0`. -/
theorem Module.End.aeval_map_starRingEnd_apply_eq_zero_of_isRoot_glnHeckePolynomial
    {B : V →ₛₗ[starRingEnd ℂ] V →ₗ[ℂ] ℂ}
    (U U' : End ℂ V) {n : ℕ} {q : ℝ} {t : Fin (n + 2) → ℂ} (T : Fin (n + 1) → V)
    (hB : ∀ f ≠ (0 : V), 0 < B f f) (adj : ∀ a y : V, B (U' a) y = B a (U y))
    (hq : 1 < q) (ht_zero : t 0 • T 0 = T 0)
    (ht_last : t (Fin.last (n + 1)) ≠ 0)
    (rec_U : ∀ j : Fin n,
      U (T j.castSucc) = (q : ℂ) ^ (j : ℕ) • (t j.succ.castSucc • T 0 - T j.succ))
    (rec_U' : ∀ i : Fin n,
      U' (T i.succ) =
        (q : ℂ) ^ (n - (i : ℕ) - 1) •
          ((t i.succ.castSucc / (q : ℂ) ^ n) • U' (T 0) - T i.castSucc))
    (U'_first : U' (T 0) = (q : ℂ) ^ n • (t (Fin.last (n + 1)))⁻¹ • T (Fin.last n))
    (U_last : U (T (Fin.last n)) = (q : ℂ) ^ n • t (Fin.last (n + 1)) • T 0)
    {d : ℂ} (hd : d ≠ 0) (k : ℕ) (R : ℂ[X])
    (hroot : (glnHeckePolynomial (n + 1) (q : ℂ) t).IsRoot ((q : ℂ) ^ k / d))
    (hP : glnHeckePolynomial (n + 1) (q : ℂ) t =
      (∏ i ∈ range k, (C d * X - C ((q : ℂ) ^ i))) * R) :
    aeval U' (R.map (starRingEnd ℂ)) (T 0) = 0 := by
  by_cases hT_ne : T 0 = 0
  · simp [hT_ne]
  · exact (glnHeckePolynomial_adjoint_core U U' T hB adj hq hT_ne ht_zero ht_last rec_U rec_U'
      U'_first U_last).2 d hd k R hroot hP

end RootChain

namespace TauCeti

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
  cases N with
  | zero =>
    have ht0 : t 0 = 0 := by simpa [glnHeckePolynomial_zero] using hy'
    simpa [glnHeckePolynomial_zero] using ht0
  | succ n =>
    set P := glnHeckePolynomial (n + 1) (q : ℂ) t
    set P_rev := glnHeckePolynomial (n + 1) (q : ℂ) (fun d ↦ t d.rev)
    have hy_prod : star y * y' = (q : ℂ) ^ n :=
      mul_right_cancel₀ hqC (by simpa [pow_succ] using hy)
    have hy'_ne : y' ≠ 0 := fun h0 ↦ pow_ne_zero n hqC (by simpa [h0] using hy_prod.symm)
    have h_arg : (q : ℂ) ^ n * y'⁻¹ = star y := by
      rw [← hy_prod, mul_inv_cancel_right₀ hy'_ne]
    have h_refl := congrArg (eval y'⁻¹) (C_mul_glnHeckePolynomial_rev_comp (q : ℂ) t)
    have h_eval_refl : eval y'⁻¹ (reflect (n + 1) P) = 0 := by
      have : Invertible y' := invertibleOfNonzero hy'_ne
      have h := (eval₂_reflect_eq_zero_iff (RingHom.id ℂ) y' (n + 1) P
        (natDegree_glnHeckePolynomial_le _ _)).mpr hy'.eq_zero
      rw [invOf_eq_inv] at h
      exact h
    have hP_rev_zero : P_rev.eval (star y) = 0 := by
      dsimp only [P, P_rev] at h_eval_refl ⊢
      simp only [eval_mul, eval_C, eval_comp, eval_X, Nat.add_sub_cancel, h_arg, h_eval_refl,
        mul_zero] at h_refl
      have hc_ne : (-1 : ℂ) ^ (n + 1) * (q : ℂ) ^ (n + 1).choose 2 ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ hqC)
      exact (mul_eq_zero.mp h_refl).resolve_left hc_ne
    have h_conj_eq : C b₀ * P.map (starRingEnd ℂ) = C z * P_rev := by
      simp only [P, P_rev, glnHeckePolynomial_def, Polynomial.map_sum, Polynomial.map_mul,
        Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, Polynomial.map_neg,
        Polynomial.map_one, map_mul, map_pow, map_neg, map_one, Complex.conj_ofReal,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun d _ ↦ ?_
      have hd : C (starRingEnd ℂ (t d)) * C b₀ = C (t d.rev) * C z := by
        simpa [← map_mul, Complex.star_def] using congrArg C (h_dual d)
      linear_combination (-1) ^ (d : ℕ) * C (q : ℂ) ^ (d : ℕ).choose 2 *
        X ^ (n + 1 - (d : ℕ)) * hd
    have h_eval_conj : b₀ * star (P.eval y) = 0 := by
      have h := congrArg (eval (star y)) h_conj_eq
      rw [eval_mul, eval_C, eval_mul, eval_C, hP_rev_zero, mul_zero, eval_map] at h
      have hstar : star (P.eval y) = P.eval₂ (starRingEnd ℂ) (star y) := by simp
      rwa [← hstar] at h
    exact star_eq_zero.mp ((mul_eq_zero.mp h_eval_conj).resolve_left hb₀)

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
    have hmul_eq : (q : ℂ) * (c * (q : ℂ) ^ i) = c * (q : ℂ) ^ (i + 1) := by ring
    have h_not' : ¬ (glnHeckePolynomial N (q : ℂ) t).IsRoot ((q : ℂ) * (c * (q : ℂ) ^ i)) := by
      rwa [hmul_eq]
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
