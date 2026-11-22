/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Kontsevich's finite polylogarithm and the residue dilogarithm

For a prime `p` and `n : ℤ`, Kontsevich's finite polylogarithm is the polynomial
`li_{n,p}(X) = ∑_{k=1}^{p-1} X ^ k / k ^ n` over `𝔽_p`. It satisfies
`X * li_{n,p}' = li_{n-1,p}`, and its value at `1` is the power sum `∑_{k=1}^{p-1} k ^ (-n)`,
which is `-1` when `p - 1 ∣ n` and `0` otherwise. For `p > 3` this makes `1` a double root of
the finite dilogarithm `li_{2,p}`, so `li_{2,p} = (X - 1) ^ 2 * g_p` with `g_p` of degree `p - 3`
and `g_p(1) = -1/2`.

On a field `F` over `𝔽_p`, the residue dilogarithm is `f_p(x) = li_{2,p}(x) / (x - 1) ^ p`. At the
residue `x` of a root of unity `ζ ≠ 1` of order prime to `p` in an unramified extension of `ℚ_p`,
it is the reduction modulo `p` of `p⁻² D(ζ ^ p)`, where `D` is Coleman's `p`-adic dilogarithm.
The main result is that for `p > 3` and a finite field `F` of characteristic `p`, the values of
`f_p` on `F ∖ {0, 1}` span `F` over `𝔽_p`, and so do their pairwise differences. Combined with
Nakayama's lemma, this is the residue-field input to the computation of the image of the `p`-adic
regulator on completed `K₃` of an unramified `p`-adic field.

The proof counts fibres: for `x ≠ 1` one has `f_p(x) = g_p(x) / (x - 1) ^ (p - 2)`, so each fibre
of `f_p` has at most `p - 2` points, while a proper `𝔽_p`-subspace of `F` has at most `q / p`
elements, where `q = |F|`.

## Main definitions

* `TauCeti.finitePolylog p n`: the finite polylogarithm `li_{n,p} ∈ 𝔽_p[X]`.
* `TauCeti.finiteDilogCofactor p`: the cofactor `g_p` of `(X - 1) ^ 2` in `li_{2,p}`.
* `TauCeti.residueDilogValue p x`: the residue dilogarithm `li_{2,p}(x) / (x - 1) ^ p`.

## Main results

* `TauCeti.X_mul_derivative_finitePolylog`: `X * li_{n,p}' = li_{n-1,p}`.
* `TauCeti.eval_one_finitePolylog`: `li_{n,p}(1)` is `-1` if `p - 1 ∣ n` and `0` otherwise.
* `TauCeti.sq_X_sub_one_dvd_finitePolylog_two`: `(X - 1) ^ 2 ∣ li_{2,p}` for `p > 3`.
* `TauCeti.residueDilogValue_eq_div`: `f_p(x) = g_p(x) / (x - 1) ^ (p - 2)` for `x ≠ 1`.
* `TauCeti.span_residueDilogValue_eq_top`: the values of `f_p` on `F ∖ {0, 1}` span `F`.
* `TauCeti.span_residueDilogValue_sub_eq_top`: so do their pairwise differences.

## References

* M. Kontsevich, *The `1½`-logarithm*, appendix to P. Elbaz-Vincent and H. Gangl,
  *On poly(ana)logs I*, Compositio Math. 130 (2002).
* S. Garoufalidis, P. Scholze, C. Wheeler and D. Zagier, *The Habiro ring of a number field*,
  §3.1, Propositions 3.2 and 3.3 (2024).
-/

public section

open Finset Polynomial

namespace TauCeti

variable (p : ℕ) [hp : Fact p.Prime]

/-- Kontsevich's finite polylogarithm `li_{n,p}(X) = ∑_{k=1}^{p-1} X ^ k / k ^ n` over `𝔽_p`,
for an integer index `n`. -/
noncomputable def finitePolylog (n : ℤ) : (ZMod p)[X] :=
  ∑ k ∈ Ico 1 p, C ((k : ZMod p) ^ n)⁻¹ * X ^ k

variable {p}

theorem finitePolylog_def (n : ℤ) :
    finitePolylog p n = ∑ k ∈ Ico 1 p, C ((k : ZMod p) ^ n)⁻¹ * X ^ k :=
  (rfl)

/-- The residues `1, …, p - 1` are nonzero in `𝔽_p`. -/
private lemma natCast_ne_zero_of_mem_Ico {k : ℕ} (hk : k ∈ Ico 1 p) : (k : ZMod p) ≠ 0 := by
  rw [mem_Ico] at hk
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt hk.1 hk.2

private lemma two_ne_zero_of_ne_two (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 :=
  Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])

theorem coeff_finitePolylog (n : ℤ) (k : ℕ) :
    (finitePolylog p n).coeff k = if k ∈ Ico 1 p then ((k : ZMod p) ^ n)⁻¹ else 0 := by
  simp only [finitePolylog_def, finsetSum_coeff, coeff_C_mul_X_pow]
  exact sum_ite_eq _ _ _

theorem eval_finitePolylog (n : ℤ) (x : ZMod p) :
    (finitePolylog p n).eval x = ∑ k ∈ Ico 1 p, ((k : ZMod p) ^ n)⁻¹ * x ^ k := by
  simp [finitePolylog_def, eval_finsetSum]

@[simp]
theorem eval_zero_finitePolylog (n : ℤ) : (finitePolylog p n).eval 0 = 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_finitePolylog]
  simp

/-- `X * li_{n,p}' = li_{n-1,p}`. -/
theorem X_mul_derivative_finitePolylog (n : ℤ) :
    X * derivative (finitePolylog p n) = finitePolylog p (n - 1) := by
  rw [finitePolylog_def, finitePolylog_def, derivative_sum, mul_sum]
  refine sum_congr rfl fun k hk ↦ ?_
  have hk0 := natCast_ne_zero_of_mem_Ico hk
  have hk1 : 1 ≤ k := (mem_Ico.1 hk).1
  rw [derivative_C_mul_X_pow, zpow_sub_one₀ hk0, mul_inv, inv_inv, ← mul_assoc, mul_comm X,
    mul_assoc, ← pow_succ', Nat.sub_add_cancel hk1]

/-- The finite polylogarithm has degree `p - 1`. -/
theorem natDegree_finitePolylog (n : ℤ) : (finitePolylog p n).natDegree = p - 1 := by
  have hp2 := hp.out.two_le
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_finitePolylog, ite_eq_right]
    rw [mem_Ico]
    have : p - 1 < k := by exact_mod_cast hk
    omega
  · have hmem : p - 1 ∈ Ico 1 p := by rw [mem_Ico]; omega
    rw [coeff_finitePolylog, ite_eq_left hmem]
    exact inv_ne_zero (zpow_ne_zero _ (natCast_ne_zero_of_mem_Ico hmem))

/-- The value `li_{n,p}(1) = ∑_{k=1}^{p-1} k ^ (-n)` is `-1` if `p - 1 ∣ n` and `0` otherwise. -/
theorem eval_one_finitePolylog (n : ℤ) :
    (finitePolylog p n).eval 1 = if (p : ℤ) - 1 ∣ n then -1 else 0 := by
  classical
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hd : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by push_cast [Nat.cast_sub hp1]; ring
  have hd0 : (p : ℤ) - 1 ≠ 0 := by have := hp.out.two_le; omega
  set m := ((-n) % ((p : ℤ) - 1)).toNat
  have hm' : (m : ℤ) = (-n) % ((p : ℤ) - 1) := Int.toNat_of_nonneg (Int.emod_nonneg _ hd0)
  have hunit : ∀ u : (ZMod p)ˣ, ((u : ZMod p) ^ n)⁻¹ = (u : ZMod p) ^ m := by
    intro u
    rw [← Units.val_zpow_eq_zpow_val, ← Units.val_inv_eq_inv_val, ← zpow_neg,
      zpow_eq_zpow_emod' (-n) (ZMod.units_pow_card_sub_one_eq_one p u), hd, ← hm',
      zpow_natCast, Units.val_pow_eq_pow_val]
  have hsum : ∑ k ∈ Ico 1 p, ((k : ZMod p) ^ n)⁻¹ = ∑ u : (ZMod p)ˣ, (u : ZMod p) ^ m := by
    refine sum_bij' (fun k hk ↦ Units.mk0 (k : ZMod p) (natCast_ne_zero_of_mem_Ico hk))
      (fun u _ ↦ (u : ZMod p).val) (fun _ _ ↦ mem_univ _) ?_ ?_ ?_ ?_
    · intro u _
      rw [mem_Ico]
      refine ⟨Nat.pos_of_ne_zero fun h ↦ u.ne_zero ?_, ZMod.val_lt _⟩
      rwa [ZMod.val_eq_zero] at h
    · intro k hk
      simp [ZMod.val_natCast, Nat.mod_eq_of_lt (mem_Ico.1 hk).2]
    · intro u _
      ext
      simp
    · intro k hk
      rw [← hunit, Units.val_mk0]
  rw [eval_finitePolylog]
  simp only [one_pow, mul_one]
  rw [hsum, FiniteField.sum_pow_units, ZMod.card]
  congr 1
  rw [← Int.natCast_dvd_natCast, hd, hm', Int.dvd_iff_emod_eq_zero, Int.emod_emod,
    ← Int.dvd_iff_emod_eq_zero, Int.dvd_neg]

/-- At `-1`, the finite polylogarithm of even index vanishes for odd `p`: the terms for `k` and
`p - k` cancel. -/
theorem eval_neg_one_finitePolylog (hp2 : p ≠ 2) {n : ℤ} (hn : Even n) :
    (finitePolylog p n).eval (-1) = 0 := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  rw [eval_finitePolylog]
  have hrefl : ∑ k ∈ Ico 1 p, ((k : ZMod p) ^ n)⁻¹ * (-1) ^ k =
      -∑ k ∈ Ico 1 p, ((k : ZMod p) ^ n)⁻¹ * (-1) ^ k := by
    have := sum_Ico_reflect (fun k ↦ ((k : ZMod p) ^ n)⁻¹ * (-1) ^ k) 1 (Nat.le_succ p)
    simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left] at this
    conv_lhs => rw [← this]
    rw [← sum_neg_distrib]
    refine sum_congr rfl fun k hk ↦ ?_
    have hkp : k ≤ p := (mem_Ico.1 hk).2.le
    have hpow : ((-1 : ZMod p) ^ (p - k)) * (-1) ^ k = -1 := by
      rw [← pow_add, Nat.sub_add_cancel hkp, hodd.neg_one_pow]
    rw [Nat.cast_sub hkp, ZMod.natCast_self, zero_sub, hn.neg_zpow]
    have hk : ((-1 : ZMod p) ^ k) * (-1) ^ k = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
    linear_combination ((k : ZMod p) ^ n)⁻¹ * (-1) ^ k * hpow
      - ((k : ZMod p) ^ n)⁻¹ * (-1) ^ (p - k) * hk
  have : (2 : ZMod p) * ∑ k ∈ Ico 1 p, ((k : ZMod p) ^ n)⁻¹ * (-1) ^ k = 0 := by
    linear_combination hrefl
  exact (mul_eq_zero.1 this).resolve_left (two_ne_zero_of_ne_two hp2)

/-- For `p > 3`, `1` is a double root of the finite dilogarithm `li_{2,p}`. -/
theorem sq_X_sub_one_dvd_finitePolylog_two (hp3 : 3 < p) : (X - 1) ^ 2 ∣ finitePolylog p 2 := by
  have hne : finitePolylog p 2 ≠ 0 := fun h ↦ by
    have := natDegree_finitePolylog (p := p) 2
    rw [h, natDegree_zero] at this
    omega
  have hroot : 1 < (finitePolylog p 2).rootMultiplicity 1 := by
    rw [one_lt_rootMultiplicity_iff_isRoot hne, IsRoot, IsRoot, eval_one_finitePolylog,
      ite_eq_right]
    · refine ⟨rfl, ?_⟩
      have h := congrArg (eval 1) (X_mul_derivative_finitePolylog (p := p) 2)
      rw [eval_mul, eval_X, one_mul] at h
      rw [h, eval_one_finitePolylog, ite_eq_right]
      intro hd
      have := Int.le_of_dvd (by norm_num) hd
      omega
    · intro hd
      have := Int.le_of_dvd (by norm_num) hd
      omega
  simpa using (pow_dvd_pow (X - C 1) hroot).trans (pow_rootMultiplicity_dvd _ 1)

variable (p) in
/-- The cofactor `g_p` of `(X - 1) ^ 2` in the finite dilogarithm: for `p > 3`,
`li_{2,p} = (X - 1) ^ 2 * g_p` (`sq_X_sub_one_mul_finiteDilogCofactor`). -/
noncomputable def finiteDilogCofactor : (ZMod p)[X] :=
  finitePolylog p 2 /ₘ (X - 1) ^ 2

private lemma monic_sq_X_sub_one : ((X - 1) ^ 2 : (ZMod p)[X]).Monic := by
  simpa using (monic_X_sub_C (1 : ZMod p)).pow 2

theorem sq_X_sub_one_mul_finiteDilogCofactor (hp3 : 3 < p) :
    (X - 1) ^ 2 * finiteDilogCofactor p = finitePolylog p 2 := by
  have h := modByMonic_add_div (finitePolylog p 2) ((X - 1) ^ 2)
  rwa [(modByMonic_eq_zero_iff_dvd monic_sq_X_sub_one).2 (sq_X_sub_one_dvd_finitePolylog_two hp3),
    zero_add] at h

theorem natDegree_finiteDilogCofactor : (finiteDilogCofactor p).natDegree = p - 3 := by
  rw [finiteDilogCofactor, natDegree_divByMonic _ monic_sq_X_sub_one, natDegree_finitePolylog,
    natDegree_pow, ← C_1, natDegree_X_sub_C]
  omega

/-- `g_p(1) = -1/2`: the finite dilogarithm has a root of multiplicity exactly two at `1`. -/
theorem eval_one_finiteDilogCofactor (hp3 : 3 < p) : (finiteDilogCofactor p).eval 1 = -2⁻¹ := by
  have h2 := two_ne_zero_of_ne_two (p := p) (by omega)
  -- Differentiate `X * li_{2,p}' = li_{1,p}` and `X * li_{1,p}' = li_{0,p}`, and evaluate at `1`.
  have h21 := X_mul_derivative_finitePolylog (p := p) 2
  have h10 := X_mul_derivative_finitePolylog (p := p) 1
  norm_num at h21 h10
  have e10 := congrArg (eval 1) h10
  have d21 := congrArg (fun q ↦ eval 1 (derivative q)) h21
  simp only [eval_mul, eval_X, one_mul, derivative_mul, derivative_X, eval_add] at e10 d21
  rw [eval_one_finitePolylog, ite_eq_left (dvd_zero _)] at e10
  -- Substituting `li_{2,p} = (X - 1) ^ 2 * g_p`, the left side of `d21` becomes `2 g_p(1)`.
  rw [← sq_X_sub_one_mul_finiteDilogCofactor hp3] at d21
  simp [derivative_mul, derivative_pow] at d21
  field_simp
  linear_combination d21 + e10

variable {F : Type*} [Field F] [Algebra (ZMod p) F]

variable (p) in
/-- The residue dilogarithm `f_p(x) = li_{2,p}(x) / (x - 1) ^ p` on a field over `𝔽_p`. With the
convention `0⁻¹ = 0` it takes the value `0` at `x = 1`, which carries no dilogarithm meaning; at
the residue of a root of unity `ζ ≠ 1` of order prime to `p` it is the reduction of
`p⁻² D(ζ ^ p)`. -/
noncomputable def residueDilogValue (x : F) : F :=
  aeval x (finitePolylog p 2) / (x - 1) ^ p

theorem residueDilogValue_def (x : F) :
    residueDilogValue p x = aeval x (finitePolylog p 2) / (x - 1) ^ p :=
  (rfl)

@[simp]
theorem residueDilogValue_zero : residueDilogValue p (0 : F) = 0 := by
  rw [residueDilogValue_def, ← map_zero (algebraMap (ZMod p) F),
    aeval_algebraMap_apply_eq_algebraMap_eval, eval_zero_finitePolylog, map_zero, zero_div]

@[simp]
theorem residueDilogValue_one : residueDilogValue p (1 : F) = 0 := by
  rw [residueDilogValue_def, sub_self, zero_pow hp.out.ne_zero, div_zero]

theorem residueDilogValue_neg_one : residueDilogValue p (-1 : F) = 0 := by
  rcases eq_or_ne p 2 with rfl | hp2
  · -- In characteristic `2`, `-1 = 1`.
    have h : (-1 : F) = 1 := by
      rw [← map_one (algebraMap (ZMod 2) F), ← map_neg, ZMod.neg_eq_self_mod_two]
    rw [h, residueDilogValue_one]
  rw [residueDilogValue_def, ← map_one (algebraMap (ZMod p) F), ← map_neg,
    aeval_algebraMap_apply_eq_algebraMap_eval, eval_neg_one_finitePolylog hp2 even_two, map_zero,
    zero_div]

/-- Away from `1`, `f_p(x) = g_p(x) / (x - 1) ^ (p - 2)`. -/
theorem residueDilogValue_eq_div (hp3 : 3 < p) {x : F} (hx : x ≠ 1) :
    residueDilogValue p x = aeval x (finiteDilogCofactor p) / (x - 1) ^ (p - 2) := by
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.2 hx
  have hp' : (x - 1) ^ p = (x - 1) ^ 2 * (x - 1) ^ (p - 2) := by
    rw [← pow_add, Nat.add_sub_cancel' (by omega)]
  rw [residueDilogValue_def, ← sq_X_sub_one_mul_finiteDilogCofactor hp3, map_mul, map_pow,
    map_sub, aeval_X, map_one, hp', mul_div_mul_left _ _ (pow_ne_zero _ hx1)]

theorem map_residueDilogValue {F' : Type*} [Field F'] [Algebra (ZMod p) F']
    (φ : F →ₐ[ZMod p] F') (x : F) :
    φ (residueDilogValue p x) = residueDilogValue p (φ x) := by
  rw [residueDilogValue_def, residueDilogValue_def, map_div₀, map_pow, map_sub, map_one,
    aeval_algHom_apply]

/-- A fibre of `f_p` avoiding `1` lies in the roots of `g_p - y (X - 1) ^ (p - 2)`. -/
private lemma card_filter_residueDilogValue_eq_le [DecidableEq F] (hp3 : 3 < p) (s : Finset F)
    (hs : 1 ∉ s) (y : F) :
    #{x ∈ s | residueDilogValue p x = y} ≤
      ((finiteDilogCofactor p).map (algebraMap (ZMod p) F) -
        C y * (X - 1) ^ (p - 2)).natDegree := by
  set P := (finiteDilogCofactor p).map (algebraMap (ZMod p) F) - C y * (X - 1) ^ (p - 2)
  have hP : P ≠ 0 := by
    intro h
    have h1 := congrArg (eval 1) h
    simp only [P, eval_sub, eval_map_algebraMap, eval_mul, eval_C, eval_pow, eval_X, eval_one,
      sub_self, zero_pow (show p - 2 ≠ 0 by omega), mul_zero, sub_zero, eval_zero] at h1
    rw [← map_one (algebraMap (ZMod p) F), aeval_algebraMap_apply_eq_algebraMap_eval,
      eval_one_finiteDilogCofactor hp3, map_eq_zero_iff _ (algebraMap (ZMod p) F).injective] at h1
    simp [two_ne_zero_of_ne_two (p := p) (by omega)] at h1
  refine card_le_degree_of_subset_roots fun x hx ↦ ?_
  rw [mem_val, mem_filter] at hx
  have hx1 : x ≠ 1 := fun h ↦ hs (h ▸ hx.1)
  rw [mem_roots hP, IsRoot, eval_sub, eval_map_algebraMap, eval_mul, eval_C, eval_pow, eval_sub,
    eval_X, eval_one, sub_eq_zero, ← div_eq_iff (pow_ne_zero _ (sub_ne_zero.2 hx1)),
    ← residueDilogValue_eq_div hp3 hx1, hx.2]

variable [Finite F]

/-- For `p > 3`, the values of the residue dilogarithm `f_p` on `F ∖ {0, 1}` span the finite
field `F` over `𝔽_p`. -/
theorem span_residueDilogValue_eq_top (hp3 : 3 < p) :
    Submodule.span (ZMod p) (residueDilogValue p '' ({0, 1}ᶜ : Set F)) = ⊤ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  set W := Submodule.span (ZMod p) (residueDilogValue p '' ({0, 1}ᶜ : Set F))
  by_contra hW
  set n := Module.finrank (ZMod p) F
  have hcard : Fintype.card F = p ^ n := by rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
  have hWn : Module.finrank (ZMod p) W < n := Submodule.finrank_lt hW
  set s : Finset F := ({0, 1} : Finset F)ᶜ
  have hs1 : (1 : F) ∉ s := by simp [s]
  have hscard : #s = p ^ n - 2 := by rw [card_compl, card_pair zero_ne_one, hcard]
  have hmem : ∀ x ∈ s, residueDilogValue p x ∈ W := fun x hx ↦
    Submodule.subset_span ⟨x, by simpa [s] using hx, rfl⟩
  have hp_le : p ≤ p ^ n := Nat.le_self_pow (by omega) p
  rcases Nat.eq_zero_or_pos (Module.finrank (ZMod p) W) with hW0 | hW0
  · -- `W = 0`, so every point of `s` is a root of `g_p`, which has only `p - 3` roots.
    rw [Submodule.finrank_eq_zero] at hW0
    have h := card_filter_residueDilogValue_eq_le hp3 s hs1 0
    rw [filter_true_of_mem fun x hx ↦ by simpa [hW0] using hmem x hx, map_zero, zero_mul,
      sub_zero] at h
    have hdeg := (natDegree_map_le (f := algebraMap (ZMod p) F)
      (p := finiteDilogCofactor p)).trans natDegree_finiteDilogCofactor.le
    omega
  · -- Otherwise each of the at most `p ^ (n - 1)` values has at most `p - 2` preimages.
    have hfib : ∀ y ∈ s.image (residueDilogValue p), #{x ∈ s | residueDilogValue p x = y} ≤
        p - 2 := by
      intro y _
      refine (card_filter_residueDilogValue_eq_le hp3 s hs1 y).trans
        ((natDegree_sub_le_of_le (m := p - 2) (n := p - 2) ?_ ?_).trans (max_self _).le)
      · exact natDegree_map_le.trans (by rw [natDegree_finiteDilogCofactor]; omega)
      · refine (natDegree_C_mul_le _ _).trans ?_
        rw [← C_1, natDegree_pow, natDegree_X_sub_C, mul_one]
    have himg : #(s.image (residueDilogValue p)) ≤ p ^ (n - 1) := by
      calc #(s.image (residueDilogValue p)) ≤ Fintype.card W := by
            rw [Fintype.card_subtype]
            exact card_le_card fun y hy ↦ by
              obtain ⟨x, hx, rfl⟩ := mem_image.1 hy
              simpa using hmem x hx
        _ = p ^ Module.finrank (ZMod p) W := by
            rw [Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]
        _ ≤ p ^ (n - 1) := Nat.pow_le_pow_right hp.out.pos (by omega)
    have h := card_le_mul_card_image s (p - 2) hfib
    have hn : n = (n - 1) + 1 := by omega
    have hpn : p ^ n = p * p ^ (n - 1) := by rw [hn, pow_succ, mul_comm]; simp
    have hpn1 : p ≤ p ^ (n - 1) := Nat.le_self_pow (by omega) p
    have key : (p - 2) * p ^ (n - 1) + 2 * p ^ (n - 1) = p * p ^ (n - 1) := by
      rw [← add_mul, Nat.sub_add_cancel (by omega)]
    have := Nat.mul_le_mul_left (p - 2) himg
    omega

/-- For `p > 3`, the pairwise differences of the values of the residue dilogarithm `f_p` on
`F ∖ {0, 1}` span the finite field `F` over `𝔽_p`. -/
theorem span_residueDilogValue_sub_eq_top (hp3 : 3 < p) :
    Submodule.span (ZMod p) (Set.image2 (fun x x' ↦ residueDilogValue p x - residueDilogValue p x')
      ({0, 1}ᶜ : Set F) {0, 1}ᶜ) = ⊤ := by
  have h2 : (2 : F) ≠ 0 := by
    rw [← map_ofNat (algebraMap (ZMod p) F) 2]
    exact (map_ne_zero_iff _ (algebraMap (ZMod p) F).injective).2
      (two_ne_zero_of_ne_two (by omega))
  have hneg : (-1 : F) ∈ ({0, 1}ᶜ : Set F) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or, neg_eq_zero,
      one_ne_zero, not_false_eq_true, true_and]
    intro h
    exact h2 (by linear_combination -h)
  rw [eq_top_iff, ← span_residueDilogValue_eq_top (F := F) hp3, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact Submodule.subset_span ⟨x, hx, -1, hneg, by simp [residueDilogValue_neg_one]⟩

end TauCeti
