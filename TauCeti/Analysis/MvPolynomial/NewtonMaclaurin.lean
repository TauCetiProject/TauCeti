/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.Polynomial.Vieta
import TauCeti.Algebra.Order.BigOperators.Ring.Multiset
import TauCeti.Analysis.Convex.Sequence.DiscreteConcave
import TauCeti.Analysis.MvPolynomial.Deriv
import TauCeti.Analysis.MvPolynomial.Jacobian
import TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary
import TauCeti.RingTheory.MvPolynomial.Symmetric.NewtonIdentities

/-!
# Elementary symmetric functions and the Newton–Maclaurin inequalities

For `λ ∈ ℝⁿ` write `σ_k(λ)` for the elementary symmetric polynomial `MvPolynomial.esymm` evaluated
at `λ`, `σ_{k;i}(λ) = σ_k(λ)|_{λ_i = 0}` (written `eval (update λ i 0) (esymm ι R k)`), and
`S_k = σ_k / binom(n, k)` for the normalized function `TauCeti.normalizedEsymm`. The cone
`Γ_k = {λ | σ_1(λ) > 0, …, σ_k(λ) > 0}` is `TauCeti.hessianCone n k`.

## Main results

* `TauCeti.fderiv_eval_esymm_succ_apply_single`: `∂σ_{k+1}/∂λ_i = σ_{k;i}`, from the expansion
  `σ_{k+1} = λ_i σ_{k;i} + σ_{k+1;i}` (`TauCeti.eval_esymm_succ`, with the other algebraic
  identities for `σ_{k;i}` in `TauCeti.RingTheory.MvPolynomial.Symmetric.Elementary`).
* `TauCeti.normalizedEsymm_mul_normalizedEsymm_le_sq`: **Newton's inequalities**
  `S_k S_{k+2} ≤ S_{k+1}²` for every `λ ∈ ℝⁿ`, and
  `TauCeti.eq_of_normalizedEsymm_mul_normalizedEsymm_eq_sq`: equality with `S_{k+2} ≠ 0` (for
  instance on `Γ_n` when `k + 2 ≤ n`) forces all `λ_i` to be equal.
* `TauCeti.normalizedEsymm_div_rpow_le`: the **generalized Newton–Maclaurin inequality**
  `(S_r / S_s)^{1/(r - s)} ≤ (S_k / S_l)^{1/(k - l)}` on `Γ_r` for `s < r`, `l < k ≤ r`, `l ≤ s`.
* `TauCeti.normalizedEsymm_rpow_le`: **Maclaurin's inequalities** `S_l^{1/l} ≤ S_k^{1/k}` on `Γ_l`
  for `1 ≤ k ≤ l`, with `TauCeti.normalizedEsymm_rpow_le_of_mem_closure` on the closure of `Γ_l`
  and `TauCeti.normalizedEsymm_rpow_le_of_nonneg` on the closed positive orthant.

## Implementation notes

Newton's inequalities are proved by Rolle's theorem (`Polynomial.card_roots_le_derivative`): the
derivative of `∏ (X - λ_i)` has `n - 1` real roots with the same `S_0, …, S_{n-1}`, which lowers
`n` to `k + 2`. Replacing `λ` by `(λ_i⁻¹)` reverses the sequence `S_0, …, S_{k+2}` up to the
factor `S_{k+2}`, which reduces the inequality to `S_0 S_2 ≤ S_1²`, the inequality between the
arithmetic and the quadratic mean. The generalized Newton–Maclaurin inequality follows from the
concavity of `j ↦ log S_j` on `[0, r]`.

## References

* J. Spruck, *Geometric aspects of the theory of fully nonlinear elliptic equations*, Global
  theory of minimal surfaces, Clay Math. Proc. 2 (2005), Lemma 2.6, Proposition 2.7,
  Corollary 2.8 and Lemma 2.10.
* S. Dinew and S. Kołodziej, *A priori estimates for complex Hessian equations*, Anal. PDE 7
  (2014), §1.
-/

public section

open Finset MvPolynomial Function

namespace TauCeti

section Derivative

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] [DecidableEq ι]

/-- The partial derivative `∂σ_{k+1}/∂λ_i = σ_{k;i}`, where `σ_{k;i}(λ) = σ_k(λ)|_{λ_i = 0}`. -/
theorem fderiv_eval_esymm_succ_apply_single (μ : ι → 𝕜) (i : ι) (k : ℕ) :
    fderiv 𝕜 (fun ν ↦ eval ν (esymm ι 𝕜 (k + 1))) μ (Pi.single i 1) =
      eval (update μ i 0) (esymm ι 𝕜 k) := by
  rw [(hasFDerivAt_eval _ μ).fderiv]
  simp only [FunLike.coe_sum, FunLike.coe_smul, Finset.sum_apply,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h := hasDerivAt_eval_update (esymm ι 𝕜 (k + 1)) μ i (μ i)
  rw [update_eq_self] at h
  refine h.unique ?_
  have hline : (fun w ↦ eval (update μ i w) (esymm ι 𝕜 (k + 1))) =
      fun w ↦ w * eval (update μ i 0) (esymm ι 𝕜 k) + eval (update μ i 0) (esymm ι 𝕜 (k + 1)) := by
    funext w
    rw [eval_esymm_succ _ i, update_self, update_idem]
  rw [hline]
  simpa using ((hasDerivAt_id (μ i)).mul_const (eval (update μ i 0) (esymm ι 𝕜 k))).add_const
    (eval (update μ i 0) (esymm ι 𝕜 (k + 1)))

omit [DecidableEq ι] in
/-- `σ_0 = 1` has derivative `0`. -/
theorem fderiv_eval_esymm_zero (μ : ι → 𝕜) :
    fderiv 𝕜 (fun ν ↦ eval ν (esymm ι 𝕜 0)) μ = 0 := by
  simp

end Derivative

section Newton

/-- The normalized elementary symmetric function `e_k(s) / binom(card s, k)` of a multiset. -/
private noncomputable def mNorm (s : Multiset ℝ) (k : ℕ) : ℝ :=
  s.esymm k / (Multiset.card s).choose k

private theorem mNorm_zero (s : Multiset ℝ) : mNorm s 0 = 1 := by
  simp [mNorm]

private theorem mNorm_card (s : Multiset ℝ) : mNorm s (Multiset.card s) = s.prod := by
  rw [mNorm, Multiset.esymm_card_eq_prod, Nat.choose_self, Nat.cast_one, div_one]

private theorem mNorm_of_card_lt {s : Multiset ℝ} {k : ℕ} (h : Multiset.card s < k) :
    mNorm s k = 0 := by
  rw [mNorm, Multiset.esymm_of_card_lt h, zero_div]

private theorem mNorm_map_inv_mul_prod (s : Multiset ℝ) (hs : (0 : ℝ) ∉ s) {j : ℕ}
    (hj : j ≤ Multiset.card s) :
    mNorm (s.map (·⁻¹)) j * s.prod = mNorm s (Multiset.card s - j) := by
  rw [mNorm, mNorm, Multiset.card_map, ← Nat.choose_symm hj, div_mul_eq_mul_div,
    Multiset.esymm_map_inv_mul_prod s hs hj]

open Polynomial in
/-- Rolle's theorem: the roots `r` of the derivative of `∏_{a ∈ s} (X - a)` are real, and they
have the same normalized elementary symmetric functions as `s` up to degree `card r`. -/
private theorem exists_mNorm_eq (s : Multiset ℝ) {m : ℕ} (hs : Multiset.card s = m + 1) :
    ∃ r : Multiset ℝ, Multiset.card r = m ∧ ∀ j ≤ m, mNorm s j = mNorm r j := by
  set p : ℝ[X] := (s.map fun a ↦ Polynomial.X - Polynomial.C a).prod with hp
  have hroots : p.roots = s := roots_multiset_prod_X_sub_C s
  have hmonic : p.Monic := monic_multiset_prod_of_monic _ _ fun a _ ↦ monic_X_sub_C a
  have hdeg : p.natDegree = m + 1 := by
    rw [hp, natDegree_multiset_prod_X_sub_C_eq_card, hs]
  have hcardp : Multiset.card p.roots = p.natDegree := by rw [hroots, hdeg, hs]
  have hlead : p.coeff (m + 1) = 1 := by rw [← hdeg]; exact hmonic.coeff_natDegree
  obtain ⟨q, hqdef⟩ : ∃ q, q = derivative p := ⟨_, rfl⟩
  have hqm : q.coeff m = m + 1 := by
    rw [hqdef, coeff_derivative, hlead, one_mul]
  have hqdeg : q.natDegree = m := by
    refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rw [hqm]; positivity))
    have := natDegree_derivative_le p
    rw [← hqdef, hdeg] at this
    omega
  have hcardq : Multiset.card q.roots = q.natDegree := by
    refine le_antisymm (card_roots' q) ?_
    have := card_roots_le_derivative p
    rw [← hqdef, hcardp, hdeg] at this
    omega
  refine ⟨q.roots, by rw [hcardq, hqdeg], fun j hj ↦ ?_⟩
  have hq := coeff_eq_esymm_roots_of_card hcardq (k := m - j) (by omega)
  have hpc := coeff_eq_esymm_roots_of_card hcardp (k := m - j + 1) (by omega)
  rw [hqdeg, show m - (m - j) = j by omega, leadingCoeff, hqdeg, hqm, hqdef, coeff_derivative,
    ← hqdef] at hq
  rw [hdeg, show m + 1 - (m - j + 1) = j by omega, hmonic.leadingCoeff, hroots] at hpc
  rw [hpc] at hq
  have E : (m + 1 : ℝ) * q.roots.esymm j = s.esymm j * ((m - j : ℕ) + 1 : ℝ) := by
    have h1 : ((-1 : ℝ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    push_cast [Nat.cast_sub hj] at hq ⊢
    linear_combination (-1 : ℝ) ^ j * hq.symm -
      ((m + 1 : ℝ) * q.roots.esymm j - s.esymm j * ((m : ℝ) - j + 1)) * h1
  have Ch : (m.choose j : ℝ) * (m + 1) = ((m + 1).choose j : ℝ) * ((m - j : ℕ) + 1 : ℝ) := by
    have := Nat.choose_mul_succ_eq m j
    rw [show m + 1 - j = m - j + 1 by omega] at this
    exact_mod_cast this
  rw [mNorm, mNorm, hs, hcardq, hqdeg, div_eq_div_iff (by exact_mod_cast (Nat.choose_pos
    (by omega)).ne') (by exact_mod_cast (Nat.choose_pos hj).ne')]
  refine mul_right_cancel₀ (show (m + 1 : ℝ) ≠ 0 by positivity) ?_
  linear_combination s.esymm j * Ch - ((m + 1).choose j : ℝ) * E

/-- The second normalized elementary symmetric function in terms of the first and the second
power sum. -/
private theorem mNorm_two_eq (s : Multiset ℝ) (hs : 2 ≤ Multiset.card s) :
    mNorm s 2 = (s.sum ^ 2 - (s.map (· ^ 2)).sum) / (Multiset.card s * (Multiset.card s - 1)) := by
  have h := Multiset.sum_map_pow_two_eq_esymm s
  rw [Multiset.esymm_one] at h
  rw [mNorm, Nat.cast_choose_two, show s.esymm 2 = (s.sum ^ 2 - (s.map (· ^ 2)).sum) / 2 by
    linarith]
  have : (Multiset.card s : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ Multiset.card s := by exact_mod_cast hs
    linarith
  have : (Multiset.card s : ℝ) ≠ 0 := by positivity
  field_simp

private theorem mNorm_one_eq (s : Multiset ℝ) : mNorm s 1 = s.sum / Multiset.card s := by
  rw [mNorm, Multiset.esymm_one, Nat.choose_one_right]

/-- Newton's inequality at `k = 1`: `S₀ S₂ ≤ S₁²`, the inequality between the arithmetic and the
quadratic mean. -/
private theorem mNorm_two_le (s : Multiset ℝ) : mNorm s 2 ≤ mNorm s 1 ^ 2 := by
  rcases lt_or_ge (Multiset.card s) 2 with hs | hs
  · rw [mNorm_of_card_lt hs]
    positivity
  have hn : (2 : ℝ) ≤ Multiset.card s := by exact_mod_cast hs
  rw [mNorm_two_eq s hs, mNorm_one_eq, div_pow, div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith [Multiset.sq_sum_le_card_mul_sum_sq s, sq_nonneg s.sum]

private theorem eq_of_mNorm_two_eq (s : Multiset ℝ) (hs : 2 ≤ Multiset.card s)
    (h : mNorm s 2 = mNorm s 1 ^ 2) : ∀ x ∈ s, ∀ y ∈ s, x = y := by
  have hn : (2 : ℝ) ≤ Multiset.card s := by exact_mod_cast hs
  rw [mNorm_two_eq s hs, mNorm_one_eq, div_pow, div_eq_div_iff (by nlinarith) (by positivity)] at h
  refine Multiset.eq_of_sq_sum_eq_card_mul_sum_sq s ?_
  have : (Multiset.card s : ℝ) * (s.sum ^ 2 - Multiset.card s * (s.map (· ^ 2)).sum) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp this with h0 | h0
  · linarith
  · linarith

private theorem mNorm_replicate (n : ℕ) (hn : 2 ≤ n) (c : ℝ) :
    mNorm (Multiset.replicate n c) 1 = c ∧ mNorm (Multiset.replicate n c) 2 = c ^ 2 := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsum : (Multiset.replicate n c).sum = n * c := by simp
  have hsq : ((Multiset.replicate n c).map (· ^ 2)).sum = n * c ^ 2 := by simp
  refine ⟨?_, ?_⟩
  · rw [mNorm_one_eq, hsum, Multiset.card_replicate]
    field_simp
  · rw [mNorm_two_eq _ (by simpa using hn), hsum, hsq, Multiset.card_replicate,
      div_eq_iff (by nlinarith)]
    ring

/-- **Newton's inequality** for a multiset, `S_k S_{k+2} ≤ S_{k+1}²`. -/
private theorem mNorm_mul_le_sq (s : Multiset ℝ) (k : ℕ) :
    mNorm s k * mNorm s (k + 2) ≤ mNorm s (k + 1) ^ 2 := by
  rcases lt_or_ge (Multiset.card s) (k + 2) with hlt | hge
  · rw [mNorm_of_card_lt hlt, mul_zero]
    positivity
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge
  clear hge
  induction d generalizing s with
  | zero =>
    by_cases h0 : (0 : ℝ) ∈ s
    · rw [← add_zero (k + 2), ← hd, mNorm_card, Multiset.prod_eq_zero h0, mul_zero]
      positivity
    have h0' := mNorm_map_inv_mul_prod s h0 (j := 0) (by omega)
    have h1 := mNorm_map_inv_mul_prod s h0 (j := 1) (by omega)
    have h2 := mNorm_map_inv_mul_prod s h0 (j := 2) (by omega)
    rw [hd, show k + 2 + 0 - 0 = k + 2 by omega, mNorm_zero] at h0'
    rw [hd, show k + 2 + 0 - 1 = k + 1 by omega] at h1
    rw [hd, show k + 2 + 0 - 2 = k by omega] at h2
    rw [← h0', ← h1, ← h2]
    nlinarith [mNorm_two_le (s.map (·⁻¹)), sq_nonneg s.prod]
  | succ d ih =>
    obtain ⟨r, hr, hsr⟩ := exists_mNorm_eq s (m := k + 2 + d) (by omega)
    rw [hsr k (by omega), hsr (k + 1) (by omega), hsr (k + 2) (by omega)]
    exact ih r hr

/-- The equality case of Newton's inequality for a multiset with `S_{k+2} ≠ 0`. -/
private theorem eq_of_mNorm_mul_eq_sq (s : Multiset ℝ) (k : ℕ) (hne : mNorm s (k + 2) ≠ 0)
    (heq : mNorm s k * mNorm s (k + 2) = mNorm s (k + 1) ^ 2) :
    ∀ x ∈ s, ∀ y ∈ s, x = y := by
  have hge : k + 2 ≤ Multiset.card s := by
    by_contra h
    exact hne (mNorm_of_card_lt (by omega))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hge
  clear hge
  induction d generalizing s with
  | zero =>
    have hcard : Multiset.card s = k + 2 := hd
    have h0 : (0 : ℝ) ∉ s := fun h0 ↦ hne (by rw [← hcard, mNorm_card, Multiset.prod_eq_zero h0])
    have hP : s.prod ≠ 0 := Multiset.prod_ne_zero h0
    have h0' := mNorm_map_inv_mul_prod s h0 (j := 0) (by omega)
    have h1 := mNorm_map_inv_mul_prod s h0 (j := 1) (by omega)
    have h2 := mNorm_map_inv_mul_prod s h0 (j := 2) (by omega)
    rw [hcard, show k + 2 - 0 = k + 2 by omega, mNorm_zero] at h0'
    rw [hcard, show k + 2 - 1 = k + 1 by omega] at h1
    rw [hcard, show k + 2 - 2 = k by omega] at h2
    rw [← h0', ← h1, ← h2] at heq
    have ht : mNorm (s.map (·⁻¹)) 2 = mNorm (s.map (·⁻¹)) 1 ^ 2 := by
      refine mul_right_cancel₀ (pow_ne_zero 2 hP) ?_
      linear_combination heq
    intro x hx y hy
    have := eq_of_mNorm_two_eq _ (by rw [Multiset.card_map]; omega) ht _
      (Multiset.mem_map_of_mem _ hx) _ (Multiset.mem_map_of_mem _ hy)
    exact inv_inj.mp this
  | succ d ih =>
    obtain ⟨r, hr, hsr⟩ := exists_mNorm_eq s (m := k + 2 + d) (by omega)
    rw [hsr k (by omega), hsr (k + 1) (by omega), hsr (k + 2) (by omega)] at heq
    rw [hsr (k + 2) (by omega)] at hne
    have hrr := ih r hne heq hr
    obtain ⟨c, hc⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < Multiset.card r by omega)
    have hrep : r = Multiset.replicate (k + 2 + d) c :=
      Multiset.eq_replicate.mpr ⟨hr, fun b hb ↦ hrr b hb c hc⟩
    obtain ⟨h1, h2⟩ := mNorm_replicate (k + 2 + d) (by omega) c
    rw [← hrep, ← hsr 1 (by omega)] at h1
    rw [← hrep, ← hsr 2 (by omega)] at h2
    exact eq_of_mNorm_two_eq s (by omega) (by rw [h1, h2])

end Newton

section Normalized

variable {ι : Type*} [Fintype ι]

/-- The **normalized elementary symmetric function** `S_k(λ) = σ_k(λ) / binom(n, k)` of
`λ : ι → ℝ`, where `n` is the cardinality of `ι`. -/
noncomputable def normalizedEsymm (k : ℕ) (μ : ι → ℝ) : ℝ :=
  eval μ (esymm ι ℝ k) / (Fintype.card ι).choose k

/-- The defining formula of `TauCeti.normalizedEsymm`. -/
theorem normalizedEsymm_def (k : ℕ) (μ : ι → ℝ) :
    normalizedEsymm k μ = eval μ (esymm ι ℝ k) / (Fintype.card ι).choose k := by
  rw [normalizedEsymm]

/-- `S_0 = 1`. -/
@[simp]
theorem normalizedEsymm_zero (μ : ι → ℝ) : normalizedEsymm 0 μ = 1 := by
  simp [normalizedEsymm]

private theorem normalizedEsymm_eq_mNorm (k : ℕ) (μ : ι → ℝ) :
    normalizedEsymm k μ = mNorm (univ.val.map μ) k := by
  rw [normalizedEsymm, mNorm, eval_esymm_eq_esymm_map, Multiset.card_map, Finset.card_val,
    Finset.card_univ]

/-- `S_k` is continuous. -/
theorem continuous_normalizedEsymm (k : ℕ) : Continuous (normalizedEsymm (ι := ι) k) :=
  (MvPolynomial.continuous_eval _).div_const _

/-- `S_k(λ) ≥ 0` when every entry of `λ` is nonnegative. -/
theorem normalizedEsymm_nonneg {μ : ι → ℝ} (hμ : ∀ i, 0 ≤ μ i) (k : ℕ) :
    0 ≤ normalizedEsymm k μ := by
  rw [normalizedEsymm, eval_esymm_eq_esymm_map, Finset.esymm_map_val]
  exact div_nonneg (Finset.sum_nonneg fun A _ ↦ Finset.prod_nonneg fun i _ ↦ hμ i)
    (Nat.cast_nonneg _)

/-- **Newton's inequality** `S_k S_{k+2} ≤ S_{k+1}²`, for every `λ ∈ ℝⁿ` and every `k`. -/
theorem normalizedEsymm_mul_normalizedEsymm_le_sq (μ : ι → ℝ) (k : ℕ) :
    normalizedEsymm k μ * normalizedEsymm (k + 2) μ ≤ normalizedEsymm (k + 1) μ ^ 2 := by
  simpa only [normalizedEsymm_eq_mNorm] using mNorm_mul_le_sq _ k

/-- The equality case of Newton's inequality: if `S_{k+2}(λ) ≠ 0` and
`S_k(λ) S_{k+2}(λ) = S_{k+1}(λ)²`, then all `λ_i` are equal. The hypothesis `S_{k+2} ≠ 0` holds on
`Γ_{k+2}`, in particular on `Γ_n` when `k + 2 ≤ n`
(`TauCeti.normalizedEsymm_pos_of_mem_hessianCone`); without it
`λ = (1, 0, 0)` and `k = 1` give equality with unequal entries. -/
theorem eq_of_normalizedEsymm_mul_normalizedEsymm_eq_sq {μ : ι → ℝ} {k : ℕ}
    (hne : normalizedEsymm (k + 2) μ ≠ 0)
    (h : normalizedEsymm k μ * normalizedEsymm (k + 2) μ = normalizedEsymm (k + 1) μ ^ 2)
    (i j : ι) : μ i = μ j := by
  simp only [normalizedEsymm_eq_mNorm] at hne h
  exact eq_of_mNorm_mul_eq_sq _ k hne h _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val i)) _
    (Multiset.mem_map_of_mem _ (Finset.mem_univ_val j))

end Normalized

section Cone

/-- The cone `Γ_k = {λ | σ_1(λ) > 0, …, σ_k(λ) > 0}` of `ℝⁿ`. -/
def hessianCone (n k : ℕ) : Set (Fin n → ℝ) :=
  {μ | ∀ j ∈ Finset.Icc 1 k, 0 < eval μ (esymm (Fin n) ℝ j)}

/-- The defining property of `TauCeti.hessianCone`. -/
@[simp]
theorem mem_hessianCone {n k : ℕ} {μ : Fin n → ℝ} :
    μ ∈ hessianCone n k ↔ ∀ j ∈ Finset.Icc 1 k, 0 < eval μ (esymm (Fin n) ℝ j) :=
  Iff.rfl

/-- A vector with positive entries lies in `Γ_k` for every `k ≤ n`. -/
theorem mem_hessianCone_of_pos {n k : ℕ} {μ : Fin n → ℝ} (hμ : ∀ i, 0 < μ i) (hk : k ≤ n) :
    μ ∈ hessianCone n k := fun j hj ↦ by
  rw [eval_esymm_eq_esymm_map, Finset.esymm_map_val]
  exact Finset.sum_pos (fun A _ ↦ Finset.prod_pos fun i _ ↦ hμ i)
    (Finset.powersetCard_nonempty.mpr (by simpa using (Finset.mem_Icc.mp hj).2.trans hk))

/-- On `Γ_k`, `S_j > 0` for every `j ≤ k`, including `S_0 = 1`. -/
theorem normalizedEsymm_pos_of_mem_hessianCone {n k j : ℕ} {μ : Fin n → ℝ}
    (hμ : μ ∈ hessianCone n k) (hj : j ≤ k) : 0 < normalizedEsymm j μ := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  have hσ := hμ j (Finset.mem_Icc.mpr ⟨hj0, hj⟩)
  have hjn : j ≤ n := by
    by_contra h
    rw [eval_esymm_eq_esymm_map, Multiset.esymm_of_card_lt (by simpa using h)] at hσ
    exact lt_irrefl _ hσ
  exact div_pos hσ (by exact_mod_cast Nat.choose_pos (by simpa using hjn))

/-- The **generalized Newton–Maclaurin inequality**: for `0 ≤ s < r`, `0 ≤ l < k ≤ r` with `l ≤ s`
and `λ ∈ Γ_r`, `(S_r / S_s)^{1/(r - s)} ≤ (S_k / S_l)^{1/(k - l)}`. -/
theorem normalizedEsymm_div_rpow_le {n r s k l : ℕ} {μ : Fin n → ℝ}
    (hμ : μ ∈ hessianCone n r) (hsr : s < r) (hlk : l < k) (hkr : k ≤ r) (hls : l ≤ s) :
    (normalizedEsymm r μ / normalizedEsymm s μ) ^ (1 / ((r : ℝ) - s)) ≤
      (normalizedEsymm k μ / normalizedEsymm l μ) ^ (1 / ((k : ℝ) - l)) := by
  have hpos : ∀ j ≤ r, 0 < normalizedEsymm j μ := fun j hj ↦
    normalizedEsymm_pos_of_mem_hessianCone hμ hj
  have ha : ∀ j, j + 2 ≤ r → Real.log (normalizedEsymm j μ) +
      Real.log (normalizedEsymm (j + 2) μ) ≤ 2 * Real.log (normalizedEsymm (j + 1) μ) := by
    intro j hj
    have h2 : 2 * Real.log (normalizedEsymm (j + 1) μ) =
        Real.log (normalizedEsymm (j + 1) μ ^ 2) := by
      rw [Real.log_pow, Nat.cast_ofNat]
    rw [← Real.log_mul (hpos j (by omega)).ne' (hpos (j + 2) hj).ne', h2]
    exact Real.log_le_log (mul_pos (hpos j (by omega)) (hpos (j + 2) hj))
      (normalizedEsymm_mul_normalizedEsymm_le_sq μ j)
  have key := div_sub_le_div_sub_of_add_le_two_mul (a := fun j ↦ Real.log (normalizedEsymm j μ))
    ha hsr hlk hkr hls
  rw [Real.rpow_def_of_pos (div_pos (hpos r le_rfl) (hpos s hsr.le)),
    Real.rpow_def_of_pos (div_pos (hpos k hkr) (hpos l (by omega))), Real.exp_le_exp,
    Real.log_div (hpos r le_rfl).ne' (hpos s hsr.le).ne',
    Real.log_div (hpos k hkr).ne' (hpos l (by omega)).ne', mul_one_div, mul_one_div]
  exact key

/-- **Maclaurin's inequality** `S_l^{1/l} ≤ S_k^{1/k}` for `1 ≤ k ≤ l` and `λ ∈ Γ_l`. -/
theorem normalizedEsymm_rpow_le {n k l : ℕ} {μ : Fin n → ℝ} (hμ : μ ∈ hessianCone n l)
    (hk : 1 ≤ k) (hkl : k ≤ l) :
    normalizedEsymm l μ ^ (1 / (l : ℝ)) ≤ normalizedEsymm k μ ^ (1 / (k : ℝ)) := by
  simpa using normalizedEsymm_div_rpow_le hμ (s := 0) (l := 0) (by omega) (by omega) hkl le_rfl

/-- On the closure of `Γ_l`, `S_j ≥ 0` for `j ≤ l`. -/
theorem normalizedEsymm_nonneg_of_mem_closure {n l j : ℕ} {μ : Fin n → ℝ}
    (hμ : μ ∈ closure (hessianCone n l)) (hj : j ≤ l) : 0 ≤ normalizedEsymm j μ :=
  closure_minimal (fun _ hν ↦ (normalizedEsymm_pos_of_mem_hessianCone hν hj).le)
    (isClosed_le continuous_const (continuous_normalizedEsymm j)) hμ

/-- **Maclaurin's inequality** on the closure of `Γ_l`. -/
theorem normalizedEsymm_rpow_le_of_mem_closure {n k l : ℕ} {μ : Fin n → ℝ}
    (hμ : μ ∈ closure (hessianCone n l)) (hk : 1 ≤ k) (hkl : k ≤ l) :
    normalizedEsymm l μ ^ (1 / (l : ℝ)) ≤ normalizedEsymm k μ ^ (1 / (k : ℝ)) := by
  have hc : ∀ j : ℕ, 1 ≤ j → Continuous fun ν : Fin n → ℝ ↦ normalizedEsymm j ν ^ (1 / (j : ℝ)) :=
    fun j hj ↦ (continuous_normalizedEsymm j).rpow_const fun _ ↦ Or.inr (by positivity)
  exact closure_minimal (fun _ hν ↦ normalizedEsymm_rpow_le hν hk hkl)
    (isClosed_le (hc l (hk.trans hkl)) (hc k hk)) hμ

/-- The closed positive orthant lies in the closure of `Γ_k` for `k ≤ n`. -/
theorem mem_closure_hessianCone_of_nonneg {n k : ℕ} {μ : Fin n → ℝ} (hμ : ∀ i, 0 ≤ μ i)
    (hk : k ≤ n) : μ ∈ closure (hessianCone n k) := by
  have ht : Filter.Tendsto (fun ε : ℝ ↦ μ + ε • (1 : Fin n → ℝ)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds μ) := by
    have : Continuous fun ε : ℝ ↦ μ + ε • (1 : Fin n → ℝ) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε ↦ ?_)
  exact mem_hessianCone_of_pos (fun i ↦ by simpa using add_pos_of_nonneg_of_pos (hμ i) hε) hk

/-- **Maclaurin's inequality** `S_l^{1/l} ≤ S_k^{1/k}` for `1 ≤ k ≤ l` and `λ` with nonnegative
entries. -/
theorem normalizedEsymm_rpow_le_of_nonneg {n k l : ℕ} {μ : Fin n → ℝ} (hμ : ∀ i, 0 ≤ μ i)
    (hk : 1 ≤ k) (hkl : k ≤ l) :
    normalizedEsymm l μ ^ (1 / (l : ℝ)) ≤ normalizedEsymm k μ ^ (1 / (k : ℝ)) := by
  rcases le_or_gt l n with hln | hln
  · exact normalizedEsymm_rpow_le_of_mem_closure (mem_closure_hessianCone_of_nonneg hμ hln) hk hkl
  have hl : (0 : ℝ) < l := by exact_mod_cast hk.trans hkl
  rw [normalizedEsymm, Nat.choose_eq_zero_of_lt (by simpa using hln), Nat.cast_zero, div_zero,
    Real.zero_rpow (by positivity)]
  exact Real.rpow_nonneg (normalizedEsymm_nonneg hμ k) _

end Cone

end TauCeti
