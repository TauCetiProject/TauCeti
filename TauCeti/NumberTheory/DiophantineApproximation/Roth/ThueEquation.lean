/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DiophantineApproximation.Roth.BinaryForm

import TauCeti.RingTheory.Polynomial.BinaryForm

/-!
# Thue's theorem on Thue equations

Let `F ∈ ℤ[X₀, X₁]` be a binary form such that `F(X, 1)` has at least three distinct complex
zeros. **Thue's theorem** states that for every integer `m ≠ 0` the Thue equation `F(x, y) = m`
has only finitely many solutions `(x, y) ∈ ℤ²`. More generally, the Thue inequality
`0 < |F(x, y)| ≤ B` has only finitely many integer solutions.

The proof deduces this from the Thue–Roth inequality. The form `F` has a divisor `G ∈ ℤ[X₀, X₁]`
which is a binary form of degree `r ≥ 3` without squared linear factors over `ℂ`
(`MvPolynomial.IsHomogeneous.exists_dvd_isHomogeneous_not_sq_dvd`). If `F(x, y) ≠ 0`, then the
integer `G(x, y)` is a nonzero divisor of `F(x, y)`, so `|G(x, y)| ≤ |F(x, y)|`. The Thue–Roth
inequality `MvPolynomial.IsHomogeneous.exists_pos_mul_max_abs_rpow_le_abs_eval` for `G` with
exponent `κ = r - 1/2 > 2` gives `c > 0` with `c max(|x|, |y|) ^ (1/2) ≤ |G(x, y)|`, which bounds
`max(|x|, |y|)` in terms of `B` and `c`. Like Roth's theorem, the argument is ineffective: it gives
no bound on the size of the solutions.

## Main results

* `MvPolynomial.IsHomogeneous.finite_setOfPred_eval_ne_zero_and_abs_le`: the Thue inequality
  `0 < |F(x, y)| ≤ B` has finitely many integer solutions.
* `MvPolynomial.IsHomogeneous.finite_setOfPred_eval_eq`: **Thue's theorem**, the Thue equation
  `F(x, y) = m` with `m ≠ 0` has finitely many integer solutions.

## References

* A. Thue, *Über Annäherungswerte algebraischer Zahlen*, J. Reine Angew. Math. 135 (1909).
* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 6, Corollary 6.4.
-/

public section

open Real

namespace MvPolynomial

/-- **Thue inequalities** (Evertse, Corollary 6.4). Let `F ∈ ℤ[X₀, X₁]` be a binary form such
that `F(X, 1)` has at least three distinct complex zeros. Then for every `B ∈ ℤ` only finitely
many integer points `(x, y)` satisfy `0 < |F(x, y)| ≤ B`. The proof is ineffective. -/
theorem IsHomogeneous.finite_setOfPred_eval_ne_zero_and_abs_le {F : MvPolynomial (Fin 2) ℤ}
    {d : ℕ} (hF : F.IsHomogeneous d)
    (hroots : 3 ≤ ((MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial ℤ).map
      (Int.castRingHom ℂ)).roots.toFinset.card) (B : ℤ) :
    {p : ℤ × ℤ | eval ![p.1, p.2] F ≠ 0 ∧ |eval ![p.1, p.2] F| ≤ B}.Finite := by
  classical
  obtain ⟨G, hGF, hG, hsq⟩ := hF.exists_dvd_isHomogeneous_not_sq_dvd ℂ
  set r := ((MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial ℤ).map
    (Int.castRingHom ℂ)).roots.toFinset.card
  have hr : (3 : ℝ) ≤ r := by exact_mod_cast hroots
  -- The Thue–Roth inequality for `G` with `κ = r - 1/2` has exponent `r - κ = 1/2`.
  obtain ⟨c, hc, hcG⟩ := hG.exists_pos_mul_max_abs_rpow_le_abs_eval hsq
    (κ := r - 1 / 2) (by linarith)
  set N : ℤ := ⌈((B : ℝ) / c) ^ 2⌉
  refine ((Set.finite_Icc (-N) N).prod (Set.finite_Icc (-N) N)).subset ?_
  rintro ⟨x, y⟩ ⟨hne, hle⟩
  -- `G(x, y)` divides the nonzero integer `F(x, y)`, so it is nonzero and `|G(x, y)| ≤ B`.
  have hdvd : eval ![x, y] G ∣ eval ![x, y] F := map_dvd (eval ![x, y]) hGF
  have hG₀ : eval ![x, y] G ≠ 0 := fun h ↦ hne (zero_dvd_iff.1 (h ▸ hdvd))
  have hGB : |eval ![x, y] G| ≤ B :=
    (Int.le_of_dvd (abs_pos.2 hne) ((abs_dvd_abs _ _).2 hdvd)).trans hle
  have hGB' : |(eval ![x, y] G : ℝ)| ≤ B := by exact_mod_cast hGB
  have key := hcG x y hG₀
  rw [show (r : ℝ) - (r - 1 / 2) = 1 / 2 by ring] at key
  -- Hence `max(|x|, |y|) ^ (1/2) ≤ B / c`, and squaring bounds `max(|x|, |y|)` by `N`.
  set M := max |(x : ℝ)| |(y : ℝ)|
  have hM₀ : 0 ≤ M := (abs_nonneg _).trans (le_max_left _ _)
  have hsqrt : M ^ (1 / 2 : ℝ) ≤ B / c := by
    rw [le_div_iff₀ hc]
    linarith
  have hMN : M ≤ N := calc
    M = (M ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [← rpow_natCast, ← rpow_mul hM₀]
      norm_num
    _ ≤ (B / c) ^ 2 := pow_le_pow_left₀ (by positivity) hsqrt 2
    _ ≤ N := Int.le_ceil _
  simp only [Set.mem_prod, Set.mem_Icc, ← abs_le]
  constructor
  · exact_mod_cast (le_max_left _ _).trans hMN
  · exact_mod_cast (le_max_right _ _).trans hMN

/-- **Thue's theorem** (Thue 1909; Evertse, Corollary 6.4). Let `F ∈ ℤ[X₀, X₁]` be a binary
form such that `F(X, 1)` has at least three distinct complex zeros. Then for every nonzero
`m ∈ ℤ` the Thue equation `F(x, y) = m` has only finitely many integer solutions. The proof is
ineffective: it gives no bound on the solutions. -/
theorem IsHomogeneous.finite_setOfPred_eval_eq {F : MvPolynomial (Fin 2) ℤ} {d : ℕ}
    (hF : F.IsHomogeneous d)
    (hroots : 3 ≤ ((MvPolynomial.aeval ![Polynomial.X, 1] F : Polynomial ℤ).map
      (Int.castRingHom ℂ)).roots.toFinset.card) {m : ℤ} (hm : m ≠ 0) :
    {p : ℤ × ℤ | eval ![p.1, p.2] F = m}.Finite :=
  (hF.finite_setOfPred_eval_ne_zero_and_abs_le hroots |m|).subset fun p hp ↦ by
    rw [Set.mem_ofPred_eq] at hp ⊢
    rw [hp]
    exact ⟨hm, le_rfl⟩

end MvPolynomial
