/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Resultant.Coleman
public import TauCeti.RingTheory.PowerSeries.Entire.Majorant
import TauCeti.Algebra.Order.BigOperators.ProdSubProd
import TauCeti.GroupTheory.Perm.GapCrossing
import TauCeti.RingTheory.Polynomial.Resultant.Basic

/-!
# Coefficient bounds for Coleman's transform

Let `R` be an ultrametric seminormed commutative ring with `‖1‖ = 1`. Let `P = ∑ aⱼ Tʲ` and
`B = ∑ bₗ Tˡ` be polynomials over `R` with `B(0) = 0`, let `ρ` be a nonnegative antitone sequence
with `‖aⱼ‖ ≤ ∏ i < j, ρᵢ`, and let `β` satisfy `‖bₗ‖ ρₜˡ ≤ βₜ` for all `t` and all `l ≥ 1`. Then
every bounded Coleman transform `D_(n,m)(B, P)` satisfies

`‖coeff k D_(n,m)(B, P)‖ ≤ ∏ t < k, βₜ` (`Polynomial.norm_coeff_colemanDBounded_le`).

If `P = ∏ (1 - αᵢ T)` with `‖αᵢ‖ ≤ ρᵢ`, then `D(B, P) = ∏ (1 - B(αᵢ) T)` and the bound is the
ultrametric estimate for the elementary symmetric functions of the `B(αᵢ)`. The theorem asserts
the same bound for every `P` obeying the coefficient bounds, over any coefficient ring, with no
access to roots. It is uniform in the ranks `n` and `m`, so it applies to all truncations of an
entire series `F` with Newton majorant `ρ` along an entire series `B` with `B(0) = 0`, with
`βₜ = β_B(ρₜ)` the Coleman majorant (`PowerSeries.norm_coeff_colemanDBounded_trunc_le`). These
products are the coefficient bounds of an entire series, so they control the limit of the finite
transforms that defines Coleman's transform with entire functional input.

The estimate is read off the Leibniz expansion of the Sylvester matrix defining the resultant,
term by term. In a nonzero term, the permutation `σ` of the `n + m` columns moves each of the
first `n` columns `x` (carrying coefficients of `1 - T B(X)`) down to a row `σ x ≥ x`, picking
`b_(σ x - x) T` when `σ x > x`, and moves each of the last `m` columns up, picking
`a_(x - σ x)`. Count both kinds of moves across each gap between consecutive rows: a column moved
across `j` gaps is charged `ρ₀, …, ρⱼ₋₁` in order on the `a` side, while on the `b` side every gap
it crosses is charged `ρ_r`, where `r` is its rank by decreasing target row. At each gap the two
counts agree, and the `a` charges are never larger than the `b` charges after sorting, so
`∏ ‖a‖ ≤ ∏ ρ_r ^ (σ x - x)` (`Equiv.Perm.prod_prod_range_le_prod_pow_upRank`). The ranks
enumerate the moved columns, so each term is bounded by `∏ t < k, βₜ`.

## Main results

* `Polynomial.norm_coeff_colemanDBounded_le`: the uniform coefficient bound for the bounded
  Coleman transform of polynomials.
* `PowerSeries.norm_coeff_colemanDBounded_trunc_le`: the bound `∏ i < k, β_B(ρᵢ)` for the
  transforms of truncations of power series.

## References

* R. Coleman, *p-adic Banach spaces and families of modular forms*, Invent. Math. **127** (1997),
  417–479, Appendix A3.
-/

public section

open Equiv Finset

namespace Polynomial

variable {R : Type*} [SeminormedCommRing R] [NormOneClass R] [IsUltrametricDist R]

/-- **Coleman's coefficient bound.** Let `P` and `B` be polynomials over an ultrametric seminormed
ring with `‖1‖ = 1` and `B(0) = 0`. If `ρ` is a nonnegative antitone sequence with
`‖coeff j P‖ ≤ ∏ i < j, ρ i` for `j ≤ n`, and `‖coeff l B‖ * ρ t ^ l ≤ β t` for every `t` and every
`l ≥ 1`, then the `k`-th coefficient of Coleman's transform `D_(n,m)(B, P)` has norm at most
`∏ t < k, β t`, for all ranks `n` and degree bounds `m`. -/
theorem norm_coeff_colemanDBounded_le {B P : R[X]} {n m : ℕ} {ρ β : ℕ → ℝ}
    (hB₀ : B.coeff 0 = 0) (hρ₀ : ∀ i, 0 ≤ ρ i) (hρ : Antitone ρ)
    (hP : ∀ j ≤ n, ‖P.coeff j‖ ≤ ∏ i ∈ range j, ρ i)
    (hβ : ∀ t j, ‖B.coeff (j + 1)‖ * ρ t ^ (j + 1) ≤ β t) (k : ℕ) :
    ‖(colemanDBounded B P n m).coeff k‖ ≤ ∏ t ∈ range k, β t := by
  have hβ₀ (t : ℕ) : 0 ≤ β t :=
    (mul_nonneg (norm_nonneg _) (pow_nonneg (hρ₀ t) _)).trans (hβ t 0)
  have hprod : 0 ≤ ∏ t ∈ range k, β t := prod_nonneg fun t _ ↦ hβ₀ t
  rw [colemanDBounded_def, resultant, Matrix.det_apply, finsetSum_coeff]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hprod fun σ _ ↦ ?_
  rw [coeff_smul, norm_units_zsmul]
  set M := sylvester ((P.reflect n).map C) (1 - C X * B.map C) n m with hM_def
  by_cases hzero : ∃ x, M (σ x) x = 0
  · obtain ⟨x, hx⟩ := hzero
    have : ∏ i, M (σ i) i = 0 := prod_eq_zero (mem_univ x) hx
    rw [this, coeff_zero, norm_zero]
    exact hprod
  -- Hence each of the first `n` columns `x` is moved to a row in `[x, x + m]` and each of the last
  -- `m` columns to a row in `[x - n, x]`, since the other entries vanish.
  have hband (x : Fin (n + m)) : ((x : ℕ) < n → (x : ℕ) ≤ σ x ∧ (σ x : ℕ) ≤ x + m) ∧
      (n ≤ (x : ℕ) → (x : ℕ) ≤ σ x + n ∧ (σ x : ℕ) ≤ x) := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> by_contra hc <;> refine hzero ⟨x, ?_⟩
    · rw [hM_def, sylvester_apply_of_lt _ _ _ _ h, ite_eq_right hc]
    · rw [hM_def, sylvester_apply_of_le _ _ _ _ h, ite_eq_right hc]
  -- Otherwise every entry of the term is a monomial: `1` or `-b_(σ x - x) T` in the first `n`
  -- columns, according as `σ x = x` or not, and `a_(x - σ x)` in the last `m` columns.
  set c : Fin (n + m) → R := fun x ↦
    if (x : ℕ) < σ x then -B.coeff (σ x - x) else if (x : ℕ) < n then 1 else P.coeff (x - σ x)
  set e : Fin (n + m) → ℕ := fun x ↦ if (x : ℕ) < σ x then 1 else 0
  have hM (x : Fin (n + m)) : M (σ x) x = C (c x) * X ^ e x := by
    rcases lt_or_ge (x : ℕ) n with h | h
    · rw [hM_def, sylvester_apply_of_lt _ _ _ _ h, ite_eq_left ((hband x).1 h)]
      simp only [coeff_sub, coeff_one, coeff_C_mul, coeff_map, c, e, ite_eq_left h]
      by_cases hx : (x : ℕ) < σ x
      · rw [ite_eq_right (by omega), ite_eq_left hx, ite_eq_left hx, zero_sub, pow_one, map_neg,
          neg_mul, mul_comm]
      · have : (σ x : ℕ) - x = 0 := by omega
        simp [hx, this, hB₀]
    · have hσx : ¬(x : ℕ) < σ x := by have := (hband x).2 h; omega
      rw [hM_def, sylvester_apply_of_le _ _ _ _ h, ite_eq_left ((hband x).2 h)]
      simp only [coeff_map, coeff_reflect, c, e, ite_eq_right hσx, ite_eq_right (not_lt.2 h)]
      rw [revAt_le (by have := (hband x).2 h; omega)]
      simp only [pow_zero, mul_one]
      have := (hband x).2 h
      congr 2
      omega
  simp_rw [hM]
  rw [prod_mul_distrib, ← map_prod, prod_pow_eq_pow_sum, coeff_C_mul_X_pow]
  split_ifs with hk
  swap
  · rw [norm_zero]
    exact hprod
  have hsum : ∑ x, e x = #{x : Fin (n + m) | (x : ℕ) < σ x} := by
    simp [e, sum_boole]
  -- the weight of each column of the term, apart from the factors `ρ` of the `a`'s
  set w : Fin (n + m) → ℝ := fun x ↦ if (x : ℕ) < σ x then ‖B.coeff (σ x - x)‖ else 1
  have hw₀ (x : Fin (n + m)) : 0 ≤ w x := by
    simp only [w]
    split_ifs <;> positivity
  have hc (x : Fin (n + m)) : ‖c x‖ ≤ w x * ∏ i ∈ range ((x : ℕ) - σ x), ρ i := by
    simp only [c, w]
    by_cases hx : (x : ℕ) < σ x
    · simp [hx, Nat.sub_eq_zero_of_le hx.le]
    by_cases hn : (x : ℕ) < n
    · have : (x : ℕ) - σ x = 0 := by have := (hband x).1 hn; omega
      simp [hx, hn, this]
    · rw [ite_eq_right hx, ite_eq_right hn, ite_eq_right hx, one_mul]
      exact hP _ (by have := (hband x).2 (not_lt.1 hn); omega)
  have hwρ (x : Fin (n + m)) : w x * ρ (σ.upRank x) ^ ((σ x : ℕ) - x) ≤
      if (x : ℕ) < σ x then β (σ.upRank x) else 1 := by
    simp only [w]
    by_cases hx : (x : ℕ) < σ x
    · obtain ⟨j, hj⟩ : ∃ j, (σ x : ℕ) - x = j + 1 := ⟨σ x - x - 1, by omega⟩
      rw [ite_eq_left hx, ite_eq_left hx, hj]
      exact hβ _ j
    · rw [ite_eq_right hx, ite_eq_right hx, Nat.sub_eq_zero_of_le (not_lt.1 hx), pow_zero,
        one_mul]
  calc ‖∏ x : Fin (n + m), c x‖ ≤ ∏ x : Fin (n + m), ‖c x‖ := TauCeti.norm_prod_le_prod_norm _ _
    _ ≤ ∏ x : Fin (n + m), (w x * ∏ i ∈ range ((x : ℕ) - σ x), ρ i) :=
        prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun x _ ↦ hc x
    _ = (∏ x : Fin (n + m), w x) * ∏ x : Fin (n + m), ∏ i ∈ range ((x : ℕ) - σ x), ρ i :=
        prod_mul_distrib
    _ ≤ (∏ x : Fin (n + m), w x) * ∏ x : Fin (n + m), ρ (σ.upRank x) ^ ((σ x : ℕ) - x) :=
        mul_le_mul_of_nonneg_left (σ.prod_prod_range_le_prod_pow_upRank
          (fun x hx ↦ ((hband x).1 hx).1) (fun x hx ↦ ((hband x).2 hx).2) hρ₀ hρ)
          (prod_nonneg fun x _ ↦ hw₀ x)
    _ = ∏ x : Fin (n + m), w x * ρ (σ.upRank x) ^ ((σ x : ℕ) - x) := prod_mul_distrib.symm
    _ ≤ ∏ x : Fin (n + m), if (x : ℕ) < σ x then β (σ.upRank x) else 1 :=
        prod_le_prod₀ (fun x _ ↦ mul_nonneg (hw₀ x) (pow_nonneg (hρ₀ _) _)) fun x _ ↦ hwρ x
    _ = ∏ x ∈ {x : Fin (n + m) | (x : ℕ) < σ x}, β (σ.upRank x) := (prod_filter _ _).symm
    _ = ∏ t ∈ range k, β t := by rw [Perm.prod_upRank, hk, hsum]

end Polynomial

namespace PowerSeries

open Finset

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]

/-- **Coleman's bound for truncations.** Let `ρ` be a nonnegative antitone Newton majorant of a
power series `F`, `‖coeff j F‖ ≤ ∏ i < j, ρ i`, and let `B` be restricted at every radius `ρ i`
with `B(0) = 0`. Then the Coleman transforms of the truncations of `F` along the truncations of
`B` satisfy `‖coeff k D_(n,m)(trunc a B, trunc b F)‖ ≤ ∏ i < k, β_B(ρ i)`, uniformly in the ranks,
degree bounds and truncation orders. In particular this bounds
`D_(N,M)(trunc (M + 1) B, trunc (N + 1) F)`. -/
theorem norm_coeff_colemanDBounded_trunc_le {F B : R⟦X⟧} {ρ : ℕ → ℝ} (hρ₀ : ∀ i, 0 ≤ ρ i)
    (hρ : Antitone ρ) (hF : ∀ j, ‖coeff j F‖ ≤ ∏ i ∈ range j, ρ i)
    (hB : ∀ i, B.IsRestricted (ρ i)) (hB₀ : coeff 0 B = 0) (n m a b k : ℕ) :
    ‖(Polynomial.colemanDBounded (trunc a B) (trunc b F) n m).coeff k‖ ≤
      ∏ i ∈ range k, colemanMajorant B (ρ i) := by
  refine Polynomial.norm_coeff_colemanDBounded_le (by simp [coeff_trunc, hB₀]) hρ₀ hρ
    (fun j _ ↦ ?_) (fun t j ↦ ?_) k
  · rw [coeff_trunc]
    split_ifs
    · exact hF j
    · simpa using prod_nonneg fun i _ ↦ hρ₀ i
  · rw [coeff_trunc]
    split_ifs
    · exact norm_coeff_succ_mul_pow_le_colemanMajorant (hB t) j
    · simpa using colemanMajorant_nonneg B (hρ₀ t)

end PowerSeries
