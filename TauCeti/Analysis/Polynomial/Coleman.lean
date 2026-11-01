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
import TauCeti.RingTheory.PowerSeries.TateAlgebra

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

Over a normed ring the same bound controls differences. If `P₂ - P₁` and `B₂ - B₁` satisfy the
hypotheses after multiplication by `r ≥ 1`, then the `k`-th coefficients of `D_(n,m)(B₂, P₂)` and
`D_(n,m)(B₁, P₁)` differ by at most `r⁻¹ ∏ t < k, βₜ`
(`Polynomial.dist_coeff_colemanDBounded_mul_le`). To see this, join the inputs by the segments
`Bₛ = B₁ + s (B₂ - B₁)` and `Pₛ = P₁ + s (P₂ - P₁)` over the polynomial ring `R[s]`, and give
`R[s]` the Gauss norm at radius `r`, in which `‖s‖ = r`. The coefficient bound over this ring says
that the `i`-th coefficient in `s` of the `k`-th coefficient of `D_(n,m)(Bₛ, Pₛ)` has norm at most
`r⁻ⁱ ∏ t < k, βₜ`, and the difference of the two transforms is the sum of these coefficients for
`i ≥ 1`. No polynomial identity for the transform is needed beyond its compatibility with ring
homomorphisms.

For an entire `F` with Newton majorant `ρ` and an entire `B`, the tails of the truncations from
order `a` of `B` and `b` of `F` are small against the majorants at the radii `c ρᵢ` for any
`c ≥ 1`. So lengthening the truncations moves the coefficients by at most
`c ^ (-min a b) ∏ i < k, β_B(c² ρᵢ)` (`PowerSeries.dist_coeff_colemanDBounded_trunc_mul_le`).
Hence the coefficients of the finite transforms `D_(N,M)(trunc (M + 1) B, trunc (N + 1) F)` are
Cauchy as `N` and `M` tend to infinity independently
(`PowerSeries.cauchySeq_coeff_colemanDBounded_trunc`).

## Main results

* `Polynomial.norm_coeff_colemanDBounded_le`: the uniform coefficient bound for the bounded
  Coleman transform of polynomials.
* `PowerSeries.norm_coeff_colemanDBounded_trunc_le`: the bound `∏ i < k, β_B(ρᵢ)` for the
  transforms of truncations of power series.
* `Polynomial.dist_coeff_colemanDBounded_mul_le`: the perturbation bound for the bounded
  Coleman transform of polynomials.
* `PowerSeries.dist_coeff_colemanDBounded_trunc_mul_le`: the explicit continuity estimate in the
  truncation orders of `B` and `F`.
* `PowerSeries.cauchySeq_coeff_colemanDBounded_trunc`: the coefficients of the finite transforms
  of truncations of entire series are Cauchy.

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

namespace Polynomial

section Perturbation

open TauCeti.PowerSeries

variable {R : Type*} [NormedCommRing R] [NormOneClass R] [IsUltrametricDist R]

omit [NormOneClass R] in
/-- In the Gauss norm at a radius `r > 0`, the linear polynomial `a + d Y` has weighted norm at
most `M` once both `‖a‖` and `‖d‖ r` do. -/
private theorem norm_polynomialToRestricted_C_add_X_mul_C_mul_le {r : ℝ} [Fact (0 < r)] {a d : R}
    {w M : ℝ} (hw : 0 ≤ w) (ha : ‖a‖ * w ≤ M) (hd : ‖d‖ * r * w ≤ M) :
    ‖polynomialToRestricted r (C a + X * C d)‖ * w ≤ M := by
  have hM : 0 ≤ M := (mul_nonneg (norm_nonneg _) hw).trans ha
  rcases hw.eq_or_lt with rfl | hw
  · simpa using hM
  rw [← le_div_iff₀ hw, norm_le_iff (div_nonneg hM hw.le)]
  intro i
  rw [le_div_iff₀ hw]
  rcases i with _ | _ | i
  · simpa using ha
  · simpa [mul_right_comm] using hd
  · simpa [coeff_C, coeff_X_mul] using hM

/-- **Coleman's perturbation bound.** Let `ρ` be a nonnegative antitone sequence and `r ≥ 1`. If
`P₁` has Newton majorant `ρ` up to degree `n`, the perturbation `P₂ - P₁` satisfies the same
bound after multiplication by `r`, and the coefficients of positive degree of `B₁` and of
`r (B₂ - B₁)` are bounded by `β` at every radius `ρ t`, where `B₁(0) = B₂(0) = 0`, then the
coefficients of the bounded Coleman transforms satisfy
`dist (coeff k D_(n,m)(B₂, P₂)) (coeff k D_(n,m)(B₁, P₁)) * r ≤ ∏ t < k, β t`.

Thus perturbing the inputs by a factor `r⁻¹` relative to their majorants moves every coefficient
of the transform by at most `r⁻¹` times its coefficient bound
`Polynomial.norm_coeff_colemanDBounded_le`, uniformly in the ranks `n` and degree bounds `m`. -/
theorem dist_coeff_colemanDBounded_mul_le {B₁ B₂ P₁ P₂ : R[X]} {n m : ℕ} {ρ β : ℕ → ℝ} {r : ℝ}
    (hB₁ : B₁.coeff 0 = 0) (hB₂ : B₂.coeff 0 = 0) (hρ₀ : ∀ i, 0 ≤ ρ i) (hρ : Antitone ρ)
    (hr : 1 ≤ r) (hP₁ : ∀ j ≤ n, ‖P₁.coeff j‖ ≤ ∏ i ∈ range j, ρ i)
    (hP : ∀ j ≤ n, ‖(P₂ - P₁).coeff j‖ * r ≤ ∏ i ∈ range j, ρ i)
    (hβ₁ : ∀ t j, ‖B₁.coeff (j + 1)‖ * ρ t ^ (j + 1) ≤ β t)
    (hβ : ∀ t j, ‖(B₂ - B₁).coeff (j + 1)‖ * r * ρ t ^ (j + 1) ≤ β t) (k : ℕ) :
    dist ((colemanDBounded B₂ P₂ n m).coeff k) ((colemanDBounded B₁ P₁ n m).coeff k) * r ≤
      ∏ t ∈ range k, β t := by
  have hr₀ : 0 < r := one_pos.trans_le hr
  have : Fact (0 < r) := ⟨hr₀⟩
  have hprod : 0 ≤ ∏ t ∈ range k, β t := prod_nonneg fun t _ ↦
    (mul_nonneg (norm_nonneg _) (pow_nonneg (hρ₀ t) _)).trans (hβ₁ t 0)
  -- Join the inputs by the segment `Q₁ + Y (Q₂ - Q₁)`, over the polynomial ring in a parameter `Y`.
  set seg : R[X] → R[X] → R[X][X] := fun Q₁ Q₂ ↦ Q₁.map C + C X * (Q₂ - Q₁).map C with hseg
  have hcoeff (Q₁ Q₂ : R[X]) (j : ℕ) :
      (seg Q₁ Q₂).coeff j = C (Q₁.coeff j) + X * C ((Q₂ - Q₁).coeff j) := by
    simp [hseg, coeff_C_mul]
  set f : R[X] := (colemanDBounded (seg B₁ B₂) (seg P₁ P₂) n m).coeff k with hf
  have heval (a : R) : f.eval a =
      (colemanDBounded (B₁ + C a * (B₂ - B₁)) (P₁ + C a * (P₂ - P₁)) n m).coeff k := by
    have hmap (Q₁ Q₂ : R[X]) : (seg Q₁ Q₂).map (evalRingHom a) = Q₁ + C a * (Q₂ - Q₁) := by
      ext j
      simp [hcoeff, coeff_C_mul]
    rw [← hmap, ← hmap, ← colemanDBounded_map, coeff_map, coe_evalRingHom]
  -- At `Y = 1` and `Y = 0` the segment gives the two transforms.
  have h₁ : f.eval 1 = (colemanDBounded B₂ P₂ n m).coeff k := by simp [heval]
  have h₀ : f.coeff 0 = (colemanDBounded B₁ P₁ n m).coeff k := by
    simp [coeff_zero_eq_eval_zero, heval]
  -- In the Gauss norm at radius `r`, Coleman's bound applies to the whole segment.
  set ψ : R[X] →+* PowerSeries.IsRestricted.subring (R := R) r :=
    (polynomialToRestricted (R := R) r).toRingHom with hψ
  have hbound : ‖ψ f‖ ≤ ∏ t ∈ range k, β t := by
    have h := norm_coeff_colemanDBounded_le (B := (seg B₁ B₂).map ψ) (P := (seg P₁ P₂).map ψ)
      (n := n) (m := m) (by simp [hcoeff, hB₁, hB₂]) hρ₀ hρ
      (fun j hj ↦ by
        rw [coeff_map, hcoeff, ← mul_one ‖_‖]
        exact norm_polynomialToRestricted_C_add_X_mul_C_mul_le zero_le_one
          (by simpa using hP₁ j hj) (by simpa using hP j hj))
      (fun t j ↦ by
        rw [coeff_map, hcoeff]
        exact norm_polynomialToRestricted_C_add_X_mul_C_mul_le (pow_nonneg (hρ₀ t) _) (hβ₁ t j)
          (hβ t j)) k
    rwa [← colemanDBounded_map, coeff_map] at h
  have hcoeffs (i : ℕ) : ‖f.coeff (i + 1)‖ * r ≤ ∏ t ∈ range k, β t :=
    calc ‖f.coeff (i + 1)‖ * r ≤ ‖f.coeff (i + 1)‖ * r ^ (i + 1) :=
          mul_le_mul_of_nonneg_left (le_self_pow₀ hr (Nat.succ_ne_zero i)) (norm_nonneg _)
      _ ≤ ‖ψ f‖ := by
          simpa [hψ] using norm_coeff_mul_pow_le (ψ f) (i + 1)
      _ ≤ ∏ t ∈ range k, β t := hbound
  -- The difference of the two transforms is the sum of the coefficients of positive degree.
  rw [← h₁, ← h₀, eval_eq_sum_range, sum_range_succ', dist_eq_norm]
  simp only [one_pow, mul_one, pow_zero, add_sub_cancel_right]
  rw [← le_div_iff₀ hr₀]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_nonneg hprod hr₀.le)
    fun i _ ↦ (le_div_iff₀ hr₀).2 (hcoeffs i)

end Perturbation

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

/-- **Continuity of Coleman's transform in the truncation orders.** Let `ρ` be a nonnegative
antitone Newton majorant of `F`, let `c ≥ 1`, and let `B` be restricted at every radius
`c² ρ i` with `B(0) = 0`. Lengthening the truncations of `F` and `B` from orders `b` and `a` to
`b' ≥ b` and `a' ≥ a` moves the `k`-th coefficient of every bounded Coleman transform by at most
`c ^ (-min a b) ∏ i < k, β_B(c² ρ i)`: the tails of `F` and `B` from these orders on are smaller
than their majorants at the radii scaled by `c`. -/
theorem dist_coeff_colemanDBounded_trunc_mul_le {F B : R⟦X⟧} {ρ : ℕ → ℝ} (hρ₀ : ∀ i, 0 ≤ ρ i)
    (hρ : Antitone ρ) (hF : ∀ j, ‖coeff j F‖ ≤ ∏ i ∈ range j, ρ i) {c : ℝ} (hc : 1 ≤ c)
    (hB : ∀ i, B.IsRestricted (c ^ 2 * ρ i)) (hB₀ : coeff 0 B = 0) {a a' b b' : ℕ}
    (ha : a ≤ a') (hb : b ≤ b') (n m k : ℕ) :
    dist ((Polynomial.colemanDBounded (trunc a' B) (trunc b' F) n m).coeff k)
        ((Polynomial.colemanDBounded (trunc a B) (trunc b F) n m).coeff k) * c ^ min a b ≤
      ∏ i ∈ range k, colemanMajorant B (c ^ 2 * ρ i) := by
  have hc₀ : 0 ≤ c := zero_le_one.trans hc
  have hcρ (i : ℕ) : 0 ≤ c * ρ i := mul_nonneg hc₀ (hρ₀ i)
  have hprod (j : ℕ) : ∏ i ∈ range j, c * ρ i = c ^ j * ∏ i ∈ range j, ρ i := by
    rw [prod_mul_distrib, prod_const, card_range]
  have hprod₀ (j : ℕ) : 0 ≤ ∏ i ∈ range j, c * ρ i := prod_nonneg fun i _ ↦ hcρ i
  have hpow (t j : ℕ) : c ^ j * (c * ρ t) ^ j = (c ^ 2 * ρ t) ^ j := by
    rw [← mul_pow, ← mul_assoc, sq]
  have hβ₀ (t : ℕ) : 0 ≤ colemanMajorant B (c ^ 2 * ρ t) :=
    colemanMajorant_nonneg B (mul_nonneg (pow_nonneg hc₀ 2) (hρ₀ t))
  refine Polynomial.dist_coeff_colemanDBounded_mul_le (ρ := fun i ↦ c * ρ i)
    (by simp [coeff_trunc, hB₀]) (by simp [coeff_trunc, hB₀]) hcρ
    (fun i j hij ↦ mul_le_mul_of_nonneg_left (hρ hij) hc₀) (one_le_pow₀ hc)
    (fun j _ ↦ ?_) (fun j _ ↦ ?_) (fun t j ↦ ?_) (fun t j ↦ ?_) k
  · rw [coeff_trunc]
    split_ifs
    · rw [hprod]
      exact (hF j).trans (le_mul_of_one_le_left (prod_nonneg fun i _ ↦ hρ₀ i) (one_le_pow₀ hc))
    · simpa using hprod₀ j
  · rw [Polynomial.coeff_sub, coeff_trunc, coeff_trunc]
    split_ifs with h' h
    · simpa using hprod₀ j
    · rw [sub_zero, hprod, mul_comm]
      exact mul_le_mul (pow_le_pow_right₀ hc ((min_le_right a b).trans (not_lt.1 h)))
        (hF j) (norm_nonneg _) (pow_nonneg hc₀ j)
    · omega
    · simpa using hprod₀ j
  · rw [coeff_trunc]
    split_ifs
    · refine le_trans ?_ (norm_coeff_succ_mul_pow_le_colemanMajorant (hB t) j)
      rw [← hpow]
      exact mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_left (pow_nonneg (hcρ t) _) (one_le_pow₀ hc)) (norm_nonneg _)
    · simpa using hβ₀ t
  · rw [Polynomial.coeff_sub, coeff_trunc, coeff_trunc]
    split_ifs with h' h
    · simpa using hβ₀ t
    · rw [sub_zero, mul_assoc]
      refine le_trans ?_ (norm_coeff_succ_mul_pow_le_colemanMajorant (hB t) j)
      rw [← hpow]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hc ((min_le_left a b).trans (not_lt.1 h))) (pow_nonneg (hcρ t) _))
        (norm_nonneg _)
    · omega
    · simpa using hβ₀ t

/-- **The finite Coleman transforms are Cauchy.** Let `F` be an entire series with `F(0) = 1`
and `B` an entire series with `B(0) = 0`. For each `k`, the `k`-th coefficients of the finite
transforms `D_(N,M)(trunc (M + 1) B, trunc (N + 1) F)` form a Cauchy family as `N` and `M` tend
to infinity independently. -/
theorem cauchySeq_coeff_colemanDBounded_trunc {F B : R⟦X⟧} (hF : F.IsEntire)
    (hF₀ : coeff 0 F = 1) (hB : B.IsEntire) (hB₀ : coeff 0 B = 0) (k : ℕ) :
    CauchySeq fun NM : ℕ × ℕ ↦
      (Polynomial.colemanDBounded (trunc (NM.2 + 1) B) (trunc (NM.1 + 1) F) NM.1 NM.2).coeff k := by
  obtain ⟨ρ, hρ₀, hρ, -, hFρ⟩ := hF.exists_newtonMajorant (by simp [hF₀])
  set bound := ∏ i ∈ range k, colemanMajorant B (2 ^ 2 * ρ i)
  -- the transforms at smaller truncation orders keep their value at larger ranks
  have hrank {N M N' M' : ℕ} (hN : N ≤ N') (hM : M ≤ M') :
      Polynomial.colemanDBounded (trunc (M + 1) B) (trunc (N + 1) F) N M =
        Polynomial.colemanDBounded (trunc (M + 1) B) (trunc (N + 1) F) N' M' := by
    have hP0 : (trunc (N + 1) F).coeff 0 = 1 := by simp [coeff_trunc, hF₀]
    have hB0 : (trunc (M + 1) B).coeff 0 = 0 := by simp [coeff_trunc, hB₀]
    have hdP := Nat.lt_succ_iff.1 (natDegree_trunc_lt F N)
    have hdB := Nat.lt_succ_iff.1 (natDegree_trunc_lt B M)
    rw [← Polynomial.colemanD_eq_colemanDBounded hdP hdB hP0 hB0,
      Polynomial.colemanD_eq_colemanDBounded (hdP.trans hN) (hdB.trans hM) hP0 hB0]
  refine Metric.cauchySeq_iff'.2 fun ε hε ↦ ?_
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (bound / ε) one_lt_two
  refine ⟨(K, K), fun ⟨N, M⟩ ⟨hN, hM⟩ ↦ ?_⟩
  dsimp only at hN hM ⊢
  have hle := dist_coeff_colemanDBounded_trunc_mul_le (fun i ↦ (hρ₀ i).le) hρ hFρ one_le_two
    (fun i ↦ hB.isRestricted _) hB₀ (Nat.succ_le_succ hM) (Nat.succ_le_succ hN) N M k
  rw [← hrank hN hM, min_self] at hle
  have h2 : (0 : ℝ) < 2 ^ (K + 1) := by positivity
  rw [div_lt_iff₀ hε] at hK
  refine lt_of_mul_lt_mul_right (hle.trans_lt ?_) h2.le
  calc bound < 2 ^ K * ε := hK
    _ ≤ ε * 2 ^ (K + 1) := by rw [pow_succ, mul_comm]; gcongr; norm_num

end PowerSeries
