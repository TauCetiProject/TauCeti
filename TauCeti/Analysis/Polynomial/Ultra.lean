/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Polynomial bounds over ultrametric rings

Over an ultrametric seminormed commutative ring with `‖1‖ = 1`, let `p a` be polynomials of
degree at most one whose constant coefficients have norm at most one and whose linear
coefficients have norm at most `r a`. The `m`-th coefficient of `∏ a ∈ s, p a` is a sum of
products of `m` linear and `#s - m` constant coefficients, so the ultrametric inequality bounds
it by every common bound for the products `∏ a ∈ t, r a` over the `m`-element subsets `t` of `s`
(`TauCeti.norm_coeff_prod_le_of_natDegree_le_one`). Applied to the Leibniz expansion, this
bounds the coefficients of determinants such as `det (1 - X A)` and of the adjugate of
`1 - X A`.

An integral polynomial has norm at most one on the closed unit ball of an ultrametric
seminormed ring with `‖1‖ = 1` (`Polynomial.norm_aeval_le_one`). More generally, let `P` be a
polynomial over a normed field whose coefficients satisfy `‖cₖ‖ Rᵏ ≤ R`, that is, whose Gauss norm
at radius `R` is at most `R`. If `P` vanishes below degree `m` and at `0`, then in an ultrametric
normed algebra it takes at `x` with `‖x‖ ≤ R` a value of norm at most `R (‖x‖ / R) ^ m`
(`Polynomial.norm_aeval_le_mul_div_pow`): every term `cₖ xᵏ` has norm at most `R (‖x‖ / R) ^ k`
(`TauCeti.norm_smul_pow_le_mul_div_pow`).

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§4–5.
-/

public section

open Finset Polynomial

namespace Polynomial

/-- An integral polynomial evaluated at a point of the closed unit ball of a non-archimedean
seminormed ring with `‖1‖ = 1` has norm at most one. -/
theorem norm_aeval_le_one {K : Type*} [SeminormedRing K] [NormOneClass K] [IsUltrametricDist K]
    (p : ℤ[X]) {x : K} (hx : ‖x‖ ≤ 1) : ‖aeval x p‖ ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ ↦ ?_
  exact (IsUltrametricDist.norm_zsmul_le (x ^ i) (p.coeff i)).trans
    ((norm_pow_le x i).trans (pow_le_one₀ (norm_nonneg _) hx))

end Polynomial


namespace TauCeti

/-- **A weighted monomial bound.** If `‖c‖ Rᵏ ≤ R` with `R > 0` and `k ≠ 0`, then
`‖c • xᵏ‖ ≤ R (‖x‖ / R) ^ k` in every normed algebra. -/
theorem norm_smul_pow_le_mul_div_pow {K A : Type*} [NormedField K] [SeminormedRing A]
    [NormedAlgebra K A] {c : K} {k : ℕ} {R : ℝ} (hR : 0 < R) (hk : k ≠ 0)
    (hc : ‖c‖ * R ^ k ≤ R) (x : A) : ‖c • x ^ k‖ ≤ R * (‖x‖ / R) ^ k :=
  calc ‖c • x ^ k‖ ≤ ‖c‖ * ‖x‖ ^ k :=
        (norm_smul_le _ _).trans (by gcongr; exact norm_pow_le' x (Nat.pos_of_ne_zero hk))
    _ = ‖c‖ * R ^ k * (‖x‖ / R) ^ k := by
        rw [div_pow, mul_assoc, mul_div_cancel₀ _ (pow_pos hR k).ne']
    _ ≤ R * (‖x‖ / R) ^ k := by gcongr

/-- **Coefficients of a product of linear polynomials.** Over an ultrametric seminormed
commutative ring with `‖1‖ = 1`, let `p a` be polynomials of degree at most one with
`‖(p a).coeff 0‖ ≤ 1` and `‖(p a).coeff 1‖ ≤ r a`. If `c ≥ 0` bounds `∏ a ∈ t, r a` for every
`m`-element subset `t` of `s`, then `c` bounds the `m`-th coefficient of `∏ a ∈ s, p a`. -/
theorem norm_coeff_prod_le_of_natDegree_le_one {α R : Type*}
    [SeminormedCommRing R] [NormOneClass R] [IsUltrametricDist R]
    {s : Finset α} {p : α → R[X]} {r : α → ℝ}
    (hdeg : ∀ a ∈ s, (p a).natDegree ≤ 1) (h₀ : ∀ a ∈ s, ‖(p a).coeff 0‖ ≤ 1)
    (h₁ : ∀ a ∈ s, ‖(p a).coeff 1‖ ≤ r a) {m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hs : ∀ t ⊆ s, t.card = m → ∏ a ∈ t, r a ≤ c) :
    ‖(∏ a ∈ s, p a).coeff m‖ ≤ c := by
  classical
  induction s using Finset.induction_on generalizing m c with
  | empty =>
    rcases m with _ | m
    · simpa using hs ∅ (empty_subset _) rfl
    · simpa [Polynomial.coeff_one] using hc
  | insert a s ha ih =>
    have hdeg' := fun b hb ↦ hdeg b (mem_insert_of_mem hb)
    have h₀' := fun b hb ↦ h₀ b (mem_insert_of_mem hb)
    have h₁' := fun b hb ↦ h₁ b (mem_insert_of_mem hb)
    have hra : ‖(p a).coeff 1‖ ≤ r a := h₁ a (mem_insert_self a s)
    -- Multiplying by `p a = p₁ X + p₀` mixes the coefficients of `∏ b ∈ s, p b` in degrees
    -- `m` and `m - 1`; the second one is weighted by `‖p₁‖ ≤ r a`.
    have hlow : ‖(p a).coeff 0 * (∏ b ∈ s, p b).coeff m‖ ≤ c :=
      (norm_mul_le _ _).trans <| (mul_le_of_le_one_left (norm_nonneg _)
        (h₀ a (mem_insert_self a s))).trans <|
          ih hdeg' h₀' h₁' hc fun t ht htm ↦ hs t (ht.trans (subset_insert a s)) htm
    rw [prod_insert ha, eq_X_add_C_of_natDegree_le_one (hdeg a (mem_insert_self a s)), add_mul,
      coeff_add, coeff_C_mul, mul_comm (C _), mul_assoc]
    rcases m with _ | k
    · simpa using hlow
    refine IsUltrametricDist.norm_add_le_max _ _ |>.trans (max_le ?_ hlow)
    rw [coeff_X_mul, coeff_C_mul]
    refine (norm_mul_le _ _).trans <| (mul_le_mul_of_nonneg_right hra (norm_nonneg _)).trans ?_
    rcases (norm_nonneg _).trans hra |>.eq_or_lt with hr | hr
    · simpa [← hr] using hc
    rw [← le_div_iff₀' hr]
    refine ih hdeg' h₀' h₁' (div_nonneg hc hr.le) fun t ht htk ↦ ?_
    have hat : a ∉ t := fun h ↦ ha (ht h)
    rw [le_div_iff₀' hr, ← prod_insert hat]
    exact hs _ (insert_subset_insert a ht) (by rw [card_insert_of_notMem hat, htk])

end TauCeti

namespace Polynomial

/-- **Evaluating a polynomial with small coefficients.** In an ultrametric normed algebra over
a normed field, a polynomial with vanishing constant coefficient, vanishing coefficients below
degree `m` and coefficients bounded by `‖cₖ‖ Rᵏ ≤ R` takes at `x` with `‖x‖ ≤ R` a value of norm
at most `R (‖x‖ / R) ^ m`. -/
theorem norm_aeval_le_mul_div_pow {K A : Type*} [NormedField K] [SeminormedRing A]
    [NormedAlgebra K A] [IsUltrametricDist A] {P : K[X]} {R : ℝ} (hR : 0 < R)
    (hP0 : P.coeff 0 = 0) {m : ℕ} (hPm : ∀ k < m, P.coeff k = 0)
    (hP : ∀ k, ‖P.coeff k‖ * R ^ k ≤ R) {x : A} (hx : ‖x‖ ≤ R) :
    ‖aeval x P‖ ≤ R * (‖x‖ / R) ^ m := by
  have hS0 : 0 ≤ ‖x‖ / R := by positivity
  have hS1 : ‖x‖ / R ≤ 1 := (div_le_one hR).mpr hx
  rw [aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun k _ ↦ ?_
  rcases lt_or_ge k m with hk | hk
  · simpa [hPm k hk] using by positivity
  rcases eq_or_ne k 0 with rfl | hk0
  · simpa [hP0] using by positivity
  exact (TauCeti.norm_smul_pow_le_mul_div_pow hR hk0 (hP k) x).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hS0 hS1 hk) hR.le)

end Polynomial
