/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Basic
import TauCeti.Algebra.Polynomial.Taylor
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Polynomial bounds over ultrametric rings

Over an ultrametric seminormed ring, the Gauss bound `∀ n, ‖p.coeff n‖ * c ^ n ≤ B` at a
nonnegative radius `c` is preserved under scalar multiplication
(`Polynomial.norm_coeff_smul_mul_pow_le`), finite sums (`Polynomial.norm_coeff_sum_mul_pow_le`),
products (`Polynomial.norm_coeff_mul_mul_pow_le`, `Polynomial.norm_coeff_pow_mul_pow_le`,
`Polynomial.norm_coeff_prod_mul_pow_le`), Taylor shifts `p(X + r)` by points `r` of `‖r‖ ≤ c`
(`Polynomial.norm_coeff_taylor_mul_pow_le`), and degree truncation with radius rescaling
(`Polynomial.norm_coeff_sum_range_monomial_mul_pow_le`), while a linear factor `X - a` with
`‖a‖ ≤ c` (`Polynomial.norm_coeff_X_sub_C_mul_pow_le`) and a truncated geometric series
(`Polynomial.norm_coeff_sum_monomial_mul_neg_pow_mul_pow_le`) satisfy explicit weighted bounds.

Over an ultrametric seminormed commutative ring with `‖1‖ = 1`, let `p a` be polynomials of
degree at most one whose constant coefficients have norm at most one and whose linear
coefficients have norm at most `r a`. The `m`-th coefficient of `∏ a ∈ s, p a` is a sum of
products of `m` linear and `#s - m` constant coefficients, so the ultrametric inequality bounds
it by every common bound for the products `∏ a ∈ t, r a` over the `m`-element subsets `t` of `s`
(`TauCeti.norm_coeff_prod_le_of_natDegree_le_one`). Applied to the Leibniz expansion, this
bounds the coefficients of determinants such as `det (1 - X A)` and of the adjugate of
`1 - X A`.

An integral polynomial has norm at most one on the closed unit ball of an ultrametric
seminormed ring with `‖1‖ = 1` (`Polynomial.norm_aeval_le_one`).

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

section WeightedCoeff

variable {R : Type*} [SeminormedRing R]

/-- Left multiplication of a polynomial by a scalar multiplies a weighted coefficient bound at a
nonnegative radius `c` by the norm of the scalar. -/
theorem norm_coeff_smul_mul_pow_le (a : R) {p : R[X]} {c B : ℝ} (hc : 0 ≤ c)
    (hp : ∀ n, ‖p.coeff n‖ * c ^ n ≤ B) (n : ℕ) :
    ‖(a • p).coeff n‖ * c ^ n ≤ ‖a‖ * B := by
  rw [AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  calc ‖a * p.coeff n‖ * c ^ n ≤ ‖a‖ * ‖p.coeff n‖ * c ^ n :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (pow_nonneg hc n)
    _ = ‖a‖ * (‖p.coeff n‖ * c ^ n) := mul_assoc _ _ _
    _ ≤ ‖a‖ * B := mul_le_mul_of_nonneg_left (hp n) (norm_nonneg a)

/-- The `c`-weighted coefficients of `X - C a` are bounded by `c` whenever `‖a‖ ≤ c`. -/
theorem norm_coeff_X_sub_C_mul_pow_le [NormOneClass R] {a : R} {c : ℝ} (ha : ‖a‖ ≤ c) (n : ℕ) :
    ‖(X - C a).coeff n‖ * c ^ n ≤ c := by
  have hc : 0 ≤ c := (norm_nonneg a).trans ha
  rcases n with _ | _ | n
  · simpa [coeff_X] using ha
  · simp [coeff_X]
  · simp [coeff_X, hc]

/-- If `‖v‖ ≤ ϱ⁻¹` with `0 < ϱ`, the `ϱ`-weighted coefficients of the truncated geometric
polynomial `∑ k ∈ range N, monomial k (v * (-v) ^ k)` are bounded by `‖v‖`. -/
theorem norm_coeff_sum_monomial_mul_neg_pow_mul_pow_le {v : R} {ϱ : ℝ} (hϱ0 : 0 < ϱ)
    (hv : ‖v‖ ≤ ϱ⁻¹) (N n : ℕ) :
    ‖(∑ k ∈ range N, monomial k (v * (-v) ^ k)).coeff n‖ * ϱ ^ n ≤ ‖v‖ := by
  rw [finsetSum_coeff]
  by_cases hn : n ∈ range N
  · rw [sum_eq_single n (fun j _ hjn ↦ by simp [hjn]) (fun hn' ↦ absurd hn hn'),
      coeff_monomial_same]
    have hvϱ : ‖v‖ * ϱ ≤ 1 :=
      (mul_le_mul_of_nonneg_right hv hϱ0.le).trans_eq (inv_mul_cancel₀ hϱ0.ne')
    calc ‖v * (-v) ^ n‖ * ϱ ^ n
        ≤ ‖v‖ * ‖-v‖ ^ n * ϱ ^ n :=
          mul_le_mul_of_nonneg_right (TauCeti.norm_mul_pow_le _ _ _) (by positivity)
      _ = ‖v‖ * (‖v‖ * ϱ) ^ n := by rw [norm_neg, mul_assoc, ← mul_pow]
      _ ≤ ‖v‖ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ (by positivity) hvϱ) (norm_nonneg _)
      _ = ‖v‖ := mul_one _
  · rw [sum_eq_zero fun j hj ↦ by simp [ne_of_mem_of_not_mem hj hn]]
    simp [norm_nonneg v]

/-- Truncating a polynomial `p` below degree `N` rescales a `ϱ`-weighted coefficient bound `C`
(`0 < ϱ ≤ B`) to the `B`-weighted bound `C * (B / ϱ) ^ (N - 1)`. -/
theorem norm_coeff_sum_range_monomial_mul_pow_le {p : R[X]} {ϱ B C : ℝ} (hϱ0 : 0 < ϱ)
    (hϱB : ϱ ≤ B) (hp : ∀ n, ‖p.coeff n‖ * ϱ ^ n ≤ C) (N n : ℕ) :
    ‖(∑ d ∈ range N, monomial d (p.coeff d)).coeff n‖ * B ^ n ≤ C * (B / ϱ) ^ (N - 1) := by
  have hC0 : 0 ≤ C := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hp 0)
  have hBϱ0 : 0 ≤ B / ϱ := div_nonneg (hϱ0.le.trans hϱB) hϱ0.le
  rw [finsetSum_coeff]
  by_cases hn : n ∈ range N
  · rw [sum_eq_single n (fun j _ hjn ↦ by simp [hjn]) (fun hn' ↦ absurd hn hn'),
      coeff_monomial_same]
    have hnle : n ≤ N - 1 := by have := mem_range.1 hn; omega
    have hBϱ : B ^ n = ϱ ^ n * (B / ϱ) ^ n := by rw [← mul_pow, mul_div_cancel₀ _ hϱ0.ne']
    rw [hBϱ, ← mul_assoc]
    exact mul_le_mul (hp n) (pow_le_pow_right₀ ((one_le_div hϱ0).2 hϱB) hnle) (pow_nonneg hBϱ0 n)
      hC0
  · rw [sum_eq_zero fun j hj ↦ by simp [ne_of_mem_of_not_mem hj hn]]
    simp only [norm_zero, zero_mul]
    exact mul_nonneg hC0 (pow_nonneg hBϱ0 _)

variable [IsUltrametricDist R]

/-- Over an ultrametric seminormed ring, a common nonnegative bound on the `c`-weighted
coefficients of a finite family of polynomials bounds the `c`-weighted coefficients of their
sum. -/
theorem norm_coeff_sum_mul_pow_le {ι : Type*} (s : Finset ι) (f : ι → R[X]) {c B : ℝ}
    (hc : 0 ≤ c) (hB : 0 ≤ B) (hf : ∀ i ∈ s, ∀ n, ‖(f i).coeff n‖ * c ^ n ≤ B) (n : ℕ) :
    ‖(∑ i ∈ s, f i).coeff n‖ * c ^ n ≤ B := by
  rcases (pow_nonneg hc n).eq_or_lt with hcn | hcn
  · simpa [← hcn] using hB
  rw [← le_div_iff₀ hcn, finsetSum_coeff]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_nonneg hB hcn.le) fun i hi ↦ ?_
  exact (le_div_iff₀ hcn).2 (hf i hi n)

/-- Over an ultrametric seminormed ring, bounds `Bp` and `Bq` on the `c`-weighted coefficients of
`p` and `q` at `c ≥ 0` multiply to bound the `c`-weighted coefficients of `p * q`. -/
theorem norm_coeff_mul_mul_pow_le {p q : R[X]} {c Bp Bq : ℝ} (hc : 0 ≤ c)
    (hp : ∀ n, ‖p.coeff n‖ * c ^ n ≤ Bp) (hq : ∀ n, ‖q.coeff n‖ * c ^ n ≤ Bq) (n : ℕ) :
    ‖(p * q).coeff n‖ * c ^ n ≤ Bp * Bq := by
  have hBp : 0 ≤ Bp := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hp 0)
  have hBq : 0 ≤ Bq := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hq 0)
  rcases (pow_nonneg hc n).eq_or_lt with hcn | hcn
  · simpa [← hcn] using mul_nonneg hBp hBq
  rw [← le_div_iff₀ hcn, coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (div_nonneg (mul_nonneg hBp hBq) hcn.le) fun x hx ↦ ?_
  rw [le_div_iff₀ hcn, ← mem_antidiagonal.1 hx, pow_add]
  calc ‖p.coeff x.1 * q.coeff x.2‖ * (c ^ x.1 * c ^ x.2)
      ≤ ‖p.coeff x.1‖ * ‖q.coeff x.2‖ * (c ^ x.1 * c ^ x.2) :=
        mul_le_mul_of_nonneg_right (norm_mul_le _ _) (by positivity)
    _ = (‖p.coeff x.1‖ * c ^ x.1) * (‖q.coeff x.2‖ * c ^ x.2) := by ring
    _ ≤ Bp * Bq :=
        mul_le_mul (hp x.1) (hq x.2) (mul_nonneg (norm_nonneg _) (pow_nonneg hc _)) hBp

/-- Over an ultrametric seminormed ring with `‖1‖ = 1`, a bound `B` on the `c`-weighted
coefficients of `p` at `c ≥ 0` gives the bound `B ^ m` on those of `p ^ m`. -/
theorem norm_coeff_pow_mul_pow_le [NormOneClass R] {p : R[X]} {c B : ℝ} (hc : 0 ≤ c)
    (hp : ∀ n, ‖p.coeff n‖ * c ^ n ≤ B) (m n : ℕ) :
    ‖(p ^ m).coeff n‖ * c ^ n ≤ B ^ m := by
  induction m generalizing n with
  | zero => rcases n with _ | n <;> simp [coeff_one]
  | succ m ih =>
    rw [pow_succ, pow_succ]
    exact norm_coeff_mul_mul_pow_le hc ih hp n

/-- The `c`-weighted coefficients of `(X - C a) ^ m` are bounded by `c ^ m` whenever `‖a‖ ≤ c`. -/
theorem norm_coeff_X_sub_C_pow_mul_pow_le [NormOneClass R] {a : R} {c : ℝ} (ha : ‖a‖ ≤ c)
    (m n : ℕ) : ‖((X - C a) ^ m).coeff n‖ * c ^ n ≤ c ^ m :=
  norm_coeff_pow_mul_pow_le ((norm_nonneg a).trans ha) (norm_coeff_X_sub_C_mul_pow_le ha) m n

/-- **Taylor invariance of ultrametric Gauss bounds.** Over an ultrametric seminormed ring,
shifting `p` to `taylor r p = p(X + r)` by a point `r` with `‖r‖ ≤ c` preserves any bound on its
`c`-weighted coefficients: binomial coefficients have norm at most `1`. -/
theorem norm_coeff_taylor_mul_pow_le {p : R[X]} {r : R} {c B : ℝ} (hr : ‖r‖ ≤ c)
    (hp : ∀ n, ‖p.coeff n‖ * c ^ n ≤ B) (n : ℕ) :
    ‖(taylor r p).coeff n‖ * c ^ n ≤ B := by
  have hc : 0 ≤ c := (norm_nonneg r).trans hr
  have hB : 0 ≤ B := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hp 0)
  rcases (pow_nonneg hc n).eq_or_lt with hcn | hcn
  · simpa [← hcn] using hB
  rw [coeff_taylor_eq_sum (Nat.lt_succ_self p.natDegree), ← le_div_iff₀ hcn]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (div_nonneg hB hcn.le) fun k _ ↦ ?_
  rw [le_div_iff₀ hcn]
  calc ‖(k + n).choose n • (p.coeff (k + n) * r ^ k)‖ * c ^ n
      ≤ ‖p.coeff (k + n) * r ^ k‖ * c ^ n :=
        mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_nsmul_le _ _) hcn.le
    _ ≤ ‖p.coeff (k + n)‖ * c ^ k * c ^ n := by
        refine mul_le_mul_of_nonneg_right ?_ hcn.le
        exact (TauCeti.norm_mul_pow_le _ _ _).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg r) hr k) (norm_nonneg _))
    _ = ‖p.coeff (k + n)‖ * c ^ (k + n) := by rw [mul_assoc, ← pow_add]
    _ ≤ B := hp (k + n)

end WeightedCoeff

/-- Over an ultrametric seminormed commutative ring with `‖1‖ = 1`, bounds `B i` on the
`c`-weighted coefficients of a finite family `f i` at `c ≥ 0` multiply to bound the `c`-weighted
coefficients of `∏ i ∈ s, f i`. -/
theorem norm_coeff_prod_mul_pow_le {ι R : Type*} [SeminormedCommRing R] [NormOneClass R]
    [IsUltrametricDist R] (s : Finset ι) (f : ι → R[X]) {c : ℝ} {B : ι → ℝ} (hc : 0 ≤ c)
    (hf : ∀ i ∈ s, ∀ n, ‖(f i).coeff n‖ * c ^ n ≤ B i) (n : ℕ) :
    ‖(∏ i ∈ s, f i).coeff n‖ * c ^ n ≤ ∏ i ∈ s, B i := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty => rcases n with _ | n <;> simp [coeff_one]
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi]
    exact norm_coeff_mul_mul_pow_le hc (hf i (mem_insert_self i s))
      (ih fun j hj ↦ hf j (mem_insert_of_mem hj)) n

end Polynomial


namespace TauCeti

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
