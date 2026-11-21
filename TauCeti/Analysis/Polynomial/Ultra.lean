/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.IsNonarchimedean
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree
public import Mathlib.Analysis.Normed.Group.Ultra
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
seminormed ring with `‖1‖ = 1` (`Polynomial.norm_aeval_le_one`).

Let `f` be a nonarchimedean, nonnegative, submultiplicative function from a semiring to a
linearly ordered monoid with zero `Γ` whose multiplication is monotone on nonnegative elements,
such as a nonarchimedean ring seminorm (`Γ = ℝ`) or a valuation. Bounds
`f (p.coeff i) ≤ M ^ (d - i)` on the coefficients of polynomials `p` of degree at most `d` pass to
the product of two polynomials, since each coefficient of a product is a sum of products of
coefficients (`Polynomial.apply_coeff_mul_le_pow`). If moreover `f 1 ≤ 1`, they pass to powers
(`Polynomial.apply_coeff_pow_le_pow`), and if also `f 0 ≤ 1`, over a commutative semiring, to
finite products (`Polynomial.apply_coeff_prod_le_pow`). The function `f` need not vanish at `0`.

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

section CoeffBound

variable {R Γ : Type*} [MonoidWithZero Γ] [LinearOrder Γ] [PosMulMono Γ] [MulPosMono Γ]
  {f : R → Γ} {M : Γ}

section Semiring

variable [Semiring R]

/-- **Coefficient bounds multiply.** Let `p` and `q` be polynomials of degree at most `d` and `e`
with `f (p.coeff i) ≤ M ^ (d - i)` and `f (q.coeff i) ≤ M ^ (e - i)` for every `i`. Then
`f ((p * q).coeff k) ≤ M ^ (d + e - k)` for every `k`, for every nonarchimedean, nonnegative,
submultiplicative function `f` into a linearly ordered monoid with zero whose multiplication is
monotone on nonnegative elements, such as a nonarchimedean ring seminorm or a valuation. -/
theorem apply_coeff_mul_le_pow (hf_nn : ∀ a, 0 ≤ f a)
    (hf_mul : ∀ a b, f (a * b) ≤ f a * f b) (hf_na : IsNonarchimedean f) {p q : R[X]}
    {d e : ℕ} (hpd : p.natDegree ≤ d) (hqe : q.natDegree ≤ e)
    (hp : ∀ i, f (p.coeff i) ≤ M ^ (d - i)) (hq : ∀ i, f (q.coeff i) ≤ M ^ (e - i)) (k : ℕ) :
    f ((p * q).coeff k) ≤ M ^ (d + e - k) := by
  -- The coefficient is a sum over `i + j = k`, dominated by one of its terms.
  rw [coeff_mul]
  obtain ⟨⟨i, j⟩, hij, hle⟩ := hf_na.finset_image_add_of_nonempty
    (fun x : ℕ × ℕ ↦ p.coeff x.1 * q.coeff x.2) (s := antidiagonal k)
    ⟨(k, 0), mem_antidiagonal.mpr (add_zero k)⟩
  rw [mem_antidiagonal] at hij
  refine hle.trans ?_
  have key (a b : ℕ) : f (p.coeff a * q.coeff b) ≤ M ^ (d - a + (e - b)) := by
    rw [pow_add]
    exact (hf_mul _ _).trans (mul_le_mul (hp a) (hq b) (hf_nn _) ((hf_nn _).trans (hp a)))
  -- A term with a vanishing factor is rewritten as `p.coeff (d + 1) * q.coeff (k - d)` or
  -- `p.coeff (k - e) * q.coeff (e + 1)`, which also vanishes and is bounded by `M ^ (d + e - k)`.
  change f (p.coeff i * q.coeff j) ≤ _
  rcases le_or_gt j e with hj | hj
  · rcases le_or_gt i d with hi | hi
    · exact (key i j).trans_eq (by congr 1; omega)
    · rw [coeff_eq_zero_of_natDegree_lt (hpd.trans_lt hi), zero_mul,
        ← zero_mul (q.coeff (k - d)), ← coeff_eq_zero_of_natDegree_lt (hpd.trans_lt d.lt_succ_self)]
      exact (key _ _).trans_eq (by congr 1; omega)
  · rw [coeff_eq_zero_of_natDegree_lt (hqe.trans_lt hj), mul_zero,
      ← mul_zero (p.coeff (k - e)), ← coeff_eq_zero_of_natDegree_lt (hqe.trans_lt e.lt_succ_self)]
    exact (key _ _).trans_eq (by congr 1; omega)

/-- **Coefficient bounds pass to powers.** Let `p` be a polynomial of degree at most `d` with
`f (p.coeff i) ≤ M ^ (d - i)` for every `i`. Then `f ((p ^ n).coeff k) ≤ M ^ (n * d - k)` for
every `n` and `k`, for every `f` as in `Polynomial.apply_coeff_mul_le_pow` with `f 1 ≤ 1`. -/
theorem apply_coeff_pow_le_pow (hf_nn : ∀ a, 0 ≤ f a)
    (hf_mul : ∀ a b, f (a * b) ≤ f a * f b) (hf1 : f 1 ≤ 1) (hf_na : IsNonarchimedean f)
    {p : R[X]} {d : ℕ} (hpd : p.natDegree ≤ d) (hp : ∀ i, f (p.coeff i) ≤ M ^ (d - i))
    (n k : ℕ) : f ((p ^ n).coeff k) ≤ M ^ (n * d - k) := by
  induction n generalizing k with
  | zero =>
    -- `f 0 ≤ 1` is the bound on the coefficient of `p` in degree `d + 1`.
    have hf0 := hp (d + 1)
    rw [coeff_eq_zero_of_natDegree_lt (hpd.trans_lt d.lt_succ_self),
      Nat.sub_eq_zero_of_le d.le_succ, pow_zero] at hf0
    rw [pow_zero, coeff_one]
    split_ifs <;> simp [hf0, hf1]
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact apply_coeff_mul_le_pow hf_nn hf_mul hf_na (natDegree_pow_le_of_le n hpd) hpd ih hp k

end Semiring

variable [CommSemiring R]

/-- **Coefficient bounds pass to finite products.** Let `p a` be polynomials over a commutative
semiring. Suppose that for each `a ∈ s`, the polynomial `p a` has degree at most `d a` and
satisfies `f ((p a).coeff i) ≤ M ^ (d a - i)` for every `i`. Then
`f ((∏ a ∈ s, p a).coeff k) ≤ M ^ (∑ a ∈ s, d a - k)` for every `k`, for every `f` as in
`Polynomial.apply_coeff_mul_le_pow` with `f 0 ≤ 1` and `f 1 ≤ 1`. -/
theorem apply_coeff_prod_le_pow (hf_nn : ∀ a, 0 ≤ f a)
    (hf_mul : ∀ a b, f (a * b) ≤ f a * f b) (hf0 : f 0 ≤ 1) (hf1 : f 1 ≤ 1)
    (hf_na : IsNonarchimedean f)
    {ι : Type*} (s : Finset ι) (p : ι → R[X]) (d : ι → ℕ)
    (hpd : ∀ a ∈ s, (p a).natDegree ≤ d a)
    (hp : ∀ a ∈ s, ∀ i, f ((p a).coeff i) ≤ M ^ (d a - i)) (k : ℕ) :
    f ((∏ a ∈ s, p a).coeff k) ≤ M ^ (∑ a ∈ s, d a - k) := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
    rw [prod_empty, sum_empty, coeff_one]
    split_ifs <;> simp [hf0, hf1]
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    simp only [forall_mem_insert] at hpd hp
    exact apply_coeff_mul_le_pow hf_nn hf_mul hf_na hpd.1
      ((natDegree_prod_le _ _).trans (sum_le_sum hpd.2)) hp.1 (ih hpd.2 hp.2) k

end CoeffBound

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
