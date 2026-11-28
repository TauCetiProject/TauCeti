/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Block.Subst
public import TauCeti.RingTheory.MvPolynomial.HasseDeriv.ChainRule
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Hasse derivatives and block-linear changes of variables

This file propagates coefficient-vanishing conditions across Hasse derivatives after a block
change of variables `MvPolynomial.blockSubst A` (defined in
`TauCeti.RingTheory.MvPolynomial.Block.Subst`).

By the chain rule for block-linear substitutions (`MvPolynomial.hasseDeriv_blockSubst`), a Hasse
derivative of `P` of order `I` becomes, in the coordinates of the rows of an invertible matrix `A`,
a combination of derivatives of `blockSubst A⁻¹ P` whose orders `e` have the same block degrees
`∑ j, e (h, j) = ∑ j, I (h, j)` as `I` (`MvPolynomial.blockSubst_inv_hasseDeriv`). Shifting an
exponent vector by such an `e` raises its weighted degree in a single form by at most the weighted
order `∑ h, (∑ j, I (h, j)) / d h` of `I`. No division by integers occurs, so no assumption on the
characteristic is needed.

For a multihomogeneous polynomial in at least two variables per block, lower-tail vanishing at
order zero along every row of `A` upgrades automatically to two-sided concentration around the mean
`card κ / card ι` (`MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero_of_notMem_Ioo`).

## Main results

* `MvPolynomial.hasseDeriv_blockSubst`: the chain rule for a block substitution.
* `MvPolynomial.blockSubst_inv_hasseDeriv`: a Hasse derivative of `P`, written in the coordinates
  of the rows of `A`, is a combination of the derivatives of `blockSubst A⁻¹ P` of the same block
  degrees.
* `TauCeti.coeff_blockSubst_inv_hasseDeriv_eq_zero_of_weight_gt` transfers coefficient vanishing
  above a weighted threshold to the derivative after allowing for the normalized derivative order.
  This and the one-row result use the shifted-coefficient criterion
  `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero_of_forall_coeff_add`.
* `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero`,
  `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero_of_le`: if the coefficients of
  `blockSubst A⁻¹ P` vanish below (or at most) the threshold `θ` in the weighted degree
  `∑ h, N (h, i) / d h`, then those of `blockSubst A⁻¹ (hasseDeriv I P)` vanish below (or at most)
  `θ` minus the weighted order of `I`.
* `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero_of_notMem_Ioo`: for a multihomogeneous `P` in
  at least two variables per block, lower-tail vanishing at order zero along every row of `A`
  forces the coefficients of `blockSubst A⁻¹ (hasseDeriv I P)` to vanish outside the open interval
  `(m / card ι - 2 m η, m / card ι + 2 m (card ι - 1) η)`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press
  (2006), §7.5.14 and Lemma 7.5.15.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace theorem*,
  Ann. of Math. 177 (2013), §13, Proposition 13.6.
-/

public section

namespace MvPolynomial

open Finset Matrix

section CommSemiring

variable {R κ ι : Type*} [CommSemiring R] [Fintype ι] [Fintype κ] [DecidableEq κ] [DecidableEq ι]

/-- **The chain rule for a block substitution**:
`∂^I (Q(A x)) = ∑_e c_{e,I} (∂^e Q)(A x)`, where `c_{e,I}` is the coefficient of `X ^ I` in the
substituted monomial `(A X) ^ e`, and the sum runs over the `e` with the block degrees
`∑ j, e (h, j) = ∑ j, I (h, j)` of `I`. -/
theorem hasseDeriv_blockSubst (A : Matrix ι ι R) (I : κ × ι →₀ ℕ) (Q : MvPolynomial (κ × ι) R) :
    hasseDeriv I (blockSubst A Q) =
      ∑ e ∈ univ.finsuppAntidiag I.degree with ∀ h, ∑ j, e (h, j) = ∑ j, I (h, j),
        (blockSubst A (monomial e (1 : R))).coeff I • blockSubst A (hasseDeriv e Q) := by
  simpa [blockSubst_eq_aeval] using hasseDeriv_aeval_blockLinearForm_hasseDeriv
    (fun _ j i ↦ A j i) Q 0 I

end CommSemiring

section CommRing

variable {R κ ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι] {A : Matrix ι ι R}

/-- A Hasse derivative of `P`, written in the coordinates of the rows of an invertible matrix `A`,
is a combination of the derivatives of `blockSubst A⁻¹ P` (that is, of `P` in those coordinates)
whose orders have the same block degrees as the order `I`. -/
theorem blockSubst_inv_hasseDeriv [Fintype κ] [DecidableEq κ] (hA : IsUnit A.det) (I : κ × ι →₀ ℕ)
    (P : MvPolynomial (κ × ι) R) :
    blockSubst A⁻¹ (hasseDeriv I P) =
      ∑ e ∈ univ.finsuppAntidiag I.degree with ∀ h, ∑ j, e (h, j) = ∑ j, I (h, j),
        (blockSubst A (monomial e (1 : R))).coeff I • hasseDeriv e (blockSubst A⁻¹ P) := by
  conv_lhs => rw [← blockSubst_blockSubst_inv hA P]
  simp only [hasseDeriv_blockSubst, map_sum, map_smul, blockSubst_inv_blockSubst hA]

/-- If the coefficients of `blockSubst A⁻¹ P` vanish at every shift `J + e` of `J` by an order `e`
with the block degrees of `I`, then the coefficient of `blockSubst A⁻¹ (hasseDeriv I P)` at `J`
vanishes. -/
theorem coeff_blockSubst_hasseDeriv_eq_zero_of_forall_coeff_add [Finite κ]
    (hA : IsUnit A.det) {P : MvPolynomial (κ × ι) R} {I J : κ × ι →₀ ℕ}
    (hP : ∀ e : κ × ι →₀ ℕ, (∀ h, ∑ j, e (h, j) = ∑ j, I (h, j)) →
      (blockSubst A⁻¹ P).coeff (J + e) = 0) :
    (blockSubst A⁻¹ (hasseDeriv I P)).coeff J = 0 := by
  classical
  have := Fintype.ofFinite κ
  rw [blockSubst_inv_hasseDeriv hA, coeff_sum]
  refine sum_eq_zero fun e he ↦ ?_
  rw [AddMonoidAlgebra.coeff_smul_apply, hasseDeriv_coeff, hP e (mem_filter.1 he).2, mul_zero,
    smul_zero]

/-- Suppose `A.det` is a unit and the coefficients of `blockSubst A⁻¹ P` vanish above weight
`θ`. If the weights in block `h` are bounded below by `b h`, the coefficients of
`blockSubst A⁻¹ (hasseDeriv I P)` vanish above `θ` minus the sum of the blockwise lower bounds
times the corresponding block orders of `I`. -/
theorem _root_.TauCeti.coeff_blockSubst_inv_hasseDeriv_eq_zero_of_weight_gt_of_blockwise_le
    [Fintype κ] (hA : IsUnit A.det) {P : MvPolynomial (κ × ι) R}
    {u : κ × ι → ℝ} {b : κ → ℝ} {θ : ℝ} (hw : ∀ h i, b h ≤ u (h, i))
    (hP : ∀ n : κ × ι →₀ ℕ, θ < n.weight u → (blockSubst A⁻¹ P).coeff n = 0)
    {I J : κ × ι →₀ ℕ} (hJ : θ - ∑ h, b h * ((∑ i, I (h, i) : ℕ) : ℝ) < J.weight u) :
    (blockSubst A⁻¹ (hasseDeriv I P)).coeff J = 0 := by
  refine coeff_blockSubst_hasseDeriv_eq_zero_of_forall_coeff_add hA fun e he ↦ hP (J + e) ?_
  have hshift : ∑ h, b h * ((∑ i, I (h, i) : ℕ) : ℝ) ≤ e.weight u := by
    rw [Finsupp.weight_prod_eq_sum]
    refine sum_le_sum fun h _ ↦ ?_
    rw [← he h, Nat.cast_sum, mul_sum]
    simp only [nsmul_eq_mul]
    refine sum_le_sum fun i _ ↦ ?_
    rw [mul_comm (b h)]
    exact mul_le_mul_of_nonneg_left (hw h i) (Nat.cast_nonneg _)
  rw [map_add]
  linarith

/-- Suppose `A.det` is a unit, every weight is at least `-γ`, and coefficients of
`blockSubst A⁻¹ P` vanish above normalized weight `θ`. The coefficients of
`blockSubst A⁻¹ (hasseDeriv I P)` then vanish above `θ` plus `γ` times the normalized order.
Both weights and derivative orders are normalized by the original block degrees. -/
theorem _root_.TauCeti.coeff_blockSubst_inv_hasseDeriv_eq_zero_of_weight_gt
    [Fintype κ] (hA : IsUnit A.det) {P : MvPolynomial (κ × ι) R} {r : κ → ℕ}
    {w : κ → ι → ℝ} {γ θ : ℝ} (hw : ∀ h i, -γ ≤ w h i)
    (hP : ∀ n : κ × ι →₀ ℕ, θ < n.weight (fun p ↦ w p.1 p.2 / r p.1) →
      (blockSubst A⁻¹ P).coeff n = 0) {I J : κ × ι →₀ ℕ}
    (hJ : θ + γ * (∑ h, ((∑ i, I (h, i) : ℕ) : ℝ) / r h) <
      J.weight (fun p ↦ w p.1 p.2 / r p.1)) :
    (blockSubst A⁻¹ (hasseDeriv I P)).coeff J = 0 := by
  refine TauCeti.coeff_blockSubst_inv_hasseDeriv_eq_zero_of_weight_gt_of_blockwise_le hA
    (b := fun h ↦ -γ / r h) (fun h i ↦ div_le_div_of_nonneg_right (hw h i) (Nat.cast_nonneg _))
    hP ?_
  have hloss : ∑ h, (-γ / (r h : ℝ)) * ((∑ i, I (h, i) : ℕ) : ℝ) =
      -(γ * ∑ h, ((∑ i, I (h, i) : ℕ) : ℝ) / r h) := by
    rw [mul_sum, ← sum_neg_distrib]
    exact sum_congr rfl fun h _ ↦ by ring
  rwa [hloss, sub_neg_eq_add]

/-- **Vanishing along a form passes to Hasse derivatives** (Bombieri–Gubler, §7.5.14). Fix a
row `i` of the invertible matrix `A` and a multidegree `d`. If the coefficients of
`blockSubst A⁻¹ P` vanish at every exponent vector `N` whose weighted degree
`∑ h, N (h, i) / d h` in the variables `X (h, i)` is at most `θ`, then the coefficients of
`blockSubst A⁻¹ (hasseDeriv I P)` vanish at every `J` whose weighted degree is at most `θ` minus
the weighted order `∑ h, (∑ j, I (h, j)) / d h` of `I`. -/
theorem coeff_blockSubst_hasseDeriv_eq_zero_of_le [Fintype κ] (hA : IsUnit A.det)
    {P : MvPolynomial (κ × ι) R} {d : κ → ℕ} {i : ι} {θ : ℝ}
    (hP : ∀ N : κ × ι →₀ ℕ, ∑ h, (N (h, i) : ℝ) / d h ≤ θ → (blockSubst A⁻¹ P).coeff N = 0)
    {I J : κ × ι →₀ ℕ}
    (hJ : ∑ h, (J (h, i) : ℝ) / d h ≤ θ - ∑ h, ((∑ j, I (h, j) : ℕ) : ℝ) / d h) :
    (blockSubst A⁻¹ (hasseDeriv I P)).coeff J = 0 := by
  refine coeff_blockSubst_hasseDeriv_eq_zero_of_forall_coeff_add hA fun e he ↦ hP _ ?_
  -- Shifting by `e` raises the weighted degree in row `i` by at most the weighted order of `I`.
  have hle : ∑ h, (e (h, i) : ℝ) / d h ≤ ∑ h, ((∑ j, I (h, j) : ℕ) : ℝ) / d h := by
    refine sum_le_sum fun h _ ↦ div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    rw [← he h]
    exact_mod_cast single_le_sum (f := fun j ↦ e (h, j)) (fun _ _ ↦ Nat.zero_le _) (mem_univ i)
  simp only [Finsupp.coe_add, Pi.add_apply, Nat.cast_add, add_div, sum_add_distrib]
  linarith

/-- Strict form of `coeff_blockSubst_hasseDeriv_eq_zero_of_le`: if the coefficients of
`blockSubst A⁻¹ P` vanish whenever `∑ h, N (h, i) / d h < θ`, then those of
`blockSubst A⁻¹ (hasseDeriv I P)` vanish whenever `∑ h, J (h, i) / d h` is strictly below `θ`
minus the weighted order of `I`. -/
theorem coeff_blockSubst_hasseDeriv_eq_zero [Fintype κ] (hA : IsUnit A.det)
    {P : MvPolynomial (κ × ι) R} {d : κ → ℕ} {i : ι} {θ : ℝ}
    (hP : ∀ N : κ × ι →₀ ℕ, ∑ h, (N (h, i) : ℝ) / d h < θ → (blockSubst A⁻¹ P).coeff N = 0)
    {I J : κ × ι →₀ ℕ}
    (hJ : ∑ h, (J (h, i) : ℝ) / d h < θ - ∑ h, ((∑ j, I (h, j) : ℕ) : ℝ) / d h) :
    (blockSubst A⁻¹ (hasseDeriv I P)).coeff J = 0 :=
  coeff_blockSubst_hasseDeriv_eq_zero_of_le hA
    (θ := ∑ h, (J (h, i) : ℝ) / d h + ∑ h, ((∑ j, I (h, j) : ℕ) : ℝ) / d h)
    (fun N hN ↦ hP N (hN.trans_lt (add_lt_of_lt_sub_right hJ))) (add_sub_cancel_right _ _).ge

/-- **Two-sided concentration from lower-tail vanishing** (Bombieri–Gubler, Lemma 7.5.15). Suppose
`ι` has at least two elements, `P` is multihomogeneous of multidegree `d`, and the coefficients of
`blockSubst A⁻¹ P` vanish whenever the weighted degree along any row `i'` of `A` is at most
`card κ / card ι - card κ * η`. Then for every order `I` of weighted order at most `card κ * η`,
the coefficients of `blockSubst A⁻¹ (hasseDeriv I P)` vanish at every `J` whose weighted degree
along some row `i` lies outside the open interval
`(card κ / card ι - 2 * card κ * η, card κ / card ι + 2 * card κ * (card ι - 1) * η)`. -/
theorem coeff_blockSubst_hasseDeriv_eq_zero_of_notMem_Ioo [Fintype κ] [DecidableEq κ] [Nontrivial ι]
    (hA : IsUnit A.det) {P : MvPolynomial (κ × ι) R} {d : κ → ℕ} (hP_hom : IsMultiHomogeneous d P)
    {η : ℝ} (hP : ∀ (i' : ι) (N : κ × ι →₀ ℕ),
      ∑ h, (N (h, i') : ℝ) / d h ≤ (Fintype.card κ : ℝ) / Fintype.card ι - Fintype.card κ * η →
      (blockSubst A⁻¹ P).coeff N = 0)
    {I J : κ × ι →₀ ℕ} (hI : ∑ h, ((∑ j, I (h, j) : ℕ) : ℝ) / d h ≤ Fintype.card κ * η)
    {i : ι} (hJ : ∑ h, (J (h, i) : ℝ) / d h ∉
      Set.Ioo ((Fintype.card κ : ℝ) / Fintype.card ι - 2 * Fintype.card κ * η)
        ((Fintype.card κ : ℝ) / Fintype.card ι + 2 * Fintype.card κ * (Fintype.card ι - 1) * η)) :
    (blockSubst A⁻¹ (hasseDeriv I P)).coeff J = 0 := by
  by_contra hne
  apply hJ
  -- Every row `i'` satisfies the strict lower bound, since `coeff J ≠ 0`.
  have hlow (i' : ι) :
      (Fintype.card κ : ℝ) / Fintype.card ι - 2 * Fintype.card κ * η <
        ∑ h, (J (h, i') : ℝ) / d h := by
    by_contra! hle
    exact hne (coeff_blockSubst_hasseDeriv_eq_zero_of_le hA (hP i') (by linarith))
  refine ⟨hlow i, ?_⟩
  -- Multihomogeneity bounds the sum over all rows by `card κ`; summing `hlow` over the remaining
  -- `card ι - 1 ≥ 1` rows bounds row `i` strictly from above.
  have htot : ∑ i', ∑ h, (J (h, i') : ℝ) / d h ≤ Fintype.card κ := by
    rw [sum_comm]
    refine (sum_le_sum (g := fun _ : κ ↦ (1 : ℝ)) fun h _ ↦ ?_).trans_eq (by simp)
    rcases eq_or_ne (d h) 0 with hd0 | hd0
    · simp [hd0]
    · simp_rw [div_eq_mul_inv, ← sum_mul, ← div_eq_mul_inv]
      refine (div_le_one (Nat.cast_pos.2 (Nat.pos_of_ne_zero hd0))).2 ?_
      have hdeg := isMultiHomogeneous_iff.1 ((hP_hom.hasseDeriv I).blockSubst A⁻¹) J hne h
      exact_mod_cast hdeg.trans_le (Nat.sub_le _ _)
  obtain ⟨i₁, hi₁⟩ := exists_ne i
  have hne_erase : (univ.erase i).Nonempty := ⟨i₁, mem_erase.2 ⟨hi₁, mem_univ _⟩⟩
  have herase : ((Fintype.card ι : ℝ) - 1) *
      ((Fintype.card κ : ℝ) / Fintype.card ι - 2 * Fintype.card κ * η) <
      ∑ i' ∈ univ.erase i, ∑ h, (J (h, i') : ℝ) / d h := by
    have hcard : (#(univ.erase i) : ℝ) = (Fintype.card ι : ℝ) - 1 := by
      have hk : 1 ≤ Fintype.card ι := Nat.one_le_iff_ne_zero.2 Fintype.card_ne_zero
      rw [card_erase_of_mem (mem_univ i), card_univ, Nat.cast_sub hk, Nat.cast_one]
    simpa only [sum_const, nsmul_eq_mul, hcard] using
      sum_lt_sum_of_nonempty hne_erase fun i' _ ↦ hlow i'
  have hsplit := add_sum_erase univ (fun i' ↦ ∑ h, (J (h, i') : ℝ) / d h) (mem_univ i)
  have hk0 : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hid : (Fintype.card κ : ℝ) - ((Fintype.card ι : ℝ) - 1) *
      ((Fintype.card κ : ℝ) / Fintype.card ι - 2 * Fintype.card κ * η) =
      (Fintype.card κ : ℝ) / Fintype.card ι + 2 * Fintype.card κ * (Fintype.card ι - 1) * η := by
    field_simp
    ring
  linarith

end CommRing

/-! ### Examples -/

/-- The loss in `coeff_blockSubst_hasseDeriv_eq_zero` cannot be dropped. In one block of one
variable, with `A = 1` and `d = 1`, the coefficients of `X ^ 2` vanish at every exponent below
`2`, while its first Hasse derivative `2 X` has a nonzero coefficient at the exponent `1 < 2`;
the lemma only promises vanishing below `2 - 1`. -/
example : (blockSubst (1 : Matrix Unit Unit ℚ)⁻¹
    (hasseDeriv (Finsupp.single ((), ()) 1) (X ((), ()) ^ 2 : MvPolynomial (Unit × Unit) ℚ))).coeff
      (Finsupp.single ((), ()) 1) = 2 := by
  simp [X_pow_eq_monomial, hasseDeriv_monomial, coeff_monomial, ← Finsupp.single_tsub]

/-- `Nontrivial ι` cannot be dropped in `coeff_blockSubst_hasseDeriv_eq_zero_of_notMem_Ioo`: with
`ι = Unit`, `κ = Unit`, `d = 1`, `A = 1`, `P = X`, and `η = 1 / 2`, the polynomial vanishes at the
only exponent `N = 0` below `1 - 1 / 2 = 1 / 2`, yet at `I = 0` and `J = 1` the weighted degree `1`
lies outside `Set.Ioo 0 1` while the coefficient of `P` at `J` is `1`. -/
example :
    let P : MvPolynomial (Unit × Unit) ℚ := X ((), ())
    (∀ (_ : Unit) (N : Unit × Unit →₀ ℕ),
      (N ((), ()) : ℝ) / 1 ≤ 1 / 1 - 1 * (1 / 2) →
      (blockSubst (1 : Matrix Unit Unit ℚ)⁻¹ P).coeff N = 0) ∧
    ((1 : ℝ) / 1 ∉ Set.Ioo (1 / 1 - 2 * 1 * (1 / 2)) (1 / 1 + 2 * 1 * (1 - 1) * (1 / 2))) ∧
    (blockSubst (1 : Matrix Unit Unit ℚ)⁻¹ (hasseDeriv 0 P)).coeff
      (Finsupp.single ((), ()) 1) = 1 := by
  refine ⟨fun _ N hN ↦ ?_, by norm_num, by simp [coeff_X]⟩
  have h0 : N = 0 := by
    ext ⟨⟨⟩, ⟨⟩⟩
    have : (N ((), ()) : ℝ) < 1 := by linarith
    exact_mod_cast Nat.lt_one_iff.1 (by exact_mod_cast this)
  simp [h0]

end MvPolynomial
