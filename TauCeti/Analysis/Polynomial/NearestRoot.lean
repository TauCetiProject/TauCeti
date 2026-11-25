/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Polynomial.MahlerMeasure
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import TauCeti.Algebra.Polynomial.Splits
import TauCeti.Analysis.Polynomial.SupNorm.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# The derivative at a root and the nearest root of a polynomial

Let `f ∈ ℂ[X]` have degree `d`, leading coefficient `a` and roots `α₁, …, α_d`, and let `M(f)` be
its Mahler measure. The discriminant pairs the roots into a square,
`disc f = a ^ (2 d - 2) ∏_{i < j} (αᵢ - αⱼ) ^ 2`, while the derivative at the root `α = α₁` is
`f'(α) = a ∏_{j ≠ 1} (α - αⱼ)`. Splitting off the factors that involve `α₁` and bounding every
other difference by `|αᵢ - αⱼ| ≤ 2 max(1, |αᵢ|) max(1, |αⱼ|)` gives, for `d ≥ 2`,

`|disc f| ≤ (2 ^ C(d - 1, 2) M(f) ^ (d - 2) |f'(α)|) ^ 2`.

For `P ∈ ℤ[X]` with nonzero discriminant, `|disc P| ≥ 1`, so the derivative at every complex root
is bounded below: `1 ≤ 2 ^ C(d - 1, 2) M(P) ^ (d - 2) |P'(α)|`, which also holds in degree one,
where `P'(α)` is the leading coefficient.

If `α` is a root of `f` nearest to a point `z`, then `|α - αⱼ| ≤ 2 |z - αⱼ|` for every other root,
and comparing `f(z) = a ∏ (z - αⱼ)` with `f'(α)` gives `|z - α| |f'(α)| ≤ 2 ^ (d - 1) |f(z)|`; this
holds for a split polynomial over any normed field.
Together with the lower bound for the derivative, a small value of an integer polynomial at `z`
forces a root nearby: `|z - α| ≤ 2 ^ C(d, 2) M(P) ^ (d - 2) |P(z)|`, and, since
`M(P) ≤ √(d + 1) H(P)` for the naive height `H(P)`, also
`|z - α| ≤ 2 ^ C(d, 2) (√(d + 1) H(P)) ^ (d - 2) |P(z)|`. This is the nearest-root estimate
behind Wirsing's lower bound for approximation by algebraic numbers in terms of Mahler's
exponent: it turns a polynomial taking a small value at `ξ` into an algebraic number close to `ξ`.

## Main results

* `Polynomial.norm_discr_le_two_pow_mul_mahlerMeasure_pow_mul_norm_eval_derivative_sq`: the
  bound on `|disc f|` for `f ∈ ℂ[X]` of degree at least `2`.
* `Polynomial.one_le_two_pow_mul_mahlerMeasure_pow_mul_norm_eval_derivative`: the lower bound for
  the derivative of an integer polynomial with nonzero discriminant at a complex root.
* `Polynomial.norm_sub_mul_norm_eval_derivative_le_two_pow_mul_norm_eval`: the distance to a
  nearest root times the derivative there is at most `2 ^ (d - 1) |f(z)|`, for a split polynomial
  over any normed field.
* `Polynomial.norm_sub_le_two_pow_mul_mahlerMeasure_pow_mul_norm_eval` and
  `Polynomial.norm_sub_le_two_pow_mul_sqrt_mul_supNorm_pow_mul_norm_eval`: the nearest-root
  estimate for an integer polynomial with nonzero discriminant, with the Mahler measure and with
  the naive height.

## References

* K. Mahler, *An inequality for the discriminant of a polynomial*, Michigan Math. J. **11**
  (1964), 257–262.
* E. Wirsing, *Approximation mit algebraischen Zahlen beschränkten Grades*, J. reine angew. Math.
  **206** (1961), 67–77.
* Y. Bugeaud, *Approximation by Algebraic Numbers*, Cambridge University Press (2004), Chapter 3
  and Appendix A.
-/

public section

namespace Polynomial

/-! ### Products of differences of complex numbers -/

/-- The product of `‖β - γ‖` over the ordered pairs `(β, γ)` of members of the multiset `t` at
distinct positions. For the roots of `f`, it is `|disc f|` divided by `|a| ^ (2 d - 2)`. -/
private noncomputable def pairProd (t : Multiset ℂ) : ℝ :=
  (t.map fun β ↦ ((t.erase β).map fun γ ↦ ‖β - γ‖).prod).prod

/-- Adjoining `α` to `t` multiplies the product over pairs by the square of the product of the
distances from `α` to the members of `t`: each such distance occurs once with `α` first and once
with `α` second. -/
private theorem pairProd_cons (α : ℂ) (t : Multiset ℂ) :
    pairProd (α ::ₘ t) = (t.map fun γ ↦ ‖α - γ‖).prod ^ 2 * pairProd t := by
  have h : ∀ β ∈ t, (((α ::ₘ t).erase β).map fun γ ↦ ‖β - γ‖).prod =
      ‖α - β‖ * ((t.erase β).map fun γ ↦ ‖β - γ‖).prod := fun β hβ ↦ by
    rw [Multiset.erase_cons_tail_of_mem hβ, Multiset.map_cons, Multiset.prod_cons, norm_sub_rev]
  unfold pairProd
  simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.erase_cons_head]
  rw [Multiset.map_congr rfl h, Multiset.prod_map_mul]
  ring

/-- The distances from `α` to the members of `t` multiply to at most
`(2 max(1, |α|)) ^ #t ∏_{γ ∈ t} max(1, |γ|)`. -/
private theorem prod_map_norm_sub_le (α : ℂ) (t : Multiset ℂ) :
    (t.map fun γ ↦ ‖α - γ‖).prod ≤
      (2 * max 1 ‖α‖) ^ Multiset.card t * (t.map fun γ ↦ max 1 ‖γ‖).prod := by
  have hle (γ : ℂ) : ‖α - γ‖ ≤ 2 * max 1 ‖α‖ * max 1 ‖γ‖ := by
    have hα := le_max_right 1 ‖α‖
    have hγ := le_max_right 1 ‖γ‖
    have hα₁ := le_max_left 1 ‖α‖
    have hγ₁ := le_max_left 1 ‖γ‖
    calc ‖α - γ‖ ≤ ‖α‖ + ‖γ‖ := norm_sub_le α γ
      _ ≤ 2 * max 1 ‖α‖ * max 1 ‖γ‖ := by nlinarith [norm_nonneg α, norm_nonneg γ]
  calc (t.map fun γ ↦ ‖α - γ‖).prod ≤ (t.map fun γ ↦ 2 * max 1 ‖α‖ * max 1 ‖γ‖).prod :=
        Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ norm_nonneg _) fun γ _ ↦ hle γ
    _ = _ := by rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]

/-- The product over pairs is at most `(2 ^ C(#t, 2) ∏_{γ ∈ t} max(1, |γ|) ^ (#t - 1)) ^ 2`: every
member of `t` takes part in `#t - 1` of the `C(#t, 2)` unordered pairs. -/
private theorem pairProd_le (t : Multiset ℂ) :
    pairProd t ≤ (2 ^ (Multiset.card t).choose 2 *
      (t.map fun γ ↦ max 1 ‖γ‖).prod ^ (Multiset.card t - 1)) ^ 2 := by
  induction t using Multiset.induction_on with
  | empty => simp [pairProd]
  | cons α t ih =>
    rcases Multiset.empty_or_exists_mem t with rfl | ⟨β, hβ⟩
    · simp [pairProd]
    obtain ⟨k, hk⟩ : ∃ k, Multiset.card t = k + 1 :=
      ⟨Multiset.card t - 1, (Nat.succ_pred_eq_of_pos (Multiset.card_pos_iff_exists_mem.2
        ⟨β, hβ⟩)).symm⟩
    set P := (t.map fun γ ↦ ‖α - γ‖).prod
    set M := (t.map fun γ ↦ max 1 ‖γ‖).prod
    have hP := prod_map_norm_sub_le α t
    have hP₀ : 0 ≤ P := Multiset.prod_map_nonneg fun _ _ ↦ norm_nonneg _
    have hM : 0 ≤ M := zero_le_one.trans (Multiset.one_le_prod_map fun _ _ ↦ le_max_left _ _)
    rw [hk, Nat.add_sub_cancel] at ih
    rw [hk] at hP
    have hch : (k + 1 + 1).choose 2 = (k + 1) + (k + 1).choose 2 := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right]
    rw [pairProd_cons, Multiset.card_cons, hk, Multiset.map_cons, Multiset.prod_cons,
      Nat.add_sub_cancel, hch]
    calc P ^ 2 * pairProd t ≤ P ^ 2 * (2 ^ (k + 1).choose 2 * M ^ k) ^ 2 := by gcongr
      _ = (P * (2 ^ (k + 1).choose 2 * M ^ k)) ^ 2 := by ring
      _ ≤ ((2 * max 1 ‖α‖) ^ (k + 1) * M * (2 ^ (k + 1).choose 2 * M ^ k)) ^ 2 := by gcongr
      _ = (2 ^ ((k + 1) + (k + 1).choose 2) * (max 1 ‖α‖ * M) ^ (k + 1)) ^ 2 := by ring

/-! ### The derivative at a root -/

/-- The discriminant of `f ∈ ℂ[X]` of degree `d` is `|a| ^ (2 d - 2)` times the product of the
differences of its roots over ordered pairs: this is the root-product formula
`Multiset.prod_map_prod_map_sub_erase_eq_neg_one_pow_mul_discr` for `f.roots`, in norm. -/
private theorem norm_discr_eq_mul_pairProd {f : ℂ[X]} (hf₀ : f ≠ 0) :
    ‖f.discr‖ = ‖f.leadingCoeff‖ ^ (2 * f.natDegree - 2) * pairProd f.roots := by
  have hs : f.Splits := IsAlgClosed.splits f
  have hd : (f.roots.map fun w ↦ X - C w).prod.natDegree = f.natDegree := by
    rw [natDegree_multiset_prod_X_sub_C_eq_card, hs.natDegree_eq_card_roots]
  have h := congrArg norm (Multiset.prod_map_prod_map_sub_erase_eq_neg_one_pow_mul_discr f.roots)
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Multiset.norm_prod_map] at h
  conv_lhs => rw [hs.eq_prod_roots]
  rw [TauCeti.discr_C_mul _ (leadingCoeff_ne_zero.2 hf₀), hd, norm_mul, norm_pow, ← h, pairProd]

/-- **The discriminant against the derivative at one root.** Let `f ∈ ℂ[X]` have degree
`d ≥ 2` and let `α` be a root of `f`. Then
`|disc f| ≤ (2 ^ C(d - 1, 2) M(f) ^ (d - 2) |f'(α)|) ^ 2`, where `M(f)` is the Mahler measure. -/
theorem norm_discr_le_two_pow_mul_mahlerMeasure_pow_mul_norm_eval_derivative_sq {f : ℂ[X]}
    (hf : 2 ≤ f.natDegree) {α : ℂ} (hα : f.IsRoot α) :
    ‖f.discr‖ ≤ (2 ^ (f.natDegree - 1).choose 2 * f.mahlerMeasure ^ (f.natDegree - 2) *
      ‖f.derivative.eval α‖) ^ 2 := by
  have hf₀ : f ≠ 0 := by
    rintro rfl
    simp at hf
  have hs : f.Splits := IsAlgClosed.splits f
  have hαs : α ∈ f.roots := (mem_roots hf₀).2 hα
  set t := f.roots.erase α with ht
  have hst : f.roots = α ::ₘ t := (Multiset.cons_erase hαs).symm
  obtain ⟨k, hk⟩ : ∃ k, Multiset.card t = k + 1 :=
    ⟨Multiset.card t - 1, by rw [hs.natDegree_eq_card_roots, hst, Multiset.card_cons] at hf; omega⟩
  have hd : f.natDegree = k + 2 := by rw [hs.natDegree_eq_card_roots, hst, Multiset.card_cons, hk]
  set P := (t.map fun γ ↦ ‖α - γ‖).prod
  set M := (t.map fun γ ↦ max 1 ‖γ‖).prod
  have hP₀ : 0 ≤ P := Multiset.prod_map_nonneg fun _ _ ↦ norm_nonneg _
  have hM₁ : 1 ≤ M := Multiset.one_le_prod_map fun _ _ ↦ le_max_left _ _
  -- `|disc f| = |a| ^ (2 d - 2) P ^ 2 (pairs of other roots)` and `|f'(α)| = |a| P`.
  have hdisc : ‖f.discr‖ = ‖f.leadingCoeff‖ ^ (2 * (k + 1)) * P ^ 2 * pairProd t := by
    rw [norm_discr_eq_mul_pairProd hf₀, hst, pairProd_cons, hd,
      show 2 * (k + 2) - 2 = 2 * (k + 1) by omega, mul_assoc]
  have hderiv : ‖f.derivative.eval α‖ = ‖f.leadingCoeff‖ * P := by
    rw [hs.eval_root_derivative_eq_leadingCoeff_mul hαs, norm_mul, Multiset.norm_prod_map, ← ht]
  have hpair := pairProd_le t
  rw [hk, Nat.add_sub_cancel] at hpair
  have hmahler : f.mahlerMeasure = ‖f.leadingCoeff‖ * (max 1 ‖α‖ * M) := by
    rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots, hst, Multiset.map_cons, Multiset.prod_cons]
  rw [hdisc, hderiv, hmahler, hd, show k + 2 - 1 = k + 1 by omega, Nat.add_sub_cancel]
  calc ‖f.leadingCoeff‖ ^ (2 * (k + 1)) * P ^ 2 * pairProd t
      ≤ ‖f.leadingCoeff‖ ^ (2 * (k + 1)) * P ^ 2 * (2 ^ (k + 1).choose 2 * M ^ k) ^ 2 := by
        gcongr
    _ = (2 ^ (k + 1).choose 2 * (‖f.leadingCoeff‖ * M) ^ k * (‖f.leadingCoeff‖ * P)) ^ 2 := by
        ring
    _ ≤ (2 ^ (k + 1).choose 2 * (‖f.leadingCoeff‖ * (max 1 ‖α‖ * M)) ^ k *
          (‖f.leadingCoeff‖ * P)) ^ 2 := by
        gcongr
        exact le_mul_of_one_le_left (zero_le_one.trans hM₁) (le_max_left _ _)

/-- **The derivative of an integer polynomial at a root.** Let `P ∈ ℤ[X]` have degree `d` and
nonzero discriminant. At every complex root `α` of `P`,
`1 ≤ 2 ^ C(d - 1, 2) M(P) ^ (d - 2) |P'(α)|`, where `M(P)` is the Mahler measure. -/
theorem one_le_two_pow_mul_mahlerMeasure_pow_mul_norm_eval_derivative {P : ℤ[X]}
    (hdisc : P.discr ≠ 0) {α : ℂ} (hα : α ∈ (P.map (Int.castRingHom ℂ)).roots) :
    1 ≤ 2 ^ (P.natDegree - 1).choose 2 *
      (P.map (Int.castRingHom ℂ)).mahlerMeasure ^ (P.natDegree - 2) *
        ‖(P.map (Int.castRingHom ℂ)).derivative.eval α‖ := by
  set f := P.map (Int.castRingHom ℂ) with hf
  have hf₀ : f ≠ 0 := ne_zero_of_mem_roots hα
  have hdeg : f.natDegree = P.natDegree :=
    natDegree_map_eq_of_injective (RingHom.injective_int _) P
  have hpos : 0 < P.natDegree :=
    hdeg ▸ natDegree_pos_iff_degree_pos.2 (degree_pos_of_root hf₀ (isRoot_of_mem_roots hα))
  rcases lt_or_ge P.natDegree 2 with h₂ | h₂
  · -- In degree one the derivative is the leading coefficient, a nonzero integer.
    have h₁ : P.natDegree = 1 := by omega
    have hderiv : f.derivative = C (P.leadingCoeff : ℂ) := by
      rw [eq_X_add_C_of_natDegree_le_one (hdeg.trans h₁).le]
      simp [hf, leadingCoeff, h₁]
    have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 (by rintro rfl; simp at hpos)
    rw [h₁, hderiv, eval_C, Complex.norm_intCast]
    simp only [Nat.reduceSub, Nat.choose_zero_succ, pow_zero, one_mul]
    exact_mod_cast Int.one_le_abs hlc
  · have hfdisc : f.discr = (P.discr : ℂ) := by
      rw [hf, discr_map_of_natDegree_eq _ (hf ▸ hdeg), eq_intCast]
    have h₁ : 1 ≤ ‖f.discr‖ := by
      rw [hfdisc, Complex.norm_intCast]
      exact_mod_cast Int.one_le_abs hdisc
    have h := norm_discr_le_two_pow_mul_mahlerMeasure_pow_mul_norm_eval_derivative_sq
      (hdeg ▸ h₂) (isRoot_of_mem_roots hα)
    rw [hdeg] at h
    have hM := f.mahlerMeasure_nonneg
    exact (one_le_sq_iff₀ (by positivity)).1 (h₁.trans h)

/-! ### The nearest root -/

/-- **The nearest root.** Let `f` be a polynomial of degree `d` that splits over a normed field
`K`, and let `α` be a root of `f` that is nearest to `z` among the roots of `f`. Then
`|z - α| |f'(α)| ≤ 2 ^ (d - 1) |f(z)|`. -/
theorem norm_sub_mul_norm_eval_derivative_le_two_pow_mul_norm_eval {K : Type*} [NormedField K]
    {f : K[X]} (hs : f.Splits) {z α : K} (hα : α ∈ f.roots)
    (hmin : ∀ β ∈ f.roots, ‖z - α‖ ≤ ‖z - β‖) :
    ‖z - α‖ * ‖f.derivative.eval α‖ ≤ 2 ^ (f.natDegree - 1) * ‖f.eval z‖ := by
  classical
  set t := f.roots.erase α with ht
  have hst : f.roots = α ::ₘ t := (Multiset.cons_erase hα).symm
  have hd : f.natDegree - 1 = Multiset.card t := by
    rw [hs.natDegree_eq_card_roots, hst, Multiset.card_cons, Nat.add_sub_cancel]
  -- Every other root `β` has `|α - β| ≤ |α - z| + |z - β| ≤ 2 |z - β|`.
  have hle : (t.map fun β ↦ ‖α - β‖).prod ≤
      2 ^ Multiset.card t * (t.map fun β ↦ ‖z - β‖).prod := by
    calc (t.map fun β ↦ ‖α - β‖).prod ≤ (t.map fun β ↦ 2 * ‖z - β‖).prod := by
          refine Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ norm_nonneg _) fun β hβ ↦ ?_
          have h := hmin β (hst ▸ Multiset.mem_cons_of_mem hβ)
          calc ‖α - β‖ ≤ ‖α - z‖ + ‖z - β‖ := norm_sub_le_norm_sub_add_norm_sub α z β
            _ ≤ 2 * ‖z - β‖ := by rw [norm_sub_rev]; linarith
      _ = 2 ^ Multiset.card t * (t.map fun β ↦ ‖z - β‖).prod := by
          rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]
  rw [hs.eval_root_derivative_eq_leadingCoeff_mul hα, ← ht, hs.eval_eq_prod_roots, hst,
    Multiset.map_cons, Multiset.prod_cons, hd]
  simp only [norm_mul, Multiset.norm_prod_map]
  calc ‖z - α‖ * (‖f.leadingCoeff‖ * (t.map fun β ↦ ‖α - β‖).prod)
      ≤ ‖z - α‖ * (‖f.leadingCoeff‖ * (2 ^ Multiset.card t * (t.map fun β ↦ ‖z - β‖).prod)) := by
        gcongr
    _ = _ := by ring

/-- **The nearest-root estimate.** Let `P ∈ ℤ[X]` have degree `d` and nonzero discriminant, and let
`α` be a complex root of `P` nearest to `z ∈ ℂ`. Then
`|z - α| ≤ 2 ^ C(d, 2) M(P) ^ (d - 2) |P(z)|`, where `M(P)` is the Mahler measure. -/
theorem norm_sub_le_two_pow_mul_mahlerMeasure_pow_mul_norm_eval {P : ℤ[X]} (hdisc : P.discr ≠ 0)
    {z α : ℂ} (hα : α ∈ (P.map (Int.castRingHom ℂ)).roots)
    (hmin : ∀ β ∈ (P.map (Int.castRingHom ℂ)).roots, ‖z - α‖ ≤ ‖z - β‖) :
    ‖z - α‖ ≤ 2 ^ P.natDegree.choose 2 *
      (P.map (Int.castRingHom ℂ)).mahlerMeasure ^ (P.natDegree - 2) *
        ‖(P.map (Int.castRingHom ℂ)).eval z‖ := by
  set f := P.map (Int.castRingHom ℂ)
  have hdeg : f.natDegree = P.natDegree :=
    natDegree_map_eq_of_injective (RingHom.injective_int _) P
  have hpos : 0 < P.natDegree := hdeg ▸ natDegree_pos_iff_degree_pos.2
    (degree_pos_of_root (ne_zero_of_mem_roots hα) (isRoot_of_mem_roots hα))
  have hder := one_le_two_pow_mul_mahlerMeasure_pow_mul_norm_eval_derivative hdisc hα
  have hM := f.mahlerMeasure_nonneg
  have hnear := norm_sub_mul_norm_eval_derivative_le_two_pow_mul_norm_eval
    (IsAlgClosed.splits f) hα hmin
  rw [hdeg] at hnear
  obtain ⟨n, hn⟩ : ∃ n, P.natDegree = n + 1 := ⟨P.natDegree - 1, by omega⟩
  rw [hn, Nat.add_sub_cancel] at hder hnear
  rw [hn, Nat.choose_succ_succ', Nat.choose_one_right, pow_add]
  calc ‖z - α‖ ≤ ‖z - α‖ * (2 ^ n.choose 2 * f.mahlerMeasure ^ (n + 1 - 2) *
        ‖f.derivative.eval α‖) := le_mul_of_one_le_right (norm_nonneg _) hder
    _ = 2 ^ n.choose 2 * f.mahlerMeasure ^ (n + 1 - 2) *
        (‖z - α‖ * ‖f.derivative.eval α‖) := by ring
    _ ≤ 2 ^ n.choose 2 * f.mahlerMeasure ^ (n + 1 - 2) * (2 ^ n * ‖f.eval z‖) := by gcongr
    _ = 2 ^ n * 2 ^ n.choose 2 * f.mahlerMeasure ^ (n + 1 - 2) * ‖f.eval z‖ := by ring

/-- **The nearest-root estimate with the naive height.** Let `P ∈ ℤ[X]` have degree `d`, nonzero
discriminant and naive height `H(P)`, the largest absolute value of a coefficient, and let `α` be
a complex root of `P` nearest to `z ∈ ℂ`. Then
`|z - α| ≤ 2 ^ C(d, 2) (√(d + 1) H(P)) ^ (d - 2) |P(z)|`. -/
theorem norm_sub_le_two_pow_mul_sqrt_mul_supNorm_pow_mul_norm_eval {P : ℤ[X]}
    (hdisc : P.discr ≠ 0) {z α : ℂ} (hα : α ∈ (P.map (Int.castRingHom ℂ)).roots)
    (hmin : ∀ β ∈ (P.map (Int.castRingHom ℂ)).roots, ‖z - α‖ ≤ ‖z - β‖) :
    ‖z - α‖ ≤ 2 ^ P.natDegree.choose 2 * (√(P.natDegree + 1) * P.supNorm) ^ (P.natDegree - 2) *
      ‖(P.map (Int.castRingHom ℂ)).eval z‖ := by
  refine (norm_sub_le_two_pow_mul_mahlerMeasure_pow_mul_norm_eval hdisc hα hmin).trans ?_
  have h := (P.map (Int.castRingHom ℂ)).mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm
  rw [natDegree_map_eq_of_injective (RingHom.injective_int _), supNorm_map] at h
  gcongr
  exact mahlerMeasure_nonneg _

end Polynomial
