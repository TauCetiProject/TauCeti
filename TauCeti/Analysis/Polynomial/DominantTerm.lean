/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Ultra
public import TauCeti.Algebra.Polynomial.Eval.Nonarchimedean

/-!
# Dominant terms of polynomials over normed rings

Let `g = ∑ gᵢ Xⁱ` be a polynomial over a seminormed ring and `r ≥ 0` a radius; call
`‖gᵢ‖ rⁱ` the weighted coefficient norms of `g` at `r`. Over an ultrametric normed division
ring, at a point `x` with `‖x‖ ≤ 1` where one weighted coefficient norm `‖g_k‖ ‖x‖ ^ k` is
strictly larger than all the others, the value is bounded below: `‖g_d‖ ‖x‖ ^ D ≤ ‖g(x)‖` for
`d ≤ D` (`Polynomial.norm_coeff_mul_pow_le_norm_eval`). This is the norm form of
`IsNonarchimedean.apply_eval_eq_coeff_mul_pow`.

The radii `0 < r < 1` at which the maximum of the weighted coefficient norms is attained at
least twice are few, independently of the degree of `g`: if `0 < ‖g_d‖` and the coefficient
norms at least `‖g_d‖` lie in a finite set `S`, there are at most `d + #S` of them
(`Polynomial.card_le_of_forall_not_exists_norm_coeff_mul_pow_lt`). As the radius grows, an index
attaining the maximum does not decrease (`Polynomial.index_le_of_forall_norm_coeff_mul_pow_le`,
the polynomial form, without Gauss norms, of
`TauCeti.PowerSeries.index_le_of_norm_coeff_mul_pow_eq`), and the coefficient norm at such an
index is the largest one among the lower indices
(`Polynomial.norm_coeff_le_of_forall_norm_coeff_mul_pow_le`); so at successive radii with a tie
the least maximal index and the norm of its coefficient both strictly increase. In the language of
Newton polygons, with `‖x‖ = b ^ (-v(x))` for some `b > 1`, the radii with a tie are the
`b ^ σ` for the slopes `σ` of the Newton polygon of the points `(i, v(gᵢ))`.

## Main results

* `Polynomial.norm_coeff_mul_pow_le_norm_eval`: a strictly dominant term bounds the value below.
* `Polynomial.norm_coeff_le_of_forall_norm_coeff_mul_pow_le`: a maximal weighted coefficient
  norm has the largest coefficient norm among the lower indices.
* `Polynomial.index_le_of_forall_norm_coeff_mul_pow_le`: maximal indices do not decrease with the
  radius.
* `Polynomial.card_le_of_forall_not_exists_norm_coeff_mul_pow_lt`: the number of radii in
  `(0, 1)` without a strictly dominant term is at most `d + #S`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter IV §§3–4 (Newton polygons).
-/

public section

open Polynomial

namespace Polynomial

variable {R : Type*} [SeminormedRing R] {g : R[X]} {r r' : ℝ} {d i j k l : ℕ}

/-- **A strictly dominant term bounds the value of a polynomial below.** Over an ultrametric
normed division ring, if `‖g.coeff i‖ * ‖x‖ ^ i < ‖g.coeff k‖ * ‖x‖ ^ k` for every `i ≠ k` and
`‖x‖ ≤ 1`, then `‖g.coeff d‖ * ‖x‖ ^ D ≤ ‖g.eval x‖` for every `d ≤ D`. In valuation terms,
`v(g(x)) ≤ v(g_d) + D v(x)`. -/
theorem norm_coeff_mul_pow_le_norm_eval {K : Type*} [NormedDivisionRing K] [IsUltrametricDist K]
    {g : K[X]} {x : K} {d D k : ℕ} (hd : d ≤ D) (hx : ‖x‖ ≤ 1)
    (hk : ∀ i ≠ k, ‖g.coeff i‖ * ‖x‖ ^ i < ‖g.coeff k‖ * ‖x‖ ^ k) :
    ‖g.coeff d‖ * ‖x‖ ^ D ≤ ‖g.eval x‖ := by
  rw [(IsUltrametricDist.isNonarchimedean_norm (R := K)).apply_eval_eq_coeff_mul_pow norm_neg
    (p := g) (t := x) (k := k) fun i _ hi ↦ by simpa only [norm_mul, norm_pow] using hk i hi,
    norm_mul, norm_pow]
  refine (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (norm_nonneg x) hx hd)
    (norm_nonneg _)).trans ?_
  rcases eq_or_ne d k with rfl | h
  · exact le_rfl
  · exact (hk d h).le

/-- At a radius `0 < r ≤ 1`, an index `i` attaining the maximum of the weighted coefficient
norms `‖g.coeff l‖ * r ^ l` has the largest coefficient norm among the indices `l ≤ i`. -/
theorem norm_coeff_le_of_forall_norm_coeff_mul_pow_le (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hmax : ∀ l, ‖g.coeff l‖ * r ^ l ≤ ‖g.coeff i‖ * r ^ i) (hl : l ≤ i) :
    ‖g.coeff l‖ ≤ ‖g.coeff i‖ :=
  le_of_mul_le_mul_right ((hmax l).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hr0.le hr1 hl) (norm_nonneg _))) (pow_pos hr0 l)

/-- Two equal weighted coefficient norms at a radius `0 < r < 1`: the larger index has the
strictly larger coefficient norm. -/
private lemma norm_coeff_lt_of_eq (hr0 : 0 < r) (hr1 : r < 1) (hij : i < j)
    (hj : 0 < ‖g.coeff j‖) (heq : ‖g.coeff i‖ * r ^ i = ‖g.coeff j‖ * r ^ j) :
    ‖g.coeff i‖ < ‖g.coeff j‖ := by
  refine lt_of_mul_lt_mul_right ?_ (pow_pos hr0 i).le
  rw [heq]
  exact mul_lt_mul_of_pos_left (pow_lt_pow_right_of_lt_one₀ hr0 hr1 hij) hj

/-- **The index of a maximal weighted coefficient norm does not decrease with the radius.** An
index `k` with `0 < ‖g.coeff k‖` attaining the maximum of the weighted coefficient norms
`‖g.coeff i‖ * r ^ i` at a radius `0 < r` is at most an index `l` attaining it at a radius
`r' > r`. This is the polynomial form, without Gauss norms, of
`TauCeti.PowerSeries.index_le_of_norm_coeff_mul_pow_eq`. -/
theorem index_le_of_forall_norm_coeff_mul_pow_le (hr0 : 0 < r) (hrr : r < r')
    (hk : 0 < ‖g.coeff k‖) (hmk : ∀ i, ‖g.coeff i‖ * r ^ i ≤ ‖g.coeff k‖ * r ^ k)
    (hml : ∀ i, ‖g.coeff i‖ * r' ^ i ≤ ‖g.coeff l‖ * r' ^ l) : k ≤ l := by
  by_contra! hlk
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hlk.le
  have ht : t ≠ 0 := by omega
  have hr' : 0 < r' := hr0.trans hrr
  have h1 : ‖g.coeff l‖ * r ^ l ≤ (‖g.coeff (l + t)‖ * r ^ t) * r ^ l :=
    (hmk l).trans_eq (by rw [pow_add]; ring)
  have h2 : (‖g.coeff (l + t)‖ * r' ^ t) * r' ^ l ≤ ‖g.coeff l‖ * r' ^ l :=
    (hml (l + t)).trans_eq' (by rw [pow_add]; ring)
  have h3 := (le_of_mul_le_mul_right h2 (pow_pos hr' l)).trans
    (le_of_mul_le_mul_right h1 (pow_pos hr0 l))
  exact (pow_lt_pow_left₀ hrr hr0.le ht).not_ge
    (le_of_mul_le_mul_left h3 hk)

/-- If no weighted coefficient norm is strictly dominant at `r`, the maximum is attained at two
indices `i < j`. -/
private lemma exists_lt_of_not_exists
    (h : ¬∃ k, ∀ i ≠ k, ‖g.coeff i‖ * r ^ i < ‖g.coeff k‖ * r ^ k) :
    ∃ i j, i < j ∧ (∀ l, ‖g.coeff l‖ * r ^ l ≤ ‖g.coeff i‖ * r ^ i) ∧
      ‖g.coeff i‖ * r ^ i = ‖g.coeff j‖ * r ^ j := by
  -- the index `g.natDegree + 1` carries the weight `0` of every index outside the support
  obtain ⟨k, -, hk⟩ := (insert (g.natDegree + 1) g.support).exists_max_image
    (fun i ↦ ‖g.coeff i‖ * r ^ i) (Finset.insert_nonempty _ _)
  have hmax : ∀ l, ‖g.coeff l‖ * r ^ l ≤ ‖g.coeff k‖ * r ^ k := fun l ↦ by
    by_cases hl : g.coeff l = 0
    · rw [hl, norm_zero, zero_mul]
      simpa only [coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self _), norm_zero, zero_mul] using
        hk _ (Finset.mem_insert_self _ _)
    · exact hk l (Finset.mem_insert_of_mem (mem_support_iff.2 hl))
  push Not at h
  obtain ⟨i, hik, hle⟩ := h k
  have heq := le_antisymm (hmax i) hle
  rcases hik.lt_or_gt with hlt | hlt
  · exact ⟨i, k, hlt, fun l ↦ (hmax l).trans_eq heq.symm, heq⟩
  · exact ⟨k, i, hlt, hmax, heq.symm⟩

/-- An index attaining the maximum of the weighted coefficient norms at `r > 0` has a
coefficient of positive norm when `g.coeff d` has. -/
private lemma norm_coeff_pos_of_isMax (hd : 0 < ‖g.coeff d‖) (hr0 : 0 < r)
    (hmax : ∀ l, ‖g.coeff l‖ * r ^ l ≤ ‖g.coeff i‖ * r ^ i) : 0 < ‖g.coeff i‖ :=
  pos_of_mul_pos_left ((mul_pos hd (pow_pos hr0 d)).trans_le (hmax d)) (pow_nonneg hr0.le i)

/-- **Few radii without a dominant term.** Let `g` be a polynomial over a seminormed ring with
`0 < ‖g.coeff d‖`, and suppose every coefficient norm at least `‖g.coeff d‖` lies in a finite set
`S`. Then at most `d + #S` radii `0 < r < 1` admit no index `k` with
`‖g.coeff i‖ * r ^ i < ‖g.coeff k‖ * r ^ k` for all `i ≠ k`. The bound does not involve the
degree of `g`. -/
theorem card_le_of_forall_not_exists_norm_coeff_mul_pow_lt (hd : 0 < ‖g.coeff d‖)
    {S : Finset ℝ} (hS : ∀ i, ‖g.coeff d‖ ≤ ‖g.coeff i‖ → ‖g.coeff i‖ ∈ S) {T : Finset ℝ}
    (hT : ∀ r ∈ T, 0 < r ∧ r < 1 ∧ ¬∃ k, ∀ i ≠ k, ‖g.coeff i‖ * r ^ i < ‖g.coeff k‖ * r ^ k) :
    T.card ≤ d + S.card := by
  have hex : ∀ r, ∃ i j : ℕ, r ∈ T → i < j ∧ (∀ l, ‖g.coeff l‖ * r ^ l ≤ ‖g.coeff i‖ * r ^ i) ∧
      ‖g.coeff i‖ * r ^ i = ‖g.coeff j‖ * r ^ j := fun r ↦ by
    by_cases hr : r ∈ T
    · obtain ⟨i, j, h⟩ := exists_lt_of_not_exists (hT r hr).2.2
      exact ⟨i, j, fun _ ↦ h⟩
    · exact ⟨0, 0, fun h ↦ (hr h).elim⟩
  choose i j hij using hex
  have key : ∀ r ∈ T, ∀ r' ∈ T, r < r' → i r < i r' ∧ ‖g.coeff (i r)‖ < ‖g.coeff (i r')‖ := by
    intro r hr r' hr' hrr
    obtain ⟨hr0, hr1, -⟩ := hT r hr
    obtain ⟨hlt, hmax, heq⟩ := hij r hr
    have hmax' : ∀ l, ‖g.coeff l‖ * r ^ l ≤ ‖g.coeff (j r)‖ * r ^ j r :=
      fun l ↦ (hmax l).trans_eq heq
    have hj := norm_coeff_pos_of_isMax hd hr0 hmax'
    have hji := index_le_of_forall_norm_coeff_mul_pow_le hr0 hrr hj hmax' (hij r' hr').2.1
    exact ⟨hlt.trans_le hji, (norm_coeff_lt_of_eq hr0 hr1 hlt hj heq).trans_le
      (norm_coeff_le_of_forall_norm_coeff_mul_pow_le (hT r' hr').1 (hT r' hr').2.1.le
        (hij r' hr').2.1 hji)⟩
  have hinj₁ : Set.InjOn i T := StrictMonoOn.injOn fun r hr r' hr' h ↦ (key r hr r' hr' h).1
  have hinj₂ : Set.InjOn (fun r ↦ ‖g.coeff (i r)‖) T :=
    StrictMonoOn.injOn fun r hr r' hr' h ↦ (key r hr r' hr' h).2
  rw [← Finset.card_filter_add_card_filter_not (s := T) (fun r ↦ i r < d)]
  refine add_le_add ?_ ?_
  · refine (Finset.card_le_card_of_injOn i (t := Finset.range d) (fun r hr ↦ ?_)
      (hinj₁.mono (Finset.coe_subset.2 (Finset.filter_subset _ _)))).trans_eq (Finset.card_range d)
    exact Finset.mem_range.2 (Finset.mem_filter.1 hr).2
  · refine Finset.card_le_card_of_injOn _ (fun r hr ↦ hS _ ?_)
      (hinj₂.mono (Finset.coe_subset.2 (Finset.filter_subset _ _)))
    obtain ⟨hrT, hrd⟩ := Finset.mem_filter.1 hr
    exact norm_coeff_le_of_forall_norm_coeff_mul_pow_le (hT r hrT).1 (hT r hrT).2.1.le
      (hij r hrT).2.1 (not_lt.1 hrd)

end Polynomial
