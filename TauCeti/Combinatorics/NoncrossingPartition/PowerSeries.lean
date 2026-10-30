/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.Combinatorics.NoncrossingPartition.Catalan
import TauCeti.Algebra.BigOperators.Finset.Range

/-!
# Noncrossing partitions weighted by their part sizes

Give each part of size `k` of a noncrossing partition the weight `c_k`, the `k`-th coefficient of
a formal power series `C(z) = 1 + ∑_{k ≥ 1} c_k z^k`, and let
`m_n = ∑_{π ∈ NC(n)} ∏_{B ∈ π} c_{|B|}` be the total weight of the noncrossing partitions of `n`
ordered positions. Then the series
`M(z) = ∑_{n ≥ 0} m_n z^n` satisfies the functional equation `M(z) = C(z M(z))`, which determines
it. In free probability `c_k` is the `k`-th free cumulant of a variable and `m_n` its `n`-th
moment, so this is the moment–cumulant relation between the moment series and the cumulant series
`C(z) = 1 + z R(z)`.

The proof is coefficientwise, by the recurrence of noncrossing partitions by the part containing
the first position (`TauCeti.NoncrossingPartition.sum_mul_prod_eq_sum_mul_sum`). If that part ends
at the position `x`, a noncrossing partition is a noncrossing partition of the positions before `x`
whose first part is extended by `x`, together with one of the positions after `x`. Weighting the
first part by the coefficients of an arbitrary series `f`, the total weight of the noncrossing
partitions of `n` positions is the `n`-th coefficient of `f(z M(z))`: extending the first part
shifts `f` to `(f(z) - f(0)) / z`, and the positions after `x` contribute the factor `M(z)`.

## Main results

* `TauCeti.NoncrossingPartition.sum_prod_coeff_eq_coeff_of_subst_eq` — if `C(0) = 1` and
  `M(z) = C(z M(z))`, then `∑_{π ∈ NC(s)} ∏_{B ∈ π} c_{|B|}` is the `|s|`-th coefficient of `M`,
  for every finite set `s` of positions in a linear order.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 16 (the
  functional relation between the moment series and the cumulant series of one variable).
-/

public section

open Finset PowerSeries

namespace TauCeti.NoncrossingPartition

variable {R α : Type*} [CommRing R] [LinearOrder α]

/-- The total weight of the noncrossing partitions of `t` when the part through `m` has weight
the coefficient of `f` at its size and every other part has weight the coefficient of `C` at its
size. -/
private noncomputable def firstPartSum (C f : R⟦X⟧) (m : α) (t : Finset α) : R :=
  ∑ P : NoncrossingPartition t,
    coeff #(P.1.part m) f * ∏ B ∈ P.1.parts with m ∉ B, coeff #B C

/-- The `(n + 1)`-st coefficient of `f(z M(z))` is the `n`-th coefficient of `M(z) g(z M(z))`,
where `g(z) = (f(z) - f(0)) / z`. -/
private theorem coeff_succ_subst (M f : R⟦X⟧) (n : ℕ) :
    coeff (n + 1) (f.subst (X * M)) =
      coeff n (M * (mk fun p => coeff (p + 1) f).subst (X * M)) := by
  have hP : HasSubst (X * M) := HasSubst.of_constantCoeff_zero' (by simp)
  conv_lhs => rw [f.eq_X_mul_shift_add_const]
  rw [subst_add hP, subst_mul hP, subst_X hP, subst_C, mul_assoc, map_add, coeff_succ_X_mul,
    add_eq_left]
  exact (coeff_C _ _).trans (ite_eq_right_iff.2 fun h => absurd h n.succ_ne_zero)

/-- The `0`-th coefficient of `f(z M(z))` is `f(0)`. -/
private theorem coeff_zero_subst (M f : R⟦X⟧) : coeff 0 (f.subst (X * M)) = coeff 0 f := by
  have hP : HasSubst (X * M) := HasSubst.of_constantCoeff_zero' (by simp)
  conv_lhs => rw [f.eq_X_mul_shift_add_const]
  rw [subst_add hP, subst_mul hP, subst_X hP, subst_C, mul_assoc, map_add, coeff_zero_X_mul,
    zero_add]
  exact (coeff_C _ _).trans (by simp)

/-- The only noncrossing partition of the empty set has no parts. -/
private theorem parts_eq_empty (P : NoncrossingPartition (∅ : Finset α)) : P.1.parts = ∅ :=
  Finpartition.parts_eq_empty_iff.2 rfl

/-- Assume that the total weight of the noncrossing partitions of every set of fewer than `n`
positions is the coefficient of `M` at its size. Then for every set `t` of at most `n` positions,
whose least position is `m` if `t` is nonempty, the total weight with the first part weighted by
`f` is the coefficient of `f(z M(z))` at `|t|`. -/
private theorem firstPartSum_eq_coeff_subst {C M : R⟦X⟧} {n : ℕ}
    (hZ : ∀ u : Finset α, #u < n →
      ∑ P : NoncrossingPartition u, ∏ B ∈ P.1.parts, coeff #B C = coeff #u M)
    (t : Finset α) (m : α) (hm : ∀ y ∈ t, m ≤ y) (hmt : t.Nonempty → m ∈ t) (ht : #t ≤ n)
    (f : R⟦X⟧) : firstPartSum C f m t = coeff #t (f.subst (X * M)) := by
  induction hk : #t using Nat.strong_induction_on generalizing t f with
  | _ k ih =>
  obtain rfl | hne := t.eq_empty_or_nonempty
  · rw [← hk, card_empty, coeff_zero_subst, firstPartSum, Fintype.sum_unique, parts_eq_empty,
      filter_empty, prod_empty, mul_one, (default : NoncrossingPartition _).1.part_eq_empty.2
        (notMem_empty m), card_empty]
  have hmin : t.min' hne = m := le_antisymm (min'_le t m (hmt hne)) (le_min' t hne m hm)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (hk ▸ hne.card_pos.ne')
  -- The positions before `x ∈ t`, or after it, are fewer than those of `t`.
  have hlt {x : α} (hx : x ∈ t) {p : α → Prop} [DecidablePred p] (hp : ¬p x) :
      #{y ∈ t | p y} < k + 1 :=
    hk ▸ card_lt_card (filter_ssubset.2 ⟨x, hx, hp⟩)
  set S := (mk fun p => coeff (p + 1) f).subst (X * M)
  have h := sum_card_filter_lt_card_filter_gt t fun i j => coeff i S * coeff j M
  rw [hk, Nat.add_sub_cancel] at h
  rw [firstPartSum, ← hmin,
    sum_mul_prod_eq_sum_mul_sum hne (fun B => coeff #B f) fun B => coeff #B C, coeff_succ_subst,
    mul_comm M, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j =>
      coeff i S * coeff j M, ← h]
  refine sum_congr rfl fun x hx => ?_
  -- The weight of the part of `m` extended by `x` is the shifted coefficient of `f`.
  have hshift (L : NoncrossingPartition {y ∈ t | y < x}) :
      coeff #(insert x (L.1.part m)) f = coeff #(L.1.part m) (mk fun p => coeff (p + 1) f) := by
    rw [card_insert_of_notMem fun h => lt_irrefl x (mem_filter.1 (L.1.part_subset m h)).2,
      coeff_mk]
  simp_rw [hmin, hshift]
  have hlt' := hlt (p := (· < x)) hx (lt_irrefl x)
  rw [hZ _ ((hlt (p := (x < ·)) hx (lt_irrefl x)).trans_le (hk ▸ ht))]
  congr 1
  refine ih _ hlt' _ (fun y hy => hm y (mem_filter.1 hy).1) (fun ⟨y, hy⟩ => ?_)
    (hlt'.le.trans (hk ▸ ht)) _ rfl
  exact mem_filter.2 ⟨hmt hne, (hm y (mem_filter.1 hy).1).trans_lt (mem_filter.1 hy).2⟩

/-- *The moment–cumulant functional equation, coefficientwise.* Let `C` be a formal power series
with constant coefficient `1` and let `M` satisfy `M(z) = C(z M(z))`. Then for every finite set `s`
of positions in a linear order, the sum over the noncrossing partitions `π` of `s` of the products
`∏_{B ∈ π} c_{|B|}` of the coefficients of `C` at the part sizes is the coefficient of `M` at
`|s|`. -/
theorem sum_prod_coeff_eq_coeff_of_subst_eq {C M : R⟦X⟧} (hC : constantCoeff C = 1)
    (hM : C.subst (X * M) = M) (s : Finset α) :
    ∑ π : NoncrossingPartition s, ∏ B ∈ π.1.parts, coeff #B C = coeff #s M := by
  induction hn : #s using Nat.strong_induction_on generalizing s with
  | _ n ih =>
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [← hn, card_empty, ← hM, coeff_zero_subst, coeff_zero_eq_constantCoeff_apply, hC,
      Fintype.sum_unique, parts_eq_empty, prod_empty]
  have h := firstPartSum_eq_coeff_subst (C := C) (M := M) (fun u hu => ih _ hu u rfl) s
    (s.min' hs) (fun y hy => s.min'_le y hy) (fun _ => s.min'_mem hs) hn.le C
  rw [hM, hn] at h
  rw [← h, firstPartSum]
  exact sum_congr rfl fun π _ =>
    π.1.prod_parts_eq_mul_prod_filter_notMem (s.min'_mem hs) fun B => coeff #B C

end TauCeti.NoncrossingPartition
