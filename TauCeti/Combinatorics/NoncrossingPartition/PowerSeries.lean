/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Substitution
public import TauCeti.Combinatorics.NoncrossingPartition.Catalan
import TauCeti.Algebra.BigOperators.Finset.Range
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Noncrossing partitions weighted by their part sizes

Give each part of size `k` of a noncrossing partition the weight `c_k`, the `k`-th coefficient of
a formal power series `C(z) = 1 + ∑_{k ≥ 1} c_k z^k`, and let
`m_n = ∑_{π ∈ NC(n)} ∏_{B ∈ π} c_{|B|}` be the total weight of the noncrossing partitions of `n`
ordered positions. Then any series `M` satisfying the functional equation `M(z) = C(z M(z))` has
`n`-th coefficient `m_n`, that is, `M(z) = ∑_{n ≥ 0} m_n z^n`. In free probability `c_k` is the
`k`-th free cumulant of a variable and `m_n` its `n`-th moment, so this is the moment–cumulant
relation between the moment series and the cumulant series `C(z) = 1 + z R(z)`.

The proof is coefficientwise, by the recurrence of noncrossing partitions by the part containing
the first position (`TauCeti.NoncrossingPartition.sum_mul_prod_eq_sum_mul_sum`). If that part ends
at the position `x`, a noncrossing partition is a noncrossing partition of the positions before `x`
whose first part is extended by `x`, together with one of the positions after `x`. Weighting the
first part by the coefficients of an arbitrary series `f`, the total weight of the noncrossing
partitions of `n ≥ 1` positions is the `n`-th coefficient of `f(z M(z))`: extending the first part
shifts `f` to `(f(z) - f(0)) / z`, and the positions after `x` contribute the factor `M(z)`. For
`n = 0` the identity holds with the convention that the empty partition, which has no first part,
has weight `f(0)`, the constant coefficient of `f(z M(z))`.

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
size. If `m ∉ t`, the part through `m` is empty and contributes `f(0)`; in particular the empty
partition of `t = ∅` has weight `f(0)` rather than `1`. -/
private noncomputable def firstPartSum (C f : R⟦X⟧) (m : α) (t : Finset α) : R :=
  ∑ P : NoncrossingPartition t,
    coeff #(P.1.part m) f * ∏ B ∈ P.1.parts with m ∉ B, coeff #B C

/-- The only noncrossing partition of the empty set has no parts. -/
private theorem parts_eq_empty (P : NoncrossingPartition (∅ : Finset α)) : P.1.parts = ∅ :=
  Finpartition.parts_eq_empty_iff.2 rfl

/-- Assume that the total weight of the noncrossing partitions of every set of fewer than `n`
positions is the coefficient of `M` at its size. Then for every set `t` of at most `n` positions,
whose least position is `m` if `t` is nonempty, the total weight with the first part weighted by
`f` is the coefficient of `f(z M(z))` at `|t|`. For `t = ∅` both sides are `f(0)`, since
`firstPartSum` gives the empty partition the weight `f(0)`. -/
private theorem firstPartSum_eq_coeff_subst {C M : R⟦X⟧} {n : ℕ}
    (hZ : ∀ u : Finset α, #u < n →
      ∑ P : NoncrossingPartition u, ∏ B ∈ P.1.parts, coeff #B C = coeff #u M)
    (t : Finset α) (m : α) (hm : ∀ y ∈ t, m ≤ y) (hmt : t.Nonempty → m ∈ t) (ht : #t ≤ n)
    (f : R⟦X⟧) : firstPartSum C f m t = coeff #t (f.subst (X * M)) := by
  induction hk : #t using Nat.strong_induction_on generalizing t f with
  | _ k ih =>
  obtain rfl | hne := t.eq_empty_or_nonempty
  · -- The constant coefficient of `f(z M(z))` is `f(0)`.
    have h0 : coeff 0 (f.subst (X * M)) = coeff 0 f := by
      rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply]
      exact constantCoeff_subst_of_constantCoeff_zero (S := R) (by simp [← constantCoeff_eq]) f
    rw [← hk, card_empty, h0, firstPartSum, Fintype.sum_unique,
      parts_eq_empty, filter_empty, prod_empty, mul_one,
      (default : NoncrossingPartition _).1.part_eq_empty.2 (notMem_empty m), card_empty]
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
    sum_mul_prod_eq_sum_mul_sum hne (fun B => coeff #B f) fun B => coeff #B C,
    coeff_succ_subst_X_mul, mul_comm M, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j => coeff i S * coeff j M, ← h]
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
  · -- The constant coefficient of `C(z M(z))` is `C(0) = 1`.
    have h0 : constantCoeff (C.subst (X * M)) = constantCoeff C :=
      constantCoeff_subst_of_constantCoeff_zero (S := R) (by simp [← constantCoeff_eq]) C
    rw [← hn, card_empty, ← hM, coeff_zero_eq_constantCoeff_apply, h0, hC,
      Fintype.sum_unique, parts_eq_empty, prod_empty]
  have h := firstPartSum_eq_coeff_subst (C := C) (M := M) (fun u hu => ih _ hu u rfl) s
    (s.min' hs) (fun y hy => s.min'_le y hy) (fun _ => s.min'_mem hs) hn.le C
  rw [hM, hn] at h
  rw [← h, firstPartSum]
  exact sum_congr rfl fun π _ =>
    π.1.prod_parts_eq_mul_prod_filter_notMem (s.min'_mem hs) fun B => coeff #B C

end TauCeti.NoncrossingPartition
