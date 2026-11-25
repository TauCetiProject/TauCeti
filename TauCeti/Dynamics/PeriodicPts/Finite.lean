/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finiteness and periodic points

## Periods of distinct periodic points tend to infinity

Let `f : α → α` be a map each of whose positive iterates `f^[n]` has only finitely many fixed
points. Then `f` has only finitely many points of each positive period, so if `x i` are distinct
points of positive periods `d i`, the periods `d i` tend to infinity along the cofinite filter
(`Function.tendsto_cofinite_atTop_of_finite_ptsOfPeriod`). For instance, the closed orbits of the
suspension flow of a diffeomorphism with this property are finite in number below every period.

## Factorial iterates of a self-map of a finite type

Let `f : α → α` be a self-map of a finite type and let `m ≥ Nat.card α`. Every orbit of `f`
reaches the periodic points of `f` within `m` steps, so the image of `f^[m]` is exactly the set of
periodic points (`Function.range_iterate_of_card_le`), which is also the eventual image
`⋂ k, range f^[k]` (`Function.iInter_range_iterate`). Every periodic point has minimal period at
most `Nat.card α`, so it is fixed by `f^[m !]` (`Function.isPeriodicPt_factorial_of_card_le`).

Consequently the factorial iterates `f^[n !]` are constant from `n = Nat.card α` on
(`Function.iterate_factorial_eq_of_card_le`): `f^[m !]` is the retraction of `α` onto the periodic
points of `f`, on which `f` is a bijection with inverse `f^[m ! - 1]`
(`Function.invOn_iterate_factorial_pred`). No division by `m !` and no algebraic structure is
used. Applied to a linear endomorphism of a finite module, this gives Hida's ordinary projector
`lim U^{n!}`.

## References

* H. Hida, *Iwasawa modules attached to congruences of cusp forms*, Ann. Sci. École Norm. Sup.
  (4) 19 (1986), §1.
* C. Khare, J. Thorne, *Potential automorphy and the Leopoldt conjecture*, Amer. J. Math. 139
  (2017), §2.4, Lemma 2.10.
-/

public section

open Filter

namespace Function

/-- **Periods of distinct periodic points tend to infinity.** If each positive iterate of `f` has
only finitely many fixed points, and `x i` are distinct points of positive periods `d i`, then
`d i → ∞` along the cofinite filter: the fibre of `d` over `n > 0` lies in the preimage under `x`
of the finite set of fixed points of `f^[n]`. -/
theorem tendsto_cofinite_atTop_of_finite_ptsOfPeriod {α ι : Type*} {f : α → α}
    (hfin : ∀ n, 0 < n → (ptsOfPeriod f n).Finite) {x : ι → α} (hx : Injective x) {d : ι → ℕ}
    (hxd : ∀ i, IsPeriodicPt f (d i) (x i)) (hd : ∀ i, 0 < d i) :
    Tendsto d cofinite atTop := by
  rw [← Nat.cofinite_eq_atTop]
  refine Tendsto.cofinite_of_finite_preimage_singleton fun n ↦ Set.Finite.to_subtype ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Set.finite_empty.subset fun i hi ↦
      (hd i).ne' (Set.mem_singleton_iff.mp (Set.mem_preimage.mp hi))
  · refine ((hfin n hn).preimage hx.injOn).subset fun i hi ↦ ?_
    rw [Set.mem_preimage, mem_ptsOfPeriod, ← Set.mem_singleton_iff.mp (Set.mem_preimage.mp hi)]
    exact hxd i

section Finite

open Nat

variable {α : Type*} [Finite α] {f : α → α} {m n : ℕ}

/-- If `Nat.card α ≤ m`, then the `m`th iterate of any point under `f` is a periodic point of `f`:
every orbit of a self-map of a finite type enters a cycle within `Nat.card α` steps. -/
theorem iterate_mem_periodicPts_of_card_le (hm : Nat.card α ≤ m) (x : α) :
    f^[m] x ∈ periodicPts f := by
  -- Two of the `m + 1` points `x, f x, …, f^[m] x` coincide.
  have key : ∀ i j : ℕ, i < j → j ≤ m → f^[i] x = f^[j] x → f^[m] x ∈ periodicPts f := by
    intro i j hij hjm h
    have hper : IsPeriodicPt f (j - i) (f^[i] x) := by
      rw [IsPeriodicPt, IsFixedPt, ← iterate_add_apply, Nat.sub_add_cancel hij.le, h]
    have := hper.apply_iterate (m - i)
    rw [← iterate_add_apply, Nat.sub_add_cancel (by omega)] at this
    exact mk_mem_periodicPts (by omega) this
  have hni : ¬ Injective fun k : Fin (m + 1) ↦ f^[k] x := fun hinj ↦ by
    have := Nat.card_le_card_of_injective _ hinj
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    omega
  simp only [Injective, not_forall] at hni
  obtain ⟨i, j, h, hne⟩ := hni
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
  · exact key i j hlt (by omega) h
  · exact key j i hlt (by omega) h.symm

/-- If `Nat.card α ≤ m`, the image of `f^[m]` is the set of periodic points of `f`. -/
theorem range_iterate_of_card_le (hm : Nat.card α ≤ m) : Set.range f^[m] = periodicPts f := by
  refine Set.Subset.antisymm ?_ fun x hx ↦ ?_
  · rintro _ ⟨x, rfl⟩
    exact iterate_mem_periodicPts_of_card_le hm x
  · obtain ⟨p, hp, hpx⟩ := mem_periodicPts.mp hx
    exact periodicPts_subset_range (mk_mem_periodicPts hp (hpx.iterate m))

/-- For a self-map of a finite type, the eventual image `⋂ k, range f^[k]` is the set of periodic
points. -/
theorem iInter_range_iterate (f : α → α) : ⋂ k, Set.range f^[k] = periodicPts f := by
  refine Set.Subset.antisymm (fun x hx ↦ ?_) fun x hx ↦ Set.mem_iInter.mpr fun k ↦ ?_
  · rw [← range_iterate_of_card_le (f := f) le_rfl]
    exact Set.mem_iInter.mp hx _
  · obtain ⟨p, hp, hpx⟩ := mem_periodicPts.mp hx
    exact periodicPts_subset_range (mk_mem_periodicPts hp (hpx.iterate k))

/-- If `Nat.card α ≤ m`, every periodic point of `f` is fixed by `f^[m !]`. -/
theorem isPeriodicPt_factorial_of_card_le (hm : Nat.card α ≤ m) {x : α}
    (hx : x ∈ periodicPts f) : IsPeriodicPt f (m !) x := by
  have := Fintype.ofFinite α
  rw [Nat.card_eq_fintype_card] at hm
  exact (isPeriodicPt_factorial_card_of_mem_periodicPts hx).trans_dvd
    (Nat.factorial_dvd_factorial hm)

/-- The factorial iterates of a self-map of a finite type are constant from `Nat.card α` on:
`f^[n !] = f^[m !]` whenever `Nat.card α ≤ m ≤ n`. -/
theorem iterate_factorial_eq_of_card_le (hm : Nat.card α ≤ m) (hmn : m ≤ n) :
    f^[n !] = f^[m !] := by
  funext x
  have hx := iterate_mem_periodicPts_of_card_le (f := f) (hm.trans (Nat.self_le_factorial m)) x
  have hsub : IsPeriodicPt f ((n !) - m !) (f^[m !] x) :=
    (isPeriodicPt_factorial_of_card_le (hm.trans hmn) hx).sub
      (isPeriodicPt_factorial_of_card_le hm hx)
  rw [← Nat.sub_add_cancel (Nat.factorial_le hmn), iterate_add_apply, hsub.eq]

/-- If `Nat.card α ≤ m`, then on the periodic points of `f` the inverse of `f` is
`f^[m ! - 1]`. -/
theorem invOn_iterate_factorial_pred (hm : Nat.card α ≤ m) :
    Set.InvOn f^[(m !) - 1] f (periodicPts f) (periodicPts f) := by
  have h := Nat.sub_add_cancel (Nat.factorial_pos m)
  constructor <;> intro x hx
  · rw [← iterate_succ_apply f, Nat.succ_eq_add_one, h]
    exact isPeriodicPt_factorial_of_card_le hm hx
  · rw [← iterate_succ_apply' f, Nat.succ_eq_add_one, h]
    exact isPeriodicPt_factorial_of_card_le hm hx

end Finite

end Function
