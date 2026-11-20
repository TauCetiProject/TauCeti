/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Idempotent
import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Factorial iterates of finite self-maps

For a self-map of a nonempty finite type with `m` elements, the image stabilizes after at most
`m - 1` steps and consists of the periodic points. The iterate at `m!` retracts onto this image
and is the unique idempotent among the positive iterates. This is the finite-set argument
underlying the ordinary projector of Khare and Thorne, *Potential automorphy and the Leopoldt
conjecture*,
[§2.4, Lemma 2.10](https://arxiv.org/pdf/1409.7007v2).

We use Mathlib's `Function.periodicPts` and its common-period lemma
`Function.mem_periodicPts_iff_isPeriodicPt_factorial_card`.
-/

public section

open Nat Set

namespace Function

variable {α : Type*} (f : α → α)

/-- Every periodic point belongs to the range of every iterate, even on an infinite type. -/
theorem periodicPts_subset_range_iterate (n : ℕ) : periodicPts f ⊆ range f^[n] := by
  intro x hx
  obtain ⟨y, _, hy⟩ := ((bijOn_periodicPts f).surjOn.iterate n) hx
  exact ⟨y, hy⟩

variable [Finite α]

/-- An orbit of a self-map of a finite type reaches a periodic point within `Nat.card α - 1`
iterations. -/
theorem iterate_mem_periodicPts_of_card_sub_one_le {n : ℕ} (hn : Nat.card α - 1 ≤ n) (x : α) :
    f^[n] x ∈ periodicPts f := by
  let := Fintype.ofFinite α
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (Nat.card α + 1) ↦ f^[i.val] x) (by simp [Nat.card_eq_fintype_card])
  have hcycle (i j : Fin (Nat.card α + 1)) (hlt : i < j) (h : f^[i.val] x = f^[j.val] x) :
      f^[n] x ∈ periodicPts f := by
    have hp : IsPeriodicPt f (j.val - i.val) (f^[i.val] x) := by
      rw [IsPeriodicPt, IsFixedPt, ← iterate_add_apply, Nat.sub_add_cancel hlt.le]
      exact h.symm
    have hij' : i.val < j.val := hlt
    have hi : i.val ≤ n :=
      (Nat.le_sub_one_of_lt (hij'.trans_le (Nat.le_of_lt_succ j.isLt))).trans hn
    have hpn := hp.apply_iterate (n - i.val)
    rw [← iterate_add_apply, Nat.sub_add_cancel hi] at hpn
    exact mk_mem_periodicPts (Nat.sub_pos_of_lt hlt) hpn
  rcases lt_or_gt_of_ne hij with h | h
  · exact hcycle i j h heq
  · exact hcycle j i h heq.symm

/-- Once the number of iterations reaches `Nat.card α - 1`, the range is exactly the
periodic points. -/
theorem range_iterate_eq_periodicPts_of_card_sub_one_le {n : ℕ} (hn : Nat.card α - 1 ≤ n) :
    range f^[n] = periodicPts f := by
  refine Subset.antisymm ?_ (f.periodicPts_subset_range_iterate n)
  rintro _ ⟨x, rfl⟩
  exact f.iterate_mem_periodicPts_of_card_sub_one_le hn x

/-- The intersection of the images of all iterates is the set of periodic points. -/
theorem iInter_range_iterate_eq_periodicPts : (⋂ n : ℕ, range f^[n]) = periodicPts f := by
  refine Subset.antisymm ?_ (subset_iInter (f.periodicPts_subset_range_iterate))
  exact (iInter_subset _ (Nat.card α - 1)).trans
    (f.range_iterate_eq_periodicPts_of_card_sub_one_le le_rfl).le

/-- Once the number of iterations reaches `Nat.card α - 1`, adding a multiple of the
factorial of the cardinality does not change the iterate. -/
theorem iterate_add_eq_of_card_sub_one_le_of_factorial_dvd {n k : ℕ} (hn : Nat.card α - 1 ≤ n)
    (hk : (Nat.card α)! ∣ k) : f^[k + n] = f^[n] := by
  funext x
  rw [iterate_add_apply]
  let := Fintype.ofFinite α
  have hp : IsPeriodicPt f (Nat.card α)! (f^[n] x) := by
    rw [Nat.card_eq_fintype_card]
    exact isPeriodicPt_factorial_card_of_mem_periodicPts
      (f.iterate_mem_periodicPts_of_card_sub_one_le hn x)
  exact (hp.trans_dvd hk).eq

/-- The factorial iterates stabilize once the factorial index reaches the cardinality. -/
theorem iterate_factorial_eq_iterate_factorial_card {n : ℕ} (hn : Nat.card α ≤ n) :
    f^[n !] = f^[(Nat.card α)!] := by
  have hle := Nat.factorial_le hn
  have hd := Nat.dvd_sub (Nat.factorial_dvd_factorial hn) (dvd_refl (Nat.card α)!)
  have hcard := (Nat.sub_le (Nat.card α) 1).trans (Nat.self_le_factorial (Nat.card α))
  simpa only [Nat.sub_add_cancel hle] using
    f.iterate_add_eq_of_card_sub_one_le_of_factorial_dvd hcard hd

/-- The stabilized factorial iterate is idempotent under composition. -/
@[simp]
theorem iterate_factorial_card_comp_self :
    f^[(Nat.card α)!] ∘ f^[(Nat.card α)!] = f^[(Nat.card α)!] := by
  rw [← iterate_add]
  exact f.iterate_add_eq_of_card_sub_one_le_of_factorial_dvd
    ((Nat.sub_le _ _).trans (Nat.self_le_factorial _)) (dvd_refl _)

/-- The inverse to `f` on the stable image is the iterate at one less than the factorial
of the cardinality. The bijection itself is `Function.bijOn_periodicPts`. -/
theorem invOn_iterate_pred_factorial_card :
    InvOn f^[(Nat.card α)! - 1] f (periodicPts f) (periodicPts f) := by
  have hfix (x : α) (hx : x ∈ periodicPts f) : f^[(Nat.card α)!] x = x := by
    have hcard := (Nat.sub_le (Nat.card α) 1).trans (Nat.self_le_factorial (Nat.card α))
    rw [← f.range_iterate_eq_periodicPts_of_card_sub_one_le hcard] at hx
    obtain ⟨y, rfl⟩ := hx
    exact congrFun f.iterate_factorial_card_comp_self y
  have hpos := Nat.factorial_pos (Nat.card α)
  rw [← Nat.pred_eq_sub_one]
  exact ⟨fun x hx ↦ (congrFun (iterate_pred_comp_of_pos f hpos) x).trans (hfix x hx),
    fun x hx ↦ (congrFun (comp_iterate_pred_of_pos f hpos) x).trans (hfix x hx)⟩

/-- Among positive powers of a finite self-map, the only idempotent is the stabilized
factorial power. -/
theorem End.isIdempotentElem_pow_iff_eq_pow_factorial_card (g : Function.End α) {n : ℕ}
    (hn : n ≠ 0) : IsIdempotentElem (g ^ n) ↔ g ^ n = g ^ (Nat.card α)! := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero hn) (le_max_left n (Nat.card α))
    have hk₀ : k ≠ 0 := by
      intro hzero
      exact Nat.factorial_ne_zero _ (by simpa [hzero] using hk)
    calc
      g ^ n = (g ^ n) ^ k := (h.pow_eq hk₀).symm
      _ = g ^ (max n (Nat.card α))! := by rw [← pow_mul, ← hk]
      _ = g ^ (Nat.card α)! := g.iterate_factorial_eq_iterate_factorial_card (le_max_right _ _)
  · intro h
    rw [h]
    -- Powers and multiplication in `Function.End` are iteration and composition by definition.
    exact g.iterate_factorial_card_comp_self

end Function
