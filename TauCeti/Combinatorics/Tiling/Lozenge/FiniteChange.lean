/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Height
import Mathlib.Algebra.BigOperators.Group.Finset.Interval
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.SuccPred.Int

/-!
# Finite changes preserve lozenge counts

Let `M`, `M'` be plane tilings differing on finitely many edges. The increments of the difference
`D = H_M − H_{M'}` of their height functions vanish along every edge outside the symmetric
difference, so `D` is constant along every row and column far from it, hence constant off a
square: `D` minus that constant has finite support. Along each row, the number of edges of
direction `e₁` in `M ∖ M'` minus the number in `M' ∖ M` is a telescoping sum of the increments of
`D`, which vanishes between two points far away. So for each direction `k` the sets `M ∖ M'` and
`M' ∖ M` contain equally many edges of direction `k`: for `e₁` by the telescoping sums, and for the
other two directions by applying the rotation `ρ`, which permutes the directions.

## Main statements

* `TauCeti.IsTiling.exists_finite_setOf_tilingHeight_sub_ne`: if two plane tilings differ on
  finitely many edges, the difference of their height functions is constant off a finite set.
* `TauCeti.IsTiling.ncard_sdiff_inter_eq`: if two plane tilings differ on finitely many edges,
  then for each direction `k` the sets `M ∖ M'` and `M' ∖ M` contain equally many edges of
  direction `k`.

## References

* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009).
-/

public section

namespace TauCeti

variable {M M' : Set TriEdge}

/-- A set `X` of edges of direction `e₁` whose initial vertices lie in a finite set `s` has as
many elements as there are `p ∈ s` with `(p, e₁) ∈ X`. -/
private theorem ncard_eq_sum_indicator_of_subset {X : Set TriEdge} {s : Finset (ℤ × ℤ)}
    (hX : X ⊆ edgesOfDir 0) (hXs : ∀ e ∈ X, e.v ∈ s) :
    (X.ncard : ℤ) = ∑ p ∈ s, X.indicator 1 ⟨p, 0⟩ := by
  classical
  have hX' : X = (fun p : ℤ × ℤ => (⟨p, 0⟩ : TriEdge)) '' ↑(s.filter fun p => ⟨p, 0⟩ ∈ X) := by
    ext ⟨v, k⟩
    refine ⟨fun he => ⟨v, ?_, ?_⟩, ?_⟩
    · have hk : k = 0 := mem_edgesOfDir.1 (hX he)
      subst hk
      exact Finset.mem_filter.2 ⟨hXs _ he, he⟩
    · rw [show k = 0 from mem_edgesOfDir.1 (hX he)]
    · rintro ⟨p, hp, hpe⟩
      exact hpe ▸ (Finset.mem_filter.1 hp).2
  simp_rw [Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole, Nat.cast_inj]
  conv_lhs => rw [hX']
  rw [Set.ncard_image_of_injective _ fun p q h => congrArg TriEdge.v h, Set.ncard_coe_finset]

namespace IsTiling

variable (h : IsTiling Set.univ M) (h' : IsTiling Set.univ M')
include h h'

/-- Along an edge on which two plane tilings agree, the difference of their height functions does
not change. -/
theorem tilingHeight_sub_target_eq {e : TriEdge} (he : e ∉ symmDiff M M') :
    tilingHeight M e.target - tilingHeight M' e.target =
      tilingHeight M e.v - tilingHeight M' e.v := by
  have h₁ := h.tilingHeight_target_sub_v e
  have h₂ := h'.tilingHeight_target_sub_v e
  have hc : heightCochain M e = heightCochain M' e := by
    by_cases hM : e ∈ M <;> by_cases hM' : e ∈ M' <;> simp_all [Set.mem_symmDiff]
  omega

/-- Along an edge `e` of direction `e₁` the increment of `H_M − H_{M'}` is
`[e ∈ M ∖ M'] − [e ∈ M' ∖ M]`. -/
theorem tilingHeight_sub_add_one_zero_sub (p : ℤ × ℤ) :
    (tilingHeight M (p + (1, 0)) - tilingHeight M' (p + (1, 0))) -
        (tilingHeight M p - tilingHeight M' p) =
      (M \ M' ∩ edgesOfDir 0).indicator 1 ⟨p, 0⟩ - (M' \ M ∩ edgesOfDir 0).indicator 1 ⟨p, 0⟩ := by
  have h₁ := h.tilingHeight_target_sub_v ⟨p, 0⟩
  have h₂ := h'.tilingHeight_target_sub_v ⟨p, 0⟩
  rw [heightCochain_mk_zero] at h₁ h₂
  simp only [TriEdge.target_mk, latticeDir_zero] at h₁ h₂
  by_cases hM : (⟨p, 0⟩ : TriEdge) ∈ M <;> by_cases hM' : (⟨p, 0⟩ : TriEdge) ∈ M' <;>
    simp [hM, hM'] at h₁ h₂ ⊢ <;> omega

/-- If two plane tilings differ on finitely many edges, there is `K` such that the difference of
their height functions takes one value at every point with a coordinate of absolute value at least
`K`. -/
theorem exists_tilingHeight_sub_eq (hS : (symmDiff M M').Finite) :
    ∃ K : ℕ, (∀ e ∈ symmDiff M M', |e.v.1| < K ∧ |e.v.2| < K) ∧ ∃ c : ℤ,
      ∀ p : ℤ × ℤ, ((K : ℤ) ≤ |p.1| ∨ (K : ℤ) ≤ |p.2|) →
        tilingHeight M p - tilingHeight M' p = c := by
  set D : ℤ × ℤ → ℤ := fun p => tilingHeight M p - tilingHeight M' p
  -- A bound `R` on the coordinates of the initial vertices of the edges where `M`, `M'` differ.
  obtain ⟨R, hR⟩ : ∃ R : ℕ, ∀ e ∈ symmDiff M M', |e.v.1| < R ∧ |e.v.2| < R := by
    refine ⟨hS.toFinset.sup (fun e => e.v.1.natAbs + e.v.2.natAbs) + 1, fun e he => ?_⟩
    have := Finset.le_sup (f := fun e => e.v.1.natAbs + e.v.2.natAbs) (hS.mem_toFinset.2 he)
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
    constructor <;> omega
  have hstep : ∀ e : TriEdge, (((R + 1 : ℕ) : ℤ) ≤ |e.v.1| ∨ ((R + 1 : ℕ) : ℤ) ≤ |e.v.2|) →
      D e.target = D e.v := fun e he =>
    tilingHeight_sub_target_eq h h' fun hS' => by
      have := hR e hS'
      push_cast at he
      omega
  set K : ℕ := R + 1
  -- `D` is constant along the rows and columns with a coordinate of absolute value at least `K`.
  have hrow : ∀ y : ℤ, (K : ℤ) ≤ |y| → ∀ x x', D (x, y) = D (x', y) := fun y hy x x' => by
    have hp : Function.Periodic (fun x => D (x, y)) 1 := fun x => by
      simpa using hstep ⟨(x, y), 0⟩ (Or.inr hy)
    simpa using (hp.int_mul_eq x).trans (hp.int_mul_eq x').symm
  have hcol : ∀ x : ℤ, (K : ℤ) ≤ |x| → ∀ y y', D (x, y) = D (x, y') := fun x hx y y' => by
    have hp : Function.Periodic (fun y => D (x, y)) 1 := fun y => by
      simpa using hstep ⟨(x, y), 1⟩ (Or.inl hx)
    simpa using (hp.int_mul_eq y).trans (hp.int_mul_eq y').symm
  have hK : (K : ℤ) ≤ |(K : ℤ)| := le_abs_self _
  refine ⟨K, fun e he => ?_, D (K, K), fun ⟨x, y⟩ hp => ?_⟩
  · have := hR e he
    push_cast [K]
    omega
  -- The goal is `D (x, y) = D (K, K)` with `D` unfolded; restate it in terms of `D` so that `hrow`
  -- and `hcol` rewrite it.
  change D (x, y) = D (K, K)
  rcases hp with hx | hy
  · rw [hcol x hx y K, hrow K hK x K]
  · rw [hrow y hy x K, hcol K hK y K]

/-- **Heights of finitely different tilings.** If two plane tilings differ on finitely many edges,
the difference `H_M − H_{M'}` of their height functions is constant off a finite set. -/
theorem exists_finite_setOf_tilingHeight_sub_ne (hS : (symmDiff M M').Finite) :
    ∃ c : ℤ, {p : ℤ × ℤ | tilingHeight M p - tilingHeight M' p ≠ c}.Finite := by
  obtain ⟨K, -, c, hc⟩ := exists_tilingHeight_sub_eq h h' hS
  refine ⟨c, (Set.finite_Icc ((-K : ℤ), (-K : ℤ)) ((K : ℤ), (K : ℤ))).subset fun p hp => ?_⟩
  have : ¬((K : ℤ) ≤ |p.1| ∨ (K : ℤ) ≤ |p.2|) := fun h'' => hp (hc p h'')
  rw [not_or, not_le, not_le, abs_lt, abs_lt] at this
  exact ⟨⟨this.1.1.le, this.2.1.le⟩, ⟨this.1.2.le, this.2.2.le⟩⟩

/-- The case `k = 0` (direction `e₁`) of `ncard_sdiff_inter_eq`. -/
private theorem ncard_sdiff_inter_edgesOfDir_zero_eq (hS : (symmDiff M M').Finite) :
    (M \ M' ∩ edgesOfDir 0).ncard = (M' \ M ∩ edgesOfDir 0).ncard := by
  -- Both counts are sums over a square `box` containing the symmetric difference; their
  -- difference is the sum of the increments of `H_M − H_{M'}` along the rows of `box`, and each
  -- row telescopes to the difference of two values far away, which is `0`.
  obtain ⟨K, hK, c, hc⟩ := exists_tilingHeight_sub_eq h h' hS
  set D : ℤ × ℤ → ℤ := fun p => tilingHeight M p - tilingHeight M' p with hD
  set box : Finset (ℤ × ℤ) := Finset.Ico (-K : ℤ) K ×ˢ Finset.Ico (-K : ℤ) K
  have hbox : ∀ e ∈ symmDiff M M', e.v ∈ box := fun e he => by
    obtain ⟨h₁, h₂⟩ := hK e he
    simp only [box, Finset.mem_product, Finset.mem_Ico]
    rw [abs_lt] at h₁ h₂
    exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
  have hA := ncard_eq_sum_indicator_of_subset (X := M \ M' ∩ edgesOfDir 0) Set.inter_subset_right
    fun e he => hbox e (Or.inl he.1)
  have hB := ncard_eq_sum_indicator_of_subset (X := M' \ M ∩ edgesOfDir 0) Set.inter_subset_right
    fun e he => hbox e (Or.inr he.1)
  have hzero : ∑ p ∈ box, (D (p + (1, 0)) - D p) = 0 := by
    rw [Finset.sum_product_right]
    refine Finset.sum_eq_zero fun y _ => ?_
    have := Finset.sum_Ico_int_sub K (fun x => D (x, y))
    simp only [Prod.mk_add_mk, add_zero]
    rw [← neg_eq_zero, ← Finset.sum_neg_distrib]
    simp only [neg_sub]
    rw [this]
    have hK₁ := hc (K, y) (Or.inl (by simp))
    have hK₂ := hc (-K, y) (Or.inl (by simp))
    simp only [hD] at hK₁ hK₂ ⊢
    omega
  simp_rw [hD, tilingHeight_sub_add_one_zero_sub h h', Finset.sum_sub_distrib, sub_eq_zero] at hzero
  have : ((M \ M' ∩ edgesOfDir 0).ncard : ℤ) = (M' \ M ∩ edgesOfDir 0).ncard := by
    rw [hA, hB, hzero]
  exact_mod_cast this

end IsTiling

/-- **Finite changes preserve lozenge counts.** If two plane tilings differ on finitely many
edges, then for each direction `k` the sets `M ∖ M'` and `M' ∖ M` contain equally many edges of
direction `k`. -/
theorem IsTiling.ncard_sdiff_inter_eq (h : IsTiling Set.univ M) (h' : IsTiling Set.univ M')
    (hS : (symmDiff M M').Finite) (k : Fin 3) :
    (M \ M' ∩ edgesOfDir k).ncard = (M' \ M ∩ edgesOfDir k).ncard := by
  -- `ρ` moves direction `k` to `k + 1`; rotating once or twice brings it to direction `0`.
  have hρ : ∀ (N N' : Set TriEdge) (j : Fin 3), (N \ N' ∩ edgesOfDir j).ncard =
      (TriEdge.rot '' N \ TriEdge.rot '' N' ∩ edgesOfDir (j + 1)).ncard := fun N N' j => by
    rw [← image_rot_edgesOfDir, ← Set.image_sdiff TriEdge.rot.injective,
      ← Set.image_inter TriEdge.rot.injective, Set.ncard_image_of_injective _ TriEdge.rot.injective]
  have hS₁ : (symmDiff (TriEdge.rot '' M) (TriEdge.rot '' M')).Finite := by
    rw [← Set.image_symmDiff TriEdge.rot.injective]
    exact hS.image _
  have hS₂ : (symmDiff (TriEdge.rot '' (TriEdge.rot '' M))
      (TriEdge.rot '' (TriEdge.rot '' M'))).Finite := by
    rw [← Set.image_symmDiff TriEdge.rot.injective]
    exact hS₁.image _
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · exact ncard_sdiff_inter_edgesOfDir_zero_eq h h' hS
  · rw [hρ M M', hρ M' M, hρ (TriEdge.rot '' M), hρ (TriEdge.rot '' M')]
    exact ncard_sdiff_inter_edgesOfDir_zero_eq h.image_rot.image_rot h'.image_rot.image_rot hS₂
  · rw [hρ M M', hρ M' M]
    exact ncard_sdiff_inter_edgesOfDir_zero_eq h.image_rot h'.image_rot hS₁

end TauCeti
