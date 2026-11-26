/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Height
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Int.Interval
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

## Main definitions

* `TauCeti.edgesOfDir k`: the edges of direction `k`.

## Main statements

* `TauCeti.IsTiling.finite_setOf_tilingHeight_sub_ne`: if two plane tilings differ on finitely
  many edges, the difference of their height functions is constant off a finite set.
* `TauCeti.IsTiling.ncard_sdiff_inter_eq`: if two plane tilings differ on finitely many edges,
  then for each direction `k` the sets `M ∖ M'` and `M' ∖ M` contain equally many edges of
  direction `k`.

## References

* R. Kenyon, *Lectures on dimers*, IAS/Park City Math. Ser. 16 (2009).
-/

public section

namespace TauCeti

variable {M M' : Set TriEdge}

/-- The edges of direction `k` of a set of edges. -/
def edgesOfDir (k : Fin 3) : Set TriEdge :=
  {e | e.k = k}

@[simp] theorem mem_edgesOfDir {k : Fin 3} {e : TriEdge} : e ∈ edgesOfDir k ↔ e.k = k :=
  Iff.rfl

/-- A function of an integer whose consecutive differences vanish is constant. -/
theorem eq_of_forall_add_one_eq {f : ℤ → ℤ} (hf : ∀ n, f (n + 1) = f n) (n m : ℤ) :
    f n = f m := by
  have h : ∀ n, f n = f 0 := fun n => by
    induction n using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [hf, ih]
    | pred n ih => rw [← ih, ← hf (-(n : ℤ) - 1), sub_add_cancel]
  rw [h n, h m]

open Classical in
/-- The height cochain along an edge of direction `e₁` is the indicator of `M`. -/
theorem heightCochain_mk_zero (M : Set TriEdge) (v : ℤ × ℤ) :
    heightCochain M ⟨v, 0⟩ = if (⟨v, 0⟩ : TriEdge) ∈ M then 1 else 0 := by
  by_cases hM : (⟨v, 0⟩ : TriEdge) ∈ M <;> simp [hM]

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
    rw [Set.mem_symmDiff, not_or, not_and_not_right, not_and_not_right] at he
    by_cases hM : e ∈ M
    · rw [heightCochain_of_mem hM, heightCochain_of_mem (he.1 hM)]
    · rw [heightCochain_of_notMem hM, heightCochain_of_notMem fun hM' => hM (he.2 hM')]
  omega

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
  have hrow : ∀ y : ℤ, (K : ℤ) ≤ |y| → ∀ x x', D (x, y) = D (x', y) := fun y hy =>
    eq_of_forall_add_one_eq (f := fun x => D (x, y)) fun x => by
      simpa using hstep ⟨(x, y), 0⟩ (Or.inr hy)
  have hcol : ∀ x : ℤ, (K : ℤ) ≤ |x| → ∀ y y', D (x, y) = D (x, y') := fun x hx =>
    eq_of_forall_add_one_eq (f := fun y => D (x, y)) fun y => by
      simpa using hstep ⟨(x, y), 1⟩ (Or.inl hx)
  have hK : (K : ℤ) ≤ |(K : ℤ)| := le_abs_self _
  refine ⟨K, fun e he => ?_, D (K, K), fun ⟨x, y⟩ hp => ?_⟩
  · have := hR e he
    push_cast [K]
    omega
  change D (x, y) = D (K, K)
  rcases hp with hx | hy
  · rw [hcol x hx y K, hrow K hK x K]
  · rw [hrow y hy x K, hcol K hK y K]

/-- **Heights of finitely different tilings.** If two plane tilings differ on finitely many edges,
the difference `H_M − H_{M'}` of their height functions is constant off a finite set. -/
theorem finite_setOf_tilingHeight_sub_ne (hS : (symmDiff M M').Finite) :
    ∃ c : ℤ, {p : ℤ × ℤ | tilingHeight M p - tilingHeight M' p ≠ c}.Finite := by
  obtain ⟨K, -, c, hc⟩ := exists_tilingHeight_sub_eq h h' hS
  refine ⟨c, (Set.finite_Icc ((-K : ℤ), (-K : ℤ)) ((K : ℤ), (K : ℤ))).subset fun p hp => ?_⟩
  have : ¬((K : ℤ) ≤ |p.1| ∨ (K : ℤ) ≤ |p.2|) := fun h'' => hp (hc p h'')
  rw [not_or, not_le, not_le, abs_lt, abs_lt] at this
  exact ⟨⟨this.1.1.le, this.2.1.le⟩, ⟨this.1.2.le, this.2.2.le⟩⟩

/-- The case `k = e₁` of `ncard_sdiff_inter_eq`: along each row the signed count of edges of
direction `e₁` in `M ∖ M'` and `M' ∖ M` telescopes to a difference of `H_M − H_{M'}` between two
points far away. -/
theorem ncard_sdiff_inter_edgesOfDir_zero_eq (hS : (symmDiff M M').Finite) :
    (M \ M' ∩ edgesOfDir 0).ncard = (M' \ M ∩ edgesOfDir 0).ncard := by
  classical
  obtain ⟨K, hK, c, hc⟩ := exists_tilingHeight_sub_eq h h' hS
  set D : ℤ × ℤ → ℤ := fun p => tilingHeight M p - tilingHeight M' p with hD
  set A := M \ M' ∩ edgesOfDir 0
  set B := M' \ M ∩ edgesOfDir 0
  -- The edges `((x, y), 0)` with `-K ≤ x, y < K` contain `A` and `B`.
  set box : Finset (ℤ × ℤ) := Finset.Ico (-K : ℤ) K ×ˢ Finset.Ico (-K : ℤ) K
  set edge : ℤ × ℤ → TriEdge := fun p => ⟨p, 0⟩
  have hinj : Set.InjOn edge box := fun p _ q _ hpq => congrArg TriEdge.v hpq
  have hsub : ∀ X : Set TriEdge, X ⊆ symmDiff M M' → X ⊆ edgesOfDir 0 →
      X = ↑((box.image edge).filter (· ∈ X)) := by
    intro X hX hX0
    ext e
    simp only [Finset.coe_filter, Finset.mem_image, Set.mem_ofPred_eq]
    refine ⟨fun he => ⟨⟨e.v, ?_, ?_⟩, he⟩, fun he => he.2⟩
    · obtain ⟨h₁, h₂⟩ := hK e (hX he)
      simp only [box, Finset.mem_product, Finset.mem_Ico]
      rw [abs_lt] at h₁ h₂
      exact ⟨⟨by omega, by omega⟩, by omega, by omega⟩
    · obtain ⟨v, k⟩ := e
      have hk : k = 0 := hX0 he
      simp [edge, hk]
  have hA : A ⊆ symmDiff M M' := fun e he => Or.inl ⟨he.1.1, he.1.2⟩
  have hB : B ⊆ symmDiff M M' := fun e he => Or.inr ⟨he.1.1, he.1.2⟩
  -- The increment of `D` along `((x, y), 0)` is `[e ∈ A] − [e ∈ B]`.
  have hterm : ∀ p : ℤ × ℤ, D (p + (1, 0)) - D p =
      (if edge p ∈ A then 1 else 0) - (if edge p ∈ B then 1 else 0) := fun p => by
    have h₁ := h.tilingHeight_target_sub_v (edge p)
    have h₂ := h'.tilingHeight_target_sub_v (edge p)
    rw [heightCochain_mk_zero] at h₁ h₂
    simp only [edge, TriEdge.target_mk, latticeDir_zero] at h₁ h₂
    simp only [hD, A, B, edge, Set.mem_inter_iff, Set.mem_sdiff, mem_edgesOfDir, and_true]
    by_cases hM : (⟨p, 0⟩ : TriEdge) ∈ M <;> by_cases hM' : (⟨p, 0⟩ : TriEdge) ∈ M' <;>
      simp [hM, hM'] at h₁ h₂ ⊢ <;> omega
  -- Along each row of the box the increments telescope to `c − c = 0`.
  have htel : ∀ (f : ℤ → ℤ) (a b : ℤ), a ≤ b →
      ∑ x ∈ Finset.Ico a b, (f (x + 1) - f x) = f b - f a := by
    intro f a b hab
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = a + n := ⟨(b - a).toNat, by omega⟩
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.cast_succ, ← add_assoc, ← Finset.sum_Ico_add_eq_sum_Ico_add_one (by omega),
        ih (by omega)]
      ring
  have hzero : ∑ p ∈ box, (D (p + (1, 0)) - D p) = 0 := by
    rw [Finset.sum_product_right]
    refine Finset.sum_eq_zero fun y _ => ?_
    have := htel (fun x => D (x, y)) (-K) K (by omega)
    simp only [Prod.mk_add_mk, add_zero] at this ⊢
    rw [this]
    have hK₁ := hc (K, y) (Or.inl (by simp))
    have hK₂ := hc (-K, y) (Or.inl (by simp))
    simp only [hD] at hK₁ hK₂ ⊢
    omega
  simp_rw [hterm] at hzero
  rw [Finset.sum_sub_distrib, ← Finset.sum_image (f := fun e => if e ∈ A then (1 : ℤ) else 0)
    hinj, ← Finset.sum_image (f := fun e => if e ∈ B then (1 : ℤ) else 0) hinj,
    Finset.sum_boole, Finset.sum_boole, sub_eq_zero, Nat.cast_inj] at hzero
  rw [hsub A hA Set.inter_subset_right, hsub B hB Set.inter_subset_right, Set.ncard_coe_finset,
    Set.ncard_coe_finset]
  convert hzero using 3

end IsTiling

/-- `ρ` maps the edges of direction `k` of `M ∖ M'` onto the edges of direction `k + 1` of
`ρ M ∖ ρ M'`. -/
theorem image_rot_sdiff_inter_edgesOfDir (M M' : Set TriEdge) (k : Fin 3) :
    TriEdge.rot '' (M \ M' ∩ edgesOfDir k) =
      TriEdge.rot '' M \ TriEdge.rot '' M' ∩ edgesOfDir (k + 1) := by
  ext e
  obtain ⟨e, rfl⟩ := TriEdge.rot.surjective e
  simp only [TriEdge.rot.injective.mem_set_image, Set.mem_inter_iff, Set.mem_sdiff,
    mem_edgesOfDir, TriEdge.rot_k, add_left_inj]

/-- `ρ` maps the symmetric difference of `M` and `M'` onto that of `ρ M` and `ρ M'`. -/
theorem symmDiff_image_rot (M M' : Set TriEdge) :
    symmDiff (TriEdge.rot '' M) (TriEdge.rot '' M') = TriEdge.rot '' symmDiff M M' :=
  (Set.image_symmDiff TriEdge.rot.injective M M').symm

/-- `ρ` maps plane tilings to plane tilings. -/
theorem IsTiling.image_rot (h : IsTiling Set.univ M) : IsTiling Set.univ (TriEdge.rot '' M) := by
  have := (isTiling_rot_iff (R := Set.univ) (M := M)).2 h
  rwa [Set.image_univ_of_surjective TriFace.rot.surjective] at this

/-- **Finite changes preserve lozenge counts.** If two plane tilings differ on finitely many
edges, then for each direction `k` the sets `M ∖ M'` and `M' ∖ M` contain equally many edges of
direction `k`. -/
theorem IsTiling.ncard_sdiff_inter_eq (h : IsTiling Set.univ M) (h' : IsTiling Set.univ M')
    (hS : (symmDiff M M').Finite) (k : Fin 3) :
    (M \ M' ∩ edgesOfDir k).ncard = (M' \ M ∩ edgesOfDir k).ncard := by
  -- `ρ` moves direction `k` to `k + 1`; rotating once or twice brings it to direction `0`.
  have hρ : ∀ (N N' : Set TriEdge) (j : Fin 3), (N \ N' ∩ edgesOfDir j).ncard =
      (TriEdge.rot '' N \ TriEdge.rot '' N' ∩ edgesOfDir (j + 1)).ncard := fun N N' j => by
    rw [← image_rot_sdiff_inter_edgesOfDir, Set.ncard_image_of_injective _ TriEdge.rot.injective]
  have hS₁ : (symmDiff (TriEdge.rot '' M) (TriEdge.rot '' M')).Finite := by
    rw [symmDiff_image_rot]
    exact hS.image _
  have hS₂ : (symmDiff (TriEdge.rot '' (TriEdge.rot '' M))
      (TriEdge.rot '' (TriEdge.rot '' M'))).Finite := by
    rw [symmDiff_image_rot]
    exact hS₁.image _
  fin_cases k
  · exact ncard_sdiff_inter_edgesOfDir_zero_eq h h' hS
  · change (M \ M' ∩ edgesOfDir 1).ncard = (M' \ M ∩ edgesOfDir 1).ncard
    rw [hρ M M', hρ M' M, hρ (TriEdge.rot '' M), hρ (TriEdge.rot '' M')]
    exact ncard_sdiff_inter_edgesOfDir_zero_eq h.image_rot.image_rot h'.image_rot.image_rot hS₂
  · change (M \ M' ∩ edgesOfDir 2).ncard = (M' \ M ∩ edgesOfDir 2).ncard
    rw [hρ M M', hρ M' M]
    exact ncard_sdiff_inter_edgesOfDir_zero_eq h.image_rot h'.image_rot hS₁

end TauCeti
