/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real
public import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Basic

import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Rify
import TauCeti.Algebra.Order.BigOperators.ChainCombination
import TauCeti.Data.Fintype.CardFilterOrder

/-!
# The simplices of edgewise subdivisions are small and uniformly fat

Let `σ` be a finite set of vertices and `ρ` a face of the `k`-th edgewise subdivision whose
vertices have all their entries in `σ`. In barycentric coordinates on `σ`, with the sup norm on
`σ → ℝ`, the vertices of `ρ` are placed at mutual distance at most `1 / k`, and every
combination of them with coefficients `v` summing to zero has norm at least
`(2 * #σ ^ 2)⁻¹ * k⁻¹ * ∑ a, |v a|`. So the simplices of the edgewise subdivisions of a simplex
have mesh tending to zero and fatness bounded below independently of `k`, which is what
Whitehead's secant approximation of smooth triangulations needs from a subdivision.

Both estimates go through the partial sums of the coordinates along the vertex order: `k` times
the partial sum up to `i` of the coordinates of a vertex `u` is the number of entries of `u` that
are at most `i`. Along the vertices of a face these counts increase by one at a time and in
disjoint places, so a combination with coefficients summing to zero has partial sums at least
half as large as its coefficients.

## Main results

* `PreAbstractSimplicialComplex.norm_edgewisePoint_sub_edgewisePoint_le`: the vertices of a face
  of the `k`-th edgewise subdivision are at distance at most `1 / k`.
* `PreAbstractSimplicialComplex.mul_sum_abs_le_norm_sum_smul_edgewisePoint`: the faces of the
  `k`-th edgewise subdivision of `σ` are `(2 * #σ ^ 2)⁻¹`-fat at scale `1 / k`.

## References

* H. Freudenthal, *Simplizialzerlegungen von beschränkter Flachheit*, Ann. of Math. 43 (1942),
  580–582.
* H. Edelsbrunner, D. R. Grayson, *Edgewise subdivision of a simplex*, Discrete Comput. Geom. 24
  (2000), 707–719.
-/

public section

open Finset TauCeti

namespace PreAbstractSimplicialComplex

variable {ι : Type*} [LinearOrder ι] {K : PreAbstractSimplicialComplex ι} {k : ℕ}
  {ρ : Finset (K.EdgewiseVertex k)} {u w : K.EdgewiseVertex k}

/-! ### Counting entries in initial segments -/

/-- In a face of the edgewise subdivision, the number of entries of a vertex `u` in a lower set
exceeds that of any other vertex `w` by at most one. -/
private theorem card_filter_le_card_filter_add_one (hρ : ρ ∈ K.edgewiseSubdivision k)
    (hu : u ∈ ρ) (hw : w ∈ ρ) {p : ι → Prop} [DecidablePred p] (hp : Antitone p) :
    #{l | p (u.1 l)} ≤ #{l | p (w.1 l)} + 1 := by
  cases k with
  | zero => simp
  | succ m =>
    -- Drop the first entry of `u`; the `l + 1`-st entry of `u` dominates the `l`-th of `w`.
    rw [Fin.card_filter_univ_succ']
    have h₁ : #{l : Fin m | p (u.1 l.succ)} ≤ #{l : Fin m | p (w.1 l.castSucc)} :=
      card_le_card (monotone_filter_right _ fun l _ hl =>
        hp (le_of_lt_of_mem_edgewiseSubdivision hρ hw hu (Fin.castSucc_lt_succ (i := l))) hl)
    have h₂ : #{l : Fin m | p (w.1 l.castSucc)} ≤ #{l | p (w.1 l)} :=
      card_le_card_of_injOn Fin.castSucc (fun l hl => by simpa using hl)
        (Fin.castSucc_injective m).injOn
    split_ifs <;> omega

/-! ### Mesh and fatness -/

/-- The vertices of a face of the `k`-th edgewise subdivision are placed at distance at most
`1 / k` from each other, in the sup norm of the barycentric coordinates on any finite set `σ` of
vertices. -/
theorem norm_edgewisePoint_sub_edgewisePoint_le (hρ : ρ ∈ K.edgewiseSubdivision k) (hu : u ∈ ρ)
    (hw : w ∈ ρ) (σ : Finset ι) :
    ‖(fun i : σ => edgewisePoint u.1 i) - fun i : σ => edgewisePoint w.1 i‖ ≤ (k : ℝ)⁻¹ := by
  wlog huw : u ≤ w generalizing u w
  · rw [norm_sub_rev]
    exact this hw hu ((le_or_le_of_mem_edgewiseSubdivision hρ hu hw).resolve_left huw)
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  -- The number of entries equal to `i` is the number at most `i` minus the number below `i`.
  have hcount (x : K.EdgewiseVertex k) :
      (#{l | x.1 l = i} : ℝ) = #{l | x.1 l ≤ i} - #{l | x.1 l < i} := by
    rw [eq_sub_iff_add_eq, ← Nat.cast_add, Nat.cast_inj, ← card_union_of_disjoint
      (disjoint_filter.mpr fun l _ h h' => h'.ne h)]
    congr 1
    ext l
    simp [le_iff_eq_or_lt]
  have h₁ := card_filter_le_card_filter_add_one hρ hu hw (p := (· ≤ (i : ι))) antitone_le
  have h₂ := card_filter_le_card_filter_add_one hρ hu hw (p := (· < (i : ι))) antitone_lt
  have h₃ := card_filter_le_card_filter_of_le huw (p := (· ≤ (i : ι))) antitone_le
  have h₄ := card_filter_le_card_filter_of_le huw (p := (· < (i : ι))) antitone_lt
  rify at h₁ h₂ h₃ h₄
  rw [Pi.sub_apply, edgewisePoint_apply, edgewisePoint_apply, ← mul_sub, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (by positivity), hcount, hcount]
  refine mul_le_of_le_one_right (by positivity) (abs_le.mpr ⟨?_, ?_⟩) <;> linarith

/-- **Uniform fatness of edgewise subdivisions.** Let `ρ` be a face of the `k`-th edgewise
subdivision whose vertices have all their entries in `σ`. Then every combination of the
barycentric coordinate vectors of its vertices with coefficients `v` summing to zero has sup norm
at least `(2 * #σ ^ 2)⁻¹ * k⁻¹ * ∑ a, |v a|`. -/
theorem mul_sum_abs_le_norm_sum_smul_edgewisePoint (hρ : ρ ∈ K.edgewiseSubdivision k)
    {σ : Finset ι} (hσ : ∀ u ∈ ρ, ∀ l, u.1 l ∈ σ) (v : ρ → ℝ) (hv : ∑ a, v a = 0) :
    ((2 : ℝ) * #σ ^ 2)⁻¹ * (k : ℝ)⁻¹ * ∑ a, |v a| ≤
      ‖∑ a, v a • fun i : σ => edgewisePoint a.1.1 i‖ := by
  set x : σ → ℝ := ∑ a, v a • fun i : σ => edgewisePoint a.1.1 i with hx
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  -- `C a i` counts the entries of the vertex `a` that are at most `i`, and `N a j` those equal
  -- to `j`; `F i` is the set of vertices of `σ` that are at most `i`.
  set C : ρ → σ → ℕ := fun a i => #{l | a.1.1 l ≤ i.1} with hC
  set N : ρ → σ → ℕ := fun a j => #{l | a.1.1 l = j.1} with hN
  set F : σ → Finset σ := fun i => {j | j ≤ i} with hF
  have hcount (a : ρ) (i : σ) : C a i = ∑ j ∈ F i, N a j :=
    card_filter_le_eq_sum_card_filter_eq (hσ a.1 a.2) i
  have hxj (j : σ) : (k : ℝ) * x j = ∑ a, v a * N a j := by
    simp only [hx, hN, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, edgewisePoint_apply,
      Finset.mul_sum]
    refine sum_congr rfl fun a _ => ?_
    field_simp
  -- `k` times the partial sum of `x` up to `i` is the combination of the counts `C a i`.
  have hpartial (i : σ) : ∑ a, v a * C a i = (k : ℝ) * ∑ j ∈ F i, x j := by
    simp only [hcount, Nat.cast_sum, Finset.mul_sum, hxj]
    exact Finset.sum_comm
  -- Each partial sum of `x` is at most `#σ * ‖x‖`.
  have hbound (i : σ) : |∑ j ∈ F i, x j| ≤ #σ * ‖x‖ := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_card_nsmul _ _ ‖x‖
      fun j _ => norm_le_pi_norm x j).trans ?_)
    rw [nsmul_eq_mul]
    gcongr
    exact (card_filter_le _ _).trans (by simp)
  -- The counting vectors of the vertices of `ρ` form a chain to which the estimate applies.
  have hchain : ∀ a ∈ (univ : Finset ρ), ∀ b ∈ (univ : Finset ρ),
      (C a ≤ C b ∧ C b ≤ C a + 1) ∨ (C b ≤ C a ∧ C a ≤ C b + 1) := by
    intro a _ b _
    have hab := fun i : σ => card_filter_le_card_filter_add_one hρ a.2 b.2
      (p := (· ≤ (i : ι))) antitone_le
    have hba := fun i : σ => card_filter_le_card_filter_add_one hρ b.2 a.2
      (p := (· ≤ (i : ι))) antitone_le
    rcases le_or_le_of_mem_edgewiseSubdivision hρ a.2 b.2 with h | h
    · exact Or.inr ⟨fun i => card_filter_le_card_filter_of_le h (p := (· ≤ (i : ι))) antitone_le,
        hab⟩
    · exact Or.inl ⟨fun i => card_filter_le_card_filter_of_le h (p := (· ≤ (i : ι))) antitone_le,
        hba⟩
  have hinj : ∀ a ∈ (univ : Finset ρ), ∀ b ∈ (univ : Finset ρ), C a = C b → a = b := by
    intro a _ b _ hab
    by_contra hne
    have hne' : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
    rcases le_or_le_of_mem_edgewiseSubdivision hρ a.2 b.2 with h | h
    · obtain ⟨j, hj⟩ := exists_card_filter_lt_card_filter a.1.2.1 b.1.2.1 h
        (fun h' => hne' (Subtype.ext h'))
      exact hj.ne (congrFun hab ⟨a.1.1 j, hσ a.1 a.2 j⟩).symm
    · obtain ⟨j, hj⟩ := exists_card_filter_lt_card_filter b.1.2.1 a.1.2.1 h
        (fun h' => hne' (Subtype.ext h').symm)
      exact hj.ne (congrFun hab ⟨b.1.1 j, hσ b.1 b.2 j⟩)
  have hmain := sum_abs_le_two_mul_sum_abs_sum_mul C univ hchain hinj v hv
  simp only [hpartial, abs_mul, Nat.abs_cast] at hmain
  have hsum : ∑ i : σ, (k : ℝ) * |∑ j ∈ F i, x j| ≤ k * #σ ^ 2 * ‖x‖ := by
    calc ∑ i : σ, (k : ℝ) * |∑ j ∈ F i, x j| ≤ ∑ _i : σ, (k : ℝ) * (#σ * ‖x‖) :=
          sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hbound i) (by positivity)
      _ = k * #σ ^ 2 * ‖x‖ := by simp; ring
  rcases (#σ).eq_zero_or_pos with hσ0 | hσ0
  · simp [hσ0]
  have hrw : ((2 : ℝ) * #σ ^ 2)⁻¹ * (k : ℝ)⁻¹ * ∑ a, |v a| =
      (∑ a, |v a|) / (2 * (k * #σ ^ 2)) := by
    field_simp
  rw [hrw, div_le_iff₀ (by positivity)]
  linarith

end PreAbstractSimplicialComplex
