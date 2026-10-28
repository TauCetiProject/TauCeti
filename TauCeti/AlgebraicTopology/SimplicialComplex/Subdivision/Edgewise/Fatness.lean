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
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic.Rify
import TauCeti.Order.Chain

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

/-! ### Chains of counting vectors -/

/-- Let the vectors `C a`, for `a ∈ A`, of natural numbers be distinct and pairwise comparable,
with each coordinate differing by at most one between any two of them. Then a combination of them
with coefficients `v` summing to zero satisfies `∑ a, |v a| ≤ 2 * ∑ i, |∑ a, v a * C a i|`. -/
private theorem sum_abs_le_two_mul_sum_abs_sum_mul {α β : Type*} [Fintype β]
    (C : α → β → ℕ) (A : Finset α)
    (hC : ∀ a ∈ A, ∀ b ∈ A, (C a ≤ C b ∧ C b ≤ C a + 1) ∨ (C b ≤ C a ∧ C a ≤ C b + 1))
    (hinj : ∀ a ∈ A, ∀ b ∈ A, C a = C b → a = b) (v : α → ℝ) (hv : ∑ a ∈ A, v a = 0) :
    ∑ a ∈ A, |v a| ≤ 2 * ∑ i, |∑ a ∈ A, v a * C a i| := by
  classical
  -- Remove the largest vector `t`. Where it exceeds the second largest `t'`, all the other
  -- vectors agree with `t'`, so there the combination only sees the coefficient of `t`. Merge
  -- that coefficient into the one of `t'` and induct.
  induction A using Finset.strongInduction generalizing v with
  | H A ih =>
  rcases A.eq_empty_or_nonempty with rfl | hne
  · simp
  -- Every nonempty part of `A` has a vector dominating all the others in it.
  have hmax : ∀ B ⊆ A, B.Nonempty → ∃ t ∈ B, ∀ a ∈ B, C a ≤ C t := by
    intro B hBA hB
    have hchain : IsChain (· ≤ ·) (C '' (B : Set α)) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ -
      exact (hC a (hBA ha) b (hBA hb)).imp And.left And.left
    obtain ⟨_, ⟨t, ht, rfl⟩, hgreat⟩ :=
      hchain.exists_isGreatest (B.finite_toSet.image C) ((coe_nonempty.mpr hB).image C)
    exact ⟨t, ht, fun a ha => hgreat ⟨a, ha, rfl⟩⟩
  obtain ⟨t, htA, ht⟩ := hmax A subset_rfl hne
  rcases (A.erase t).eq_empty_or_nonempty with hA' | hA'
  · -- Then `A = {t}`, and `v t = 0`.
    obtain rfl : A = {t} := (erase_eq_empty_iff A t).mp hA' |>.resolve_left hne.ne_empty
    simp only [sum_singleton] at hv
    simp [hv]
  obtain ⟨t', ht'A', ht'⟩ := hmax (A.erase t) (erase_subset t A) hA'
  have ht'A : t' ∈ A := mem_of_mem_erase ht'A'
  -- Merge the coefficient of `t` into that of `t'`, and apply the induction hypothesis.
  set v' : α → ℝ := fun a => v a + if a = t' then v t else 0 with hv'_def
  have hsum' (f : α → ℝ) : ∑ a ∈ A.erase t, v' a * f a =
      ∑ a ∈ A.erase t, v a * f a + v t * f t' := by
    simp [hv'_def, add_mul, Finset.sum_add_distrib, ht'A']
  have hv' : ∑ a ∈ A.erase t, v' a = 0 := by
    have h := hsum' fun _ => 1
    simp only [mul_one] at h
    rw [h, sum_erase_add A v htA, hv]
  have hIH := ih (A.erase t) (erase_ssubset htA)
    (fun a ha b hb => hC a (mem_of_mem_erase ha) b (mem_of_mem_erase hb))
    (fun a ha b hb => hinj a (mem_of_mem_erase ha) b (mem_of_mem_erase hb)) v' hv'
  -- Coordinatewise, the vector of `t` exceeds that of `t'` by `0` or `1`.
  have htt' (i : β) : C t i = C t' i ∨ C t i = C t' i + 1 := by
    have h₁ : C t' i ≤ C t i := ht t' ht'A i
    rcases hC t htA t' ht'A with h | h
    · have h₂ : C t i ≤ C t' i := h.1 i
      omega
    · have h₂ : C t i ≤ C t' i + 1 := h.2 i
      omega
  have hcoord (i : β) : |∑ a ∈ A, v a * C a i| =
      |∑ a ∈ A.erase t, v' a * C a i| + |v t| * ((C t i : ℝ) - C t' i) := by
    rw [hsum' fun a => (C a i : ℝ), ← add_sum_erase A _ htA]
    rcases htt' i with h | h
    · rw [h, sub_self, mul_zero, add_zero, add_comm]
    · -- Where `t` exceeds `t'`, every other vector agrees with `t'`, so the rest cancels.
      have hagree : ∀ a ∈ A.erase t, C a i = C t' i := by
        intro a ha
        refine le_antisymm (ht' a ha i) ?_
        rcases hC a (mem_of_mem_erase ha) t htA with h' | h'
        · have h₂ : C t i ≤ C a i + 1 := h'.2 i
          omega
        · have h₂ : C t i ≤ C a i := h'.1 i
          omega
      have hrest : ∑ a ∈ A.erase t, v a * C a i + v t * C t' i = 0 := by
        rw [← hsum' fun a => (C a i : ℝ), Finset.sum_congr rfl fun a ha => by rw [hagree a ha],
          ← Finset.sum_mul, hv', zero_mul]
      rw [h, Nat.cast_add, Nat.cast_one, add_sub_cancel_left, mul_one, hrest, abs_zero, zero_add]
      congr 1
      linarith
  -- The vectors of `t` and `t'` differ somewhere.
  obtain ⟨i₀, hi₀⟩ : ∃ i, C t' i < C t i := by
    have hne : C t' ≠ C t := fun h => (ne_of_mem_erase ht'A') (hinj t' ht'A t htA h)
    exact (Pi.lt_def.mp (lt_of_le_of_ne (ht t' ht'A) hne)).2
  have hgap : 1 ≤ ∑ i, ((C t i : ℝ) - C t' i) := by
    calc (1 : ℝ) ≤ (C t i₀ : ℝ) - C t' i₀ := by
          rw [le_sub_iff_add_le', ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
          omega
      _ ≤ ∑ i, ((C t i : ℝ) - C t' i) :=
          single_le_sum (f := fun i => (C t i : ℝ) - C t' i)
            (fun i _ => sub_nonneg.mpr (Nat.cast_le.mpr (ht t' ht'A i))) (mem_univ i₀)
  -- Removing `t` costs `|v t|` once on the left and at least `|v t|` on the right.
  have hleft : ∑ a ∈ A.erase t, |v a| ≤ ∑ a ∈ A.erase t, |v' a| + |v t| := by
    have hpt (a : α) : |v a| ≤ |v' a| + if a = t' then |v t| else 0 := by
      split_ifs with h
      · simpa [hv'_def, h] using abs_sub (v t' + v t) (v t)
      · simp [hv'_def, h]
    calc ∑ a ∈ A.erase t, |v a| ≤ ∑ a ∈ A.erase t, (|v' a| + if a = t' then |v t| else 0) :=
          sum_le_sum fun a _ => hpt a
      _ = ∑ a ∈ A.erase t, |v' a| + |v t| := by simp [Finset.sum_add_distrib, ht'A']
  have hright : ∑ i, |∑ a ∈ A, v a * C a i| =
      ∑ i, |∑ a ∈ A.erase t, v' a * C a i| + |v t| * ∑ i, ((C t i : ℝ) - C t' i) := by
    simp only [hcoord, Finset.sum_add_distrib, Finset.mul_sum]
  rw [← add_sum_erase A _ htA, hright]
  nlinarith [abs_nonneg (v t)]

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

/-- If `u ≤ w` coordinatewise, then `w` has at most as many entries as `u` in a lower set. -/
private theorem card_filter_le_card_filter_of_le (huw : u ≤ w) {p : ι → Prop} [DecidablePred p]
    (hp : Antitone p) : #{l | p (w.1 l)} ≤ #{l | p (u.1 l)} :=
  card_le_card (monotone_filter_right _ fun l _ hl => hp (huw l) hl)

/-- If `u ≤ w` are distinct monotone tuples, then at some entry `u j` of `u`, fewer entries of
`w` than of `u` are at most `u j`. -/
private theorem exists_card_filter_lt_card_filter (huw : u ≤ w) (hne : u ≠ w) :
    ∃ j, #{l | w.1 l ≤ u.1 j} < #{l | u.1 l ≤ u.1 j} := by
  obtain ⟨j, hj⟩ : ∃ j, u.1 j ≠ w.1 j := by
    by_contra! h
    exact hne (Subtype.ext (funext h))
  have hlt : u.1 j < w.1 j := lt_of_le_of_ne (huw j) hj
  refine ⟨j, ?_⟩
  calc #{l | w.1 l ≤ u.1 j} ≤ #(Iio j) := card_le_card fun l hl => by
        rw [mem_filter] at hl
        exact mem_Iio.mpr (lt_of_not_ge fun hjl => (hlt.trans_le (w.2.1 hjl)).not_ge hl.2)
    _ < #(Iic j) := by simp
    _ ≤ #{l | u.1 l ≤ u.1 j} := card_le_card fun l hl =>
        mem_filter.mpr ⟨mem_univ l, u.2.1 (mem_Iic.mp hl)⟩

/-- For a tuple with entries in `σ`, the number of entries at most `i` is the sum over the
vertices `j ≤ i` of `σ` of the number of entries equal to `j`. -/
private theorem card_filter_le_eq_sum_card_filter_eq {σ : Finset ι} {u : Fin k → ι}
    (hu : ∀ l, u l ∈ σ) (i : σ) :
    #{l | u l ≤ i.1} = ∑ j ∈ ({j | j ≤ i} : Finset σ), #{l | u l = j.1} := by
  rw [card_eq_sum_card_fiberwise (f := fun l => (⟨u l, hu l⟩ : σ)) (t := {j | j ≤ i})
    fun l hl => by simpa [← Subtype.coe_le_coe] using hl]
  refine sum_congr rfl fun j hj => ?_
  rw [filter_filter]
  congr 1
  ext l
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  exact ⟨fun h => congrArg Subtype.val h.2, fun h => ⟨h ▸ hj, Subtype.ext h⟩⟩

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
    · obtain ⟨j, hj⟩ := exists_card_filter_lt_card_filter h hne'
      exact hj.ne (congrFun hab ⟨a.1.1 j, hσ a.1 a.2 j⟩).symm
    · obtain ⟨j, hj⟩ := exists_card_filter_lt_card_filter h hne'.symm
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
