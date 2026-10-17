/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Analysis.Convex.Gauge
import Mathlib.Algebra.Order.Round
import Mathlib.Analysis.LocallyConvex.Basic
import Mathlib.LinearAlgebra.Basis.Fin
import TauCeti.Algebra.Module.ZLattice.Rank
import TauCeti.LinearAlgebra.FreeModule.RankOneExtension

/-!
# A lattice basis of controlled gauge from an independent family

Let `L` be a discrete `ℤ`-submodule of a finite-dimensional real normed space `E`, let `B` be a
convex, symmetric, absorbent subset of `E`, and let `a 0, …, a (n - 1)` be `ℝ`-linearly
independent vectors of `L` with `n = finrank ℝ E`. The vectors `a i` need not be a `ℤ`-basis of
`L`, but some `ℤ`-basis `b` of `L` is almost as short, measured by the gauge of `B`:
`gauge B (b j) ≤ max (gauge B (a j)) ((∑ i ≤ j, gauge B (a i)) / 2)` for every `j`.

Applied to a family of vectors realizing the successive minima `λ 0 ≤ λ 1 ≤ ⋯` of `L` with
respect to a closed convex body, this gives the lattice basis from the successive minima: its
`i`-th member (indices from `0`) lies in `max 1 ((i + 1) / 2) · λ i` times the body. Against
Minkowski's second theorem this costs the factor
`∏ i < n, max 1 ((i + 1) / 2) = n! / 2 ^ (n - 1)` (`TauCeti.prod_max_one_add_one_div_two`).

## Main results

* `ZLattice.exists_basis_gauge_le`: the basis of controlled gauge.

## Implementation notes

The basis is built one vector at a time along the flag
`L ∩ span ℝ {a i | i < j}`, `j = 0, …, n`. Each step of the flag is saturated in the next, and its
`ℤ`-rank is `j` because `L` is discrete (`TauCeti.discreteTopology_iff_finrank_eq_finrank_span`),
so a single vector `y` extends a basis of one step to a basis of the next
(`Submodule.exists_extending_of_finrank_eq_add_one`, `Module.Basis.mkFinSnocOfLE`). The vector
`y` matters only modulo the smaller step, and `a j + c • y` lies in the smaller step for a
nonzero integer `c`. If `|c| = 1`, take `-c • a j`. If `|c| ≥ 2`, then
`y = -c⁻¹ • a j + ∑ i < j, t i • a i` for real `t i`, and rounding each `t i` to an integer moves
`y` within its class to a vector of gauge at most `(∑ i ≤ j, gauge B (a i)) / 2`.

The body enters only through its gauge, which is subadditive for a convex absorbent set
(`gauge_add_le`) and absolutely homogeneous for a balanced one (`gauge_smul`); a convex set is
balanced over `ℝ` exactly when it is symmetric (`balanced_iff_neg_mem`). No measure, closedness or
boundedness of `B` is used. A convex symmetric set with `0` in its interior is absorbent by
`absorbent_nhds_zero`.

## References

* J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Springer, 1959: Chapter I,
  Theorem I (bases adapted to a flag), and Chapter V, Lemma 8 (the basis from the minima).
* Y. Bugeaud and K. Győry, *Bounds for the solutions of unit equations*, Acta Arith. **74**
  (1996), 67–80, §3.

The construction and its proof are adapted from the Apache-2.0 formalization in
`rwst/Subspace-Theorems` (files `ArithmeticHeights/AdaptedBasis.lean` and
`ArithmeticHeights/MinimaBasis.lean`), by Ralf Stephan.
-/

public section

open Module Submodule

namespace ZLattice

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `j`-th step `L ∩ span ℝ {a i | i < j}` of the flag of a family `a`. -/
private def flag {n : ℕ} (L : Submodule ℤ E) (a : Fin n → E) (j : ℕ) : Submodule ℤ E :=
  L ⊓ (span ℝ (a '' {i | (i : ℕ) < j})).restrictScalars ℤ

private theorem mem_flag {n : ℕ} {L : Submodule ℤ E} {a : Fin n → E} {j : ℕ} {x : E} :
    x ∈ flag L a j ↔ x ∈ L ∧ x ∈ span ℝ (a '' {i | (i : ℕ) < j}) :=
  Iff.rfl

private theorem flag_mono {n : ℕ} (L : Submodule ℤ E) (a : Fin n → E) {j k : ℕ} (hjk : j ≤ k) :
    flag L a j ≤ flag L a k := fun _ hx ↦
  ⟨hx.1, span_mono (Set.image_mono fun _ hi ↦ lt_of_lt_of_le hi hjk) hx.2⟩

private theorem apply_mem_flag {n : ℕ} {L : Submodule ℤ E} {a : Fin n → E} (haL : ∀ i, a i ∈ L)
    {i : Fin n} {j : ℕ} (hij : (i : ℕ) < j) : a i ∈ flag L a j :=
  ⟨haL i, subset_span ⟨i, hij, rfl⟩⟩

private theorem discreteTopology_flag {n : ℕ} (L : Submodule ℤ E) [DiscreteTopology L]
    (a : Fin n → E) (j : ℕ) : DiscreteTopology (flag L a j) :=
  DiscreteTopology.of_continuous_injective (f := inclusion (inf_le_left : flag L a j ≤ L))
    (continuous_inclusion inf_le_left) (inclusion_injective _)

/-- A lattice point a nonzero integer multiple of which lies in a step of the flag lies in that
step: the step is cut out by an `ℝ`-subspace. -/
private theorem mem_flag_of_smul_mem {n : ℕ} {L : Submodule ℤ E} {a : Fin n → E} {j : ℕ}
    {c : ℤ} (hc : c ≠ 0) {z : E} (hz : z ∈ L) (hcz : c • z ∈ flag L a j) : z ∈ flag L a j := by
  refine ⟨hz, ?_⟩
  have h := (mem_flag.1 hcz).2
  rw [← Int.cast_smul_eq_zsmul ℝ] at h
  simpa [smul_smul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hc : (c : ℝ) ≠ 0)] using
    smul_mem _ ((c : ℝ)⁻¹) h

/-- For an independent family of lattice vectors, the `j`-th step of the flag has `ℤ`-rank `j`.
This is where the discreteness of `L` enters. -/
private theorem finrank_flag [FiniteDimensional ℝ E] {n : ℕ} (L : Submodule ℤ E)
    [DiscreteTopology L] {a : Fin n → E} (haL : ∀ i, a i ∈ L) (ha : LinearIndependent ℝ a)
    {j : ℕ} (hj : j ≤ n) : finrank ℤ (flag L a j) = j := by
  have := discreteTopology_flag L a j
  have hspan : span ℝ (flag L a j : Set E) = span ℝ (a '' {i | (i : ℕ) < j}) :=
    le_antisymm (span_le.2 fun _ hx ↦ hx.2)
      (span_le.2 <| by rintro _ ⟨i, hi, rfl⟩; exact subset_span (apply_mem_flag haL hi))
  have hrange : a '' {i | (i : ℕ) < j} = Set.range (a ∘ Fin.castLE hj) := by
    rw [Set.range_comp, Fin.range_castLE]
  rw [TauCeti.discreteTopology_iff_finrank_eq_finrank_span.1 ‹_›, hspan, hrange,
    finrank_span_eq_card (ha.comp _ (Fin.castLE_injective hj)), Fintype.card_fin]

/-- The last step of the flag of a spanning family is the whole lattice. -/
private theorem flag_eq_self [FiniteDimensional ℝ E] {n : ℕ} (L : Submodule ℤ E) {a : Fin n → E}
    (hn : n = finrank ℝ E) (ha : LinearIndependent ℝ a) : flag L a n = L := by
  have htop : span ℝ (a '' {i | (i : ℕ) < n}) = ⊤ := by
    simpa using ha.span_eq_top_of_card_eq_finrank' (by simp [hn])
  rw [flag, htop, restrictScalars_top, inf_top_eq]

/-- **The extension step.** If `a k + c • y` lies in the `k`-th step of the flag, then some
translate of `y` by that step has gauge at most
`max (gauge B (a k)) ((∑ i ≤ k, gauge B (a i)) / 2)`. -/
private theorem exists_sub_mem_flag_gauge_le {n : ℕ} {L : Submodule ℤ E} {B : Set E}
    (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : Absorbent ℝ B) {a : Fin n → E}
    (haL : ∀ i, a i ∈ L) (ha : LinearIndependent ℝ a) (k : Fin n) {y : E} {c : ℤ}
    (hc : a k + c • y ∈ flag L a k) :
    ∃ y' : E, y' - y ∈ flag L a k ∧
      gauge B y' ≤ max (gauge B (a k)) ((∑ i ∈ Finset.Iic k, gauge B (a i)) / 2) := by
  classical
  have hbal : Balanced ℝ B := (balanced_iff_neg_mem hB₀).2 hB₁
  have hc₀ : c ≠ 0 := by
    rintro rfl
    exact ha.notMem_span_image (s := {i | (i : ℕ) < k}) (lt_irrefl (k : ℕ))
      (by simpa using (mem_flag.1 hc).2)
  have hgsmul : ∀ (r : ℝ) (x : E), gauge B (r • x) = |r| * gauge B x := fun r x ↦ by
    rw [gauge_smul hbal, Real.norm_eq_abs]
  by_cases hunit : |c| = 1
  · -- `a k = -c • y` modulo the flag, so `-c • a k` is admissible.
    refine ⟨-c • a k, ?_, ?_⟩
    · have hcc : -c * c = -1 := by
        rcases abs_eq (zero_le_one' ℤ) |>.1 hunit with h | h <;> simp [h]
      have : -c • a k - y = -c • (a k + c • y) := by
        rw [smul_add, smul_smul, hcc, neg_one_smul]
        abel
      rw [this]
      exact smul_mem _ _ hc
    · rw [← Int.cast_smul_eq_zsmul ℝ, hgsmul, Int.cast_neg, abs_neg, ← Int.cast_abs, hunit,
        Int.cast_one, one_mul]
      exact le_max_left _ _
  · -- Otherwise `y = -c⁻¹ • a k + ∑ i < k, t i • a i`; round the coefficients `t i`.
    have hc₂ : (2 : ℝ) ≤ |(c : ℝ)| := by
      rw [← Int.cast_abs]
      have := abs_pos.2 hc₀
      exact_mod_cast (by omega : (2 : ℤ) ≤ |c|)
    obtain ⟨l, hl, hlc⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).1 (mem_flag.1 hc).2
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ fun i ↦ zero_smul ℝ (a i)] at hlc
    have hl₀ : ∀ i, ¬ i < k → l i = 0 := fun i hi ↦ (Finsupp.mem_supported' ℝ l).1 hl i hi
    set t : Fin n → ℝ := fun i ↦ (c : ℝ)⁻¹ * l i
    have ht₀ : ∀ i, ¬ i < k → t i = 0 := fun i hi ↦ by simp [t, hl₀ i hi]
    have hcR : (c : ℝ) ≠ 0 := Int.cast_ne_zero.2 hc₀
    have hy : y = -(c : ℝ)⁻¹ • a k + ∑ i, t i • a i := by
      have h : (c : ℝ) • y = ∑ i, l i • a i - a k := by
        rw [Int.cast_smul_eq_zsmul, hlc]
        abel
      calc y = (c : ℝ)⁻¹ • ((c : ℝ) • y) := by rw [smul_smul, inv_mul_cancel₀ hcR, one_smul]
        _ = _ := by simp [h, t, Finset.smul_sum, smul_smul, sub_eq_neg_add]
    refine ⟨y - ∑ i, round (t i) • a i, ?_, ?_⟩
    · rw [sub_sub_cancel_left]
      refine neg_mem (sum_mem fun i _ ↦ ?_)
      by_cases hi : i < k
      · exact smul_mem _ _ (apply_mem_flag haL hi)
      · simp [ht₀ i hi]
    · have hy' : y - ∑ i, round (t i) • a i =
          -(c : ℝ)⁻¹ • a k + ∑ i, (t i - round (t i)) • a i := by
        simp only [hy, sub_smul, Finset.sum_sub_distrib, Int.cast_smul_eq_zsmul]
        abel
      have hsum : ∑ i, gauge B ((t i - round (t i)) • a i) ≤
          ∑ i ∈ Finset.Iio k, gauge B (a i) / 2 := by
        rw [← Finset.sum_subset (Finset.subset_univ (Finset.Iio k)) fun i _ hi ↦ by
          simp [ht₀ i (by simpa using hi)]]
        refine Finset.sum_le_sum fun i _ ↦ ?_
        rw [hgsmul]
        nlinarith [abs_sub_round (t i), gauge_nonneg (s := B) (a i)]
      have hfirst : gauge B (-(c : ℝ)⁻¹ • a k) ≤ gauge B (a k) / 2 := by
        rw [hgsmul, abs_neg, abs_inv]
        nlinarith [inv_anti₀ two_pos hc₂, gauge_nonneg (s := B) (a k)]
      calc gauge B (y - ∑ i, round (t i) • a i)
          ≤ gauge B (-(c : ℝ)⁻¹ • a k) + ∑ i, gauge B ((t i - round (t i)) • a i) := by
            rw [hy']
            exact (gauge_add_le hB₀ hB₂ _ _).trans
              (add_le_add_right (gauge_sum_le hB₀ hB₂ _ _) _)
        _ ≤ (∑ i ∈ Finset.Iic k, gauge B (a i)) / 2 := by
            rw [Finset.Iic_eq_cons_Iio, Finset.sum_cons, add_div, Finset.sum_div]
            exact add_le_add hfirst hsum
        _ ≤ _ := le_max_right _ _

/-- **A lattice basis of controlled gauge.** Let `L` be a discrete `ℤ`-submodule of a
finite-dimensional real normed space `E`, and `B` a convex, symmetric, absorbent subset of `E`.
For `ℝ`-linearly independent vectors `a 0, …, a (n - 1)` of `L` with `n = finrank ℝ E`, there is
a `ℤ`-basis `b` of `L` with
`gauge B (b j) ≤ max (gauge B (a j)) ((∑ i ≤ j, gauge B (a i)) / 2)` for every `j`.

The family `a` need not be a basis of `L`, and `L` is not assumed to be a full lattice: that
follows from the hypotheses on `a`. This is the form of Cassels' Chapter V, Lemma 8 which does not
mention successive minima. -/
theorem exists_basis_gauge_le [FiniteDimensional ℝ E] (L : Submodule ℤ E) [DiscreteTopology L]
    {B : Set E} (hB₀ : Convex ℝ B) (hB₁ : ∀ x ∈ B, -x ∈ B) (hB₂ : Absorbent ℝ B) {n : ℕ}
    (hn : n = finrank ℝ E) {a : Fin n → E} (haL : ∀ i, a i ∈ L) (ha : LinearIndependent ℝ a) :
    ∃ b : Basis (Fin n) ℤ L, ∀ j : Fin n,
      gauge B (b j : E) ≤ max (gauge B (a j)) ((∑ i ∈ Finset.Iic j, gauge B (a i)) / 2) := by
  set β : Fin n → ℝ := fun j ↦ max (gauge B (a j)) ((∑ i ∈ Finset.Iic j, gauge B (a i)) / 2)
  -- Build a basis of each step of the flag, one vector at a time.
  have key : ∀ j (hj : j ≤ n), ∃ b : Basis (Fin j) ℤ (flag L a j), ∀ k : Fin j,
      gauge B (b k : E) ≤ β (Fin.castLE hj k) := by
    intro j
    induction j with
    | zero =>
      intro _
      have : Subsingleton (flag L a 0) := by
        rw [subsingleton_iff_eq_bot]
        ext x
        simp +contextual [mem_flag]
      exact ⟨Basis.empty _, fun k ↦ k.elim0⟩
    | succ j ih =>
      intro hj
      obtain ⟨b, hb⟩ := ih (Nat.le_of_succ_le hj)
      have hmono := flag_mono L a (Nat.le_succ j)
      have := discreteTopology_flag L a (j + 1)
      obtain ⟨y, hyN, hy⟩ := exists_extending_of_finrank_eq_add_one hmono
        (fun c hc z hz hcz ↦ mem_flag_of_smul_mem hc hz.1 hcz)
        (by rw [finrank_flag L haL ha hj, finrank_flag L haL ha (Nat.le_of_succ_le hj)])
      set k : Fin n := ⟨j, hj⟩
      obtain ⟨c, hc⟩ := (hy y (by simp)).2 (a k) (apply_mem_flag haL (Nat.lt_succ_self j))
      obtain ⟨y', hy'y, hy'⟩ := exists_sub_mem_flag_gauge_le hB₀ hB₁ hB₂ haL ha k hc
      have hy'N : y' ∈ flag L a (j + 1) := by
        simpa using add_mem hyN (hmono hy'y)
      obtain ⟨hli, hsp⟩ := hy y' hy'y
      refine ⟨Basis.mkFinSnocOfLE b hmono y' hy'N hli hsp, Fin.lastCases ?_ fun k' ↦ ?_⟩
      · have hlast : (Basis.mkFinSnocOfLE b hmono y' hy'N hli hsp (Fin.last j) : E) = y' := by
          simp
        rw [hlast]
        exact hy'
      · have hcast : (Basis.mkFinSnocOfLE b hmono y' hy'N hli hsp k'.castSucc : E) = b k' := by
          simp
        rw [hcast]
        exact hb k'
  obtain ⟨b, hb⟩ := key n le_rfl
  refine ⟨b.map (LinearEquiv.ofEq _ _ (flag_eq_self L hn ha)), fun j ↦ ?_⟩
  have hmap : (b.map (LinearEquiv.ofEq _ _ (flag_eq_self L hn ha)) j : E) = b j := by simp
  rw [hmap]
  exact hb j

end ZLattice
