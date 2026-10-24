/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.SaturatedModule
public import TauCeti.Topology.Algebra.Valued.Integer
public import TauCeti.Topology.MetricSpace.SphericallyComplete

import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Saturated lattices over a nonarchimedean field

Let `K` be a nontrivially normed field with an ultrametric norm, with valuation ring `𝒪[K]` (the
closed unit ball) and maximal ideal `𝓂[K]` (the open unit ball). This file relates the
`𝓂[K]`-saturation of `TauCeti.IsValuationSaturated` to the metric structure of `K`.

Bounded `𝒪[K]`-submodules of `ι → K` are transported along `𝒪[K]`-linear equivalences by
`LinearEquiv.isBounded_image_iff_of_integer`, and saturation by
`TauCeti.isValuationSaturated_congr`.

If the norm of `K` is dense, for instance if its value group is all of `ℝ_{>0}`, the maximal
ideal `𝓂[K]` is not finitely generated, so `𝒪[K]` and every principal lattice `a • 𝒪[K]` in `K`
are `𝓂[K]`-saturated. For a discretely valued field such as `ℚ_p` this fails: `ℤ_p` is not
saturated with respect to its maximal ideal `p ℤ_p`.

Conversely, if `K` is spherically complete and its norm takes every positive real value, every
bounded `𝓂[K]`-saturated `𝒪[K]`-submodule of `K^r` is free of rank at most `r` (Bhatt–Scholze,
Lemma 6.14). In rank one a bounded submodule of `K` is a closed or an open ball about `0`;
saturation excludes the open ball, and the value-group hypothesis makes the closed ball
principal. In general, the part of the lattice on which one coordinate vanishes is again
saturated, hence free by induction, and spherical completeness shows that the image of that
coordinate is saturated, hence principal, so that the lattice is an extension of free modules.
Without the value-group hypothesis the statement fails: if `‖K^×‖` is dense but not all of
`ℝ_{>0}`, a closed ball whose radius is not a norm is saturated but not finitely generated.

## Main results

* `TauCeti.isValuationSaturated_integer`, `TauCeti.isValuationSaturated_integer_span_singleton`:
  for a densely normed field, `𝒪[K]` and every principal lattice `a • 𝒪[K]` in `K` are
  `𝓂[K]`-saturated.
* `TauCeti.not_isValuationSaturated_maximalIdeal_integer`: the open unit ball `𝓂[K]` is not
  `𝓂[K]`-saturated.
* `TauCeti.exists_eq_span_singleton_of_isValuationSaturated`: if the norm of `K` takes every
  positive real value, a bounded saturated submodule of `K` is a principal lattice.
* `TauCeti.IsValuationSaturated.exists_add_sum_smul_mem`: over a spherically complete field, a
  saturated lattice can be extended across a free sublattice.
* `TauCeti.exists_basis_of_isValuationSaturated`: over a spherically complete field whose norm
  takes every positive real value, a bounded saturated submodule of `ι → K` has a finite basis
  of cardinality at most that of `ι`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Lemma 6.14.
-/

public section

open IsLocalRing Metric
open scoped NormedField

namespace TauCeti

/-- Over a nontrivially normed nonarchimedean field, the open unit ball `𝓂[K]` is not saturated
with respect to itself. -/
theorem not_isValuationSaturated_maximalIdeal_integer {K : Type*} [NontriviallyNormedField K]
    [IsUltrametricDist K] :
    ¬ IsValuationSaturated (Valued.integer K) (maximalIdeal (Valued.integer K))
      (maximalIdeal (Valued.integer K)) := by
  refine not_isValuationSaturated_ideal_ideal (fun h ↦ ?_) (maximalIdeal.isMaximal _).ne_top
  obtain ⟨x, hx0, hx1⟩ := Valued.integer.exists_norm_lt_one (K := K)
  have hx : x ∈ maximalIdeal (Valued.integer K) := Valued.integer.mem_maximalIdeal_iff.2 hx1
  rw [h, Ideal.mem_bot] at hx
  simp [hx] at hx0

section DenselyNormed

variable {K : Type*} [DenselyNormedField K] [IsUltrametricDist K]

/-- Over a densely normed nonarchimedean field `K`, the valuation ring `𝒪[K]` is saturated with
respect to its maximal ideal. -/
theorem isValuationSaturated_integer :
    IsValuationSaturated (Valued.integer K) (maximalIdeal (Valued.integer K)) (Valued.integer K) :=
  isValuationSaturated_maximalIdeal_self not_fg_maximalIdeal_integer

/-- Over a densely normed nonarchimedean field `K`, every principal lattice `a • 𝒪[K]` in `K`,
including `a = 0`, is saturated with respect to the maximal ideal of `𝒪[K]`. -/
theorem isValuationSaturated_integer_span_singleton (a : K) :
    IsValuationSaturated (Valued.integer K) (maximalIdeal (Valued.integer K))
      (Valued.integer K ∙ a) :=
  isValuationSaturated_span_singleton not_fg_maximalIdeal_integer a

end DenselyNormed

/-- The ring `ℤ_[p]` of `p`-adic integers is not saturated with respect to its maximal ideal
`p ℤ_[p]`, since that ideal is finitely generated. -/
example (p : ℕ) [Fact p.Prime] :
    ¬ IsValuationSaturated ℤ_[p] (maximalIdeal ℤ_[p]) ℤ_[p] := fun h ↦
  isValuationSaturated_maximalIdeal_self_iff.1 h (IsNoetherian.noetherian _)

section Lattice

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

local notation "𝒪K" => Valued.integer K

/-- The action of `𝒪[K]` on a `K`-module is the restriction of the `K`-action. -/
private theorem integer_smul_eq {E : Type*} [AddCommGroup E] [Module K E] [Module 𝒪K E]
    [IsScalarTower 𝒪K K E] (c : 𝒪K) (v : E) : c • v = (c : K) • v :=
  (algebraMap_smul K c v).symm

/-- Every `𝒪[K]`-linear map from the maximal ideal `𝓂[K]` to `K` is multiplication by an element
of `K`. -/
private theorem exists_eq_mul_of_linearMap_maximalIdeal (f : maximalIdeal 𝒪K →ₗ[𝒪K] K) :
    ∃ q : K, ∀ c : maximalIdeal 𝒪K, f c = ((c : 𝒪K) : K) * q := by
  obtain ⟨a, ha0, ha1⟩ := Valued.integer.exists_norm_coe_lt_one (K := K)
  have ham : a ∈ maximalIdeal 𝒪K := Valued.integer.mem_maximalIdeal_iff.2 ha1
  refine ⟨f ⟨a, ham⟩ / a, fun c ↦ ?_⟩
  -- `f` is linear, so `a * f c = f (a * c) = c * f a`.
  have h : (a : K) * f c = (c : K) * f ⟨a, ham⟩ := by
    rw [← smul_eq_mul, ← integer_smul_eq, ← map_smul, ← smul_eq_mul ((c : 𝒪K) : K),
      ← integer_smul_eq, ← map_smul]
    congr 1
    exact Subtype.ext (mul_comm _ _)
  field_simp [norm_pos_iff.1 ha0]
  linear_combination h

/-- **Bounded saturated lattices of rank one are principal.** Let `K` be a nonarchimedean field
whose norm takes every positive real value. A bounded `𝒪[K]`-submodule of `K` which is
`𝓂[K]`-saturated is a principal lattice `a • 𝒪[K]`, possibly with `a = 0`. -/
theorem exists_eq_span_singleton_of_isValuationSaturated
    (hK : ∀ r : ℝ, 0 < r → ∃ x : K, ‖x‖ = r) {M : Submodule 𝒪K K}
    (hb : Bornology.IsBounded (M : Set K))
    (hM : IsValuationSaturated 𝒪K (maximalIdeal 𝒪K) M) : ∃ a : K, M = 𝒪K ∙ a := by
  by_cases hmax : ∃ x ∈ M, ∀ y ∈ M, ‖y‖ ≤ ‖x‖
  · obtain ⟨x, hx, hxmax⟩ := hmax
    exact ⟨x, le_antisymm (fun y hy ↦ Valued.integer.submodule_mem_of_norm_le
      (Submodule.mem_span_singleton_self x) (hxmax y hy))
      ((Submodule.span_singleton_le_iff_mem x M).2 hx)⟩
  -- Otherwise `M` is the open ball of radius `s = sup ‖M‖`, isomorphic to `𝓂[K]`.
  push Not at hmax
  exfalso
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.1 hb
  have hne : (norm '' (M : Set K)).Nonempty := ⟨‖(0 : K)‖, 0, M.zero_mem, rfl⟩
  have hbdd : BddAbove (norm '' (M : Set K)) := ⟨C, by rintro _ ⟨x, hx, rfl⟩; exact hC x hx⟩
  set s := sSup (norm '' (M : Set K))
  have hle {y : K} (hy : y ∈ M) : ‖y‖ ≤ s := le_csSup hbdd ⟨y, hy, rfl⟩
  have hlt {y : K} (hy : y ∈ M) : ‖y‖ < s := by
    obtain ⟨y', hy', hyy'⟩ := hmax y hy
    exact hyy'.trans_le (hle hy')
  have hs : 0 < s := by simpa using hlt M.zero_mem
  obtain ⟨a, ha⟩ := hK s hs
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp [← ha] at hs
  have hmem (b : maximalIdeal 𝒪K) : (b : 𝒪K) • a ∈ M := by
    have hb1 : ‖((b : 𝒪K) : K)‖ < 1 := Valued.integer.mem_maximalIdeal_iff.1 b.2
    have hlt' : ‖(b : 𝒪K) • a‖ < s := by
      rw [integer_smul_eq, norm_smul, ha]
      exact mul_lt_of_lt_one_left hs hb1
    obtain ⟨_, ⟨y, hy, rfl⟩, hyb⟩ := exists_lt_of_lt_csSup hne hlt'
    exact Valued.integer.submodule_mem_of_norm_le hy hyb.le
  let f : maximalIdeal 𝒪K →ₗ[𝒪K] M :=
    LinearMap.codRestrict M ((LinearMap.toSpanSingleton 𝒪K K a).comp (maximalIdeal 𝒪K).subtype)
      hmem
  -- By definition `f b = b • a`.
  have hfa (b : maximalIdeal 𝒪K) : (f b : K) = ((b : 𝒪K) : K) * a := integer_smul_eq (b : 𝒪K) a
  have hf : Function.Bijective f := by
    refine ⟨fun b c hbc ↦ ?_, fun y ↦ ?_⟩
    · have h := congrArg Subtype.val hbc
      rw [hfa, hfa] at h
      exact Subtype.ext (Subtype.ext (mul_right_cancel₀ ha0 h))
    · have hy1 : ‖(y : K) / a‖ < 1 := by
        rw [norm_div, ha, div_lt_one hs]
        exact hlt y.2
      refine ⟨⟨⟨y / a, Valued.integer.mem_iff.2 hy1.le⟩,
        Valued.integer.mem_maximalIdeal_iff.2 hy1⟩, Subtype.ext ?_⟩
      rw [hfa]
      exact div_mul_cancel₀ _ ha0
  exact not_isValuationSaturated_maximalIdeal_integer
    ((isValuationSaturated_congr (LinearEquiv.ofBijective f hf)).2 hM)

end Lattice

section SphericallyComplete

/-- In a spherically complete ultrametric space `X`, let `A n` be sets of families `ι → X` such
that `A n` contains the closed polydisc of radius `r n` about each of its points, and every point
of `A n` is within `r n` of some point of `A (n + 1)`. If the radii decrease and `A 0` is
nonempty, the sets `A n` have a common point. -/
private theorem exists_forall_mem_of_closedBall {X ι : Type*} [PseudoMetricSpace X]
    [IsUltrametricDist X] [SphericallyCompleteSpace X] {A : ℕ → Set (ι → X)} {r : ℕ → ℝ}
    (hr : Antitone r) (hr0 : ∀ n, 0 ≤ r n) (h0 : (A 0).Nonempty)
    (hstep : ∀ n, ∀ c ∈ A n, ∃ c' ∈ A (n + 1), ∀ i, dist (c' i) (c i) ≤ r n)
    (hball : ∀ n, ∀ c ∈ A n, ∀ t : ι → X, (∀ i, dist (t i) (c i) ≤ r n) → t ∈ A n) :
    ∃ t : ι → X, ∀ n, t ∈ A n := by
  choose! g hgA hg using hstep
  obtain ⟨c₀, hc₀⟩ := h0
  -- The centres `c n ∈ A n`, defined recursively by `c (n + 1) = g n (c n)`.
  let c : ℕ → ι → X := fun n ↦ Nat.rec c₀ g n
  have hcA (n : ℕ) : c n ∈ A n := by
    induction n with
    | zero => exact hc₀
    | succ n ih => exact hgA n (c n) ih
  have hball' (i : ι) : (⋂ n, closedBall (c n i) (r n)).Nonempty := by
    refine SphericallyCompleteSpace.nonempty_iInter_closedBall hr0
      (antitone_nat_of_succ_le fun n ↦ ?_)
    have hmem : c (n + 1) i ∈ closedBall (c n i) (r n) := hg n (c n) (hcA n) i
    rw [IsUltrametricDist.closedBall_eq_of_mem hmem]
    exact closedBall_subset_closedBall (hr n.le_succ)
  choose t ht using hball'
  exact ⟨t, fun n ↦ hball n (c n) (hcA n) t fun i ↦ Set.mem_iInter.1 (ht i) n⟩

variable {K : Type*} [DenselyNormedField K] [IsUltrametricDist K]

local notation "𝒪K" => Valued.integer K

/-- Over a densely normed field, the maximal ideal of `𝒪[K]` contains a sequence of nonzero
elements of increasing norm which is cofinal for the norm. -/
private theorem exists_seq_mem_maximalIdeal :
    ∃ a : ℕ → 𝒪K, (∀ n, (a n : K) ≠ 0) ∧ (∀ n, a n ∈ maximalIdeal 𝒪K) ∧
      Monotone (fun n ↦ ‖(a n : K)‖) ∧
      ∀ b ∈ maximalIdeal 𝒪K, ∃ n, ‖(b : K)‖ ≤ ‖(a n : K)‖ := by
  set S := (fun x : K ↦ ‖x‖) '' {x | 0 < ‖x‖ ∧ ‖x‖ < 1}
  obtain ⟨x₀, hx₀⟩ := NormedField.exists_lt_norm_lt K le_rfl zero_lt_one
  have hS1 : ∀ y ∈ S, y ≤ 1 := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2.le
  have hne : S.Nonempty := ⟨_, x₀, hx₀, rfl⟩
  have hsup : sSup S = 1 := by
    refine csSup_eq_of_forall_le_of_forall_lt_exists_gt hne hS1 fun w hw ↦ ?_
    obtain ⟨x, hx1, hx2⟩ :=
      NormedField.exists_lt_norm_lt K (le_max_right w 0) (max_lt hw zero_lt_one)
    exact ⟨‖x‖, ⟨x, ⟨(le_max_right w 0).trans_lt hx1, hx2⟩, rfl⟩, (le_max_left w 0).trans_lt hx1⟩
  obtain ⟨u, hu, hlim, huS⟩ := exists_seq_tendsto_sSup hne ⟨1, hS1⟩
  choose x hx hxu using huS
  simp only at hxu
  refine ⟨fun n ↦ ⟨x n, Valued.integer.mem_iff.2 (hx n).2.le⟩, fun n ↦ norm_pos_iff.1 (hx n).1,
    fun n ↦ Valued.integer.mem_maximalIdeal_iff.2 (hx n).2, fun m n hmn ↦ ?_, fun b hb ↦ ?_⟩
  · simpa [hxu] using hu hmn
  · rw [hsup] at hlim
    obtain ⟨n, hn⟩ :=
      ((tendsto_order.1 hlim).1 _ (Valued.integer.mem_maximalIdeal_iff.1 hb)).exists
    exact ⟨n, hn.le.trans_eq (hxu n).symm⟩

variable [SphericallyCompleteSpace K] {E : Type*} [AddCommGroup E] [Module K E]
  [Module (Valued.integer K) E] [IsScalarTower (Valued.integer K) K E]

/-- **Extension across a free sublattice.** Let `K` be a densely normed, spherically complete
nonarchimedean field and `M` an `𝓂[K]`-saturated `𝒪[K]`-submodule of a `K`-vector space `E`. Let
`e` be a finite family in `M` such that every `K`-linear combination of `e` lying in `M` is an
`𝒪[K]`-linear combination. If `a • z` lies in `M + K e` for every `a ∈ 𝓂[K]`, then so does `z`.
This expresses the vanishing of `Ext¹(𝓂[K], 𝒪[K]ⁿ)` in the form used to split a saturated
lattice along a free sublattice. -/
theorem IsValuationSaturated.exists_add_sum_smul_mem {M : Submodule 𝒪K E}
    (hM : IsValuationSaturated 𝒪K (maximalIdeal 𝒪K) M) {ι : Type*} [Fintype ι] {e : ι → E}
    (he : ∀ i, e i ∈ M)
    (hspan : ∀ t : ι → K, ∑ i, t i • e i ∈ M → ∃ s : ι → 𝒪K, ∑ i, t i • e i = ∑ i, s i • e i)
    {z : E} (hz : ∀ a ∈ maximalIdeal 𝒪K, ∃ t : ι → K, a • z + ∑ i, t i • e i ∈ M) :
    ∃ t : ι → K, z + ∑ i, t i • e i ∈ M := by
  -- Choose `a n ∈ 𝓂[K]` with `‖a n‖` increasing to `1`. The coefficient families `t` with
  -- `a n • (z + ∑ i, t i • e i) ∈ M` form decreasing unions of polydiscs of radius `‖a n‖⁻¹`;
  -- spherical completeness gives a common `t`, and saturation puts `z + ∑ i, t i • e i` in `M`.
  obtain ⟨a, ha0, ham, hmono, hcof⟩ := exists_seq_mem_maximalIdeal (K := K)
  -- `A n` is the set of coefficient families `t` with `a n • (z + ∑ i, t i • e i) ∈ M`; it is a
  -- union of closed polydiscs of radius `‖a n‖⁻¹`, and the sets `A n` decrease.
  let A : ℕ → Set (ι → K) := fun n ↦ {t | a n • (z + ∑ i, t i • e i) ∈ M}
  have hA (n : ℕ) (t : ι → K) :
      t ∈ A n ↔ (a n : K) • z + ∑ i, ((a n : K) * t i) • e i ∈ M := by
    simp [A, integer_smul_eq, smul_add, Finset.smul_sum, smul_smul]
  have hA_succ (n : ℕ) : A (n + 1) ⊆ A n := by
    intro t ht
    obtain ⟨c, hc⟩ := Valued.integer.dvd_of_norm_le (hmono n.le_succ)
    have := M.smul_mem c ht
    rwa [smul_smul, mul_comm, ← hc] at this
  have hA_ne (n : ℕ) : (A n).Nonempty := by
    obtain ⟨t, ht⟩ := hz (a n) (ham n)
    refine ⟨fun i ↦ (a n : K)⁻¹ * t i, (hA n _).2 ?_⟩
    simpa [integer_smul_eq, mul_inv_cancel_left₀ (ha0 n)] using ht
  -- `A n` contains the closed polydisc of radius `‖a n‖⁻¹` about each of its points.
  have hball (n : ℕ) (c : ι → K) (hc : c ∈ A n) (t : ι → K)
      (htc : ∀ i, dist (t i) (c i) ≤ ‖(a n : K)‖⁻¹) : t ∈ A n := by
    have hmem (i : ι) : (a n : K) * (t i - c i) ∈ Valued.integer K := by
      refine Valued.integer.mem_iff.2 ?_
      rw [norm_mul, ← dist_eq_norm]
      calc ‖(a n : K)‖ * dist (t i) (c i) ≤ ‖(a n : K)‖ * ‖(a n : K)‖⁻¹ :=
            mul_le_mul_of_nonneg_left (htc i) (norm_nonneg _)
        _ = 1 := mul_inv_cancel₀ (norm_ne_zero_iff.2 (ha0 n))
    let s : ι → 𝒪K := fun i ↦ ⟨_, hmem i⟩
    have hs (i : ι) : (s i : K) = (a n : K) * (t i - c i) := rfl
    have key : (a n : K) • z + ∑ i, ((a n : K) * t i) • e i =
        ((a n : K) • z + ∑ i, ((a n : K) * c i) • e i) + ∑ i, s i • e i := by
      simp only [integer_smul_eq, hs, add_assoc, ← Finset.sum_add_distrib, ← add_smul]
      congr 2 with i
      module
    rw [hA, key] at *
    exact M.add_mem hc (M.sum_mem fun i _ ↦ M.smul_mem _ (he i))
  -- Every point of `A n` is within `‖a n‖⁻¹` of a point of `A (n + 1)`.
  have hstep (n : ℕ) (c : ι → K) (hc : c ∈ A n) :
      ∃ c' ∈ A (n + 1), ∀ i, dist (c' i) (c i) ≤ ‖(a n : K)‖⁻¹ := by
    obtain ⟨d, hd⟩ := hA_ne (n + 1)
    have hdiff : ∑ i, ((a n : K) * (d i - c i)) • e i ∈ M := by
      have := M.sub_mem ((hA n d).1 (hA_succ n hd)) ((hA n c).1 hc)
      convert this using 1
      simp only [mul_sub, sub_smul, Finset.sum_sub_distrib]
      abel
    obtain ⟨s, hs⟩ := hspan _ hdiff
    have hsum : ∑ i, (c i + (a n : K)⁻¹ * s i) • e i = ∑ i, d i • e i := by
      have h2 := congrArg ((a n : K)⁻¹ • ·) hs
      simp only [Finset.smul_sum, smul_smul, integer_smul_eq, ← mul_assoc,
        inv_mul_cancel₀ (ha0 n), one_mul] at h2
      simp only [add_smul, Finset.sum_add_distrib, ← h2, sub_smul, Finset.sum_sub_distrib]
      abel
    refine ⟨fun i ↦ c i + (a n : K)⁻¹ * s i, ?_, fun i ↦ ?_⟩
    · simpa only [A, Set.mem_ofPred_eq, hsum] using hd
    · rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_inv]
      exact mul_le_of_le_one_right (inv_nonneg.2 (norm_nonneg _)) (Valued.integer.norm_le_one (s i))
  obtain ⟨t, ht⟩ := exists_forall_mem_of_closedBall (A := A) (r := fun n ↦ ‖(a n : K)‖⁻¹)
    (fun m n hmn ↦ inv_anti₀ (norm_pos_iff.2 (ha0 m)) (hmono hmn))
    (fun n ↦ inv_nonneg.2 (norm_nonneg _)) (hA_ne 0) hstep hball
  refine ⟨t, hM.mem_of_forall_smul_mem (ham 0) (fun x y hxy ↦ ?_) fun b hb ↦ ?_⟩
  · -- `a 0` is a nonzero scalar, hence a nonzerodivisor on the `K`-vector space `E`.
    simp only [integer_smul_eq] at hxy
    exact smul_right_injective E (ha0 0) hxy
  · obtain ⟨n, hn⟩ := hcof b hb
    obtain ⟨d, hd⟩ := Valued.integer.dvd_of_norm_le hn
    rw [hd, mul_comm, mul_smul]
    exact M.smul_mem d (ht n)

/-- The image of an `𝓂[K]`-saturated lattice `M ⊆ ι → K` under the `i`-th coordinate is
saturated, provided the sublattice of `M` on which this coordinate vanishes has a finite basis. -/
private theorem isValuationSaturated_map_proj {ι : Type*} {M : Submodule 𝒪K (ι → K)}
    (hM : IsValuationSaturated 𝒪K (maximalIdeal 𝒪K) M) (i : ι) {k : ℕ}
    (b : Module.Basis (Fin k) 𝒪K ↥(M ⊓ LinearMap.ker (LinearMap.proj i))) :
    IsValuationSaturated 𝒪K (maximalIdeal 𝒪K) (M.map (LinearMap.proj i)) := by
  -- Injectivity holds since `K` is torsion-free. A linear map `f : 𝓂[K] → M.map (proj i)` is
  -- multiplication by some `q ∈ K`; lifting each `c • q` to `M` and applying
  -- `IsValuationSaturated.exists_add_sum_smul_mem` to the basis of the kernel part lifts `q`.
  obtain ⟨a, ha0, ha1⟩ := Valued.integer.exists_norm_coe_lt_one (K := K)
  have ham : a ∈ maximalIdeal 𝒪K := Valued.integer.mem_maximalIdeal_iff.2 ha1
  have ha : (a : K) ≠ 0 := norm_pos_iff.1 ha0
  refine isValuationSaturated_def.2
    ⟨valuationSaturationMap_injective_iff.2 fun x hx ↦ ?_, fun f ↦ ?_⟩
  · have h := congrArg Subtype.val (hx a ham)
    rw [Submodule.coe_smul, integer_smul_eq, smul_eq_mul, ZeroMemClass.coe_zero] at h
    exact Subtype.ext ((mul_eq_zero.1 h).resolve_left ha)
  obtain ⟨q, hq⟩ :=
    exists_eq_mul_of_linearMap_maximalIdeal ((M.map (LinearMap.proj i)).subtype ∘ₗ f)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hq
  -- The basis vectors `e j` span the part of `M` on which the `i`-th coordinate vanishes.
  let e : Fin k → ι → K := fun j ↦ (b j : ι → K)
  have he (j : Fin k) : e j ∈ M := (b j).2.1
  have hei (j : Fin k) : e j i = 0 := (b j).2.2
  have hrepr (y : ι → K) (hy : y ∈ M) (hyi : y i = 0) : ∃ s : Fin k → 𝒪K, y = ∑ j, s j • e j :=
    ⟨b.repr ⟨y, hy, hyi⟩, (congrArg Subtype.val (b.sum_repr ⟨y, hy, hyi⟩)).symm.trans
      (by simp only [Submodule.coe_sum, Submodule.coe_smul, e])⟩
  have hspan (t : Fin k → K) (ht : ∑ j, t j • e j ∈ M) :
      ∃ s : Fin k → 𝒪K, ∑ j, t j • e j = ∑ j, s j • e j :=
    hrepr _ ht (by simp [Finset.sum_apply, hei])
  -- A point `z` over `q`: `z = a⁻¹ • m₀` for some `m₀ ∈ M` over `a * q`.
  obtain ⟨m₀, hm₀, hm₀i⟩ := Submodule.mem_map.1 (f ⟨a, ham⟩).2
  rw [hq, LinearMap.proj_apply] at hm₀i
  have hz (c : 𝒪K) (hc : c ∈ maximalIdeal 𝒪K) :
      ∃ t : Fin k → K, c • (a : K)⁻¹ • m₀ + ∑ j, t j • e j ∈ M := by
    rcases le_total ‖(c : K)‖ ‖(a : K)‖ with hle | hle
    · obtain ⟨d, hd⟩ := Valued.integer.dvd_of_norm_le hle
      refine ⟨0, ?_⟩
      have h : c • (a : K)⁻¹ • m₀ = d • m₀ := by
        rw [integer_smul_eq, integer_smul_eq, hd, smul_smul, Subring.coe_mul, mul_right_comm,
          mul_inv_cancel₀ ha, one_mul]
      simpa [h] using M.smul_mem d hm₀
    · have hc0 : (c : K) ≠ 0 := norm_pos_iff.1 (ha0.trans_le hle)
      obtain ⟨d, hd⟩ := Valued.integer.dvd_of_norm_le hle
      have hd' : (d : K) * c = a := by rw [hd, Subring.coe_mul, mul_comm]
      obtain ⟨mc, hmc, hmci⟩ := Submodule.mem_map.1 (f ⟨c, hc⟩).2
      rw [hq, LinearMap.proj_apply] at hmci
      obtain ⟨s, hs⟩ := hrepr (d • mc - m₀) (M.sub_mem (M.smul_mem d hmc) hm₀) (by
        simp [integer_smul_eq, hmci, hm₀i, ← hd', mul_assoc])
      refine ⟨fun j ↦ (c : K) / a * s j, ?_⟩
      have hsum : ∑ j, ((c : K) / a * s j) • e j = ((c : K) / a) • ((d : K) • mc - m₀) := by
        rw [← integer_smul_eq d mc, hs, Finset.smul_sum]
        simp only [smul_smul, integer_smul_eq]
      have hcd : (c : K) / a * d = 1 := by
        rw [← hd', div_mul_eq_mul_div, mul_comm (c : K), div_self (mul_ne_zero
          (fun h ↦ ha (by rw [← hd', h, zero_mul])) hc0)]
      rw [hsum, integer_smul_eq, smul_sub, smul_smul, smul_smul, hcd, one_smul, div_eq_mul_inv,
        add_sub_cancel]
      exact hmc
  obtain ⟨t, ht⟩ := hM.exists_add_sum_smul_mem he hspan hz
  have hqmem : q ∈ M.map (LinearMap.proj i) :=
    Submodule.mem_map.2 ⟨_, ht, by simp [Finset.sum_apply, hei, hm₀i, ha]⟩
  refine ⟨⟨q, hqmem⟩, LinearMap.ext fun c ↦ Subtype.ext ?_⟩
  rw [valuationSaturationMap_apply, Submodule.coe_smul, integer_smul_eq, smul_eq_mul, hq]

end SphericallyComplete

section FiniteFree

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [SphericallyCompleteSpace K]

local notation "𝒪K" => Valued.integer K

/-- **Bounded saturated lattices are finite free** (Bhatt–Scholze, Lemma 6.14). Let `K` be a
spherically complete nonarchimedean field whose norm takes every positive real value. A bounded
`𝒪[K]`-submodule of `ι → K`, `ι` finite, which is `𝓂[K]`-saturated is a free `𝒪[K]`-module of
rank at most the cardinality of `ι`. -/
theorem exists_basis_of_isValuationSaturated (hK : ∀ r : ℝ, 0 < r → ∃ x : K, ‖x‖ = r)
    {ι : Type*} [Fintype ι] {M : Submodule 𝒪K (ι → K)}
    (hb : Bornology.IsBounded (M : Set (ι → K)))
    (hM : IsValuationSaturated 𝒪K (maximalIdeal 𝒪K) M) :
    ∃ k ≤ Fintype.card ι, Nonempty (Module.Basis (Fin k) 𝒪K M) := by
  classical
  -- The value-group hypothesis makes the norm of `K` dense.
  let _ : DenselyNormedField K :=
    { ‹NontriviallyNormedField K› with
      lt_norm_lt := fun r₁ r₂ h₀ hr ↦ by
        obtain ⟨x, hx⟩ := hK ((r₁ + r₂) / 2) (by linarith)
        exact ⟨x, by linarith, by linarith⟩ }
  obtain ⟨a, ha0, ha1⟩ := Valued.integer.exists_norm_coe_lt_one (K := K)
  have ham : a ∈ maximalIdeal 𝒪K := Valued.integer.mem_maximalIdeal_iff.2 ha1
  -- Induct on a finite set `s` of coordinates outside which `M` vanishes.
  suffices h : ∀ s : Finset ι, ∀ M : Submodule 𝒪K (ι → K), (∀ x ∈ M, ∀ j ∉ s, x j = 0) →
      Bornology.IsBounded (M : Set (ι → K)) → IsValuationSaturated 𝒪K (maximalIdeal 𝒪K) M →
      ∃ k ≤ s.card, Nonempty (Module.Basis (Fin k) 𝒪K M) from
    Finset.card_univ (α := ι) ▸ h Finset.univ M (fun _ _ j hj ↦ absurd (Finset.mem_univ j) hj) hb hM
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro M hM0 _ _
    have : Subsingleton M := ⟨fun x y ↦ Subtype.ext (funext fun j ↦ by
      rw [hM0 x x.2 j (Finset.notMem_empty j), hM0 y y.2 j (Finset.notMem_empty j)])⟩
    exact ⟨0, le_rfl, ⟨Module.Basis.empty M⟩⟩
  | insert i s hi ih =>
    intro M hMs hb hM
    -- The part `N` of `M` on which the `i`-th coordinate vanishes is free by induction.
    set N := M ⊓ LinearMap.ker (LinearMap.proj i : (ι → K) →ₗ[𝒪K] K)
    have hNs (x : ι → K) (hx : x ∈ N) (j : ι) (hj : j ∉ s) : x j = 0 := by
      by_cases hji : j = i
      · exact hji ▸ hx.2
      · exact hMs x hx.1 j (by simp [hji, hj])
    have hNsat : IsValuationSaturated 𝒪K (maximalIdeal 𝒪K) N :=
      hM.of_le_of_forall_smul_mem inf_le_left fun x hx hxa ↦ ⟨hx, by
        have h : (a : K) * x i = 0 := by
          simpa [integer_smul_eq] using (hxa a ham).2
        exact (mul_eq_zero.1 h).resolve_left (norm_pos_iff.1 ha0)⟩
    obtain ⟨k, hk, ⟨bN⟩⟩ := ih N hNs (hb.subset inf_le_left) hNsat
    -- The image `Q` of the `i`-th coordinate is a bounded saturated lattice in `K`, so principal.
    have hQb : Bornology.IsBounded ((M.map (LinearMap.proj i) : Submodule 𝒪K K) : Set K) := by
      rw [Submodule.map_coe]
      exact (LinearMap.proj i).isBounded_image_of_integer hb
    obtain ⟨q, hq⟩ := exists_eq_span_singleton_of_isValuationSaturated hK hQb
      (isValuationSaturated_map_proj hM i bN)
    rcases eq_or_ne q 0 with rfl | hq0
    · have hNM : N = M := inf_eq_left.2 fun x hx ↦ by
        have h : x i ∈ M.map (LinearMap.proj i) := Submodule.mem_map_of_mem hx
        rwa [hq, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at h
      exact ⟨k, hk.trans (Finset.card_le_card (Finset.subset_insert i s)),
        ⟨bN.map (LinearEquiv.ofEq N M hNM)⟩⟩
    -- Otherwise a lift `y ∈ M` of the generator `q` extends the basis of `N` to one of `M`.
    have hqQ : q ∈ M.map (LinearMap.proj i) := hq ▸ Submodule.mem_span_singleton_self q
    obtain ⟨y, hy, hyi⟩ := Submodule.mem_map.1 hqQ
    rw [LinearMap.proj_apply] at hyi
    refine ⟨k + 1, by rw [Finset.card_insert_of_notMem hi]; omega,
      ⟨Module.Basis.mkFinConsOfLE y hy bN inf_le_left (fun c x hx hcx ↦ ?_) fun z hz ↦ ?_⟩⟩
    · have hxi : x i = 0 := hx.2
      have h := congrFun hcx i
      simp only [Pi.add_apply, Pi.smul_apply, integer_smul_eq, smul_eq_mul, hyi, hxi,
        Pi.zero_apply, add_zero] at h
      exact Subtype.ext ((mul_eq_zero.1 h).resolve_right hq0)
    · have hzi : z i ∈ 𝒪K ∙ q := hq ▸ Submodule.mem_map_of_mem hz
      obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.1 hzi
      refine ⟨-d, M.add_mem hz (M.smul_mem _ hy), ?_⟩
      simp [integer_smul_eq, hyi, ← hd]

end FiniteFree

end TauCeti
