/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Analysis.Complex.Basic

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.Contractible
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
import TauCeti.AlgebraicTopology.FundamentalGroup.PuncturedStarConvex
import TauCeti.AlgebraicTopology.FundamentalGroup.VanKampen.Basic
import TauCeti.GroupTheory.CoprodI
import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Topology.MetricSpace.SeparatedBalls

/-!
# The fundamental group of the plane minus finitely many points

The fundamental group of `ℂ` with a finite set `s` of points removed is the free group on `s`, at
every base point (`TauCeti.nonempty_fundamentalGroup_compl_mulEquiv_freeGroup`).

A homeomorphism of the plane first moves the punctures onto the real axis: a linear map gives
them distinct real parts, and a vertical shear along a polynomial through their imaginary parts
then makes them real. So it suffices to treat real points `c i`, for `i : ι`, any two of which are
at distance at least `δ > 0`.

For those, the proof is the Seifert--van Kampen theorem for a family of open sets with a common
simply connected pairwise intersection (`TauCeti.vanKampenWideEquiv`). The common part is a
*comb*: the open lower half-plane together with the *teeth*, the points whose real part is at
distance more than `δ / 4` from every `c i`. The `k`-th member of the cover adds to the comb the
vertical strip of half-width `δ / 2` about `c k`, punctured at `c k`. Distinct strips are disjoint,
so two members meet exactly in the comb.

Both computations are vertical deformations which keep real parts fixed. Pushing every point
down into the lower half-plane deformation retracts the comb onto that convex set, so the comb is
contractible. Pushing down only the points of the `k`-th member outside a narrower strip about
`c k` deformation retracts that member, in the weak sense, onto the union of the lower
half-plane and the strip, punctured at `c k`. This union is star-convex about `c k`, so its
fundamental group is infinite cyclic (`StarConvex.fundamentalGroupMulEquivInt`).

## Main results

* `TauCeti.nonempty_fundamentalGroup_compl_mulEquiv_freeGroup`: the fundamental group of `ℂ`
  minus a finite set of points is free on that set.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.2, Theorem 1.20
  (the Seifert--van Kampen theorem), and Chapter 0, Exercise 4 (weak deformation retractions).
-/

public section

noncomputable section

open Set Metric Topology Complex
open scoped ContinuousMap

namespace TauCeti

variable {ι : Type*} {c : ι → ℝ} {δ : ℝ}

/-! ### The pieces of the cover, as subsets of `ℂ` -/

/-- The open lower half-plane. -/
private def lower : Set ℂ := {z | z.im < 0}

variable (c δ) in
/-- The teeth of the comb: the points whose real part is at distance more than `δ / 4` from
every `c i`. -/
private def teeth : Set ℂ := {z | ∀ i, δ / 4 < |z.re - c i|}

variable (c δ) in
/-- The vertical strip of half-width `δ / 2` about the real point `c k`. -/
private def strip (k : ι) : Set ℂ := {z | |z.re - c k| < δ / 2}

variable (c δ) in
/-- The common part of the cover: the lower half-plane together with the teeth. -/
private def comb : Set ℂ := lower ∪ teeth c δ

variable (c δ) in
/-- The `k`-th member of the cover: the comb together with the strip about `c k`, punctured
at `c k`. -/
private def piece (k : ι) : Set ℂ := comb c δ ∪ (strip c δ k \ {(c k : ℂ)})

variable (c δ) in
/-- The lower half-plane together with the strip about `c k`, a set star-convex about `c k`. -/
private def model (k : ι) : Set ℂ := lower ∪ strip c δ k

private theorem convex_lower : Convex ℝ lower := by
  unfold lower
  exact convex_halfSpace_im_lt 0

private theorem neg_I_mem_lower : -I ∈ lower := by
  simp [lower]

private theorem ofReal_notMem_lower (x : ℝ) : (x : ℂ) ∉ lower := by
  simp [lower]

private theorem ofReal_notMem_comb (hδ : 0 < δ) (k : ι) : (c k : ℂ) ∉ comb c δ := by
  rintro (h | h)
  · exact ofReal_notMem_lower _ h
  · have := h k
    simp only [ofReal_re, sub_self, abs_zero] at this
    linarith

private theorem mem_strip_self (hδ : 0 < δ) (k : ι) : (c k : ℂ) ∈ strip c δ k := by
  simp [strip, hδ]

private theorem neg_I_mem_comb : -I ∈ comb c δ :=
  .inl neg_I_mem_lower

private theorem neg_I_mem_compl_range : -I ∈ (range fun i ↦ (c i : ℂ))ᶜ := by
  rintro ⟨i, hi⟩
  simpa using congrArg Complex.im hi

private theorem comb_subset_piece (k : ι) : comb c δ ⊆ piece c δ k :=
  subset_union_left

private theorem model_diff_subset_piece (k : ι) :
    model c δ k \ {(c k : ℂ)} ⊆ piece c δ k := by
  rintro z ⟨hz | hz, hzk⟩
  · exact .inl (.inl hz)
  · exact .inr ⟨hz, hzk⟩

/-- A member of the cover avoids every puncture. -/
private theorem piece_subset_compl_range (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|)
    (k : ι) : piece c δ k ⊆ (range fun i ↦ (c i : ℂ))ᶜ := by
  rintro z hz ⟨i, rfl⟩
  rcases hz with h | ⟨h, hk⟩
  · exact ofReal_notMem_comb hδ i h
  · rcases eq_or_ne i k with rfl | hik
    · exact hk rfl
    · have h' : |c i - c k| < δ / 2 := by simpa [strip] using h
      linarith [hc hik]

private theorem comb_subset_compl_range (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|)
    [Nonempty ι] : comb c δ ⊆ (range fun i ↦ (c i : ℂ))ᶜ :=
  (comb_subset_piece (Classical.arbitrary ι)).trans
    (piece_subset_compl_range hδ hc (Classical.arbitrary ι))

/-- Two distinct members of the cover meet inside the comb, as their strips are disjoint. -/
private theorem piece_inter_piece_subset (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) {i j : ι}
    (hij : i ≠ j) : piece c δ i ∩ piece c δ j ⊆ comb c δ := by
  rintro z ⟨hi | ⟨hi, -⟩, hj | ⟨hj, -⟩⟩
  · exact hi
  · exact hi
  · exact hj
  · simp only [strip, mem_ofPred_eq] at hi hj
    have := abs_sub_le (c i) z.re (c j)
    rw [abs_sub_comm] at hi
    linarith [hc hij]

/-- The union of the lower half-plane and the strip about `c k` is star-convex about `c k`. -/
private theorem starConvex_model (hδ : 0 < δ) (k : ι) : StarConvex ℝ (c k : ℂ) (model c δ k) := by
  intro z hz a b ha hb hab
  rcases hz with hz | hz
  · rcases hb.eq_or_lt with rfl | hb
    · rw [add_zero] at hab
      subst hab
      rw [one_smul, zero_smul, add_zero]
      exact .inr (mem_strip_self hδ k)
    · refine .inl ?_
      simp only [lower, mem_ofPred_eq, add_im, smul_im, ofReal_im, smul_eq_mul, mul_zero,
        zero_add] at hz ⊢
      exact mul_neg_of_pos_of_neg hb hz
  · refine .inr ?_
    simp only [strip, mem_ofPred_eq, add_re, smul_re, ofReal_re, smul_eq_mul] at hz ⊢
    have h : a * c k + b * z.re - c k = b * (z.re - c k) := by
      linear_combination c k * hab
    rw [h, abs_mul, abs_of_nonneg hb]
    nlinarith [abs_nonneg (z.re - c k)]

private theorem sphere_subset_model (hδ : 0 < δ) (k : ι) :
    sphere (c k : ℂ) (δ / 4) ⊆ model c δ k := by
  intro z hz
  refine .inr ?_
  have h := abs_re_le_norm (z - c k)
  rw [mem_sphere_iff_norm] at hz
  simp only [strip, mem_ofPred_eq]
  simp only [sub_re, ofReal_re] at h
  linarith

/-! ### Pushing points down -/

/-- Push `z` down by `s * (max z.im 0 + 1)`, keeping its real part. For `s = 1` the result lies in
the lower half-plane. -/
private def pushDown (s : ℝ) (z : ℂ) : ℂ := z - ((s * (max z.im 0 + 1) : ℝ) : ℂ) * I

@[simp]
private theorem pushDown_re (s : ℝ) (z : ℂ) : (pushDown s z).re = z.re := by
  simp [pushDown]

@[simp]
private theorem pushDown_im (s : ℝ) (z : ℂ) :
    (pushDown s z).im = z.im - s * (max z.im 0 + 1) := by
  simp [pushDown]

@[simp]
private theorem pushDown_zero (z : ℂ) : pushDown 0 z = z := by
  simp [pushDown]

@[fun_prop]
private theorem continuous_pushDown {X : Type*} [TopologicalSpace X] {s : X → ℝ} {z : X → ℂ}
    (hs : Continuous s) (hz : Continuous z) : Continuous fun x ↦ pushDown (s x) (z x) := by
  unfold pushDown
  fun_prop

private theorem pushDown_im_le {s : ℝ} (hs : 0 ≤ s) (z : ℂ) : (pushDown s z).im ≤ z.im := by
  rw [pushDown_im]
  nlinarith [le_max_right z.im 0]

private theorem pushDown_one_mem_lower (z : ℂ) : pushDown 1 z ∈ lower := by
  simp only [lower, mem_ofPred_eq, pushDown_im, one_mul]
  linarith [le_max_left z.im 0]

private theorem pushDown_mem_lower {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ lower) :
    pushDown s z ∈ lower :=
  lt_of_le_of_lt (pushDown_im_le hs z) hz

private theorem pushDown_mem_comb {s : ℝ} (hs : 0 ≤ s) {z : ℂ} (hz : z ∈ comb c δ) :
    pushDown s z ∈ comb c δ := by
  rcases hz with hz | hz
  · exact .inl (pushDown_mem_lower hs hz)
  · exact .inr (by simpa [teeth] using hz)

/-- The weight of the push in the `k`-th member: `0` within `δ / 4` of `0`, `1` from `δ / 2` on. -/
private def ramp (δ x : ℝ) : ℝ := min 1 (max 0 (4 * |x| / δ - 1))

private theorem ramp_nonneg (δ x : ℝ) : 0 ≤ ramp δ x :=
  le_min zero_le_one (le_max_left _ _)

private theorem ramp_zero (δ : ℝ) : ramp δ 0 = 0 := by
  simp [ramp]

private theorem ramp_eq_one (hδ : 0 < δ) {x : ℝ} (hx : δ / 2 ≤ |x|) : ramp δ x = 1 := by
  refine min_eq_left (le_max_of_le_right ?_)
  rw [le_sub_iff_add_le, le_div_iff₀ hδ]
  linarith

@[fun_prop]
private theorem continuous_ramp (δ : ℝ) : Continuous (ramp δ) := by
  unfold ramp
  fun_prop

/-- The push in the `k`-th member never reaches the puncture `c k`: it moves only points whose real
part differs from `c k`. -/
private theorem pushDown_ramp_ne {k : ι} {t : ℝ} {z : ℂ} (hz : z ≠ c k) :
    pushDown (t * ramp δ (z.re - c k)) z ≠ c k := by
  intro h
  have hre : z.re = c k := by simpa using congrArg Complex.re h
  rw [hre, sub_self, ramp_zero, mul_zero, pushDown_zero] at h
  exact hz h

/-! ### The two deformations -/

/-- The comb deformation retracts, in the weak sense, onto the lower half-plane. -/
private def lowerHomotopyEquivComb : lower ≃ₕ comb c δ :=
  .ofWeakDeformationRetraction subset_union_left (fun p ↦ pushDown p.1 p.2)
    (by fun_prop)
    (fun p ↦ pushDown_mem_comb p.1.2.1 p.2.2)
    (fun _ ↦ pushDown_zero _)
    (fun _ ↦ pushDown_one_mem_lower _)
    (fun t _ hz ↦ pushDown_mem_lower t.2.1 hz)

/-- The comb is contractible. -/
private theorem contractibleSpace_comb : ContractibleSpace (comb c δ) :=
  haveI : ContractibleSpace lower := convex_lower.contractibleSpace ⟨-I, neg_I_mem_lower⟩
  lowerHomotopyEquivComb.symm.contractibleSpace

/-- The time-`t` push of a point of the `k`-th member. -/
private def piecePush (k : ι) (p : unitInterval × ℂ) : ℂ :=
  pushDown ((p.1 : ℝ) * ramp δ (p.2.re - c k)) p.2

private theorem continuous_piecePush (k : ι) : Continuous (piecePush (c := c) (δ := δ) k) := by
  unfold piecePush
  fun_prop

private theorem piecePush_mem_piece (k : ι) (t : unitInterval) {z : ℂ}
    (hz : z ∈ piece c δ k) : piecePush (c := c) (δ := δ) k (t, z) ∈ piece c δ k := by
  have hs : 0 ≤ (t : ℝ) * ramp δ (z.re - c k) := mul_nonneg t.2.1 (ramp_nonneg _ _)
  rcases hz with hz | ⟨hz, hzk⟩
  · exact .inl (pushDown_mem_comb hs hz)
  · exact .inr ⟨by simpa [strip, piecePush] using hz, pushDown_ramp_ne hzk⟩

private theorem piecePush_mem_model (k : ι) (t : unitInterval) {z : ℂ}
    (hz : z ∈ model c δ k \ {(c k : ℂ)}) :
    piecePush (c := c) (δ := δ) k (t, z) ∈ model c δ k \ {(c k : ℂ)} := by
  have hs : 0 ≤ (t : ℝ) * ramp δ (z.re - c k) := mul_nonneg t.2.1 (ramp_nonneg _ _)
  refine ⟨?_, pushDown_ramp_ne hz.2⟩
  rcases hz.1 with h | h
  · exact .inl (pushDown_mem_lower hs h)
  · exact .inr (by simpa [strip, piecePush] using h)

private theorem piecePush_one_mem_model (hδ : 0 < δ) (k : ι) {z : ℂ} (hz : z ∈ piece c δ k) :
    piecePush (c := c) (δ := δ) k (1, z) ∈ model c δ k \ {(c k : ℂ)} := by
  have hzk : z ≠ c k := by
    rintro rfl
    rcases hz with h | ⟨-, h⟩
    · exact ofReal_notMem_comb hδ k h
    · exact h rfl
  refine ⟨?_, pushDown_ramp_ne hzk⟩
  by_cases h : |z.re - c k| < δ / 2
  · exact .inr (by simpa [strip, piecePush] using h)
  · rw [piecePush, ramp_eq_one hδ (not_lt.1 h), Icc.coe_one, one_mul]
    exact .inl (pushDown_one_mem_lower z)

/-- The `k`-th member deformation retracts, in the weak sense, onto the union of the lower
half-plane and the strip about `c k`, punctured at `c k`. -/
private def modelHomotopyEquivPiece (hδ : 0 < δ) (k : ι) :
    ↥(model c δ k \ {(c k : ℂ)}) ≃ₕ piece c δ k :=
  .ofWeakDeformationRetraction (model_diff_subset_piece k) (fun p ↦ piecePush k (p.1, p.2))
    ((continuous_piecePush k).comp (by fun_prop))
    (fun p ↦ piecePush_mem_piece k p.1 p.2.2)
    (fun _ ↦ by simp [piecePush])
    (fun z ↦ piecePush_one_mem_model hδ k z.2)
    (fun t _ hz ↦ piecePush_mem_model k t hz)

/-! ### The cover of the punctured plane -/

/-- Every point of the punctured plane has a member of the cover as a neighbourhood. -/
private theorem exists_piece_mem_nhds [Nonempty ι] (hδ : 0 < δ) {z : ℂ}
    (hz : z ∈ (range fun i ↦ (c i : ℂ))ᶜ) : ∃ k, piece c δ k ∈ 𝓝 z := by
  by_cases h : ∃ k, |z.re - c k| < δ / 2
  · obtain ⟨k, hk⟩ := h
    have hopen : IsOpen (strip c δ k \ {(c k : ℂ)}) :=
      (isOpen_lt (by fun_prop) continuous_const).sdiff isClosed_singleton
    exact ⟨k, Filter.mem_of_superset (hopen.mem_nhds ⟨hk, fun h ↦ hz ⟨k, h.symm⟩⟩)
      subset_union_right⟩
  · simp only [not_exists, not_lt] at h
    refine ⟨Classical.arbitrary ι, Filter.mem_of_superset
      (ball_mem_nhds z (by positivity : 0 < δ / 4)) fun w hw ↦ .inl (.inr fun i ↦ ?_)⟩
    have hw' := abs_re_le_norm (w - z)
    rw [mem_ball_iff_norm] at hw
    simp only [sub_re] at hw'
    have := abs_sub_abs_le_abs_sub (z.re - c i) (w.re - c i)
    rw [show z.re - c i - (w.re - c i) = -(w.re - z.re) by ring, abs_neg] at this
    linarith [h i]

variable (c δ) in
/-- The `k`-th member of the cover, as a subset of the punctured plane. -/
private def cover (k : ι) : Set ↥(range fun i ↦ (c i : ℂ))ᶜ := Subtype.val ⁻¹' piece c δ k

/-- A member of the cover, as a subset of the punctured plane, is homeomorphic to the
corresponding subset of `ℂ`. -/
private def coverHomeomorph (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) (k : ι) :
    cover c δ k ≃ₜ piece c δ k :=
  Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
    (by rw [Subtype.range_coe]; exact piece_subset_compl_range hδ hc k)

private theorem isPathConnected_cover (hδ : 0 < δ) (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|)
    (k : ι) : IsPathConnected (cover c δ k) := by
  have := (starConvex_model (c := c) hδ k).pathConnectedSpace_diff_singleton (by positivity)
    (sphere_subset_model hδ k)
  have := (modelHomotopyEquivPiece (c := c) hδ k).pathConnectedSpace
  exact (isPathConnected_iff_pathConnectedSpace.2 ‹_›).preimage_coe
    (piece_subset_compl_range hδ hc k)

/-- Each member of the cover has infinite cyclic fundamental group. -/
private theorem nonempty_fundamentalGroup_cover_mulEquiv_int (hδ : 0 < δ)
    (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) (k : ι) (z : cover c δ k) :
    Nonempty (FundamentalGroup (cover c δ k) z ≃* Multiplicative ℤ) := by
  have := isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_cover hδ hc k)
  have hV := starConvex_model (c := c) hδ k
  have hr : (0 : ℝ) < δ / 4 := by positivity
  let x : sphere (c k : ℂ) (δ / 4) := ⟨c k + (δ / 4 : ℝ), by simp [hδ.le]⟩
  obtain ⟨e⟩ := ((coverHomeomorph hδ hc k).toHomotopyEquiv.trans
    (modelHomotopyEquivPiece hδ k).symm).nonempty_fundamentalGroupMulEquiv z
      (hV.sphereHomotopyEquiv hr (sphere_subset_model hδ k) x)
  exact ⟨e.trans (hV.fundamentalGroupMulEquivInt hr (sphere_subset_model hδ k) x)⟩

/-- The punctured plane is path connected when there is at least one puncture. -/
private theorem pathConnectedSpace_compl_range [Nonempty ι] (hδ : 0 < δ)
    (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) :
    PathConnectedSpace ↥(range fun i ↦ (c i : ℂ))ᶜ := by
  let b : ↥(range fun i ↦ (c i : ℂ))ᶜ := ⟨-I, neg_I_mem_compl_range⟩
  have hb (z : ↥(range fun i ↦ (c i : ℂ))ᶜ) : Joined z b := by
    obtain ⟨k, hk⟩ := exists_piece_mem_nhds hδ z.2
    exact ((isPathConnected_cover hδ hc k).joinedIn z (mem_preimage.2 (mem_of_mem_nhds hk)) b
      (comb_subset_piece k neg_I_mem_comb)).joined
  exact ⟨⟨b⟩, fun z w ↦ (hb z).trans (hb w).symm⟩

/-- If the real numbers `c i` are pairwise at distance at least `δ > 0`, then the fundamental
group of `ℂ` with the points `c i` removed is the free group on `ι`, at every base point. -/
private theorem nonempty_fundamentalGroup_compl_range_mulEquiv_freeGroup (hδ : 0 < δ)
    (hc : Pairwise fun i j ↦ δ ≤ |c i - c j|) (z : ↥(range fun i ↦ (c i : ℂ))ᶜ) :
    Nonempty (FundamentalGroup ↥(range fun i ↦ (c i : ℂ))ᶜ z ≃* FreeGroup ι) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · -- Without punctures the space is the whole plane, which is contractible.
    have hconv : Convex ℝ (range fun i ↦ (c i : ℂ))ᶜ := by
      rw [range_eq_empty, compl_empty]
      exact convex_univ
    have := hconv.contractibleSpace ⟨z, z.2⟩
    have : Unique (FundamentalGroup ↥(range fun i ↦ (c i : ℂ))ᶜ z) := uniqueOfSubsingleton 1
    exact ⟨MulEquiv.ofUnique⟩
  have := pathConnectedSpace_compl_range hδ hc
  let C : Set ↥(range fun i ↦ (c i : ℂ))ᶜ := Subtype.val ⁻¹' comb c δ
  have hC : IsSimplyConnected C :=
    have := contractibleSpace_comb (c := c) (δ := δ)
    have : ContractibleSpace C := (Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange
      (by rw [Subtype.range_coe]; exact comb_subset_compl_range hδ hc)).contractibleSpace
    SimplyConnectedSpace.ofContractible C
  have hx : (⟨-I, neg_I_mem_compl_range⟩ : ↥(range fun i ↦ (c i : ℂ))ᶜ) ∈ C := neg_I_mem_comb
  let vK := vanKampenWideEquiv (U := cover c δ) (C := C)
    (fun y ↦ (exists_piece_mem_nhds hδ y.2).imp fun _ h ↦
      continuous_subtype_val.continuousAt.preimage_mem_nhds h)
    (isPathConnected_cover hδ hc) hC (fun k ↦ preimage_mono (comb_subset_piece k))
    (fun _ _ hij _ hz ↦ piece_inter_piece_subset hc hij hz)
    hx
  exact ⟨(FundamentalGroup.fundamentalGroupMulEquivOfPathConnected _ _).trans <| vK.symm.trans <|
    (MulEquiv.coprodICongr fun k ↦
      (nonempty_fundamentalGroup_cover_mulEquiv_int hδ hc k _).some.trans
        FreeGroup.mulEquivIntOfUnique.symm).trans freeGroupEquivCoprodI.symm⟩

/-! ### Finitely many punctures anywhere in the plane -/

/-- The vertical shear `z ↦ z - ψ z.re * I` of the plane, a homeomorphism keeping real parts. -/
private def shearIm (ψ : ℝ → ℝ) (hψ : Continuous ψ) : ℂ ≃ₜ ℂ where
  toFun z := z - (ψ z.re : ℂ) * I
  invFun z := z + (ψ z.re : ℂ) * I
  left_inv z := by simp
  right_inv z := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
private theorem shearIm_apply (ψ : ℝ → ℝ) (hψ : Continuous ψ) (z : ℂ) :
    shearIm ψ hψ z = z - (ψ z.re : ℂ) * I :=
  rfl

/-- A homeomorphism of the plane carries a finite set onto real points, injectively. It is a
linear map giving the points distinct real parts, followed by a vertical shear along a polynomial
through their imaginary parts. -/
private theorem exists_homeomorph_eq_ofReal {s : Set ℂ} (hs : s.Finite) :
    ∃ (e : ℂ ≃ₜ ℂ) (c : ℂ → ℝ), InjOn c s ∧ ∀ z ∈ s, e z = c z := by
  obtain ⟨t, ht⟩ :=
    ((hs.prod hs).image fun p : ℂ × ℂ ↦ (p.1 - p.2).re / (p.1 - p.2).im).exists_notMem
  have hu : (1 + t * I : ℂ) ≠ 0 := fun h ↦ by simpa using congrArg re h
  have hc : InjOn (fun z ↦ ((1 + t * I) * z).re) s := by
    intro a ha b hb hab
    by_contra hne
    have hre : (a - b).re = t * (a - b).im := by
      simp only [mul_re, add_re, one_re, mul_im, ofReal_re, I_re, ofReal_im, I_im, add_im,
        one_im] at hab
      simp only [sub_re, sub_im]
      linarith
    have him : (a - b).im ≠ 0 := fun h ↦
      hne (sub_eq_zero.1 (Complex.ext (by simpa [h] using hre) (by simpa using h)))
    exact ht ⟨(a, b), ⟨ha, hb⟩, by simp only [hre, mul_div_assoc, div_self him, mul_one]⟩
  have hc' : InjOn (fun z ↦ ((1 + t * I) * z).re) hs.toFinset := by rwa [hs.coe_toFinset]
  let P := Lagrange.interpolate hs.toFinset (fun z ↦ ((1 + t * I) * z).re)
    fun z ↦ ((1 + t * I) * z).im
  refine ⟨(Homeomorph.mulLeft₀ _ hu).trans (shearIm _ P.continuous),
    fun z ↦ ((1 + t * I) * z).re, hc, fun z hz ↦ ?_⟩
  have hP := Lagrange.eval_interpolate_at_node (r := fun z ↦ ((1 + t * I) * z).im) hc'
    (hs.mem_toFinset.2 hz)
  beta_reduce at hP
  rw [Homeomorph.trans_apply, Homeomorph.coe_mulLeft₀, shearIm_apply, hP]
  apply Complex.ext <;> simp

/-- **The fundamental group of the plane minus finitely many points is free** on those points,
at every base point. -/
theorem nonempty_fundamentalGroup_compl_mulEquiv_freeGroup {s : Set ℂ} (hs : s.Finite)
    (z : ↥sᶜ) : Nonempty (FundamentalGroup ↥sᶜ z ≃* FreeGroup s) := by
  obtain ⟨e, c, hc, he⟩ := exists_homeomorph_eq_ofReal hs
  -- Finitely many distinct real numbers are uniformly separated.
  obtain ⟨r, hr, -, hrc⟩ := exists_pos_closedBall_subset_and_lt_dist (T := hs.toFinset.image c)
    (U := fun _ ↦ univ) fun _ _ ↦ Filter.univ_mem
  have hmem (x : s) : c x ∈ hs.toFinset.image c := Finset.mem_image_of_mem c (by simp)
  have hcδ : Pairwise fun i j : s ↦ 2 * r ≤ |c i - c j| := fun i j hij ↦ by
    simpa only [Real.dist_eq] using
      (hrc _ (hmem i) _ (hmem j) (hc.ne i.2 j.2 (Subtype.coe_ne_coe.2 hij))).le
  have himage : e '' sᶜ = (range fun i : s ↦ (c i : ℂ))ᶜ := by
    rw [e.image_compl]
    congr 1
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (he x hx).symm⟩
    · rintro ⟨⟨x, hx⟩, rfl⟩
      exact ⟨x, hx, he x hx⟩
  let f : ↥sᶜ ≃ₜ ↥(range fun i : s ↦ (c i : ℂ))ᶜ := (e.image sᶜ).trans (.setCongr himage)
  obtain ⟨φ⟩ := nonempty_fundamentalGroup_compl_range_mulEquiv_freeGroup (by positivity) hcδ (f z)
  exact ⟨(FundamentalGroup.homeomorphMulEquiv f z).trans φ⟩

end TauCeti
