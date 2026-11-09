/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Normed.Operator.Prod
public import TauCeti.Analysis.Calculus.ApproximatesLinearOn
public import TauCeti.Analysis.Calculus.MeanValue
public import TauCeti.Analysis.Convex.Prod

/-!
# Splicing two maps with a cutoff along a linear functional

Let `k l : X → Y` be maps between real normed spaces, `π : X →L[ℝ] ℝ` a continuous linear
functional and `δ > 0` a scale. The splice `TauCeti.spliceAlong π k l δ` is the convex combination
`x ↦ k x + χ (δ⁻¹ π x) • (l x - k x)`, where `χ = TauCeti.spliceCutoff` is a fixed smooth cutoff
which is `1` on `[-1, 1]`, vanishes off `(-2, 2)` and takes values in `[0, 1]`. It is `l` where
`|π x| ≤ δ` and `k` where `2 δ ≤ |π x|`, it stays in every convex set containing the values of `k`
and `l`, and it is as smooth as `k` and `l`.

The derivative of the splice is controlled uniformly in the scale. Suppose `‖π‖ ≤ 1`. If the
derivatives of `k` and `l` at `x` are within `ε` of a linear map `A`, and
`‖l x - k x‖ ≤ 2 ε |π x|`, then the splice has derivative within `(3 + 4 B) ε` of `A` at `x`, where
`B` bounds the derivative of the cutoff (`TauCeti.exists_hasFDerivAt_spliceAlong_sub_le`). The
hypothesis on `l x - k x` holds by the mean value inequality when the two maps agree at a point `y`
with `‖x - y‖ = |π x|` (`Convex.norm_sub_le_of_norm_hasFDerivWithin_sub_le` in
`TauCeti.Analysis.Calculus.MeanValue`); the derivative `δ⁻¹ χ' (δ⁻¹ π x) • π` of the cutoff has
norm at most `δ⁻¹ B ‖π‖ ≤ δ⁻¹ B`, but only meets `l x - k x` where `|π x| ≤ 2 δ`.

This is the device used to straighten an embedding near a point or a line: there the two maps are
the embedding and a model agreeing with it to first order, read in a chart.

## Main definitions

* `TauCeti.spliceCutoff`: the fixed smooth cutoff on the line.
* `TauCeti.spliceAlong`: the splice of two maps along a linear functional at a given scale.

## Main results

* `TauCeti.spliceAlong_of_abs_le`, `TauCeti.spliceAlong_of_le_abs`: the splice is `l` near the
  kernel of `π` and `k` away from it.
* `TauCeti.spliceAlong_mem`, `TauCeti.contDiffOn_spliceAlong`: convexity and smoothness.
* `TauCeti.exists_hasFDerivAt_spliceAlong_sub_le`: the uniform derivative estimate.
* `TauCeti.injOn_and_injective_fderiv_spliceAlong_fst`: injectivity and injective derivative
  for splices across a strip whose derivatives stay close to a linear map with a left inverse.
-/

public section

noncomputable section

open Set
open scoped ContDiff

namespace TauCeti

/-! ### The cutoff -/

/-- A fixed smooth cutoff on the line: it is `1` on `[-1, 1]`, vanishes off `(-2, 2)`, and takes
values in `[0, 1]`. -/
def spliceCutoff : ℝ → ℝ :=
  (⟨1, 2, one_pos, one_lt_two⟩ : ContDiffBump (0 : ℝ))

/-- The cutoff is `1` on `[-1, 1]`. -/
@[simp]
theorem spliceCutoff_eq_one {x : ℝ} (hx : |x| ≤ 1) : spliceCutoff x = 1 :=
  ContDiffBump.one_of_mem_closedBall _ (by simpa [Real.dist_eq] using hx)

/-- The cutoff vanishes off `(-2, 2)`. -/
@[simp]
theorem spliceCutoff_eq_zero {x : ℝ} (hx : 2 ≤ |x|) : spliceCutoff x = 0 :=
  ContDiffBump.zero_of_le_dist _ (by simpa [Real.dist_eq] using hx)

/-- The cutoff is nonnegative. -/
theorem spliceCutoff_nonneg (x : ℝ) : 0 ≤ spliceCutoff x := ContDiffBump.nonneg _

/-- The cutoff is at most `1`. -/
theorem spliceCutoff_le_one (x : ℝ) : spliceCutoff x ≤ 1 := ContDiffBump.le_one _

/-- The cutoff is smooth. -/
theorem contDiff_spliceCutoff {n : ℕ∞} : ContDiff ℝ n spliceCutoff := ContDiffBump.contDiff _

/-- The derivative of the cutoff vanishes off `[-2, 2]`. -/
@[simp]
theorem deriv_spliceCutoff_eq_zero {x : ℝ} (hx : 2 < |x|) : deriv spliceCutoff x = 0 := by
  have h : spliceCutoff =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hx] with y hy
    exact spliceCutoff_eq_zero (le_of_lt hy)
  rw [h.deriv_eq, deriv_const]

/-- The derivative of the cutoff is bounded, since it is continuous with compact support. -/
theorem exists_abs_deriv_spliceCutoff_le : ∃ B, ∀ x, |deriv spliceCutoff x| ≤ B :=
  ((contDiff_spliceCutoff (n := ⊤)).continuous_deriv (by simp)).bounded_above_of_compact_support
    (ContDiffBump.hasCompactSupport _).deriv

/-! ### The splice -/

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

/-- The map `k` with its values near the kernel of `π` replaced by those of `l`: the convex
combination of `k x` and `l x` with weight the cutoff `spliceCutoff` at scale `δ` along `π`. It is
`l` where `|π x| ≤ δ` and `k` where `2 δ ≤ |π x|`. -/
def spliceAlong (π : X →L[ℝ] ℝ) (k l : X → Y) (δ : ℝ) (x : X) : Y :=
  k x + spliceCutoff (δ⁻¹ * π x) • (l x - k x)

variable {π : X →L[ℝ] ℝ} {k l : X → Y} {δ : ℝ} {x : X}

/-- The value of the spliced map at a point. -/
theorem spliceAlong_apply :
    spliceAlong π k l δ x = k x + spliceCutoff (δ⁻¹ * π x) • (l x - k x) := by
  rw [spliceAlong]

/-- Where `2 δ ≤ |π x|`, the spliced map is `k`. -/
@[simp]
theorem spliceAlong_of_le_abs (hδ : 0 < δ) (hx : 2 * δ ≤ |π x|) : spliceAlong π k l δ x = k x := by
  rw [spliceAlong, spliceCutoff_eq_zero, zero_smul, add_zero]
  rwa [abs_mul, abs_inv, abs_of_pos hδ, le_inv_mul_iff₀ hδ, mul_comm]

/-- Where `|π x| ≤ δ`, the spliced map is `l`. -/
@[simp]
theorem spliceAlong_of_abs_le (hδ : 0 < δ) (hx : |π x| ≤ δ) : spliceAlong π k l δ x = l x := by
  rw [spliceAlong, spliceCutoff_eq_one, one_smul, add_sub_cancel]
  rwa [abs_mul, abs_inv, abs_of_pos hδ, inv_mul_le_iff₀ hδ, mul_one]

/-- Where `k` and `l` agree, the spliced map is their common value. -/
@[simp]
theorem spliceAlong_of_eq (hx : k x = l x) : spliceAlong π k l δ x = k x := by
  rw [spliceAlong, hx, sub_self, smul_zero, add_zero]

/-- The spliced map is a convex combination of the two maps, so it stays in any convex set
containing both values. -/
theorem spliceAlong_mem {S : Set Y} (hS : Convex ℝ S) (hk : k x ∈ S) (hl : l x ∈ S) :
    spliceAlong π k l δ x ∈ S :=
  hS.add_smul_sub_mem hk hl ⟨spliceCutoff_nonneg _, spliceCutoff_le_one _⟩

/-- The spliced map is as smooth as the two maps. -/
theorem contDiffOn_spliceAlong {n : ℕ∞} {W : Set X} (hk : ContDiffOn ℝ n k W)
    (hl : ContDiffOn ℝ n l W) (π : X →L[ℝ] ℝ) (δ : ℝ) :
    ContDiffOn ℝ n (spliceAlong π k l δ) W := by
  have hc : ContDiff ℝ n fun x => spliceCutoff (δ⁻¹ * π x) :=
    contDiff_spliceCutoff.comp (contDiff_const.mul π.contDiff)
  exact hk.add (hc.contDiffOn.smul (hl.sub hk))

/-- The derivative of the spliced map, by the product rule. -/
theorem hasFDerivAt_spliceAlong {k' l' : X →L[ℝ] Y} (hk : HasFDerivAt k k' x)
    (hl : HasFDerivAt l l' x) :
    HasFDerivAt (spliceAlong π k l δ)
      (k' + (spliceCutoff (δ⁻¹ * π x) • (l' - k') +
        ((δ⁻¹ * deriv spliceCutoff (δ⁻¹ * π x)) • π).smulRight (l x - k x))) x := by
  have hc : HasFDerivAt (fun x => spliceCutoff (δ⁻¹ * π x))
      ((δ⁻¹ * deriv spliceCutoff (δ⁻¹ * π x)) • π) x := by
    have h := (((contDiff_spliceCutoff (n := 1)).differentiable (by simp))
      (δ⁻¹ * π x)).hasDerivAt.comp_hasFDerivAt x (π.hasFDerivAt.const_mul δ⁻¹)
    rwa [smul_smul, mul_comm] at h
  exact hk.add (hc.smul (hl.sub hk))

/-- **The derivative of a spliced map.** If the derivatives of `k` and `l` at `x` are within `ε` of
a linear map `A`, `‖l x - k x‖ ≤ 2 ε |π x|` and `B` bounds the derivative of the cutoff, then at
every scale `δ > 0` the spliced map has derivative within `(3 + 4 B) ε` of `A` at `x`, for a
functional `π` of norm at most `1`. The derivative `δ⁻¹ χ' (δ⁻¹ π x) • π` of the cutoff only
meets `l x - k x` where `|π x| ≤ 2 δ`. -/
theorem exists_hasFDerivAt_spliceAlong_sub_le {k' l' A : X →L[ℝ] Y} {ε B : ℝ} (hδ : 0 < δ)
    (hπ : ‖π‖ ≤ 1) (hB : ∀ x, |deriv spliceCutoff x| ≤ B) (hk : HasFDerivAt k k' x)
    (hl : HasFDerivAt l l' x) (hk' : ‖k' - A‖ ≤ ε) (hl' : ‖l' - A‖ ≤ ε)
    (hlk : ‖l x - k x‖ ≤ 2 * ε * |π x|) :
    ∃ h' : X →L[ℝ] Y, HasFDerivAt (spliceAlong π k l δ) h' x ∧ ‖h' - A‖ ≤ (3 + 4 * B) * ε := by
  have hε : 0 ≤ ε := (norm_nonneg _).trans hk'
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set c := spliceCutoff (δ⁻¹ * π x)
  set c' : X →L[ℝ] ℝ := (δ⁻¹ * deriv spliceCutoff (δ⁻¹ * π x)) • π with hc'_def
  refine ⟨k' + (c • (l' - k') + c'.smulRight (l x - k x)), hasFDerivAt_spliceAlong hk hl, ?_⟩
  -- The term from the derivative of the cutoff is at most `4 B ε`.
  have hcorr : ‖c'.smulRight (l x - k x)‖ ≤ 4 * B * ε := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    have hc'n : ‖c'‖ ≤ δ⁻¹ * |deriv spliceCutoff (δ⁻¹ * π x)| := by
      rw [hc'_def, norm_smul, Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hδ]
      exact mul_le_of_le_one_right (by positivity) hπ
    by_cases h2 : 2 < |δ⁻¹ * π x|
    · rw [deriv_spliceCutoff_eq_zero h2, abs_zero, mul_zero] at hc'n
      rw [le_antisymm hc'n (norm_nonneg _), zero_mul]; positivity
    · rw [not_lt, abs_mul, abs_inv, abs_of_pos hδ, inv_mul_le_iff₀ hδ] at h2
      calc ‖c'‖ * ‖l x - k x‖ ≤ (δ⁻¹ * B) * (2 * ε * (δ * 2)) := by
            gcongr
            · exact hc'n.trans (by gcongr; exact hB _)
            · exact hlk.trans (by gcongr)
        _ = 4 * B * ε := by field_simp; ring
  have hmid : ‖c • (l' - k')‖ ≤ 2 * ε := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (spliceCutoff_nonneg _)]
    calc c * ‖l' - k'‖ ≤ 1 * (ε + ε) := by
          gcongr
          · exact spliceCutoff_le_one _
          · exact (norm_sub_le_norm_sub_add_norm_sub l' A k').trans
              (by rw [norm_sub_rev A]; linarith)
      _ = 2 * ε := by ring
  calc ‖k' + (c • (l' - k') + c'.smulRight (l x - k x)) - A‖
      = ‖(k' - A) + (c • (l' - k') + c'.smulRight (l x - k x))‖ := by congr 1; abel
    _ ≤ ‖k' - A‖ + (‖c • (l' - k')‖ + ‖c'.smulRight (l x - k x)‖) :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ε + (2 * ε + 4 * B * ε) := by gcongr
    _ = (3 + 4 * B) * ε := by ring

/-- A splice across a strip is injective with injective derivative when both maps agree on the
central line and their derivatives stay close to a linear map with a left inverse. The bound on
`ε` makes the splice composed with that left inverse approximate the identity. -/
theorem injOn_and_injective_fderiv_spliceAlong_fst {k l : ℝ × ℝ → Y}
    {ρ δ ε B : ℝ} {A : ℝ × ℝ →L[ℝ] Y} {P : Y →L[ℝ] ℝ × ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ)
    (hkC : ContDiffOn ℝ 1 k {u | |u.1| < ρ})
    (hlC : ContDiffOn ℝ 1 l {u | |u.1| < ρ})
    (hkl0 : ∀ t, k (0, t) = l (0, t))
    (hbound : ∀ u : ℝ × ℝ, |u.1| < ρ →
      ‖fderiv ℝ k u - A‖ < ε ∧ ‖fderiv ℝ l u - A‖ < ε)
    (hB : ∀ x, |deriv spliceCutoff x| ≤ B) (hP : Function.LeftInverse P A)
    (hPε : ‖P‖ * ((3 + 4 * B) * ε) ≤ 1 / 2) :
    InjOn (spliceAlong (ContinuousLinearMap.fst ℝ ℝ ℝ) k l δ) {u | |u.1| < ρ} ∧
      ∀ u : ℝ × ℝ, |u.1| < ρ →
        Function.Injective (fderiv ℝ (spliceAlong (ContinuousLinearMap.fst ℝ ℝ ℝ) k l δ) u) := by
  let h := spliceAlong (ContinuousLinearMap.fst ℝ ℝ ℝ) k l δ
  have hW : IsOpen {u : ℝ × ℝ | |u.1| < ρ} :=
    isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  have hdk (v : ℝ × ℝ) (hv : |v.1| < ρ) : HasFDerivAt k (fderiv ℝ k v) v :=
    ((hkC.contDiffAt (hW.mem_nhds hv)).differentiableAt one_ne_zero).hasFDerivAt
  have hdl (v : ℝ × ℝ) (hv : |v.1| < ρ) : HasFDerivAt l (fderiv ℝ l v) v :=
    ((hlC.contDiffAt (hW.mem_nhds hv)).differentiableAt one_ne_zero).hasFDerivAt
  have hderiv (u : ℝ × ℝ) (hu : |u.1| < ρ) :
      ∃ h' : ℝ × ℝ →L[ℝ] Y, HasFDerivAt h h' u ∧ ‖h' - A‖ ≤ (3 + 4 * B) * ε := by
    -- `l - k` vanishes on the line `u.1 = 0`, so it is at most `2 ε |u.1|` on the strip.
    have hzero : ((0 : ℝ), u.2) ∈ {v : ℝ × ℝ | |v.1| < ρ} := by
      simpa using hρ
    have hdist : ‖u - ((0 : ℝ), u.2)‖ = |u.1| := by
      simp [Prod.norm_def, Real.norm_eq_abs]
    have hlk := (convex_setOf_abs_fst_lt (W := ℝ) ρ).norm_sub_le_of_norm_hasFDerivWithin_sub_le
      (fun v hv => (hdk v hv).hasFDerivWithinAt) (fun v hv => (hdl v hv).hasFDerivWithinAt)
      (fun v hv => (hbound v hv).1.le) (fun v hv => (hbound v hv).2.le) hu
      hzero (hkl0 u.2)
    rw [hdist] at hlk
    exact exists_hasFDerivAt_spliceAlong_sub_le hδ (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ) hB
      (hdk u hu) (hdl u hu) (hbound u hu).1.le (hbound u hu).2.le hlk
  choose! h' hh' hh'A using hderiv
  obtain ⟨hinj, hinj'⟩ :=
    (convex_setOf_abs_fst_lt (W := ℝ) ρ).injOn_and_injective_of_norm_hasFDerivAt_sub_le hP hh'
      fun u hu => (mul_le_mul_of_nonneg_left (hh'A u hu) (norm_nonneg P)).trans hPε
  exact ⟨hinj, fun u hu => (hh' u hu).fderiv ▸ hinj' u hu⟩

end TauCeti
