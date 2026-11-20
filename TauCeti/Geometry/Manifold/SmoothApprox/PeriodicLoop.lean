/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Topology.Homotopy.Path
public import TauCeti.Geometry.Manifold.SmoothApprox
import TauCeti.Algebra.Order.Floor.Ring
import TauCeti.Topology.Homotopy.HomotopyGroup.LoopSpace
import TauCeti.Topology.Homotopy.Path

/-!
# Smooth representatives of paths of smooth loops

Let `M` be a Hausdorff boundaryless manifold, and let `γ₀`, `γ₁` be loops at `x` that are the
restrictions to `[0, 1]` of `C^n` `1`-periodic maps `g₀ g₁ : ℝ → M`. A path of loops `P` from
`γ₀` to `γ₁` is a continuous cylinder whose seam stays at `x`. This file shows that `P` is
homotopic, relative to its endpoints, to the path of loops `s ↦ u (s, ·)` of a `C^n` map
`u : ℝ × ℝ → M` that is `1`-periodic in its second coordinate, with `u (0, ·) = g₀` and
`u (1, ·) = g₁`. The target need not be compact. For `n ≥ 2` such a `u` is a cylinder in the sense
of `TauCeti.IsLoopCylinder`; the consequences for cylinders and caps are drawn in
`Geometry/Symplectic/Hamiltonian/ContractibleAction/Smooth.lean`.

The proof smooths a continuous representative relative to a closed set, by the relative Whitney
approximation theorem (`ContinuousMap.exists_contMDiff_homotopicRel_of_isCompact_closure_range`).
A continuous path of loops is not smooth anywhere a priori, so its map of the square is first
precomposed with a continuous self-map of the square, homotopic to the identity through maps
preserving its boundary conditions. This reparametrization `G` is smooth on a neighbourhood of the
complement `S` of the open square `(1/4, 3/4)²` within the strip `ℝ × [0, 1]`:

* for `s ≤ 1/3` it stays at the loop `γ₀`, reparametrized by the smooth maps
  `t ↦ t + c (χ(3t - 1) - t)` of `[0, 1]` fixing `0` and `1`, `χ` the smooth transition function,
  with `c` rising smoothly from `0` to `1`; so there `G (s, t) = g₀ (…)` is a smooth function of
  `(s, t)`;
* for `c = 1` the reparametrization is locally constant near `t = 0` and `t = 1`, so for
  `1/3 ≤ s ≤ 2/3` the path of loops is run with its loops collapsed near the seam, where `G = x`;
* for `s ≥ 2/3` it stays at the loop `γ₁`, while `c` falls back to `0`, and `G (s, t) = g₁ (…)`.

The approximation `u₀` agrees with `G` on `S`, and `u (s, t) = u₀ (s, fract t)` is `C^n` and
`1`-periodic, since near the seam lines `t ∈ ℤ` it equals the periodic map `G`.

## Main results

* `TauCeti.exists_contMDiff_periodic_homotopic`: every path of loops between `C^n` periodic loops
  is homotopic to the path of loops of a `C^n` periodic map of the plane.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., GTM 218, Springer, 2013, Theorem 6.26
  (relative Whitney approximation).
-/

public section

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology

namespace TauCeti

/-! ### The reparametrization of the square -/

/-- The weight `c` of the slide, a smooth bump: `1` for `1/3 ≤ s ≤ 2/3`, and `0` for `s ≤ 1/6` and
for `s ≥ 5/6`. -/
private def slideWeight : ContDiffBump (1 / 2 : ℝ) :=
  ⟨1 / 6, 1 / 3, by norm_num, by norm_num⟩

/-- The reparametrization `t ↦ t + c (χ(3t - 1) - t)` of the unit interval. For `c = 1` it is
`0` on `[0, 1/3]` and `1` on `[2/3, 1]`. -/
private def seamCollapse (c t : ℝ) : ℝ :=
  t + c * (Real.smoothTransition (3 * t - 1) - t)

/-- The radial coordinate `s ↦ 3 s - 1`, clamped to the unit interval. -/
private def radial (s : ℝ) : unitInterval :=
  projIcc 0 1 zero_le_one (3 * s - 1)

private theorem continuous_radial : Continuous radial :=
  continuous_projIcc.comp ((continuous_const.mul continuous_id).sub continuous_const)

private theorem continuous_seamCollapse : Continuous fun p : ℝ × ℝ ↦ seamCollapse p.1 p.2 := by
  unfold seamCollapse
  have := Real.smoothTransition.continuous
  fun_prop

private theorem contDiff_seamCollapse {m : ℕ∞} :
    ContDiff ℝ m fun p : ℝ × ℝ ↦ seamCollapse p.1 p.2 :=
  contDiff_snd.add (contDiff_fst.mul ((Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_snd).sub contDiff_const)).sub contDiff_snd))

private theorem slideWeight_of_le {s : ℝ} (hs : s ≤ 1 / 6) : slideWeight s = 0 :=
  slideWeight.zero_of_le_dist <| by
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]
    dsimp only [slideWeight]
    linarith

private theorem slideWeight_of_ge {s : ℝ} (hs : 5 / 6 ≤ s) : slideWeight s = 0 :=
  slideWeight.zero_of_le_dist <| by
    rw [Real.dist_eq, abs_of_nonneg (by linarith)]
    dsimp only [slideWeight]
    linarith

private theorem slideWeight_of_mem {s : ℝ} (hs₁ : 1 / 3 ≤ s) (hs₂ : s ≤ 2 / 3) :
    slideWeight s = 1 :=
  slideWeight.one_of_mem_closedBall <| by
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le]
    dsimp only [slideWeight]
    constructor <;> linarith

private theorem slideWeight_mem (s : ℝ) : slideWeight s ∈ Icc (0 : ℝ) 1 :=
  ⟨slideWeight.nonneg, slideWeight.le_one⟩

private theorem radial_of_le {s : ℝ} (hs : s ≤ 1 / 3) : radial s = 0 :=
  projIcc_of_le_left _ (by linarith)

private theorem radial_of_ge {s : ℝ} (hs : 2 / 3 ≤ s) : radial s = 1 :=
  projIcc_of_right_le _ (by linarith)

private theorem seamCollapse_zero_left (t : ℝ) : seamCollapse 0 t = t := by
  simp [seamCollapse]

private theorem seamCollapse_zero_right (c : ℝ) : seamCollapse c 0 = 0 := by
  rw [seamCollapse, Real.smoothTransition.zero_of_nonpos (by norm_num)]
  ring

private theorem seamCollapse_one_right (c : ℝ) : seamCollapse c 1 = 1 := by
  rw [seamCollapse, Real.smoothTransition.one_of_one_le (by norm_num)]
  ring

/-- Near `t = 0` the reparametrization is the dilation `t ↦ (1 - c) t`. -/
private theorem seamCollapse_of_le (c : ℝ) {t : ℝ} (ht : t ≤ 1 / 3) :
    seamCollapse c t = (1 - c) * t := by
  rw [seamCollapse, Real.smoothTransition.zero_of_nonpos (by linarith)]
  ring

/-- Near `t = 1` the reparametrization is the dilation `t ↦ 1 + (1 - c) (t - 1)`. -/
private theorem seamCollapse_of_ge (c : ℝ) {t : ℝ} (ht : 2 / 3 ≤ t) :
    seamCollapse c t = 1 + (1 - c) * (t - 1) := by
  rw [seamCollapse, Real.smoothTransition.one_of_one_le (by linarith)]
  ring

/-- For `0 ≤ c ≤ 1` the reparametrization maps the unit interval to itself. -/
private theorem seamCollapse_mem {c t : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    seamCollapse c t ∈ Icc (0 : ℝ) 1 :=
  (convex_Icc 0 1).add_smul_sub_mem ht
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ hc

/-! ### Loops of the reparametrized square -/

variable {M : Type*} [TopologicalSpace M] {x : M} {γ₀ γ₁ : Path x x}

/-- A loop `δ` that is `g` on the unit interval, evaluated at a parameter `r ∈ [0, 1]`. -/
private theorem apply_projIcc {δ : Path x x} {g : ℝ → M} (hδ : ∀ t : unitInterval, δ t = g t)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) : δ (projIcc 0 1 zero_le_one r) = g r := by
  rw [hδ, projIcc_of_mem _ hr]

/-- Near a seam line `t = n`, the loop `δ` reparametrized by `seamCollapse c` is
`g ((1 - c) (t - n))`. -/
private theorem apply_seamCollapse_fract {δ : Path x x} {g : ℝ → M} (hgp : Periodic g 1)
    (hδ : ∀ t : unitInterval, δ t = g t) {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1) {n : ℤ} {t : ℝ}
    (ht : |t - n| < 1 / 3) :
    δ (projIcc 0 1 zero_le_one (seamCollapse c (Int.fract t))) = g ((1 - c) * (t - n)) := by
  obtain ⟨ht₁, ht₂⟩ := abs_lt.1 ht
  rcases le_or_gt (n : ℝ) t with htn | htn
  · -- Just above the seam line, `fract t = t - n`.
    rw [Int.fract, Int.floor_eq_iff.2 ⟨htn, by linarith⟩, seamCollapse_of_le _ (by linarith)]
    have h₁ := mul_nonneg hc.1 (by linarith : (0 : ℝ) ≤ t - n)
    have h₂ := mul_nonneg (sub_nonneg.2 hc.2) (by linarith : (0 : ℝ) ≤ t - n)
    exact apply_projIcc hδ ⟨by nlinarith, by nlinarith⟩
  · -- Just below the seam line, `fract t = t - (n - 1)`.
    rw [Int.fract, (Int.floor_eq_iff (z := n - 1)).2 ⟨by push_cast; linarith,
      by push_cast; linarith⟩, seamCollapse_of_ge _ (by push_cast; linarith)]
    have e : (1 : ℝ) + (1 - c) * (t - ↑(n - 1) - 1) = (1 - c) * (t - n) + 1 := by
      push_cast
      ring
    have h₁ := mul_nonneg hc.1 (by linarith : (0 : ℝ) ≤ n - t)
    have h₂ := mul_nonneg (sub_nonneg.2 hc.2) (by linarith : (0 : ℝ) ≤ n - t)
    rw [e, apply_projIcc hδ ⟨by nlinarith, by nlinarith⟩, hgp]

/-- Near a seam line, every loop reparametrized by `seamCollapse 1` is at the base point. -/
private theorem apply_seamCollapse_one_fract (δ : Path x x) {n : ℤ} {t : ℝ}
    (ht : |t - n| < 1 / 3) : δ (projIcc 0 1 zero_le_one (seamCollapse 1 (Int.fract t))) = x := by
  obtain ⟨ht₁, ht₂⟩ := abs_lt.1 ht
  rcases le_or_gt (n : ℝ) t with htn | htn
  · rw [Int.fract, Int.floor_eq_iff.2 ⟨htn, by linarith⟩, seamCollapse_of_le _ (by linarith),
      sub_self, zero_mul, projIcc_eq_zero.2 le_rfl, δ.source]
  · rw [Int.fract, (Int.floor_eq_iff (z := n - 1)).2 ⟨by push_cast; linarith,
      by push_cast; linarith⟩, seamCollapse_of_ge _ (by push_cast; linarith), sub_self, zero_mul,
      add_zero, projIcc_eq_one.2 le_rfl, δ.target]

/-- The reparametrized square of a path of loops `P`, extended `1`-periodically in `t`. -/
private def reparamDisc (P : Path γ₀ γ₁) (z : ℝ × ℝ) : M :=
  P (radial z.1) (projIcc 0 1 zero_le_one (seamCollapse (slideWeight z.1) (Int.fract z.2)))

private theorem reparamDisc_fract (P : Path γ₀ γ₁) (s t : ℝ) :
    reparamDisc P (s, Int.fract t) = reparamDisc P (s, t) := by
  simp [reparamDisc, Int.fract_fract]

/-- On the strip `n ≤ t < n + 1` the reparametrized square is given without `fract`. -/
private theorem reparamDisc_of_mem_Ico (P : Path γ₀ γ₁) (s : ℝ) {n : ℤ} {t : ℝ}
    (ht : t ∈ Ico (n : ℝ) (n + 1)) :
    reparamDisc P (s, t) =
      P (radial s) (projIcc 0 1 zero_le_one (seamCollapse (slideWeight s) (t - n))) := by
  rw [reparamDisc, Int.fract, Int.floor_eq_iff.2 ht]

/-- On the unit square the reparametrized square is given without `fract`. -/
private theorem reparamDisc_of_mem_Icc (P : Path γ₀ γ₁) (s : ℝ) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    reparamDisc P (s, t) =
      P (radial s) (projIcc 0 1 zero_le_one (seamCollapse (slideWeight s) t)) := by
  rcases ht.2.lt_or_eq with ht' | rfl
  · simpa using reparamDisc_of_mem_Ico P s (n := 0) ⟨by simpa using ht.1, by simpa using ht'⟩
  · rw [reparamDisc, Int.fract_one, seamCollapse_zero_right, seamCollapse_one_right,
      projIcc_eq_zero.2 le_rfl, projIcc_eq_one.2 le_rfl, (P (radial s)).source,
      (P (radial s)).target]

variable {g₀ g₁ : ℝ → M}

/-- Near a seam line `t = n` and for `s < 2/3` the reparametrized square is
`g₀ ((1 - c) (t - n))`, with `c` the slide weight. -/
private theorem reparamDisc_of_abs_sub_lt_left (hgp₀ : Periodic g₀ 1)
    (hγ₀ : ∀ t : unitInterval, γ₀ t = g₀ t) (P : Path γ₀ γ₁) {s : ℝ} (hs : s < 2 / 3) {n : ℤ}
    {t : ℝ} (ht : |t - n| < 1 / 3) :
    reparamDisc P (s, t) = g₀ ((1 - slideWeight s) * (t - n)) := by
  rcases le_or_gt s (1 / 3) with hs' | hs'
  · rw [reparamDisc, radial_of_le hs', P.source]
    exact apply_seamCollapse_fract hgp₀ hγ₀ (slideWeight_mem s) ht
  · have hg₀ : g₀ 0 = x := by simpa using (hγ₀ 0).symm
    rw [reparamDisc, slideWeight_of_mem hs'.le hs.le, apply_seamCollapse_one_fract _ ht, sub_self,
      zero_mul, hg₀]

/-- Near a seam line `t = n` and for `s > 1/3` the reparametrized square is
`g₁ ((1 - c) (t - n))`, with `c` the slide weight. -/
private theorem reparamDisc_of_abs_sub_lt_right (hgp₁ : Periodic g₁ 1)
    (hγ₁ : ∀ t : unitInterval, γ₁ t = g₁ t) (P : Path γ₀ γ₁) {s : ℝ} (hs : 1 / 3 < s) {n : ℤ}
    {t : ℝ} (ht : |t - n| < 1 / 3) :
    reparamDisc P (s, t) = g₁ ((1 - slideWeight s) * (t - n)) := by
  rcases le_or_gt (2 / 3) s with hs' | hs'
  · rw [reparamDisc, radial_of_ge hs', P.target]
    exact apply_seamCollapse_fract hgp₁ hγ₁ (slideWeight_mem s) ht
  · have hg₁ : g₁ 0 = x := by simpa using (hγ₁ 0).symm
    rw [reparamDisc, slideWeight_of_mem hs.le hs'.le, apply_seamCollapse_one_fract _ ht, sub_self,
      zero_mul, hg₁]

private theorem continuous_reparamDisc (P : Path γ₀ γ₁) : Continuous (reparamDisc P) := by
  have h : Continuous (uncurry fun (z : ℝ × ℝ) (τ : ℝ) ↦
      P (radial z.1) (projIcc 0 1 zero_le_one (seamCollapse (slideWeight z.1) τ))) :=
    (P.continuous.comp (continuous_radial.comp (continuous_fst.comp continuous_fst))).eval
      (continuous_projIcc.comp (continuous_seamCollapse.comp
        ((slideWeight.continuous.comp (continuous_fst.comp continuous_fst)).prodMk
          continuous_snd)))
  refine h.continuousOn.comp_fract continuous_snd fun z ↦ ?_
  rw [seamCollapse_zero_right, seamCollapse_one_right, projIcc_eq_zero.2 le_rfl,
    projIcc_eq_one.2 le_rfl, Path.source, Path.target]

/-- Along `s = 0` the reparametrized square is the periodic loop `g₀`. -/
private theorem reparamDisc_zero_left (hgp₀ : Periodic g₀ 1)
    (hγ₀ : ∀ t : unitInterval, γ₀ t = g₀ t) (P : Path γ₀ γ₁) (t : ℝ) :
    reparamDisc P (0, t) = g₀ t := by
  rw [reparamDisc, slideWeight_of_le (by norm_num), seamCollapse_zero_left,
    radial_of_le (by norm_num), P.source, apply_projIcc hγ₀
      (unitInterval.fract_mem t), hgp₀.apply_fract]

/-- Along `s = 1` the reparametrized square is the periodic loop `g₁`. -/
private theorem reparamDisc_one_left (hgp₁ : Periodic g₁ 1)
    (hγ₁ : ∀ t : unitInterval, γ₁ t = g₁ t) (P : Path γ₀ γ₁) (t : ℝ) :
    reparamDisc P (1, t) = g₁ t := by
  rw [reparamDisc, slideWeight_of_ge (by norm_num), seamCollapse_zero_left,
    radial_of_ge (by norm_num), P.target, apply_projIcc hγ₁
      (unitInterval.fract_mem t), hgp₁.apply_fract]

/-- Along the seam the reparametrized square is at the base point `x`. -/
private theorem reparamDisc_seam (P : Path γ₀ γ₁) (s : ℝ) {t : ℝ}
    (ht : t = 0 ∨ t = 1) : reparamDisc P (s, t) = x := by
  rcases ht with rfl | rfl
  · rw [reparamDisc_of_mem_Icc P s ⟨le_rfl, zero_le_one⟩, seamCollapse_zero_right,
      projIcc_eq_zero.2 le_rfl, (P _).source]
  · rw [reparamDisc_of_mem_Icc P s ⟨zero_le_one, le_rfl⟩, seamCollapse_one_right,
      projIcc_eq_one.2 le_rfl, (P _).target]

/-- A path of loops is homotopic to the path of loops of its reparametrized square. The homotopy
moves the radial coordinate linearly from `s` to `3 s - 1` and the reparametrization weight
linearly from `0` to `c`. -/
private theorem homotopic_reparamDisc (P P' : Path γ₀ γ₁)
    (hP' : ∀ s t : unitInterval, P' s t = reparamDisc P (s, t)) : P.Homotopic P' := by
  have hw : Continuous fun q : unitInterval × unitInterval × unitInterval ↦
      ((q.1 : ℝ) * slideWeight q.2.1, (q.2.2 : ℝ)) :=
    (continuous_subtype_val.comp continuous_fst |>.mul
      (slideWeight.continuous.comp (continuous_subtype_val.comp
        (continuous_fst.comp continuous_snd)))).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_snd))
  refine Path.homotopic_of_continuous_cube
    (fun q ↦ P (projIcc 0 1 zero_le_one ((1 - q.1) * q.2.1 + q.1 * (3 * q.2.1 - 1)))
      (projIcc 0 1 zero_le_one (seamCollapse (q.1 * slideWeight q.2.1) q.2.2)))
    ((P.continuous.comp (continuous_projIcc.comp (by fun_prop))).eval
      (continuous_projIcc.comp (continuous_seamCollapse.comp hw))) ?_ ?_ ?_ ?_ ?_ ?_
  · intro s t
    simp [seamCollapse_zero_left]
  · intro s t
    rw [hP', reparamDisc_of_mem_Icc P s ⟨t.2.1, t.2.2⟩]
    simp [radial]
  · intro τ t
    have hτ : projIcc (0 : ℝ) 1 zero_le_one ((1 - τ) * 0 + τ * (3 * 0 - 1)) = 0 :=
      projIcc_of_le_left _ (by nlinarith [τ.2.1])
    dsimp only
    rw [Icc.coe_zero, hτ, slideWeight_of_le (by norm_num), mul_zero, seamCollapse_zero_left,
      projIcc_val, P.source]
  · intro τ t
    have hτ : projIcc (0 : ℝ) 1 zero_le_one ((1 - τ) * 1 + τ * (3 * 1 - 1)) = 1 :=
      projIcc_of_right_le _ (by nlinarith [τ.2.1])
    dsimp only
    rw [Icc.coe_one, hτ, slideWeight_of_ge (by norm_num), mul_zero, seamCollapse_zero_left,
      projIcc_val, P.target]
  · intro τ s
    simp only [Icc.coe_zero, seamCollapse_zero_right, projIcc_eq_zero.2 le_rfl, Path.source]
  · intro τ s
    simp only [Icc.coe_one, seamCollapse_one_right, projIcc_eq_one.2 le_rfl, Path.target]

/-- The complement `S` of the open square `(1/4, 3/4)²` in the strip `ℝ × [0, 1]`: the set
relative to which the reparametrized square is smoothed. -/
private def frame : Set (ℝ × ℝ) :=
  (univ ×ˢ Icc 0 1) \ (Ioo (1 / 4) (3 / 4) ×ˢ Ioo (1 / 4) (3 / 4))

private theorem isClosed_frame : IsClosed frame :=
  (isClosed_univ.prod isClosed_Icc).sdiff (isOpen_Ioo.prod isOpen_Ioo)

private theorem mem_frame_of_fst {s t : ℝ} (hs : s ∉ Ioo (1 / 4 : ℝ) (3 / 4))
    (ht : t ∈ Icc (0 : ℝ) 1) : (s, t) ∈ frame :=
  ⟨⟨mem_univ _, ht⟩, fun h ↦ hs h.1⟩

private theorem mem_frame_of_snd {s t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (ht' : t ∉ Ioo (1 / 4 : ℝ) (3 / 4)) : (s, t) ∈ frame :=
  ⟨⟨mem_univ _, ht⟩, fun h ↦ ht' h.2⟩

/-- Points of the frame lie in the region where the reparametrized square is smooth. -/
private theorem frame_subset :
    frame ⊆ {z | z.1 < 1 / 3 ∨ 2 / 3 < z.1 ∨ ∃ n : ℤ, |z.2 - n| < 1 / 3} := by
  rintro ⟨s, t⟩ ⟨⟨-, ht₀, ht₁⟩, hz⟩
  simp only [mem_prod, mem_Ioo, not_and_or, not_lt] at hz
  simp only [mem_ofPred_eq]
  rcases le_or_gt s (1 / 4) with hs | hs
  · exact Or.inl (by linarith)
  rcases le_or_gt (3 / 4) s with hs' | hs'
  · exact Or.inr (Or.inl (by linarith))
  refine Or.inr (Or.inr ?_)
  rcases hz with ((hz | hz) | (hz | hz))
  · linarith
  · linarith
  · exact ⟨0, by rw [Int.cast_zero, sub_zero, abs_lt]; constructor <;> linarith⟩
  · exact ⟨1, by rw [Int.cast_one, abs_lt]; constructor <;> linarith⟩

/-- Near a seam line `t = n`, `(s, fract t)` lies in the frame. -/
private theorem mem_frame_fract {s t : ℝ} {n : ℤ} (ht : |t - n| < 1 / 4) :
    (s, Int.fract t) ∈ frame := by
  obtain ⟨ht₁, ht₂⟩ := abs_lt.1 ht
  refine mem_frame_of_snd (unitInterval.fract_mem t) fun h ↦ ?_
  rcases le_or_gt (n : ℝ) t with htn | htn
  · rw [Int.fract, Int.floor_eq_iff.2 ⟨htn, by linarith⟩] at h
    linarith [h.1]
  · rw [Int.fract, (Int.floor_eq_iff (z := n - 1)).2 ⟨by push_cast; linarith,
      by push_cast; linarith⟩] at h
    push_cast at h
    linarith [h.2]

/-- Two paths of loops whose maps of the square are homotopic relative to the frame are
homotopic. -/
private theorem homotopic_of_homotopicRel {P₀ P₁ : Path γ₀ γ₁} {f₀ f₁ : C(ℝ × ℝ, M)}
    (h : f₀.HomotopicRel f₁ frame) (h₀ : ∀ s t : unitInterval, P₀ s t = f₀ (s, t))
    (h₁ : ∀ s t : unitInterval, P₁ s t = f₁ (s, t)) : P₀.Homotopic P₁ := by
  obtain ⟨H⟩ := h
  have hH {τ : unitInterval} {s t : unitInterval} (hz : ((s : ℝ), (t : ℝ)) ∈ frame) :
      H (τ, ((s : ℝ), (t : ℝ))) = P₀ s t := (H.eq_fst τ hz).trans (h₀ s t).symm
  have h0 : ((0 : unitInterval) : ℝ) ∉ Ioo (1 / 4 : ℝ) (3 / 4) := by norm_num
  have h1 : ((1 : unitInterval) : ℝ) ∉ Ioo (1 / 4 : ℝ) (3 / 4) := by norm_num
  refine Path.homotopic_of_continuous_cube (fun q ↦ H (q.1, ((q.2.1 : ℝ), (q.2.2 : ℝ))))
    (H.continuous.comp (by fun_prop)) (fun s t ↦ (H.apply_zero _).trans (h₀ s t).symm)
    (fun s t ↦ (H.apply_one _).trans (h₁ s t).symm) (fun τ t ↦ ?_) (fun τ t ↦ ?_)
    (fun τ s ↦ ?_) (fun τ s ↦ ?_)
  · rw [hH (mem_frame_of_fst h0 ⟨t.2.1, t.2.2⟩), P₀.source]
  · rw [hH (mem_frame_of_fst h1 ⟨t.2.1, t.2.2⟩), P₀.target]
  · rw [hH (mem_frame_of_snd ⟨le_rfl, zero_le_one⟩ h0), (P₀ s).source]
  · rw [hH (mem_frame_of_snd ⟨zero_le_one, le_rfl⟩ h1), (P₀ s).target]

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [ChartedSpace H M] {n : ℕ∞}

/-- A map agreeing near `z` with `(s, t) ↦ g ((1 - c) (t - m))`, `c` the slide weight, is `C^n`
at `z`. -/
private theorem contMDiffAt_of_eqOn_seam {g : ℝ → M} (hg : ContMDiff 𝓘(ℝ, ℝ) I n g)
    {f : ℝ × ℝ → M} {z : ℝ × ℝ} {U : Set (ℝ × ℝ)} (hU : U ∈ 𝓝 z) {m : ℤ}
    (hf : ∀ w ∈ U, f w = g ((1 - slideWeight w.1) * (w.2 - m))) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n f z :=
  (hg.comp ((contDiff_const.sub (slideWeight.contDiff.comp contDiff_fst)).mul
    (contDiff_snd.sub contDiff_const)).contMDiff).contMDiffAt.congr_of_eventuallyEq
    (eventuallyEq_of_mem hU hf)

/-- Off the seam lines, where the radial coordinate is constant at `r`, the reparametrized square
is the loop `P r` reparametrized smoothly. -/
private theorem contMDiffAt_reparamDisc_of_radial {g : ℝ → M} (hg : ContMDiff 𝓘(ℝ, ℝ) I n g)
    (P : Path γ₀ γ₁) {r : unitInterval} (hr : ∀ t : unitInterval, P r t = g t) {V : Set ℝ}
    (hV : IsOpen V) (hVr : ∀ s ∈ V, radial s = r) {z : ℝ × ℝ} (hz : z.1 ∈ V) {m : ℤ}
    (h : z.2 ∈ Ioo (m : ℝ) (m + 1)) : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (reparamDisc P) z := by
  have hev : reparamDisc P =ᶠ[𝓝 z] fun w ↦ g (seamCollapse (slideWeight w.1) (w.2 - m)) := by
    filter_upwards [(hV.preimage continuous_fst).mem_nhds hz,
      (isOpen_Ioo.preimage continuous_snd).mem_nhds h] with w hw₁ hw₂
    rw [reparamDisc_of_mem_Ico P w.1 (Ioo_subset_Ico_self hw₂), hVr _ hw₁]
    exact apply_projIcc hr (seamCollapse_mem (slideWeight_mem _)
      ⟨by linarith [hw₂.1], by linarith [hw₂.2]⟩)
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hev
  exact (hg.comp (contDiff_seamCollapse.comp ((slideWeight.contDiff.comp contDiff_fst).prodMk
    (contDiff_snd.sub contDiff_const))).contMDiff).contMDiffAt

/-- The reparametrized square is `C^n` for `s < 1/3`, for `s > 2/3`, and near the seam lines. -/
private theorem contMDiffAt_reparamDisc (hg₀ : ContMDiff 𝓘(ℝ, ℝ) I n g₀) (hgp₀ : Periodic g₀ 1)
    (hγ₀ : ∀ t : unitInterval, γ₀ t = g₀ t) (hg₁ : ContMDiff 𝓘(ℝ, ℝ) I n g₁)
    (hgp₁ : Periodic g₁ 1) (hγ₁ : ∀ t : unitInterval, γ₁ t = g₁ t) (P : Path γ₀ γ₁)
    {z : ℝ × ℝ} (hz : z.1 < 1 / 3 ∨ 2 / 3 < z.1 ∨ ∃ m : ℤ, |z.2 - m| < 1 / 3) :
    ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (reparamDisc P) z := by
  -- Near a seam line, the square is `g₀ ((1 - c) (t - m))` or `g₁ ((1 - c) (t - m))`.
  have hseam {m : ℤ} (hm : |z.2 - m| < 1 / 3) :
      ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I n (reparamDisc P) z := by
    have ho : IsOpen {w : ℝ × ℝ | |w.2 - m| < 1 / 3} := isOpen_lt (by fun_prop) continuous_const
    rcases lt_or_ge z.1 (2 / 3) with hs | hs
    · exact contMDiffAt_of_eqOn_seam hg₀
        (((isOpen_lt continuous_fst continuous_const).inter ho).mem_nhds ⟨hs, hm⟩)
        fun w hw ↦ reparamDisc_of_abs_sub_lt_left hgp₀ hγ₀ P hw.1 hw.2
    · exact contMDiffAt_of_eqOn_seam hg₁
        (((isOpen_lt continuous_const continuous_fst).inter ho).mem_nhds
          ⟨(by linarith : (1 : ℝ) / 3 < z.1), hm⟩)
        fun w hw ↦ reparamDisc_of_abs_sub_lt_right hgp₁ hγ₁ P hw.1 hw.2
  have hfloor : |z.2 - ⌊z.2⌋| < 1 / 3 ∨ z.2 ∈ Ioo (⌊z.2⌋ : ℝ) (⌊z.2⌋ + 1) :=
    (eq_floor_or_mem_Ioo z.2).imp_left fun h ↦ by rw [← h, sub_self, abs_zero]; norm_num
  rcases hz with hz | hz | ⟨m, hm⟩
  · -- For `s < 1/3` the square is `γ₀`, reparametrized smoothly.
    refine hfloor.elim hseam fun h ↦ contMDiffAt_reparamDisc_of_radial hg₀ P
      (fun t ↦ by rw [P.source, hγ₀]) isOpen_Iio (fun s hs ↦ radial_of_le (le_of_lt hs)) hz h
  · -- For `s > 2/3` the square is `γ₁`, reparametrized smoothly.
    refine hfloor.elim hseam fun h ↦ contMDiffAt_reparamDisc_of_radial hg₁ P
      (fun t ↦ by rw [P.target, hγ₁]) isOpen_Ioi (fun s hs ↦ radial_of_ge (le_of_lt hs)) hz h
  · exact hseam hm

/-- If `u₀` is `C^n` and agrees with the reparametrized square on the frame, then its periodic
extension `(s, t) ↦ u₀ (s, fract t)` from the strip `ℝ × [0, 1)` is `C^n`: near the seam lines it
is the reparametrized square, and between them it is a translate of `u₀`. -/
private theorem contMDiff_comp_fract (hg₀ : ContMDiff 𝓘(ℝ, ℝ) I n g₀) (hgp₀ : Periodic g₀ 1)
    (hγ₀ : ∀ t : unitInterval, γ₀ t = g₀ t) (hg₁ : ContMDiff 𝓘(ℝ, ℝ) I n g₁)
    (hgp₁ : Periodic g₁ 1) (hγ₁ : ∀ t : unitInterval, γ₁ t = g₁ t) (P : Path γ₀ γ₁)
    {u₀ : ℝ × ℝ → M} (hu₀ : ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u₀)
    (hframe : ∀ z ∈ frame, u₀ z = reparamDisc P z) :
    ContMDiff 𝓘(ℝ, ℝ × ℝ) I n fun z : ℝ × ℝ ↦ u₀ (z.1, Int.fract z.2) := by
  intro z
  rcases eq_floor_or_mem_Ioo z.2 with h | h
  · have hz : |z.2 - ⌊z.2⌋| < 1 / 4 := by rw [← h, sub_self, abs_zero]; norm_num
    have ho : IsOpen {w : ℝ × ℝ | |w.2 - ⌊z.2⌋| < 1 / 4} :=
      isOpen_lt (continuous_snd.sub continuous_const).abs continuous_const
    have hev : (fun w : ℝ × ℝ ↦ u₀ (w.1, Int.fract w.2)) =ᶠ[𝓝 z] reparamDisc P := by
      filter_upwards [ho.mem_nhds hz] with w hw
      rw [hframe _ (mem_frame_fract hw), reparamDisc_fract]
    exact (contMDiffAt_reparamDisc hg₀ hgp₀ hγ₀ hg₁ hgp₁ hγ₁ P
      (Or.inr (Or.inr ⟨⌊z.2⌋, by linarith⟩))).congr_of_eventuallyEq hev
  · have hev : (fun w : ℝ × ℝ ↦ u₀ (w.1, Int.fract w.2)) =ᶠ[𝓝 z]
        fun w ↦ u₀ (w.1, w.2 - ⌊z.2⌋) := by
      filter_upwards [(isOpen_Ioo.preimage continuous_snd).mem_nhds h] with w hw
      rw [Int.fract, Int.floor_eq_iff.2 ⟨hw.1.le, hw.2⟩]
    exact (hu₀.comp (contDiff_fst.prodMk (contDiff_snd.sub contDiff_const)).contMDiff
      ).contMDiffAt.congr_of_eventuallyEq hev

/-! ### Smooth representatives -/

variable [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M] [T2Space M]

/-- **Smooth representatives of paths of loops.** Let `γ₀` and `γ₁` be loops at `x` in a
Hausdorff boundaryless manifold, the restrictions of `C^n` `1`-periodic maps `g₀ g₁ : ℝ → M`. Every
path of loops `P` from `γ₀` to `γ₁` is homotopic, relative to its endpoints, to the path of loops
`s ↦ u (s, ·)` of a `C^n` map `u : ℝ × ℝ → M` that is `1`-periodic in its second coordinate, with
`u (0, ·) = g₀` and `u (1, ·) = g₁`. -/
theorem exists_contMDiff_periodic_homotopic (hg₀ : ContMDiff 𝓘(ℝ, ℝ) I n g₀)
    (hgp₀ : Periodic g₀ 1) (hγ₀ : ∀ t : unitInterval, γ₀ t = g₀ t)
    (hg₁ : ContMDiff 𝓘(ℝ, ℝ) I n g₁) (hgp₁ : Periodic g₁ 1)
    (hγ₁ : ∀ t : unitInterval, γ₁ t = g₁ t) (P : Path γ₀ γ₁) :
    ∃ u : ℝ × ℝ → M, ContMDiff 𝓘(ℝ, ℝ × ℝ) I n u ∧ (∀ z : ℝ × ℝ, u (z.1, z.2 + 1) = u z) ∧
      (∀ t, u (0, t) = g₀ t) ∧ (∀ t, u (1, t) = g₁ t) ∧
      ∃ P' : Path γ₀ γ₁, (∀ s t : unitInterval, P' s t = u (s, t)) ∧ P'.Homotopic P := by
  -- Reparametrize the square of `P`, so that it is smooth near the frame.
  let G : C(ℝ × ℝ, M) := ⟨reparamDisc P, continuous_reparamDisc P⟩
  have hU : {z : ℝ × ℝ | z.1 < 1 / 3 ∨ 2 / 3 < z.1 ∨ ∃ m : ℤ, |z.2 - m| < 1 / 3} ∈ 𝓝ˢ frame := by
    have h₁ : IsOpen {z : ℝ × ℝ | z.1 < 1 / 3} := isOpen_lt continuous_fst continuous_const
    have h₂ : IsOpen {z : ℝ × ℝ | 2 / 3 < z.1} := isOpen_lt continuous_const continuous_fst
    have h₃ : IsOpen {z : ℝ × ℝ | ∃ m : ℤ, |z.2 - m| < 1 / 3} := by
      simp only [ofPred_exists]
      exact isOpen_iUnion fun m ↦ isOpen_lt (by fun_prop) continuous_const
    exact (h₁.union (h₂.union h₃)).mem_nhdsSet.2 frame_subset
  -- Each value of `G` is by definition a value of `P` on the square.
  have hcpt : IsCompact (closure (range G)) :=
    (isCompact_range (Path.continuous_uncurry_iff.2 P.continuous)).closure_of_subset
      (range_subset_iff.2 fun _ ↦ ⟨(_, _), rfl⟩)
  -- Smooth it relative to the frame, and extend the result periodically from `ℝ × [0, 1)`.
  obtain ⟨u₀, hu₀, hGu₀⟩ := G.exists_contMDiff_homotopicRel_of_isCompact_closure_range
    (I := 𝓘(ℝ, ℝ × ℝ)) n hcpt isClosed_frame hU fun z hz ↦
      (contMDiffAt_reparamDisc hg₀ hgp₀ hγ₀ hg₁ hgp₁ hγ₁ P hz).contMDiffWithinAt
  have hframe (z : ℝ × ℝ) (hz : z ∈ frame) : u₀ z = reparamDisc P z :=
    (hGu₀.fst_eq_snd hz).symm
  have hseam (s : ℝ) : u₀ (s, 0) = x := by
    rw [hframe _ (mem_frame_of_snd ⟨le_rfl, zero_le_one⟩ (by norm_num)),
      reparamDisc_seam P s (Or.inl rfl)]
  let u : ℝ × ℝ → M := fun z ↦ u₀ (z.1, Int.fract z.2)
  have hu_left (t : ℝ) : u (0, t) = g₀ t := by
    simp only [u]
    rw [hframe _ (mem_frame_of_fst (by norm_num) (unitInterval.fract_mem t)), reparamDisc_fract,
      reparamDisc_zero_left hgp₀ hγ₀]
  have hu_right (t : ℝ) : u (1, t) = g₁ t := by
    simp only [u]
    rw [hframe _ (mem_frame_of_fst (by norm_num) (unitInterval.fract_mem t)), reparamDisc_fract,
      reparamDisc_one_left hgp₁ hγ₁]
  have hu_seam (s : ℝ) {t : ℝ} (ht : t = 0 ∨ t = 1) : u (s, t) = x := by
    rcases ht with rfl | rfl
    · simpa [u] using hseam s
    · simpa [u] using hseam s
  have hu_eq (s t : unitInterval) : u (s, t) = u₀ (s, t) := by
    rcases t.2.2.lt_or_eq with ht | ht
    · simp only [u, Int.fract_eq_self.2 ⟨t.2.1, ht⟩]
    · rw [hu_seam s (Or.inr ht), ht, hframe _ (mem_frame_of_snd ⟨zero_le_one, le_rfl⟩
        (by norm_num)), reparamDisc_seam P s (Or.inr rfl)]
  have hu := contMDiff_comp_fract hg₀ hgp₀ hγ₀ hg₁ hgp₁ hγ₁ P hu₀ hframe
  refine ⟨u, hu, fun z ↦ by simp [u, Int.fract_add_one], hu_left, hu_right, ?_⟩
  -- The path of loops of `u` is homotopic to that of `G` by smoothing, and so to `P`.
  let Pu : Path γ₀ γ₁ := Path.ofContinuousSquare (fun q ↦ u (q.1, q.2))
    (hu.continuous.comp (by fun_prop)) (fun t ↦ (hu_left t).trans (hγ₀ t).symm)
    (fun t ↦ (hu_right t).trans (hγ₁ t).symm)
    (fun s ↦ hu_seam s (Or.inl rfl)) (fun s ↦ hu_seam s (Or.inr rfl))
  let PG : Path γ₀ γ₁ := Path.ofContinuousSquare (fun q ↦ G (q.1, q.2)) (by fun_prop)
    (fun t ↦ (reparamDisc_zero_left hgp₀ hγ₀ P t).trans (hγ₀ t).symm)
    (fun t ↦ (reparamDisc_one_left hgp₁ hγ₁ P t).trans (hγ₁ t).symm)
    (fun s ↦ reparamDisc_seam P s (Or.inl rfl)) (fun s ↦ reparamDisc_seam P s (Or.inr rfl))
  refine ⟨Pu, fun s t ↦ Path.ofContinuousSquare_apply s t, ?_⟩
  have hPG : P.Homotopic PG :=
    homotopic_reparamDisc P PG fun s t ↦ Path.ofContinuousSquare_apply s t
  have hPu : PG.Homotopic Pu :=
    homotopic_of_homotopicRel hGu₀ (fun s t ↦ Path.ofContinuousSquare_apply s t)
      fun s t ↦ (Path.ofContinuousSquare_apply s t).trans (hu_eq s t)
  exact (hPG.trans hPu).symm

end TauCeti
