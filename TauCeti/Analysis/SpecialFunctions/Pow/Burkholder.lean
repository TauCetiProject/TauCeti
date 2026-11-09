/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Convex.Piecewise

/-!
# Burkholder's function and the scalar Bellman estimates

For a real exponent `p`, Burkholder's function is
`Φ_p(x, y) = (x + y) ^ (p - 1) * ((p - 1) * x - y)`, evaluated at nonnegative arguments.
For `2 ≤ p` it satisfies the two scalar Bellman estimates behind Burkholder's proof that martingale
difference sequences, and in particular the Haar system, are unconditional in `Lᵖ`:

* a majorization: `((p - 1) ^ (p - 1) / p ^ (p - 2)) * Φ_p(x, y) ≤ (p - 1) ^ p * x ^ p - y ^ p`
  for `x, y ≥ 0`;
* a zigzag convexity: for real `x`, `y` and `ε = ±1`, the function
  `t ↦ Φ_p(|x + t|, |y + ε t|)` is convex, so that
  `Φ_p(|x + a|, |y + ε a|) + Φ_p(|x - a|, |y - ε a|) ≥ 2 Φ_p(|x|, |y|)`.

Up to the factor `-(p - 1) ^ (p - 1) / p ^ (p - 2)`, `Φ_p(|x|, |y|)` is the function `U` of
Burkholder for the exponent `p ≥ 2`, and the two estimates are `V ≤ U` and the concavity of `U`
along lines of slope `±1`, where `V(x, y) = |y| ^ p - (p - 1) ^ p |x| ^ p`. Integrated over
dyadic intervals, the midpoint inequality is the scalar input to the bound `p - 1` for Haar sign
transforms on `Lᵖ([0, 1])`.

## Main definitions and statements

* `TauCeti.burkholderPhi p x y`: the function `Φ_p(x, y)`.
* `TauCeti.burkholderPhi_mul_mul`: positive homogeneity of degree `p`.
* `TauCeti.mul_burkholderPhi_le`: the majorization estimate.
* `TauCeti.convexOn_burkholderPhi_abs_add`: convexity of `t ↦ Φ_p(|x + t|, |y + ε t|)`.
* `TauCeti.two_mul_burkholderPhi_abs_le`: the midpoint inequality.

## References

* D. L. Burkholder, *Boundary value problems and sharp inequalities for martingale transforms*,
  Ann. Probab. **12** (1984), 647–702.
* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, 2nd ed., Graduate Texts in
  Mathematics 233, Springer, 2016, §6.1 (Lemmas 6.1.5 and 6.1.6).
-/

public section

namespace TauCeti

open Set

/-- Burkholder's function `Φ_p(x, y) = (x + y) ^ (p - 1) * ((p - 1) * x - y)`. It is intended for
nonnegative arguments, typically `x = |f|` and `y = |g|` for a function `f` and a transform `g`
of it. -/
noncomputable def burkholderPhi (p x y : ℝ) : ℝ := (x + y) ^ (p - 1) * ((p - 1) * x - y)

/-- The defining formula for Burkholder's function. -/
theorem burkholderPhi_def (p x y : ℝ) :
    burkholderPhi p x y = (x + y) ^ (p - 1) * ((p - 1) * x - y) := (rfl)

/-- Burkholder's function vanishes at the origin, for every exponent `p`. -/
@[simp]
theorem burkholderPhi_zero_zero (p : ℝ) : burkholderPhi p 0 0 = 0 := by
  simp [burkholderPhi_def]

variable {p : ℝ}

/-- Burkholder's function is positively homogeneous of degree `p`:
`Φ_p(c x, c y) = c ^ p Φ_p(x, y)` for `c ≥ 0` and `x + y ≥ 0`. -/
theorem burkholderPhi_mul_mul (hp : p ≠ 0) {c x y : ℝ} (hc : 0 ≤ c) (hxy : 0 ≤ x + y) :
    burkholderPhi p (c * x) (c * y) = c ^ p * burkholderPhi p x y := by
  have hpow : c ^ p = c ^ (p - 1) * c := by
    rw [← Real.rpow_add_one' hc (by simpa using hp)]
    ring_nf
  rw [burkholderPhi_def, burkholderPhi_def, ← mul_add, Real.mul_rpow hc hxy, hpow]
  ring

/-! ### The majorization estimate -/

/-- For `2 ≤ p`, the constant `(p - 1) ^ (p - 1) / p ^ (p - 2)` is at least `1`. -/
private theorem one_le_burkholderConst (hp : 2 ≤ p) : 1 ≤ (p - 1) ^ (p - 1) / p ^ (p - 2) := by
  have hp₀ : 0 < p := by linarith
  have hp₁ : 0 < p - 1 := by linarith
  rw [one_le_div (Real.rpow_pos_of_pos hp₀ _), Real.rpow_def_of_pos hp₀, Real.rpow_def_of_pos hp₁,
    Real.exp_le_exp]
  -- `(p - 2) (log p - log (p - 1)) ≤ (p - 2) / (p - 1) = 1 - 1 / (p - 1) ≤ log (p - 1)`.
  have h₁ : Real.log p - Real.log (p - 1) ≤ (p - 1)⁻¹ := by
    rw [← Real.log_div hp₀.ne' hp₁.ne']
    calc _ ≤ p / (p - 1) - 1 := Real.log_le_sub_one_of_pos (div_pos hp₀ hp₁)
      _ = (p - 1)⁻¹ := by field_simp; ring
  have h₂ : 1 - (p - 1)⁻¹ ≤ Real.log (p - 1) := Real.one_sub_inv_le_log_of_pos hp₁
  have h₃ : (p - 2) * (Real.log p - Real.log (p - 1)) ≤ (p - 2) * (p - 1)⁻¹ :=
    mul_le_mul_of_nonneg_left h₁ (by linarith)
  have h₄ : (p - 2) * (p - 1)⁻¹ = 1 - (p - 1)⁻¹ := by field_simp; ring
  linarith

/-- The function `k(s) = (p - 1) ^ p s ^ (p - 1) + (1 - s) ^ (p - 1)` crosses the constant
`c = (p - 1) ^ (p - 1) / p ^ (p - 2)` at `s = 1 / p`: on `[0, 1]` it is at most `c` before `1 / p`
and at least `c` after, because it is convex with `k(0) = 1 ≤ c = k(1 / p)`. -/
private theorem burkholderConst_sign (hp : 2 ≤ p) {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    (s ≤ 1 / p →
      (p - 1) ^ p * s ^ (p - 1) + (1 - s) ^ (p - 1) ≤ (p - 1) ^ (p - 1) / p ^ (p - 2)) ∧
    (1 / p ≤ s →
      (p - 1) ^ (p - 1) / p ^ (p - 2) ≤ (p - 1) ^ p * s ^ (p - 1) + (1 - s) ^ (p - 1)) := by
  set c := (p - 1) ^ (p - 1) / p ^ (p - 2) with hc
  set k : ℝ → ℝ := fun s => (p - 1) ^ p * s ^ (p - 1) + (1 - s) ^ (p - 1) with hk
  have hp₀ : 0 < p := by linarith
  have hp₁ : 0 < p - 1 := by linarith
  have hc₁ : 1 ≤ c := one_le_burkholderConst hp
  have hp₁' : 1 / p ≤ 1 := (div_le_one hp₀).2 (by linarith)
  have hkconv : ConvexOn ℝ (Icc 0 1) k := by
    have h₁ : ConvexOn ℝ (Icc 0 1) fun s : ℝ => s ^ (p - 1) :=
      (convexOn_rpow (by linarith)).subset Icc_subset_Ici_self (convex_Icc 0 1)
    have h₂ : ConvexOn ℝ (Icc 0 1) fun s : ℝ => (1 - s) ^ (p - 1) := by
      refine (((convexOn_rpow (p := p - 1) (by linarith)).comp_affineMap
        (AffineMap.lineMap (1 : ℝ) 0)).subset (fun s hs => ?_) (convex_Icc 0 1)).congr
        fun s _ => ?_ <;>
      simp only [mem_preimage, mem_Ici, Function.comp_apply, AffineMap.lineMap_apply_ring']
      · linarith [hs.2]
      · ring_nf
    exact (h₁.smul (Real.rpow_nonneg hp₁.le _)).add h₂
  have hk₀ : k 0 = 1 := by simp [hk, Real.zero_rpow hp₁.ne']
  have hkp : k (1 / p) = c := by
    have e₁ : (p - 1) ^ p = (p - 1) ^ (p - 1) * (p - 1) := by
      rw [← Real.rpow_add_one hp₁.ne']
      ring_nf
    have e₂ : p ^ (p - 1) = p ^ (p - 2) * p := by
      rw [← Real.rpow_add_one hp₀.ne']
      ring_nf
    have e₃ : 1 - 1 / p = (p - 1) / p := by field_simp
    simp only [hk, hc, e₃, Real.div_rpow zero_le_one hp₀.le, Real.div_rpow hp₁.le hp₀.le,
      Real.one_rpow, e₁, e₂]
    have : 0 < p ^ (p - 2) := Real.rpow_pos_of_pos hp₀ _
    field_simp
    ring
  refine ⟨fun hsp => ?_, fun hsp => ?_⟩
  · -- `k s ≤ max (k 0) (k (1 / p)) = c`.
    have hks := hkconv.le_on_segment (x := 0) (y := 1 / p) ⟨le_rfl, zero_le_one⟩
      ⟨by positivity, hp₁'⟩ (by rw [segment_eq_Icc (by positivity)]; exact ⟨hs₀, hsp⟩)
    rwa [hk₀, hkp, max_eq_right hc₁] at hks
  · -- The slope of `k` on `[1 / p, s]` is at least its slope on `[0, 1 / p]`, which is `≥ 0`.
    rcases hsp.eq_or_lt with rfl | hsp
    · exact hkp.ge
    have hks := hkconv.slope_mono_adjacent (x := 0) (y := 1 / p) (z := s) ⟨le_rfl, zero_le_one⟩
      ⟨hs₀, hs₁⟩ (by positivity) hsp
    rw [hk₀, hkp] at hks
    have : 0 ≤ (k s - c) / (s - 1 / p) :=
      (div_nonneg (by linarith) (by rw [sub_zero]; positivity)).trans hks
    rw [le_div_iff₀ (sub_pos.2 hsp), zero_mul, sub_nonneg] at this
    exact this

/-- The majorization estimate on the segment `x + y = 1`, `x = s`: for `0 ≤ s ≤ 1`,
`((p - 1) ^ (p - 1) / p ^ (p - 2)) (p s - 1) ≤ (p - 1) ^ p s ^ p - (1 - s) ^ p`. -/
private theorem burkholderConst_mul_le (hp : 2 ≤ p) {s : ℝ} (hs₀ : 0 ≤ s) (hs₁ : s ≤ 1) :
    (p - 1) ^ (p - 1) / p ^ (p - 2) * (p * s - 1) ≤ (p - 1) ^ p * s ^ p - (1 - s) ^ p := by
  set c := (p - 1) ^ (p - 1) / p ^ (p - 2) with hc
  have hp₀ : 0 < p := by linarith
  have hp₁ : 0 < p - 1 := by linarith
  -- `F(s) = (p - 1) ^ p s ^ p - (1 - s) ^ p - c (p s - 1)` has derivative `p (k(s) - c)`, with `k`
  -- as in `burkholderConst_sign`. Hence `F` decreases on `[0, 1 / p]`, increases on `[1 / p, 1]`,
  -- and vanishes at `1 / p`.
  set F : ℝ → ℝ := fun s => (p - 1) ^ p * s ^ p - (1 - s) ^ p - c * (p * s - 1) with hF
  have hF' : ∀ s, HasDerivAt F
      (p * ((p - 1) ^ p * s ^ (p - 1) + (1 - s) ^ (p - 1) - c)) s := by
    intro s
    have ha := Real.hasDerivAt_rpow_const (x := s) (p := p) (Or.inr (by linarith))
    have hb : HasDerivAt (fun s => (1 - s) ^ p) (-1 * p * (1 - s) ^ (p - 1)) s := by
      simpa using ((hasDerivAt_id' s).const_sub 1).rpow_const (p := p) (Or.inr (by linarith))
    convert ((ha.const_mul ((p - 1) ^ p)).sub hb).sub
      ((((hasDerivAt_id' s).const_mul p).sub_const 1).const_mul c) using 1
    ring
  have hFc : Continuous F := by
    simp only [hF]
    fun_prop (disch := linarith)
  have hFp : F (1 / p) = 0 := by
    have e₃ : 1 - 1 / p = (p - 1) / p := by field_simp
    simp only [hF, e₃, Real.div_rpow zero_le_one hp₀.le, Real.div_rpow hp₁.le hp₀.le,
      Real.one_rpow]
    field_simp
    ring
  have hp₁' : 1 / p ≤ 1 := (div_le_one hp₀).2 (by linarith)
  suffices 0 ≤ F s by simp only [hF] at this; linarith
  rw [← hFp]
  rcases le_total s (1 / p) with hsp | hsp
  · refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 (1 / p)) hFc.continuousOn
      (fun x _ => (hF' x).hasDerivWithinAt) (fun x hx => ?_) ⟨hs₀, hsp⟩
      ⟨by positivity, le_rfl⟩ hsp
    rw [interior_Icc] at hx
    have := (burkholderConst_sign hp hx.1.le (hx.2.le.trans hp₁')).1 hx.2.le
    exact mul_nonpos_of_nonneg_of_nonpos hp₀.le (by linarith)
  · refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (1 / p) 1) hFc.continuousOn
      (fun x _ => (hF' x).hasDerivWithinAt) (fun x hx => ?_) ⟨le_rfl, hp₁'⟩ ⟨hsp, hs₁⟩ hsp
    rw [interior_Icc] at hx
    have := (burkholderConst_sign hp ((by positivity : (0 : ℝ) ≤ 1 / p).trans hx.1.le)
      hx.2.le).2 hx.1.le
    exact mul_nonneg hp₀.le (by linarith)

/-- **The scalar Bellman majorization estimate.** For `2 ≤ p` and `x, y ≥ 0`,
`((p - 1) ^ (p - 1) / p ^ (p - 2)) Φ_p(x, y) ≤ (p - 1) ^ p x ^ p - y ^ p`. -/
theorem mul_burkholderPhi_le (hp : 2 ≤ p) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (p - 1) ^ (p - 1) / p ^ (p - 2) * burkholderPhi p x y ≤ (p - 1) ^ p * x ^ p - y ^ p := by
  have hp₀ : 0 < p := by linarith
  rcases (add_nonneg hx hy).eq_or_lt with h | hσ
  · obtain ⟨rfl, rfl⟩ : x = 0 ∧ y = 0 := ⟨by linarith, by linarith⟩
    simp [burkholderPhi_def, Real.zero_rpow hp₀.ne']
  -- Write `x = σ s` and `y = σ (1 - s)` with `σ = x + y`, and use homogeneity of degree `p`.
  set σ := x + y with hσ_def
  have hxs : x = σ * (x / σ) := by field_simp
  have hys : y = σ * (1 - x / σ) := by field_simp; ring
  have hs₀ : 0 ≤ x / σ := div_nonneg hx hσ.le
  have hs₁ : x / σ ≤ 1 := (div_le_one hσ).2 (by linarith)
  have hΦ : burkholderPhi p x y = σ ^ p * (p * (x / σ) - 1) := by
    rw [burkholderPhi_def, ← hσ_def, Real.rpow_sub_one hσ.ne']
    field_simp
    ring
  have key := mul_le_mul_of_nonneg_left (burkholderConst_mul_le hp hs₀ hs₁)
    (Real.rpow_nonneg hσ.le p)
  have ex : x ^ p = σ ^ p * (x / σ) ^ p := by rw [← Real.mul_rpow hσ.le hs₀, ← hxs]
  have ey : y ^ p = σ ^ p * (1 - x / σ) ^ p := by
    rw [← Real.mul_rpow hσ.le (by linarith), ← hys]
  rw [hΦ, ex, ey]
  linarith

/-! ### Convexity along the diagonal -/

/-- The derivative of `u ↦ Φ_p(u, u + e)` where the base `2u + e` is nonnegative. -/
private theorem hasDerivAt_burkholderPhi_self_add (hp : 2 ≤ p) {e u : ℝ} (hu : 0 ≤ 2 * u + e) :
    HasDerivAt (fun v => burkholderPhi p v (v + e))
      (p * (2 * u + e) ^ (p - 2) * (2 * (p - 2) * u - e)) u := by
  have h₁ : HasDerivAt (fun v => (2 * v + e) ^ (p - 1))
      (2 * (p - 1) * (2 * u + e) ^ (p - 1 - 1)) u := by
    simpa using (((hasDerivAt_id u).const_mul 2).add_const e).rpow_const
      (p := p - 1) (Or.inr (by linarith))
  have h₂ : HasDerivAt (fun v => (p - 2) * v - e) (p - 2) u := by
    simpa using ((hasDerivAt_id u).const_mul (p - 2)).sub_const e
  have hpow : (2 * u + e) ^ (p - 1) = (2 * u + e) ^ (p - 2) * (2 * u + e) := by
    rw [← Real.rpow_add_one' hu (by linarith)]
    ring_nf
  convert h₁.mul h₂ using 1
  · funext v
    rw [Pi.mul_apply, burkholderPhi_def, show v + (v + e) = 2 * v + e by ring]
    ring
  · rw [show p - 1 - 1 = p - 2 by ring, hpow]
    ring

/-- `u ↦ Φ_p(u, u + e)` is convex on `[a, ∞)` when `a ≥ 0` and `2a + e ≥ 0`: its second derivative
is `4p(p - 1)(p - 2) u (2u + e) ^ (p - 3)`. -/
private theorem convexOn_burkholderPhi_self_add (hp : 2 ≤ p) {e a : ℝ} (ha : 0 ≤ a)
    (hae : 0 ≤ 2 * a + e) : ConvexOn ℝ (Ici a) (fun v => burkholderPhi p v (v + e)) := by
  have hpos : ∀ u ∈ Ioi a, 0 < 2 * u + e := fun u hu => by linarith [mem_Ioi.1 hu]
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Ici a)
    (f' := fun u => p * (2 * u + e) ^ (p - 2) * (2 * (p - 2) * u - e))
    (f'' := fun u => 4 * p * (p - 1) * (p - 2) * u * (2 * u + e) ^ (p - 3))
    (fun u hu => (hasDerivAt_burkholderPhi_self_add hp
      (by linarith [mem_Ici.1 hu])).continuousAt.continuousWithinAt) ?_ ?_ ?_ <;>
    simp only [interior_Ici]
  · exact fun u hu => (hasDerivAt_burkholderPhi_self_add hp (hpos u hu).le).hasDerivWithinAt
  · intro u hu
    have hu' := hpos u hu
    have h₁ : HasDerivAt (fun v => (2 * v + e) ^ (p - 2))
        (2 * (p - 2) * (2 * u + e) ^ (p - 2 - 1)) u := by
      simpa using (((hasDerivAt_id u).const_mul 2).add_const e).rpow_const
        (p := p - 2) (Or.inl hu'.ne')
    have h₂ : HasDerivAt (fun v => 2 * (p - 2) * v - e) (2 * (p - 2)) u := by
      simpa using ((hasDerivAt_id u).const_mul (2 * (p - 2))).sub_const e
    have hpow : (2 * u + e) ^ (p - 2) = (2 * u + e) ^ (p - 3) * (2 * u + e) := by
      rw [← Real.rpow_add_one hu'.ne']
      ring_nf
    refine HasDerivAt.hasDerivWithinAt ?_
    convert (h₁.const_mul p).mul h₂ using 1
    · rw [show p - 2 - 1 = p - 3 by ring, hpow]
      ring
  · intro u hu
    have hu₀ : 0 ≤ u := ha.trans (mem_Ioi.1 hu).le
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith))
      (by linarith)) hu₀) (Real.rpow_nonneg (hpos u hu).le _)

/-- For `d ≥ 0`, the function `u ↦ Φ_p(|u|, |u + d|)` is convex on `ℝ`. It is given by
`u ↦ Φ_p(-u, -u - d)` on `(-∞, -d]`, is affine on `[-d, 0]` and is `u ↦ Φ_p(u, u + d)` on
`[0, ∞)`; the derivative is continuous at `0` and jumps up at `-d`. -/
private theorem convexOn_burkholderPhi_abs_abs_add_of_nonneg (hp : 2 ≤ p) {d : ℝ} (hd : 0 ≤ d) :
    ConvexOn ℝ univ (fun u => burkholderPhi p |u| |u + d|) := by
  -- The piece on `(-∞, -d]` is the reflection of `v ↦ Φ_p(v, v - d)` on `[d, ∞)`.
  have hL : ConvexOn ℝ (Iic (-d)) (fun u => burkholderPhi p (-u) (-u + -d)) := by
    convert (convexOn_burkholderPhi_self_add hp (e := -d) hd (by linarith)).comp_linearMap
      (-LinearMap.id) using 1
    · ext u
      simp [le_neg]
    · funext u
      simp
  have hL' : HasDerivAt (fun u => burkholderPhi p (-u) (-u + -d))
      (p * (2 * d + -d) ^ (p - 2) * (2 * (p - 2) * d - -d) * -1) (-d) :=
    (hasDerivAt_burkholderPhi_self_add hp (by linarith)).comp_of_eq (-d) (hasDerivAt_neg (-d))
      (neg_neg d).symm
  have hEqL : EqOn (fun u => burkholderPhi p |u| |u + d|)
      (fun u => burkholderPhi p (-u) (-u + -d)) (Iic (-d)) := fun u hu => by
    have hu := mem_Iic.1 hu
    simp only
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), neg_add]
  -- The piece on `[0, ∞)`.
  have hR : ConvexOn ℝ (Ici 0) (fun u => burkholderPhi p |u| (u + d)) :=
    (convexOn_burkholderPhi_self_add hp le_rfl (by linarith)).congr fun u hu => by
      simp only [abs_of_nonneg (mem_Ici.1 hu)]
  have hR' : HasDerivWithinAt (fun u => burkholderPhi p |u| (u + d))
      (p * (2 * 0 + d) ^ (p - 2) * (2 * (p - 2) * 0 - d)) (Ici 0) 0 :=
    (hasDerivAt_burkholderPhi_self_add hp (by linarith)).hasDerivWithinAt.congr_of_mem
      (fun u hu => by simp only [abs_of_nonneg (mem_Ici.1 hu)]) self_mem_Ici
  rcases hd.eq_or_lt with rfl | hd
  · -- For `d = 0` the two pieces meet at `0`, where both one-sided derivatives vanish.
    rw [neg_zero] at hL hL' hEqL
    refine convexOn_univ_of_convexOn_Iic_Ici (a := 0) (hL.congr hEqL.symm)
      (hR.congr fun u hu => by simp [abs_of_nonneg (mem_Ici.1 hu)])
      (hL'.hasDerivWithinAt.congr_of_mem hEqL self_mem_Iic)
      (hR'.congr_of_mem (fun u hu => by simp [abs_of_nonneg (mem_Ici.1 hu)]) self_mem_Ici) ?_
    simp
  -- For `d > 0` the function `u ↦ Φ_p(|u|, u + d)` is affine on `(-∞, 0]`.
  set A : ℝ → ℝ := fun u => d ^ (p - 1) * (-p * u - d) with hA_def
  have hA : ConvexOn ℝ (Iic 0) A := ⟨convex_Iic 0, fun x _ y _ a b _ _ hab => le_of_eq <| by
    simp only [hA_def, smul_eq_mul]
    linear_combination (d ^ (p - 1) * d) * hab⟩
  have hA' : ∀ x, HasDerivAt A (d ^ (p - 1) * -p) x := fun x =>
    ((((hasDerivAt_id' x).const_mul (-p)).sub_const d).const_mul (d ^ (p - 1))).congr_deriv
      (by ring)
  have hEqA : EqOn (fun u => burkholderPhi p |u| (u + d)) A (Iic 0) := fun u hu => by
    simp only [hA_def]
    rw [burkholderPhi_def, abs_of_nonpos (mem_Iic.1 hu), show -u + (u + d) = d by ring]
    ring
  have hpow : d ^ (p - 1) = d ^ (p - 2) * d := by
    rw [← Real.rpow_add_one hd.ne']
    ring_nf
  -- Gluing at `0`, where the derivative is continuous.
  have hR₀ : ConvexOn ℝ univ (fun u => burkholderPhi p |u| (u + d)) :=
    convexOn_univ_of_convexOn_Iic_Ici (a := 0) (hA.congr hEqA.symm) hR
      ((hA' 0).hasDerivWithinAt.congr_of_mem hEqA self_mem_Iic) hR'
      (le_of_eq (by rw [hpow, mul_zero, zero_add]; ring))
  -- Gluing at `-d`, where the derivative jumps up.
  have hEqR : EqOn (fun u => burkholderPhi p |u| |u + d|)
      (fun u => burkholderPhi p |u| (u + d)) (Ici (-d)) := fun u hu => by
    simp only [abs_of_nonneg (show 0 ≤ u + d by linarith [mem_Ici.1 hu])]
  have hRd : HasDerivAt (fun u => burkholderPhi p |u| (u + d)) (d ^ (p - 1) * -p) (-d) :=
    (hA' (-d)).congr_of_eventuallyEq <| Filter.eventually_of_mem (Iio_mem_nhds (by linarith))
      fun u hu => hEqA (mem_Iic.2 (mem_Iio.1 hu).le)
  refine convexOn_univ_of_convexOn_Iic_Ici (a := -d) (hL.congr hEqL.symm)
    ((hR₀.subset (subset_univ _) (convex_Ici _)).congr hEqR.symm)
    (hL'.hasDerivWithinAt.congr_of_mem hEqL self_mem_Iic)
    (hRd.hasDerivWithinAt.congr_of_mem hEqR self_mem_Ici) ?_
  have hX : 0 ≤ d ^ (p - 2) * d := mul_nonneg (Real.rpow_nonneg hd.le _) hd.le
  rw [hpow, show 2 * d + -d = d by ring]
  nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ p) hX) (by linarith : (0 : ℝ) ≤ p - 2)]

/-- **Zigzag convexity of Burkholder's function.** For `2 ≤ p`, real `x`, `y` and `ε` with
`|ε| = 1`, the function `t ↦ Φ_p(|x + t|, |y + ε t|)` is convex on `ℝ`. -/
theorem convexOn_burkholderPhi_abs_add (hp : 2 ≤ p) (x y : ℝ) {ε : ℝ} (hε : |ε| = 1) :
    ConvexOn ℝ univ fun t => burkholderPhi p |x + t| |y + ε * t| := by
  -- Reduce to `u ↦ Φ_p(|u|, |u + d|)` for real `d`, and then to `d ≥ 0` by the reflection `u ↦ -u`.
  have key : ∀ d : ℝ, ConvexOn ℝ univ fun u => burkholderPhi p |u| |u + d| := by
    intro d
    rcases le_total 0 d with hd | hd
    · exact convexOn_burkholderPhi_abs_abs_add_of_nonneg hp hd
    · convert (convexOn_burkholderPhi_abs_abs_add_of_nonneg hp (neg_nonneg.2 hd)).comp_linearMap
        (-LinearMap.id) using 1
      · simp
      · funext u
        simp only [Function.comp_apply, LinearMap.neg_apply, LinearMap.id_apply, abs_neg,
          ← neg_add]
  rcases (abs_eq zero_le_one).1 hε with rfl | rfl
  · convert (key (y - x)).translate_right x using 1
    · simp
    · funext t
      simp only [Function.comp_apply]
      rw [show x + t + (y - x) = y + 1 * t by ring]
  · convert (key (-y - x)).translate_right x using 1
    · simp
    · funext t
      simp only [Function.comp_apply]
      rw [show x + t + (-y - x) = -(y + -1 * t) by ring, abs_neg]

/-- **The scalar Bellman midpoint estimate.** For `2 ≤ p`, real `x`, `y`, `a` and `ε` with
`|ε| = 1`, `2 Φ_p(|x|, |y|) ≤ Φ_p(|x + a|, |y + ε a|) + Φ_p(|x - a|, |y - ε a|)`. -/
theorem two_mul_burkholderPhi_abs_le (hp : 2 ≤ p) (x y a : ℝ) {ε : ℝ} (hε : |ε| = 1) :
    2 * burkholderPhi p |x| |y| ≤
      burkholderPhi p |x + a| |y + ε * a| + burkholderPhi p |x - a| |y - ε * a| := by
  have h := (convexOn_burkholderPhi_abs_add hp x y hε).2 (mem_univ a) (mem_univ (-a))
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul, mul_neg, ← sub_eq_add_neg, sub_self, mul_zero, add_zero] at h
  linarith

end TauCeti
