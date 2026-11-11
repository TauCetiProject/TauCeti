/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Concat
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Continuity
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.StarConvex
import TauCeti.Analysis.Contour.Winding.Number.Segment.Jump
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Gluing

/-!
# Winding-number jump across a regular point of an absolutely continuous curve

If an absolutely continuous curve `γ` on `[a, b]` (`a < b`) is differentiable at an interior
parameter `t₀ ∈ (a, b)` with nonzero derivative `v ≠ 0` and visits `γ t₀` nowhere else on `[a, b]`,
then the difference of winding numbers across the normal line at `γ t₀`,
`windingNumber γ a b (γ t₀ + h • (I * v)) - windingNumber γ a b (γ t₀ - h • (I * v))`,
tends to `1` as `h → 0⁺`. When `γ` is closed (`γ a = γ b`), integer-valuedness of the off-trace
winding number upgrades this limit to exact equality `= + 1` for all sufficiently small `h > 0`.

Unlike `TauCeti.Contour.exists_forall_windingNumber_eq_add_one_of_eqOn_segment`, the curve need not
contain a straight segment: near `t₀` the Fréchet derivative confines both `γ` and a three-piece
polygonal tangent replacement to the complement of each normal ray `γ t₀ ± (0, ∞) • (I * v)`, which
is star-shaped about `γ t₀`. Star-convex homotopy invariance replaces the local arc of `γ` by that
polygonal replacement, reducing the jump to `tendsto_windingNumber_segment_sub`.

## Main results

* `AbsolutelyContinuousOnInterval.tendsto_windingNumber_add_I_mul_sub`: the normal-crossing
  difference of winding numbers tends to `1` as `h → 0⁺`.
* `AbsolutelyContinuousOnInterval.eventually_windingNumber_add_I_mul_eq_add_one_of_forall_eq`:
  for a closed absolutely continuous curve visiting `γ t₀` only at `t₀`, the winding number on the
  left normal ray eventually exceeds that on the right normal ray by `1`.
* `AbsolutelyContinuousOnInterval.eventually_windingNumber_add_I_mul_eq_add_one`: specialization to
  simple closed absolutely continuous curves (`InjOn γ (Ico a b)`).

## References

* L. Ahlfors, *Complex Analysis*, Chapter 4, §2.
* R. B. Burckel, *An Introduction to Classical Complex Analysis*, Vol. 1, Chapter IV.
-/

public section

open Complex Filter MeasureTheory Metric Set
open scoped Topology

namespace TauCeti.Contour

section Helpers

/-- The plane slit along an open normal ray `{w | ((w - p) / v).re = 0 ∧ 0 < σ * ((w - p) / v).im}`.
It contains the basepoint `p` and is star-shaped about `p`. -/
private def slitCompl (p v : ℂ) (σ : ℝ) : Set ℂ :=
  {w : ℂ | ((w - p) / v).re ≠ 0 ∨ σ * ((w - p) / v).im ≤ 0}

private theorem starConvex_slitCompl (p v : ℂ) (σ : ℝ) :
    StarConvex ℝ p (slitCompl p v σ) := by
  intro y hy r s _ hs hrs
  have hdiv : (r • p + s • y - p) / v = (s : ℂ) * ((y - p) / v) := by
    have hr' : r = 1 - s := by linarith
    rw [hr', sub_smul, one_smul, Complex.real_smul, Complex.real_smul]
    ring
  rcases hs.eq_or_lt with rfl | hs_pos
  · right; rw [hdiv]; simp
  · rcases hy with hre | him
    · left
      rw [hdiv, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
      exact mul_ne_zero hs_pos.ne' hre
    · right
      rw [hdiv, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
      nlinarith

private theorem self_mem_slitCompl (p v : ℂ) (σ : ℝ) : p ∈ slitCompl p v σ :=
  Or.inr (by simp)

private theorem notMem_slitCompl_smul {p v : ℂ} {σ h : ℝ} (hv : v ≠ 0)
    (hσ : 0 < σ ^ 2) (hh : 0 < h) :
    p + (σ * h) • (I * v) ∉ slitCompl p v σ := by
  have hdiv : (p + (σ * h) • (I * v) - p) / v = ((σ * h : ℝ) : ℂ) * I := by
    rw [Complex.real_smul]; field_simp; ring
  rintro (hre | him)
  · rw [hdiv] at hre; exact hre (by simp)
  · rw [hdiv] at him
    simp only [mul_im, ofReal_re, ofReal_im, I_re, I_im, mul_one, mul_zero, add_zero] at him
    nlinarith

private theorem notMem_slitCompl_add_smul {p v : ℂ} {h : ℝ} (hv : v ≠ 0) (hh : 0 < h) :
    p + h • (I * v) ∉ slitCompl p v 1 := by
  simpa using notMem_slitCompl_smul (p := p) hv (by norm_num : (0 : ℝ) < 1 ^ 2) hh

private theorem notMem_slitCompl_sub_smul {p v : ℂ} {h : ℝ} (hv : v ≠ 0) (hh : 0 < h) :
    p - h • (I * v) ∉ slitCompl p v (-1) := by
  simpa [sub_eq_add_neg, neg_smul] using
    notMem_slitCompl_smul (p := p) hv (by norm_num : (0 : ℝ) < (-1 : ℝ) ^ 2) hh

/-- Three-segment polygonal curve on `[t₀ - δ, t₀ + δ]` matching `γ` at `t₀ ± δ` and following the
exact tangent line `t ↦ γ t₀ + (t - t₀) • v` on `[t₀ - δ / 2, t₀ + δ / 2]`. -/
private noncomputable def localTangentCurve (γ : ℝ → ℂ) (t₀ δ : ℝ) (v : ℂ) (t : ℝ) : ℂ :=
  if t ≤ t₀ - δ / 2 then
    γ (t₀ - δ) + ((t - (t₀ - δ)) / (δ / 2)) • ((γ t₀ - (δ / 2) • v) - γ (t₀ - δ))
  else if t ≤ t₀ + δ / 2 then
    v * (t : ℂ) + (γ t₀ - v * (t₀ : ℂ))
  else
    (γ t₀ + (δ / 2) • v) + ((t - (t₀ + δ / 2)) / (δ / 2)) • (γ (t₀ + δ) - (γ t₀ + (δ / 2) • v))

private theorem eqOn_localTangentCurve_left {γ : ℝ → ℂ} {t₀ δ : ℝ} {v : ℂ} :
    EqOn (localTangentCurve γ t₀ δ v)
      (fun t : ℝ ↦ γ (t₀ - δ) + ((t - (t₀ - δ)) / (δ / 2)) • ((γ t₀ - (δ / 2) • v) - γ (t₀ - δ)))
      (Icc (t₀ - δ) (t₀ - δ / 2)) :=
  fun _ ht ↦ by simp only [localTangentCurve, ht.2, ↓reduceIte]

private theorem eqOn_localTangentCurve_mid {γ : ℝ → ℂ} {t₀ δ : ℝ} {v : ℂ} (hδ : 0 < δ) :
    EqOn (localTangentCurve γ t₀ δ v) (fun t : ℝ ↦ v * (t : ℂ) + (γ t₀ - v * (t₀ : ℂ)))
      (Icc (t₀ - δ / 2) (t₀ + δ / 2)) := by
  intro t ht
  by_cases hle : t ≤ t₀ - δ / 2
  · have ht_eq : t = t₀ - δ / 2 := le_antisymm hle ht.1
    subst ht_eq
    have h1 : t₀ - δ / 2 - (t₀ - δ) = δ / 2 := by ring
    simp only [localTangentCurve, le_rfl, ↓reduceIte, h1, div_self (half_pos hδ).ne', one_smul,
      Complex.real_smul, ofReal_sub, ofReal_div, ofReal_ofNat]
    ring
  · simp only [localTangentCurve, hle, ht.2, ↓reduceIte]

private theorem eqOn_localTangentCurve_right {γ : ℝ → ℂ} {t₀ δ : ℝ} {v : ℂ} (hδ : 0 < δ) :
    EqOn (localTangentCurve γ t₀ δ v)
      (fun t : ℝ ↦ (γ t₀ + (δ / 2) • v) +
        ((t - (t₀ + δ / 2)) / (δ / 2)) • (γ (t₀ + δ) - (γ t₀ + (δ / 2) • v)))
      (Icc (t₀ + δ / 2) (t₀ + δ)) := by
  intro t ht
  have hnot₁ : ¬ t ≤ t₀ - δ / 2 := by linarith [ht.1, hδ]
  by_cases hle : t ≤ t₀ + δ / 2
  · have ht_eq : t = t₀ + δ / 2 := le_antisymm hle ht.1
    subst ht_eq
    simp only [localTangentCurve, hnot₁, le_rfl, ↓reduceIte, sub_self, zero_div, zero_smul,
      add_zero, Complex.real_smul, ofReal_add, ofReal_div, ofReal_ofNat]
    ring
  · simp only [localTangentCurve, hnot₁, hle, ↓reduceIte]

private theorem absolutelyContinuousOnInterval_localTangentCurve (γ : ℝ → ℂ) (t₀ : ℝ) {δ : ℝ}
    (v : ℂ) (hδ : 0 < δ) :
    AbsolutelyContinuousOnInterval (localTangentCurve γ t₀ δ v) (t₀ - δ) (t₀ - δ / 2) ∧
      AbsolutelyContinuousOnInterval (localTangentCurve γ t₀ δ v) (t₀ - δ / 2) (t₀ + δ / 2) ∧
      AbsolutelyContinuousOnInterval (localTangentCurve γ t₀ δ v) (t₀ + δ / 2) (t₀ + δ) := by
  have h₁ : t₀ - δ ≤ t₀ - δ / 2 := by linarith
  have h₂ : t₀ - δ / 2 ≤ t₀ + δ / 2 := by linarith
  have h₃ : t₀ + δ / 2 ≤ t₀ + δ := by linarith
  let d₁ : ℂ := (γ t₀ - (δ / 2) • v) - γ (t₀ - δ)
  let c₃ : ℂ := γ t₀ + (δ / 2) • v
  let d₃ : ℂ := γ (t₀ + δ) - c₃
  refine ⟨(TauCeti.absolutelyContinuousOnInterval_add_smul
      (γ (t₀ - δ) - ((t₀ - δ) / (δ / 2)) • d₁) ((δ / 2)⁻¹ • d₁) _ _).congr fun t ht ↦ ?_,
    (TauCeti.absolutelyContinuousOnInterval_add_smul
      (γ t₀ - v * (t₀ : ℂ)) v _ _).congr fun t ht ↦ ?_,
    (TauCeti.absolutelyContinuousOnInterval_add_smul
      (c₃ - ((t₀ + δ / 2) / (δ / 2)) • d₃) ((δ / 2)⁻¹ • d₃) _ _).congr fun t ht ↦ ?_⟩
  · rw [eqOn_localTangentCurve_left (uIcc_of_le h₁ ▸ ht)]
    dsimp only [d₁]; rw [← mul_smul, ← div_eq_mul_inv, sub_div t, sub_smul]; abel
  · rw [eqOn_localTangentCurve_mid hδ (uIcc_of_le h₂ ▸ ht)]
    dsimp only; rw [Complex.real_smul]; ring
  · rw [eqOn_localTangentCurve_right hδ (uIcc_of_le h₃ ▸ ht)]
    dsimp only [c₃, d₃]; rw [← mul_smul, ← div_eq_mul_inv, sub_div t, sub_smul]; abel

/-- On `[t₀ - δ, t₀ - δ / 2]` and `[t₀ + δ / 2, t₀ + δ]`, `localTangentCurve` has nonzero
tangential real coordinate, so it avoids `γ t₀` and stays in `slitCompl (γ t₀) v σ`. -/
private theorem re_localTangentCurve_ne_zero_left {γ : ℝ → ℂ} {t₀ δ : ℝ} {v : ℂ}
    (hv : v ≠ 0) (hδ : 0 < δ) (hleft : ((γ (t₀ - δ) - γ t₀) / v).re < 0)
    {t : ℝ} (ht : t ∈ Icc (t₀ - δ) (t₀ - δ / 2)) :
    ((localTangentCurve γ t₀ δ v t - γ t₀) / v).re < 0 := by
  rw [eqOn_localTangentCurve_left ht]
  set s : ℝ := (t - (t₀ - δ)) / (δ / 2)
  have hs0 : 0 ≤ s := div_nonneg (sub_nonneg.mpr ht.1) (half_pos hδ).le
  have hs1 : s ≤ 1 := (div_le_one (half_pos hδ)).mpr (by linarith [ht.2])
  have hlin : (γ (t₀ - δ) + s • ((γ t₀ - (δ / 2) • v) - γ (t₀ - δ)) - γ t₀) / v =
      ((1 - s : ℝ) : ℂ) * ((γ (t₀ - δ) - γ t₀) / v) + (s : ℂ) * (-(δ / 2) : ℝ) := by
    simp only [Complex.real_smul, ofReal_sub, ofReal_one, ofReal_neg, ofReal_div, ofReal_ofNat]
    field_simp; ring
  rw [hlin]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  rcases hs0.eq_or_lt with _ | _ <;> nlinarith

private theorem re_localTangentCurve_ne_zero_right {γ : ℝ → ℂ} {t₀ δ : ℝ} {v : ℂ}
    (hv : v ≠ 0) (hδ : 0 < δ) (hright : 0 < ((γ (t₀ + δ) - γ t₀) / v).re)
    {t : ℝ} (ht : t ∈ Icc (t₀ + δ / 2) (t₀ + δ)) :
    0 < ((localTangentCurve γ t₀ δ v t - γ t₀) / v).re := by
  rw [eqOn_localTangentCurve_right hδ ht]
  set s : ℝ := (t - (t₀ + δ / 2)) / (δ / 2)
  have hs0 : 0 ≤ s := div_nonneg (sub_nonneg.mpr ht.1) (half_pos hδ).le
  have hs1 : s ≤ 1 := (div_le_one (half_pos hδ)).mpr (by linarith [ht.2])
  have hlin : (γ t₀ + (δ / 2) • v + s • (γ (t₀ + δ) - (γ t₀ + (δ / 2) • v)) - γ t₀) / v =
      ((1 - s : ℝ) : ℂ) * ((δ / 2 : ℝ) : ℂ) + (s : ℂ) * ((γ (t₀ + δ) - γ t₀) / v) := by
    simp only [Complex.real_smul, ofReal_sub, ofReal_one, ofReal_div, ofReal_ofNat]
    field_simp; ring
  rw [hlin]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
  rcases hs0.eq_or_lt with _ | _ <;> nlinarith

private theorem localTangentCurve_mem_slitCompl {γ : ℝ → ℂ} {t₀ δ : ℝ} {v : ℂ}
    (hv : v ≠ 0) (hδ : 0 < δ) (hleft : ((γ (t₀ - δ) - γ t₀) / v).re < 0)
    (hright : 0 < ((γ (t₀ + δ) - γ t₀) / v).re) (σ : ℝ)
    {t : ℝ} (ht : t ∈ Icc (t₀ - δ) (t₀ + δ)) :
    localTangentCurve γ t₀ δ v t ∈ slitCompl (γ t₀) v σ := by
  rcases le_total t (t₀ - δ / 2) with h₁ | h₁
  · exact Or.inl (re_localTangentCurve_ne_zero_left hv hδ hleft ⟨ht.1, h₁⟩).ne
  · rcases le_total t (t₀ + δ / 2) with h₂ | h₂
    · rw [eqOn_localTangentCurve_mid hδ ⟨h₁, h₂⟩]; dsimp only
      rcases eq_or_ne t t₀ with rfl | htt₀
      · convert self_mem_slitCompl (γ t) v σ using 1; ring
      · left
        have hdiv : (v * (t : ℂ) + (γ t₀ - v * (t₀ : ℂ)) - γ t₀) / v = (t : ℂ) - t₀ := by
          field_simp; ring
        simpa [hdiv] using sub_ne_zero.mpr htt₀
    · exact Or.inl (re_localTangentCurve_ne_zero_right hv hδ hright ⟨h₂, ht.2⟩).ne'

/-- Decompose a winding-number difference across `[a, d]` (`a ≤ b ≤ c ≤ d`) into the sum of
winding-number differences across the three adjacent subintervals `[a, b]`, `[b, c]`, `[c, d]`. -/
private theorem windingNumber_sub_eq_add_three_of_notMem {γ : ℝ → ℂ} {a b c d : ℝ} {w₁ w₂ : ℂ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (h₁ : AbsolutelyContinuousOnInterval γ a b)
    (h₂ : AbsolutelyContinuousOnInterval γ b c)
    (h₃ : AbsolutelyContinuousOnInterval γ c d)
    (hw₁ : w₁ ∉ γ '' uIcc a d) (hw₂ : w₂ ∉ γ '' uIcc a d) :
    windingNumber γ a d w₁ - windingNumber γ a d w₂ =
      (windingNumber γ a b w₁ - windingNumber γ a b w₂) +
      (windingNumber γ b c w₁ - windingNumber γ b c w₂) +
      (windingNumber γ c d w₁ - windingNumber γ c d w₂) := by
  have hsub : ∀ {x y}, a ≤ x → x ≤ y → y ≤ d → uIcc x y ⊆ uIcc a d := fun hx hxy hy ↦ by
    rw [uIcc_of_le hxy, uIcc_of_le ((hab.trans hbc).trans hcd)]; exact Icc_subset_Icc hx hy
  have h₁d := hsub le_rfl hab (hbc.trans hcd)
  have hbd := hsub hab (hbc.trans hcd) le_rfl
  have h₂d := hsub hab hbc hcd
  have h₃d := hsub (hab.trans hbc) hcd le_rfl
  rw [h₁.windingNumber_concat (h₂.trans h₃)
      (mt (image_mono h₁d ·) hw₁) (mt (image_mono hbd ·) hw₁),
    h₂.windingNumber_concat h₃ (mt (image_mono h₂d ·) hw₁) (mt (image_mono h₃d ·) hw₁),
    h₁.windingNumber_concat (h₂.trans h₃)
      (mt (image_mono h₁d ·) hw₂) (mt (image_mono hbd ·) hw₂),
    h₂.windingNumber_concat h₃ (mt (image_mono h₂d ·) hw₂) (mt (image_mono h₃d ·) hw₂)]
  ring

/-- The winding-number normal jump of the local tangent curve `L` splits into the jumps on the two
outer pieces and the jump of the middle straight segment, once the test points `z₀ ± h • (I * v)`
miss the trace of `L` and `L` agrees with the segment on the middle piece. -/
private theorem eventuallyEq_windingNumber_sub_add_three {L : ℝ → ℂ} {t₀ δ : ℝ} {v z₀ : ℂ}
    (hδ : 0 < δ)
    (hac₁ : AbsolutelyContinuousOnInterval L (t₀ - δ) (t₀ - δ / 2))
    (hac₂ : AbsolutelyContinuousOnInterval L (t₀ - δ / 2) (t₀ + δ / 2))
    (hac₃ : AbsolutelyContinuousOnInterval L (t₀ + δ / 2) (t₀ + δ))
    (hoff_pos : ∀ {h : ℝ}, 0 < h → z₀ + h • (I * v) ∉ L '' uIcc (t₀ - δ) (t₀ + δ))
    (hoff_neg : ∀ {h : ℝ}, 0 < h → z₀ - h • (I * v) ∉ L '' uIcc (t₀ - δ) (t₀ + δ))
    (hmid_seg : ∀ w, windingNumber L (t₀ - δ / 2) (t₀ + δ / 2) w =
      windingNumber (fun t : ℝ ↦ v * (t : ℂ) + (z₀ - v * (t₀ : ℂ)))
        (t₀ - δ / 2) (t₀ + δ / 2) w) :
    (fun h : ℝ ↦
      (windingNumber L (t₀ - δ) (t₀ - δ / 2) (z₀ + h • (I * v)) -
        windingNumber L (t₀ - δ) (t₀ - δ / 2) (z₀ - h • (I * v))) +
      (windingNumber (fun t : ℝ ↦ v * (t : ℂ) + (z₀ - v * (t₀ : ℂ)))
          (t₀ - δ / 2) (t₀ + δ / 2) (v * (t₀ + h * I) + (z₀ - v * (t₀ : ℂ))) -
        windingNumber (fun t : ℝ ↦ v * (t : ℂ) + (z₀ - v * (t₀ : ℂ)))
          (t₀ - δ / 2) (t₀ + δ / 2) (v * (t₀ - h * I) + (z₀ - v * (t₀ : ℂ)))) +
      (windingNumber L (t₀ + δ / 2) (t₀ + δ) (z₀ + h • (I * v)) -
        windingNumber L (t₀ + δ / 2) (t₀ + δ) (z₀ - h • (I * v))))
      =ᶠ[𝓝[>] 0] fun h : ℝ ↦
        windingNumber L (t₀ - δ) (t₀ + δ) (z₀ + h • (I * v)) -
          windingNumber L (t₀ - δ) (t₀ + δ) (z₀ - h • (I * v)) := by
  have hle₁ : t₀ - δ ≤ t₀ - δ / 2 := by linarith
  have hle₂ : t₀ - δ / 2 ≤ t₀ + δ / 2 := by linarith
  have hle₃ : t₀ + δ / 2 ≤ t₀ + δ := by linarith
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hp_pos : v * (t₀ + h * I) + (z₀ - v * (t₀ : ℂ)) = z₀ + h • (I * v) := by
    rw [Complex.real_smul]; ring
  have hp_neg : v * (t₀ - h * I) + (z₀ - v * (t₀ : ℂ)) = z₀ - h • (I * v) := by
    rw [Complex.real_smul]; ring
  rw [windingNumber_sub_eq_add_three_of_notMem hle₁ hle₂ hle₃ hac₁ hac₂ hac₃
      (hoff_pos hh) (hoff_neg hh),
    hmid_seg, hmid_seg, hp_pos, hp_neg]

/-- Near `t₀`, `localTangentCurve` has winding-number normal jump tending to `1`. -/
private theorem tendsto_windingNumber_localTangentCurve_sub {γ : ℝ → ℂ} {t₀ δ : ℝ} {v : ℂ}
    (hv : v ≠ 0) (hδ : 0 < δ) (hleft : ((γ (t₀ - δ) - γ t₀) / v).re < 0)
    (hright : 0 < ((γ (t₀ + δ) - γ t₀) / v).re) :
    Tendsto (fun h : ℝ ↦
        windingNumber (localTangentCurve γ t₀ δ v) (t₀ - δ) (t₀ + δ) (γ t₀ + h • (I * v)) -
          windingNumber (localTangentCurve γ t₀ δ v) (t₀ - δ) (t₀ + δ) (γ t₀ - h • (I * v)))
      (𝓝[>] 0) (𝓝 1) := by
  set L := localTangentCurve γ t₀ δ v
  obtain ⟨hac₁, hac₂, hac₃⟩ := absolutelyContinuousOnInterval_localTangentCurve γ t₀ v hδ
  have hle₁ : t₀ - δ ≤ t₀ - δ / 2 := by linarith
  have hle₂ : t₀ - δ / 2 ≤ t₀ + δ / 2 := by linarith
  have hle₃ : t₀ + δ / 2 ≤ t₀ + δ := by linarith
  have hle₁₃ : t₀ - δ ≤ t₀ + δ := by linarith
  have hp₁ : γ t₀ ∉ L '' uIcc (t₀ - δ) (t₀ - δ / 2) := by
    rintro ⟨t, ht, heq⟩
    dsimp only [L] at heq
    exact (re_localTangentCurve_ne_zero_left hv hδ hleft (uIcc_of_le hle₁ ▸ ht)).ne
      (by rw [heq, sub_self, zero_div, zero_re])
  have hp₃ : γ t₀ ∉ L '' uIcc (t₀ + δ / 2) (t₀ + δ) := by
    rintro ⟨t, ht, heq⟩
    dsimp only [L] at heq
    exact (re_localTangentCurve_ne_zero_right hv hδ hright (uIcc_of_le hle₃ ▸ ht)).ne'
      (by rw [heq, sub_self, zero_div, zero_re])
  have hoff_pos : ∀ {h : ℝ}, 0 < h → γ t₀ + h • (I * v) ∉ L '' uIcc (t₀ - δ) (t₀ + δ) := by
    rintro h hh ⟨t, ht, heq⟩
    dsimp only [L] at heq
    exact notMem_slitCompl_add_smul hv hh
      (heq ▸ localTangentCurve_mem_slitCompl hv hδ hleft hright 1 (uIcc_of_le hle₁₃ ▸ ht))
  have hoff_neg : ∀ {h : ℝ}, 0 < h → γ t₀ - h • (I * v) ∉ L '' uIcc (t₀ - δ) (t₀ + δ) := by
    rintro h hh ⟨t, ht, heq⟩
    dsimp only [L] at heq
    exact notMem_slitCompl_sub_smul hv hh
      (heq ▸ localTangentCurve_mem_slitCompl hv hδ hleft hright (-1) (uIcc_of_le hle₁₃ ▸ ht))
  have hmid_seg : ∀ w, windingNumber L (t₀ - δ / 2) (t₀ + δ / 2) w =
      windingNumber (fun t : ℝ ↦ v * (t : ℂ) + (γ t₀ - v * (t₀ : ℂ)))
        (t₀ - δ / 2) (t₀ + δ / 2) w := fun w ↦
    windingNumber_congr_curve fun t ht ↦
      eqOn_localTangentCurve_mid hδ (Ioo_subset_Icc_self (uIoo_of_le hle₂ ▸ ht))
  refine Tendsto.congr' (eventuallyEq_windingNumber_sub_add_three hδ hac₁ hac₂ hac₃ hoff_pos
    hoff_neg hmid_seg) ?_
  have hs : t₀ ∈ Ioo (t₀ - δ / 2) (t₀ + δ / 2) := ⟨by linarith, by linarith⟩
  simpa using (((hac₁.tendsto_windingNumber_add_smul_sub hp₁ (I * v)).mono_left
      nhdsWithin_le_nhds).add
    (tendsto_windingNumber_segment_sub (z₀ := γ t₀ - v * (t₀ : ℂ)) hv hs)).add
    ((hac₃.tendsto_windingNumber_add_smul_sub hp₃ (I * v)).mono_left nhdsWithin_le_nhds)

/-- When `γ` lies in `slitCompl (γ t₀) v σ` (`0 < σ ^ 2`) on `[t₀ - δ, t₀ + δ]` and avoids `γ t₀`
on the outer intervals, `γ t₀ + (σ * h) • (I * v)` eventually misses `γ '' uIcc a b`. -/
private theorem eventually_notMem_trace_smul {γ : ℝ → ℂ} {a b t₀ δ σ : ℝ} {v : ℂ}
    (hab : a < b) (hγ : ContinuousOn γ (uIcc a b)) (hv : v ≠ 0) (hσ : 0 < σ ^ 2)
    (haδ : a < t₀ - δ) (hbδ : t₀ + δ < b) (hle_mid : t₀ - δ ≤ t₀ + δ)
    (hp₁ : γ t₀ ∉ γ '' uIcc a (t₀ - δ)) (hp₃ : γ t₀ ∉ γ '' uIcc (t₀ + δ) b)
    (hγ_slit : ∀ t ∈ uIcc (t₀ - δ) (t₀ + δ), γ t ∈ slitCompl (γ t₀) v σ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, γ t₀ + (σ * h) • (I * v) ∉ γ '' uIcc a b := by
  have hsub₁ : uIcc a (t₀ - δ) ⊆ uIcc a b := by
    rw [uIcc_of_le haδ.le, uIcc_of_le hab.le]; exact Icc_subset_Icc le_rfl (by linarith)
  have hsub₃ : uIcc (t₀ + δ) b ⊆ uIcc a b := by
    rw [uIcc_of_le hbδ.le, uIcc_of_le hab.le]; exact Icc_subset_Icc (by linarith) le_rfl
  have hK : IsClosed (γ '' uIcc a (t₀ - δ) ∪ γ '' uIcc (t₀ + δ) b) :=
    ((isCompact_uIcc.image_of_continuousOn (hγ.mono hsub₁)).union
      (isCompact_uIcc.image_of_continuousOn (hγ.mono hsub₃))).isClosed
  have htend : Tendsto (fun h : ℝ ↦ γ t₀ + (σ * h) • (I * v)) (𝓝[>] 0) (𝓝 (γ t₀)) :=
    ((by fun_prop : Continuous fun h : ℝ ↦ γ t₀ + (σ * h) • (I * v)).tendsto' 0 (γ t₀)
      (by simp)).mono_left nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,
      htend.eventually (hK.isOpen_compl.mem_nhds fun h ↦ h.elim hp₁ hp₃)]
    with h hh hout ⟨t, ht, heq⟩
  have ht' : t ∈ Icc a b := uIcc_of_le hab.le ▸ ht
  rcases lt_or_ge t (t₀ - δ) with hlt | hge
  · exact hout (Or.inl ⟨t, uIcc_of_le haδ.le ▸ ⟨ht'.1, hlt.le⟩, heq⟩)
  · rcases le_or_gt t (t₀ + δ) with hle | hgt
    · exact notMem_slitCompl_smul hv hσ hh (heq ▸ hγ_slit t (uIcc_of_le hle_mid ▸ ⟨hge, hle⟩))
    · exact hout (Or.inr ⟨t, uIcc_of_le hbδ.le ▸ ⟨hgt.le, ht'.2⟩, heq⟩)

private theorem eventually_notMem_trace_add_sub_I_mul {γ : ℝ → ℂ} {a b t₀ δ : ℝ} {v : ℂ}
    (hab : a < b) (hγ : ContinuousOn γ (uIcc a b)) (hv : v ≠ 0)
    (haδ : a < t₀ - δ) (hbδ : t₀ + δ < b) (hle_mid : t₀ - δ ≤ t₀ + δ)
    (hp₁ : γ t₀ ∉ γ '' uIcc a (t₀ - δ)) (hp₃ : γ t₀ ∉ γ '' uIcc (t₀ + δ) b)
    (hγ_slit : ∀ σ : ℝ, ∀ t ∈ uIcc (t₀ - δ) (t₀ + δ), γ t ∈ slitCompl (γ t₀) v σ) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      γ t₀ + h • (I * v) ∉ γ '' uIcc a b ∧ γ t₀ - h • (I * v) ∉ γ '' uIcc a b := by
  filter_upwards [eventually_notMem_trace_smul hab hγ hv (by norm_num : (0 : ℝ) < 1 ^ 2)
      haδ hbδ hle_mid hp₁ hp₃ (hγ_slit 1),
    eventually_notMem_trace_smul hab hγ hv (by norm_num : (0 : ℝ) < (-1 : ℝ) ^ 2)
      haδ hbδ hle_mid hp₁ hp₃ (hγ_slit (-1))] with h hpos hneg
  exact ⟨by simpa using hpos, by simpa [sub_eq_add_neg, neg_smul] using hneg⟩

/-- A curve agreeing with `localTangentCurve` at both endpoints, and lying in the slit plane
`slitCompl (γ t₀) v σ`, has the same winding number as `localTangentCurve` about every point
outside that slit plane. -/
private theorem windingNumber_eq_localTangentCurve {γ : ℝ → ℂ} {t₀ δ : ℝ} {v : ℂ} {σ : ℝ} {w : ℂ}
    (hv : v ≠ 0) (hδ : 0 < δ) (hleft : ((γ (t₀ - δ) - γ t₀) / v).re < 0)
    (hright : 0 < ((γ (t₀ + δ) - γ t₀) / v).re)
    (hγ : AbsolutelyContinuousOnInterval γ (t₀ - δ) (t₀ + δ))
    (hacL : AbsolutelyContinuousOnInterval (localTangentCurve γ t₀ δ v) (t₀ - δ) (t₀ + δ))
    (hLa : localTangentCurve γ t₀ δ v (t₀ - δ) = γ (t₀ - δ))
    (hLb : localTangentCurve γ t₀ δ v (t₀ + δ) = γ (t₀ + δ))
    (hγ_slit : ∀ t ∈ uIcc (t₀ - δ) (t₀ + δ), γ t ∈ slitCompl (γ t₀) v σ)
    (hw : w ∉ slitCompl (γ t₀) v σ) :
    windingNumber γ (t₀ - δ) (t₀ + δ) w =
      windingNumber (localTangentCurve γ t₀ δ v) (t₀ - δ) (t₀ + δ) w :=
  hγ.windingNumber_eq_of_starConvex_of_eq_endpoints hacL (starConvex_slitCompl (γ t₀) v σ)
    hLa.symm hLb.symm hγ_slit
    (fun t ht ↦ localTangentCurve_mem_slitCompl hv hδ hleft hright σ
      (uIcc_of_le (by linarith : t₀ - δ ≤ t₀ + δ) ▸ ht)) hw

/-- Choose a symmetric parameter window `[t₀ - δ, t₀ + δ] ⊂ (a, b)` on which `γ` lies in every
normalized slit plane `slitCompl (γ t₀) v σ`, crosses from negative to positive normalized real
part, and misses `γ t₀` on both complementary arcs. -/
private theorem exists_window_slitCompl {γ : ℝ → ℂ} {a b t₀ : ℝ} {v : ℂ}
    (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hv : v ≠ 0)
    (huniq : ∀ t ∈ Icc a b, γ t = γ t₀ → t = t₀) :
    ∃ δ : ℝ, 0 < δ ∧ a < t₀ - δ ∧ t₀ + δ < b ∧
      ((γ (t₀ - δ) - γ t₀) / v).re < 0 ∧
      0 < ((γ (t₀ + δ) - γ t₀) / v).re ∧
      (∀ σ : ℝ, ∀ t ∈ uIcc (t₀ - δ) (t₀ + δ), γ t ∈ slitCompl (γ t₀) v σ) ∧
      γ t₀ ∉ γ '' uIcc a (t₀ - δ) ∧
      γ t₀ ∉ γ '' uIcc (t₀ + δ) b := by
  have hg : HasDerivAt (fun t ↦ ((γ t - γ t₀) / v).re) 1 t₀ := by
    simpa [Function.comp_def, div_self hv] using
      HasFDerivAt.comp_hasDerivAt t₀ Complex.reCLM.hasFDerivAt ((hd.sub_const (γ t₀)).div_const v)
  obtain ⟨δ₀, hδ₀, hlittle⟩ := Metric.eventually_nhds_iff.mp (hg.isLittleO.bound one_half_pos)
  set δ : ℝ := min (δ₀ / 2) (min ((t₀ - a) / 2) ((b - t₀) / 2))
  have hδ : 0 < δ := lt_min (half_pos hδ₀)
    (lt_min (half_pos (sub_pos.mpr ht₀.1)) (half_pos (sub_pos.mpr ht₀.2)))
  have hltδ : δ < δ₀ := (min_le_left _ _).trans_lt (half_lt_self hδ₀)
  have haδ : a < t₀ - δ := by
    have : δ ≤ (t₀ - a) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith [ht₀.1]
  have hbδ : t₀ + δ < b := by
    have : δ ≤ (b - t₀) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith [ht₀.2]
  have hle_mid : t₀ - δ ≤ t₀ + δ := by linarith
  have hre : ∀ t ∈ Icc (t₀ - δ) (t₀ + δ),
      (t < t₀ → ((γ t - γ t₀) / v).re < 0) ∧ (t₀ < t → 0 < ((γ t - γ t₀) / v).re) := by
    intro t ⟨ht1, ht2⟩
    have hdist : dist t t₀ < δ₀ := by
      rw [Real.dist_eq, abs_sub_lt_iff]
      exact ⟨by linarith, by linarith⟩
    have hb : |((γ t - γ t₀) / v).re - (t - t₀)| ≤ 1 / 2 * |t - t₀| := by
      simpa [Real.norm_eq_abs] using hlittle hdist
    exact ⟨fun hlt ↦ by linarith [(abs_le.mp hb).2, abs_of_neg (sub_neg.mpr hlt)],
      fun hgt ↦ by linarith [(abs_le.mp hb).1, abs_of_pos (sub_pos.mpr hgt)]⟩
  refine ⟨δ, hδ, haδ, hbδ, (hre (t₀ - δ) ⟨le_rfl, hle_mid⟩).1 (by linarith),
    (hre (t₀ + δ) ⟨hle_mid, le_rfl⟩).2 (by linarith), ?_, ?_, ?_⟩
  · intro σ t ht
    have ht' : t ∈ Icc (t₀ - δ) (t₀ + δ) := uIcc_of_le hle_mid ▸ ht
    rcases lt_trichotomy t t₀ with hlt | rfl | hgt
    · exact Or.inl ((hre t ht').1 hlt).ne
    · exact self_mem_slitCompl _ _ _
    · exact Or.inl ((hre t ht').2 hgt).ne'
  · rintro ⟨t, ht, heq⟩
    have ht' : t ∈ Icc a (t₀ - δ) := uIcc_of_le haδ.le ▸ ht
    exact (by linarith [ht'.2] : t ≠ t₀) (huniq t ⟨ht'.1, by linarith [ht'.2]⟩ heq)
  · rintro ⟨t, ht, heq⟩
    have ht' : t ∈ Icc (t₀ + δ) b := uIcc_of_le hbδ.le ▸ ht
    exact (by linarith [ht'.1] : t ≠ t₀) (huniq t ⟨by linarith [ht'.1], ht'.2⟩ heq)

end Helpers

end TauCeti.Contour

open TauCeti.Contour

namespace AbsolutelyContinuousOnInterval

/-- **Normal-crossing jump of the winding number at a regular interior point.** Let `γ` be an
absolutely continuous curve on `[a, b]` (`a < b`) that is differentiable at `t₀ ∈ (a, b)` with
nonzero derivative `v ≠ 0` and visits `γ t₀` nowhere else on `[a, b]`. Then the winding-number
difference between `γ t₀ + h • (I * v)` (to the left of `v`) and `γ t₀ - h • (I * v)` (to the right
of `v`) tends to `1` as `h → 0⁺`, and both normal test points eventually lie off the trace. -/
theorem tendsto_windingNumber_add_I_mul_sub
    {γ : ℝ → ℂ} {a b t₀ : ℝ} {v : ℂ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (ht₀ : t₀ ∈ Ioo a b)
    (hd : HasDerivAt γ v t₀) (hv : v ≠ 0)
    (huniq : ∀ t ∈ Icc a b, γ t = γ t₀ → t = t₀) :
    (∀ᶠ h : ℝ in 𝓝[>] 0,
      γ t₀ + h • (I * v) ∉ γ '' uIcc a b ∧ γ t₀ - h • (I * v) ∉ γ '' uIcc a b) ∧
    Tendsto (fun h : ℝ ↦
        windingNumber γ a b (γ t₀ + h • (I * v)) - windingNumber γ a b (γ t₀ - h • (I * v)))
      (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨δ, hδ, haδ, hbδ, hleft, hright, hγ_slit, hp₁, hp₃⟩ :=
    exists_window_slitCompl ht₀ hd hv huniq
  have hle_mid : t₀ - δ ≤ t₀ + δ := by linarith
  have hle_tail : t₀ - δ ≤ b := by linarith
  have havoid := eventually_notMem_trace_add_sub_I_mul hab hγ.continuousOn hv haδ hbδ hle_mid
    hp₁ hp₃ hγ_slit
  refine ⟨havoid, ?_⟩
  have hsub : ∀ {x y}, a ≤ x → x ≤ y → y ≤ b → uIcc x y ⊆ uIcc a b := fun hx hxy hy ↦ by
    rw [uIcc_of_le hxy, uIcc_of_le hab.le]; exact Icc_subset_Icc hx hy
  have hγ₁ := hγ.mono (hsub le_rfl haδ.le hle_tail)
  have hγ₂ := hγ.mono (hsub haδ.le hle_mid hbδ.le)
  have hγ₃ := hγ.mono (hsub (by linarith) hbδ.le le_rfl)
  obtain ⟨hacL₁, hacL₂, hacL₃⟩ := absolutelyContinuousOnInterval_localTangentCurve γ t₀ v hδ
  have hacL : AbsolutelyContinuousOnInterval (localTangentCurve γ t₀ δ v) (t₀ - δ) (t₀ + δ) :=
    hacL₁.trans (hacL₂.trans hacL₃)
  have hLa : localTangentCurve γ t₀ δ v (t₀ - δ) = γ (t₀ - δ) := by
    simp [localTangentCurve, (by linarith : t₀ - δ ≤ t₀ - δ / 2)]
  have hLb : localTangentCurve γ t₀ δ v (t₀ + δ) = γ (t₀ + δ) := by
    have h₃ : t₀ + δ - (t₀ + δ / 2) = δ / 2 := by ring
    simp [localTangentCurve, (by linarith : ¬ t₀ + δ ≤ t₀ - δ / 2),
      (by linarith : ¬ t₀ + δ ≤ t₀ + δ / 2), h₃, (half_pos hδ).ne']
  have heq : (fun h : ℝ ↦
      (windingNumber γ a (t₀ - δ) (γ t₀ + h • (I * v)) -
        windingNumber γ a (t₀ - δ) (γ t₀ - h • (I * v))) +
      (windingNumber (localTangentCurve γ t₀ δ v) (t₀ - δ) (t₀ + δ) (γ t₀ + h • (I * v)) -
        windingNumber (localTangentCurve γ t₀ δ v) (t₀ - δ) (t₀ + δ) (γ t₀ - h • (I * v))) +
      (windingNumber γ (t₀ + δ) b (γ t₀ + h • (I * v)) -
        windingNumber γ (t₀ + δ) b (γ t₀ - h • (I * v))))
      =ᶠ[𝓝[>] 0] fun h : ℝ ↦
        windingNumber γ a b (γ t₀ + h • (I * v)) - windingNumber γ a b (γ t₀ - h • (I * v)) := by
    filter_upwards [self_mem_nhdsWithin, havoid] with h hh ⟨hpos, hneg⟩
    have hw_pos := windingNumber_eq_localTangentCurve hv hδ hleft hright hγ₂ hacL hLa hLb
      (hγ_slit 1) (notMem_slitCompl_add_smul hv hh)
    have hw_neg := windingNumber_eq_localTangentCurve hv hδ hleft hright hγ₂ hacL hLa hLb
      (hγ_slit (-1)) (notMem_slitCompl_sub_smul hv hh)
    rw [windingNumber_sub_eq_add_three_of_notMem haδ.le hle_mid hbδ.le hγ₁ hγ₂ hγ₃ hpos hneg,
      hw_pos, hw_neg]
  refine Tendsto.congr' heq ?_
  simpa using (((hγ₁.tendsto_windingNumber_add_smul_sub hp₁ (I * v)).mono_left
      nhdsWithin_le_nhds).add
    (tendsto_windingNumber_localTangentCurve_sub hv hδ hleft hright)).add
    ((hγ₃.tendsto_windingNumber_add_smul_sub hp₃ (I * v)).mono_left nhdsWithin_le_nhds)

/-- **Exact `+1` winding-number jump across a regular interior point of a closed AC curve.** If `γ`
is closed on `[a, b]` (`a < b`), differentiable at `t₀ ∈ (a, b)` with `v ≠ 0`, and visits `γ t₀`
only at `t₀`, then for all sufficiently small `h > 0`, both `γ t₀ ± h • (I * v)` miss the trace and
`windingNumber γ a b (γ t₀ + h • (I * v)) = windingNumber γ a b (γ t₀ - h • (I * v)) + 1`. -/
theorem eventually_windingNumber_add_I_mul_eq_add_one_of_forall_eq
    {γ : ℝ → ℂ} {a b t₀ : ℝ} {v : ℂ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hv : v ≠ 0)
    (huniq : ∀ t ∈ Icc a b, γ t = γ t₀ → t = t₀) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      γ t₀ + h • (I * v) ∉ γ '' uIcc a b ∧
      γ t₀ - h • (I * v) ∉ γ '' uIcc a b ∧
      windingNumber γ a b (γ t₀ + h • (I * v)) =
        windingNumber γ a b (γ t₀ - h • (I * v)) + 1 := by
  obtain ⟨havoid, htend⟩ := hγ.tendsto_windingNumber_add_I_mul_sub hab ht₀ hd hv huniq
  filter_upwards [havoid, htend (Metric.ball_mem_nhds (1 : ℂ) one_half_pos)]
    with h ⟨hpos, hneg⟩ hball
  refine ⟨hpos, hneg, ?_⟩
  obtain ⟨m, hm⟩ := hγ.exists_int_windingNumber hclosed hpos
  obtain ⟨n, hn⟩ := hγ.exists_int_windingNumber hclosed hneg
  have hmn : m = n + 1 := by
    rw [mem_preimage, Metric.mem_ball, dist_eq_norm, hm, hn] at hball
    have hnorm : ((|m - (n + 1)| : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by
      have heq : (m : ℂ) - (n : ℂ) - 1 = ((m - (n + 1) : ℤ) : ℂ) := by push_cast; ring
      rw [heq, Complex.norm_intCast, ← Int.cast_abs] at hball
      rw [Int.cast_one]
      linarith
    obtain ⟨h1, h2⟩ := abs_lt.mp (Int.cast_lt.mp hnorm)
    omega
  rw [hm, hn, hmn, Int.cast_add, Int.cast_one]

/-- **Exact `+1` winding-number jump across a regular interior point of a simple closed AC curve.**
For a simple closed absolutely continuous curve (`InjOn γ (Ico a b)` and `γ a = γ b`), at any
interior point `t₀ ∈ (a, b)` where `HasDerivAt γ v t₀` with `v ≠ 0`, the winding number at
`γ t₀ + h • (I * v)` eventually equals that at `γ t₀ - h • (I * v)` plus `1`. -/
theorem eventually_windingNumber_add_I_mul_eq_add_one
    {γ : ℝ → ℂ} {a b t₀ : ℝ} {v : ℂ} (hab : a < b)
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hinj : InjOn γ (Ico a b)) (ht₀ : t₀ ∈ Ioo a b) (hd : HasDerivAt γ v t₀) (hv : v ≠ 0) :
    ∀ᶠ h : ℝ in 𝓝[>] 0,
      γ t₀ + h • (I * v) ∉ γ '' uIcc a b ∧
      γ t₀ - h • (I * v) ∉ γ '' uIcc a b ∧
      windingNumber γ a b (γ t₀ + h • (I * v)) =
        windingNumber γ a b (γ t₀ - h • (I * v)) + 1 := by
  refine hγ.eventually_windingNumber_add_I_mul_eq_add_one_of_forall_eq hab hclosed ht₀ hd hv ?_
  intro t ht heq
  rcases ht.2.eq_or_lt with htb | hlt
  · rw [htb, ← hclosed] at heq
    exact absurd (hinj ⟨le_rfl, hab⟩ ⟨ht₀.1.le, ht₀.2⟩ heq) ht₀.1.ne
  · exact hinj ⟨ht.1, hlt⟩ ⟨ht₀.1.le, ht₀.2⟩ heq

end AbsolutelyContinuousOnInterval
