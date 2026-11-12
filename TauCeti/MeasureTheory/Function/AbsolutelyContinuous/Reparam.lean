/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Order.MinMax
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Absolutely continuous monotone changes of parameter

Composing an absolutely continuous metric-valued curve with an absolutely continuous monotone
change of parameter preserves absolute continuity. Monotonicity is required only on the parameter
interval, and the change of parameter may have constant pieces or unbounded speed. Affine changes
of parameter, of any slope, both preserve and reflect absolute continuity; in particular so does
the affine normalization of the parameter interval to `[0, 1]`.
-/

public section

open Filter Function Set

namespace AbsolutelyContinuousOnInterval

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {θ : ℝ → ℝ} {a b c d : ℝ}

/-- A monotone change of parameter maps a collection of disjoint half-open parameter intervals
to a collection of disjoint half-open intervals in the image parameter interval. -/
private theorem mapsTo_disjWithin_of_monotoneOn_or_antitoneOn
    (hθ : MonotoneOn θ (uIcc a b) ∨ AntitoneOn θ (uIcc a b))
    (hmap : MapsTo θ (uIcc a b) (uIcc c d)) :
    MapsTo (fun E : ℕ × (ℕ → ℝ × ℝ) ↦
      (E.1, fun i ↦ (θ (E.2 i).1, θ (E.2 i).2))) (disjWithin a b) (disjWithin c d) := by
  rintro ⟨n, I⟩ ⟨hmem, hdisj⟩
  refine ⟨fun i hi ↦ ⟨hmap (hmem i hi).1, hmap (hmem i hi).2⟩, ?_⟩
  have hmin {x y : ℝ} (hx : x ∈ uIcc a b) (hy : y ∈ uIcc a b) :
      min x y ∈ uIcc a b := by rcases min_choice x y with h | h <;> simp_all
  have hmax {x y : ℝ} (hx : x ∈ uIcc a b) (hy : y ∈ uIcc a b) :
      max x y ∈ uIcc a b := by rcases max_choice x y with h | h <;> simp_all
  intro i hi j hj hij
  have hd := hdisj hi hj hij
  simp only [uIoc, Ioc_disjoint_Ioc] at hd ⊢
  have hi₁ := (hmem i hi).1
  have hi₂ := (hmem i hi).2
  have hj₁ := (hmem j hj).1
  have hj₂ := (hmem j hj).2
  rcases hθ with hθ | hθ
  all_goals
    have hm := hθ (hmin (hmax hi₁ hi₂) (hmax hj₁ hj₂))
      (hmax (hmin hi₁ hi₂) (hmin hj₁ hj₂)) hd
    simpa only [hθ.map_min (hmax hi₁ hi₂) (hmax hj₁ hj₂),
      hθ.map_max (hmin hi₁ hi₂) (hmin hj₁ hj₂),
      hθ.map_min hi₁ hi₂, hθ.map_min hj₁ hj₂, hθ.map_max hi₁ hi₂, hθ.map_max hj₁ hj₂] using hm

/-- Composition preserves absolute continuity when the absolutely continuous change of parameter
is monotone or antitone on its parameter interval. -/
private theorem comp_of_monotoneOn_or_antitoneOn (hγ : AbsolutelyContinuousOnInterval γ c d)
    (hθ_ac : AbsolutelyContinuousOnInterval θ a b)
    (hθ : MonotoneOn θ (uIcc a b) ∨ AntitoneOn θ (uIcc a b))
    (hmap : MapsTo θ (uIcc a b) (uIcc c d)) :
    AbsolutelyContinuousOnInterval (γ ∘ θ) a b := by
  let T (E : ℕ × (ℕ → ℝ × ℝ)) := (E.1, fun i ↦ (θ (E.2 i).1, θ (E.2 i).2))
  have hlength : Tendsto T (totalLengthFilter ⊓ 𝓟 (disjWithin a b)) totalLengthFilter := by
    rw [totalLengthFilter, tendsto_comap_iff]
    exact hθ_ac
  have hdisj := mapsTo_disjWithin_of_monotoneOn_or_antitoneOn hθ hmap
  exact hγ.comp (tendsto_inf.mpr ⟨hlength, hdisj.tendsto.mono_left inf_le_right⟩)

/-- Absolutely continuous metric-valued curves remain absolutely continuous under an absolutely
continuous change of parameter that is monotone on its parameter interval. Constant pieces and
unbounded speeds are allowed. -/
theorem comp_monotoneOn (hγ : AbsolutelyContinuousOnInterval γ c d)
    (hθ_ac : AbsolutelyContinuousOnInterval θ a b) (hθ : MonotoneOn θ (uIcc a b))
    (hmap : MapsTo θ (uIcc a b) (uIcc c d)) :
    AbsolutelyContinuousOnInterval (γ ∘ θ) a b :=
  comp_of_monotoneOn_or_antitoneOn hγ hθ_ac (Or.inl hθ) hmap

/-- Absolutely continuous metric-valued curves remain absolutely continuous under an absolutely
continuous change of parameter that is antitone on its parameter interval. -/
theorem comp_antitoneOn (hγ : AbsolutelyContinuousOnInterval γ c d)
    (hθ_ac : AbsolutelyContinuousOnInterval θ a b) (hθ : AntitoneOn θ (uIcc a b))
    (hmap : MapsTo θ (uIcc a b) (uIcc c d)) :
    AbsolutelyContinuousOnInterval (γ ∘ θ) a b :=
  comp_of_monotoneOn_or_antitoneOn hγ hθ_ac (Or.inr hθ) hmap

/-- Composing an absolutely continuous metric-valued curve with an affine change of parameter
preserves absolute continuity whenever that parameter maps into the curve's interval.
The slope may be positive, zero, or negative. -/
theorem comp_affine {γ : ℝ → X} {a b c d : ℝ}
    (hγ : AbsolutelyContinuousOnInterval γ c d) (m k : ℝ)
    (hmap : MapsTo (fun t : ℝ ↦ m * t + k) (uIcc a b) (uIcc c d)) :
    AbsolutelyContinuousOnInterval (γ ∘ (fun t : ℝ ↦ m * t + k)) a b := by
  have hc : ContDiffOn ℝ 1 (fun t : ℝ ↦ m * t + k) (uIcc a b) := by fun_prop
  rcases le_total 0 m with hm | hm
  · exact hγ.comp_monotoneOn hc.absolutelyContinuousOnInterval
      (fun _ _ _ _ hst ↦ add_le_add (mul_le_mul_of_nonneg_left hst hm) le_rfl) hmap
  · exact hγ.comp_antitoneOn hc.absolutelyContinuousOnInterval
      (fun _ _ _ _ hst ↦ add_le_add (mul_le_mul_of_nonpos_left hst hm) le_rfl) hmap

/-- Affine changes of time preserve absolute continuity of metric-valued curves. The slope may be
zero, in which case the reparameterized curve is constant. -/
theorem comp_mul_add (hγ : AbsolutelyContinuousOnInterval γ (c * a + d) (c * b + d)) :
    AbsolutelyContinuousOnInterval (fun t ↦ γ (c * t + d)) a b := by
  have hmap : MapsTo (fun t : ℝ ↦ c * t + d) (uIcc a b) (uIcc (c * a + d) (c * b + d)) := by
    intro t ht
    have hmul : c * t ∈ uIcc (c * a) (c * b) :=
      image_const_mul_uIcc c a b ▸ mem_image_of_mem (c * ·) ht
    have hadd := mem_image_of_mem (fun x : ℝ ↦ x + d) hmul
    rwa [image_add_const_uIcc] at hadd
  simpa only [comp_def] using hγ.comp_affine c d hmap

end AbsolutelyContinuousOnInterval

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X]

/-- Absolute continuity on the transformed interval is equivalent to absolute continuity of the
affinely reparameterized curve on the original interval. For zero slope both sides hold. -/
theorem absolutelyContinuousOnInterval_comp_mul_add_iff (γ : ℝ → X) (c d a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t ↦ γ (c * t + d)) a b ↔
      AbsolutelyContinuousOnInterval γ (c * a + d) (c * b + d) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_mul_add⟩
  rcases eq_or_ne c 0 with rfl | hc
  · simpa only [zero_mul, zero_add] using AbsolutelyContinuousOnInterval.refl γ d
  -- Undo the change of time with the inverse affine map `t ↦ c⁻¹ * t - c⁻¹ * d`.
  have hinv (t : ℝ) : c * (c⁻¹ * t + -(c⁻¹ * d)) + d = t := by
    field_simp
    ring
  have ha : c⁻¹ * (c * a + d) + -(c⁻¹ * d) = a := by field_simp; ring
  have hb : c⁻¹ * (c * b + d) + -(c⁻¹ * d) = b := by field_simp; ring
  have h₁ : AbsolutelyContinuousOnInterval (fun t ↦ γ (c * t + d))
      (c⁻¹ * (c * a + d) + -(c⁻¹ * d)) (c⁻¹ * (c * b + d) + -(c⁻¹ * d)) := by
    rwa [ha, hb]
  simpa only [hinv] using h₁.comp_mul_add

/-- A metric-valued curve is absolutely continuous on `uIcc a b` exactly when its affine
normalization to the unit interval is absolutely continuous on `uIcc 0 1`. Reversed and constant
parameter intervals are allowed. -/
@[simp]
theorem absolutelyContinuousOnInterval_comp_lineMap_iff {γ : ℝ → X} {a b : ℝ} :
    AbsolutelyContinuousOnInterval (γ ∘ AffineMap.lineMap a b) 0 1 ↔
      AbsolutelyContinuousOnInterval γ a b := by
  have he : γ ∘ AffineMap.lineMap a b = fun t ↦ γ ((b - a) * t + a) := by
    funext t
    rw [comp_apply, AffineMap.lineMap_apply_ring', mul_comm]
  rw [he, absolutelyContinuousOnInterval_comp_mul_add_iff, mul_zero, zero_add, mul_one,
    sub_add_cancel]

end TauCeti
