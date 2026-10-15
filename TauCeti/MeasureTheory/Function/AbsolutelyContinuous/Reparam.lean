/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Order.Interval.Set.Disjoint
import Mathlib.Order.MinMax
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Absolutely continuous monotone changes of parameter

Composing an absolutely continuous metric-valued curve with an absolutely continuous monotone
change of parameter preserves absolute continuity. Monotonicity is required only on the parameter
interval, and the change of parameter may have constant pieces or unbounded speed.
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

end AbsolutelyContinuousOnInterval
