/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Reparam
public import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousSubstitution.Antitone
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# The almost-everywhere chain rule for absolutely continuous curves

Composing an absolutely continuous curve in a finite-dimensional real normed space with a
monotone or antitone absolutely continuous change of parameter satisfies the chain rule almost
everywhere.
The derivative formula includes constant pieces and unbounded speeds.
-/

public section

open MeasureTheory Set
open scoped Topology

namespace AbsolutelyContinuousOnInterval

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {γ : ℝ → F} {θ : ℝ → ℝ} {a b c d : ℝ}

/-- The common primitive proof of the chain rule for either direction of monotonicity. -/
private theorem ae_hasDerivAt_comp_of_monotoneOn_or_antitoneOn
    (hγ : AbsolutelyContinuousOnInterval γ c d)
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (horder : MonotoneOn θ (Icc a b) ∨ AntitoneOn θ (Icc a b))
    (hmap : MapsTo θ (Icc a b) (uIcc c d)) :
    ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt (γ ∘ θ) (deriv θ t • deriv γ (θ t)) t := by
  have hθa := hmap (left_mem_Icc.mpr hab)
  have hθb := hmap (right_mem_Icc.mpr hab)
  have hγab := hγ.mono (uIcc_subset_uIcc hθa hθb)
  let V : ℝ → F := fun t ↦ deriv θ t • deriv γ (θ t)
  have hV : IntervalIntegrable V volume a b := by
    rcases horder with hmono | hanti
    · exact hθ.intervalIntegrable_deriv_smul_comp_of_monotoneOn hab hmono
        hγab.intervalIntegrable_deriv_of_finiteDimensional
    · exact hθ.intervalIntegrable_deriv_smul_comp_of_antitoneOn hab hanti
        hγab.intervalIntegrable_deriv_of_finiteDimensional
  let A : ℝ → F := fun t ↦ γ (θ a) + ∫ v in a..t, V v
  have heq : EqOn (γ ∘ θ) A (Icc a b) := by
    intro t ht
    have hat : uIcc a t ⊆ uIcc a b := by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc le_rfl ht.2
    have hθat := hθ.mono hat
    have hγat := hγ.mono (uIcc_subset_uIcc hθa (hmap ht))
    have hi : (∫ v in a..t, V v) = ∫ u in θ a..θ t, deriv γ u := by
      rcases horder with hmono | hanti
      · exact hθat.integral_deriv_smul_comp_of_monotoneOn ht.1
          (hmono.mono (Icc_subset_Icc le_rfl ht.2))
          hγat.intervalIntegrable_deriv_of_finiteDimensional
      · exact hθat.integral_deriv_smul_comp_of_antitoneOn ht.1
          (hanti.mono (Icc_subset_Icc le_rfl ht.2))
          hγat.intervalIntegrable_deriv_of_finiteDimensional
    dsimp [A, V, Function.comp_def]
    rw [hi, hγat.integral_deriv_eq_sub_of_finiteDimensional]
    abel
  filter_upwards [hV.ae_hasDerivAt_integral, volume.ae_ne a, volume.ae_ne b] with t ht hta htb hmem
  have htmem : t ∈ Icc a b := by simpa only [uIcc_of_le hab] using hmem
  have htnhds : Icc a b ∈ 𝓝 t := Icc_mem_nhds
    (lt_of_le_of_ne htmem.1 (Ne.symm hta)) (lt_of_le_of_ne htmem.2 htb)
  apply ((ht hmem a left_mem_uIcc).const_add (γ (θ a))).congr_of_eventuallyEq
  filter_upwards [htnhds] with u hu
  exact heq hu

/-- The chain rule almost everywhere for an absolutely continuous curve under a monotone
absolutely continuous change of parameter. -/
theorem ae_hasDerivAt_comp_of_monotoneOn (hγ : AbsolutelyContinuousOnInterval γ c d)
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (hmono : MonotoneOn θ (Icc a b)) (hmap : MapsTo θ (Icc a b) (uIcc c d)) :
    ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt (γ ∘ θ) (deriv θ t • deriv γ (θ t)) t :=
  ae_hasDerivAt_comp_of_monotoneOn_or_antitoneOn hγ hθ hab (Or.inl hmono) hmap

/-- The canonical derivative satisfies the chain rule almost everywhere under a monotone
absolutely continuous change of parameter. -/
theorem ae_deriv_comp_of_monotoneOn (hγ : AbsolutelyContinuousOnInterval γ c d)
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (hmono : MonotoneOn θ (Icc a b)) (hmap : MapsTo θ (Icc a b) (uIcc c d)) :
    ∀ᵐ t, t ∈ uIcc a b → deriv (γ ∘ θ) t = deriv θ t • deriv γ (θ t) := by
  filter_upwards [hγ.ae_hasDerivAt_comp_of_monotoneOn hθ hab hmono hmap] with t ht hmem
  exact (ht hmem).deriv

/-- The chain rule almost everywhere for an absolutely continuous curve under an antitone
absolutely continuous change of parameter. -/
theorem ae_hasDerivAt_comp_of_antitoneOn (hγ : AbsolutelyContinuousOnInterval γ c d)
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (hanti : AntitoneOn θ (Icc a b)) (hmap : MapsTo θ (Icc a b) (uIcc c d)) :
    ∀ᵐ t, t ∈ uIcc a b →
      HasDerivAt (γ ∘ θ) (deriv θ t • deriv γ (θ t)) t :=
  ae_hasDerivAt_comp_of_monotoneOn_or_antitoneOn hγ hθ hab (Or.inr hanti) hmap

/-- The canonical derivative satisfies the chain rule almost everywhere under an antitone
absolutely continuous change of parameter. -/
theorem ae_deriv_comp_of_antitoneOn (hγ : AbsolutelyContinuousOnInterval γ c d)
    (hθ : AbsolutelyContinuousOnInterval θ a b) (hab : a ≤ b)
    (hanti : AntitoneOn θ (Icc a b)) (hmap : MapsTo θ (Icc a b) (uIcc c d)) :
    ∀ᵐ t, t ∈ uIcc a b → deriv (γ ∘ θ) t = deriv θ t • deriv γ (θ t) := by
  filter_upwards [hγ.ae_hasDerivAt_comp_of_antitoneOn hθ hab hanti hmap] with t ht hmem
  exact (ht hmem).deriv

end AbsolutelyContinuousOnInterval
