/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The half-angle quantities `1 - cos θ`, `1 + cos θ` and their quotient

The quantity `1 - cos θ = 2 sin² (θ/2)` is positive for `θ ∈ (0, 2π)`, and
`1 + cos θ = 2 cos² (θ/2)` is positive for `θ ∈ (-π, π)`. Their quotient
`(1 - cos θ)/(1 + cos θ) = tan² (θ/2)` maps `(0, π)` bijectively onto `(0, ∞)`. This is the
substitution that turns integrals over a half-line into integrals over `(0, π)`.

## Main declarations

* `TauCeti.one_sub_cos_pos`, `TauCeti.one_add_cos_pos`: positivity of `1 ∓ cos θ`.
* `TauCeti.injOn_one_sub_cos_div_one_add_cos`: `θ ↦ (1 - cos θ)/(1 + cos θ)` is injective on
  `[0, π)`.
* `TauCeti.image_one_sub_cos_div_one_add_cos_Ioo`: it maps `(0, π)` onto `(0, ∞)`.
-/

public section

open Real Set

namespace TauCeti

/-- For `θ ∈ (0, 2π)`, `1 - cos θ` is positive. -/
theorem one_sub_cos_pos {θ : ℝ} (h₀ : 0 < θ) (h₁ : θ < 2 * π) : 0 < 1 - cos θ :=
  sub_pos.2 <| (cos_le_one θ).lt_of_ne fun h ↦
    h₀.ne' ((cos_eq_one_iff_of_lt_of_lt (by linarith [pi_pos]) h₁).1 h)

/-- For `θ ∈ (-π, π)`, `1 + cos θ` is positive. -/
theorem one_add_cos_pos {θ : ℝ} (h₀ : -π < θ) (h₁ : θ < π) : 0 < 1 + cos θ := by
  simpa [cos_add_pi] using one_sub_cos_pos (θ := θ + π) (by linarith) (by linarith)

/-- The map `θ ↦ (1 - cos θ)/(1 + cos θ)` is injective on `[0, π)`. -/
theorem injOn_one_sub_cos_div_one_add_cos :
    InjOn (fun θ ↦ (1 - cos θ) / (1 + cos θ)) (Ico 0 π) := by
  intro s hs t ht hst
  have hs' := one_add_cos_pos (by linarith [hs.1, pi_pos]) hs.2
  have ht' := one_add_cos_pos (by linarith [ht.1, pi_pos]) ht.2
  rw [div_eq_div_iff hs'.ne' ht'.ne'] at hst
  exact injOn_cos (Ico_subset_Icc_self hs) (Ico_subset_Icc_self ht) (by linarith)

/-- The map `θ ↦ (1 - cos θ)/(1 + cos θ)` sends `(0, π)` onto `(0, ∞)`. -/
theorem image_one_sub_cos_div_one_add_cos_Ioo :
    (fun θ ↦ (1 - cos θ) / (1 + cos θ)) '' Ioo 0 π = Ioi 0 := by
  ext u
  refine ⟨?_, fun hu ↦ ?_⟩
  · rintro ⟨θ, hθ, rfl⟩
    exact div_pos (one_sub_cos_pos hθ.1 (by linarith [hθ.2, pi_pos]))
      (one_add_cos_pos (by linarith [hθ.1, pi_pos]) hθ.2)
  · -- The preimage is `θ = arccos ((1 - u)/(1 + u))`.
    have hu : 0 < u := hu
    have hy₁ : (1 - u) / (1 + u) < 1 := (div_lt_one (by linarith)).2 (by linarith)
    have hy₂ : -1 < (1 - u) / (1 + u) := by
      rw [lt_div_iff₀ (by linarith)]
      linarith
    refine ⟨arccos ((1 - u) / (1 + u)), ⟨arccos_pos.2 hy₁, arccos_lt_pi.2 hy₂⟩, ?_⟩
    have : 1 + u ≠ 0 := by linarith
    simp only
    rw [cos_arccos hy₂.le hy₁.le]
    field_simp
    ring

end TauCeti
