/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Normed.Group.RelativeApproximation

/-!
# Maps within relative error of a linear map on a finite-dimensional space

On a finite-dimensional normed space over a complete nontrivially normed field, an injective
linear map is antilipschitz. Hence a map within relative error `δ < 1` of an injective linear map
on a set `p` is antilipschitz on `p`
(`TauCeti.exists_antilipschitzWith_domRestrict_of_approx`). This is the lower bi-Lipschitz bound
on the pieces of the decomposition of a differentiable map with injective derivative.
-/

public section

open Set Function
open scoped NNReal

namespace TauCeti

/-- A map within relative error `δ < 1` of an injective linear map on `p` has a Lipschitz inverse
on `p`. -/
theorem exists_antilipschitzWith_domRestrict_of_approx {𝕜 U V 𝓕 : Type*}
    [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [NormedAddCommGroup U] [NormedSpace 𝕜 U]
    [FiniteDimensional 𝕜 U] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FunLike 𝓕 U V]
    [LinearMapClass 𝓕 𝕜 U V] {f : U → V} {p : Set U} {A : 𝓕} {δ : ℝ}
    (hA : p.Nonempty → Injective A) (hδ : δ < 1)
    (happ : ∀ x ∈ p, ∀ y ∈ p, ‖f x - f y - A (x - y)‖ ≤ δ * ‖A (x - y)‖) :
    ∃ L : ℝ≥0, AntilipschitzWith L (p.domRestrict f) := by
  rcases p.eq_empty_or_nonempty with rfl | hp
  · exact ⟨1, fun x ↦ x.2.elim⟩
  obtain ⟨c, -, hAc⟩ := (A : U →ₗ[𝕜] V).injective_iff_antilipschitz.mp (hA hp)
  have hδ' : 0 < 1 - δ := sub_pos.2 hδ
  refine ⟨c * (Real.toNNReal (1 - δ))⁻¹, AntilipschitzWith.of_le_mul_dist fun x y ↦ ?_⟩
  have hxy : ‖(x : U) - y‖ ≤ c * ‖A x - A y‖ := by
    simpa [map_sub] using hAc.le_mul_dist (x - y : U) 0
  have h := one_sub_mul_norm_sub_le_norm_sub happ x.2 y.2
  simp only [Subtype.dist_eq, domRestrict_apply, dist_eq_norm, NNReal.coe_mul, NNReal.coe_inv,
    Real.coe_toNNReal _ hδ'.le]
  calc ‖(x : U) - y‖ ≤ c * ‖A x - A y‖ := hxy
    _ ≤ c * ((1 - δ)⁻¹ * ‖f x - f y‖) := by
        gcongr
        rwa [le_inv_mul_iff₀ hδ']
    _ = c * (1 - δ)⁻¹ * ‖f x - f y‖ := by ring

end TauCeti
