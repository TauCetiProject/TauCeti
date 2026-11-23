/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Maps.Strict.Basic

import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Reverse norm bounds for inducing linear maps

Over a nontrivially normed field `𝕜`, a linear map `f : E →ₗ[𝕜] F` between seminormed spaces that
is topologically inducing (`Topology.IsInducing f`) satisfies a reverse norm bound `‖x‖ ≤ C * ‖f x‖`
for some `C > 0` and is antilipschitz, since `f` pulls back the norm seminorm of `F` to generate the
topology of `E` (`Seminorm.bound_comp_of_isInducing`). Neither injectivity, completeness, nor
Hausdorffness is needed.

In particular, this applies to any strict injective linear map (`Topology.IsStrictMap f` and
`Function.Injective f`), such as an injective linear map out of a finite module over a complete
Noetherian Tate ring (`LinearMap.isStrictMap_of_module_finite`).

## Main results

* `LinearMap.exists_pos_norm_le_mul_norm_of_isInducing`: if `f : E →ₗ[𝕜] F` is topologically
  inducing, then `∃ C > 0, ∀ x, ‖x‖ ≤ C * ‖f x‖`.
* `LinearMap.exists_antilipschitzWith_of_isInducing`: the corresponding `AntilipschitzWith` bound.
* `LinearMap.exists_pos_norm_le_mul_norm_of_isStrictMap_of_injective`: the same bound for a strict
  injective linear map.
-/

public section

open Topology

namespace LinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **An inducing linear map over a nontrivially normed field is bounded below.** If
`f : E →ₗ[𝕜] F` is topologically inducing (`Topology.IsInducing f`), then `‖x‖ ≤ C * ‖f x‖` for a
single constant `C > 0`. Neither injectivity, completeness, nor Hausdorffness is needed. -/
theorem exists_pos_norm_le_mul_norm_of_isInducing (f : E →ₗ[𝕜] F) (hf : IsInducing f) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖x‖ ≤ C * ‖f x‖ := by
  obtain ⟨s, C, hC, h⟩ := Seminorm.bound_comp_of_isInducing (p := normSeminorm 𝕜 E)
    continuous_norm (norm_withSeminorms 𝕜 F) hf
  refine ⟨C, NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hC), fun x ↦ ?_⟩
  have hsup : s.sup (fun _ ↦ normSeminorm 𝕜 F) ≤ normSeminorm 𝕜 F :=
    Finset.sup_le fun _ _ ↦ le_rfl
  calc
    ‖x‖ = normSeminorm 𝕜 E x := rfl
    _ ≤ (C • s.sup (fun _ ↦ normSeminorm 𝕜 F)).comp f x := h x
    _ = (C : ℝ) * s.sup (fun _ ↦ normSeminorm 𝕜 F) (f x) := rfl
    _ ≤ (C : ℝ) * ‖f x‖ := mul_le_mul_of_nonneg_left (hsup (f x)) C.coe_nonneg

/-- An inducing linear map over a nontrivially normed field is antilipschitz. -/
theorem exists_antilipschitzWith_of_isInducing (f : E →ₗ[𝕜] F) (hf : IsInducing f) :
    ∃ K : NNReal, 0 < K ∧ AntilipschitzWith K f := by
  obtain ⟨C, hC, hbound⟩ := f.exists_pos_norm_le_mul_norm_of_isInducing hf
  refine ⟨Real.toNNReal C, Real.toNNReal_pos.mpr hC, AntilipschitzWith.of_le_mul_dist fun x y ↦ ?_⟩
  rw [dist_eq_norm, dist_eq_norm, ← map_sub, Real.coe_toNNReal C hC.le]
  exact hbound (x - y)

/-- **A strict injective linear map over a nontrivially normed field is bounded below.** -/
theorem exists_pos_norm_le_mul_norm_of_isStrictMap_of_injective (f : E →ₗ[𝕜] F)
    (hf : IsStrictMap f) (hinj : Function.Injective f) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E, ‖x‖ ≤ C * ‖f x‖ :=
  f.exists_pos_norm_le_mul_norm_of_isInducing
    (isEmbedding_iff_isStrictMap_injective.mpr ⟨hf, hinj⟩).isInducing

end LinearMap
