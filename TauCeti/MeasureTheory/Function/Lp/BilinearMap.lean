/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder

/-!
# Bilinear maps with `L∞` coefficients on `Lᵖ` spaces

An essentially bounded field of continuous bilinear maps acts on an `Lᵖ` function and an `Lᵠ`
function, for Hölder conjugate exponents `p` and `q`, by pointwise evaluation and integration.
This file packages that operation as a continuous bilinear map using Mathlib's Hölder
multiplication and `Lᵖ` pairing.  The motivating case is a field of bilinear forms acting on two
square-integrable functions.

The integrability of the pointwise action, for functions rather than `Lᵖ` classes, is
`MeasureTheory.MemLp.integrable_bilinear_apply` in `TauCeti.MeasureTheory.Function.Holder`.

## Main declarations

* `TauCeti.lpBilinearMap`: the continuous bilinear map associated to an `L∞` field.
* `TauCeti.lpBilinearMap_apply`: its integral characterization.
* `MeasureTheory.MemLp.smul_mul`: an essentially bounded function `V` gives the essentially
  bounded field `z ↦ V z • (s, t) ↦ s t` of bilinear forms on `ℝ`.
-/

public section

noncomputable section

namespace TauCeti

open ENNReal MeasureTheory

variable {X 𝕜 E F G : Type*} [MeasurableSpace X] [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G]
  [CompleteSpace G]
variable {p q : ℝ≥0∞} [HolderConjugate p q] [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- The continuous bilinear map obtained by integrating an essentially bounded field of
continuous bilinear maps against an `Lᵖ` function and an `Lᵠ` function, for Hölder conjugate
exponents `p` and `q`. -/
noncomputable def lpBilinearMap (μ : Measure X) (B : Lp (E →L[𝕜] F →L[𝕜] G) ⊤ μ) :
    Lp E p μ →L[𝕜] Lp F q μ →L[𝕜] G :=
  ((ContinuousLinearMap.id 𝕜 (F →L[𝕜] G)).lpPairing μ p q).comp
    ((ContinuousLinearMap.id 𝕜 (E →L[𝕜] F →L[𝕜] G)).holderL μ ⊤ p p B)

/-- The bilinear map with `L∞` coefficients is the integral of its pointwise action. -/
@[simp]
theorem lpBilinearMap_apply (μ : Measure X) (B : Lp (E →L[𝕜] F →L[𝕜] G) ⊤ μ) (U : Lp E p μ)
    (V : Lp F q μ) : lpBilinearMap μ B U V = ∫ x, B x (U x) (V x) ∂μ := by
  rw [lpBilinearMap, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.id 𝕜 (E →L[𝕜] F →L[𝕜] G)).coeFn_holder
    (𝕜 := 𝕜) (r := p) B U] with x hx
  simp [hx]

end TauCeti

namespace MeasureTheory

/-- An essentially bounded function `V` gives the essentially bounded field
`z ↦ V z • (s, t) ↦ s t` of bilinear forms on `ℝ`, the coefficient field of the bilinear form
`(u, v) ↦ ∫ V u v`. -/
theorem MemLp.smul_mul {X : Type*} [MeasurableSpace X] {μ : Measure X} {V : X → ℝ}
    (hV : MemLp V ⊤ μ) : MemLp (fun z ↦ V z • ContinuousLinearMap.mul ℝ ℝ) ⊤ μ := by
  -- The source and target of the composed map are named explicitly: unification does not
  -- recover them from the expected type.
  convert ContinuousLinearMap.comp_memLp' (𝕜 := ℝ) (𝕜' := ℝ) (σ := RingHom.id ℝ)
    (F := ℝ →L[ℝ] ℝ →L[ℝ] ℝ)
    ((ContinuousLinearMap.id ℝ ℝ).smulRight (ContinuousLinearMap.mul ℝ ℝ) :
      ℝ →L[ℝ] ℝ →L[ℝ] ℝ →L[ℝ] ℝ) hV using 1
  ext z
  simp

end MeasureTheory

end
