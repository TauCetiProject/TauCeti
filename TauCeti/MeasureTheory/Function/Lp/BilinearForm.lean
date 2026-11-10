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

## Main declarations

* `TauCeti.lpBilinearForm`: the continuous bilinear map associated to an `L∞` field.
* `TauCeti.lpBilinearForm_apply`: its integral characterization.
* `TauCeti.integrable_bilinear_apply_of_memLp`: integrability of the pointwise action.
-/

public section

noncomputable section

namespace TauCeti

open ENNReal MeasureTheory

variable {X 𝕜 E F G : Type*} [MeasurableSpace X] [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable [NormedAddCommGroup G] [NormedSpace 𝕜 G]
variable {p q : ℝ≥0∞} [HolderConjugate p q]

section Pairing

variable [Fact (1 ≤ p)] [Fact (1 ≤ q)] [NormedSpace ℝ G] [SMulCommClass ℝ 𝕜 G] [CompleteSpace G]

/-- The continuous bilinear map obtained by integrating an essentially bounded field of
continuous bilinear maps against an `Lᵖ` function and an `Lᵠ` function, for Hölder conjugate
exponents `p` and `q`. -/
noncomputable def lpBilinearForm (μ : Measure X) (B : Lp (E →L[𝕜] F →L[𝕜] G) ⊤ μ) :
    Lp E p μ →L[𝕜] Lp F q μ →L[𝕜] G :=
  ((ContinuousLinearMap.id 𝕜 (F →L[𝕜] G)).lpPairing μ p q).comp
    ((ContinuousLinearMap.id 𝕜 (E →L[𝕜] F →L[𝕜] G)).holderL μ ⊤ p p B)

/-- The bilinear map with `L∞` coefficients is the integral of its pointwise action. -/
@[simp]
theorem lpBilinearForm_apply (μ : Measure X) (B : Lp (E →L[𝕜] F →L[𝕜] G) ⊤ μ) (U : Lp E p μ)
    (V : Lp F q μ) : lpBilinearForm μ B U V = ∫ x, B x (U x) (V x) ∂μ := by
  rw [lpBilinearForm, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [(ContinuousLinearMap.id 𝕜 (E →L[𝕜] F →L[𝕜] G)).coeFn_holder
    (𝕜 := 𝕜) (r := p) B U] with x hx
  simp [hx]

end Pairing

/-- Applying an `L∞` field of continuous bilinear maps to an `Lᵖ` function and an `Lᵠ` function,
for Hölder conjugate exponents `p` and `q`, gives an integrable function. -/
theorem integrable_bilinear_apply_of_memLp {μ : Measure X} {B : X → E →L[𝕜] F →L[𝕜] G}
    {f : X → E} {g : X → F} (hB : MemLp B ⊤ μ) (hf : MemLp f p μ) (hg : MemLp g q μ) :
    Integrable (fun x => B x (f x) (g x)) μ := by
  -- The Hölder exponents are pinned explicitly, and the application goes through `exact`:
  -- elaborating it against the expected type in term mode unfolds `MemLp` and loops.
  have hBf : MemLp (fun x => B x (f x)) p μ := by
    exact (ContinuousLinearMap.id 𝕜 (E →L[𝕜] F →L[𝕜] G)).memLp_of_bilin (𝕜 := 𝕜)
      (p := ⊤) (q := p) (f := B) (g := f) p hB hf
  exact memLp_one_iff_integrable.mp
    ((ContinuousLinearMap.id 𝕜 (F →L[𝕜] G)).memLp_of_bilin
      (p := p) (q := q) (f := fun x => B x (f x)) (g := g) 1 hBf hg)

end TauCeti

end
