/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic

/-!
# The third derivative of a composition along a curve

Faà di Bruno's formula `iteratedDeriv_vcomp_three` writes the third derivative of `g ∘ X` at `x`
as four terms. After a continuous linear map `L` that vanishes on the range of `Dg(X x)`, the
term with the third derivative of the curve drops out. What remains is the third derivative of
`g` in the direction of the velocity `X'(x)` and the second derivative of `g` paired with the
velocity and the acceleration `X''(x)`.

## Main results

* `TauCeti.iteratedDeriv_three_comp_of_apply_fderiv_eq_zero`: if `L ∘ Dg(X x) = 0`, then
  `(L ∘ g ∘ X)'''(x) = L (D³g (X', X', X')) + L (D²g (X'', X')) + 2 L (D²g (X', X''))`.
-/

public section

namespace TauCeti

variable {𝕜 F G H : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- **The third derivative of a composition along a curve, projected.** If `g` and the curve `X`
are `C³` and `L` vanishes on the range of `Dg(X x)`, then the third derivative of
`a ↦ L (g (X a))` at `x` is `L (D³g (X', X', X')) + L (D²g (X'', X')) + 2 L (D²g (X', X''))`,
with all derivatives of `g` taken at `X x` and those of `X` at `x`. -/
theorem iteratedDeriv_three_comp_of_apply_fderiv_eq_zero {g : F → G} {L : G →L[𝕜] H}
    {X : 𝕜 → F} {x : 𝕜} (hg : ContDiffAt 𝕜 3 g (X x)) (hX : ContDiffAt 𝕜 3 X x)
    (hL : ∀ y, L (fderiv 𝕜 g (X x) y) = 0) :
    iteratedDeriv 3 (fun a ↦ L (g (X a))) x =
      L (fderiv 𝕜 (fderiv 𝕜 (fderiv 𝕜 g)) (X x) (deriv X x) (deriv X x) (deriv X x)) +
        L (fderiv 𝕜 (fderiv 𝕜 g) (X x) (iteratedDeriv 2 X x) (deriv X x)) +
        2 • L (fderiv 𝕜 (fderiv 𝕜 g) (X x) (deriv X x) (iteratedDeriv 2 X x)) := by
  -- Faà di Bruno's formula for `(L ∘ g) ∘ X`; `L ∘ Dg(X x) = 0` kills its last term.
  have hLg : fderiv 𝕜 (L ∘ g) (X x) = L.comp (fderiv 𝕜 g (X x)) :=
    (L.hasFDerivAt.comp (X x) (hg.differentiableAt (by norm_num)).hasFDerivAt).fderiv
  have h₃ := iteratedDeriv_vcomp_three (L.contDiff.contDiffAt.comp (X x) hg) hX
  rw [L.iteratedFDeriv_comp_left hg le_rfl, L.iteratedFDeriv_comp_left hg (i := 2) (by norm_num),
    hLg] at h₃
  simpa [Function.comp_def, hL, iteratedFDeriv_three_apply, iteratedFDeriv_two_apply] using h₃

end TauCeti
