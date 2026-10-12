/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Derivatives along coordinate slices of an `L^p` product

For a function `g` on the `L^p` product `WithLp p (F × E)`, freezing one coordinate gives a
function of the other coordinate alone. Its derivative is the derivative of `g` in the
corresponding coordinate direction: along the line `s ↦ (s, y)` in the first factor `𝕜` it is
`fderiv 𝕜 g (t, y) (1, 0)`, and on the slice `z ↦ (t, z)` it is `w ↦ fderiv 𝕜 g (t, y) (0, w)`.
These are the chain rules used to compute integrals over a half-space `{x | a < x.fst}` one
normal line or one tangential slice at a time, as in Fubini-type proofs of the divergence
theorem.

## Main declarations

* `TauCeti.hasDerivAt_comp_toLp_fst`: the derivative of `g` along a line in the first factor is
  its derivative in the direction `(1, 0)`.
* `TauCeti.fderiv_comp_toLp_snd`: the derivative of `g` on a slice of the second factor is its
  derivative in the direction `(0, w)`.
-/

public section

namespace TauCeti

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {p : ENNReal} [Fact (1 ≤ p)]

/-- Along the line `s ↦ (s, y)` in the first factor of `WithLp p (𝕜 × E)`, the derivative of a
function differentiable at `(t, y)` is its derivative in the direction `(1, 0)`. -/
theorem hasDerivAt_comp_toLp_fst {g : WithLp p (𝕜 × E) → G} {t : 𝕜} {y : E}
    (hg : DifferentiableAt 𝕜 g (WithLp.toLp p (t, y))) :
    HasDerivAt (fun s : 𝕜 ↦ g (WithLp.toLp p (s, y)))
      (fderiv 𝕜 g (WithLp.toLp p (t, y)) (WithLp.toLp p (1, (0 : E)))) t := by
  have hl : HasDerivAt (fun s : 𝕜 ↦ WithLp.toLp p (s, y)) (WithLp.toLp p (1, (0 : E))) t :=
    ((WithLp.prodContinuousLinearEquiv p 𝕜 𝕜 E).symm.hasFDerivAt).comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t y))
  exact hg.hasFDerivAt.comp_hasDerivAt t hl

/-- On the slice `z ↦ (t, z)` of the second factor of `WithLp p (F × E)`, the derivative of a
function differentiable at `(t, y)`, applied to a direction `w` of `E`, is its derivative in the
direction `(0, w)`. -/
theorem fderiv_comp_toLp_snd {g : WithLp p (F × E) → G} {t : F} {y : E}
    (hg : DifferentiableAt 𝕜 g (WithLp.toLp p (t, y))) (w : E) :
    fderiv 𝕜 (fun z : E ↦ g (WithLp.toLp p (t, z))) y w =
      fderiv 𝕜 g (WithLp.toLp p (t, y)) (WithLp.toLp p (0, w)) := by
  have hl : HasFDerivAt (fun z : E ↦ WithLp.toLp p (t, z))
      ((WithLp.prodContinuousLinearEquiv p 𝕜 F E).symm.toContinuousLinearMap.comp
        ((0 : E →L[𝕜] F).prod (ContinuousLinearMap.id 𝕜 E))) y :=
    ((WithLp.prodContinuousLinearEquiv p 𝕜 F E).symm.hasFDerivAt).comp y
      ((hasFDerivAt_const t y).prodMk (hasFDerivAt_id y))
  have h : HasFDerivAt (fun z : E ↦ g (WithLp.toLp p (t, z))) _ y := hg.hasFDerivAt.comp y hl
  rw [h.fderiv]
  simp

end TauCeti

end
