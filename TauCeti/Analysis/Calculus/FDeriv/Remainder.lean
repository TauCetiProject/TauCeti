/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# The punctured remainder form of the Fréchet derivative

A map `f` has Fréchet derivative `L` at `x` exactly when the relative remainder
`‖f (x + h) - f x - L h‖ / ‖h‖` tends to `0` as `h → 0` with `h ≠ 0`. This is
Mathlib's `hasFDerivAt_iff_isLittleO_nhds_zero` with the increment `0` removed from the filter,
which is the form in which difference quotients are usually compared.
-/

public section

open Filter Topology

namespace TauCeti

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {L : E →L[𝕜] F} {x : E}

/-- The punctured remainder form of a Fréchet derivative: `f` has derivative `L` at `x` exactly
when `‖f (x + h) - f x - L h‖ / ‖h‖ → 0` as `h → 0`, `h ≠ 0`. -/
theorem hasFDerivAt_iff_tendsto_norm_div_nhdsNE :
    HasFDerivAt f L x ↔ Tendsto (fun h ↦ ‖f (x + h) - f x - L h‖ / ‖h‖) (𝓝[≠] 0) (𝓝 0) := by
  -- The remainder vanishes at `h = 0`, so the point `0` can be removed from the filter.
  have hpunct : HasFDerivAt f L x ↔
      (fun h ↦ f (x + h) - f x - L h) =o[𝓝[≠] 0] fun h ↦ h := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, ← nhdsNE_sup_pure 0, Asymptotics.isLittleO_sup,
      Asymptotics.isLittleO_pure]
    simp
  rw [hpunct, ← Asymptotics.isLittleO_norm_norm,
    Asymptotics.isLittleO_iff_tendsto (by simp +contextual)]

end TauCeti
