/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Alternating.Uncurry.Fin

/-!
# Alternatization and interior products

For a continuous linear map `f : E →L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] F` and a vector `y`, the two ways
of combining the alternatization `ContinuousAlternatingMap.alternatizeUncurryFin` with the
interior product `ι_y = ContinuousAlternatingMap.curryLeft · y` add up to evaluation at `y`:

`alternatizeUncurryFin (ι_y ∘ f) + ι_y (alternatizeUncurryFin f) = f y`.

Applied to the derivative `f = Dω(x)` of a differential form, this is the pointwise form of
Cartan's formula `d ι_y + ι_y d = L_y` for the constant vector field `y`. It is the algebraic
identity behind the homotopy formula of the Poincaré lemma.

## Main declarations

* `ContinuousAlternatingMap.alternatizeUncurryFin_curryLeft_comp_add_curryLeft`: the identity
  above.
-/

public section

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {n : ℕ}

namespace ContinuousAlternatingMap

/-- Alternatizing the interior product with `y` of a family of forms, plus the interior product
with `y` of its alternatization, is evaluation of the family at `y`. This is the pointwise
constant-coefficient case of Cartan's formula `d ι_y + ι_y d = L_y`. -/
theorem alternatizeUncurryFin_curryLeft_comp_add_curryLeft
    (f : E →L[𝕜] E [⋀^Fin (n + 1)]→L[𝕜] F) (y : E) :
    alternatizeUncurryFin ((curryLeftLI (𝕜 := 𝕜) (E := E) (F := F)).toContinuousLinearMap.flip y ∘L
      f) + (alternatizeUncurryFin f).curryLeft y = f y := by
  ext v
  have hremove (i : Fin (n + 1)) :
      Fin.removeNth i.succ (Matrix.vecCons y v) = Matrix.vecCons y (Fin.removeNth i v) := by
    funext j
    cases j using Fin.cases <;> simp [Fin.removeNth_apply]
  rw [add_apply, curryLeft_apply_apply, alternatizeUncurryFin_apply, alternatizeUncurryFin_apply,
    Fin.sum_univ_succ (n := n + 1)]
  simp [hremove, pow_succ]

end ContinuousAlternatingMap
