/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Homotopies given by maps on `ℝ × X`

A continuous map `F : ℝ × X → Y` with `F (0, ·) = f` and `F (1, ·) = g` restricts to a homotopy
from `f` to `g` on `[0, 1] × X` (`TauCeti.homotopyOfRealProd`). Smooth homotopies of manifolds are
usually given in this form, since smoothness is a condition on an open domain.
-/

public section

open scoped unitInterval

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f g : C(X, Y)} {F : ℝ × X → Y}

/-- The homotopy from `f` to `g` obtained by restricting a continuous map `F : ℝ × X → Y`, with
`F (0, ·) = f` and `F (1, ·) = g`, to `[0, 1] × X`. -/
def homotopyOfRealProd (hF : Continuous F) (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x) :
    ContinuousMap.Homotopy f g where
  toFun p := F (p.1, p.2)
  continuous_toFun := hF.comp (continuous_subtypeVal.prodMap continuous_id)
  map_zero_left := h₀
  map_one_left := h₁

/-- The homotopy obtained by restricting `F` to `[0, 1] × X` takes the values of `F`. -/
@[simp]
theorem homotopyOfRealProd_apply (hF : Continuous F) (h₀ : ∀ x, F (0, x) = f x)
    (h₁ : ∀ x, F (1, x) = g x) (p : I × X) :
    homotopyOfRealProd hF h₀ h₁ p = F (p.1, p.2) :=
  (rfl)

end TauCeti
