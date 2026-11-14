/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Homotopies from real-parameter families

`ContinuousMap.Homotopy.ofReal` restricts a continuous family on `ℝ × X` to the unit interval.
This lets families defined for every real time, such as jointly smooth families, use the usual
homotopy API with their given endpoint maps.
-/

public section

namespace ContinuousMap.Homotopy

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)} {F : ℝ × X → Y}

/-- Restrict a continuous real-parameter family with endpoints `f` and `g` to a homotopy. -/
def ofReal (hF : Continuous F) (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x) :
    Homotopy f g where
  toFun p := F (p.1, p.2)
  continuous_toFun := hF.comp (continuous_subtype_val.prodMap continuous_id)
  map_zero_left := h₀
  map_one_left := h₁

/-- Restricting a real-parameter family evaluates it at the same time and point. -/
@[simp]
theorem ofReal_apply (hF : Continuous F) (h₀ : ∀ x, F (0, x) = f x)
    (h₁ : ∀ x, F (1, x) = g x) (p : unitInterval × X) :
    ofReal hF h₀ h₁ p = F (p.1, p.2) :=
  (rfl)

end ContinuousMap.Homotopy
