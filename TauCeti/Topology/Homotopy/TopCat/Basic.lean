/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.TopCat.Basic

/-!
# Homotopies in `TopCat` from continuous maps on `ℝ × X`

Given a continuous map `F : ℝ × X → Y` with `F (0, x) = f x` and `F (1, x) = g x`, restricting the
time coordinate to `unitInterval` yields a homotopy `Continuous.toTopCatHomotopy` in `TopCat`
between the morphisms induced by `f` and `g`. This packages homotopies naturally defined on the
entire real line (such as smooth homotopies on manifolds) as morphisms in `TopCat.Homotopy`.

## Main definitions and results

* `Continuous.toTopCatHomotopy`: the `TopCat.Homotopy` obtained by restricting a continuous map
  `F : ℝ × X → Y` with `F (0, ·) = f` and `F (1, ·) = g` to `[0, 1] × X`.
* `Continuous.toTopCatHomotopy_apply`: evaluating `hF.toTopCatHomotopy h₀ h₁` at `p : [0, 1] × X`
  gives `F (p.1, p.2)`.
-/

public section

universe u

namespace Continuous

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : X → Y} {F : ℝ × X → Y}

/-- The `[0, 1]`-homotopy in `TopCat` obtained by restricting a continuous map `F : ℝ × X → Y` with
`F (0, ·) = f` and `F (1, ·) = g`. -/
def toTopCatHomotopy (hF : Continuous F)
    (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x) :
    TopCat.Homotopy
      (TopCat.ofHom ⟨f, (hF.comp (continuous_const.prodMk continuous_id)).congr h₀⟩)
      (TopCat.ofHom ⟨g, (hF.comp (continuous_const.prodMk continuous_id)).congr h₁⟩) where
  toFun p := F (p.1, p.2)
  continuous_toFun := hF.comp (continuous_subtype_val.prodMap continuous_id)
  map_zero_left := h₀
  map_one_left := h₁

/-- Evaluating `hF.toTopCatHomotopy h₀ h₁` on `p : [0, 1] × X` evaluates `F` at `(p.1, p.2)`. -/
@[simp]
theorem toTopCatHomotopy_apply (hF : Continuous F)
    (h₀ : ∀ x, F (0, x) = f x) (h₁ : ∀ x, F (1, x) = g x) (p : unitInterval × X) :
    hF.toTopCatHomotopy h₀ h₁ p = F (p.1, p.2) :=
  (rfl)

end Continuous
