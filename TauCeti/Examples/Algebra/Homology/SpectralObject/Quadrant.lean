/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.SpectralObject.ConvergenceBounds

/-!
# Convergence bounds of quadrant spectral objects: checks

For a first-quadrant spectral object `X`, the groups `H^m(⊥ ≤ i)` vanish for `i ≤ 0`, and the two
outer terms of the exact sequence `H^{n-1}(j ≤ ⊤) ⟶ H^n(⊥ ≤ j) ⟶ H^n(⊥ ≤ ⊤) ⟶ H^n(j ≤ ⊤)` vanish
for `j ≥ n + 1`; so `X` has convergence bounds `0, 1` in degree `0`, and its abutment vanishes in
degree `-1`. A third-quadrant spectral object has convergence bounds `-2, 1` in cohomological
degree `-2`.
-/

namespace TauCeti.Examples.SpectralObjectQuadrant

open CategoryTheory Limits ComposableArrows CategoryTheory.Abelian

variable {C : Type*} [Category* C] [Abelian C] (X : SpectralObject C EInt)

/-- A first-quadrant spectral object has `H^m(⊥ ≤ i) = 0` for `i ≤ 0`. -/
example [X.IsFirstQuadrant] (m i : ℤ) (hi : i ≤ 0) :
    IsZero ((X.H m).obj (mk₁ (homOfLE (bot_le : (⊥ : EInt) ≤ i)))) :=
  X.isZero₁_of_isFirstQuadrant _ _ _ (by simpa using hi) _

/-- For a first-quadrant spectral object, `H^{n-1}(j ≤ ⊤)` and `H^n(j ≤ ⊤)` vanish for
`j ≥ n + 1`. -/
example [X.IsFirstQuadrant] (n j : ℤ) (hj : n + 1 ≤ j) :
    IsZero ((X.H (n - 1)).obj (mk₁ (homOfLE (le_top : (j : EInt) ≤ ⊤)))) ∧
      IsZero ((X.H n).obj (mk₁ (homOfLE (le_top : (j : EInt) ≤ ⊤)))) :=
  ⟨X.isZero₂_of_isFirstQuadrant _ _ _ _ (by simp; lia),
    X.isZero₂_of_isFirstQuadrant _ _ _ _ (by simp; lia)⟩

/-- In total degree `0`, a first-quadrant spectral object has convergence bounds `0, 1`. -/
example [X.IsFirstQuadrant] : X.HasConvergenceBounds 0 0 1 := by
  simpa using X.hasConvergenceBounds_of_isFirstQuadrant 0

/-- The abutment of a first-quadrant spectral object vanishes in degree `-1`. -/
example [X.IsFirstQuadrant] : IsZero (X.abutment (-1)) :=
  X.isZero_abutment_of_isFirstQuadrant (by norm_num)

/-- In cohomological degree `-2`, a third-quadrant spectral object has convergence bounds
`a = -2` and `b = 1`. -/
example [X.IsThirdQuadrant] : X.HasConvergenceBounds (-2) (-2) 1 := by
  simpa using X.hasConvergenceBounds_of_isThirdQuadrant (-2)

end TauCeti.Examples.SpectralObjectQuadrant
