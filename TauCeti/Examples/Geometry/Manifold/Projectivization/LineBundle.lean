/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Analysis.Complex.Basic
import TauCeti.Geometry.Manifold.Projectivization.LineBundle

/-!
# Examples: the line bundles `𝒪(k)` on `ℂℙⁿ`

These examples check the line bundles `𝒪(k)` on complex projective space `ℂℙⁿ`, constructed as
the vector-bundle cores `Projectivization.twistCore k`:

* for every integer `k`, instance search finds that `𝒪(k)` is a holomorphic vector bundle;
* the coordinate function `X 0` gives a holomorphic section of the hyperplane bundle `𝒪(1)`,
  vanishing exactly on the hyperplane `{v 0 = 0}`;
* the transitions of `𝒪(-1)` are the coordinate changes of vectors in the line, so `𝒪(-1)` is
  the tautological line bundle.
-/

open Bundle MvPolynomial Projectivization
open scoped Manifold ContDiff LinearAlgebra.Projectivization

variable {n : ℕ}

-- For every integer `k`, `𝒪(k)` is a holomorphic line bundle on `ℂℙⁿ`.
example (k : ℤ) :
    ContMDiffVectorBundle ω ℂ (twistCore (𝕜 := ℂ) (n := n) k).Fiber 𝓘(ℂ, Fin n → ℂ) :=
  inferInstance

example (k : ℤ) :
    ContMDiffVectorBundle ∞ ℂ (twistCore (𝕜 := ℂ) (n := n) k).Fiber 𝓘(ℂ, Fin n → ℂ) :=
  inferInstance

-- The coordinate `X 0` is a holomorphic section of the hyperplane bundle `𝒪(1)` on `ℂℙⁿ`.
example :
    ContMDiff 𝓘(ℂ, Fin n → ℂ) (𝓘(ℂ, Fin n → ℂ).prod 𝓘(ℂ)) ω
      (fun x ↦ TotalSpace.mk' ℂ (E := (twistCore (𝕜 := ℂ) (n := n) ((1 : ℕ) : ℤ)).Fiber) x
        (homogeneousSection (𝕜 := ℂ) 1 (X 0) x)) :=
  contMDiff_homogeneousSection (isHomogeneous_X ℂ 0) ω

-- It vanishes exactly on the hyperplane `{v 0 = 0}`.
example (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    homogeneousSection 1 (X 0) (mk ℂ v hv) = 0 ↔ v 0 = 0 := by
  rw [homogeneousSection_mk_eq_zero_iff (isHomogeneous_X ℂ 0), eval_X]

-- The section of `𝒪(1)` defined by a nonzero linear form is not identically zero.
example : homogeneousSection (𝕜 := ℂ) 1 (X (0 : Fin (n + 1))) ≠ 0 := by
  rw [Ne, homogeneousSection_eq_zero_iff (isHomogeneous_X ℂ 0)]
  exact X_ne_zero 0

-- A vector `w` of the line `x` changes coordinates by the transitions of `𝒪(-1)`.
example {i j : Fin (n + 1)} {x : ℙ ℂ (Fin (n + 1) → ℂ)} (hi : x ∈ affineOpen i)
    {w : Fin (n + 1) → ℂ} (hw : w ∈ x.submodule) :
    (twistCore (-1)).coordChange i j x (w i) = w j := by
  rw [twistCore_coordChange_apply, twistTransition_neg_one_mul j hi hw]
