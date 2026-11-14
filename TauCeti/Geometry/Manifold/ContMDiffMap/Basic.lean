/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# Basic lemmas on bundled `C^n` maps

This file evaluates Mathlib's constant `C^n` map `ContMDiffMap.const` pointwise
(`ContMDiffMap.const_apply`).
-/

public section

open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners 𝕜 E' H'} {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {n : WithTop ℕ∞}

/-- The constant `C^n` map with value `y` takes the value `y` at every point. -/
@[simp]
theorem const_apply (y : M') (x : M) : (const y : C^n⟮I, M; I', M'⟯) x = y :=
  rfl

end ContMDiffMap
