/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.ZMod.Basic
import TauCeti.LinearAlgebra.QuadraticForm.Arf.Basic
import TauCeti.LinearAlgebra.QuadraticForm.CharTwo

/-!
# Nonsingular binary forms `[a, b]`: checks

These examples test the binary forms `TauCeti.binaryQuadraticForm R a b`, written `[a, b]`, against
the expected answers. The mixed term is present: `[0, 0]` takes the value `1` at `(1, 1)`. The
nonsingularity criterion `1 - 4ab ≠ 0` detects the singular form `[1, 1]` in characteristic three.
Over `𝔽₂` the anisotropic form `[1, 1]` is nonsingular but not hyperbolic, while `[1, 0]` is
hyperbolic. Finally, the form `x ↦ x ^ 2` on the line `𝔽₂` satisfies Mathlib's
`QuadraticMap.Nondegenerate` but has zero polar form, so the comparison
`QuadraticMap.nondegenerate_polar_iff_of_even_finrank` needs its even-dimension hypothesis.

## References

* R. Elman, N. Karpenko, and A. Merkurjev, *The Algebraic and Geometric Theory of Quadratic Forms*,
  American Mathematical Society Colloquium Publications 56 (2008), Chapter II, §7.
-/

open QuadraticMap

namespace TauCeti

/-- The hyperbolic plane `[0, 0]` takes the value `1` at `(1, 1)`: the mixed term `x 0 * x 1` is
part of the form. -/
example {R : Type*} [CommRing R] : binaryQuadraticForm R 0 0 ![1, 1] = 1 := by
  simp

/-- In characteristic three, `4 = 1`, so `1 - 4 * 1 * 1 = 0` and `[1, 1]` is singular. -/
example : ¬(binaryQuadraticForm (ZMod 3) 1 1).polarBilin.Nondegenerate := by
  rw [nondegenerate_polarBilin_binaryQuadraticForm_iff]
  decide

/-- Over `𝔽₂`, `[1, 1]` is nonsingular, since `1 - 4 * 1 * 1 = 1 ≠ 0`. -/
example : (binaryQuadraticForm (ZMod 2) 1 1).polarBilin.Nondegenerate := by
  rw [nondegenerate_polarBilin_binaryQuadraticForm_iff]
  decide

/-- Over `𝔽₂`, the anisotropic nonsingular plane `[1, 1]` is not isometric to the hyperbolic plane
`[0, 0]`. -/
example : ¬(binaryQuadraticForm (ZMod 2) 1 1).Equivalent (binaryQuadraticForm (ZMod 2) 0 0) := by
  rw [equivalent_binaryQuadraticForm_zero_iff_not_anisotropic (by simp)
    (nondegenerate_polarBilin_binaryQuadraticForm 1 1), not_not]
  exact anisotropic_binaryQuadraticForm_one

/-- Over `𝔽₂`, the plane `[1, 0]` vanishes at `(0, 1)`, so it is isometric to the hyperbolic plane
`[0, 0]`. -/
example : (binaryQuadraticForm (ZMod 2) 1 0).Equivalent (binaryQuadraticForm (ZMod 2) 0 0) := by
  rw [equivalent_binaryQuadraticForm_zero_iff_not_anisotropic (by simp)
    (nondegenerate_polarBilin_binaryQuadraticForm 1 0)]
  exact fun h ↦ one_ne_zero (congrFun (h ![0, 1] (by simp)) 1)

/-- The form `x ↦ x ^ 2` on the line `𝔽₂` is nondegenerate in the sense of
`QuadraticMap.Nondegenerate`, although its polar form vanishes: the comparison with nonsingularity
needs even dimension. -/
example : (QuadraticMap.sq : QuadraticForm (ZMod 2) (ZMod 2)).Nondegenerate ∧
    ¬(QuadraticMap.sq : QuadraticForm (ZMod 2) (ZMod 2)).polarBilin.Nondegenerate := by
  have hpolar : (QuadraticMap.sq : QuadraticForm (ZMod 2) (ZMod 2)).polarBilin = 0 := by
    -- A bilinear form on the line `𝔽₂` is determined by its value at `(1, 1)`.
    ext
    simp only [polarBilin_apply_apply, polar, sq_apply, LinearMap.zero_apply]
    decide
  refine ⟨⟨?_, ?_⟩, fun h ↦ ?_⟩
  · refine eq_bot_iff.mpr fun x hx ↦ (Submodule.mem_bot _).mpr ?_
    exact mul_self_eq_zero.mp (by simpa using hx.1)
  · exact (Submodule.rank_le _).trans (Module.rank_self (ZMod 2)).le
  · rw [hpolar] at h
    exact one_ne_zero (h.1 1 fun _ ↦ rfl)

end TauCeti
