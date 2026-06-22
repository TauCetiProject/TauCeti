/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Algebra.Ring.Parity
import TauCeti.Geometry.Symplectic.ComplexModule

/-!
# An almost complex structure forces even real dimension

A pointwise almost complex structure `J` on a real module `V` turns `V` into a complex vector
space (`TauCeti.AlmostComplexStructure.complexModule`), where multiplication by `i` is `J`. Since
`ℂ` is a degree-two extension of `ℝ`, the tower law forces the real dimension of `V` to be twice
its complex dimension, hence even. This is the classical fact that a manifold (or vector bundle)
admitting an almost complex structure is even-dimensional (McDuff--Salamon, *J-holomorphic Curves
and Symplectic Topology*, Section 2.1), recorded here at the pointwise linear-algebra level.

Everything is stated without a finite-dimensionality hypothesis: the tower law
`Module.finrank_mul_finrank` holds for `Module.finrank` unconditionally (an infinite-dimensional
`V` has `Module.finrank ℝ V = 0 = 2 * 0`), so the identities below need no `FiniteDimensional`
assumption.

## Main declarations

* `TauCeti.AlmostComplexStructure.complexFinrank`: the `ℂ`-dimension of `V` under the complex
  module structure induced by `J`.
* `TauCeti.AlmostComplexStructure.finrank_real_eq_two_mul_complexFinrank`: the real dimension is
  twice the complex dimension, `finrank ℝ V = 2 * J.complexFinrank`.
* `TauCeti.AlmostComplexStructure.even_finrank_real`: the real dimension of a module carrying an
  almost complex structure is even.
* `TauCeti.AlmostComplexStructure.isEmpty_of_odd_finrank`: an odd-dimensional real module admits no
  almost complex structure.

The conventions follow McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1.
-/

namespace TauCeti

namespace AlmostComplexStructure

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The complex dimension of `V` with respect to an almost complex structure `J`: the
`ℂ`-dimension of `V` under the complex module structure induced by `J`
(`AlmostComplexStructure.complexModule`). -/
noncomputable def complexFinrank (J : AlmostComplexStructure V) : ℕ :=
  letI := J.complexModule
  Module.finrank ℂ V

/-- The real dimension of a module carrying an almost complex structure `J` is twice its complex
dimension: `finrank ℝ V = 2 * J.complexFinrank`. This is the tower law `finrank ℝ V =
finrank ℝ ℂ * finrank ℂ V` together with `finrank ℝ ℂ = 2`. -/
theorem finrank_real_eq_two_mul_complexFinrank (J : AlmostComplexStructure V) :
    Module.finrank ℝ V = 2 * J.complexFinrank := by
  letI := J.complexModule
  letI := J.complexModule_isScalarTower
  change Module.finrank ℝ V = 2 * Module.finrank ℂ V
  rw [← Module.finrank_mul_finrank ℝ ℂ V, Complex.finrank_real_complex]

/-- The real dimension of a module carrying an almost complex structure is even. -/
theorem even_finrank_real (J : AlmostComplexStructure V) :
    Even (Module.finrank ℝ V) := by
  rw [J.finrank_real_eq_two_mul_complexFinrank]
  exact even_two_mul _

/-- An odd-dimensional real module admits no almost complex structure. -/
theorem isEmpty_of_odd_finrank (h : Odd (Module.finrank ℝ V)) :
    IsEmpty (AlmostComplexStructure V) :=
  ⟨fun J => (Nat.not_odd_iff_even.mpr J.even_finrank_real) h⟩

end AlmostComplexStructure

end TauCeti
