/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RingTheory.Semisimple.PositiveInvolution
public import TauCeti.RingTheory.Semisimple.PositiveInvolution.Center

/-!
# The centre of a simple algebra with a positive involution: examples

* The transpose of `M_2(ℚ)` induces the identity on the centre `ℚ`, which is totally real.
* Its trace positivity `Tr_{ℚ/ℚ}(x σ(x)) > 0` on the centre.
* On `ℚ` itself, the fixed field of the induced involution is totally real.
-/

public section

open TauCeti TauCeti.PositiveInvolutionExamples NumberField

namespace TauCeti.PositiveInvolutionCenterExamples

/-- The transpose of `M_2(ℚ)` induces the identity on the centre `ℚ`. -/
example : (transpose (Fin 2)).centerInvolution ℚ = RingHom.id ℚ :=
  Subsingleton.elim _ _

/-- The induced involution of the transpose on the centre `ℚ` of `M_2(ℚ)` is positive for the
trace: `Tr_{ℚ/ℚ}(x σ(x)) = x² > 0`. -/
example {x : ℚ} (hx : x ≠ 0) :
    0 < Algebra.trace ℚ ℚ (x * (transpose (Fin 2)).centerInvolution ℚ x) :=
  (transpose (Fin 2)).trace_mul_centerInvolution_pos ℚ hx

/-- The fixed field of the identity involution of `ℚ` is totally real. -/
example : IsTotallyReal ((rat.centerInvolution ℚ).eqLocusField (RingHom.id ℚ)) :=
  rat.fixedCenter_totallyReal ℚ

end TauCeti.PositiveInvolutionCenterExamples
