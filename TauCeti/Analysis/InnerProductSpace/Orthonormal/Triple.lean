/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Orthonormal triples

The relations of an orthonormal triple `![a, b, c]`, read off by index: each vector is a unit
vector (`Orthonormal.norm_eq_one_vecCons_zero`, `Orthonormal.norm_eq_one_vecCons_one`,
`Orthonormal.norm_eq_one_vecCons_two`) and any two distinct vectors are orthogonal
(`Orthonormal.inner_eq_zero_vecCons_zero_one`, `Orthonormal.inner_eq_zero_vecCons_zero_two`,
`Orthonormal.inner_eq_zero_vecCons_one_two`).
-/

public section

open scoped InnerProductSpace

namespace Orthonormal

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] {a b c : E}
  (h : Orthonormal 𝕜 ![a, b, c])
include h

/-- The first vector of an orthonormal triple is a unit vector. -/
theorem norm_eq_one_vecCons_zero : ‖a‖ = 1 := by
  simpa using h.norm_eq_one 0

/-- The second vector of an orthonormal triple is a unit vector. -/
theorem norm_eq_one_vecCons_one : ‖b‖ = 1 := by
  simpa using h.norm_eq_one 1

/-- The third vector of an orthonormal triple is a unit vector. -/
theorem norm_eq_one_vecCons_two : ‖c‖ = 1 := by
  simpa using h.norm_eq_one 2

/-- The first two vectors of an orthonormal triple are orthogonal. -/
theorem inner_eq_zero_vecCons_zero_one : ⟪a, b⟫_𝕜 = 0 := by
  simpa using h.inner_eq_zero (by decide : (0 : Fin 3) ≠ 1)

/-- The first and third vectors of an orthonormal triple are orthogonal. -/
theorem inner_eq_zero_vecCons_zero_two : ⟪a, c⟫_𝕜 = 0 := by
  simpa using h.inner_eq_zero (by decide : (0 : Fin 3) ≠ 2)

/-- The last two vectors of an orthonormal triple are orthogonal. -/
theorem inner_eq_zero_vecCons_one_two : ⟪b, c⟫_𝕜 = 0 := by
  simpa using h.inner_eq_zero (by decide : (1 : Fin 3) ≠ 2)

end Orthonormal
