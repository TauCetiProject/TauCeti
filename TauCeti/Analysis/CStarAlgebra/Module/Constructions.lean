/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions

/-!
# The row–column inequality in a C⋆-algebra

A finite family `(u i)` in a C⋆-algebra `A` is a row `[u₁ ⋯ uₙ]` and a family `(v i)` is a column;
their product is `∑ᵢ uᵢ vᵢ`, and the norms of the row and of the column are
`‖∑ᵢ uᵢ uᵢ*‖^(1/2)` and `‖∑ᵢ vᵢ* vᵢ‖^(1/2)`. The norm of the product is at most the product of
these norms. This is the Cauchy–Schwarz inequality `‖⟪x, y⟫‖ ≤ ‖x‖ ‖y‖` of the Hilbert
`A`-module `Aⁿ` (Mathlib's `C⋆ᵐᵒᵈ(A, ι → A)`), whose inner product is `⟪x, y⟫ = ∑ᵢ yᵢ xᵢ*`.

## References

* G. Pisier, *Grothendieck's theorem, past and present*, Bull. Amer. Math. Soc. 49 (2012),
  237–323, §9 (the row–column estimate in the proof of Lemma 9.2).
-/

public section

open CStarModule

namespace TauCeti

variable {ι A : Type*} [Fintype ι] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **The row–column inequality.** In a C⋆-algebra,
`‖∑ᵢ uᵢ vᵢ‖ ≤ ‖∑ᵢ uᵢ uᵢ*‖^(1/2) ‖∑ᵢ vᵢ* vᵢ‖^(1/2)`: the product of a row and a column has norm
at most the product of their norms. -/
theorem norm_sum_mul_le_sqrt_mul_sqrt (u v : ι → A) :
    ‖∑ i, u i * v i‖ ≤ √‖∑ i, u i * star (u i)‖ * √‖∑ i, star (v i) * v i‖ := by
  have h := norm_inner_le (A := A) (WithCStarModule A (ι → A))
    (x := (WithCStarModule.equiv A (ι → A)).symm fun i => star (v i))
    (y := (WithCStarModule.equiv A (ι → A)).symm u)
  simp only [WithCStarModule.pi_inner, WithCStarModule.pi_norm, WithCStarModule.inner_def,
    WithCStarModule.equiv_symm_pi_apply, star_star] at h
  rwa [mul_comm (√_)]

end TauCeti
