/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.NumberTheory.NumberField.FractionalIdeal

/-!
# The index of one fractional ideal in another

An invertible fractional ideal of a number field `K` is a full `ℤ`-lattice in `K`.  If `J ≤ I` are
two such ideals, the index of `J` in `I` is the ratio of their absolute norms.  The index is
computed from the determinant formula `NumberField.det_basisOfFractionalIdeal_eq_absNorm` and
`AddSubgroup.relIndex_eq_abs_det`.

## Main results

* `NumberField.relIndex_fractionalIdeal_eq_absNorm_div_absNorm`: the index of `J` in `I`, as
  additive subgroups of `K`, is `absNorm J / absNorm I`.
-/

public section

open NumberField
open scoped nonZeroDivisors

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **The index of a fractional ideal in a larger one is the ratio of the norms.**  For invertible
fractional ideals `J ≤ I` of a number field, the index of `J` in `I`, as additive subgroups of the
field, is `absNorm J / absNorm I`. -/
theorem relIndex_fractionalIdeal_eq_absNorm_div_absNorm {I J : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hJI : (J : FractionalIdeal (𝓞 K)⁰ K) ≤ I) :
    ((J : Submodule (𝓞 K) K).toAddSubgroup.relIndex (I : Submodule (𝓞 K) K).toAddSubgroup : ℚ) =
      FractionalIdeal.absNorm (J : FractionalIdeal (𝓞 K)⁰ K) /
        FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) := by
  -- Reindex the `ℚ`-bases of `K` coming from `ℤ`-bases of `I` and `J` by the index type of the
  -- integral basis, so that all three bases share one index type.
  let e (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :=
    (integralBasis K).indexEquiv (basisOfFractionalIdeal K L)
  let b (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) := (basisOfFractionalIdeal K L).reindex (e L).symm
  have closure_eq (L : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      (L : Submodule (𝓞 K) K).toAddSubgroup = AddSubgroup.closure (Set.range (b L)) := by
    ext x
    simp [b, ← Submodule.span_int_eq_addSubgroupClosure, mem_span_basisOfFractionalIdeal]
  rw [AddSubgroup.relIndex_eq_abs_det _ _ hJI (b J) (b I) (closure_eq J) (closure_eq I),
    ← det_basisOfFractionalIdeal_eq_absNorm K I (e I),
    ← det_basisOfFractionalIdeal_eq_absNorm K J (e J), ← (integralBasis K).det_mul_det (b I) (b J),
    abs_mul, mul_div_cancel_left₀ _ (abs_ne_zero.mpr ((integralBasis K).isUnit_det _).ne_zero)]

end NumberField
