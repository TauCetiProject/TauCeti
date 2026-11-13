/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.NumberTheory.NumberField.FractionalIdeal
public import Mathlib.RingTheory.ClassGroup.Basic
import Mathlib.RingTheory.Norm.Basic

/-!
# The index of one fractional ideal in another, and clearing denominators

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

/-- **Clearing the denominator of a fractional ideal.**  A nonzero integer multiple `n I` of an
invertible fractional ideal `I` is a nonzero integral ideal. -/
theorem exists_mk0_eq_toPrincipalIdeal_natCast_mul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ (n : ℕ) (hn : (n : K) ≠ 0) (J : (Ideal (𝓞 K))⁰),
      FractionalIdeal.mk0 K J = toPrincipalIdeal (𝓞 K) K (Units.mk0 (n : K) hn) * I := by
  -- `n = N((d))` for the denominator `d` of `I` is a multiple `b d` of `d`, and `d I` is integral
  set d : 𝓞 K := ((I : FractionalIdeal (𝓞 K)⁰ K).den : 𝓞 K)
  have hd : d ≠ 0 := nonZeroDivisors.coe_ne_zero _
  set n := Ideal.absNorm (Ideal.span {d})
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {d}))
  have hn : (n : K) ≠ 0 := by
    simpa [n, Ideal.absNorm_span_singleton, Algebra.norm_eq_zero_iff] using hd
  have hJ : ((Ideal.span {b} * (I : FractionalIdeal (𝓞 K)⁰ K).num : Ideal (𝓞 K)) :
      FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton _ (n : K) * (I : FractionalIdeal (𝓞 K)⁰ K) := by
    rw [FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_span_singleton,
      ← FractionalIdeal.den_mul_self_eq_num', ← mul_assoc, ← map_mul, ← map_mul, hb,
      map_natCast]
  have hJ0 : Ideal.span {b} * (I : FractionalIdeal (𝓞 K)⁰ K).num ∈ (Ideal (𝓞 K))⁰ := by
    rw [mem_nonZeroDivisors_iff_ne_zero, Ideal.zero_eq_bot,
      ← FractionalIdeal.coeIdeal_ne_zero (K := K), hJ]
    exact mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hn) I.ne_zero
  exact ⟨n, hn, ⟨_, hJ0⟩, Units.ext (by
    rw [FractionalIdeal.coe_mk0, Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, hJ])⟩

end NumberField
