/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
public import Mathlib.NumberTheory.NumberField.FractionalIdeal
public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# Fractional ideals of a number field: index and denominator clearing

An invertible fractional ideal of a number field `K` is a full `ℤ`-lattice in `K`.  If `J ≤ I` are
two such ideals, the index of `J` in `I` is the ratio of their absolute norms.  The index is
computed from the determinant formula `NumberField.det_basisOfFractionalIdeal_eq_absNorm` and
`AddSubgroup.relIndex_eq_abs_det`.

Every invertible fractional ideal `I` can be scaled by a nonzero natural number `m` into a nonzero
integral ideal `J` with `J = (m) * I`.

## Main results

* `NumberField.relIndex_fractionalIdeal_eq_absNorm_div_absNorm`: the index of `J` in `I`, as
  additive subgroups of `K`, is `absNorm J / absNorm I`.
* `NumberField.exists_mk0_eq_toPrincipalIdeal_natCast_mul`: for any invertible fractional ideal `I`,
  there exist a nonzero `m : ℕ` and a nonzero integral ideal `J` with `J = (m) * I`.
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

/-- For every invertible fractional ideal `I`, there exist a nonzero `m : ℕ` and a nonzero integral
ideal `J` such that `J = (m) * I`. -/
theorem exists_mk0_eq_toPrincipalIdeal_natCast_mul (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    ∃ (m : ℕ) (hm : m ≠ 0) (J : (Ideal (𝓞 K))⁰),
      FractionalIdeal.mk0 K J =
        toPrincipalIdeal (𝓞 K) K (Units.mk0 (m : K) (Nat.cast_ne_zero.mpr hm)) * I := by
  set d : (𝓞 K)⁰ := (I : FractionalIdeal (𝓞 K)⁰ K).den
  set m : ℕ := Ideal.absNorm (Ideal.span {(d : 𝓞 K)})
  have hm : m ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.coe_ne_zero d
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {(d : 𝓞 K)}))
  have hmK : (m : K) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hm_eq : (m : K) = algebraMap (𝓞 K) K q * algebraMap (𝓞 K) K (d : 𝓞 K) := by
    rw [← map_mul, mul_comm, ← hq, map_natCast]
  have hmul : FractionalIdeal.spanSingleton (𝓞 K)⁰ (m : K) * (I : FractionalIdeal (𝓞 K)⁰ K) =
      ((Ideal.span {q} * (I : FractionalIdeal (𝓞 K)⁰ K).num : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) := by
    rw [hm_eq, map_mul (FractionalIdeal.spanSingleton (𝓞 K)⁰), mul_assoc,
      FractionalIdeal.den_mul_self_eq_num', ← FractionalIdeal.coeIdeal_span_singleton,
      ← FractionalIdeal.coeIdeal_mul]
  have hJ0 : Ideal.span {q} * (I : FractionalIdeal (𝓞 K)⁰ K).num ≠ 0 := fun h0 ↦
    mul_ne_zero (FractionalIdeal.spanSingleton_eq_zero_iff.not.mpr hmK) I.ne_zero
      (by simp [hmul, h0])
  refine ⟨m, hm, ⟨Ideal.span {q} * (I : FractionalIdeal (𝓞 K)⁰ K).num,
    mem_nonZeroDivisors_of_ne_zero hJ0⟩, Units.ext ?_⟩
  rw [FractionalIdeal.coe_mk0, Units.val_mul, coe_toPrincipalIdeal, Units.val_mk0, hmul]

end NumberField
