/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Units
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import TauCeti.GroupTheory.GroupAction.MaximalInvariant

/-!
# The scale group and its maximal invariant

The positive scalars act on pairs `(x, s)` with `s > 0` by `(x, s) ↦ (c x, c s)`; the ratio
`x / s` is a maximal invariant of this action (Ferguson, *Mathematical Statistics: A Decision
Theoretic Approach*, §5.6, Example 2). So a test on the half plane is invariant under scaling
exactly when it is a function of `x / s` (`MulAction.IsMaximalInvariant.factorsThrough_iff`).

## Main definitions

* `SubMulAction.posHalfPlane K`: the pairs `(x, s)` with `s > 0`, as a set stable under the
  diagonal scaling by the positive units of an ordered semiring `K`.

## Main results

* `SubMulAction.isMaximalInvariant_posHalfPlane_div`: `x / s` is a maximal invariant of the scale
  group acting on pairs `(x, s)` with `s > 0`.

The result is adapted from `CKSD.mean_scale_ratio_eq_iff` in lean-CKSD's
`CKSD/Inference/InvariantTesting.lean`.

## References

* T. S. Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*, Academic Press, 1967,
  §5.6, pp. 244–246.
-/

public section

namespace SubMulAction

section Semiring

variable (K : Type*) [Semiring K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The pairs `(x, s)` with `s > 0`, stable under the diagonal action `(x, s) ↦ (c x, c s)` of the
positive units `c` of `K`. -/
def posHalfPlane : SubMulAction (Units.posSubgroup K) (K × K) where
  carrier := {p | 0 < p.2}
  smul_mem' c _ hp := mul_pos c.prop hp

variable {K}

/-- A pair lies in `SubMulAction.posHalfPlane K` if and only if its second coordinate is
positive. -/
@[simp]
theorem mem_posHalfPlane {p : K × K} : p ∈ posHalfPlane K ↔ 0 < p.2 :=
  Iff.rfl

end Semiring

variable {K : Type*} [Semifield K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The ratio `x / s` is a maximal invariant of the scale group of positive units acting on the
pairs `(x, s)` with `s > 0`. -/
theorem isMaximalInvariant_posHalfPlane_div :
    MulAction.IsMaximalInvariant (Units.posSubgroup K)
      (fun p : posHalfPlane K ↦ (p : K × K).1 / (p : K × K).2) where
  -- `c • (x, s)` unfolds definitionally to `(c * x, c * s)`.
  apply_smul c _ := mul_div_mul_left _ _ (Units.ne_zero (c : Kˣ))
  exists_smul_eq := by
    -- Membership in `posHalfPlane K` is `0 < s` by definition (`mem_posHalfPlane`).
    rintro ⟨⟨x, s⟩, hs : 0 < s⟩ ⟨⟨y, t⟩, ht : 0 < t⟩ (h : x / s = y / t)
    have hc : Units.mk0 (t / s) (div_pos ht hs).ne' ∈ Units.posSubgroup K :=
      (Units.mem_posSubgroup _).2 (div_pos ht hs)
    refine ⟨⟨_, hc⟩, ?_⟩
    ext <;> simp only [SubMulAction.val_smul, Prod.smul_fst, Prod.smul_snd, Subgroup.mk_smul,
      Units.smul_mk0, smul_eq_mul]
    · rw [div_mul_comm, h, div_mul_cancel₀ y ht.ne']
    · exact div_mul_cancel₀ t hs.ne'

end SubMulAction
