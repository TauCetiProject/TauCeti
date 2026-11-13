/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic

import TauCeti.NumberTheory.NumberField.CanonicalEmbedding.PoissonSummation

/-!
# Identification of the Euclidean Minkowski space of `ℚ` with `ℝ`

The field `ℚ` has a unique infinite place `Rat.infinitePlace`, which is real, and no complex places.
Evaluating at `Rat.infinitePlace` identifies `NumberField.mixedEmbedding.euclidean.mixedSpace ℚ`
isometrically with `ℝ` (`TauCeti.NumberField.mixedEmbedding.euclidean.mixedSpaceRatEquivReal`),
sending the canonical embedding of `q : ℚ` to `(q : ℝ)` and identifying
`NumberField.mixedEmbedding.euclidean.integerLattice ℚ` with `ℤ`.

## Main definitions and results

* `TauCeti.NumberField.mixedEmbedding.euclidean.mixedSpaceRatEquivReal`: the canonical linear
  isometry `NumberField.mixedEmbedding.euclidean.mixedSpace ℚ ≃ₗᵢ[ℝ] ℝ`, with evaluation lemmas
  `mixedSpaceRatEquivReal_apply` and `mixedSpaceRatEquivReal_symm_apply`.
* `TauCeti.NumberField.mixedEmbedding.euclidean.mixedSpaceRatEquivReal_toMixed_symm_mixedEmbedding`:
  `mixedSpaceRatEquivReal` sends `(toMixed ℚ).symm (mixedEmbedding ℚ q)` to `(q : ℝ)`.
* `TauCeti.NumberField.mixedEmbedding.euclidean.mem_integerLattice_rat_iff`: a point of
  `euclidean.mixedSpace ℚ` belongs to `euclidean.integerLattice ℚ` iff its image under
  `mixedSpaceRatEquivReal` is an integer.
-/

public section

noncomputable section

open NumberField NumberField.mixedEmbedding
open scoped RealInnerProductSpace

namespace TauCeti.NumberField.mixedEmbedding.euclidean

/-- The linear equivalence `mixedSpace ℚ ≃ₗ[ℝ] ℝ` given by evaluation at `Rat.infinitePlace`. -/
private def mixedRatEquivReal : mixedSpace ℚ ≃ₗ[ℝ] ℝ where
  toFun x := x.1 ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun r := (fun _ ↦ r, isEmptyElim)
  left_inv x := by
    ext w
    · exact congrArg x.1 (Subtype.ext (Subsingleton.elim Rat.infinitePlace w.1))
    · exact isEmptyElim w
  right_inv _ := rfl

open Classical in
/-- The canonical linear isometry identifying `euclidean.mixedSpace ℚ` with `ℝ` via the unique
infinite place of `ℚ`. -/
def mixedSpaceRatEquivReal : NumberField.mixedEmbedding.euclidean.mixedSpace ℚ ≃ₗᵢ[ℝ] ℝ :=
  { (NumberField.mixedEmbedding.euclidean.toMixed ℚ).toLinearEquiv.trans mixedRatEquivReal with
    norm_map' x := by
      let _ : Unique {w : InfinitePlace ℚ // w.IsReal} :=
        { default := ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
          uniq w := Subtype.ext (Subsingleton.elim w.1 Rat.infinitePlace) }
      have hinner : ⟪x, x⟫ =
          ((NumberField.mixedEmbedding.euclidean.toMixed ℚ x).1
            ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩) ^ 2 := by
        rw [← TauCeti.NumberField.mixedEmbedding.mixedInner_toMixed,
          TauCeti.NumberField.mixedEmbedding.mixedInner_def, Fintype.sum_unique, Fintype.sum_empty,
          add_zero, Unique.eq_default (⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩ :
            {w : InfinitePlace ℚ // w.IsReal}), sq]
      rw [norm_eq_sqrt_real_inner x, hinner, Real.sqrt_sq_eq_abs, ← Real.norm_eq_abs]
      simp [mixedRatEquivReal] }

open Classical in
/-- `mixedSpaceRatEquivReal` evaluates the real coordinate at `Rat.infinitePlace`. -/
@[simp]
theorem mixedSpaceRatEquivReal_apply (x : NumberField.mixedEmbedding.euclidean.mixedSpace ℚ) :
    mixedSpaceRatEquivReal x =
      (NumberField.mixedEmbedding.euclidean.toMixed ℚ x).1
        ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩ := by
  simp [mixedSpaceRatEquivReal, mixedRatEquivReal]

open Classical in
/-- The inverse of `mixedSpaceRatEquivReal` embeds `r : ℝ` with mixed-space coordinates
`(fun _ ↦ r, isEmptyElim)`. -/
@[simp]
theorem mixedSpaceRatEquivReal_symm_apply (r : ℝ) :
    mixedSpaceRatEquivReal.symm r =
      (NumberField.mixedEmbedding.euclidean.toMixed ℚ).symm (fun _ ↦ r, isEmptyElim) :=
  mixedSpaceRatEquivReal.injective (by simp)

open Classical in
/-- `mixedSpaceRatEquivReal` sends the canonical embedding of `q : ℚ` to `(q : ℝ)`. -/
theorem mixedSpaceRatEquivReal_toMixed_symm_mixedEmbedding (q : ℚ) :
    mixedSpaceRatEquivReal
        ((NumberField.mixedEmbedding.euclidean.toMixed ℚ).symm (mixedEmbedding ℚ q)) = (q : ℝ) := by
  simp

open Classical in
/-- A point of `euclidean.mixedSpace ℚ` lies in `euclidean.integerLattice ℚ` if and only if its
image in `ℝ` under `mixedSpaceRatEquivReal` is an integer. -/
theorem mem_integerLattice_rat_iff (x : NumberField.mixedEmbedding.euclidean.mixedSpace ℚ) :
    x ∈ NumberField.mixedEmbedding.euclidean.integerLattice ℚ ↔
      ∃ z : ℤ, mixedSpaceRatEquivReal x = z := by
  let e := NumberField.mixedEmbedding.euclidean.toMixed ℚ
  have hmem : x ∈ NumberField.mixedEmbedding.euclidean.integerLattice ℚ ↔
      ∃ a : 𝓞 ℚ, mixedEmbedding ℚ a = e x := by
    simp [e, NumberField.mixedEmbedding.euclidean.integerLattice, ZLattice.comap]
  rw [hmem]
  refine ⟨fun ⟨a, ha⟩ ↦ ⟨Rat.ringOfIntegersEquiv a, ?_⟩,
    fun ⟨z, hz⟩ ↦ ⟨Rat.ringOfIntegersEquiv.symm z, ?_⟩⟩
  · have hx : x = e.symm (mixedEmbedding ℚ a) := e.injective (by simpa [e] using ha.symm)
    rw [hx, mixedSpaceRatEquivReal_toMixed_symm_mixedEmbedding, RingOfIntegers.coe_eq_algebraMap,
      ← Rat.ringOfIntegersEquiv_apply_coe, Rat.cast_intCast]
  · have hx : x = e.symm (mixedEmbedding ℚ (z : ℚ)) := mixedSpaceRatEquivReal.injective
      (by rw [hz, mixedSpaceRatEquivReal_toMixed_symm_mixedEmbedding, Rat.cast_intCast])
    rw [hx, ContinuousLinearEquiv.apply_symm_apply, Rat.ringOfIntegersEquiv_symm_apply_coe]

end TauCeti.NumberField.mixedEmbedding.euclidean

end
