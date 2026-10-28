/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Basic

/-!
# The real numbers inside an archimedean completion

Let `w` be an infinite place of a field `K`. The completion `w.Completion` is a copy of `ℝ` when
`w` is real and of `ℂ` when `w` is complex, and in either case it contains a canonical copy of
`ℝ`: the real numbers are the elements sent into `ℝ ⊆ ℂ` by the extension embedding
`w.Completion → ℂ`. At a complex place this does not depend on the embedding chosen to represent
`w`, since the two conjugate embeddings agree on `ℝ`.

This file defines the resulting ring homomorphism `Completion.ofReal w : ℝ →+* w.Completion`. It
is characterized by `Completion.extensionEmbedding_ofReal`, it is an isometry onto its image, and
its normalized absolute value is `|r| ^ w.mult`. It supplies the positive real scalars at an
infinite place, for instance an idele at one infinite place with any prescribed idele norm: the
unit `completionNormSection w t = t ^ (1 / m_w)` has normalized absolute value `t`.

## Main definitions

* `NumberField.InfinitePlace.Completion.ofReal`: the embedding `ℝ →+* w.Completion`.
* `NumberField.InfinitePlace.completionNormSection`: the positive real number `t ^ (1 / m_w)`
  as a unit of the completion `K_w`, a continuous homomorphism `ℝ>0 →ₜ* K_wˣ`.

## Main results

* `NumberField.InfinitePlace.Completion.extensionEmbedding_ofReal`: the extension embedding sends
  `ofReal w r` to `r`; `NumberField.InfinitePlace.Completion.eq_ofReal_iff` says that this
  determines `ofReal w r`.
* `NumberField.InfinitePlace.Completion.norm_ofReal` and
  `NumberField.InfinitePlace.Completion.isometry_ofReal`: the embedding preserves absolute values.
* `NumberField.InfinitePlace.completionNormalizedAbsValue_ofReal`: the normalized absolute value
  of `ofReal w r` is `|r| ^ w.mult`.
* `NumberField.InfinitePlace.exists_completionNormalizedAbsValue_eq`: every nonnegative real
  number is a normalized absolute value.
* `NumberField.InfinitePlace.completionNormalizedAbsValue_completionNormSection`: the normalized
  absolute value of `completionNormSection w t` is `t`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §4.
-/

public section
noncomputable section

open scoped NNReal

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K] (w : InfinitePlace K)

namespace Completion

open scoped Classical in
/-- The real numbers inside the completion at an infinite place `w`: the inverse of
`w.Completion ≃+* ℝ` at a real place, and the inverse of `w.Completion ≃+* ℂ` restricted to `ℝ`
at a complex place. It is characterized by `extensionEmbedding_ofReal`. -/
def ofReal : ℝ →+* w.Completion :=
  if hw : w.IsReal then (ringEquivRealOfIsReal hw).symm.toRingHom
  else (ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm.toRingHom.comp
    Complex.ofRealHom

/-- **Characterization of `ofReal`**: the extension embedding `w.Completion → ℂ` sends
`ofReal w r` to the real number `r`. -/
@[simp]
theorem extensionEmbedding_ofReal (r : ℝ) : extensionEmbedding w (ofReal w r) = r := by
  rw [ofReal]
  split_ifs with hw
  · rw [← extensionEmbeddingOfIsReal_apply hw, ← ringEquivRealOfIsReal_apply hw]
    simp
  · rw [← ringEquivComplexOfIsComplex_apply (not_isReal_iff_isComplex.mp hw)]
    simp

/-- An element of the completion is `ofReal w r` exactly when the extension embedding sends it to
`r`. -/
theorem eq_ofReal_iff {x : w.Completion} {r : ℝ} :
    x = ofReal w r ↔ extensionEmbedding w x = r := by
  rw [← extensionEmbedding_ofReal w r]
  exact (extensionEmbedding w).injective.eq_iff.symm

/-- At a real place, the real extension embedding sends `ofReal w r` to `r`. -/
@[simp]
theorem extensionEmbeddingOfIsReal_ofReal {w : InfinitePlace K} (hw : w.IsReal) (r : ℝ) :
    extensionEmbeddingOfIsReal hw (ofReal w r) = r :=
  Complex.ofReal_injective <| by
    rw [extensionEmbeddingOfIsReal_apply, extensionEmbedding_ofReal]

/-- The embedding of `ℝ` into an archimedean completion preserves absolute values. -/
@[simp]
theorem norm_ofReal (r : ℝ) : ‖ofReal w r‖ = |r| := by
  rw [← (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _),
    extensionEmbedding_ofReal, Complex.norm_real, Real.norm_eq_abs]

/-- The embedding of `ℝ` into an archimedean completion is an isometry. -/
theorem isometry_ofReal : Isometry (ofReal w) :=
  AddMonoidHomClass.isometry_of_norm (ofReal w) fun r ↦ by rw [norm_ofReal, Real.norm_eq_abs]

/-- The embedding of `ℝ` into an archimedean completion is continuous. -/
@[continuity, fun_prop]
theorem continuous_ofReal : Continuous (ofReal w) :=
  (isometry_ofReal w).continuous

end Completion

/-- The normalized absolute value of a real number in the completion at `w` is its absolute
value raised to the multiplicity of `w`. -/
theorem completionNormalizedAbsValue_ofReal (r : ℝ) :
    completionNormalizedAbsValue w (Completion.ofReal w r) = |r| ^ w.mult := by
  rw [completionNormalizedAbsValue_apply, Completion.norm_ofReal]

/-- Every nonnegative real number is the normalized absolute value of an element of the completion
at an infinite place, namely of the real number `t ^ (1 / m_w)`. -/
theorem exists_completionNormalizedAbsValue_eq {t : ℝ} (ht : 0 ≤ t) :
    ∃ x : w.Completion, completionNormalizedAbsValue w x = t :=
  ⟨Completion.ofReal w (t ^ (w.mult : ℝ)⁻¹), by
    rw [completionNormalizedAbsValue_ofReal, abs_of_nonneg (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul ht, inv_mul_cancel₀ (by exact_mod_cast w.mult_ne_zero), Real.rpow_one]⟩

/-! ### The positive real units of norm `t` -/

/-- The positive real number `t ^ (1 / m_w)` as a unit of the completion at the infinite place
`w`, where `m_w` is the multiplicity of `w`. Its normalized absolute value is `t`
(`completionNormalizedAbsValue_completionNormSection`). -/
def completionNormSection : ℝ≥0ˣ →ₜ* w.Completionˣ where
  toMonoidHom := Units.map <|
    ((Completion.ofReal w).toMonoidHom.comp NNReal.toRealHom.toMonoidHom).comp
      (NNReal.rpowMonoidHom (w.mult : ℝ)⁻¹)
  continuous_toFun := Continuous.units_map _ <|
    (Completion.continuous_ofReal w).comp <| NNReal.continuous_coe.comp <|
      NNReal.continuous_rpow_const (by positivity)

/-- The underlying element of `completionNormSection w t` is the real number `t ^ (1 / m_w)`. -/
@[simp]
theorem coe_completionNormSection (t : ℝ≥0ˣ) :
    (completionNormSection w t : w.Completion) =
      Completion.ofReal w ((t : ℝ≥0) ^ (w.mult : ℝ)⁻¹ : ℝ≥0) :=
  (rfl)

/-- The normalized absolute value of `completionNormSection w t` is `t`. -/
theorem completionNormalizedAbsValue_completionNormSection (t : ℝ≥0ˣ) :
    completionNormalizedAbsValue w (completionNormSection w t) = (t : ℝ≥0) := by
  rw [coe_completionNormSection, completionNormalizedAbsValue_ofReal, NNReal.abs_eq,
    ← NNReal.coe_pow, NNReal.rpow_inv_natCast_pow _ w.mult_ne_zero]

end NumberField.InfinitePlace
