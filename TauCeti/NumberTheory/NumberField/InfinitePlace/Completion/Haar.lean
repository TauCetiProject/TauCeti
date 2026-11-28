/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Basic
public import TauCeti.MeasureTheory.Measure.Haar.DistribChar.FiniteProduct
import TauCeti.MeasureTheory.Measure.Haar.DistribChar

/-!
# Haar scaling at infinite places

Multiplication by a nonzero element of an archimedean completion scales additive Haar measure
by its normalized absolute value: the norm at a real place, and its square at a complex place.
This is the archimedean factor of the idele module.
-/

public noncomputable section

open MeasureTheory

namespace NumberField.InfinitePlace

variable {K : Type*} [Field K]

/-- At an infinite place, the Haar character is the norm raised to the multiplicity of the
place. -/
@[simp]
theorem distribHaarChar_completion (w : InfinitePlace K) (a : w.Completionˣ) :
    distribHaarChar w.Completion a = ‖(a : w.Completion)‖₊ ^ w.mult := by
  rcases w.isReal_or_isComplex with hw | hw
  · let e : w.Completion ≃ₜ+ ℝ :=
      { (Completion.ringEquivRealOfIsReal hw).toAddEquiv,
        (Completion.isometryEquivRealOfIsReal hw).toHomeomorph with }
    let b : ℝˣ := Units.map (Completion.ringEquivRealOfIsReal hw).toMonoidHom a
    have he (x : w.Completion) : e (a • x) = b • e x :=
      (Completion.ringEquivRealOfIsReal hw).map_mul a x
    rw [e.distribHaarChar_eq a b he, distribHaarChar_real_eq, hw.mult_eq_one]
    simp only [Module.finrank_self, pow_one]
    apply NNReal.eq
    exact (Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) a
  · let e : w.Completion ≃ₜ+ ℂ :=
      { (Completion.ringEquivComplexOfIsComplex hw).toAddEquiv,
        (Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph with }
    let b : ℂˣ := Units.map (Completion.ringEquivComplexOfIsComplex hw).toMonoidHom a
    have he (x : w.Completion) : e (a • x) = b • e x :=
      (Completion.ringEquivComplexOfIsComplex hw).map_mul a x
    rw [e.distribHaarChar_eq a b he, distribHaarChar_complex_eq, hw.mult_eq_two,
      Complex.finrank_real_complex]
    congr 1
    apply NNReal.eq
    exact (Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) a

end NumberField.InfinitePlace
