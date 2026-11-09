/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Analysis.Normed.Ring.MaxSquare
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# A non-Tate norm on the topological Tate ring of p-adic numbers

The norm `N(x) = max (|x|_p) (|x|_p ^ 2)` has the usual complete uniformity,
is ultrametric and norm-one, but has no multiplicative pseudo-uniformiser.
In particular `N(p) N(p⁻¹) = p > 1`. These checks use explicit norm structures
so that the usual normed-field instance cannot silently supply the original norm.
-/

open TauCeti

variable (p : ℕ) [Fact p.Prime]

example : maxSquareRingNorm ℚ_[p] (p : ℚ_[p]) *
    maxSquareRingNorm ℚ_[p] (p : ℚ_[p])⁻¹ = (p : ℝ) := by
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [maxSquareRingNorm_mul_inv_of_norm_lt_one hp Padic.norm_p_lt_one,
    Padic.norm_p, inv_inv]

example : @norm ℚ_[p] (maxSquareNormedRing ℚ_[p]).toNorm (p : ℚ_[p]) = (p : ℝ)⁻¹ := by
  rw [norm_maxSquareNormedRing,
    maxSquareRingNorm_of_norm_le_one Padic.norm_p_lt_one.le, Padic.norm_p]

example : @CompleteSpace ℚ_[p] (maxSquareNormedRing ℚ_[p]).toMetricSpace.toUniformSpace :=
  completeSpace_maxSquareNormedRing

example : @IsUltrametricDist ℚ_[p] (maxSquareNormedRing ℚ_[p]).toDist :=
  isUltrametricDist_maxSquareNormedRing

example : @NormOneClass ℚ_[p] (maxSquareNormedRing ℚ_[p]).toNorm inferInstance :=
  normOneClass_maxSquareNormedRing

example : ¬ @NormedRing.IsTate ℚ_[p] (maxSquareNormedRing ℚ_[p]).toSeminormedRing :=
  not_isTate_maxSquareNormedRing

example : ∃ n : NormedRing ℚ_[p], n.toRing = (inferInstance : Ring ℚ_[p]) ∧
    n.toMetricSpace.toUniformSpace = (inferInstance : UniformSpace ℚ_[p]) ∧
    @IsUltrametricDist ℚ_[p] n.toDist ∧ @NormOneClass ℚ_[p] n.toNorm inferInstance ∧
    Huber.IsTateRing ℚ_[p] ∧ ¬ @NormedRing.IsTate ℚ_[p] n.toSeminormedRing :=
  exists_normedRing_isTateRing_not_isTate ℚ_[p]
