/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Bounded
public import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog

/-!
# Norm-controlled polar deformation

An invertible operator `T = U P` on a real Hilbert space deforms to its canonical polar
isometry by `U P^(1-t)`. If `T` expands every vector, the deformation continues to expand
vectors and never increases their norms beyond their original images under `T`.
Consequently negative discs can be deformed to orthogonal discs without leaving a prescribed
coordinate ball or raising the negative quadratic value above its boundary value.

The construction uses `ContinuousLinearMap.polarFactor` and the positive modulus, together
with real powers from the continuous functional calculus. It does not require a choice of
eigenbasis or finite dimensionality.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, Sections 2–3.
-/

public section

open Set

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The polar deformation `U P^(1-t)`, where `T = U P` is the canonical polar decomposition.
It is defined for every real parameter; its norm control holds on the unit interval. -/
noncomputable def polarDeformation (T : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E :=
  T.polarFactor ∘L T.modulus ^ (1 - t)

/-- The defining operator formula for the polar deformation. -/
theorem polarDeformation_def (T : E →L[ℝ] E) (t : ℝ) :
    T.polarDeformation t = T.polarFactor ∘L T.modulus ^ (1 - t) := (rfl)

/-- The pointwise formula for the polar deformation. -/
theorem polarDeformation_apply (T : E →L[ℝ] E) (t : ℝ) (x : E) :
    T.polarDeformation t x = T.polarFactor ((T.modulus ^ (1 - t)) x) :=
  congrArg (fun A : E →L[ℝ] E ↦ A x) (T.polarDeformation_def t)

/-- The polar deformation starts at the original operator. -/
@[simp]
theorem polarDeformation_zero (T : E →L[ℝ] E) : T.polarDeformation 0 = T := by
  simp only [polarDeformation_def, sub_zero, CFC.rpow_one _ T.modulus_nonneg,
    polarFactor_comp_modulus]

/-- The polar deformation ends at the canonical polar factor. -/
@[simp]
theorem polarDeformation_one (T : E →L[ℝ] E) : T.polarDeformation 1 = T.polarFactor := by
  rw [polarDeformation_def, sub_self, CFC.rpow_zero _ T.modulus_nonneg]
  exact mul_one T.polarFactor

/-- The polar deformation is continuous in the parameter in operator norm. -/
theorem continuous_polarDeformation (T : E →L[ℝ] E) (hT : IsUnit T) :
    Continuous T.polarDeformation := by
  have hp : Continuous (fun t : ℝ ↦ T.modulus ^ (1 - t)) := by
    simp_rw [CFC.rpow_eq_exp_smul_log _ _ (T.isStrictlyPositive_modulus hT)]
    have hexp : Continuous (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) :=
      continuous_iff_continuousAt.mpr fun A ↦ (NormedSpace.exp_analytic (𝕂 := ℝ) A).continuousAt
    exact hexp.comp ((continuous_const.sub continuous_id).smul continuous_const)
  exact continuous_const.clm_comp hp

/-- For an invertible operator, the norm along the deformation is the norm of the corresponding
power of its modulus. -/
theorem norm_polarDeformation_apply (T : E →L[ℝ] E) (hT : IsUnit T) (t : ℝ) (x : E) :
    ‖T.polarDeformation t x‖ = ‖(T.modulus ^ (1 - t)) x‖ := by
  rw [polarDeformation_def, comp_apply]
  exact T.norm_polarFactor_apply_of_injective (isUnit_iff_bijective.mp hT).injective _

/-- An expanding invertible operator deforms to its polar factor without shortening a vector
below its original norm or lengthening it beyond its original image. -/
theorem norm_le_norm_polarDeformation_apply_le (T : E →L[ℝ] E) (hT : IsUnit T)
    (hexpand : ∀ x, ‖x‖ ≤ ‖T x‖) {t : ℝ} (ht : t ∈ Icc 0 1) (x : E) :
    ‖x‖ ≤ ‖T.polarDeformation t x‖ ∧ ‖T.polarDeformation t x‖ ≤ ‖T x‖ := by
  have hP := T.one_le_modulus_of_forall_norm_le hexpand
  have hunit := (T.isStrictlyPositive_modulus hT).isUnit
  have hpos := T.modulus_nonneg
  rw [T.norm_polarDeformation_apply hT]
  constructor
  · have hcancel : (T.modulus ^ (t - 1)) ((T.modulus ^ (1 - t)) x) = x := by
      have he : (t - 1) + (1 - t) = 0 := by ring
      have hop := CFC.rpow_add hunit (x := t - 1) (y := 1 - t)
      rw [he, CFC.rpow_zero _ hpos] at hop
      exact congrArg (fun A : E →L[ℝ] E ↦ A x) hop.symm
    calc
      ‖x‖ = ‖(T.modulus ^ (t - 1)) ((T.modulus ^ (1 - t)) x)‖ := congrArg norm hcancel.symm
      _ ≤ ‖(T.modulus ^ (1 - t)) x‖ := by
        simpa only [one_mul] using (T.modulus ^ (t - 1)).le_of_opNorm_le
          (T.modulus.norm_rpow_le_one_of_one_le hP (sub_nonpos.mpr ht.2)) ((T.modulus ^ (1 - t)) x)
  · have hfactor : (T.modulus ^ (1 - t)) x = (T.modulus ^ (-t)) (T.modulus x) := by
      have he : -t + 1 = 1 - t := by ring
      have hop := CFC.rpow_add hunit (x := -t) (y := 1)
      rw [he, CFC.rpow_one _ hpos] at hop
      exact congrArg (fun A : E →L[ℝ] E ↦ A x) hop
    rw [hfactor, ← T.norm_modulus_apply x]
    simpa only [one_mul] using (T.modulus ^ (-t)).le_of_opNorm_le
      (T.modulus.norm_rpow_le_one_of_one_le hP (neg_nonpos.mpr ht.1)) (T.modulus x)

end ContinuousLinearMap
