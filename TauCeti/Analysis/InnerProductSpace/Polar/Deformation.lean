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
  rw [one_def, comp_id]

/-- The polar deformation is continuous in the parameter in operator norm when the modulus
is strictly positive. -/
theorem continuous_polarDeformation (T : E →L[ℝ] E) (hT : IsStrictlyPositive T.modulus) :
    Continuous T.polarDeformation := by
  have hp : Continuous (fun t : ℝ ↦ T.modulus ^ (1 - t)) := by
    simp_rw [CFC.rpow_eq_exp_smul_log _ _ hT]
    have hexp : Continuous (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) :=
      continuous_iff_continuousAt.mpr fun A ↦ (NormedSpace.exp_analytic (𝕂 := ℝ) A).continuousAt
    exact hexp.comp ((continuous_const.sub continuous_id).smul continuous_const)
  exact continuous_const.clm_comp hp

/-- For an injective operator, the norm along the deformation is the norm of the corresponding
power of its modulus. -/
theorem norm_polarDeformation_apply (T : E →L[ℝ] E) (hT : Function.Injective T)
    (t : ℝ) (x : E) :
    ‖T.polarDeformation t x‖ = ‖(T.modulus ^ (1 - t)) x‖ := by
  rw [polarDeformation_def, comp_apply]
  exact T.norm_polarFactor_apply_of_injective hT _

/-- Every operator along the polar deformation of an invertible operator is invertible. -/
@[simp]
theorem isUnit_polarDeformation (T : E →L[ℝ] E) (hT : IsUnit T) (t : ℝ) :
    IsUnit (T.polarDeformation t) := by
  have hP := (T.isStrictlyPositive_modulus_of_isUnit hT).isUnit
  rw [polarDeformation_def, ← mul_def]
  exact (T.isUnit_polarFactor hT).mul (hP.cfcRpow _ T.modulus_nonneg)

/-- The modulus along the polar deformation of an injective operator is the corresponding
power of its original modulus. -/
@[simp]
theorem modulus_polarDeformation (T : E →L[ℝ] E) (hT : Function.Injective T) (t : ℝ) :
    (T.polarDeformation t).modulus = T.modulus ^ (1 - t) := by
  have hpos : (T.modulus ^ (1 - t)).IsPositive :=
    nonneg_iff_isPositive.mp CFC.rpow_nonneg
  refine (eq_modulus_iff.mpr ⟨hpos, ?_⟩).symm
  have hgram := adjoint_comp_self_eq_adjoint_comp_self_iff.mpr
    (fun x ↦ (T.norm_polarDeformation_apply hT t x).symm)
  simpa only [hpos.isSelfAdjoint.adjoint_eq] using hgram

/-- The polar factor is unchanged along the polar deformation of an invertible operator. -/
@[simp]
theorem polarFactor_polarDeformation (T : E →L[ℝ] E) (hT : IsUnit T) (t : ℝ) :
    (T.polarDeformation t).polarFactor = T.polarFactor := by
  refine (eq_polarFactor ?_ ?_).symm
  · rw [T.modulus_polarDeformation (isUnit_iff_bijective.mp hT).injective,
      polarDeformation_def]
  · intro x hx
    have hx₀ : x = 0 := (isUnit_iff_bijective.mp (T.isUnit_polarDeformation hT t)).injective
      (by simpa using hx)
    simp [hx₀]

/-- An expanding operator deforms to its polar factor without shortening a vector
below its original norm or lengthening it beyond its original image. -/
theorem norm_le_norm_polarDeformation_apply_le (T : E →L[ℝ] E)
    (hexpand : ∀ x, ‖x‖ ≤ ‖T x‖) {t : ℝ} (ht : t ∈ Icc 0 1) (x : E) :
    ‖x‖ ≤ ‖T.polarDeformation t x‖ ∧ ‖T.polarDeformation t x‖ ≤ ‖T x‖ := by
  have hP := T.one_le_modulus_of_forall_norm_le hexpand
  have hpos := T.modulus_nonneg
  have hsp := T.isStrictlyPositive_modulus_of_forall_norm_le hexpand
  have hinj : Function.Injective T :=
    injective_of_forall_norm_le (M := 1) fun x ↦ by simpa using hexpand x
  rw [T.norm_polarDeformation_apply hinj]
  constructor
  · have hcancel : (T.modulus ^ (t - 1)) ((T.modulus ^ (1 - t)) x) = x := by
      rw [← mul_apply_eq_comp, ← neg_sub, CFC.rpow_neg_mul_rpow (1 - t) hsp,
        one_apply_eq_self]
    calc
      ‖x‖ = ‖(T.modulus ^ (t - 1)) ((T.modulus ^ (1 - t)) x)‖ := congrArg norm hcancel.symm
      _ ≤ ‖(T.modulus ^ (1 - t)) x‖ :=
        T.modulus.norm_rpow_apply_le_of_one_le_of_nonpos hP (sub_nonpos.mpr ht.2) _
  · have hfactor : (T.modulus ^ (1 - t)) x = (T.modulus ^ (-t)) (T.modulus x) := by
      have he : -t + 1 = 1 - t := by ring
      have hop := CFC.rpow_add hsp.isUnit (x := -t) (y := 1)
      rw [he, CFC.rpow_one _ hpos] at hop
      simpa only [mul_apply_eq_comp] using congrArg (fun A : E →L[ℝ] E ↦ A x) hop
    rw [hfactor, ← T.norm_modulus_apply x]
    exact T.modulus.norm_rpow_apply_le_of_one_le_of_nonpos hP (neg_nonpos.mpr ht.1) _

end ContinuousLinearMap
