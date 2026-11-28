/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.ActionAngle.RegularValue

/-!
# The flat kinetic energy on `T*Tⁿ`

Let `p > 0`, let `Tⁿ = ι → AddCircle p` be the torus and `I = (I_j)` the actions of its cotangent
bundle `T*Tⁿ` (`TauCeti.CotangentBundle.torusActions`). The kinetic energy `K = ½ ∑ⱼ I_j²` of the
flat metric `∑ⱼ dθ_j²` (`TauCeti.CotangentBundle.torusKineticEnergy`) is a function of the actions,
and its level `K = 1/2` is the unit cosphere bundle of the flat torus.

## Main results

In the namespace `TauCeti.CotangentBundle`:

* `contMDiff_torusKineticEnergy`: the flat kinetic energy is smooth.
* `torusKineticEnergy_zeroSection`: it vanishes on the zero section.
* `isCompact_preimage_Iic_torusKineticEnergy`: its sublevel sets are compact.
* `isRegularValue_torusKineticEnergy`: every nonzero value is regular.
-/

public section

noncomputable section

open Bundle Function Set
open scoped Manifold ContDiff

namespace TauCeti

namespace CotangentBundle

variable (p : ℝ) [Fact (0 < p)] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The **flat kinetic energy** `K = ½ ∑ⱼ I_j²` on the cotangent bundle of the torus: the kinetic
energy of the flat metric `∑ⱼ dθ_j²`, a function of the actions `I`. Its level `K = 1/2` is the unit
cosphere bundle of the flat torus. -/
def torusKineticEnergy :
    CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p) → ℝ :=
  (fun a : ι → ℝ ↦ (∑ j, a j ^ 2) / 2) ∘ torusActions p

/-- The flat kinetic energy of a covector is half the sum of the squares of its actions. -/
@[simp]
theorem torusKineticEnergy_apply
    (z : CotangentBundle (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (ι → AddCircle p)) :
    torusKineticEnergy p z = (∑ j, torusActions p z j ^ 2) / 2 :=
  (rfl)

/-- The flat kinetic energy is the function `a ↦ ½ ∑ⱼ a_j²` of the actions. -/
theorem torusKineticEnergy_eq_comp :
    torusKineticEnergy (ι := ι) p = (fun a : ι → ℝ ↦ (∑ j, a j ^ 2) / 2) ∘ torusActions p :=
  (rfl)

omit [DecidableEq ι] in
/-- The profile `a ↦ ½ ∑ⱼ a_j²` of the flat kinetic energy is smooth. -/
private theorem contDiff_halfSumSq : ContDiff ℝ ω (fun a : ι → ℝ ↦ (∑ j, a j ^ 2) / 2) :=
  by fun_prop

/-- The flat kinetic energy is smooth. -/
theorem contMDiff_torusKineticEnergy :
    ContMDiff ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) 𝓘(ℝ) ∞
      (torusKineticEnergy (ι := ι) p) :=
  (contDiff_halfSumSq.of_le le_top).contMDiff.comp (contMDiff_torusActions p)

/-- The flat kinetic energy vanishes on the zero section. -/
theorem torusKineticEnergy_zeroSection (x : ι → AddCircle p) :
    torusKineticEnergy p (zeroSection ((ι → ℝ) →L[ℝ] ℝ) (fun x : ι → AddCircle p ↦
      TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x →L[ℝ] ℝ) x) = 0 := by
  refine div_eq_zero_iff.2 (Or.inl (Finset.sum_eq_zero fun j _ ↦ ?_))
  rw [torusActions_apply, zeroSection_snd]
  -- The tangent space of the torus is the model space `ι → ℝ`, where the zero form is `0`.
  change (0 : (ι → ℝ) →L[ℝ] ℝ) (Pi.single j 1) ^ 2 = 0
  rw [zero_apply, sq, mul_zero]

/-- **The sublevel sets of the flat kinetic energy are compact.** The actions of a covector with
`K ≤ b` are bounded, and the action map is proper. -/
theorem isCompact_preimage_Iic_torusKineticEnergy (b : ℝ) :
    IsCompact (torusKineticEnergy (ι := ι) p ⁻¹' Iic b) := by
  rw [torusKineticEnergy_eq_comp, preimage_comp]
  refine (isProperMap_torusActions p).isCompact_preimage
    (Metric.isCompact_of_isClosed_isBounded
      (isClosed_Iic.preimage contDiff_halfSumSq.continuous) ?_)
  -- Each action satisfies `|a_j| ≤ a_j² + 1 ≤ 2b + 1`.
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨2 * b + 1, fun a ha ↦ ?_⟩
  have hb : ∑ j, a j ^ 2 ≤ 2 * b := by
    have : (∑ j, a j ^ 2) / 2 ≤ b := ha
    linarith
  have hsum (i : ι) : a i ^ 2 ≤ ∑ j, a j ^ 2 :=
    Finset.single_le_sum (f := fun j ↦ a j ^ 2) (fun j _ ↦ sq_nonneg (a j)) (Finset.mem_univ i)
  have hb0 : 0 ≤ 2 * b := le_trans (Finset.sum_nonneg fun j _ ↦ sq_nonneg (a j)) hb
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (by linarith)]
  intro i
  rw [Real.norm_eq_abs]
  nlinarith [abs_nonneg (a i), sq_abs (a i), hsum i]

/-- **Every nonzero value of the flat kinetic energy is regular.** At a covector with `K = c ≠ 0`
the actions `a` do not vanish, and the derivative `v ↦ ∑ⱼ a_j v_j` of `½ ∑ⱼ a_j²` takes the value
`∑ⱼ a_j² = 2c` on `a` itself. -/
theorem isRegularValue_torusKineticEnergy {c : ℝ} (hc : c ≠ 0) :
    IsRegularValue ((ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)).prod 𝓘(ℝ, (ι → ℝ) →L[ℝ] ℝ)) 𝓘(ℝ)
      (torusKineticEnergy (ι := ι) p) c := by
  rw [torusKineticEnergy_eq_comp, isRegularValue_comp_torusActions_iff p]
  intro a ha
  have hd : HasFDerivAt (fun a : ι → ℝ ↦ (∑ j, a j ^ 2) / 2)
      (∑ j, a j • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) j) a := by
    have hsum : HasFDerivAt (fun a : ι → ℝ ↦ ∑ j, a j ^ 2)
        (∑ j, (2 • a j ^ (2 - 1)) • ContinuousLinearMap.proj (R := ℝ) j) a :=
      HasFDerivAt.fun_sum fun j _ ↦ (hasFDerivAt_apply j a).pow 2
    simp only [div_eq_mul_inv]
    refine (hsum.mul_const (2 : ℝ)⁻¹).congr_fderiv ?_
    ext v
    simp [Finset.mul_sum, mul_assoc]
  rw [hd.fderiv]
  refine ContinuousLinearMap.surjective_iff_ne_zero.2 fun h0 ↦ hc ?_
  -- Evaluating the derivative at `a` gives `∑ⱼ a_j² = 2c`.
  have h2 : ∑ j, a j ^ 2 = 0 := by simpa [sq] using DFunLike.congr_fun h0 a
  rw [← ha, h2, zero_div]

end CotangentBundle

end TauCeti
