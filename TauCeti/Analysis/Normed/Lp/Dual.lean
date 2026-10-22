/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpHolder
import Mathlib.Analysis.Normed.Operator.Mul

/-!
# The continuous dual of ℓ¹

Over real or complex scalars, the pairing `∑' i, a i * x i` identifies bounded families with
continuous linear functionals on ℓ¹, isometrically. The inverse records their coordinate values.
The index type is arbitrary, including empty and uncountable types; no enumeration is chosen.

`lp.dualOneEquiv` uses Mathlib's `lp.dualPairing` for the pairing and `lp.hasSum_single` for
the coordinate expansion. The pairing is bilinear, including over complex scalars: the
coefficients of a functional are its values on coordinate vectors, without conjugation.

This identification describes the dual of the summable sequence space and makes its norm
and the action of its functionals accessible through coordinates.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
-/

public section

noncomputable section

open scoped ENNReal

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [DecidableEq ι]

/-- Every continuous linear functional on ℓ¹ is given by its coordinate series. -/
theorem hasSum_lp_single_mul (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1))
    (x : lp (fun _ : ι ↦ 𝕜) 1) :
    HasSum (fun i ↦ f (lp.single 1 i 1) * x i) (f x) := by
  convert (lp.hasSum_single (by simp) x).map f f.continuous using 1
  ext i
  simp only [Function.comp_apply]
  simpa [← lp.single_smul, mul_comm] using
    (f.map_smul (x i) (lp.single 1 i 1)).symm

end ContinuousLinearMap

namespace lp

variable {𝕜 ι : Type*} [RCLike 𝕜]

variable (𝕜 ι)

/-- The isometric duality between bounded scalar families and the continuous dual of ℓ¹.
It sends `a` to the functional `x ↦ ∑' i, a i * x i`. -/
def dualOneEquiv : lp (fun _ : ι ↦ 𝕜) ∞ ≃ₗᵢ[𝕜] StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1) := by
  classical
  have hmul : ‖ContinuousLinearMap.mul 𝕜 𝕜‖ ≤ ((1 : NNReal) : ℝ) := by
    simpa only [NNReal.coe_one] using ContinuousLinearMap.opNorm_mul_le 𝕜 𝕜
  let P : lp (fun _ : ι ↦ 𝕜) ∞ →L[𝕜] StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1) :=
    dualPairing (𝕜 := 𝕜) ∞ 1 (fun _ : ι ↦ ContinuousLinearMap.mul 𝕜 𝕜)
      (fun _ ↦ hmul)
  have hP (a : lp (fun _ : ι ↦ 𝕜) ∞) (i : ι) (z : 𝕜) :
      P a (lp.single 1 i z) = a i * z := by
    simp only [P, dualPairing_apply, ContinuousLinearMap.mul_apply', lp.single_apply,
      Pi.single_apply, mul_ite, mul_zero, tsum_ite_eq]
  have hnorm (a : lp (fun _ : ι ↦ 𝕜) ∞) : ‖P a‖ = ‖a‖ := by
    apply le_antisymm
    · exact (P.le_opNorm a).trans (by
        simpa using mul_le_mul_of_nonneg_right
          (norm_dualPairing (p := ∞) (q := 1)
            (fun _ : ι ↦ ContinuousLinearMap.mul 𝕜 𝕜) (fun _ ↦ hmul)) (norm_nonneg a))
    · apply norm_le_of_forall_le (norm_nonneg _)
      intro i
      simpa [hP, lp.norm_single] using (P a).le_opNorm (lp.single 1 i (1 : 𝕜))
  refine LinearIsometryEquiv.ofSurjective
    { P.toLinearMap with norm_map' := hnorm } ?_
  intro f
  have hbound (i : ι) : ‖f (lp.single 1 i (1 : 𝕜))‖ ≤ ‖f‖ := by
    simpa [lp.norm_single] using f.le_opNorm (lp.single 1 i (1 : 𝕜))
  let a : lp (fun _ : ι ↦ 𝕜) ∞ :=
    ⟨fun i ↦ f (lp.single 1 i 1), memℓp_infty ⟨‖f‖, by
      rintro _ ⟨i, rfl⟩
      exact hbound i⟩⟩
  have ha (i : ι) : a i = f (lp.single 1 i 1) := rfl
  refine ⟨a, ?_⟩
  apply ContinuousLinearMap.ext
  intro x
  simp only [LinearIsometry.coe_mk, ContinuousLinearMap.coe_coe, P, dualPairing_apply,
    ContinuousLinearMap.mul_apply', ha]
  exact (f.hasSum_lp_single_mul x).tsum_eq

variable {𝕜 ι}

/-- The forward duality map is the scalar series pairing. -/
theorem dualOneEquiv_apply (a : lp (fun _ : ι ↦ 𝕜) ∞) (x : lp (fun _ : ι ↦ 𝕜) 1) :
    dualOneEquiv 𝕜 ι a x = ∑' i, a i * x i := by
  rfl

variable [DecidableEq ι]

/-- On a coordinate vector, a bounded family's functional is multiplication by that coordinate. -/
@[simp]
theorem dualOneEquiv_apply_single (a : lp (fun _ : ι ↦ 𝕜) ∞) (i : ι) (z : 𝕜) :
    dualOneEquiv 𝕜 ι a (lp.single 1 i z) = a i * z := by
  simp [dualOneEquiv_apply, lp.single_apply, Pi.single_apply]

end lp

namespace ContinuousLinearMap

variable {𝕜 ι : Type*} [RCLike 𝕜] [DecidableEq ι]

/-- The inverse duality map records a functional's values on the unit coordinate vectors. -/
@[simp]
theorem lp_dualOneEquiv_symm_apply (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1)) (i : ι) :
    (lp.dualOneEquiv 𝕜 ι).symm f i = f (lp.single 1 i 1) := by
  have h := congrArg (fun g : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1) ↦
    g (lp.single 1 i 1)) ((lp.dualOneEquiv 𝕜 ι).apply_symm_apply f)
  rwa [lp.dualOneEquiv_apply_single, mul_one] at h

/-- The norm of a functional on ℓ¹ is the supremum of the norms of its coordinate values. -/
theorem norm_eq_ciSup_norm_lp_single (f : StrongDual 𝕜 (lp (fun _ : ι ↦ 𝕜) 1)) :
    ‖f‖ = ⨆ i, ‖f (lp.single 1 i 1)‖ := by
  rw [← (lp.dualOneEquiv 𝕜 ι).symm.norm_map f, lp.norm_eq_ciSup]
  simp only [lp_dualOneEquiv_symm_apply]

end ContinuousLinearMap
