/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.ExteriorPower.Trace
public import TauCeti.LinearAlgebra.CliffordAlgebra.Bivector.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis

/-!
# Clifford bivectors in an orthonormal basis

Let `V` be a finite-dimensional real inner product space, `Q v = -‖v‖²`, and `e` an orthonormal
basis of `V`. A two-vector `F ∈ ⋀² V` expands over all ordered wedges as
`F = ½ ∑ⱼ ∑ₖ ⟪F, eⱼ ∧ eₖ⟫ eⱼ ∧ eₖ` (`OrthonormalBasis.sum_rankOne_ιMulti_two`). Since the
symmetric part of `c(eⱼ) c(eₖ)` is `-δⱼₖ` and the diagonal coefficients `⟪F, eⱼ ∧ eⱼ⟫` vanish,
its Clifford image `c₂(F)` (`CliffordAlgebra.bivectorExterior`) is the full double sum
`∑ⱼ ∑ₖ ⟪F, eⱼ ∧ eₖ⟫ c(eⱼ) c(eₖ) = 2 c₂(F)`. This is the form in which the curvature term of the
Weitzenböck formula appears.

## Main results

* `OrthonormalBasis.sum_sum_inner_smul_ι_mul_ι`:
  `∑ⱼ ∑ₖ ⟪F, eⱼ ∧ eₖ⟫ c(eⱼ) c(eₖ) = 2 c₂(F)`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton University Press (1989),
  Chapter II, §8.
-/

public section

open CliffordAlgebra
open scoped RealInnerProductSpace

namespace OrthonormalBasis

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Q : QuadraticForm ℝ V} {κ : Type*} [Fintype κ]

/-- The Clifford image of a two-vector `F` in an orthonormal basis `e`, for `Q v = -‖v‖²`:
`∑ⱼ ∑ₖ ⟪F, eⱼ ∧ eₖ⟫ c(eⱼ) c(eₖ) = 2 c₂(F)`. -/
theorem sum_sum_inner_smul_ι_mul_ι (e : OrthonormalBasis κ ℝ V) (hQ : ∀ v, Q v = -‖v‖ ^ 2)
    (F : ⋀[ℝ]^2 V) :
    ∑ j, ∑ k, ⟪F, exteriorPower.ιMulti ℝ 2 ![e j, e k]⟫ • (ι Q (e j) * ι Q (e k)) =
      (2 : ℝ) • bivectorExterior Q F := by
  classical
  -- Expand `F = ½ ∑ⱼ ∑ₖ ⟪F, eⱼ ∧ eₖ⟫ eⱼ ∧ eₖ`, so `2 c₂(F) = ∑ⱼ ∑ₖ ⟪F, eⱼ ∧ eₖ⟫ c₂(eⱼ ∧ eₖ)`.
  have hF := congrArg (fun T : Module.End ℝ (⋀[ℝ]^2 V) ↦ bivectorExterior Q (T F))
    (e.sum_rankOne_ιMulti_two)
  simp only [LinearMap.sum_apply, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
    map_sum, map_smul, LinearMap.smul_apply, LinearMap.id_apply,
    bivectorExterior_apply_ιMulti] at hF
  rw [← hF]
  -- The symmetric part `½ polar Q eⱼ eₖ = -δⱼₖ` of `c(eⱼ) c(eₖ)` meets only the diagonal
  -- coefficients `⟪F, eⱼ ∧ eⱼ⟫ = 0`.
  have hdiag (j k : κ) : ⟪F, exteriorPower.ιMulti ℝ 2 ![e j, e k]⟫ •
      ((⅟ (2 : ℝ)) • algebraMap ℝ (CliffordAlgebra Q) (QuadraticMap.polar Q (e j) (e k))) = 0 := by
    rcases eq_or_ne j k with rfl | hjk
    · rw [(exteriorPower.ιMulti ℝ 2).map_eq_zero_of_eq ![e j, e j] (i := 0) (j := 1) (by simp)
        (by decide), inner_zero_right, zero_smul]
    · simp [e.polar_apply_apply hQ j k, hjk]
  simp only [ι_mul_ι_eq_bivector_add, smul_add, hdiag, add_zero, real_inner_comm F]

end OrthonormalBasis
