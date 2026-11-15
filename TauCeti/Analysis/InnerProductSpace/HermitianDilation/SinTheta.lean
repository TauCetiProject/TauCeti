/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HermitianDilation.Norm
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Pairwise

/-!
# The pairwise `π / 2` `sin Θ` theorem for Hermitian dilations

For linear maps `A, Â : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, the Hermitian
dilations `D(A) = [[0, A†], [A, 0]]` and `D(Â)` are self-adjoint operators on the Hilbert direct
sum `WithLp 2 (E × F)`. Select the point-spectral subspaces `E_{D(A)}(Ω)` and `E_{D(Â)}(Ω')` by
sets `Ω, Ω' ⊆ ℝ`. If every eigenvalue of `D(A)` in `Ω` is at distance at least `δ` from every
eigenvalue of `D(Â)` outside `Ω'`, with no ordering or interval structure assumed, then

  `δ ‖sin Θ(E_{D(A)}(Ω), E_{D(Â)}(Ω'))‖ ≤ (π / 2) ‖Â - A‖`.

The case `Ω' = Ω` selects the same spectral window for both dilations.

This combines the pairwise `π / 2` Davis–Kahan theorem of Bhatia, Davis and McIntosh for the two
dilations with the fact that dilation preserves the operator norm, so that
`‖D(Â) - D(A)‖ = ‖Â - A‖`. The spectral blocks of the dilation recover the singular subspaces of
the rectangular map (`LinearMap.mem_pointSpectralSubspace_hermitianDilation_preimage_sq_iff`), so
this is the route by which the pairwise symmetric theory applies to rectangular perturbations.

## Main results

In the namespace `LinearMap`:

* `mul_norm_sinThetaMap_pointSpectralSubspace_hermitianDilation_le_pi_div_two_mul_norm_sub`: the
  pairwise `π / 2` `sin Θ` bound for the selected spectral subspaces of two Hermitian dilations, in
  terms of the rectangular perturbation.

## References

* R. Bhatia, C. Davis, A. McIntosh, *Perturbation of spectral subspaces and solution of linear
  operator equations*, Linear Algebra Appl. **52/53** (1983), 45–67.
* Y. Yu, T. Wang, and R. J. Samworth, *A useful variant of the Davis--Kahan theorem for
  statisticians*, Biometrika **102** (2015), 315--323.
-/

public section

open Module.End
open scoped Real

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- **The dilation pairwise-gap bound.** Let `A, Â : E →ₗ[𝕜] F` and `Ω, Ω' ⊆ ℝ`. If every
eigenvalue of the Hermitian dilation `D(A)` in `Ω` is at distance at least `δ` from every
eigenvalue of `D(Â)` outside `Ω'`, then the directed sine between the point-spectral subspaces
`E_{D(A)}(Ω)` and `E_{D(Â)}(Ω')` satisfies `δ ‖sin Θ(E_{D(A)}(Ω), E_{D(Â)}(Ω'))‖ ≤
(π / 2) ‖Â - A‖`. The right-hand side equals `(π / 2) ‖D(Â) - D(A)‖`
(`LinearMap.norm_toContinuousLinearMap_hermitianDilation_sub`). -/
theorem mul_norm_sinThetaMap_pointSpectralSubspace_hermitianDilation_le_pi_div_two_mul_norm_sub
    (A Â : E →ₗ[𝕜] F) {Ω Ω' : Set ℝ} {δ : ℝ}
    (h : PointSpectraSeparated A.hermitianDilation (pointSpectralSubspace A.hermitianDilation Ω)
      Â.hermitianDilation (pointSpectralSubspace Â.hermitianDilation Ω'ᶜ) δ) :
    δ * ‖(pointSpectralSubspace A.hermitianDilation Ω).sinThetaMap
        (pointSpectralSubspace Â.hermitianDilation Ω')‖ ≤
      π / 2 * ‖Â.toContinuousLinearMap - A.toContinuousLinearMap‖ := by
  have hsymm (B : E →ₗ[𝕜] F) :
      (B.hermitianDilation.toContinuousLinearMap :
        WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F)).IsSymmetric := by
    simpa only [coe_toContinuousLinearMap] using B.isSymmetric_hermitianDilation
  have hinv (B : E →ₗ[𝕜] F) (S : Set ℝ) :
      ∀ x ∈ pointSpectralSubspace B.hermitianDilation S,
        B.hermitianDilation.toContinuousLinearMap x ∈
          pointSpectralSubspace B.hermitianDilation S :=
    fun _ hx ↦ map_pointSpectralSubspace_le (Submodule.mem_map_of_mem hx)
  rw [← norm_toContinuousLinearMap_hermitianDilation_sub]
  refine Submodule.mul_norm_sinThetaMap_le_pi_div_two_mul_norm_sub _ _ (hsymm A) (hsymm Â)
    (hinv A Ω) (hinv Â Ω') ?_
  rwa [coe_toContinuousLinearMap, coe_toContinuousLinearMap,
    Â.isSymmetric_hermitianDilation.orthogonal_pointSpectralSubspace]

end LinearMap
