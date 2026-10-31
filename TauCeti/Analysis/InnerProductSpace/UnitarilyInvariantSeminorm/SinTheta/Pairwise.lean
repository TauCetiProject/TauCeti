/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.SinTheta.Basic
public import TauCeti.Analysis.InnerProductSpace.UnitarilyInvariantSeminorm.Sylvester.Pairwise

/-!
# Pairwise Davis--Kahan sine theorem

For symmetric operators `A` and `B`, let `U` be invariant under `A` and `V`
invariant under `B`. If the spectra of `A` on `U` and `B` on `Vᗮ` are pairwise
separated by `delta`, then every unitarily invariant seminorm satisfies

`delta * N (P_(Vᗮ) P_U) <= (pi / 2) * N (B - A)`.

No interval ordering of the two spectral blocks is required. The proof
applies the pairwise Sylvester estimate for invariant subspaces and then
uses the common projected-residual estimate to bound the perturbation.

## References

* C. Davis, W. M. Kahan, *The rotation of eigenvectors by a perturbation. III*,
  SIAM J. Numer. Anal. **7** (1970), 1--46.
* R. Bhatia, *Matrix Analysis*, Chapter VII.
* Adapted from the maintained Kitware DKPS formalization (Apache-2.0),
  `ForTauCeti/Analysis/InnerProductSpace/SinTheta/Perturbation.lean`.
-/

public section

namespace TauCeti.UnitarilyInvariantSeminorm

open scoped InnerProductSpace

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [FiniteDimensional 𝕜 E]

/-- **The pairwise `pi/2` Davis--Kahan sine theorem.** If the spectra of
`A` on `U` and `B` on `Vᗮ` are at distance at least `delta`, then the
perturbation controls the directed sine in every unitarily invariant seminorm.
The conclusion also holds at zero or negative `delta`. -/
theorem mul_map_starProjection_comp_starProjection_le_pi_div_two_mul_map_sub
    (N : UnitarilyInvariantSeminorm 𝕜 E E)
    {A B : E →L[𝕜] E}
    (hA : (A : E →ₗ[𝕜] E).IsSymmetric)
    (hB : (B : E →ₗ[𝕜] E).IsSymmetric)
    {U V : Submodule 𝕜 E} (hU : ∀ x ∈ U, A x ∈ U)
    (hV : ∀ x ∈ V, B x ∈ V) {δ : ℝ}
    (hgap : Module.End.PointSpectraSeparated (A : E →ₗ[𝕜] E) U
      (B : E →ₗ[𝕜] E) Vᗮ δ) :
    δ * N (Vᗮ.starProjection ∘L U.starProjection) ≤
      (Real.pi / 2) * N (B - A) := by
  let : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  have hVorth : ∀ x ∈ Vᗮ, B x ∈ Vᗮ :=
    fun _ hx => hB.orthogonalComplement_mem_invtSubmodule (p := V) hV hx
  have hpair : δ * N (Vᗮ.starProjection ∘L U.starProjection) ≤
      Real.pi / 2 * N (B.sylvester A (Vᗮ.starProjection ∘L U.starProjection)) :=
    N.mul_map_le_pi_div_two_mul_map_sylvester_apply_of_mem hB hA hVorth hU
      hgap.symm (fun x => Vᗮ.starProjection_apply_mem _)
      (fun x hx => by simp [U.starProjection_apply_eq_zero_iff.mpr hx])
  calc
    δ * N (Vᗮ.starProjection ∘L U.starProjection) ≤
        Real.pi / 2 * N (B.sylvester A (Vᗮ.starProjection ∘L U.starProjection)) := hpair
    _ ≤ Real.pi / 2 * N (B - A) :=
      mul_le_mul_of_nonneg_left
        (N.map_sylvester_starProjection_comp_starProjection_le hA hB hU hV)
        (by positivity)

end TauCeti.UnitarilyInvariantSeminorm
