/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic

/-!
# Pythagoras for Hilbert–Schmidt energy

A family of bounded maps that splits the squared norm of every vector also splits the
Hilbert–Schmidt energy of every operator composed with that family. On the source side the
norm-splitting condition is imposed on the adjoints. Together these give a two-sided splitting
of the energy into operator blocks.

The index types are arbitrary and all sums take values in `ℝ≥0∞`. The identities therefore
apply to infinite orthogonal decompositions and to operators of infinite energy, without
summability assumptions. Orthogonal projections onto a subspace and its orthogonal complement
give the binary splitting formulas.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  revised edition, Academic Press, 1980, Section VI.6.
* B. Simon, *Trace Ideals and Their Applications*, second edition, American Mathematical
  Society, 2005, Section 2.
-/

public section

open scoped ENNReal

namespace ContinuousLinearMap

variable {𝕜 E F G ι κ η : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-- A family splitting squared norms on the target splits Hilbert–Schmidt energy under
left composition. Neither completeness nor finite energy is required. -/
theorem tsum_hilbertSchmidtEnergy_comp_left (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (P : κ → F →L[𝕜] G) (hP : ∀ v, ∑' j, ‖P j v‖ₑ ^ 2 = ‖v‖ₑ ^ 2) :
    ∑' j, ((P j) ∘L T).hilbertSchmidtEnergy b = T.hilbertSchmidtEnergy b := by
  simp only [hilbertSchmidtEnergy_def, comp_apply]
  rw [ENNReal.tsum_comm]
  simp only [hP]

/-- Splitting the target into a projected subspace and its orthogonal complement splits
Hilbert–Schmidt energy as a sum, including when the energy is infinite. -/
theorem hilbertSchmidtEnergy_starProjection_comp_add_orthogonal (T : E →L[𝕜] F)
    (b : HilbertBasis ι 𝕜 E) (V : Submodule 𝕜 F) [V.HasOrthogonalProjection] :
    (V.starProjection ∘L T).hilbertSchmidtEnergy b +
      (Vᗮ.starProjection ∘L T).hilbertSchmidtEnergy b = T.hilbertSchmidtEnergy b := by
  rw [hilbertSchmidtEnergy_def, hilbertSchmidtEnergy_def, hilbertSchmidtEnergy_def,
    ← ENNReal.tsum_add]
  refine tsum_congr fun i ↦ ?_
  simp only [comp_apply, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← V.norm_sq_eq_add_norm_sq_starProjection]

section Complete

variable [CompleteSpace E] [CompleteSpace F]

/-- A family whose adjoints split squared norms on the source splits Hilbert–Schmidt energy
under right composition. This includes infinite energy and arbitrary index types. -/
theorem tsum_hilbertSchmidtEnergy_comp_right (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (Q : η → E →L[𝕜] E) (hQ : ∀ v, ∑' j, ‖adjoint (Q j) v‖ₑ ^ 2 = ‖v‖ₑ ^ 2) :
    ∑' j, (T ∘L Q j).hilbertSchmidtEnergy b = T.hilbertSchmidtEnergy b := by
  obtain ⟨_, c, -⟩ := exists_hilbertBasis 𝕜 F
  simp_rw [← hilbertSchmidtEnergy_adjoint _ b c, adjoint_comp]
  exact tsum_hilbertSchmidtEnergy_comp_left (adjoint T) c (fun j ↦ adjoint (Q j)) hQ

/-- Splitting the source into a projected subspace and its orthogonal complement splits
Hilbert–Schmidt energy as a sum, including when the energy is infinite. -/
theorem hilbertSchmidtEnergy_comp_starProjection_add_orthogonal (T : E →L[𝕜] F)
    (b : HilbertBasis ι 𝕜 E) (U : Submodule 𝕜 E) [U.HasOrthogonalProjection] :
    (T ∘L U.starProjection).hilbertSchmidtEnergy b +
      (T ∘L Uᗮ.starProjection).hilbertSchmidtEnergy b = T.hilbertSchmidtEnergy b := by
  obtain ⟨_, c, -⟩ := exists_hilbertBasis 𝕜 F
  simp_rw [← hilbertSchmidtEnergy_adjoint _ b c, adjoint_comp]
  simpa only [← star_eq_adjoint, (isSelfAdjoint_starProjection U).star_eq,
    (isSelfAdjoint_starProjection Uᗮ).star_eq] using
    hilbertSchmidtEnergy_starProjection_comp_add_orthogonal (adjoint T) c U

/-- Squared-norm splittings on the target and on the adjoints of source operators give the
joint Pythagoras identity for Hilbert–Schmidt energy. No summability hypothesis is needed. -/
theorem tsum_tsum_hilbertSchmidtEnergy_comp (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (P : κ → F →L[𝕜] G) (Q : η → E →L[𝕜] E)
    (hP : ∀ v, ∑' i, ‖P i v‖ₑ ^ 2 = ‖v‖ₑ ^ 2)
    (hQ : ∀ v, ∑' j, ‖adjoint (Q j) v‖ₑ ^ 2 = ‖v‖ₑ ^ 2) :
    ∑' j, ∑' i, ((P i) ∘L T ∘L Q j).hilbertSchmidtEnergy b =
      T.hilbertSchmidtEnergy b := by
  simp_rw [tsum_hilbertSchmidtEnergy_comp_left _ b P hP]
  exact tsum_hilbertSchmidtEnergy_comp_right T b Q hQ

end Complete

end ContinuousLinearMap
