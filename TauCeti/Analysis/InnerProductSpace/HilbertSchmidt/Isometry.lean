/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HilbertSchmidt.Basic

/-!
# Isometric invariance of the Hilbert–Schmidt energy and norm

Composing a bounded operator `T` on the left with a norm-preserving map `U` does not change any
of its columns' norms `‖T bᵢ‖`, so it preserves the Hilbert–Schmidt energy `E_b(T) = ∑' i, ‖T bᵢ‖ₑ²`
exactly. Dually, composing on the right with a *coisometry* `V`, a map whose adjoint `V†`
preserves norms, preserves the energy: passing to adjoints turns `T V` into `V† T†`, and the energy
is invariant under adjoints. Together these give the two-sided invariance `‖U T V‖_HS = ‖T‖_HS`.
Unitary operators are both isometries and coisometries, so in particular the Hilbert–Schmidt norm
is invariant under unitary conjugation.

All statements are equalities in `ℝ≥0∞` or of real Hilbert–Schmidt norms, and hold for operators of
infinite energy as well; no finiteness hypothesis is needed.

## Main results

* `ContinuousLinearMap.hilbertSchmidtEnergy_isometry_comp`: `E_b(U T) = E_b(T)` when `U` preserves
  norms.
* `ContinuousLinearMap.hilbertSchmidtEnergy_comp_coisometry`: `E_b(T V) = E_c(T)` when `V†`
  preserves norms.
* `ContinuousLinearMap.hilbertSchmidtEnergy_isometry_comp_coisometry`: `E_b(U T V) = E_c(T)`.
* `ContinuousLinearMap.hilbertSchmidtNorm_isometry_comp`,
  `ContinuousLinearMap.hilbertSchmidtNorm_comp_coisometry` and
  `ContinuousLinearMap.hilbertSchmidtNorm_isometry_comp_coisometry`: the corresponding identities
  `‖U T‖_HS = ‖T‖_HS`, `‖T V‖_HS = ‖T‖_HS` and `‖U T V‖_HS = ‖T‖_HS`.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  edition, Academic Press, 1980, Section VI.6.
* B. Simon, *Trace Ideals and Their Applications*, second edition, Mathematical Surveys and
  Monographs 120, American Mathematical Society, 2005, Section 2.
-/

public section

open scoped InnerProductSpace ENNReal

namespace ContinuousLinearMap

variable {𝕜 E F G H ι ι' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- **Left isometric invariance of the energy.** If `U` preserves norms, then `E_b(U T) = E_b(T)`.
-/
theorem hilbertSchmidtEnergy_isometry_comp (U : F →L[𝕜] G) (hU : ∀ x, ‖U x‖ = ‖x‖)
    (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E) :
    (U ∘L T).hilbertSchmidtEnergy b = T.hilbertSchmidtEnergy b := by
  simp [hilbertSchmidtEnergy_def, ← ofReal_norm, hU]

variable [CompleteSpace E] [CompleteSpace F] [CompleteSpace G]

/-- **Left isometric invariance of the Hilbert–Schmidt norm.** If `U` preserves norms, then
`‖U T‖_HS = ‖T‖_HS`. -/
theorem hilbertSchmidtNorm_isometry_comp (U : F →L[𝕜] G) (hU : ∀ x, ‖U x‖ = ‖x‖)
    (T : E →L[𝕜] F) :
    (U ∘L T).hilbertSchmidtNorm = T.hilbertSchmidtNorm := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 E
  rw [hilbertSchmidtNorm_eq_sqrt _ b, hilbertSchmidtNorm_eq_sqrt _ b,
    hilbertSchmidtEnergy_isometry_comp U hU]

/-- **Right coisometric invariance of the energy.** If the adjoint of `V` preserves norms, then
`E_b(T V) = E_c(T)`, where `b` and `c` are Hilbert bases of the sources of `V` and `T`. -/
theorem hilbertSchmidtEnergy_comp_coisometry (T : F →L[𝕜] G) (V : E →L[𝕜] F)
    (hV : ∀ x, ‖adjoint V x‖ = ‖x‖) (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis ι' 𝕜 F) :
    (T ∘L V).hilbertSchmidtEnergy b = T.hilbertSchmidtEnergy c := by
  obtain ⟨w, d, -⟩ := exists_hilbertBasis 𝕜 G
  rw [← hilbertSchmidtEnergy_adjoint _ b d, ← hilbertSchmidtEnergy_adjoint T c d, adjoint_comp,
    hilbertSchmidtEnergy_isometry_comp _ hV]

/-- **Right coisometric invariance of the Hilbert–Schmidt norm.** If the adjoint of `V` preserves
norms, then `‖T V‖_HS = ‖T‖_HS`. -/
theorem hilbertSchmidtNorm_comp_coisometry (T : F →L[𝕜] G) (V : E →L[𝕜] F)
    (hV : ∀ x, ‖adjoint V x‖ = ‖x‖) :
    (T ∘L V).hilbertSchmidtNorm = T.hilbertSchmidtNorm := by
  obtain ⟨_, b, -⟩ := exists_hilbertBasis 𝕜 E
  obtain ⟨_, c, -⟩ := exists_hilbertBasis 𝕜 F
  rw [hilbertSchmidtNorm_eq_sqrt _ b, hilbertSchmidtNorm_eq_sqrt _ c,
    hilbertSchmidtEnergy_comp_coisometry T V hV b c]

/-- **Two-sided isometric invariance of the energy.** If `U` and the adjoint of `V` preserve
norms, then `E_b(U T V) = E_c(T)`. -/
theorem hilbertSchmidtEnergy_isometry_comp_coisometry (U : G →L[𝕜] H) (hU : ∀ x, ‖U x‖ = ‖x‖)
    (T : F →L[𝕜] G) (V : E →L[𝕜] F) (hV : ∀ x, ‖adjoint V x‖ = ‖x‖) (b : HilbertBasis ι 𝕜 E)
    (c : HilbertBasis ι' 𝕜 F) :
    (U ∘L T ∘L V).hilbertSchmidtEnergy b = T.hilbertSchmidtEnergy c := by
  rw [hilbertSchmidtEnergy_isometry_comp U hU, hilbertSchmidtEnergy_comp_coisometry T V hV b c]

/-- **Two-sided isometric invariance of the Hilbert–Schmidt norm.** If `U` and the adjoint of `V`
preserve norms, then `‖U T V‖_HS = ‖T‖_HS`. In particular the Hilbert–Schmidt norm is invariant
under conjugation by unitaries. -/
theorem hilbertSchmidtNorm_isometry_comp_coisometry [CompleteSpace H] (U : G →L[𝕜] H)
    (hU : ∀ x, ‖U x‖ = ‖x‖) (T : F →L[𝕜] G) (V : E →L[𝕜] F) (hV : ∀ x, ‖adjoint V x‖ = ‖x‖) :
    (U ∘L T ∘L V).hilbertSchmidtNorm = T.hilbertSchmidtNorm := by
  rw [hilbertSchmidtNorm_isometry_comp U hU, hilbertSchmidtNorm_comp_coisometry T V hV]

end ContinuousLinearMap
