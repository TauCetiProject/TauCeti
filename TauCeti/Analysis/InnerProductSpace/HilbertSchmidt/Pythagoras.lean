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
For an operator of finite energy, the splitting by an orthogonal projection `p` becomes
Pythagoras for the norm, `‖T‖_HS² = ‖p T‖_HS² + ‖(1 - p) T‖_HS²`. Applied to `p` and to the
pieces `(1 - p) T` and `p (1 - q) T` of `(1 - p q) T`, it bounds the energy removed by `p q`:
`‖(1 - p q) T‖_HS² ≤ ‖(1 - p) T‖_HS² + ‖(1 - q) T‖_HS²` for every operator `q` on the target.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*,
  revised edition, Academic Press, 1980, Section VI.6.
* B. Simon, *Trace Ideals and Their Applications*, second edition, American Mathematical
  Society, 2005, Section 2.
* The bound for `1 - p q` follows the statement `New.hilbertSchmidtNorm_one_sub_mul_comp_sq_le`
  in the folder `grh` of https://github.com/lsernau/grh-lean at commit
  72fead102f663d5c7a407964a13dc0cf9d977207.
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
  rw [_root_.tsum_comm]
  simp only [hP]

/-- Splitting the target into a projected subspace and its orthogonal complement splits
Hilbert–Schmidt energy as a sum, including when the energy is infinite. -/
theorem hilbertSchmidtEnergy_starProjection_comp_add_orthogonal (T : E →L[𝕜] F)
    (b : HilbertBasis ι 𝕜 E) (V : Submodule 𝕜 F) [V.HasOrthogonalProjection] :
    (V.starProjection ∘L T).hilbertSchmidtEnergy b +
      (Vᗮ.starProjection ∘L T).hilbertSchmidtEnergy b = T.hilbertSchmidtEnergy b := by
  rw [hilbertSchmidtEnergy_def, hilbertSchmidtEnergy_def, hilbertSchmidtEnergy_def,
    ← _root_.tsum_add]
  refine tsum_congr fun i ↦ ?_
  simp only [comp_apply, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _),
    ← V.norm_sq_eq_add_norm_sq_starProjection]

section Complete

variable [CompleteSpace E] [CompleteSpace F]
variable {H ι' : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- A family whose adjoints split squared norms on the source splits Hilbert–Schmidt energy
under right composition. The composed operators may have a different source space.
This includes infinite energy and arbitrary index types. -/
theorem tsum_hilbertSchmidtEnergy_comp_right (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (b' : HilbertBasis ι' 𝕜 H) (Q : η → H →L[𝕜] E)
    (hQ : ∀ v, ∑' j, ‖adjoint (Q j) v‖ₑ ^ 2 = ‖v‖ₑ ^ 2) :
    ∑' j, (T ∘L Q j).hilbertSchmidtEnergy b' = T.hilbertSchmidtEnergy b := by
  obtain ⟨_, c, -⟩ := exists_hilbertBasis 𝕜 F
  simp_rw [← hilbertSchmidtEnergy_adjoint _ b' c,
    ← hilbertSchmidtEnergy_adjoint T b c, adjoint_comp]
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

/-- **Pythagoras for the Hilbert–Schmidt norm.** For an orthogonal projection `p` of the target
and an operator `T` of finite energy, `‖T‖_HS² = ‖p T‖_HS² + ‖(1 - p) T‖_HS²`. On a
finite-dimensional source the energy hypothesis is `hilbertSchmidtEnergy_ne_top`. -/
theorem sq_hilbertSchmidtNorm_eq_comp_add_one_sub_comp {p : F →L[𝕜] F}
    (hp : IsStarProjection p) (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (h : T.hilbertSchmidtEnergy b ≠ ∞) :
    T.hilbertSchmidtNorm ^ 2 =
      (p ∘L T).hilbertSchmidtNorm ^ 2 + ((1 - p) ∘L T).hilbertSchmidtNorm ^ 2 := by
  obtain ⟨V, _, rfl⟩ := isStarProjection_iff_eq_starProjection.mp hp
  have hsum := hilbertSchmidtEnergy_starProjection_comp_add_orthogonal T b V
  rw [← hsum, ENNReal.add_ne_top] at h
  simp only [← Submodule.starProjection_orthogonal', sq_hilbertSchmidtNorm _ b]
  rw [← ENNReal.toReal_add h.1 h.2, hsum]

/-- **Energy removed by a product with a projection.** For an orthogonal projection `p`, any
operator `q` on the target and an operator `T` of finite energy,
`‖(1 - p q) T‖_HS² ≤ ‖(1 - p) T‖_HS² + ‖(1 - q) T‖_HS²`. -/
theorem sq_hilbertSchmidtNorm_one_sub_mul_comp_le {p : F →L[𝕜] F} (hp : IsStarProjection p)
    (q : F →L[𝕜] F) (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (h : T.hilbertSchmidtEnergy b ≠ ∞) :
    ((1 - p * q) ∘L T).hilbertSchmidtNorm ^ 2 ≤
      ((1 - p) ∘L T).hilbertSchmidtNorm ^ 2 + ((1 - q) ∘L T).hilbertSchmidtNorm ^ 2 := by
  have hfin (X : F →L[𝕜] F) : (X ∘L T).hilbertSchmidtEnergy b ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) h) (hilbertSchmidtEnergy_comp_le_left X T b)
  have hpp : p * p = p := hp.isIdempotentElem.eq
  -- `1 - p q = (1 - p) + p (1 - q)`, and the two pieces have orthogonal ranges.
  have h₁ : p * (1 - p * q) = p * (1 - q) := by
    rw [mul_sub, mul_sub, ← mul_assoc, hpp]
  have h₂ : (1 - p) * (1 - p * q) = 1 - p := by
    rw [sub_mul, one_mul, h₁, mul_sub, mul_one]
    abel
  rw [sq_hilbertSchmidtNorm_eq_comp_add_one_sub_comp hp _ b (hfin _), ← comp_assoc, ← mul_def,
    h₁, ← comp_assoc, ← mul_def, h₂, add_comm, mul_def, comp_assoc]
  have hle := (hilbertSchmidtNorm_comp_le_left p ((1 - q) ∘L T) b (hfin _)).trans
    (mul_le_of_le_one_left (hilbertSchmidtNorm_nonneg _) hp.norm_le)
  gcongr
  exact hilbertSchmidtNorm_nonneg _

/-- Squared-norm splittings on the target and on the adjoints of source operators give the
joint Pythagoras identity for Hilbert–Schmidt energy. The blocks may have a different source
space. No summability hypothesis is needed. -/
theorem tsum_tsum_hilbertSchmidtEnergy_comp (T : E →L[𝕜] F) (b : HilbertBasis ι 𝕜 E)
    (b' : HilbertBasis ι' 𝕜 H) (P : κ → F →L[𝕜] G) (Q : η → H →L[𝕜] E)
    (hP : ∀ v, ∑' i, ‖P i v‖ₑ ^ 2 = ‖v‖ₑ ^ 2)
    (hQ : ∀ v, ∑' j, ‖adjoint (Q j) v‖ₑ ^ 2 = ‖v‖ₑ ^ 2) :
    ∑' j, ∑' i, ((P i) ∘L T ∘L Q j).hilbertSchmidtEnergy b' =
      T.hilbertSchmidtEnergy b := by
  simp_rw [tsum_hilbertSchmidtEnergy_comp_left _ b' P hP]
  exact tsum_hilbertSchmidtEnergy_comp_right T b b' Q hQ

end Complete

end ContinuousLinearMap
