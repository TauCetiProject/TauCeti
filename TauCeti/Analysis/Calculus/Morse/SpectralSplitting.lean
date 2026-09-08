/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.Index
public import TauCeti.Analysis.Calculus.Morse.Linearization
public import TauCeti.Analysis.InnerProductSpace.Spectrum

/-!
# Spectral splitting at a Morse critical point

At a nondegenerate critical point on a finite-dimensional real Hilbert space, the Hessian is an
invertible self-adjoint operator. Its positive and negative spectral subspaces therefore give a
direct-sum decomposition of the tangent space. For the negative-gradient vector field, the
positive Hessian subspace is the stable linear subspace and the negative Hessian subspace is the
unstable linear subspace.

This file constructs those two subspaces and identifies the dimension of the unstable one with
the Morse index. The dimension statement uses the same ordered orthonormal eigenbasis both for
the spectral subspace and for Sylvester's law of inertia: in that basis, the Hessian quadratic
form is a weighted sum of squares whose weights are precisely the Hessian eigenvalues.

These are the linear data used by the local stable-manifold theorem. No local invariant manifold
is asserted here: that theorem additionally has to control the nonlinear remainder of the
negative-gradient field, supplied by
`TauCeti.IsNondegenerateCriticalPoint.neg_gradient_sub_linearization_isLittleO`.

## Main declarations

* `ContDiffAt.stableLinearSubspace`: the positive spectral subspace of the Hessian.
* `ContDiffAt.unstableLinearSubspace`: the negative spectral subspace of the Hessian.
* `TauCeti.IsNondegenerateCriticalPoint.unstableLinearSubspace_sup_stableLinearSubspace`: at a
  nondegenerate critical point these subspaces span the whole tangent space.
* `TauCeti.IsNondegenerateCriticalPoint.finrank_unstableLinearSubspace`: the unstable dimension is
  the Morse index.
* `TauCeti.IsNondegenerateCriticalPoint.finrank_stableLinearSubspace_add_morseIndex`: the stable
  dimension plus the Morse index is the ambient dimension.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §2.
-/

public section

open InnerProductSpace Set

noncomputable section

namespace ContDiffAt

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}

/-- The stable linear subspace of the negative-gradient field at a `C²` point: the span of the
Hessian eigenvectors with positive eigenvalues. The negative Hessian linearization contracts
these directions. -/
noncomputable def stableLinearSubspace (hf : ContDiffAt ℝ 2 f x) : Submodule ℝ E :=
  hf.isSelfAdjoint_hessianOperator.isSymmetric.positiveSpectralSubspace rfl

/-- The unstable linear subspace of the negative-gradient field at a `C²` point: the span of the
Hessian eigenvectors with negative eigenvalues. The negative Hessian linearization expands these
directions in forward time. -/
noncomputable def unstableLinearSubspace (hf : ContDiffAt ℝ 2 f x) : Submodule ℝ E :=
  hf.isSelfAdjoint_hessianOperator.isSymmetric.negativeSpectralSubspace rfl

/-- The Hessian preserves the stable linear subspace. -/
theorem map_hessianOperator_stableLinearSubspace_le (hf : ContDiffAt ℝ 2 f x) :
    Submodule.map (hessianOperator f x).toLinearMap hf.stableLinearSubspace ≤
      hf.stableLinearSubspace := by
  rw [stableLinearSubspace]
  exact hf.isSelfAdjoint_hessianOperator.isSymmetric.map_positiveSpectralSubspace_le rfl

/-- The Hessian preserves the unstable linear subspace. -/
theorem map_hessianOperator_unstableLinearSubspace_le (hf : ContDiffAt ℝ 2 f x) :
    Submodule.map (hessianOperator f x).toLinearMap hf.unstableLinearSubspace ≤
      hf.unstableLinearSubspace := by
  rw [unstableLinearSubspace]
  exact hf.isSelfAdjoint_hessianOperator.isSymmetric.map_negativeSpectralSubspace_le rfl

/-- The stable and unstable linear subspaces at a `C²` point are disjoint. This does not require
nondegeneracy: the zero eigenspace belongs to neither subspace. -/
theorem disjoint_unstableLinearSubspace_stableLinearSubspace (hf : ContDiffAt ℝ 2 f x) :
    Disjoint hf.unstableLinearSubspace hf.stableLinearSubspace := by
  exact hf.isSelfAdjoint_hessianOperator.isSymmetric
    |>.disjoint_negativeSpectralSubspace_positiveSpectralSubspace rfl

/-- In the Hessian eigenbasis, the number of negative eigenvalues, counted with multiplicity, is
the Morse index. -/
theorem morseIndex_eq_ncard_hessianOperator_eigenvalues_neg (hf : ContDiffAt ℝ 2 f x) :
    morseIndex f x =
      {i | hf.isSelfAdjoint_hessianOperator.isSymmetric.eigenvalues rfl i < 0}.ncard := by
  let hT := hf.isSelfAdjoint_hessianOperator.isSymmetric
  let b := hT.eigenvectorBasis rfl
  have horth : (QuadraticMap.associated (hessianQuadraticForm f x)).IsOrthoᵢ b := by
    rw [LinearMap.isOrthoᵢ_def]
    intro i j hij
    rw [associated_hessianQuadraticForm hf, ContinuousLinearMap.toBilinForm_apply,
      ← inner_hessianOperator_left]
    have heigen : hessianOperator f x (b i) =
        (hT.eigenvalues rfl i : ℝ) • b i := by
      exact hT.apply_eigenvectorBasis rfl i
    rw [heigen, real_inner_smul_left, orthonormal_iff_ite.mp b.orthonormal i j]
    simp [hij]
  have hequiv : QuadraticMap.Equivalent (hessianQuadraticForm f x)
      (QuadraticMap.weightedSumSquares ℝ fun i ↦ hessianQuadraticForm f x (b i)) :=
    ⟨QuadraticForm.isometryEquivWeightedSumSquares (hessianQuadraticForm f x) b.toBasis horth⟩
  have hweights : (fun i ↦ hessianQuadraticForm f x (b i)) = hT.eigenvalues rfl := by
    funext i
    rw [hessianQuadraticForm_apply, ← inner_hessianOperator_left]
    have heigen : hessianOperator f x (b i) =
        (hT.eigenvalues rfl i : ℝ) • b i := by
      exact hT.apply_eigenvectorBasis rfl i
    rw [heigen, real_inner_smul_left, orthonormal_iff_ite.mp b.orthonormal i i]
    simp
  rw [hweights] at hequiv
  rw [morseIndex_def]
  simpa only [hT] using
    QuadraticForm.sigNeg_of_equiv_weightedSumSquares hequiv

end ContDiffAt

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {f : E → ℝ} {x : E}

/-- At a nondegenerate critical point, the unstable and stable linear subspaces span the whole
tangent space. Nondegeneracy excludes the zero eigenspace. -/
theorem IsNondegenerateCriticalPoint.unstableLinearSubspace_sup_stableLinearSubspace
    (h : IsNondegenerateCriticalPoint f x) :
    h.contDiffAt.unstableLinearSubspace ⊔ h.contDiffAt.stableLinearSubspace = ⊤ := by
  apply h.contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric
    |>.negativeSpectralSubspace_sup_positiveSpectralSubspace_of_ker_eq_bot rfl
  exact LinearMap.ker_eq_bot.mpr h.isInvertible_hessianOperator.injective

/-- The dimension of the unstable linear subspace at a nondegenerate critical point is its Morse
index. -/
theorem IsNondegenerateCriticalPoint.finrank_unstableLinearSubspace
    (h : IsNondegenerateCriticalPoint f x) :
    Module.finrank ℝ h.contDiffAt.unstableLinearSubspace = morseIndex f x := by
  rw [ContDiffAt.unstableLinearSubspace,
    h.contDiffAt.isSelfAdjoint_hessianOperator.isSymmetric.finrank_negativeSpectralSubspace,
    h.contDiffAt.morseIndex_eq_ncard_hessianOperator_eigenvalues_neg]

/-- At a nondegenerate critical point, the dimension of the stable linear subspace plus the Morse
index is the dimension of the ambient tangent space. -/
theorem IsNondegenerateCriticalPoint.finrank_stableLinearSubspace_add_morseIndex
    (h : IsNondegenerateCriticalPoint f x) :
    Module.finrank ℝ h.contDiffAt.stableLinearSubspace + morseIndex f x =
      Module.finrank ℝ E := by
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    h.contDiffAt.unstableLinearSubspace h.contDiffAt.stableLinearSubspace
  rw [h.unstableLinearSubspace_sup_stableLinearSubspace,
    h.contDiffAt.disjoint_unstableLinearSubspace_stableLinearSubspace.eq_bot,
    finrank_top, finrank_bot, add_zero, h.finrank_unstableLinearSubspace] at hdim
  omega

end TauCeti

end
