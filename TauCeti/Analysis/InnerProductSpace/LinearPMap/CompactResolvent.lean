/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.Resolvent
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.OneAddSq

/-!
# Self-adjoint operators with compact resolvent

Every nonreal scalar lies in the resolvent set of a self-adjoint partial linear map `D` on a
Hilbert space. Hence `D` has compact resolvent exactly when `R(z) = (z - D)⁻¹` is compact at one,
equivalently every, nonreal `z`; in particular exactly when `(D - i)⁻¹ = R(-i, -D)` is compact,
which is the usual normalization for the Dirac operator of a spectral triple.

On a complex Hilbert space the bounded inverse `K = (1 + D²)⁻¹` of `LinearPMap.invOneAddSq` is
`R(i)* R(i)`, a positive injective operator, and it is compact when `D` has compact resolvent.
Mathlib's spectral theorem for compact self-adjoint operators then applies to `K`: its eigenspaces
for nonzero eigenvalues are finite-dimensional
(`LinearPMap.HasCompactResolvent.finiteDimensional_eigenspace_invOneAddSq`, from
`ContinuousLinearMap.finite_dimensional_eigenspace`) and, since `ker K = 0`, they span a dense
subspace of the Hilbert space. Each of them lies in every iterated domain `D(Dⁿ)` and is
invariant under `D`
(`LinearPMap.eigenspace_invOneAddSq_le_domainPow`, `LinearPMap.apply_mem_eigenspace_invOneAddSq`).
These are the ingredients for an orthonormal eigenbasis of `D`, obtained by diagonalizing `D` on
each of these finite-dimensional invariant subspaces.

## Main results

* `IsSelfAdjoint.hasCompactResolvent_iff_isCompactOperator_resolvent`: a self-adjoint operator
  has compact resolvent exactly when its resolvent at a given nonreal point is compact.
* `IsSelfAdjoint.hasCompactResolvent_iff_isCompactOperator_resolvent_neg_neg`: the same for the
  inverse `(D - z)⁻¹`.
* `IsSelfAdjoint.invOneAddSq_eq_adjoint_comp`: `(1 + D²)⁻¹ = R(i)* R(i)`.
* `IsSelfAdjoint.isPositive_invOneAddSq`: `(1 + D²)⁻¹` is a positive operator.
* `LinearPMap.HasCompactResolvent.finiteDimensional_eigenspace_invOneAddSq`: for compact
  resolvent, the eigenspaces of `(1 + D²)⁻¹` for nonzero eigenvalues are finite-dimensional.
* `IsSelfAdjoint.orthogonalComplement_iSup_eigenspaces_invOneAddSq_eq_bot`: for compact
  resolvent, the eigenspaces of `(1 + D²)⁻¹` for nonzero eigenvalues span a dense subspace.

## References

* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  §XIII.14.
* A. Connes, *Noncommutative Geometry*, Chapter IV, §2.
-/

public section

noncomputable section

namespace TauCeti

open _root_.LinearPMap Module End

section RCLike

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  {A : E →ₗ.[𝕜] E} {z : 𝕜}

/-- A self-adjoint operator has compact resolvent exactly when its resolvent `(z - A)⁻¹` at a
given nonreal point `z` is compact. -/
theorem _root_.IsSelfAdjoint.hasCompactResolvent_iff_isCompactOperator_resolvent
    (hA : IsSelfAdjoint A) (hz : RCLike.im z ≠ 0) :
    A.HasCompactResolvent ↔ IsCompactOperator (A.resolvent z) :=
  LinearPMap.hasCompactResolvent_iff_isCompactOperator_resolvent
    (hA.mem_resolventSet_of_im_ne_zero hz)

/-- A self-adjoint operator has compact resolvent exactly when the inverse
`(A - z)⁻¹ = R(-z, -A)` at a given nonreal point `z` is compact. For `z = i` this is the
condition that `(A - i)⁻¹` be compact. -/
theorem _root_.IsSelfAdjoint.hasCompactResolvent_iff_isCompactOperator_resolvent_neg_neg
    (hA : IsSelfAdjoint A) (hz : RCLike.im z ≠ 0) :
    A.HasCompactResolvent ↔ IsCompactOperator ((-A).resolvent (-z)) := by
  rw [← hasCompactResolvent_neg_iff]
  exact LinearPMap.hasCompactResolvent_iff_isCompactOperator_resolvent
    (mem_resolventSet_neg_iff.mpr (hA.mem_resolventSet_of_im_ne_zero hz))

end RCLike

section Complex

open Complex

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {A : H →ₗ.[ℂ] H}

/-- For an operator with compact resolvent, the eigenspaces of the compact operator
`(1 + A²)⁻¹` for nonzero eigenvalues are finite-dimensional. -/
theorem _root_.LinearPMap.HasCompactResolvent.finiteDimensional_eigenspace_invOneAddSq
    (hp : I ∈ A.resolventSet) (h : A.HasCompactResolvent) {μ : ℂ} (hμ : μ ≠ 0) :
    FiniteDimensional ℂ (eigenspace (A.invOneAddSq : End ℂ H) μ) :=
  ContinuousLinearMap.finite_dimensional_eigenspace (h.isCompactOperator_invOneAddSq hp) μ hμ

/-- For a self-adjoint operator, `(1 + A²)⁻¹ = R(i)* R(i)`. -/
theorem _root_.IsSelfAdjoint.invOneAddSq_eq_adjoint_comp (hA : IsSelfAdjoint A) :
    A.invOneAddSq = (A.resolvent I).adjoint ∘L A.resolvent I := by
  rw [hA.adjoint_resolvent hA.I_mem_resolventSet, conj_I, invOneAddSq_def]

/-- For a self-adjoint operator, `(1 + A²)⁻¹` is a positive operator. -/
theorem _root_.IsSelfAdjoint.isPositive_invOneAddSq (hA : IsSelfAdjoint A) :
    A.invOneAddSq.IsPositive := by
  rw [hA.invOneAddSq_eq_adjoint_comp]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

/-- For a self-adjoint operator `A` with compact resolvent, the eigenspaces of the compact positive
injective operator `(1 + A²)⁻¹` for nonzero eigenvalues span a dense subspace: their orthogonal
complement is zero. -/
theorem _root_.IsSelfAdjoint.orthogonalComplement_iSup_eigenspaces_invOneAddSq_eq_bot
    (hA : IsSelfAdjoint A) (h : A.HasCompactResolvent) :
    (⨆ (μ : ℂ) (_ : μ ≠ 0), eigenspace (A.invOneAddSq : End ℂ H) μ)ᗮ = ⊥ := by
  have h0 : eigenspace (A.invOneAddSq : End ℂ H) 0 = ⊥ := by
    rw [eigenspace_zero, LinearMap.ker_eq_bot, ContinuousLinearMap.coe_coe]
    exact invOneAddSq_injective hA.I_mem_resolventSet hA.neg_I_mem_resolventSet
  have hsup := iSup_split_single (fun μ => eigenspace (A.invOneAddSq : End ℂ H) μ) 0
  rw [h0, bot_sup_eq] at hsup
  rw [← hsup]
  exact ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot
    (h.isCompactOperator_invOneAddSq hA.I_mem_resolventSet)
    hA.isPositive_invOneAddSq.isSymmetric

end Complex

end TauCeti
