/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import Mathlib.LinearAlgebra.Complex.Module
public import TauCeti.Analysis.InnerProductSpace.InvariantSubspace
public import TauCeti.Analysis.InnerProductSpace.NormalOperator
public import TauCeti.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap

/-!
# The spectral theorem for compact normal operators

A bounded operator `T` on a Hilbert space is *normal* when it commutes with its adjoint,
`IsStarNormal T`. Mathlib's spectral theorem for compact self-adjoint operators
(`ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot`) says that their eigenspaces
have trivial mutual orthogonal complement. This file extends it to compact normal operators on
complex Hilbert spaces.

*Eigenspaces of normal operators.* The eigenspaces of a normal operator are mutually orthogonal
(`IsStarNormal.orthogonalFamily_eigenspaces`), and the orthogonal complement of all of them is
invariant under both `T` and `T†`. Over `ℂ`, the eigenspace of `T` at `μ` is the joint eigenspace
of its real part `ℜ T` at `re μ` and its imaginary part `ℑ T` at `im μ`. These general facts live
in `TauCeti.Analysis.InnerProductSpace.NormalOperator`.

*Compact normal operators.* In a C⋆-algebra the spectral radius of a normal element is its norm,
and the nonzero spectral values of a compact operator are eigenvalues; hence a compact normal
operator on a complex Hilbert space whose only eigenvalue is `0` vanishes
(`IsStarNormal.forall_hasEigenvalue_eq_zero_iff`). Restricting a compact normal `T` to the
orthogonal complement of its eigenspaces gives a compact normal operator without eigenvalues, so
that complement is trivial: **the eigenspaces of a compact normal operator span a dense
subspace** (`IsStarNormal.orthogonalComplement_iSup_eigenspaces_eq_bot`). This argument follows
Mathlib's proof of the self-adjoint case. The same statement for the joint eigenspaces of `ℜ T`
and `ℑ T` is the simultaneous diagonalization of these two commuting self-adjoint operators. It
follows that a compact normal operator has a Hilbert basis of eigenvectors, and that the closure
of the span of its eigenspaces at nonzero eigenvalues is the orthogonal complement of its kernel,
so `E = ker T ⊕ closure (⨆_{μ ≠ 0} E_μ)`.

The statements are specific to complex scalars: a rotation of the real plane is a compact normal
operator without eigenvectors.

## Main results

* `IsStarNormal.orthogonalComplement_iSup_eigenspaces_eq_bot`: **the spectral theorem for compact
  normal operators**, the eigenspaces have trivial mutual orthogonal complement.
* `IsStarNormal.orthogonalComplement_iSup_iSup_eigenspace_inf_eigenspace_eq_bot`: the joint
  eigenspaces of the real and imaginary parts have trivial mutual orthogonal complement.
* `IsStarNormal.exists_hilbertBasis_forall_hasEigenvector`: a compact normal operator has a Hilbert
  basis of eigenvectors.
* `IsStarNormal.isCompl_ker_topologicalClosure_iSup_eigenspaces_ne_zero`: the kernel and the
  closed span of the eigenspaces at nonzero eigenvalues are complementary.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer GTM 96 (1990), Section II.7
  (the spectral theorem for compact normal operators).
-/

public section

open Module.End ContinuousLinearMap ComplexStarModule
open scoped InnerProductSpace ComplexConjugate

namespace IsStarNormal

section Complex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {T : E →L[ℂ] E}

/-- A compact normal operator on a complex Hilbert space is zero exactly when its only eigenvalue
is zero. -/
theorem forall_hasEigenvalue_eq_zero_iff (hT : IsStarNormal T) (hc : IsCompactOperator T) :
    (∀ μ, HasEigenvalue (T : Module.End ℂ E) μ → μ = 0) ↔ T = 0 := by
  rw [← nnnorm_eq_zero, ← ENNReal.coe_eq_zero, ← IsStarNormal.spectralRadius_eq_nnnorm T,
    spectralRadius_eq_of_unital, ← not_iff_not, ENNReal.iSup_eq_zero]
  push Not
  apply exists_congr
  simp +contextual [hc.hasEigenvalue_iff_mem_spectrum]

/-- **The spectral theorem for compact normal operators**: the eigenspaces of a compact normal
operator on a complex Hilbert space have trivial mutual orthogonal complement. -/
theorem orthogonalComplement_iSup_eigenspaces_eq_bot (hT : IsStarNormal T)
    (hc : IsCompactOperator T) : (⨆ μ, eigenspace (T : Module.End ℂ E) μ)ᗮ = ⊥ := by
  let S : (⨆ μ, eigenspace (T : Module.End ℂ E) μ)ᗮ →L[ℂ]
      (⨆ μ, eigenspace (T : Module.End ℂ E) μ)ᗮ :=
    T.restrict hT.orthogonalComplement_iSup_eigenspaces_invariant
  have hS_compact : IsCompactOperator S :=
    hc.restrict' hT.orthogonalComplement_iSup_eigenspaces_invariant
  -- The orthogonal complement of the `T`-invariant span of the eigenspaces is `T†`-invariant.
  have hadj : ∀ v ∈ (⨆ μ, eigenspace (T : Module.End ℂ E) μ)ᗮ,
      adjoint T v ∈ (⨆ μ, eigenspace (T : Module.End ℂ E) μ)ᗮ := by
    refine (mem_invtSubmodule_iff_forall_mem_of_mem _).mp (orthogonal_mem_invtSubmodule ?_)
    rw [adjoint_adjoint, mem_invtSubmodule_iff_map_le, Submodule.map_iSup]
    exact iSup_mono fun μ ↦ (mem_invtSubmodule_iff_map_le _).mp (eigenspace_mem_invtSubmodule _ μ)
  have hS_normal : IsStarNormal S :=
    hT.restrict hT.orthogonalComplement_iSup_eigenspaces_invariant hadj
  -- `S` has no eigenvectors: they would be eigenvectors of `T` orthogonal to every eigenspace.
  have hS μ : eigenspace (S : Module.End ℂ (⨆ μ, eigenspace (T : Module.End ℂ E) μ)ᗮ) μ = ⊥ :=
    eigenspace_restrict_eq_bot hT.orthogonalComplement_iSup_eigenspaces_invariant
      ((Submodule.isOrtho_orthogonal_right _).mono_left (le_iSup _ μ)).disjoint
  have h μ : HasEigenvalue (S : Module.End ℂ (⨆ μ, eigenspace (T : Module.End ℂ E) μ)ᗮ) μ →
      μ = 0 := by
    simp_all [hasEigenvalue_iff]
  rw [hS_normal.forall_hasEigenvalue_eq_zero_iff hS_compact] at h
  rw [← Submodule.subsingleton_iff_eq_bot]
  by_contra! hV
  simpa [h] using hS 0

/-- **Simultaneous diagonalization** of the real and imaginary parts of a compact normal operator:
their joint eigenspaces have trivial mutual orthogonal complement. -/
theorem orthogonalComplement_iSup_iSup_eigenspace_inf_eigenspace_eq_bot (hT : IsStarNormal T)
    (hc : IsCompactOperator T) :
    (⨆ (a : ℂ) (b : ℂ), eigenspace ((ℜ T : E →L[ℂ] E) : Module.End ℂ E) a ⊓
      eigenspace ((ℑ T : E →L[ℂ] E) : Module.End ℂ E) b)ᗮ = ⊥ := by
  refine eq_bot_iff.mpr
    ((Submodule.orthogonal_le ?_).trans (hT.orthogonalComplement_iSup_eigenspaces_eq_bot hc).le)
  exact iSup_le fun μ ↦
    (hT.eigenspace_eq_eigenspace_realPart_inf_eigenspace_imaginaryPart μ).le.trans
      (le_iSup₂_of_le (μ.re : ℂ) (μ.im : ℂ) le_rfl)

/-- **A compact normal operator on a complex Hilbert space has an orthonormal basis of
eigenvectors.** The basis is indexed by a set of vectors of `E`, and no separability is
assumed. -/
theorem exists_hilbertBasis_forall_hasEigenvector (hT : IsStarNormal T)
    (hc : IsCompactOperator T) :
    ∃ (s : Set E) (b : HilbertBasis s ℂ E) (nu : s → ℂ), ⇑b = ((↑) : s → E) ∧
      ∀ x : s, HasEigenvector (T : Module.End ℂ E) (nu x) (x : E) :=
  exists_hilbertBasis_forall_hasEigenvector_of_dense_eigenspaces hT.orthogonalFamily_eigenspaces
    (hT.orthogonalComplement_iSup_eigenspaces_eq_bot hc)

/-- For a compact normal operator on a complex Hilbert space, the vectors orthogonal to every
eigenspace at a nonzero eigenvalue form the kernel. -/
theorem orthogonalComplement_iSup_eigenspaces_ne_zero_eq_ker (hT : IsStarNormal T)
    (hc : IsCompactOperator T) :
    (⨆ (μ) (_ : μ ≠ 0), eigenspace (T : Module.End ℂ E) μ)ᗮ = LinearMap.ker (T : E →ₗ[ℂ] E) := by
  set A := (⨆ (μ) (_ : μ ≠ 0), eigenspace (T : Module.End ℂ E) μ)ᗮ
  have : CompleteSpace (eigenspace (T : Module.End ℂ E) 0) :=
    (ContinuousLinearMap.isClosed_eigenspace T 0).completeSpace_coe
  rw [← eigenspace_zero]
  -- The kernel lies in `A`, and its orthogonal complement meets `A` trivially.
  have hle : eigenspace (T : Module.End ℂ E) 0 ≤ A :=
    (Submodule.isOrtho_iff_le.mp <| Submodule.IsOrtho.symm <| Submodule.isOrtho_iff_le.mpr <|
      iSup₂_le fun μ hμ ↦ Submodule.isOrtho_iff_le.mp (hT.orthogonalFamily_eigenspaces.isOrtho hμ))
  have hbot : (eigenspace (T : Module.End ℂ E) 0)ᗮ ⊓ A = ⊥ := by
    rw [inf_comm, Submodule.inf_orthogonal, sup_comm, ← iSup_split_single,
      hT.orthogonalComplement_iSup_eigenspaces_eq_bot hc]
  calc A = (eigenspace (T : Module.End ℂ E) 0 ⊔ (eigenspace (T : Module.End ℂ E) 0)ᗮ) ⊓ A := by
        rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection, top_inf_eq]
    _ = eigenspace (T : Module.End ℂ E) 0 := by
        rw [sup_inf_assoc_of_le _ hle, hbot, sup_bot_eq]

/-- For a compact normal operator on a complex Hilbert space, the closed span of the eigenspaces
at nonzero eigenvalues is the orthogonal complement of the kernel. -/
theorem topologicalClosure_iSup_eigenspaces_ne_zero (hT : IsStarNormal T)
    (hc : IsCompactOperator T) :
    (⨆ (μ) (_ : μ ≠ 0), eigenspace (T : Module.End ℂ E) μ).topologicalClosure =
      (LinearMap.ker (T : E →ₗ[ℂ] E))ᗮ := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure,
    hT.orthogonalComplement_iSup_eigenspaces_ne_zero_eq_ker hc]

/-- A complex Hilbert space is the direct sum of the kernel of a compact normal operator and the
closed span of its eigenspaces at nonzero eigenvalues. -/
theorem isCompl_ker_topologicalClosure_iSup_eigenspaces_ne_zero (hT : IsStarNormal T)
    (hc : IsCompactOperator T) :
    IsCompl (LinearMap.ker (T : E →ₗ[ℂ] E))
      (⨆ (μ) (_ : μ ≠ 0), eigenspace (T : Module.End ℂ E) μ).topologicalClosure := by
  have : CompleteSpace (LinearMap.ker (T : E →ₗ[ℂ] E)) :=
    (T.isClosed_ker).completeSpace_coe
  rw [hT.topologicalClosure_iSup_eigenspaces_ne_zero hc]
  exact Submodule.isCompl_orthogonal _

end Complex

end IsStarNormal
