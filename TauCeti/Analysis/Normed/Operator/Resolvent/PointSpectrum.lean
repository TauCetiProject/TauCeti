/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Compact
public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.SpectralMapping

/-!
# Operators with compact resolvent have pure point spectrum

Let `A : X →ₗ.[𝕜] X` be a partial linear map on a Banach space with compact resolvent
(`LinearPMap.HasCompactResolvent`), such as a self-adjoint elliptic operator on a closed manifold.
Then every point of its spectrum is an eigenvalue: `μ` lies in the spectrum of `A` exactly when
`A - μ I` has a nonzero kernel
(`LinearPMap.HasCompactResolvent.mem_spectrum_iff_ker_subScalar_ne_bot`). So the spectrum of `A`
is its point spectrum, and two such operators with the same eigenvalues have the same spectrum.

One direction holds for every operator: an eigenvalue is never a resolvent point
(`TauCeti.LinearPMap.mem_spectrum_of_ker_subScalar_ne_bot`). For the other, take a resolvent point
`z` at which the resolvent `R(z)` is compact. If `μ` lies in the spectrum then `μ ≠ z`, and by the
spectral mapping for the resolvent (`TauCeti.LinearPMap.notMem_spectrum_resolvent_iff`) the nonzero
scalar `(z - μ)⁻¹` lies in the spectrum of `R(z)`. By the Fredholm alternative for compact
operators (`IsCompactOperator.hasEigenvalue_iff_mem_spectrum`) it is an eigenvalue of `R(z)`, with
an eigenvector `y ≠ 0`. Then `x = R(z) y = (z - μ)⁻¹ y` is a nonzero vector of the domain of `A`
with `A x = z x - y = μ x`.

## Main results

* `LinearPMap.HasCompactResolvent.mem_spectrum_iff_ker_subScalar_ne_bot`: the spectrum of an
  operator with compact resolvent consists of its eigenvalues.

## References

* T. Kato, *Perturbation Theory for Linear Operators*, Chapter III, Theorem 6.29.
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  §XIII.14.
-/

public section

namespace LinearPMap

open TauCeti.LinearPMap (mem_spectrum_of_ker_subScalar_ne_bot notMem_spectrum_resolvent_iff)

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  [CompleteSpace X] {A : X →ₗ.[𝕜] X} {μ : 𝕜}

/-- **An operator with compact resolvent has pure point spectrum.** A scalar `μ` lies in the
spectrum of `A` exactly when it is an eigenvalue, that is when `A - μ I` has a nonzero kernel. -/
theorem HasCompactResolvent.mem_spectrum_iff_ker_subScalar_ne_bot (h : A.HasCompactResolvent) :
    μ ∈ A.spectrum ↔ (A.subScalar μ).ker ≠ ⊥ := by
  refine ⟨fun hμ hbot ↦ ?_, mem_spectrum_of_ker_subScalar_ne_bot⟩
  obtain ⟨z, hz, hc⟩ := hasCompactResolvent_def.1 h
  have hzμ : z - μ ≠ 0 := sub_ne_zero.2 fun he ↦ (mem_spectrum_iff A μ).1 hμ (he ▸ hz)
  -- `(z - μ)⁻¹` lies in the spectrum of the compact resolvent `R(z)`, so it is an eigenvalue.
  have hspec : (z - μ)⁻¹ ∈ _root_.spectrum 𝕜 (A.resolvent z) := by
    by_contra hn
    have := (notMem_spectrum_resolvent_iff hz (inv_ne_zero hzμ)).1 hn
    rw [inv_inv, sub_sub_cancel] at this
    exact (mem_spectrum_iff A μ).1 hμ this
  obtain ⟨y, hy, hy0⟩ :=
    ((hc.hasEigenvalue_iff_mem_spectrum (inv_ne_zero hzμ)).2 hspec).exists_hasEigenvector
  have hRy : A.resolvent z y = (z - μ)⁻¹ • y := Module.End.mem_eigenspace_iff.1 hy
  -- The vector `R(z) y = (z - μ)⁻¹ y` is an eigenvector of `A` for `μ`, so it vanishes.
  have hx : A.resolvent z y ∈ (A.subScalar μ).ker := by
    refine mem_ker_subScalar_iff.2 ⟨resolvent_mem_domain hz y, ?_⟩
    have hcoef : z * (z - μ)⁻¹ - 1 = μ * (z - μ)⁻¹ := by
      field_simp
      ring
    rw [apply_resolvent hz, hRy, smul_smul, smul_smul, ← hcoef, sub_smul, one_smul]
  rw [hbot, Submodule.mem_bot, hRy, smul_eq_zero] at hx
  exact hy0 (hx.resolve_left (inv_ne_zero hzμ))

end LinearPMap
