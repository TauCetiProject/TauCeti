/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Pseudoconvex.Basic
public import TauCeti.Analysis.InnerProductSpace.Spectrum

/-!
# The eigenvalue criterion for strong pseudoconvexity

On a finite-dimensional complex inner product space, the Levi form of a real function is
represented by a complex-linear operator through the Riesz isomorphism. For a `C²` function this
operator is self-adjoint. Its positive spectral subspace is a largest complex subspace on which
the Levi form is positive definite. Consequently strong `q`-pseudoconvexity, defined using a
positive subspace of codimension at most `q`, is equivalent to having at least `n - q` strictly
positive Levi eigenvalues, with multiplicity.

The count is independent of the choice of Hermitian inner product: the criterion identifies it
with the maximal dimension of a Levi-positive complex subspace. Zero eigenvalues are excluded;
nonnegative Levi directions cannot replace the strictly positive ones.

## Main declarations

* `TauCeti.leviOperator`: the operator characterized by
  `⟪leviOperator f x v, w⟫ = leviForm f x v w`.
* `TauCeti.isSymmetric_leviOperator`: it is self-adjoint for a real `C²` function.
* `TauCeti.isStronglyPseudoconvexAt_iff_le_ncard_pos_eigenvalues`: the spectral criterion.

The construction uses Mathlib's `InnerProductSpace.toDual` and native
`LinearMap.IsSymmetric.eigenvalues`, and the maximal-positive-subspace results in
`TauCeti.Analysis.InnerProductSpace.Spectrum`.

## References

* R. Hain, *Notes on the Morse theory of complex manifolds*, Section 2.
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Section 4.5 (inertia).
-/

public section

open InnerProductSpace Module
open scoped InnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The complex-linear operator representing the Levi form with respect to the given Hermitian
inner product: `⟪leviOperator f x v, w⟫ = leviForm f x v w`. For a real `C²` function it is
self-adjoint, so its native eigenvalues are real. -/
noncomputable def leviOperator (f : E → ℝ) (x : E) : E →ₗ[ℂ] E := by
  letI := FiniteDimensional.complete ℂ E
  let H : E →ₗ⋆[ℂ] StrongDual ℂ E :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp (leviForm f x)
  exact (toDual ℂ E).symm.toLinearEquiv.toLinearMap.comp H

/-- The Riesz characterization of the Levi operator. -/
@[simp]
theorem inner_leviOperator (f : E → ℝ) (x v w : E) :
    ⟪leviOperator f x v, w⟫_ℂ = leviForm f x v w := by
  let := FiniteDimensional.complete ℂ E
  simp [leviOperator, toDual_symm_apply]

/-- The Levi operator of a real `C²` function is self-adjoint. -/
theorem isSymmetric_leviOperator {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    (leviOperator f x).IsSymmetric := by
  intro v w
  rw [inner_leviOperator, ← inner_conj_symm, inner_leviOperator]
  exact ((isSymm_leviForm hf).eq w v).symm

/-- The inner-product identity uniquely characterizes the Levi operator. -/
theorem leviOperator_eq_iff (f : E → ℝ) (x : E) (T : E →ₗ[ℂ] E) :
    leviOperator f x = T ↔ ∀ v w, ⟪T v, w⟫_ℂ = leviForm f x v w := by
  constructor
  · rintro rfl v w
    exact inner_leviOperator f x v w
  · intro h
    ext v
    exact ext_inner_right ℂ (fun w ↦ (inner_leviOperator f x v w).trans (h v w).symm)

/-- **The eigenvalue criterion for strong pseudoconvexity.** A real `C²` function on a complex
`n`-dimensional inner product space is strongly `q`-pseudoconvex exactly when its Levi operator
has at least `n - q` strictly positive eigenvalues, counted with multiplicity. The additive
inequality also covers `q ≥ n` and the zero-dimensional space. -/
theorem isStronglyPseudoconvexAt_iff_le_ncard_pos_eigenvalues {f : E → ℝ} {x : E} {q : ℕ}
    (hf : ContDiffAt ℝ 2 f x) :
    IsStronglyPseudoconvexAt q f x ↔
      finrank ℂ E ≤ {i | 0 < (isSymmetric_leviOperator hf).eigenvalues rfl i}.ncard + q := by
  rw [isStronglyPseudoconvexAt_iff]
  constructor
  · rintro ⟨P, hdim, hpos⟩
    have hb := (isSymmetric_leviOperator hf).finrank_le_ncard_pos_eigenvalues rfl P
      (by simpa only [inner_leviOperator, RCLike.re_to_complex] using hpos)
    omega
  · intro h
    refine ⟨(isSymmetric_leviOperator hf).positiveSpectralSubspace rfl, ?_, ?_⟩
    · simpa only [LinearMap.IsSymmetric.finrank_positiveSpectralSubspace] using h
    · intro v hv hv0
      simpa only [inner_leviOperator, RCLike.re_to_complex] using
        (isSymmetric_leviOperator hf).re_inner_pos_of_mem_positiveSpectralSubspace rfl hv hv0

end TauCeti
