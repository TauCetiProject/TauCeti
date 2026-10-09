/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Eigenspaces of `g ∘ f` and `f ∘ g`

For linear maps `f : M → N` and `g : N → M` and a unit `μ`, the map `f` carries the
`μ`-eigenspace of `g ∘ f` isomorphically onto the `μ`-eigenspace of `f ∘ g`, with inverse
`μ⁻¹ • g`. In particular the two composites have the same eigenvalue multiplicities at every
nonzero eigenvalue over a field. This is the multiplicity form of Mathlib's
`spectrum.nonzero_mul_comm`, and applied to `f = A` and `g = A†` it shows that the source and
target Gram operators `A† A` and `A A†` of a linear map between inner product spaces have the
same nonzero eigenvalues with multiplicity.

## Main declarations

* `Module.End.eigenspaceCompEquiv`: the linear equivalence induced by `f` between the
  `μ`-eigenspaces of `g ∘ₗ f` and `f ∘ₗ g`.
* `Module.End.finrank_eigenspace_comp_comm`: the two eigenspaces have the same dimension.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 1.3.22.
-/

public section

namespace Module.End

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- `f` maps the `μ`-eigenspace of `g ∘ₗ f` into the `μ`-eigenspace of `f ∘ₗ g`. -/
theorem apply_mem_eigenspace_comp {f : M →ₗ[R] N} {g : N →ₗ[R] M} {μ : R} {x : M}
    (hx : x ∈ eigenspace (g ∘ₗ f) μ) : f x ∈ eigenspace (f ∘ₗ g) μ := by
  rw [mem_eigenspace_iff] at hx ⊢
  simpa using congrArg f hx

/-- For a unit `μ`, `f` restricts to a linear equivalence from the `μ`-eigenspace of `g ∘ₗ f`
onto the `μ`-eigenspace of `f ∘ₗ g`; the inverse is the restriction of `μ⁻¹ • g`. -/
noncomputable def eigenspaceCompEquiv (f : M →ₗ[R] N) (g : N →ₗ[R] M) {μ : R} (hμ : IsUnit μ) :
    eigenspace (g ∘ₗ f) μ ≃ₗ[R] eigenspace (f ∘ₗ g) μ :=
  LinearEquiv.ofLinearMap (f.restrict fun _ ↦ apply_mem_eigenspace_comp)
    (((↑hμ.unit⁻¹ : R) • g).restrict fun _ hy ↦ Submodule.smul_mem _ _ <|
      apply_mem_eigenspace_comp hy)
    (by
      ext ⟨y, hy⟩
      rw [mem_eigenspace_iff] at hy
      simpa [smul_smul] using congrArg ((↑hμ.unit⁻¹ : R) • ·) hy)
    (by
      ext ⟨x, hx⟩
      rw [mem_eigenspace_iff] at hx
      simpa [smul_smul] using congrArg ((↑hμ.unit⁻¹ : R) • ·) hx)

@[simp]
theorem coe_eigenspaceCompEquiv_apply (f : M →ₗ[R] N) (g : N →ₗ[R] M) {μ : R} (hμ : IsUnit μ)
    (x : eigenspace (g ∘ₗ f) μ) : (eigenspaceCompEquiv f g hμ x : N) = f x :=
  (rfl)

@[simp]
theorem coe_eigenspaceCompEquiv_symm_apply (f : M →ₗ[R] N) (g : N →ₗ[R] M) {μ : R}
    (hμ : IsUnit μ) (y : eigenspace (f ∘ₗ g) μ) :
    ((eigenspaceCompEquiv f g hμ).symm y : M) = (↑hμ.unit⁻¹ : R) • g y :=
  (rfl)

/-- At a unit `μ`, the `μ`-eigenspaces of `g ∘ₗ f` and `f ∘ₗ g` have the same dimension. -/
theorem finrank_eigenspace_comp_comm (f : M →ₗ[R] N) (g : N →ₗ[R] M) {μ : R} (hμ : IsUnit μ) :
    finrank R (eigenspace (g ∘ₗ f) μ) = finrank R (eigenspace (f ∘ₗ g) μ) :=
  (eigenspaceCompEquiv f g hμ).finrank_eq

end Module.End
