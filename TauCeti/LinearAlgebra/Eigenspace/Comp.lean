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
* `LinearMap.apply_apply_add_smul_eq_inv_sq_smul`: a vector `x₁ + μ • x₂` on which two linear
  maps act dihedrally with parameter `μ + μ⁻¹` is an eigenvector of their composite for `(μ ^ 2)⁻¹`.

## References

* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Theorem 1.3.22.
-/

public section

namespace Module.End

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- For a unit `μ`, `f` restricts to a linear equivalence from the `μ`-eigenspace of `g ∘ₗ f`
onto the `μ`-eigenspace of `f ∘ₗ g`; the inverse is the restriction of `μ⁻¹ • g`. -/
noncomputable def eigenspaceCompEquiv {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) {μ : R} (hμ : IsUnit μ) :
    eigenspace (g ∘ₗ f) μ ≃ₗ[R] eigenspace (f ∘ₗ g) μ :=
  LinearEquiv.ofLinearMap
    (f.restrict fun _ hx ↦ mapsTo_genEigenspace_of_comp f (LinearMap.comp_assoc f g f) μ 1 hx)
    (((↑hμ.unit⁻¹ : R) • g).restrict fun _ hy ↦ Submodule.smul_mem _ _ <|
      mapsTo_genEigenspace_of_comp g (LinearMap.comp_assoc g f g) μ 1 hy)
    (by
      ext ⟨y, hy⟩
      rw [mem_eigenspace_iff, LinearMap.comp_apply] at hy
      simp [hy, smul_smul])
    (by
      ext ⟨x, hx⟩
      rw [mem_eigenspace_iff, LinearMap.comp_apply] at hx
      simp [hx, smul_smul])

@[simp]
theorem coe_eigenspaceCompEquiv_apply {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) {μ : R} (hμ : IsUnit μ)
    (x : eigenspace (g ∘ₗ f) μ) : (eigenspaceCompEquiv f g hμ x : N) = f x :=
  (rfl)

@[simp]
theorem coe_eigenspaceCompEquiv_symm_apply {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) {μ : R} (hμ : IsUnit μ) (y : eigenspace (f ∘ₗ g) μ) :
    ((eigenspaceCompEquiv f g hμ).symm y : M) = (↑hμ.unit⁻¹ : R) • g y :=
  (rfl)

/-- At a unit `μ`, the `μ`-eigenspaces of `g ∘ₗ f` and `f ∘ₗ g` have the same dimension. -/
theorem finrank_eigenspace_comp_comm {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (g : N →ₗ[R] M) {μ : R} (hμ : IsUnit μ) :
    finrank R (eigenspace (g ∘ₗ f) μ) = finrank R (eigenspace (f ∘ₗ g) μ) :=
  (eigenspaceCompEquiv f g hμ).finrank_eq

end Module.End

namespace LinearMap

/-- **Dihedral eigenvector identity.** If two linear endomorphisms `f₁, f₂` negate `x₁, x₂`
respectively and satisfy `f₁ x₂ = x₂ + (μ + μ⁻¹) • x₁` and `f₂ x₁ = x₁ + (μ + μ⁻¹) • x₂` for a
nonzero scalar `μ`, then `x₁ + μ • x₂` is an eigenvector of `f₁ ∘ₗ f₂` with eigenvalue `(μ ^ 2)⁻¹`.
-/
theorem apply_apply_add_smul_eq_inv_sq_smul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (f₁ f₂ : V →ₗ[K] V) {x₁ x₂ : V} {μ : K} (hμ : μ ≠ 0)
    (hf₁₁ : f₁ x₁ = -x₁) (hf₁₂ : f₁ x₂ = x₂ + (μ + μ⁻¹) • x₁)
    (hf₂₂ : f₂ x₂ = -x₂) (hf₂₁ : f₂ x₁ = x₁ + (μ + μ⁻¹) • x₂) :
    f₁ (f₂ (x₁ + μ • x₂)) = (μ ^ 2)⁻¹ • (x₁ + μ • x₂) := by
  have h2 : f₂ (x₁ + μ • x₂) = x₁ + μ⁻¹ • x₂ := by
    rw [map_add, map_smul, hf₂₁, hf₂₂, add_smul, smul_neg]
    abel
  calc f₁ (f₂ (x₁ + μ • x₂))
      = -x₁ + μ⁻¹ • (x₂ + (μ + μ⁻¹) • x₁) := by
          rw [h2, map_add, map_smul, hf₁₁, hf₁₂]
    _ = (μ ^ 2)⁻¹ • (x₁ + μ • x₂) := by
        rw [smul_add, add_smul, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hμ, one_smul,
          ← mul_inv, ← sq, smul_add, smul_smul,
          show (μ ^ 2)⁻¹ * μ = μ⁻¹ by field_simp [hμ]]
        abel

end LinearMap
