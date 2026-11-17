/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.Star.Module
public import Mathlib.Algebra.Star.Pi

/-!
# Determinants under conjugation by conjugate-linear automorphisms

Conjugating a linear endomorphism `A` of a module `M` over a commutative star ring by
a linear automorphism leaves its determinant unchanged (`LinearMap.det_conj`). Conjugating it
instead by a conjugate-linear automorphism `K`, the composite `K ∘ A ∘ K⁻¹` is again linear, and
its determinant is the conjugate `star (det A)` (`LinearMap.det_conjₛₗ`). Over `ℂ`, a complex vector
space with a real structure, such as the complexification of a real vector space, is the leading
example: there `K` is the conjugation fixing the real points.

The proof writes `K` as the coordinatewise conjugation `K₀` of a basis composed with the linear
automorphism `K₀⁻¹ ∘ K`, whose conjugation is handled by `LinearMap.det_conj`. Conjugating by
`K₀` conjugates every matrix entry, and the determinant of the conjugated matrix is the conjugate
of the determinant (`RingHom.map_det`).
-/

public section

namespace LinearMap

variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]

/-- **Conjugation by a conjugate-linear automorphism.** For a conjugate-linear automorphism `K`
of `M`, the determinant of the linear map `K ∘ A ∘ K⁻¹` is the conjugate of the determinant of
`A`. -/
@[simp]
theorem det_conjₛₗ (A : M →ₗ[R] M) (K : M ≃ₗ⋆[R] M) :
    LinearMap.det ((K : M →ₗ⋆[R] M) ∘ₛₗ A ∘ₛₗ (K.symm : M →ₗ⋆[R] M)) =
      star (LinearMap.det A) := by
  classical
  by_cases H : ∃ s : Finset M, Nonempty (Module.Basis s R M)
  swap
  · simp [LinearMap.coe_det, H]
  obtain ⟨s, ⟨b⟩⟩ := H
  -- Coordinatewise conjugation in the basis `b`, and the linear part `K₀⁻¹ ∘ K` of `K`.
  let K₀ : M ≃ₗ⋆[R] M := (b.equivFun.trans (starLinearEquiv R)).trans b.equivFun.symm
  let L : M ≃ₗ[R] M := K.trans K₀.symm
  have hrepr (v : M) (i) : b.repr (K₀ v) i = star (b.repr v i) := by
    simp [K₀, Module.Basis.equivFun_symm_apply, Finsupp.single_apply]
  have hb (j) : K₀.symm (b j) = b j := by
    apply K₀.injective
    simp only [LinearEquiv.apply_symm_apply]
    refine b.ext_elem fun i ↦ ?_
    rw [hrepr]
    by_cases h : j = i <;> simp [h]
  have hsplit : (K : M →ₗ⋆[R] M) ∘ₛₗ A ∘ₛₗ (K.symm : M →ₗ⋆[R] M) =
      (K₀ : M →ₗ⋆[R] M) ∘ₛₗ ((L : M →ₗ[R] M) ∘ₗ A ∘ₗ (L.symm : M →ₗ[R] M)) ∘ₛₗ
        (K₀.symm : M →ₗ⋆[R] M) := by
    ext v
    simp [L]
  have hmat : LinearMap.toMatrix b b ((K₀ : M →ₗ⋆[R] M) ∘ₛₗ
      ((L : M →ₗ[R] M) ∘ₗ A ∘ₗ (L.symm : M →ₗ[R] M)) ∘ₛₗ (K₀.symm : M →ₗ⋆[R] M)) =
        (LinearMap.toMatrix b b ((L : M →ₗ[R] M) ∘ₗ A ∘ₗ (L.symm : M →ₗ[R] M))).map star := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Matrix.map_apply]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, hb,
      hrepr]
  rw [hsplit, ← LinearMap.det_toMatrix b, hmat]
  refine ((starRingEnd R).map_det _).symm.trans ?_
  rw [LinearMap.det_toMatrix, LinearMap.det_conj, starRingEnd_apply]

end LinearMap
