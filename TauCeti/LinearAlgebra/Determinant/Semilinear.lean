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
# Determinants under conjugation by conjugate-linear isomorphisms

Conjugating a linear endomorphism `A` of a module `M` over a commutative star ring by
a linear isomorphism `M ≃ N` leaves its determinant unchanged (`LinearMap.det_conj`). Conjugating
it instead by a conjugate-linear isomorphism `K : M ≃ N`, the composite `K ∘ A ∘ K⁻¹` is again
linear, and its determinant is the conjugate `star (det A)` (`LinearMap.det_conjₛₗ`). Over `ℂ`, a
complex vector space with a real structure, such as the complexification of a real vector space,
is the leading example: there `K` is the conjugation fixing the real points.

The proof writes `K` as the linear isomorphism `K ∘ K₀⁻¹`, whose conjugation is handled by
`LinearMap.det_conj`, composed with the coordinatewise conjugation `K₀` of a basis of `M`.
Conjugating by `K₀` conjugates every matrix entry, and the determinant of the conjugated matrix
is the conjugate of the determinant (`RingHom.map_det`).
-/

public section

namespace LinearMap

variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]

/-- **Conjugation by a conjugate-linear isomorphism.** For a conjugate-linear isomorphism
`K : M ≃ N`, the determinant of the linear map `K ∘ A ∘ K⁻¹` is the conjugate of the determinant
of `A`. -/
@[simp]
theorem det_conjₛₗ {N : Type*} [AddCommGroup N] [Module R N] (A : M →ₗ[R] M)
    (K : M ≃ₗ⋆[R] N) :
    LinearMap.det ((K : M →ₗ⋆[R] N) ∘ₛₗ A ∘ₛₗ (K.symm : N →ₗ⋆[R] M)) =
      star (LinearMap.det A) := by
  classical
  by_cases H : ∃ s : Finset M, Nonempty (Module.Basis s R M)
  swap
  · have H' : ¬∃ t : Finset N, Nonempty (Module.Basis t R N) := by
      rintro ⟨t, ⟨c⟩⟩
      exact H ⟨_, ⟨(Module.Basis.ofEquivFun
        ((K.trans c.equivFun).trans (starLinearEquiv R))).reindexFinsetRange⟩⟩
    simp [LinearMap.coe_det, H, H']
  obtain ⟨s, ⟨b⟩⟩ := H
  -- Coordinatewise conjugation in the basis `b`, and the linear part `K ∘ K₀⁻¹` of `K`.
  let K₀ : M ≃ₗ⋆[R] M := (b.equivFun.trans (starLinearEquiv R)).trans b.equivFun.symm
  let L : M ≃ₗ[R] N := K₀.symm.trans K
  have hrepr (v : M) (i) : b.repr (K₀ v) i = star (b.repr v i) := by
    simp [K₀, Module.Basis.equivFun_symm_apply, Finsupp.single_apply]
  have hb (j) : K₀.symm (b j) = b j := by
    apply K₀.injective
    simp only [LinearEquiv.apply_symm_apply]
    refine b.ext_elem fun i ↦ ?_
    rw [hrepr]
    by_cases h : j = i <;> simp [h]
  have hsplit : (K : M →ₗ⋆[R] N) ∘ₛₗ A ∘ₛₗ (K.symm : N →ₗ⋆[R] M) =
      (L : M →ₗ[R] N) ∘ₗ ((K₀ : M →ₗ⋆[R] M) ∘ₛₗ A ∘ₛₗ (K₀.symm : M →ₗ⋆[R] M)) ∘ₗ
        (L.symm : N →ₗ[R] M) := by
    ext v
    simp [L]
  have hmat : LinearMap.toMatrix b b
      ((K₀ : M →ₗ⋆[R] M) ∘ₛₗ A ∘ₛₗ (K₀.symm : M →ₗ⋆[R] M)) =
        (LinearMap.toMatrix b b A).map star := by
    ext i j
    simp only [LinearMap.toMatrix_apply, Matrix.map_apply]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, hb,
      hrepr]
  rw [hsplit, LinearMap.det_conj, ← LinearMap.det_toMatrix b, hmat, ← LinearMap.det_toMatrix b A,
    ← starRingEnd_apply]
  exact ((starRingEnd R).map_det _).symm

end LinearMap
