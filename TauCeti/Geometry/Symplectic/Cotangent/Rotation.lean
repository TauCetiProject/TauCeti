/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.CrossProduct
public import TauCeti.Geometry.Lie.Subgroup.Unitary.Orthogonal
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.MomentMap

/-!
# The moment map of cotangent-lifted rotations

Let `V` be a finite-dimensional real inner product space, such as `ℝⁿ = EuclideanSpace ℝ (Fin n)`.
Its orthogonal group `O(V) = unitary (V →L[ℝ] V)` is a Lie group
(`TauCeti.Geometry.Manifold.Instances.Unitary`) acting linearly on `V`, and the cotangent lift of
this action to `T*V` has the moment map `⟨μ(q, p), ξ⟩ = p(ξ_V(q))`
(`TauCeti.CotangentBundle.momentMap`). Through the identification of the Lie algebra of `O(V)`
with `so(V) = skewAdjointLieSubalgebra (innerₗ V)` (`TauCeti.orthogonalLieAlgebraEquiv`), it is
the restriction along `so(V) → gl(V)` of the moment map `A ↦ p(A q)` of the cotangent-lifted
linear action of `gl(V)` (`TauCeti.cotangentMomentMap`):
`TauCeti.CotangentBundle.momentMap_unitary_eq_cotangentMomentMap_comp`.

The rest of the file concerns the linear model on `ℝ³ = Fin 3 → ℝ` directly: the moment map
`A ↦ p(A q)` on `(Fin 3 → ℝ) × StrongDual ℝ (Fin 3 → ℝ)`, restricted along the matrix Lie algebra
`so (Fin 3) ℝ → gl(3)`. The hat map `ξ ↦ (v ↦ ξ ⨯₃ v)` identifies `ℝ³` with `so(3)`, and this
restricted moment map is the angular momentum: `p(ξ ⨯₃ q) = ξ ⬝ᵥ (q ⨯₃ p)` by the scalar triple
product, where the covector `p` is identified with a vector by the dot product
(`TauCeti.cotangentMomentMap_crossProduct`). As a functional on `so(3)` it is `ν_(q ⨯₃ p)` in the
identification `ℝ³ ≃ so(3)*` of `TauCeti.soThreeDualEquiv`
(`TauCeti.cotangentMomentMap_comp_eq_soThreeDualEquiv_cross`), and it is a moment map of the
cotangent-lifted infinitesimal rotations of `ℝ³ × (ℝ³)*`
(`TauCeti.isMomentMap_soThreeDualEquiv_cross`). The sign is that of the conventions
`d⟨μ, ξ⟩ = ι_(ξ_M) ω` and `ω = Σ dqᵢ ∧ dpᵢ`: the opposite pairing `q(ξ p)` would give `p ⨯₃ q`.
The comparison of these `ℝ³` statements with
`TauCeti.CotangentBundle.momentMap_unitary_eq_cotangentMomentMap_comp` for
`V = EuclideanSpace ℝ (Fin 3)` is not proved here.

## Main declarations

* `TauCeti.CotangentBundle.momentMap_unitary_eq_cotangentMomentMap_comp`: the moment map of the
  cotangent-lifted rotations is the restriction of the `gl(V)` moment map to `so(V)`.
* `TauCeti.cotangentMomentMap_crossProduct`,
  `TauCeti.cotangentMomentMap_comp_eq_soThreeDualEquiv_cross`,
  `TauCeti.isMomentMap_soThreeDualEquiv_cross`: on `ℝ³`, the `gl(3)` moment map restricted to
  `so(3)` is the angular momentum `q ⨯₃ p`.

## References

* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Sections 11.4 and 12.1 (the angular momentum as the momentum
  map of cotangent-lifted rotations).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 22.4.
-/

public section

noncomputable section

open Bundle Manifold
open scoped ContDiff Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

namespace TauCeti

section Orthogonal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- **The moment map of cotangent-lifted rotations.** The moment map of the cotangent lift to
`T*V` of the action of the orthogonal group `O(V)` on `V`, `⟨μ(q, p), ξ⟩ = p(ξ_V(q))`, is the
restriction of the moment map `A ↦ p(A q)` of `gl(V)` (`TauCeti.cotangentMomentMap`) along
`so(V) → gl(V)`, read through the identification of the Lie algebra of `O(V)` with `so(V)`. -/
theorem CotangentBundle.momentMap_unitary_eq_cotangentMomentMap_comp
    (z : CotangentBundle 𝓘(ℝ, V) V) :
    CotangentBundle.momentMap (Unitary.model (V →L[ℝ] V)) (unitary (V →L[ℝ] V)) z =
      ((cotangentMomentMap (z.proj, z.snd)).comp
        (skewAdjointLieSubalgebra (innerₗ V)).incl.toLinearMap).comp
          (orthogonalLieAlgebraEquiv V).toLinearMap := by
  ext ξ
  -- `O(V)` acts on `V` through the inclusion `Subtype.val : O(V) → V →L[ℝ] V`.
  rw [CotangentBundle.momentMap_apply_eq_cotangentMomentMap (ρ := Subtype.val) (fun _ _ ↦ rfl)
    (Unitary.contMDiff_val.mdifferentiableAt (by simp)), LinearMap.comp_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl,
    coe_orthogonalLieAlgebraEquiv_apply, OneMemClass.coe_one]

end Orthogonal

section SoThree

open LieAlgebra.Orthogonal Matrix

/-- **Angular momentum.** On the linear cotangent space of `ℝ³`, the moment map `A ↦ p(A q)` of
`gl(3)`, evaluated at the infinitesimal rotation `v ↦ ξ ⨯₃ v`, is `ξ ⬝ᵥ (q ⨯₃ p)`, where the
covector `p` is identified with a vector by the dot product. -/
theorem cotangentMomentMap_crossProduct (q ξ : Fin 3 → ℝ) (p : StrongDual ℝ (Fin 3 → ℝ)) :
    cotangentMomentMap (q, p) (crossProduct ξ) =
      ξ ⬝ᵥ q ⨯₃ (dotProductEquiv ℝ (Fin 3)).symm (p : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) := by
  have hp (w : Fin 3 → ℝ) :
      p w = (dotProductEquiv ℝ (Fin 3)).symm (p : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) ⬝ᵥ w :=
    (LinearMap.congr_fun ((dotProductEquiv ℝ (Fin 3)).apply_symm_apply _) w).symm
  rw [cotangentMomentMap_apply, hp, triple_product_permutation]

/-- **The rotation moment map of `T*ℝ³` is the angular momentum.** Restricted along
`so(3) → gl(3)`, the moment map `A ↦ p(A q)` of the cotangent-lifted linear action is the
functional `ν_(q ⨯₃ p) : û ↦ (q ⨯₃ p) ⬝ᵥ u` of `so(3)*` (`TauCeti.soThreeDualEquiv`), where the
covector `p` is identified with a vector by the dot product. -/
theorem cotangentMomentMap_comp_eq_soThreeDualEquiv_cross
    (x : (Fin 3 → ℝ) × StrongDual ℝ (Fin 3 → ℝ)) :
    (cotangentMomentMap x).comp
        ((lieEquivMatrix' (R := ℝ) (n := Fin 3)).symm.toLieHom.comp (so (Fin 3) ℝ).incl :
          so (Fin 3) ℝ →ₗ[ℝ] Module.End ℝ (Fin 3 → ℝ)) =
      soThreeDualEquiv ℝ (x.1 ⨯₃ (dotProductEquiv ℝ (Fin 3)).symm (x.2 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)) := by
  ext A
  obtain ⟨u, rfl⟩ := (soThreeEquiv ℝ).surjective A
  -- The matrix `û` acts on `ℝ³` as `v ↦ u ⨯₃ v`.
  have hu : (lieEquivMatrix' (R := ℝ) (n := Fin 3)).symm (crossProductMatrix ℝ u) =
      crossProduct u :=
    LinearMap.ext fun v ↦ by
      rw [lieEquivMatrix'_symm_apply, toLin'_apply, crossProductMatrix_mulVec]
  simp only [LinearMap.comp_apply, LieHom.coe_toLinearMap, LieHom.comp_apply,
    LieSubalgebra.coe_incl, coe_soThreeEquiv, LieEquiv.coe_toLieHom, hu]
  rw [cotangentMomentMap_crossProduct, soThreeDualEquiv_apply_soThreeEquiv, dotProduct_comm]

/-- **Angular momentum is a moment map.** On the linear cotangent space `ℝ³ × (ℝ³)*`, the angular
momentum `(q, p) ↦ ν_(q ⨯₃ p) ∈ so(3)*` is a moment map of the cotangent-lifted infinitesimal
rotations `(q, p) ↦ (A q, -(p ∘ A))`, `A ∈ so(3)`. -/
theorem isMomentMap_soThreeDualEquiv_cross :
    (strongDualCotangentSymplecticForm (V := Fin 3 → ℝ)).constSmooth.IsMomentMap
      ((InfinitesimalAction.cotangentLinear (Fin 3 → ℝ)).comp
        ((lieEquivMatrix' (R := ℝ) (n := Fin 3)).symm.toLieHom.comp (so (Fin 3) ℝ).incl))
      fun x ↦ soThreeDualEquiv ℝ
        (x.1 ⨯₃ (dotProductEquiv ℝ (Fin 3)).symm (x.2 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)) := by
  simpa only [cotangentMomentMap_comp_eq_soThreeDualEquiv_cross] using
    (isMomentMap_cotangentMomentMap (V := Fin 3 → ℝ)).comp
      ((lieEquivMatrix' (R := ℝ) (n := Fin 3)).symm.toLieHom.comp (so (Fin 3) ℝ).incl)

end SoThree

end TauCeti
