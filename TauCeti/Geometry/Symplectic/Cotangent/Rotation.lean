/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.CrossProduct
public import TauCeti.Geometry.Symplectic.Cotangent.Bundle.LinearAction

/-!
# Moment maps of cotangent-lifted rotations and angular momentum

The rotations of `ℝⁿ` form the orthogonal Lie algebra `so(n)` of skew-symmetric matrices
(`LieAlgebra.Orthogonal.so`), acting on `ℝⁿ = n → ℝ` by `v ↦ A v`: the restriction to `so(n)` of
the Lie module of square matrices on `n → ℝ`, `LieModule.toEnd ℝ (so n ℝ) (n → ℝ)`. Their
cotangent lift acts on the linear cotangent space `ℝⁿ × (ℝⁿ)*` by `(q, p) ↦ (A q, -(p ∘ A))`, and
its moment map is

`⟨μ(q, p), A⟩ = p(A q)` (`TauCeti.rotationMomentMap`),

the restriction along `so(n) → gl(n)` of the moment map `TauCeti.cotangentMomentMap` of the
cotangent-lifted action of all of `gl(n)` (`TauCeti.rotationMomentMap_eq_comp`). Hence:

* `μ` is a moment map of the cotangent-lifted rotation action for the canonical form
  `ω = Σ dqᵢ ∧ dpᵢ` (`TauCeti.isMomentMap_rotationMomentMap`);
* it is infinitesimally equivariant, `{μ_A, μ_B} = μ_⁅A, B⁆`
  (`TauCeti.poissonBracket_rotationMomentMap`).

The same pairing `p(ξ_V q)` is the moment map `TauCeti.CotangentBundle.momentMap` of the cotangent
lift to the manifold `T*V` of any smooth linear action of a Lie group on a finite-dimensional
normed space `V`: in the global coordinates `T*V ≃ V × V*`
(`TauCeti.CotangentBundle.modelSpaceDiffeomorph`) it is `cotangentMomentMap` restricted along the
differential at the identity of the representation
(`TauCeti.CotangentBundle.momentMap_eq_cotangentMomentMap_comp_fundamentalLinearMap`). So for a
Lie group acting linearly on `ℝⁿ` whose infinitesimal action is by rotations, the intrinsic moment
map of the cotangent bundle `T*ℝⁿ` is the rotation moment map above
(`TauCeti.CotangentBundle.momentMap_eq_rotationMomentMap_comp`).

In dimension three, the hat map `ξ ↦ ξ̂ = (v ↦ ξ ⨯₃ v)` identifies `ℝ³` with `so(3)`
(`TauCeti.soThreeEquiv`) and the dot product identifies `ℝ³` with `so(3)*`
(`TauCeti.soThreeDualEquiv`). Through these, the rotation moment map is the **angular momentum**
`q ⨯₃ p` (`TauCeti.cotangentAngularMomentum`,
`TauCeti.rotationMomentMap_eq_soThreeDualEquiv_cotangentAngularMomentum`), where the covector `p`
is read as a vector by the dot product: by the scalar triple product,
`p(ξ ⨯₃ q) = ξ ⬝ᵥ (q ⨯₃ p)` (`TauCeti.rotationMomentMap_soThreeEquiv`). The equivariance of the
rotation moment map becomes the Poisson relations of angular momentum,
`{ξ ⬝ᵥ L, η ⬝ᵥ L} = (ξ ⨯₃ η) ⬝ᵥ L`
(`TauCeti.poissonBracket_dotProduct_cotangentAngularMomentum`).

## Main definitions

* `TauCeti.rotationMomentMap`: the moment map `⟨μ(q, p), A⟩ = p(A q)` of the cotangent-lifted
  rotations.
* `TauCeti.cotangentAngularMomentum`: the angular momentum `q ⨯₃ p` of a point of `ℝ³ × (ℝ³)*`.

## Main results

* `TauCeti.rotationMomentMap_eq_comp`: the rotation moment map is the restriction of the cotangent
  moment map of `gl(n)` along `so(n) → gl(n)`.
* `TauCeti.isMomentMap_rotationMomentMap`, `TauCeti.poissonBracket_rotationMomentMap`: it is an
  infinitesimally equivariant moment map of the cotangent-lifted rotation action.
* `TauCeti.CotangentBundle.momentMap_eq_rotationMomentMap_comp`: for a linear Lie group action on
  `ℝⁿ` whose infinitesimal action is by rotations, the moment map of the cotangent bundle `T*ℝⁿ` is
  the rotation moment map.
* `TauCeti.rotationMomentMap_eq_soThreeDualEquiv_cotangentAngularMomentum`: in dimension three the
  moment map is the angular momentum `q ⨯₃ p`.
* `TauCeti.poissonBracket_dotProduct_cotangentAngularMomentum`: `{ξ ⬝ᵥ L, η ⬝ᵥ L} = (ξ ⨯₃ η) ⬝ᵥ L`.

## References

* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Sections 11.4 and 12.1 (angular momentum as the momentum map of
  cotangent-lifted rotations).
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 22.4.
-/

public section

noncomputable section

open Matrix LieAlgebra.Orthogonal
open scoped Manifold

namespace TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ### The moment map of the cotangent-lifted rotations -/

section MomentMap

variable {n : Type*} [Fintype n] [DecidableEq n]

variable (n) in
/-- The **moment map of the cotangent-lifted rotations** of `ℝⁿ`: at `(q, p) ∈ ℝⁿ × (ℝⁿ)*` it is
the linear form `A ↦ p(A q)` on `so(n)`. -/
def rotationMomentMap (x : (n → ℝ) × StrongDual ℝ (n → ℝ)) : Module.Dual ℝ (so n ℝ) :=
  (cotangentMomentMap x).comp (LieModule.toEnd ℝ (so n ℝ) (n → ℝ)).toLinearMap

/-- The rotation moment map pairs `p` with the generated vector `A q`: `⟨μ(q, p), A⟩ = p(A q)`. -/
@[simp]
theorem rotationMomentMap_apply (x : (n → ℝ) × StrongDual ℝ (n → ℝ)) (A : so n ℝ) :
    rotationMomentMap n x A = x.2 ((A : Matrix n n ℝ) *ᵥ x.1) := by
  simp [rotationMomentMap, LieSubalgebra.coe_bracket_of_module]

/-- The rotation moment map is the restriction of the moment map of the cotangent-lifted action of
`gl(n)` along `so(n) → gl(n)`. -/
theorem rotationMomentMap_eq_comp (x : (n → ℝ) × StrongDual ℝ (n → ℝ)) :
    rotationMomentMap n x =
      (cotangentMomentMap x).comp (LieModule.toEnd ℝ (so n ℝ) (n → ℝ)).toLinearMap :=
  (rfl)

/-- **The moment map of the cotangent-lifted rotations.** On `ℝⁿ × (ℝⁿ)*` with the canonical form
`ω = Σ dqᵢ ∧ dpᵢ`, `⟨μ(q, p), A⟩ = p(A q)` is a moment map of the action of `so(n)` by the
cotangent-lifted vector fields `(q, p) ↦ (A q, -(p ∘ A))`. -/
theorem isMomentMap_rotationMomentMap :
    (strongDualCotangentSymplecticForm (V := n → ℝ)).constSmooth.IsMomentMap
      ((InfinitesimalAction.cotangentLinear (n → ℝ)).comp (LieModule.toEnd ℝ (so n ℝ) (n → ℝ)))
      (rotationMomentMap n) :=
  isMomentMap_cotangentMomentMap.comp (LieModule.toEnd ℝ (so n ℝ) (n → ℝ))

/-- **The rotation moment map is infinitesimally equivariant**: `{μ_A, μ_B} = μ_⁅A, B⁆`. -/
theorem poissonBracket_rotationMomentMap (A B : so n ℝ) (x : (n → ℝ) × StrongDual ℝ (n → ℝ)) :
    (strongDualCotangentSymplecticForm (V := n → ℝ)).constSmooth.poissonBracket
      (fun y ↦ rotationMomentMap n y A) (fun y ↦ rotationMomentMap n y B) x =
      rotationMomentMap n x ⁅A, B⁆ := by
  simp only [rotationMomentMap_eq_comp, LinearMap.comp_apply, LieHom.coe_toLinearMap,
    poissonBracket_cotangentMomentMap, LieHom.map_lie]

end MomentMap

/-! ### Comparison with the moment map of the cotangent bundle -/

namespace CotangentBundle

variable {EG HG : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG] [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG} {G : Type*} [TopologicalSpace G] [ChartedSpace HG G] [Group G]

/-- **The cotangent moment map of a rotation action is the rotation moment map.** If a Lie group
`G` acts linearly on `ℝⁿ` and its infinitesimal action is by rotations, `ξ_V = ψ(ξ)` for a linear
map `ψ : 𝔤 → so(n)`, then the moment map of the cotangent-lifted action on `T*ℝⁿ` is, in the
global coordinates `T*ℝⁿ ≃ ℝⁿ × (ℝⁿ)*`, the rotation moment map restricted along `ψ`. -/
theorem momentMap_eq_rotationMomentMap_comp {n : Type*} [Fintype n] [DecidableEq n]
    [DistribMulAction G (n → ℝ)] [SMulCommClass G ℝ (n → ℝ)]
    [ContMDiffSMul IG 𝓘(ℝ, n → ℝ) 1 G (n → ℝ)]
    {ψ : GroupLieAlgebra IG G →ₗ[ℝ] so n ℝ}
    (hψ : ∀ ξ, fundamentalLinearMap IG G (n → ℝ) ξ = LieModule.toEnd ℝ (so n ℝ) (n → ℝ) (ψ ξ))
    (z : CotangentBundle 𝓘(ℝ, n → ℝ) (n → ℝ)) :
    momentMap IG G z = (rotationMomentMap n (modelSpaceDiffeomorph (n → ℝ) z)).comp ψ := by
  ext ξ
  simp only [momentMap_eq_cotangentMomentMap_comp_fundamentalLinearMap, rotationMomentMap_eq_comp,
    LinearMap.comp_apply, hψ, LieHom.coe_toLinearMap]

end CotangentBundle

/-! ### Angular momentum in dimension three -/

section AngularMomentum

/-- The **angular momentum** `q ⨯₃ p` of a point `(q, p)` of `ℝ³ × (ℝ³)*`, where the covector `p`
is read as the vector `(p e₀, p e₁, p e₂)` of its values on the standard basis. -/
def cotangentAngularMomentum (x : (Fin 3 → ℝ) × StrongDual ℝ (Fin 3 → ℝ)) : Fin 3 → ℝ :=
  x.1 ⨯₃ (dotProductEquiv ℝ (Fin 3)).symm (x.2 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ)

/-- The angular momentum is `q ⨯₃ p`, with `p` read as the vector of its values on the standard
basis. -/
theorem cotangentAngularMomentum_apply (x : (Fin 3 → ℝ) × StrongDual ℝ (Fin 3 → ℝ)) :
    cotangentAngularMomentum x = x.1 ⨯₃ fun i ↦ x.2 (Pi.single i 1) := by
  rw [cotangentAngularMomentum]
  refine congrArg (x.1 ⨯₃ ·) (funext fun i ↦ ?_)
  rw [dotProductEquiv_symm_apply, LinearMap.coe_single, ContinuousLinearMap.coe_coe]

/-- **The lifted rotation moment map is the angular momentum.** For the rotation `ξ̂ = (v ↦ ξ ⨯₃ v)`
of `ℝ³`, `⟨μ(q, p), ξ̂⟩ = p(ξ ⨯₃ q) = ξ ⬝ᵥ (q ⨯₃ p)`, by the scalar triple product. -/
theorem rotationMomentMap_soThreeEquiv (x : (Fin 3 → ℝ) × StrongDual ℝ (Fin 3 → ℝ))
    (ξ : Fin 3 → ℝ) :
    rotationMomentMap (Fin 3) x (soThreeEquiv ℝ ξ) = ξ ⬝ᵥ cotangentAngularMomentum x := by
  -- The covector `p` is the dot product with the vector of its values on the standard basis.
  have hp (v : Fin 3 → ℝ) :
      x.2 v = (dotProductEquiv ℝ (Fin 3)).symm (x.2 : (Fin 3 → ℝ) →ₗ[ℝ] ℝ) ⬝ᵥ v := by
    rw [← dotProductEquiv_apply_apply, LinearEquiv.apply_symm_apply, ContinuousLinearMap.coe_coe]
  simp only [rotationMomentMap_apply, coe_soThreeEquiv, crossProductMatrix_mulVec, hp,
    cotangentAngularMomentum]
  exact triple_product_permutation _ _ _

/-- **The moment map of the cotangent-lifted rotations of `ℝ³` is the angular momentum.** Under the
identification of `ℝ³` with `so(3)*` by the dot product and the hat map, `μ(q, p) = q ⨯₃ p`. -/
theorem rotationMomentMap_eq_soThreeDualEquiv_cotangentAngularMomentum
    (x : (Fin 3 → ℝ) × StrongDual ℝ (Fin 3 → ℝ)) :
    rotationMomentMap (Fin 3) x = soThreeDualEquiv ℝ (cotangentAngularMomentum x) := by
  refine LinearMap.ext fun A ↦ ?_
  obtain ⟨ξ, rfl⟩ := (soThreeEquiv ℝ).surjective A
  rw [rotationMomentMap_soThreeEquiv, soThreeDualEquiv_apply_soThreeEquiv, dotProduct_comm]

/-- **The Poisson brackets of angular momentum.** The components `ξ ⬝ᵥ L` of the angular momentum
`L = q ⨯₃ p` close under the Poisson bracket of `ℝ³ × (ℝ³)*` into the cross product:
`{ξ ⬝ᵥ L, η ⬝ᵥ L} = (ξ ⨯₃ η) ⬝ᵥ L`. -/
theorem poissonBracket_dotProduct_cotangentAngularMomentum (ξ η : Fin 3 → ℝ)
    (x : (Fin 3 → ℝ) × StrongDual ℝ (Fin 3 → ℝ)) :
    (strongDualCotangentSymplecticForm (V := Fin 3 → ℝ)).constSmooth.poissonBracket
      (fun y ↦ ξ ⬝ᵥ cotangentAngularMomentum y) (fun y ↦ η ⬝ᵥ cotangentAngularMomentum y) x =
      (ξ ⨯₃ η) ⬝ᵥ cotangentAngularMomentum x := by
  simp only [← rotationMomentMap_soThreeEquiv, poissonBracket_rotationMomentMap, lie_soThreeEquiv]

end AngularMomentum

end TauCeti
