/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Liouville
public import TauCeti.Geometry.Symplectic.Cotangent.StrongDual
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap

/-!
# Moment maps of cotangent-lifted linear actions

A linear map `A` of a real normed space `V` acts on the linear cotangent space
`V × StrongDual ℝ V`, with its canonical symplectic form
`ω((q, p), (q', p')) = p'(q) - p(q')`, by the cotangent lift of `A`. Its **moment map** is

`⟨μ(q, p), A⟩ = p(A q)` (`TauCeti.cotangentMomentMap`),

the pairing of the covector `p` with the vector `A q` generated at the base point `q`. This file
proves the moment map identities at the level of the linear group `GL(V)` and of its Lie algebra.

For a continuous linear equivalence `g : V ≃L[ℝ] W`, the cotangent lift
`(q, p) ↦ (g q, p ∘ g⁻¹)` (`ContinuousLinearEquiv.cotangent`) is a symplectomorphism preserving
the Liouville forms. The moment map is coadjoint equivariant along it:
`μ(g · x)(A) = μ(x)(g⁻¹ A g)` (`ContinuousLinearEquiv.cotangentMomentMap_cotangent`).

For finite-dimensional `V`, the infinitesimal cotangent lift `(q, p) ↦ (A q, -(p ∘ A))` is a Lie
algebra homomorphism from `Module.End ℝ V` to the endomorphisms of `V × StrongDual ℝ V`
(`TauCeti.cotangentLiftLieHom`). It defines an infinitesimal action of `gl(V)` by linear vector
fields (`TauCeti.InfinitesimalAction.cotangentLinear`). Then:

* the infinitesimal cotangent lift takes values in `sp(V × StrongDual ℝ V)`
  (`TauCeti.cotangentLiftLieHom_mem_skewAdjointLieSubalgebra`), giving a Lie algebra
  homomorphism into it (`TauCeti.cotangentLiftSpLieHom`), and `μ_A(x) = ½ ω(A_{T*V} x, x)` is the
  linear symplectic moment map along it (`TauCeti.cotangentMomentMap_apply_eq_linearMomentMap`);
* `μ` is a moment map of this action (`TauCeti.isMomentMap_cotangentMomentMap`), and it is the
  contraction of the Liouville form with the generating vector fields,
  `⟨μ, A⟩ = λ(A_{T*V})` (`TauCeti.cotangentLiouvilleForm_cotangentLiftLieHom`);
* `μ` is infinitesimally equivariant, `{μ_A, μ_B} = μ_{⁅A, B⁆}`
  (`TauCeti.poissonBracket_cotangentMomentMap`);
* the cotangent lift of `g` carries the generating field of `A` to that of `g A g⁻¹`
  (`ContinuousLinearEquiv.cotangent_cotangentLiftLieHom`).

Restricting along a Lie algebra homomorphism `ρ : 𝔤 → gl(V)` with
`TauCeti.SmoothTwoForm.IsMomentMap.comp` gives the moment map `⟨μ(q, p), Z⟩ = p(ρ(Z) q)` of the
cotangent lift of any linear representation. For the rotations `𝔤 = so(V)` of a Euclidean space
this is the angular momentum.

## Main declarations

* `TauCeti.cotangentMomentMap`: the moment map `⟨μ(q, p), A⟩ = p(A q)`.
* `TauCeti.cotangentLiftLieHom`: the infinitesimal cotangent lift `(q, p) ↦ (A q, -(p ∘ A))`.
* `TauCeti.cotangentLiftSpLieHom`: the infinitesimal cotangent lift as a Lie algebra homomorphism
  into `sp(V × StrongDual ℝ V)`.
* `TauCeti.InfinitesimalAction.cotangentLinear`: the cotangent-lifted linear action of `gl(V)`.
* `TauCeti.isMomentMap_cotangentMomentMap`: `μ` is a moment map of this action.

## References

* J. E. Marsden, T. S. Ratiu, *Introduction to Mechanics and Symmetry*, 2nd ed., Texts in Applied
  Mathematics 17, Springer, 1999, Section 12.1 (momentum maps of cotangent lifts).
* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The **moment map of the cotangent-lifted linear action**: at a point `(q, p)` of the linear
cotangent space `V × StrongDual ℝ V`, the linear form `A ↦ p(A q)` on the endomorphisms of `V`. -/
def cotangentMomentMap (x : V × StrongDual ℝ V) : Module.Dual ℝ (Module.End ℝ V) :=
  (x.2 : V →ₗ[ℝ] ℝ) ∘ₗ LinearMap.applyₗ x.1

@[simp]
theorem cotangentMomentMap_apply (x : V × StrongDual ℝ V) (A : Module.End ℝ V) :
    cotangentMomentMap x A = x.2 (A x.1) :=
  (rfl)

end TauCeti

namespace ContinuousLinearEquiv

open TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

/-- **Coadjoint equivariance of the cotangent moment map.** For a continuous linear equivalence
`g : V ≃L[ℝ] W`, `μ(g · x)(A) = μ(x)(g⁻¹ A g)`. For `W = V` this says `μ(g · x) = Ad*_g μ(x)` for
the adjoint action `Ad_g A = g A g⁻¹` of `GL(V)` on `gl(V)`. -/
theorem cotangentMomentMap_cotangent (g : V ≃L[ℝ] W) (x : V × StrongDual ℝ V)
    (A : Module.End ℝ W) :
    cotangentMomentMap (g.cotangent x) A = cotangentMomentMap x (g.toLinearEquiv.symm.conj A) := by
  simp [LinearEquiv.conj_apply]

end ContinuousLinearEquiv

namespace TauCeti

section FiniteDimensional

attribute [local instance 100] LieRing.ofAssociativeRing

variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- The **infinitesimal cotangent lift** `(q, p) ↦ (A q, -(p ∘ A))` of an endomorphism `A` of a
finite-dimensional space `V`, as a Lie algebra homomorphism from `gl(V)` to the endomorphisms of
the linear cotangent space `V × StrongDual ℝ V`. -/
def cotangentLiftLieHom : Module.End ℝ V →ₗ⁅ℝ⁆ Module.End ℝ (V × StrongDual ℝ V) where
  toFun A := A.prodMap
    (-(ContinuousLinearMap.precomp ℝ (LinearMap.toContinuousLinearMap A)).toLinearMap)
  map_add' A B := LinearMap.ext fun x ↦ Prod.ext rfl <| ContinuousLinearMap.ext fun v ↦ by
    simp only [LinearMap.add_apply]
    simp
    ring
  map_smul' c A := LinearMap.ext fun x ↦ Prod.ext rfl <| ContinuousLinearMap.ext fun v ↦ by
    simp
  map_lie' {A B} := LinearMap.ext fun x ↦ Prod.ext rfl <| ContinuousLinearMap.ext fun v ↦ by
    simp only [LieRing.of_associative_ring_bracket]
    simp

variable {V}

@[simp]
theorem cotangentLiftLieHom_apply_fst (A : Module.End ℝ V) (x : V × StrongDual ℝ V) :
    (cotangentLiftLieHom V A x).1 = A x.1 :=
  (rfl)

@[simp]
theorem cotangentLiftLieHom_apply_snd_apply (A : Module.End ℝ V) (x : V × StrongDual ℝ V)
    (v : V) : (cotangentLiftLieHom V A x).2 v = -x.2 (A v) :=
  (rfl)

/-- The infinitesimal cotangent lift of an endomorphism is skew-adjoint for the canonical
symplectic form: it lies in `sp(V × StrongDual ℝ V)`. -/
theorem cotangentLiftLieHom_mem_skewAdjointLieSubalgebra (A : Module.End ℝ V) :
    cotangentLiftLieHom V A ∈
      skewAdjointLieSubalgebra (strongDualCotangentSymplecticForm (V := V)).toBilinForm := by
  -- `skewAdjointLieSubalgebra B` is defined as `B.skewAdjointSubmodule` with a bracket-closure
  -- proof attached, so membership in it is definitionally membership in that submodule. Mathlib
  -- has no rewrite lemma for this, so cross the wrapper to use `mem_skewAdjointSubmodule`.
  change _ ∈ LinearMap.skewAdjointSubmodule _
  rw [LinearMap.mem_skewAdjointSubmodule]
  intro x y
  simp

/-- The cotangent moment map is the contraction of the Liouville form with the generating vector
fields of the cotangent lift: `⟨μ(x), A⟩ = λ_x(A_{T*V}(x))`. -/
theorem cotangentLiouvilleForm_cotangentLiftLieHom (A : Module.End ℝ V) (x : V × StrongDual ℝ V) :
    cotangentLiouvilleForm x (fun _ ↦ cotangentLiftLieHom V A x) = cotangentMomentMap x A := by
  simp

variable (V) in
/-- The **cotangent-lifted linear action** of `gl(V) = Module.End ℝ V` on the linear cotangent
space `V × StrongDual ℝ V` of a finite-dimensional space `V`, by the linear vector fields
`(q, p) ↦ (A q, -(p ∘ A))`. -/
def InfinitesimalAction.cotangentLinear :
    InfinitesimalAction (Module.End ℝ V) 𝓘(ℝ, V × StrongDual ℝ V) (V × StrongDual ℝ V) :=
  (InfinitesimalAction.linear (V × StrongDual ℝ V)).comp (cotangentLiftLieHom V)

@[simp]
theorem InfinitesimalAction.cotangentLinear_apply (A : Module.End ℝ V) (x : V × StrongDual ℝ V) :
    InfinitesimalAction.cotangentLinear V A x = cotangentLiftLieHom V A x := by
  rw [InfinitesimalAction.cotangentLinear, InfinitesimalAction.comp_apply,
    InfinitesimalAction.linear_apply]

/-- The infinitesimal cotangent lift as a Lie algebra homomorphism into
`sp(V × StrongDual ℝ V)`. -/
def cotangentLiftSpLieHom :
    Module.End ℝ V →ₗ⁅ℝ⁆
      skewAdjointLieSubalgebra (strongDualCotangentSymplecticForm (V := V)).toBilinForm where
  toFun A := ⟨cotangentLiftLieHom V A, cotangentLiftLieHom_mem_skewAdjointLieSubalgebra A⟩
  map_add' A B := Subtype.ext <| map_add _ A B
  map_smul' c A := Subtype.ext <| map_smul _ c A
  map_lie' {A B} := Subtype.ext <| LieHom.map_lie _ A B

@[simp]
theorem coe_cotangentLiftSpLieHom (A : Module.End ℝ V) :
    (cotangentLiftSpLieHom A : Module.End ℝ (V × StrongDual ℝ V)) = cotangentLiftLieHom V A :=
  (rfl)

/-- The cotangent moment map is the linear symplectic moment map `½ ω(Ã x, x)` of the cotangent
lift `Ã` of `A`. -/
theorem cotangentMomentMap_apply_eq_linearMomentMap (x : V × StrongDual ℝ V)
    (A : Module.End ℝ V) :
    cotangentMomentMap x A =
      strongDualCotangentSymplecticForm.linearMomentMap x (cotangentLiftSpLieHom A) := by
  simp

/-- **The moment map of the cotangent-lifted linear action.** On the linear cotangent space of a
finite-dimensional space `V`, `⟨μ(q, p), A⟩ = p(A q)` is a moment map of the action of `gl(V)` by
the cotangent-lifted linear vector fields `(q, p) ↦ (A q, -(p ∘ A))`. -/
theorem isMomentMap_cotangentMomentMap :
    (strongDualCotangentSymplecticForm (V := V)).constSmooth.IsMomentMap
      (InfinitesimalAction.cotangentLinear V) cotangentMomentMap := by
  have hμ : cotangentMomentMap = fun x : V × StrongDual ℝ V ↦
      (strongDualCotangentSymplecticForm.linearMomentMap x).comp
        (cotangentLiftSpLieHom (V := V)).toLinearMap :=
    funext fun x ↦ LinearMap.ext fun A ↦ cotangentMomentMap_apply_eq_linearMomentMap x A
  have ha : InfinitesimalAction.cotangentLinear V =
      ((InfinitesimalAction.linear _).comp (skewAdjointLieSubalgebra _).incl).comp
        cotangentLiftSpLieHom :=
    InfinitesimalAction.ext fun A ↦ funext fun x ↦ by
      simp
      -- The two sides differ only in the additive structure on `V × StrongDual ℝ V`: the
      -- symplectic Lie subalgebra uses the one coming from the normed product.
      rfl
  rw [hμ, ha]
  exact (strongDualCotangentSymplecticForm (V := V)).isMomentMap_linearMomentMap.comp
    cotangentLiftSpLieHom

/-- **The cotangent moment map is infinitesimally equivariant**: it intertwines the commutator
bracket of `gl(V)` with the Poisson bracket, `{μ_A, μ_B} = μ_{⁅A, B⁆}`. -/
theorem poissonBracket_cotangentMomentMap (A B : Module.End ℝ V) (x : V × StrongDual ℝ V) :
    (strongDualCotangentSymplecticForm (V := V)).constSmooth.poissonBracket
      (fun y ↦ cotangentMomentMap y A) (fun y ↦ cotangentMomentMap y B) x =
      cotangentMomentMap x ⁅A, B⁆ := by
  simp only [cotangentMomentMap_apply_eq_linearMomentMap,
    SymplecticForm.poissonBracket_linearMomentMap, LieHom.map_lie]

end FiniteDimensional

end TauCeti

namespace ContinuousLinearEquiv

open TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- **Equivariance of the infinitesimal cotangent lift.** The cotangent lift of a continuous
linear equivalence `g` carries the generating vector field of `A` to that of `g A g⁻¹`. -/
theorem cotangent_cotangentLiftLieHom (g : V ≃L[ℝ] W) (A : Module.End ℝ V)
    (x : V × StrongDual ℝ V) :
    g.cotangent (cotangentLiftLieHom V A x) =
      cotangentLiftLieHom W (g.toLinearEquiv.conj A) (g.cotangent x) :=
  Prod.ext (by simp [LinearEquiv.conj_apply]) <| ContinuousLinearMap.ext fun w ↦ by
    simp [LinearEquiv.conj_apply]

end ContinuousLinearEquiv
