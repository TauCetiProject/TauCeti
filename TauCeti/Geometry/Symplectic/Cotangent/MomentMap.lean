/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Cotangent.Liouville
public import TauCeti.Geometry.Symplectic.Cotangent.StrongDual
public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap
public import TauCeti.Geometry.Symplectic.SymplecticTransport

/-!
# Moment maps of cotangent-lifted linear actions

A linear map `A` of a real normed space `V` acts on the linear cotangent space
`V × StrongDual ℝ V`, with its canonical symplectic form
`ω((q, p), (q', p')) = p'(q) - p(q')`, by the cotangent lift of `A`. Its **moment map** is

`⟨μ(q, p), A⟩ = p(A q)` (`TauCeti.cotangentMomentMap`),

the pairing of the covector `p` with the vector `A q` generated at the base point `q`. This file
proves the moment map identities at the level of the linear group `GL(V)` and of its Lie algebra.

For a continuous linear equivalence `g : V ≃L[ℝ] W` the cotangent lift is
`(q, p) ↦ (g q, p ∘ g⁻¹)` (`ContinuousLinearEquiv.cotangent`). It is a symplectomorphism, it
preserves the Liouville forms `λ_(q, p)(δq, δp) = p(δq)`, and it is compatible with identities,
composition and inverses. The moment map is coadjoint equivariant: `μ(g · x)(A) = μ(x)(g⁻¹ A g)`
(`ContinuousLinearEquiv.cotangentMomentMap_cotangent`).

For finite-dimensional `V`, the infinitesimal cotangent lift `(q, p) ↦ (A q, -(p ∘ A))` is a Lie
algebra homomorphism from `Module.End ℝ V` to the endomorphisms of `V × StrongDual ℝ V`
(`TauCeti.cotangentLiftLieHom`). It defines an infinitesimal action of `gl(V)` by linear vector
fields (`TauCeti.InfinitesimalAction.cotangentLinear`). Then:

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
* `ContinuousLinearEquiv.cotangent`: the cotangent lift `(q, p) ↦ (g q, p ∘ g⁻¹)`.
* `TauCeti.cotangentLiftLieHom`: the infinitesimal cotangent lift `(q, p) ↦ (A q, -(p ∘ A))`.
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

variable {V W X : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The **cotangent lift** `(q, p) ↦ (g q, p ∘ g⁻¹)` of a continuous linear equivalence
`g : V ≃L[ℝ] W`, as a continuous linear equivalence of the linear cotangent spaces
`V × StrongDual ℝ V` and `W × StrongDual ℝ W`. -/
def cotangent (g : V ≃L[ℝ] W) : (V × StrongDual ℝ V) ≃L[ℝ] (W × StrongDual ℝ W) :=
  g.prodCongr (g.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))

@[simp]
theorem cotangent_apply_fst (g : V ≃L[ℝ] W) (x : V × StrongDual ℝ V) :
    (g.cotangent x).1 = g x.1 :=
  (rfl)

@[simp]
theorem cotangent_apply_snd_apply (g : V ≃L[ℝ] W) (x : V × StrongDual ℝ V) (w : W) :
    (g.cotangent x).2 w = x.2 (g.symm w) :=
  (rfl)

/-- The cotangent lift of the identity is the identity. -/
@[simp]
theorem cotangent_refl :
    (ContinuousLinearEquiv.refl ℝ V).cotangent = ContinuousLinearEquiv.refl ℝ _ :=
  (rfl)

/-- The cotangent lift of a composite is the composite of the cotangent lifts. -/
theorem cotangent_trans (g : V ≃L[ℝ] W) (h : W ≃L[ℝ] X) :
    (g.trans h).cotangent = g.cotangent.trans h.cotangent :=
  (rfl)

/-- The cotangent lift of the inverse is the inverse of the cotangent lift. -/
theorem cotangent_symm (g : V ≃L[ℝ] W) : g.symm.cotangent = g.cotangent.symm :=
  (rfl)

/-- The cotangent lift of a continuous linear equivalence preserves the canonical symplectic
forms. -/
theorem strongDualCotangentSymplecticForm_cotangent (g : V ≃L[ℝ] W) (x y : V × StrongDual ℝ V) :
    strongDualCotangentSymplecticForm (g.cotangent x) (g.cotangent y) =
      strongDualCotangentSymplecticForm x y := by
  simp

/-- The cotangent lift of a continuous linear equivalence is a symplectomorphism of the linear
cotangent spaces. -/
theorem isSymplectomorphism_cotangent (g : V ≃L[ℝ] W) :
    SymplecticForm.IsSymplectomorphism strongDualCotangentSymplecticForm
      strongDualCotangentSymplecticForm g.cotangent.toLinearEquiv :=
  SymplecticForm.isSymplectomorphism_iff.2 g.strongDualCotangentSymplecticForm_cotangent

/-- The cotangent lift of a continuous linear equivalence preserves the Liouville forms:
`λ_(g · x)(g · v) = λ_x(v)`. -/
theorem cotangentLiouvilleForm_cotangent (g : V ≃L[ℝ] W) (x : V × StrongDual ℝ V)
    (v : Fin 1 → V × StrongDual ℝ V) :
    cotangentLiouvilleForm (g.cotangent x) (fun i ↦ g.cotangent (v i)) =
      cotangentLiouvilleForm x v := by
  simp

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

/-- The infinitesimal moment map identity in linear form: `ω(A_{T*V}(x), v) = dμ_A(x)(v)`, where
`A_{T*V}` is the infinitesimal cotangent lift of `A`. -/
theorem strongDualCotangentSymplecticForm_cotangentLiftLieHom (A : Module.End ℝ V)
    (x v : V × StrongDual ℝ V) :
    strongDualCotangentSymplecticForm (cotangentLiftLieHom V A x) v =
      v.2 (A x.1) + x.2 (A v.1) := by
  simp [sub_eq_add_neg]

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

/-- The derivative of the moment map component `μ_A(q, p) = p(A q)` is
`(δq, δp) ↦ δp(A q) + p(A δq)`. -/
theorem fderiv_cotangentMomentMap_apply (A : Module.End ℝ V) (x v : V × StrongDual ℝ V) :
    fderiv ℝ (fun y ↦ cotangentMomentMap y A) x v = v.2 (A x.1) + x.2 (A v.1) := by
  let A' := LinearMap.toContinuousLinearMap A
  have hd : HasFDerivAt (fun y : V × StrongDual ℝ V ↦ cotangentMomentMap y A)
      (x.2.comp (A'.comp (ContinuousLinearMap.fst ℝ V (StrongDual ℝ V))) +
        (ContinuousLinearMap.snd ℝ V (StrongDual ℝ V)).flip (A' x.1)) x :=
    (hasFDerivAt_snd (p := x)).clm_apply (A'.hasFDerivAt.comp x hasFDerivAt_fst)
  rw [hd.fderiv]
  simp [A', add_comm]

/-- **The moment map of the cotangent-lifted linear action.** On the linear cotangent space of a
finite-dimensional space `V`, `⟨μ(q, p), A⟩ = p(A q)` is a moment map of the action of `gl(V)` by
the cotangent-lifted linear vector fields `(q, p) ↦ (A q, -(p ∘ A))`. -/
theorem isMomentMap_cotangentMomentMap :
    (strongDualCotangentSymplecticForm (V := V)).constSmooth.IsMomentMap
      (InfinitesimalAction.cotangentLinear V) cotangentMomentMap where
  contMDiff A := contMDiff_iff_contDiff.2 <|
    contDiff_snd.clm_apply ((LinearMap.toContinuousLinearMap A).contDiff.comp contDiff_fst)
  isHamiltonianVectorField A := SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ by
    rw [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, fderiv_cotangentMomentMap_apply,
      SymplecticForm.fromTangentSpace_constSmooth_apply, InfinitesimalAction.cotangentLinear_apply,
      ContinuousLinearEquiv.coe_coe,
      NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) x (cotangentLiftLieHom V A x),
      strongDualCotangentSymplecticForm_cotangentLiftLieHom]

/-- **The cotangent moment map is infinitesimally equivariant**: it intertwines the commutator
bracket of `gl(V)` with the Poisson bracket, `{μ_A, μ_B} = μ_{⁅A, B⁆}`. -/
theorem poissonBracket_cotangentMomentMap (A B : Module.End ℝ V) (x : V × StrongDual ℝ V) :
    (strongDualCotangentSymplecticForm (V := V)).constSmooth.poissonBracket
      (fun y ↦ cotangentMomentMap y A) (fun y ↦ cotangentMomentMap y B) x =
      cotangentMomentMap x ⁅A, B⁆ := by
  rw [isMomentMap_cotangentMomentMap.poissonBracket_eq_eval₂
    (SymplecticForm.isNondegenerate_constSmooth _)]
  simp only [InfinitesimalAction.cotangentLinear_apply, SymplecticForm.constSmooth_apply,
    strongDualCotangentSymplecticForm_apply, cotangentLiftLieHom_apply_fst,
    cotangentLiftLieHom_apply_snd_apply, cotangentMomentMap_apply,
    LieRing.of_associative_ring_bracket, Module.End.mul_apply, map_sub]
  ring

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
