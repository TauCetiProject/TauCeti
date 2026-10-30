/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.SkewAdjoint
public import TauCeti.Geometry.Manifold.VectorField.InfinitesimalAction
public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold

import TauCeti.Algebra.Lie.SkewAdjoint
import TauCeti.Geometry.Manifold.MFDeriv.Constancy
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Moment maps of infinitesimal actions

Let `σ` be a two-form on a manifold `M` and let `a : Z ↦ Z_M` be an infinitesimal action of a real
Lie algebra `𝔤` on `M` (`TauCeti.InfinitesimalAction`). A **moment map** of `a` is a map
`μ : M → 𝔤*` whose components `μ_Z = ⟨μ, Z⟩` are smooth functions with Hamiltonian vector fields
`Z_M`, in the convention `ι_{X_f} σ = df`:

`ι_{Z_M} σ = d⟨μ, Z⟩` for every `Z ∈ 𝔤`

(`TauCeti.SmoothTwoForm.IsMomentMap`). No equivariance is required, so this is the infinitesimal
notion; for the fundamental vector fields of a group action, coadjoint equivariance is a separate
condition.

This file proves the basic laws of moment maps:

* a moment map stays a moment map after adding a constant `ν ∈ 𝔤*`, after restricting the action
  along a Lie algebra homomorphism `𝔥 → 𝔤` (composing with the dual map), and, negated, for the
  opposite form `-σ`;
* a moment map pulls back to a moment map along a smooth map relating two actions, so equivariant
  symplectomorphisms transport moment maps (`TauCeti.SmoothTwoForm.IsMomentMap.mpullback`), and
  the moment maps `μ` and `ν` of actions of one Lie algebra on two manifolds add up to the moment
  map `(x, y) ↦ μ x + ν y` of the diagonal action on the product
  (`TauCeti.SmoothTwoForm.IsMomentMap.prod`);
* on a preconnected manifold any two moment maps of the same action differ by a constant, so the
  moment maps of an action are exactly the constant shifts of any one of them
  (`TauCeti.SmoothTwoForm.IsMomentMap.isMomentMap_iff_exists_eq_add`);
* for a nondegenerate form on a finite-dimensional manifold, `Z_M` is the Hamiltonian vector field
  of `μ_Z`, the Poisson bracket with `μ_Z` is the derivative along `Z_M`, so `{μ_Z, μ_Z'}` is
  `σ(Z_M, Z'_M)`, and **Noether's theorem** holds: the derivative of a function along `Z_M`
  vanishes exactly when it Poisson-commutes with `μ_Z`.

The example is the linear action of the symplectic Lie algebra `sp(V, ω)`, the skew-adjoint
endomorphisms of a finite-dimensional symplectic vector space `(V, ω)`, by the vector fields
`x ↦ A x`. Its moment map is `μ_A(x) = ½ ω(A x, x)`
(`TauCeti.SymplecticForm.isMomentMap_linearMomentMap`), and it is infinitesimally equivariant:
`{μ_A, μ_B} = μ_{⁅A, B⁆}` (`TauCeti.SymplecticForm.poissonBracket_linearMomentMap`).

## Main definitions

* `TauCeti.SmoothTwoForm.IsMomentMap σ a μ`: `μ` is a moment map of the infinitesimal action `a`
  for `σ`.
* `TauCeti.SymplecticForm.linearMomentMap ω`: the moment map `μ_A(x) = ½ ω(A x, x)` of the linear
  action of `sp(V, ω)`.

## References

* V. Guillemin, S. Sternberg, *Symplectic Techniques in Physics*, Cambridge University Press,
  1984, Section 26.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Lecture 22.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 5.2.
-/

public section

noncomputable section

open scoped Manifold

namespace TauCeti

namespace SmoothTwoForm

open scoped ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]
  {σ : SmoothTwoForm I M} {a : InfinitesimalAction 𝔤 I M} {μ μ' : M → Module.Dual ℝ 𝔤}

/-- `μ : M → 𝔤*` is a **moment map** of the infinitesimal action `a : Z ↦ Z_M` for the two-form
`σ` when every component `μ_Z = fun x ↦ μ x Z` is smooth and has Hamiltonian vector field `Z_M`:
`ι_{Z_M} σ = d μ_Z`. -/
structure IsMomentMap (σ : SmoothTwoForm I M) (a : InfinitesimalAction 𝔤 I M)
    (μ : M → Module.Dual ℝ 𝔤) : Prop where
  /-- Each component of a moment map is smooth. -/
  contMDiff : ∀ Z, ContMDiff I 𝓘(ℝ) ∞ fun x ↦ μ x Z
  /-- The generated vector field `Z_M` is a Hamiltonian vector field of the component `μ_Z`. -/
  isHamiltonianVectorField : ∀ Z, σ.IsHamiltonianVectorField (fun x ↦ μ x Z) (a Z)

/-- The defining conditions of a moment map, componentwise. -/
theorem isMomentMap_iff :
    σ.IsMomentMap a μ ↔ ∀ Z, ContMDiff I 𝓘(ℝ) ∞ (fun x ↦ μ x Z) ∧
      σ.IsHamiltonianVectorField (fun x ↦ μ x Z) (a Z) :=
  ⟨fun h Z ↦ ⟨h.contMDiff Z, h.isHamiltonianVectorField Z⟩,
    fun h ↦ ⟨fun Z ↦ (h Z).1, fun Z ↦ (h Z).2⟩⟩

namespace IsMomentMap

/-- The defining identity of a moment map: `σ(Z_M x, v) = d μ_Z (v)`. -/
theorem eval₂_apply (h : σ.IsMomentMap a μ) (Z : 𝔤) (x : M) (v : TangentSpace I x) :
    SmoothBundleForm.eval₂ σ x (a Z x) v = mvfderiv I (fun y ↦ μ y Z) x v :=
  isHamiltonianVectorField_iff.1 (h.isHamiltonianVectorField Z) x v

/-- The components of a moment map are differentiable. -/
theorem mdifferentiableAt (h : σ.IsMomentMap a μ) (Z : 𝔤) (x : M) :
    MDifferentiableAt I 𝓘(ℝ) (fun y ↦ μ y Z) x :=
  (h.contMDiff Z).mdifferentiableAt (by simp)

/-- Adding a constant `ν ∈ 𝔤*` to a moment map gives a moment map of the same action. -/
theorem add_const (h : σ.IsMomentMap a μ) (ν : Module.Dual ℝ 𝔤) :
    σ.IsMomentMap a fun x ↦ μ x + ν where
  contMDiff Z := by
    simp only [LinearMap.add_apply]
    exact (h.contMDiff Z).add contMDiff_const
  isHamiltonianVectorField Z := isHamiltonianVectorField_iff.2 fun x v ↦ by
    simp only [LinearMap.add_apply]
    rw [mvfderiv_fun_add (h.mdifferentiableAt Z x) mdifferentiableAt_const, mvfderiv_const,
      add_zero, h.eval₂_apply]

/-- The negative of a moment map for `σ` is a moment map of the same action for the opposite
form `-σ`. -/
theorem neg (h : σ.IsMomentMap a μ) : (-σ).IsMomentMap a fun x ↦ -μ x where
  contMDiff Z := by
    simp only [LinearMap.neg_apply]
    exact (h.contMDiff Z).neg
  isHamiltonianVectorField Z := isHamiltonianVectorField_iff.2 fun x v ↦ by
    simp only [LinearMap.neg_apply]
    rw [mvfderiv_fun_neg, SmoothBundleForm.eval₂_neg, h.eval₂_apply, _root_.neg_apply]

/-- **Restriction of moment maps.** Along a Lie algebra homomorphism `f : 𝔥 → 𝔤`, for instance the
inclusion of a Lie subalgebra, a moment map `μ` of `a` gives the moment map `x ↦ μ x ∘ f` of the
restricted action `Z ↦ (f Z)_M`. -/
theorem comp {𝔥 : Type*} [LieRing 𝔥] [LieAlgebra ℝ 𝔥] (h : σ.IsMomentMap a μ)
    (f : 𝔥 →ₗ⁅ℝ⁆ 𝔤) :
    σ.IsMomentMap (a.comp f) fun x ↦ (μ x).comp (f : 𝔥 →ₗ[ℝ] 𝔤) where
  contMDiff Z := h.contMDiff (f Z)
  isHamiltonianVectorField Z := by
    simpa only [InfinitesimalAction.comp_apply, LinearMap.comp_apply, LieHom.coe_toLinearMap]
      using h.isHamiltonianVectorField (f Z)

/-- **Transport of moment maps.** Let a smooth map `φ : M' → M` relate an infinitesimal action
`a'` on `M'` to `a`, that is `dφ (Z_{M'} x) = Z_M (φ x)`. Then `μ ∘ φ` is a moment map of `a'` for
the pullback `φ^* σ`. For instance, an equivariant symplectomorphism carries moment maps to moment
maps. -/
theorem mpullback {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M']
    [ChartedSpace H' M'] [IsManifold I' ∞ M'] {a' : InfinitesimalAction 𝔤 I' M'}
    (h : σ.IsMomentMap a μ) {φ : M' → M} (hφ : ContMDiff I' I ∞ φ)
    (hφa : ∀ Z x, mfderiv I' I φ x (a' Z x) = a Z (φ x)) :
    IsMomentMap (SmoothForm.mpullback φ hφ σ) a' (μ ∘ φ) where
  contMDiff Z := (h.contMDiff Z).comp hφ
  isHamiltonianVectorField Z :=
    (h.isHamiltonianVectorField Z).mpullback hφ (fun x ↦ h.mdifferentiableAt Z (φ x)) (hφa Z)

/-- **Moment maps of products.** If `μ` and `ν` are moment maps of infinitesimal actions of the
same Lie algebra on `(M, σ)` and on `(N, τ)`, then `(x, y) ↦ μ x + ν y` is a moment map of the
diagonal action on `M × N` for the product form `pr₁^* σ + pr₂^* τ`. -/
theorem prod {F H' N : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H']
    {J : ModelWithCorners ℝ F H'} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
    [CompleteSpace E] [CompleteSpace F] {τ : SmoothTwoForm J N}
    {b : InfinitesimalAction 𝔤 J N} {ν : N → Module.Dual ℝ 𝔤} (h : σ.IsMomentMap a μ)
    (h' : τ.IsMomentMap b ν) :
    (σ.prod τ).IsMomentMap (a.prod b) fun p ↦ μ p.1 + ν p.2 where
  contMDiff Z := ((h.contMDiff Z).comp contMDiff_fst).add ((h'.contMDiff Z).comp contMDiff_snd)
  isHamiltonianVectorField Z := by
    simpa only [LinearMap.add_apply, InfinitesimalAction.prod_apply] using
      (h.isHamiltonianVectorField Z).prod (h'.isHamiltonianVectorField Z) (h.mdifferentiableAt Z)
        (h'.mdifferentiableAt Z)

/-- Two moment maps of the same action have components differing by functions with vanishing
differential. -/
theorem mfderiv_sub_eq_zero (h : σ.IsMomentMap a μ) (h' : σ.IsMomentMap a μ') (Z : 𝔤)
    (x : M) : mfderiv I 𝓘(ℝ) (fun y ↦ μ' y Z - μ y Z) x = 0 := by
  rw [← mvfderiv_eq_zero_iff, mvfderiv_fun_sub (h'.mdifferentiableAt Z x)
    (h.mdifferentiableAt Z x), sub_eq_zero]
  ext v
  rw [← h.eval₂_apply, ← h'.eval₂_apply]

/-- **Uniqueness of moment maps up to constants.** On a preconnected manifold, the moment maps of
an infinitesimal action are exactly the shifts `x ↦ μ x + ν` of any one moment map `μ` by constants
`ν ∈ 𝔤*`. -/
theorem isMomentMap_iff_exists_eq_add [PreconnectedSpace M] (h : σ.IsMomentMap a μ) :
    σ.IsMomentMap a μ' ↔ ∃ ν : Module.Dual ℝ 𝔤, μ' = fun x ↦ μ x + ν := by
  refine ⟨fun h' ↦ ?_, fun ⟨ν, hν⟩ ↦ hν ▸ h.add_const ν⟩
  rcases isEmpty_or_nonempty M with hM | ⟨⟨x₀⟩⟩
  · exact ⟨0, funext fun x ↦ isEmptyElim x⟩
  refine ⟨μ' x₀ - μ x₀, funext fun x ↦ LinearMap.ext fun Z ↦ ?_⟩
  have hc : μ' x Z - μ x Z = μ' x₀ Z - μ x₀ Z :=
    MDifferentiable.apply_eq_of_mfderiv_eq_zero
      (fun y ↦ (h'.mdifferentiableAt Z y).sub (h.mdifferentiableAt Z y))
      (h.mfderiv_sub_eq_zero h' Z) x x₀
  rw [LinearMap.add_apply, LinearMap.sub_apply, ← hc]
  ring

section Nondegenerate

variable [FiniteDimensional ℝ E]

/-- For a nondegenerate form, the vector field `Z_M` generated by `Z` is the Hamiltonian vector
field of the component `μ_Z`. -/
theorem hamiltonianVectorField_eq (h : σ.IsMomentMap a μ) (hσ : σ.IsNondegenerate) (Z : 𝔤) :
    σ.hamiltonianVectorField (fun x ↦ μ x Z) = a Z :=
  (hσ.isHamiltonianVectorField_iff_eq.1 (h.isHamiltonianVectorField Z)).symm

/-- The Poisson bracket `{f, μ_Z}` is the derivative of `f` along the generated vector field
`Z_M`. -/
theorem poissonBracket_eq_mvfderiv (h : σ.IsMomentMap a μ) (hσ : σ.IsNondegenerate) (f : M → ℝ)
    (Z : 𝔤) (x : M) :
    σ.poissonBracket f (fun y ↦ μ y Z) x = mvfderiv I f x (a Z x) := by
  rw [hσ.poissonBracket_eq_mvfderiv, h.hamiltonianVectorField_eq hσ]

/-- The Poisson bracket `{μ_Z, f}` is minus the derivative of `f` along the generated vector field
`Z_M`. -/
theorem poissonBracket_eq_neg_mvfderiv (h : σ.IsMomentMap a μ) (hσ : σ.IsNondegenerate) (f : M → ℝ)
    (Z : 𝔤) (x : M) :
    σ.poissonBracket (fun y ↦ μ y Z) f x = -mvfderiv I f x (a Z x) := by
  rw [← neg_poissonBracket, h.poissonBracket_eq_mvfderiv hσ]

/-- The Poisson bracket of two components of a moment map is the form evaluated on the generated
vector fields: `{μ_Z, μ_Z'} = σ(Z_M, Z'_M)`. -/
theorem poissonBracket_eq_eval₂ (h : σ.IsMomentMap a μ) (hσ : σ.IsNondegenerate) (Z Z' : 𝔤)
    (x : M) :
    σ.poissonBracket (fun y ↦ μ y Z) (fun y ↦ μ y Z') x =
      SmoothBundleForm.eval₂ σ x (a Z x) (a Z' x) := by
  rw [h.poissonBracket_eq_mvfderiv hσ, h.eval₂_apply]

/-- **Noether's theorem.** The derivative of a function `f` along the generated vector field `Z_M`
vanishes exactly when `f` Poisson-commutes with the component `μ_Z` of a moment map. -/
theorem poissonBracket_eq_zero_iff (h : σ.IsMomentMap a μ) (hσ : σ.IsNondegenerate)
    (f : M → ℝ) (Z : 𝔤) :
    σ.poissonBracket (fun y ↦ μ y Z) f = 0 ↔ ∀ x, mvfderiv I f x (a Z x) = 0 := by
  simp only [funext_iff, Pi.zero_apply, h.poissonBracket_eq_neg_mvfderiv hσ, neg_eq_zero]

end Nondegenerate

end IsMomentMap

end SmoothTwoForm

namespace SymplecticForm

attribute [local instance 100] LieRing.ofAssociativeRing

section Algebraic

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (ω : SymplecticForm V)

/-- The **moment map of the linear symplectic action**: for a symplectic vector space `(V, ω)`,
the skew-adjoint endomorphisms `A ∈ sp(V, ω)` act by the vector fields `x ↦ A x`, and
`μ_A(x) = ½ ω(A x, x)`. -/
def linearMomentMap (x : V) : Module.Dual ℝ (skewAdjointLieSubalgebra ω.toBilinForm) where
  toFun A := ω ((A : Module.End ℝ V) x) x / 2
  map_add' A B := by simp [add_div]
  map_smul' c A := by simp [mul_div_assoc]

@[simp]
theorem linearMomentMap_apply (x : V) (A : skewAdjointLieSubalgebra ω.toBilinForm) :
    ω.linearMomentMap x A = ω ((A : Module.End ℝ V) x) x / 2 :=
  (rfl)

end Algebraic

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (ω : SymplecticForm V)
  [FiniteDimensional ℝ V]

/-- The component `μ_A` is the continuous bilinear expression `y ↦ ω(A y, y) / 2`. -/
private theorem linearMomentMap_eq_comp (A : skewAdjointLieSubalgebra ω.toBilinForm) :
    (fun y ↦ ω.linearMomentMap y A) = fun y ↦
      (ω.toBilinForm.toContinuousBilinearMap.comp
        (LinearMap.toContinuousLinearMap (A : Module.End ℝ V))) y y * 2⁻¹ := by
  funext y
  simp [div_eq_mul_inv]

/-- The derivative of the moment map component `μ_A(x) = ½ ω(A x, x)` is `v ↦ ω(A x, v)`. -/
theorem fderiv_linearMomentMap_apply (A : skewAdjointLieSubalgebra ω.toBilinForm) (x v : V) :
    fderiv ℝ (fun y ↦ ω.linearMomentMap y A) x v = ω ((A : Module.End ℝ V) x) v := by
  let B := ω.toBilinForm.toContinuousBilinearMap
  let A' := LinearMap.toContinuousLinearMap (A : Module.End ℝ V)
  have hd : HasFDerivAt (fun y ↦ (B.comp A') y y)
      (((B.comp A') x).comp (ContinuousLinearMap.id ℝ V) + (B.comp A').flip x) x :=
    (B.comp A').hasFDerivAt.clm_apply (hasFDerivAt_id x)
  rw [linearMomentMap_eq_comp, (hd.mul_const 2⁻¹).fderiv]
  simp only [FunLike.coe_smul, FunLike.coe_add,
    ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_id', ContinuousLinearMap.flip_apply,
    Pi.smul_apply, Pi.add_apply, Function.comp_apply, id_eq,
    LinearMap.toContinuousBilinearMap_apply, LinearMap.coe_toContinuousLinearMap', B, A',
    smul_eq_mul]
  -- Skew-adjointness and skew-symmetry turn `ω(A v, x)` into `ω(A x, v)`.
  rw [skewAdjointLieSubalgebra.apply_left A v x, ← ω.isAlt.neg_eq ((A : Module.End ℝ V) x) v,
    neg_neg]
  ring

/-- **The moment map of the linear symplectic action.** On a finite-dimensional symplectic vector
space `(V, ω)`, `μ_A(x) = ½ ω(A x, x)` is a moment map of the action of `sp(V, ω)` by the linear
vector fields `x ↦ A x`. -/
theorem isMomentMap_linearMomentMap :
    ω.constSmooth.IsMomentMap
      ((InfinitesimalAction.linear V).comp (skewAdjointLieSubalgebra ω.toBilinForm).incl)
      ω.linearMomentMap where
  contMDiff A := by
    rw [linearMomentMap_eq_comp]
    exact contMDiff_iff_contDiff.2
      (((ContinuousLinearMap.contDiff _).clm_apply contDiff_id).mul contDiff_const)
  isHamiltonianVectorField A := SmoothTwoForm.isHamiltonianVectorField_iff.2 fun x v ↦ by
    rw [mvfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, fderiv_linearMomentMap_apply,
      fromTangentSpace_constSmooth_apply]
    simp only [InfinitesimalAction.comp_apply, LieSubalgebra.coe_incl,
      InfinitesimalAction.linear_apply]
    rw [ContinuousLinearEquiv.coe_coe, NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) x v,
      NormedSpace.fromTangentSpace_apply (𝕜 := ℝ) x ((A : Module.End ℝ V) x)]

/-- **The linear moment map is infinitesimally equivariant**: the moment map `μ_A(x) = ½ ω(A x, x)`
intertwines the Lie bracket of `sp(V, ω)` with the Poisson bracket,
`{μ_A, μ_B} = μ_{⁅A, B⁆}`. -/
theorem poissonBracket_linearMomentMap (A B : skewAdjointLieSubalgebra ω.toBilinForm) (x : V) :
    ω.constSmooth.poissonBracket (fun y ↦ ω.linearMomentMap y A)
      (fun y ↦ ω.linearMomentMap y B) x = ω.linearMomentMap x ⁅A, B⁆ := by
  rw [(ω.isMomentMap_linearMomentMap).poissonBracket_eq_eval₂ (isNondegenerate_constSmooth ω)]
  simp only [InfinitesimalAction.comp_apply, LieSubalgebra.coe_incl,
    InfinitesimalAction.linear_apply, constSmooth_apply, linearMomentMap_apply,
    LieSubalgebra.coe_bracket, LieRing.of_associative_ring_bracket, LinearMap.sub_apply,
    Module.End.mul_apply, map_sub]
  rw [skewAdjointLieSubalgebra.apply_left A ((B : Module.End ℝ V) x) x,
    skewAdjointLieSubalgebra.apply_left B ((A : Module.End ℝ V) x) x,
    ← ω.isAlt.neg_eq ((A : Module.End ℝ V) x) ((B : Module.End ℝ V) x)]
  ring

end SymplecticForm

end TauCeti
