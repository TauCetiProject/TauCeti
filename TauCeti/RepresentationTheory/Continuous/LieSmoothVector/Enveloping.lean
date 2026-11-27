/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Hom
public import TauCeti.Algebra.Lie.UniversalEnveloping.Functoriality
public import TauCeti.Geometry.Lie.Adjoint.Derivation
public import TauCeti.RepresentationTheory.Continuous.LieSmoothVector
import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
import TauCeti.Geometry.Lie.Adjoint.Exponential.Basic

/-!
# The enveloping algebra acting on smooth vectors

Let `π` be a continuous representation of a real Lie group `G` on a real normed space `V`, with
coefficients in a ring `R`. The group acts on the submodule `lieSmoothVectors I π` of smooth
vectors, and the derived action `lieSmoothVectorsDerivedAction I π` is a homomorphism of real Lie
algebras from the left-invariant derivations of `G` to the `R`-linear endomorphisms of the smooth
vectors. This file adds:

* the adjoint covariance `π(g) dπ(X) π(g)⁻¹ = dπ(Ad(g) X)`, for every `g`, so with no
  connectedness hypothesis on `G`;
* the induced action of the universal enveloping algebra `U(𝔤)` of the real Lie algebra, which
  makes the smooth vectors a `U(𝔤)`-module, together with its adjoint covariance;
* for commutative coefficients `R` (for instance `R = ℂ`), the `R`-linear extension of the derived
  action to `R ⊗[ℝ] 𝔤`, with `dπ(a ⊗ X) = a • dπ(X)` (so `dπ(i ⊗ X) = i • dπ(X)` for complex
  representations), the induced module structure over `U(R ⊗[ℝ] 𝔤)`, and the Lie module structure
  over `R ⊗[ℝ] 𝔤` with `⁅x, v⁆ = dπ(x) v`, whose `U(R ⊗[ℝ] 𝔤)`-representation is that action.

## Main definitions

* `ContRepresentation.lieSmoothVectorsEnvelopingAction I π`: the action of `U(𝔤)` on the smooth
  vectors, an `ℝ`-algebra homomorphism into the `R`-linear endomorphisms.
* `ContRepresentation.lieSmoothVectorsBaseChangeDerivedAction I π`: the `R`-linear extension of the
  derived action to `R ⊗[ℝ] 𝔤`.
* `ContRepresentation.lieSmoothVectorsBaseChangeEnvelopingAction I π`: the action of
  `U(R ⊗[ℝ] 𝔤)` on the smooth vectors.
* `ContRepresentation.instLieModuleTensorProductLieSmoothVectors`: the Lie module structure of the
  smooth vectors over `R ⊗[ℝ] 𝔤`.

## Main results

* `ContRepresentation.lieDerivative_Ad`: the derived action of `Ad(g) X` is the conjugate of the
  derived action of `X` by `π(g)`.
* `ContRepresentation.lieSmoothVectorsDerivative_Ad`: the same identity for the derived
  endomorphisms of the smooth vectors.
* `ContRepresentation.lieSmoothVectorsEnvelopingAction_map_Ad`: the adjoint covariance of the
  `U(𝔤)`-action.
* `ContRepresentation.representation_lieSmoothVectors`: the `U(R ⊗[ℝ] 𝔤)`-representation of the
  Lie module of smooth vectors is `lieSmoothVectorsBaseChangeEnvelopingAction I π`.

## References

* Bernstein, Krötz, *Smooth Fréchet globalizations of Harish-Chandra modules*, §2.
-/

public section

noncomputable section

open Manifold
open scoped ContDiff Manifold TensorProduct

namespace ContRepresentation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

variable [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField

section Ad

variable {R : Type*} [Ring R] [Module R V] (π : ContRepresentation R G V)

open TauCeti.Lie

variable {I} in
/-- **Adjoint covariance of the derived action.** For every group element `g`, the derived action
of `Ad(g) X` is the conjugate `π(g) dπ(X) π(g)⁻¹` of the derived action of `X`. -/
theorem lieDerivative_Ad (g : G) (X : LeftInvariantDerivation I G) (v : V) :
    lieDerivative π (Ad (I := I) g X) v = π g (lieDerivative π X (π g⁻¹ v)) := by
  let L : V →L[ℝ] V := (π g : V →+ V).toRealLinearMap (π g).continuous
  let L' : V →L[ℝ] V := (π g⁻¹ : V →+ V).toRealLinearMap (π g⁻¹).continuous
  set f : ℝ → V := fun t ↦ π (lieExp (t • X)) (π g⁻¹ v)
  have hfun : (fun t : ℝ ↦ π (lieExp (t • Ad (I := I) g X)) v) = L ∘ f := by
    funext t
    rw [← map_smul, ← conj_lieExp, map_mul, map_mul]
    simp [L, f]
  have hL' : L' ∘ (L ∘ f) = f := by
    funext t
    simpa [L, L'] using π.apply_inv_apply (g := g⁻¹) (v := f t)
  rw [lieDerivative_def, lieDerivative_def, hfun]
  by_cases hf : DifferentiableAt ℝ f 0
  · exact (L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf.hasDerivAt).deriv
  · have hLf : ¬DifferentiableAt ℝ (L ∘ f) 0 := fun h ↦
      hf (hL' ▸ L'.differentiableAt.comp (0 : ℝ) h)
    rw [deriv_zero_of_not_differentiableAt hf, deriv_zero_of_not_differentiableAt hLf, map_zero]

variable [SMulCommClass ℝ R V] [ContinuousConstSMul R V]

/-- **Adjoint covariance of the derived endomorphisms.** On smooth vectors,
`π(g) dπ(X) π(g)⁻¹ = dπ(Ad(g) X)` for every group element `g`. -/
theorem lieSmoothVectorsDerivative_Ad (g : G) (X : LeftInvariantDerivation I G) :
    lieSmoothVectorsDerivative I π (Ad (I := I) g X) =
      lieSmoothVectorsAction I π g * lieSmoothVectorsDerivative I π X *
        lieSmoothVectorsAction I π g⁻¹ :=
  LinearMap.ext fun w ↦ Subtype.ext (by simpa using lieDerivative_Ad π g X w)

end Ad

section Enveloping

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} [Ring R] [Module R V] (π : ContRepresentation R G V)
  [Algebra ℝ R] [IsScalarTower ℝ R V] [ContinuousConstSMul R V]

/-- **The `U(𝔤)`-action on smooth vectors.** The derived representation of the real Lie algebra
of left-invariant derivations extends uniquely to an algebra homomorphism out of its universal
enveloping algebra. -/
def lieSmoothVectorsEnvelopingAction :
    UniversalEnvelopingAlgebra ℝ (LeftInvariantDerivation I G) →ₐ[ℝ]
      Module.End R (lieSmoothVectors I π) :=
  UniversalEnvelopingAlgebra.lift ℝ (lieSmoothVectorsDerivedAction I π)

/-- A Lie algebra element acts on smooth vectors by its derived endomorphism. -/
theorem lieSmoothVectorsEnvelopingAction_ι (X : LeftInvariantDerivation I G) :
    lieSmoothVectorsEnvelopingAction I π (UniversalEnvelopingAlgebra.ι ℝ X) =
      lieSmoothVectorsDerivative I π X := by
  rw [lieSmoothVectorsEnvelopingAction, UniversalEnvelopingAlgebra.lift_ι_apply,
    lieSmoothVectorsDerivedAction_apply]

/-- `lieSmoothVectorsEnvelopingAction_ι` in `simp`-normal form, where the canonical map into
`U(𝔤)` is written through the tensor algebra. -/
@[simp]
theorem lieSmoothVectorsEnvelopingAction_mkAlgHom_ι (X : LeftInvariantDerivation I G) :
    lieSmoothVectorsEnvelopingAction I π
        (UniversalEnvelopingAlgebra.mkAlgHom ℝ (LeftInvariantDerivation I G)
          (TensorAlgebra.ι ℝ X)) =
      lieSmoothVectorsDerivative I π X :=
  lieSmoothVectorsEnvelopingAction_ι I π X

/-- **Adjoint covariance of the `U(𝔤)`-action.** Conjugating the action of `u ∈ U(𝔤)` by `π(g)`
gives the action of the image of `u` under the automorphism of `U(𝔤)` induced by `Ad(g)`. -/
theorem lieSmoothVectorsEnvelopingAction_map_Ad (g : G)
    (u : UniversalEnvelopingAlgebra ℝ (LeftInvariantDerivation I G)) :
    lieSmoothVectorsEnvelopingAction I π
        (TauCeti.UniversalEnvelopingAlgebra.map ℝ (TauCeti.Lie.Ad (I := I) g).toLieHom u) =
      lieSmoothVectorsAction I π g * lieSmoothVectorsEnvelopingAction I π u *
        lieSmoothVectorsAction I π g⁻¹ := by
  have hinv : lieSmoothVectorsAction I π g⁻¹ * lieSmoothVectorsAction I π g = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hinv' : lieSmoothVectorsAction I π g * lieSmoothVectorsAction I π g⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel, map_one]
  induction u using TauCeti.UniversalEnvelopingAlgebra.induction_ι with
  | ι X =>
    rw [TauCeti.UniversalEnvelopingAlgebra.map_ι, lieSmoothVectorsEnvelopingAction_ι,
      lieSmoothVectorsEnvelopingAction_ι, LieEquiv.coe_toLieHom, lieSmoothVectorsDerivative_Ad]
  | algebraMap c =>
    simp [← Algebra.commutes, mul_assoc, hinv']
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, mul_add, add_mul]
  | mul a b ha hb =>
    simp only [map_mul, ha, hb, mul_assoc, ← mul_assoc (lieSmoothVectorsAction I π g⁻¹) _ _, hinv,
      one_mul]

/-- **The `U(𝔤)`-module of smooth vectors**, through `lieSmoothVectorsEnvelopingAction`. -/
instance instModuleUniversalEnvelopingAlgebraLieSmoothVectors :
    Module (UniversalEnvelopingAlgebra ℝ (LeftInvariantDerivation I G)) (lieSmoothVectors I π) :=
  Module.compHom _ (lieSmoothVectorsEnvelopingAction I π).toRingHom

/-- An element of `U(𝔤)` acts on a smooth vector through `lieSmoothVectorsEnvelopingAction`. -/
theorem envelopingAlgebra_smul_lieSmoothVectors_def
    (u : UniversalEnvelopingAlgebra ℝ (LeftInvariantDerivation I G)) (w : lieSmoothVectors I π) :
    u • w = lieSmoothVectorsEnvelopingAction I π u w :=
  (rfl)

/-- The `U(𝔤)`-action on smooth vectors commutes with the coefficients. -/
instance instSMulCommClassUniversalEnvelopingAlgebraLieSmoothVectors :
    SMulCommClass (UniversalEnvelopingAlgebra ℝ (LeftInvariantDerivation I G)) R
      (lieSmoothVectors I π) where
  smul_comm u r w := by
    simp only [envelopingAlgebra_smul_lieSmoothVectors_def, map_smul]

end Enveloping

section BaseChange

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R : Type*} [CommRing R] [Module R V] (π : ContRepresentation R G V)
  [Algebra ℝ R] [IsScalarTower ℝ R V] [ContinuousConstSMul R V]

/-- **The derived action extended to `R ⊗[ℝ] 𝔤`.** For commutative coefficients `R`, the derived
representation extends `R`-linearly to the base change of the real Lie algebra; for a complex
representation this is the complex-linear extension to `𝔤 = Lie(G) ⊗ ℂ`. -/
def lieSmoothVectorsBaseChangeDerivedAction :
    R ⊗[ℝ] LeftInvariantDerivation I G →ₗ⁅R⁆ Module.End R (lieSmoothVectors I π) :=
  LieHom.liftBaseChange R (lieSmoothVectorsDerivedAction I π)

/-- The extended derived action sends `a ⊗ X` to `a • dπ(X)`; for a complex representation,
`dπ(i ⊗ X) = i • dπ(X)`. -/
@[simp]
theorem lieSmoothVectorsBaseChangeDerivedAction_tmul (a : R) (X : LeftInvariantDerivation I G) :
    lieSmoothVectorsBaseChangeDerivedAction I π (a ⊗ₜ X) = a • lieSmoothVectorsDerivative I π X :=
  (LieHom.liftBaseChange_tmul R (lieSmoothVectorsDerivedAction I π) a X).trans
    (by rw [lieSmoothVectorsDerivedAction_apply])

/-- The action of the enveloping algebra `U(R ⊗[ℝ] 𝔤)` on the smooth vectors, extending the
derived action of `R ⊗[ℝ] 𝔤`. -/
def lieSmoothVectorsBaseChangeEnvelopingAction :
    UniversalEnvelopingAlgebra R (R ⊗[ℝ] LeftInvariantDerivation I G) →ₐ[R]
      Module.End R (lieSmoothVectors I π) :=
  UniversalEnvelopingAlgebra.lift R (lieSmoothVectorsBaseChangeDerivedAction I π)

/-- An element of `R ⊗[ℝ] 𝔤` acts on smooth vectors by its extended derived endomorphism. -/
theorem lieSmoothVectorsBaseChangeEnvelopingAction_ι (x : R ⊗[ℝ] LeftInvariantDerivation I G) :
    lieSmoothVectorsBaseChangeEnvelopingAction I π (UniversalEnvelopingAlgebra.ι R x) =
      lieSmoothVectorsBaseChangeDerivedAction I π x := by
  rw [lieSmoothVectorsBaseChangeEnvelopingAction, UniversalEnvelopingAlgebra.lift_ι_apply]

/-- `lieSmoothVectorsBaseChangeEnvelopingAction_ι` in `simp`-normal form, where the canonical map
into `U(R ⊗[ℝ] 𝔤)` is written through the tensor algebra. -/
@[simp]
theorem lieSmoothVectorsBaseChangeEnvelopingAction_mkAlgHom_ι
    (x : R ⊗[ℝ] LeftInvariantDerivation I G) :
    lieSmoothVectorsBaseChangeEnvelopingAction I π
        (UniversalEnvelopingAlgebra.mkAlgHom R (R ⊗[ℝ] LeftInvariantDerivation I G)
          (TensorAlgebra.ι R x)) =
      lieSmoothVectorsBaseChangeDerivedAction I π x :=
  lieSmoothVectorsBaseChangeEnvelopingAction_ι I π x

/-- An element `a ⊗ X` of `R ⊗[ℝ] 𝔤` acts on smooth vectors by `a • dπ(X)`. -/
theorem lieSmoothVectorsBaseChangeEnvelopingAction_ι_tmul (a : R)
    (X : LeftInvariantDerivation I G) :
    lieSmoothVectorsBaseChangeEnvelopingAction I π (UniversalEnvelopingAlgebra.ι R (a ⊗ₜ X)) =
      a • lieSmoothVectorsDerivative I π X := by
  simp [UniversalEnvelopingAlgebra.ι_apply]

/-- **The `U(R ⊗[ℝ] 𝔤)`-module of smooth vectors**, through
`lieSmoothVectorsBaseChangeEnvelopingAction`. -/
instance instModuleUniversalEnvelopingAlgebraTensorProductLieSmoothVectors :
    Module (UniversalEnvelopingAlgebra R (R ⊗[ℝ] LeftInvariantDerivation I G))
      (lieSmoothVectors I π) :=
  Module.compHom _ (lieSmoothVectorsBaseChangeEnvelopingAction I π).toRingHom

/-- An element of `U(R ⊗[ℝ] 𝔤)` acts on a smooth vector through
`lieSmoothVectorsBaseChangeEnvelopingAction`. -/
theorem baseChangeEnvelopingAlgebra_smul_lieSmoothVectors_def
    (u : UniversalEnvelopingAlgebra R (R ⊗[ℝ] LeftInvariantDerivation I G))
    (w : lieSmoothVectors I π) :
    u • w = lieSmoothVectorsBaseChangeEnvelopingAction I π u w :=
  (rfl)

/-- **The smooth vectors are a Lie module over `R ⊗[ℝ] Lie(G)`**, through the extended derived
action: `⁅x, v⁆ = dπ(x) v`. -/
instance instLieRingModuleTensorProductLieSmoothVectors :
    LieRingModule (R ⊗[ℝ] LeftInvariantDerivation I G) (lieSmoothVectors I π) :=
  LieRingModule.compLieHom _ (lieSmoothVectorsBaseChangeDerivedAction I π)

/-- The bracket of `x ∈ R ⊗[ℝ] Lie(G)` with a smooth vector is the extended derived action. -/
theorem lie_lieSmoothVectors_def (x : R ⊗[ℝ] LeftInvariantDerivation I G)
    (v : lieSmoothVectors I π) : ⁅x, v⁆ = lieSmoothVectorsBaseChangeDerivedAction I π x v := by
  rw [LieRingModule.compLieHom_apply, Module.End.lie_apply]

/-- The bracket of `a ⊗ X` with a smooth vector is `a • dπ(X) v`. -/
@[simp]
theorem tmul_lie_lieSmoothVectors (a : R) (X : LeftInvariantDerivation I G)
    (v : lieSmoothVectors I π) : ⁅a ⊗ₜ[ℝ] X, v⁆ = a • lieSmoothVectorsDerivative I π X v := by
  rw [lie_lieSmoothVectors_def, lieSmoothVectorsBaseChangeDerivedAction_tmul, LinearMap.smul_apply]

/-- **The `R`-Lie module of smooth vectors** over `R ⊗[ℝ] Lie(G)`. -/
instance instLieModuleTensorProductLieSmoothVectors :
    LieModule R (R ⊗[ℝ] LeftInvariantDerivation I G) (lieSmoothVectors I π) :=
  LieModule.compLieHom _ (lieSmoothVectorsBaseChangeDerivedAction I π)

/-- **The `U(R ⊗[ℝ] 𝔤)`-representation of the Lie module of smooth vectors** is the enveloping
action `lieSmoothVectorsBaseChangeEnvelopingAction`. -/
@[simp]
theorem representation_lieSmoothVectors :
    TauCeti.UniversalEnvelopingAlgebra.representation R (R ⊗[ℝ] LeftInvariantDerivation I G)
        (lieSmoothVectors I π) =
      lieSmoothVectorsBaseChangeEnvelopingAction I π := by
  refine UniversalEnvelopingAlgebra.hom_ext R (LieHom.ext fun x ↦ ?_)
  rw [LieHom.comp_apply, LieHom.comp_apply, AlgHom.toLieHom_apply, AlgHom.toLieHom_apply,
    TauCeti.UniversalEnvelopingAlgebra.representation_ι,
    lieSmoothVectorsBaseChangeEnvelopingAction_ι]
  exact LinearMap.ext fun v ↦ by rw [LieModule.toEnd_apply_apply, lie_lieSmoothVectors_def]

end BaseChange

end ContRepresentation
