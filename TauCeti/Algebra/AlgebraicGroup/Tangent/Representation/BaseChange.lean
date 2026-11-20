/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Representation
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Representation.PointsAction.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Representation.Comodule.Morphism
public import TauCeti.Algebra.Coalgebra.Convolution.BaseChange

/-!
# Base change of the adjoint representation

Let `H` be a commutative Hopf algebra over `R` whose augmentation cotangent space is finite
projective, and let `S` be a commutative `R`-algebra. The Lie algebra of `Spec H` is the
`R`-module `𝔤 = Module.Dual R (Bialgebra.CotangentSpace R H)`, and that of its base change
`Spec (S ⊗[R] H)` is `𝔤_S = Module.Dual S (Bialgebra.CotangentSpace S (S ⊗[R] H))`.

`Derivation.cotangentDualBaseChangeEquiv` (from
`TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.BaseChange`) identifies `S ⊗[R] 𝔤` with `𝔤_S`, with
no flatness assumption.

The main result, `Derivation.map_coact_cotangentDualBaseChangeEquiv`, says that this
identification is a morphism of comodules from the base change of the adjoint comodule of `H`
(`TauCeti.Comodule.baseChange`) to the adjoint comodule of `S ⊗[R] H`: **the adjoint
representation commutes with base change.** The proof compares the two point actions. A point
of `S ⊗[R] H` is the base change of a point of `H`, and the adjoint action of a point is
convolution conjugation of tangent vectors (`Derivation.adDerivation`); restricted along
`h ↦ 1 ⊗ h`, the convolution over `S ⊗[R] H` becomes the convolution over `H`
(`Derivation.adDerivation_apply_one_tmul`).

## Main declarations

* `Derivation.adDerivation_apply_one_tmul`: the adjoint action over `S ⊗[R] H`, evaluated on
  `1 ⊗ h`, is the adjoint action over `H` of the restricted point and tangent vector.
* `Derivation.map_coact_cotangentDualBaseChangeEquiv`: **the identification is colinear for the
  adjoint coactions.**

## References

* J. S. Milne, *Algebraic Groups* (2017), §10.a and §14 (base change of the Lie algebra and the
  adjoint representation).
-/

public section

open scoped TensorProduct
open WithConv TauCeti

namespace Derivation

variable {R S H : Type*} [CommRing R] [CommRing S] [Algebra R S] [CommRing H]

variable [HopfAlgebra R H]

/-- **The adjoint action commutes with restriction along `h ↦ 1 ⊗ h`.** If a point `g'` and a
tangent vector `D'` of `H` are the restrictions of a point `g` and a tangent vector `D` of
`S ⊗[R] H`, all with values in `A`, then `Ad g D` evaluated on `1 ⊗ h` is `Ad g' D'` evaluated on
`h`. -/
theorem adDerivation_apply_one_tmul {A : Type*} [CommRing A] [Algebra S A] [Algebra R A]
    (g : WithConv (S ⊗[R] H →ₐ[S] Bialgebra.CounitAlgebra S (S ⊗[R] H) A))
    (D : Derivation S (S ⊗[R] H) (Bialgebra.CounitAlgebra S (S ⊗[R] H) A))
    (g' : WithConv (H →ₐ[R] Bialgebra.CounitAlgebra R H A))
    (D' : Derivation R H (Bialgebra.CounitAlgebra R H A))
    (hg : ∀ h, Bialgebra.CounitAlgebra.algEquivSelf R H A (g'.ofConv h) =
      Bialgebra.CounitAlgebra.algEquivSelf S (S ⊗[R] H) A (g.ofConv (1 ⊗ₜ h)))
    (hD : ∀ h, Bialgebra.CounitAlgebra.algEquivSelf R H A (D' h) =
      Bialgebra.CounitAlgebra.algEquivSelf S (S ⊗[R] H) A (D (1 ⊗ₜ h))) (h : H) :
    Bialgebra.CounitAlgebra.algEquivSelf S (S ⊗[R] H) A (adDerivation A g D (1 ⊗ₜ h)) =
      Bialgebra.CounitAlgebra.algEquivSelf R H A (adDerivation A g' D' h) := by
  let ψ : Bialgebra.CounitAlgebra S (S ⊗[R] H) A →+* Bialgebra.CounitAlgebra R H A :=
    (Bialgebra.CounitAlgebra.algEquivSelf R H A).symm.toRingEquiv.toRingHom.comp
      (Bialgebra.CounitAlgebra.algEquivSelf S (S ⊗[R] H) A).toRingEquiv.toRingHom
  have hψ (x) : Bialgebra.CounitAlgebra.algEquivSelf R H A (ψ x) =
      Bialgebra.CounitAlgebra.algEquivSelf S (S ⊗[R] H) A x :=
    (Bialgebra.CounitAlgebra.algEquivSelf R H A).apply_symm_apply _
  rw [adDerivation_apply, adDerivation_apply, ← hψ]
  congr 1
  refine LinearMap.map_convMul_apply_one_tmul ψ _ _ _ _
    (LinearMap.map_convMul_apply_one_tmul ψ _ _ _ _ ?_ ?_) ?_ h
  · intro c
    apply (Bialgebra.CounitAlgebra.algEquivSelf R H A).injective
    exact (hψ _).trans (hg c).symm
  · intro c
    apply (Bialgebra.CounitAlgebra.algEquivSelf R H A).injective
    exact (hψ _).trans (hD c).symm
  · intro c
    apply (Bialgebra.CounitAlgebra.algEquivSelf R H A).injective
    simp only [hψ, AlgHom.toLinearMap_apply, WithConv.algHom_inv_apply,
      TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul,
      HopfAlgebra.antipode_one]
    exact (hg _).symm

section Adjoint

universe u v

variable {R S : Type u} {H : Type v} [CommRing R] [CommRing S] [Algebra R S] [CommRing H]
  [HopfAlgebra R H]
  [Module.Finite R (Bialgebra.CotangentSpace R H)]
  [Module.Projective R (Bialgebra.CotangentSpace R H)]
  [Module.Finite S (Bialgebra.CotangentSpace S (S ⊗[R] H))]
  [Module.Projective S (Bialgebra.CotangentSpace S (S ⊗[R] H))]

/-- Transported through the base-change comparison, an `A`-valued tangent vector of `H` becomes the
`A`-valued tangent vector of `S ⊗[R] H` whose value on `1 ⊗ h` is its value on `h`. -/
private theorem tangentScalarExtensionEquiv_cancelBaseChange_apply_one_tmul
    {A : Type*} [CommRing A] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    (z : A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) (h : H) :
    Bialgebra.CounitAlgebra.algEquivSelf S (S ⊗[R] H) A
        (tangentScalarExtensionEquiv (R := S) (A := S ⊗[R] H) (B := A)
          ((cotangentDualBaseChangeEquiv R S H).baseChange S A _ _
            ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S A A _).symm z))
          (1 ⊗ₜ h)) =
      Bialgebra.CounitAlgebra.algEquivSelf R H A
        (tangentScalarExtensionEquiv (R := R) (A := H) (B := A) z h) := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, _root_.add_apply, hx, hy]
  | tmul a x =>
    rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul,
      LinearEquiv.baseChange_tmul, algEquivSelf_tangentScalarExtensionEquiv_tmul_apply,
      cotangentDualBaseChangeEquiv_tmul_apply_cotangentMap,
      algEquivSelf_tangentScalarExtensionEquiv_tmul_apply, one_mul,
      ← IsScalarTower.algebraMap_apply]

/-- The point action of the adjoint comodule of `S ⊗[R] H` at the base change of a point `f` of
`H` is the point action of `f` on the adjoint comodule of `H`, transported through the
base-change comparison. -/
private theorem endOfPoint_liftEquiv_baseChange_cancelBaseChange_symm
    {A : Type (max u v)} [CommRing A] [Algebra S A] [Algebra R A] [IsScalarTower R S A]
    (f : H →ₐ[R] A) (z : A ⊗[R] Module.Dual R (Bialgebra.CotangentSpace R H)) :
    (letI := adjointComodule (R := S) (H := S ⊗[R] H)
     Comodule.endOfPoint (Module.Dual S (Bialgebra.CotangentSpace S (S ⊗[R] H)))
      (AlgHom.liftEquiv R S H A f)
      ((cotangentDualBaseChangeEquiv R S H).baseChange S A _ _
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S A A _).symm z))) =
      (cotangentDualBaseChangeEquiv R S H).baseChange S A _ _
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S A A _).symm
          (letI := adjointComodule (R := R) (H := H)
           Comodule.endOfPoint (Module.Dual R (Bialgebra.CotangentSpace R H)) f z)) := by
  apply (tangentScalarExtensionEquiv (R := S) (A := S ⊗[R] H) (B := A)).injective
  have hS := tangentScalarExtensionEquiv_adjointComodule_endOfPoint (R := S) (H := S ⊗[R] H)
    (CommAlgCat.of S A) (toConv (AlgHom.liftEquiv R S H A f))
    ((cotangentDualBaseChangeEquiv R S H).baseChange S A _ _
        ((TensorProduct.AlgebraTensorModule.cancelBaseChange R S A A _).symm z))
  have hR := tangentScalarExtensionEquiv_adjointComodule_endOfPoint (R := R) (H := H)
    (CommAlgCat.of R A) (toConv f) z
  rw [hS]
  ext w
  induction w using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s h =>
    rw [← mul_one s, ← smul_eq_mul, ← TensorProduct.smul_tmul', Derivation.map_smul,
      Derivation.map_smul]
    congr 1
    apply (Bialgebra.CounitAlgebra.algEquivSelf S (S ⊗[R] H) A).injective
    rw [tangentScalarExtensionEquiv_cancelBaseChange_apply_one_tmul]
    rw [hR]
    rw [adDerivation_apply_one_tmul _ _ (pointInCounitAlgebra (CommAlgCat.of R A) (toConv f))
      (tangentScalarExtensionEquiv (R := R) (A := H) (B := A) z)]
    · intro h
      simp only [pointInCounitAlgebra_apply, AlgHom.liftEquiv_tmul, one_smul]
      exact (Bialgebra.CounitAlgebra.algEquivSelf_apply _ _ _ _).trans
        (Bialgebra.CounitAlgebra.algEquivSelf_apply _ _ _ _).symm
    · intro h
      exact (tangentScalarExtensionEquiv_cancelBaseChange_apply_one_tmul z h).symm

/-- **The adjoint representation commutes with base change.** The identification
`S ⊗[R] 𝔤 ≃ₗ[S] 𝔤_S` intertwines the base change of the adjoint coaction of `H` with the adjoint
coaction of `S ⊗[R] H`.

The base ring and its extension share a universe, so that the value algebras of the two point
actions can be compared in one category. -/
theorem map_coact_cotangentDualBaseChangeEquiv :
    letI := adjointComodule (R := R) (H := H)
    TensorProduct.map (cotangentDualBaseChangeEquiv R S H).toLinearMap LinearMap.id ∘ₗ
        (Comodule.baseChange (R := R) (H := H)
          (M := Module.Dual R (Bialgebra.CotangentSpace R H)) S).coact =
      (adjointComodule (R := S) (H := S ⊗[R] H)).coact ∘ₗ
        (cotangentDualBaseChangeEquiv R S H).toLinearMap := by
  let _ := adjointComodule (R := R) (H := H)
  refine (HopfAlgebra.PointRepresentation.map_coact_iff_baseChange_comp_endOfPoint _ _ _).mpr ?_
  intro A p
  let _ : Algebra R A := ((algebraMap S A).comp (algebraMap R S)).toAlgebra
  have _ : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨f, hf⟩ := (AlgHom.liftEquiv R S H A).surjective p.ofConv
  rw [← hf]
  apply LinearMap.ext
  intro w
  obtain ⟨z, rfl⟩ := (TensorProduct.AlgebraTensorModule.cancelBaseChange R S A A
    (Module.Dual R (Bialgebra.CotangentSpace R H))).symm.surjective w
  have h := LinearMap.congr_fun (Comodule.cancelBaseChange_conjRingEquiv_endOfPoint_liftEquiv
    (k := R) (K := S) (H := H) (M := Module.Dual R (Bialgebra.CotangentSpace R H)) f) z
  rw [LinearEquiv.conjRingEquiv_apply_apply] at h
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← LinearEquiv.coe_baseChange,
    LinearEquiv.coe_coe, (LinearEquiv.eq_symm_apply _).mpr h,
    endOfPoint_liftEquiv_baseChange_cancelBaseChange_symm]

end Adjoint

end Derivation
