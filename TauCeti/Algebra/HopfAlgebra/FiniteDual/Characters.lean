/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.FiniteDual.Basic
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.GroupLike
public import Mathlib.LinearAlgebra.TensorProduct.Projective
public import TauCeti.RingTheory.IntegralClosure.CharacterDescent
import TauCeti.Algebra.Coalgebra.Convolution

/-!
# Characters of the convolution dual

Evaluation identifies the group-like elements of a finite projective coalgebra with the
algebra homomorphisms from its convolution dual to the base. No multiplication on the
coalgebra is required. Over a commutative ring integrally closed in an extension, every
extension-valued character descends uniquely to the base, so it too is evaluation at a
unique group-like element.

## References

* J. S. Milne, *Algebraic Groups* (2017), Section 11.c and Aside 11.17,
  https://www.jmilne.org/math/Books/iAG2017.pdf.
-/

public section

open scoped TensorProduct

namespace TauCeti.ConvolutionDual

section Coalgebra

variable (R A : Type*) [CommSemiring R] [AddCommMonoid A] [Module R A] [Coalgebra R A]

/-- Evaluation at a group-like element is a character of the convolution dual. -/
noncomputable def evalGroupLike (u : GroupLike R A) : ConvolutionDual R A →ₐ[R] R :=
  AlgHom.ofLinearMap
    ((Module.Dual.eval R A u.val).comp (WithConv.linearEquiv R _).toLinearMap)
    (by simpa only [LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      WithConv.linearEquiv_apply, Module.Dual.eval_apply, LinearMap.convOne_apply,
      Algebra.algebraMap_self_apply] using u.isGroupLikeElem_val.counit_eq_one)
    (fun f g ↦ u.isGroupLikeElem_val.ofConv_convMul_apply f g)

/-- The character associated to a group-like element evaluates the underlying functional. -/
@[simp, grind =]
theorem evalGroupLike_apply (u : GroupLike R A) (f : ConvolutionDual R A) :
    evalGroupLike R A u f = f.ofConv u.val := (rfl)

variable [Module.Finite R A] [Module.Projective R A]

private noncomputable def characterElement (f : ConvolutionDual R A →ₐ[R] R) : A :=
  (Module.evalEquiv R A).symm
    (f.toLinearMap.comp (WithConv.linearEquiv R _).symm.toLinearMap)

private theorem characterElement_apply (f : ConvolutionDual R A →ₐ[R] R)
    (φ : ConvolutionDual R A) : φ.ofConv (characterElement R A f) = f φ := by
  simp [characterElement]

private theorem isGroupLikeElem_characterElement (f : ConvolutionDual R A →ₐ[R] R) :
    IsGroupLikeElem R (characterElement R A f) where
  counit_eq_one := by
    simpa only [LinearMap.convOne_apply, Algebra.algebraMap_self_apply, map_one] using
      characterElement_apply R A f 1
  comul_eq_tmul_self := by
    -- Tensor products of dual functionals span the dual of the tensor square.
    apply (Module.evalEquiv R (A ⊗[R] A)).injective
    apply LinearMap.ext
    intro l
    obtain ⟨w, rfl⟩ := (dualDistribEquiv R A).surjective l
    induction w using TensorProduct.inductionOn with
    | add w z hw hz => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) hw hz
    | tmul φ ψ =>
      simp only [Module.evalEquiv_apply, Module.Dual.eval_apply,
        dualDistribEquiv_tmul_apply, characterElement_apply]
      rw [← map_mul, ← characterElement_apply R A f (φ * ψ), LinearMap.convMul_apply]
      generalize Coalgebra.comul (R := R) (characterElement R A f) = t
      induction t using TensorProduct.inductionOn with
      | add t s ht hs => simpa only [map_add, LinearMap.add_apply] using congrArg₂ (· + ·) ht hs
      | tmul x y => simp [dualDistribEquiv_tmul_apply]

private noncomputable def characterGroupLike (f : ConvolutionDual R A →ₐ[R] R) :
    GroupLike R A :=
  ⟨characterElement R A f, isGroupLikeElem_characterElement R A f⟩

private theorem characterGroupLike_apply (f : ConvolutionDual R A →ₐ[R] R)
    (φ : ConvolutionDual R A) : φ.ofConv (characterGroupLike R A f).val = f φ :=
  characterElement_apply R A f φ

/-- Group-like elements of a finite projective coalgebra correspond to characters of its
convolution dual, by evaluation. -/
noncomputable def groupLikeEquivAlgHom :
    GroupLike R A ≃ (ConvolutionDual R A →ₐ[R] R) where
  toFun := evalGroupLike R A
  invFun := characterGroupLike R A
  left_inv u := by
    apply GroupLike.val_injective
    apply (Module.evalEquiv R A).injective
    ext φ
    simpa only [WithConv.ofConv_toConv, evalGroupLike_apply, Module.evalEquiv_apply,
      Module.Dual.eval_apply] using
      characterGroupLike_apply R A (evalGroupLike R A u) (WithConv.toConv φ)
  right_inv f := by
    ext φ
    simp only [evalGroupLike_apply, characterGroupLike_apply]

/-- The group-like/character equivalence sends a group-like element to evaluation at it. -/
@[simp, grind =]
theorem groupLikeEquivAlgHom_apply (u : GroupLike R A) (f : ConvolutionDual R A) :
    groupLikeEquivAlgHom R A u f = f.ofConv u.val := (rfl)

/-- The inverse character correspondence is characterized by evaluation. -/
@[simp, grind =]
theorem groupLikeEquivAlgHom_symm_apply_apply (f : ConvolutionDual R A →ₐ[R] R)
    (φ : ConvolutionDual R A) :
    φ.ofConv ((groupLikeEquivAlgHom R A).symm f).val = f φ := by
  simpa only [groupLikeEquivAlgHom_apply] using
    DFunLike.congr_fun ((groupLikeEquivAlgHom R A).apply_symm_apply f) φ

end Coalgebra

section AlgebraEvaluation

variable (R A : Type*) [CommSemiring R] [Semiring A] [Algebra R A] [Coalgebra R A]
  [Module.Finite R A] [Module.Projective R A]

/-- The underlying linear map of a group-like character is double-dual evaluation. -/
@[simp, grind =]
theorem toConv_groupLikeEquivAlgHom_toLinearMap (u : GroupLike R A) :
    WithConv.toConv (groupLikeEquivAlgHom R A u).toLinearMap = evalAlgEquiv R A u.val := by
  apply WithConv.ofConv_injective
  ext φ
  simp

end AlgebraEvaluation

section Bialgebra

variable (R A : Type*) [CommSemiring R] [Semiring A] [Bialgebra R A]
  [Module.Finite R A] [Module.Projective R A]

/-- For a finite projective bialgebra, evaluation respects multiplication, where characters
carry convolution multiplication. -/
noncomputable def groupLikeMulEquivAlgHom :
    GroupLike R A ≃* WithConv (ConvolutionDual R A →ₐ[R] R) :=
  MulEquiv.mk'
    ((groupLikeEquivAlgHom R A).trans (WithConv.equiv _).symm)
    (fun u v ↦ by
      apply WithConv.ofConv_injective
      apply AlgHom.toLinearMap_injective
      apply WithConv.toConv_injective
      simp only [Equiv.trans_apply, WithConv.symm_equiv_apply, WithConv.ofConv_toConv,
        AlgHom.toLinearMap_convMul, toConv_groupLikeEquivAlgHom_toLinearMap,
        GroupLike.val_mul, map_mul])

/-- The multiplicative character correspondence is evaluation. -/
@[simp, grind =]
theorem groupLikeMulEquivAlgHom_apply (u : GroupLike R A) (φ : ConvolutionDual R A) :
    (groupLikeMulEquivAlgHom R A u).ofConv φ = φ.ofConv u.val := (rfl)

/-- Evaluation at the inverse multiplicative character correspondence recovers the character. -/
@[simp, grind =]
theorem groupLikeMulEquivAlgHom_symm_apply_apply
    (f : WithConv (ConvolutionDual R A →ₐ[R] R)) (φ : ConvolutionDual R A) :
    φ.ofConv ((groupLikeMulEquivAlgHom R A).symm f).val = f.ofConv φ := by
  simpa only [groupLikeMulEquivAlgHom_apply] using
    DFunLike.congr_fun
      (congrArg WithConv.ofConv ((groupLikeMulEquivAlgHom R A).apply_symm_apply f)) φ

end Bialgebra

section Rationality

variable (R A S : Type*) [CommRing R] [AddCommMonoid A] [Module R A] [Coalgebra R A]
  [Module.Finite R A] [Module.Projective R A] [CommRing S] [Algebra R S]
  [IsIntegrallyClosedIn R S]

/-- If the base ring is integrally closed in the coefficient algebra, its group-like elements
correspond to all coefficient-valued characters of the finite convolution dual. -/
noncomputable def groupLikeEquivAlgHomOfIsIntegrallyClosedIn :
    GroupLike R A ≃ (ConvolutionDual R A →ₐ[R] S) :=
  (groupLikeEquivAlgHom R A).trans
    (algHomEquivOfIsIntegrallyClosedIn R (ConvolutionDual R A) S)

/-- The rational character correspondence composes evaluation at a group-like element with
the algebra map into the coefficient ring. -/
@[simp, grind =]
theorem groupLikeEquivAlgHomOfIsIntegrallyClosedIn_apply (u : GroupLike R A)
    (φ : ConvolutionDual R A) :
    groupLikeEquivAlgHomOfIsIntegrallyClosedIn R A S u φ = algebraMap R S (φ.ofConv u.val) := by
  simp only [groupLikeEquivAlgHomOfIsIntegrallyClosedIn, Equiv.trans_apply,
    algHomEquivOfIsIntegrallyClosedIn_apply, groupLikeEquivAlgHom_apply]

/-- Evaluation at the inverse rational character correspondence recovers the character. -/
@[simp, grind =]
theorem algebraMap_groupLikeEquivAlgHomOfIsIntegrallyClosedIn_symm_apply_apply
    (f : ConvolutionDual R A →ₐ[R] S) (φ : ConvolutionDual R A) :
    algebraMap R S
      (φ.ofConv ((groupLikeEquivAlgHomOfIsIntegrallyClosedIn R A S).symm f).val) = f φ := by
  simpa only [groupLikeEquivAlgHomOfIsIntegrallyClosedIn_apply] using
    DFunLike.congr_fun
      ((groupLikeEquivAlgHomOfIsIntegrallyClosedIn R A S).apply_symm_apply f) φ

/-- Every extension-valued character is evaluation at a unique group-like element over the
base ring. -/
theorem existsUnique_groupLike_algHom (f : ConvolutionDual R A →ₐ[R] S) :
    ∃! u : GroupLike R A, ∀ φ : ConvolutionDual R A, f φ = algebraMap R S (φ.ofConv u.val) := by
  let e := groupLikeEquivAlgHomOfIsIntegrallyClosedIn R A S
  refine ⟨e.symm f, ?_, ?_⟩
  · intro φ
    simpa only [e, groupLikeEquivAlgHomOfIsIntegrallyClosedIn_apply] using
      (DFunLike.congr_fun (e.apply_symm_apply f) φ).symm
  · intro u hu
    apply e.injective
    rw [e.apply_symm_apply]
    apply AlgHom.ext
    intro φ
    simpa only [e, groupLikeEquivAlgHomOfIsIntegrallyClosedIn_apply] using (hu φ).symm

end Rationality

end TauCeti.ConvolutionDual
