/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.TensorProduct.Galois
public import TauCeti.Algebra.Coalgebra.BaseChange
import Mathlib.RingTheory.Flat.Basic
import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# Galois descent of bialgebra morphisms

A morphism between scalar-extended bialgebras over a Galois extension descends uniquely
if and only if it commutes with the Galois action on the scalar factor. The descended algebra
morphism preserves the counit and comultiplication, since these identities can be checked after
the injective scalar extension. For Hopf algebras, antipode compatibility then follows from
the usual bialgebra-morphism theorem.

This permits descent of morphisms between affine groups from equivariant morphisms over a
splitting field, without first identifying their coordinate algebras with invariant group algebras.
Neither finite type nor commutativity of the bialgebras is required.

## Main declarations

* `BialgHom.galoisDescend`: descent of an equivariant bialgebra morphism.
* `BialgHom.map_galoisDescend`: scalar extension recovers the original morphism.
* `BialgHom.existsUnique_map_eq_iff`: equivariance characterizes unique descent.

## References

* J. S. Milne, *Algebraic Groups* (2017), Appendix A.64.
-/

public section

open scoped TensorProduct

namespace BialgHom

variable {k L A B : Type*} [Field k] [Field L] [Algebra k L]
variable [Semiring A] [Semiring B] [Bialgebra k A] [Bialgebra k B]
variable [IsGalois k L]

variable (F : L ⊗[k] A →ₐc[L] L ⊗[k] B)
variable (hF : ∀ (σ : L ≃ₐ[k] L) (x : L ⊗[k] A),
  F (TensorProduct.map σ.toLinearMap LinearMap.id x) =
    TensorProduct.map σ.toLinearMap LinearMap.id (F x))

private theorem galoisDescend_counit :
    (Bialgebra.counitAlgHom k B).comp (F.toAlgHom.galoisDescend hF) =
      Bialgebra.counitAlgHom k A := by
  ext a
  apply (algebraMap k L).injective
  have h := congrArg (Coalgebra.counit (R := L))
    (F.toAlgHom.one_tmul_galoisDescend hF a)
  simpa [Algebra.algebraMap_eq_smul_one] using h

-- Naturality of the tensor-square comparison for the particular map being descended.
private theorem galoisDescend_tensor (x : A ⊗[k] A) :
    TensorProduct.map (F : L ⊗[k] A →ₗ[L] L ⊗[k] B) F
        (TensorProduct.AlgebraTensorModule.distribBaseChange k L A A (1 ⊗ₜ[k] x)) =
      TensorProduct.AlgebraTensorModule.distribBaseChange k L B B
        (1 ⊗ₜ[k] Algebra.TensorProduct.map
          (F.toAlgHom.galoisDescend hF) (F.toAlgHom.galoisDescend hF) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy]
  | tmul a b =>
      simp only [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, coe_toLinearMap]
      exact congrArg₂ (fun x y : L ⊗[k] B ↦ x ⊗ₜ[L] y)
        (F.toAlgHom.one_tmul_galoisDescend hF a).symm
        (F.toAlgHom.one_tmul_galoisDescend hF b).symm

private theorem galoisDescend_comul :
    (Algebra.TensorProduct.map (F.toAlgHom.galoisDescend hF)
        (F.toAlgHom.galoisDescend hF)).comp (Bialgebra.comulAlgHom k A) =
      (Bialgebra.comulAlgHom k B).comp (F.toAlgHom.galoisDescend hF) := by
  let := Module.addCommMonoidToAddCommGroup k (M := B)
  ext a
  apply Algebra.TensorProduct.includeRight_injective (A := L) (algebraMap k L).injective
  apply (TensorProduct.AlgebraTensorModule.distribBaseChange k L B B).injective
  simp only [Algebra.TensorProduct.includeRight_apply, AlgHom.comp_apply,
    Bialgebra.comulAlgHom_apply]
  rw [← galoisDescend_tensor F hF, ← TauCeti.Coalgebra.baseChange_comul_tmul,
    CoalgHomClass.map_comp_comul_apply, ← coe_toAlgHom F,
    ← AlgHom.one_tmul_galoisDescend F.toAlgHom hF,
    TauCeti.Coalgebra.baseChange_comul_tmul]

/-- Descent of a bialgebra morphism commuting with the scalar-factor Galois action.
Counit and comultiplication compatibility descend along with the algebra map. -/
noncomputable def galoisDescend : A →ₐc[k] B :=
  BialgHom.ofAlgHom (F.toAlgHom.galoisDescend hF)
    (galoisDescend_counit F hF) (galoisDescend_comul F hF)

/-- The algebra map underlying bialgebra descent is algebra descent. -/
@[simp]
theorem galoisDescend_toAlgHom :
    (F.galoisDescend hF).toAlgHom = F.toAlgHom.galoisDescend hF := (rfl)

/-- Descent recovers the given map on elements of the original bialgebra. -/
@[simp]
theorem one_tmul_galoisDescend (a : A) :
    1 ⊗ₜ[k] F.galoisDescend hF a = F (1 ⊗ₜ[k] a) := by
  simpa only [← coe_toAlgHom, galoisDescend_toAlgHom] using
    F.toAlgHom.one_tmul_galoisDescend hF a

/-- Extending a descended bialgebra morphism recovers the original morphism. -/
@[simp]
theorem map_galoisDescend :
    Bialgebra.TensorProduct.map (BialgHom.id L L) (F.galoisDescend hF) = F := by
  apply BialgHom.coe_toAlgHom_injective
  simpa only [Bialgebra.TensorProduct.map_toAlgHom, id_toAlgHom,
    galoisDescend_toAlgHom] using F.toAlgHom.map_galoisDescend hF

/-- A bialgebra morphism over a Galois extension descends uniquely exactly when it
commutes with the scalar-factor Galois action. In particular this applies to coordinate Hopf
algebras of affine group schemes. -/
theorem existsUnique_map_eq_iff :
    (∃! f : A →ₐc[k] B, Bialgebra.TensorProduct.map (BialgHom.id L L) f = F) ↔
      ∀ (σ : L ≃ₐ[k] L) (x : L ⊗[k] A),
        F (TensorProduct.map σ.toLinearMap LinearMap.id x) =
          TensorProduct.map σ.toLinearMap LinearMap.id (F x) := by
  constructor
  · rintro ⟨f, rfl, _⟩ σ x
    exact TauCeti.ScalarAut.baseChangeMap_smul f.toAlgHom σ x
  · intro hF
    let := Module.addCommMonoidToAddCommGroup k (M := B)
    refine ⟨F.galoisDescend hF, F.map_galoisDescend hF, fun f hf ↦ ?_⟩
    ext a
    apply Algebra.TensorProduct.includeRight_injective (A := L) (algebraMap k L).injective
    have h := DFunLike.congr_fun hf (1 ⊗ₜ[k] a)
    simpa using h.trans (F.one_tmul_galoisDescend hF a).symm

end BialgHom
