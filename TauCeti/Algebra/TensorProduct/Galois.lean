/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.RepresentationTheory.GaloisDescent.Range
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic
import TauCeti.Algebra.TensorProduct.BaseChange

/-!
# Galois invariants of a scalar extension

For a finite Galois extension `L/k`, the elements of `L ⊗[k] A` fixed by the scalar-factor
action are precisely the tensors `1 ⊗ a`. This identifies the original vector space inside its
scalar extension, in arbitrary characteristic. An algebra morphism between scalar extensions
therefore descends uniquely if and only if it commutes with the scalar-factor Galois action.
This supplies the underlying algebra map for descent of coordinate bialgebra morphisms.

## Main declarations

* `TauCeti.GaloisDescent.tensorProduct_forall_map_eq_self_iff_exists_one_tmul_eq`: the fixed
  tensors are exactly those coming from the original vector space.
* `AlgHom.galoisDescend`: descent of an equivariant algebra morphism.
* `AlgHom.existsUnique_map_eq_iff`: equivariance characterizes unique descent.

## References

* J. S. Milne, *Algebraic Groups* (2017), Appendix A.64.
-/

public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

variable {k L A : Type*} [Field k] [Field L] [Algebra k L]
variable [AddCommGroup A] [Module k A] [FiniteDimensional k L] [IsGalois k L]

/-- The fixed elements of a scalar extension along a finite Galois extension are exactly
the image of the original vector space. -/
theorem tensorProduct_forall_map_eq_self_iff_exists_one_tmul_eq (x : L ⊗[k] A) :
    (∀ σ : L ≃ₐ[k] L, TensorProduct.map σ.toLinearMap LinearMap.id x = x) ↔
      ∃ a : A, 1 ⊗ₜ[k] a = x := by
  let ρ : Representation k (L ≃ₐ[k] L) (L ⊗[k] A) :=
    { toFun := fun σ ↦ TensorProduct.map σ.toLinearMap LinearMap.id
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp }
  let f : A →ₗ[k] L ⊗[k] A := TensorProduct.mk k L A 1
  have hrange : LinearMap.range f = ρ.invariants :=
    GaloisDescent.range_eq_invariants_of_liftBaseChange_surjective
      (k := k) (L := L) (ρ := ρ) (f := f)
      (fun σ a y ↦ by
        induction y using TensorProduct.inductionOn with
        | add x y hx hy => simp only [smul_add, map_add, hx, hy]
        | tmul b c => simp [ρ, TensorProduct.smul_tmul', map_mul])
      (fun σ a ↦ by simp [ρ, f])
      (fun y ↦ ⟨y, by
        induction y using TensorProduct.inductionOn with
        | add x y hx hy => simp only [map_add, hx, hy]
        | tmul a b =>
            simp only [LinearMap.liftBaseChange_tmul, f, TensorProduct.mk_apply]
            exact (TensorProduct.smul_tmul' a (1 : L) b).trans (by simp)⟩)
  have hx : (∀ σ : L ≃ₐ[k] L, TensorProduct.map σ.toLinearMap LinearMap.id x = x) ↔
      x ∈ ρ.invariants := by
    simp [Representation.mem_invariants, ρ]
  rw [hx, ← hrange]
  simp only [LinearMap.mem_range, f, TensorProduct.mk_apply]

end TauCeti.GaloisDescent

namespace AlgHom

variable {k L A B : Type*} [Field k] [Field L] [Algebra k L]
variable [Semiring A] [Semiring B] [Algebra k A] [Algebra k B]
variable [FiniteDimensional k L] [IsGalois k L]

variable (F : L ⊗[k] A →ₐ[L] L ⊗[k] B)
variable (hF : ∀ (σ : L ≃ₐ[k] L) (x : L ⊗[k] A),
  F (TensorProduct.map σ.toLinearMap LinearMap.id x) =
    TensorProduct.map σ.toLinearMap LinearMap.id (F x))

include hF in
private theorem galoisDescend_mem_range (a : A) :
    ((F.restrictScalars k).comp Algebra.TensorProduct.includeRight) a ∈
      (Algebra.TensorProduct.includeRight : B →ₐ[k] L ⊗[k] B).range := by
  let := Module.addCommMonoidToAddCommGroup k (M := B)
  apply (TauCeti.GaloisDescent.tensorProduct_forall_map_eq_self_iff_exists_one_tmul_eq
    (F (1 ⊗ₜ[k] a))).mp
  intro σ
  simpa using (hF σ (1 ⊗ₜ[k] a)).symm

/-- Descent of an algebra morphism commuting with the scalar-factor Galois action.
Its scalar extension is the original morphism. -/
noncomputable def galoisDescend : A →ₐ[k] B := by
  letI := Module.addCommMonoidToAddCommGroup k (M := B)
  exact (AlgEquiv.ofInjective Algebra.TensorProduct.includeRight
    (Algebra.TensorProduct.includeRight_injective (algebraMap k L).injective)).symm.toAlgHom.comp
      (((F.restrictScalars k).comp Algebra.TensorProduct.includeRight).codRestrict _
        (galoisDescend_mem_range F hF))

/-- The descended morphism is characterized on the original algebra inside its scalar extension. -/
@[simp]
theorem one_tmul_galoisDescend (a : A) :
    1 ⊗ₜ[k] F.galoisDescend hF a = F (1 ⊗ₜ[k] a) := by
  let := Module.addCommMonoidToAddCommGroup k (M := B)
  let e := AlgEquiv.ofInjective (Algebra.TensorProduct.includeRight : B →ₐ[k] L ⊗[k] B)
    (Algebra.TensorProduct.includeRight_injective (algebraMap k L).injective)
  let g := ((F.restrictScalars k).comp Algebra.TensorProduct.includeRight).codRestrict _
    (galoisDescend_mem_range F hF)
  have h := congrArg Subtype.val (e.apply_symm_apply (g a))
  simpa only [e, AlgEquiv.ofInjective_apply, Algebra.TensorProduct.includeRight_apply,
    g, AlgHom.coe_codRestrict, AlgHom.comp_apply, AlgHom.restrictScalars_apply,
    galoisDescend, AlgEquiv.coe_toAlgHom] using h

/-- Extending a descended algebra morphism recovers the given equivariant morphism. -/
@[simp]
theorem map_galoisDescend :
    Algebra.TensorProduct.map (AlgHom.id L L) (F.galoisDescend hF) = F := by
  apply Algebra.TensorProduct.ext'
  intro l a
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    TensorProduct.tmul_eq_smul_one_tmul l a, map_smul,
    ← one_tmul_galoisDescend F hF, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- An algebra morphism over a finite Galois extension descends uniquely exactly when it
commutes with the scalar-factor Galois action. -/
theorem existsUnique_map_eq_iff :
    (∃! f : A →ₐ[k] B, Algebra.TensorProduct.map (AlgHom.id L L) f = F) ↔
      ∀ (σ : L ≃ₐ[k] L) (x : L ⊗[k] A),
        F (TensorProduct.map σ.toLinearMap LinearMap.id x) =
          TensorProduct.map σ.toLinearMap LinearMap.id (F x) := by
  constructor
  · rintro ⟨f, rfl, _⟩ σ x
    exact TauCeti.ScalarAut.baseChangeMap_smul f σ x
  · intro hF
    let := Module.addCommMonoidToAddCommGroup k (M := B)
    refine ⟨F.galoisDescend hF, F.map_galoisDescend hF, fun f hf ↦ ?_⟩
    ext a
    apply Algebra.TensorProduct.includeRight_injective (A := L) (algebraMap k L).injective
    have h := DFunLike.congr_fun hf (1 ⊗ₜ[k] a)
    simpa using h.trans (F.one_tmul_galoisDescend hF a).symm

end AlgHom
