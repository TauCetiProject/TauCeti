/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Henselization.Map
public import TauCeti.RingTheory.Henselian.Integral
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Integral base change of henselization

For an integral algebra `S` over `R`, the henselization of `(S, IS)` is canonically
`Rʰ ⊗[R] S`, where `Rʰ` is the henselization of `(R, I)`. No Noetherianity or
finiteness assumption is required. The comparison is an `S`-algebra equivalence,
characterized on the two tensor factors. The tensor product uses
`Algebra.TensorProduct.rightAlgebra` for its `S`-algebra structure.

The tensor product is integral over `Rʰ`, so it is henselian along the extended
ideal. The universal property of henselization supplies an inverse to the canonical
comparison; uniqueness of maps into henselian pairs proves the inverse laws.

## References

* Stacks Project, Lemma 15.12.7 (Tag 0DYE).
-/

public section

open TensorProduct

universe u v

namespace TauCeti.Henselization

variable {R : Type u} [CommRing R] (I : Ideal R)
  (S : Type v) [CommRing S] [Algebra R S]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The canonical comparison from the base change of a henselization to the
henselization of the base-changed pair. It exists for every algebra `S`. -/
noncomputable def baseChangeHom :
    (algebra I) ⊗[R] S →ₐ[S] algebra (I.map (algebraMap R S)) := by
  let : Algebra R (algebra (I.map (algebraMap R S))) :=
    ((algebraMap S (algebra (I.map (algebraMap R S)))).comp (algebraMap R S)).toAlgebra
  let : IsScalarTower R S (algebra (I.map (algebraMap R S))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact
    { toRingHom := (Algebra.TensorProduct.lift
        { toRingHom := map (algebraMap R S) le_rfl
          commutes' := map_algebraMap _ _ }
        (IsScalarTower.toAlgHom R S (algebra (I.map (algebraMap R S))))
        (fun _ _ ↦ .all _ _)).toRingHom
      commutes' s := by simp [Algebra.TensorProduct.right_algebraMap_apply] }

/-- On pure tensors the comparison is the product of the functorial map of
henselizations and the structure map from `S`. -/
@[simp]
theorem baseChangeHom_tmul (x : algebra I) (s : S) :
    baseChangeHom I S (x ⊗ₜ[R] s) =
      map (algebraMap R S) le_rfl x * algebraMap S (algebra (I.map (algebraMap R S))) s :=
  (rfl)

private theorem tensor_extended_eq :
    (extended I).map (algebraMap (algebra I) ((algebra I) ⊗[R] S)) =
      (I.map (algebraMap R S)).map (algebraMap S ((algebra I) ⊗[R] S)) := by
  simp only [extended, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- Integral base change of the henselization is henselian along the ideal
extended from `IS`. -/
instance henselianRing_tensorProduct [Algebra.IsIntegral R S] :
    HenselianRing ((algebra I) ⊗[R] S)
      ((I.map (algebraMap R S)).map (algebraMap S ((algebra I) ⊗[R] S))) := by
  rw [← tensor_extended_eq]
  infer_instance

private noncomputable def integralBaseChangeInv [Algebra.IsIntegral R S] :
    algebra (I.map (algebraMap R S)) →ₐ[S] (algebra I) ⊗[R] S :=
  lift le_rfl

private theorem integralBaseChangeInv_map [Algebra.IsIntegral R S] (x : algebra I) :
    integralBaseChangeInv I S (map (algebraMap R S) le_rfl x) = x ⊗ₜ[R] (1 : S) := by
  have h : (integralBaseChangeInv I S).toRingHom.comp (map (algebraMap R S) le_rfl) =
      Algebra.TensorProduct.includeLeftRingHom := by
    apply ringHom_ext_of_map_le_jacobson (I := I)
    · ext r
      simp only [RingHom.comp_apply, map_algebraMap]
      exact ((integralBaseChangeInv I S).commutes _).trans
        (DFunLike.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
          (R := R) (A := algebra I) (B := S)) r).symm
    · rw [RingHom.comp_assoc, map_comp_algebraMap, ← RingHom.comp_assoc]
      have heq : (integralBaseChangeInv I S).toRingHom.comp
          (algebraMap S (algebra (I.map (algebraMap R S)))) =
          algebraMap S ((algebra I) ⊗[R] S) :=
        (integralBaseChangeInv I S).comp_algebraMap
      rw [heq, ← Ideal.map_map]
      exact _root_.HenselianRing.jac.trans Ideal.jacobson_bot.ge
  exact DFunLike.congr_fun h x

/-- Henselization commutes with integral base change. The scalar structure on the
tensor product is through its `S` factor. -/
@[stacks 0DYE]
noncomputable def integralBaseChangeEquiv [Algebra.IsIntegral R S] :
    (algebra I) ⊗[R] S ≃ₐ[S] algebra (I.map (algebraMap R S)) :=
  AlgEquiv.ofAlgHom (baseChangeHom I S) (integralBaseChangeInv I S)
    (algHom_ext_of_map_le_jacobson (extended_le_jacobson _))
    (by
      apply AlgHom.restrictScalars_injective R
      apply Algebra.TensorProduct.ext
      · ext x
        simp [integralBaseChangeInv_map]
      · ext s
        simp [Algebra.TensorProduct.right_algebraMap_apply])

/-- The integral base-change equivalence has the canonical pure-tensor formula. -/
@[simp]
theorem integralBaseChangeEquiv_tmul [Algebra.IsIntegral R S] (x : algebra I) (s : S) :
    integralBaseChangeEquiv I S (x ⊗ₜ[R] s) =
      map (algebraMap R S) le_rfl x * algebraMap S (algebra (I.map (algebraMap R S))) s :=
  baseChangeHom_tmul I S x s

/-- The inverse comparison carries the functorial image of `Rʰ` to the left
factor of the tensor product. -/
@[simp]
theorem integralBaseChangeEquiv_symm_map [Algebra.IsIntegral R S] (x : algebra I) :
    (integralBaseChangeEquiv I S).symm (map (algebraMap R S) le_rfl x) =
      x ⊗ₜ[R] (1 : S) :=
  integralBaseChangeInv_map I S x

-- A diagonal extension is integral but need not be surjective. Thus the theorem
-- applies beyond quotient base change, even over a nonreduced base.
example :
    Nonempty ((algebra (Ideal.span {(3 : ZMod 9)})) ⊗[ZMod 9] (ZMod 9 × ZMod 9) ≃ₐ[ZMod 9 × ZMod 9]
      algebra ((Ideal.span {(3 : ZMod 9)}).map (algebraMap (ZMod 9) (ZMod 9 × ZMod 9)))) :=
  ⟨integralBaseChangeEquiv _ _⟩

-- The two components are retained: the inverse comparison sends the coordinate
-- idempotent to the right tensor factor, not to the scalar unit.
example :
    (integralBaseChangeEquiv (Ideal.span {(3 : ZMod 9)}) (ZMod 9 × ZMod 9)).symm
        (algebraMap (ZMod 9 × ZMod 9) _ (1, 0)) =
      (1 : algebra (Ideal.span {(3 : ZMod 9)})) ⊗ₜ[ZMod 9] (1, 0) := by
  simp [Algebra.TensorProduct.right_algebraMap_apply]

end TauCeti.Henselization
