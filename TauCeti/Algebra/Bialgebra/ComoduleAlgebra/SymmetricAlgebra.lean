/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Bialgebra.ComoduleAlgebra
public import TauCeti.Algebra.Coalgebra.Comodule.SymmetricAlgebra.Basic
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Grading

/-!
# Symmetric algebras of comodules as comodule algebras

This file equips the symmetric algebra of a comodule with its natural comodule-algebra structure.
It also records that homogeneous components of coinvariants remain coinvariant and constructs the
equivariant algebra map induced by the inclusion of a subcomodule into a comodule algebra.

## Main declarations

* `TauCeti.ComoduleAlgebra.symmetricAlgebra`: the comodule-algebra structure on the symmetric
  algebra of a comodule.
* `TauCeti.ComoduleAlgebra.decompose_mem_coinvariants_symmetricAlgebra`: homogeneous components
  of a coinvariant in a symmetric algebra are coinvariant.
* `TauCeti.ComoduleAlgebra.liftSubcomoduleHom`: the equivariant algebra map from the symmetric
  algebra of a subcomodule into a comodule algebra.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace ComoduleAlgebra

universe u v w

section SymmetricAlgebra

variable {R : Type*} {H : Type*} {M : Type*} [CommSemiring R] [CommSemiring H] [Bialgebra R H]
  [AddCommMonoid M] [Module R M] [Comodule R H M]

variable (R H M) in
/-- The symmetric algebra of a comodule over a commutative bialgebra is a comodule algebra, with
the multiplicative coaction `TauCeti.Comodule.symmetricAlgebraCoact`.

Like `TauCeti.Comodule.symmetricAlgebra`, this is not a global instance. -/
@[implicit_reducible]
noncomputable def symmetricAlgebra : ComoduleAlgebra R H (SymmetricAlgebra R M) where
  toComodule := Comodule.symmetricAlgebra R H M
  coact_one := by rw [Comodule.symmetricAlgebra_coact, AlgHom.toLinearMap_apply, map_one]
  coact_mul x y := by rw [Comodule.symmetricAlgebra_coact, AlgHom.toLinearMap_apply,
    AlgHom.toLinearMap_apply, AlgHom.toLinearMap_apply, map_mul]

attribute [local instance] symmetricAlgebra

/-- The homogeneous components of an invariant of the symmetric algebra of a comodule are
invariant. -/
theorem decompose_mem_coinvariants_symmetricAlgebra {x : SymmetricAlgebra R M}
    (hx : x ∈ coinvariants R H (SymmetricAlgebra R M)) (n : ℕ) :
    (DirectSum.decompose (SymmetricAlgebra.homogeneousSubmodule R M) x n : SymmetricAlgebra R M) ∈
      coinvariants R H (SymmetricAlgebra R M) := by
  rw [← SetLike.mem_coe, coe_coinvariants] at hx ⊢
  exact Comodule.decompose_mem_fixedSubcomodule _
    (fun _ _ hy ↦ by
      rw [Comodule.symmetricAlgebra_coact, AlgHom.toLinearMap_apply]
      exact Comodule.symmetricAlgebraCoact_mem_decomposeTensor hy) hx n

end SymmetricAlgebra

section Lift

variable {k : Type u} [Field k] {H : Type v} [CommSemiring H] [Bialgebra k H]
  {A : Type w} [CommRing A] [Algebra k A] [ComoduleAlgebra k H A]

attribute [local instance] symmetricAlgebra

/-- The algebra homomorphism from the symmetric algebra of a subcomodule of a comodule algebra,
extending the inclusion, is a comodule morphism. -/
noncomputable def liftSubcomoduleHom [Module.Flat k H] (V : Subcomodule k H A) :
    Comodule.Hom k H (SymmetricAlgebra k V) A where
  toLinearMap := (SymmetricAlgebra.lift (SMulMemClass.subtype V)).toLinearMap
  map_coact := by
    have h : (Algebra.TensorProduct.map (SymmetricAlgebra.lift (SMulMemClass.subtype V))
        (AlgHom.id k H)).comp (Comodule.symmetricAlgebraCoact k H V) =
        (coactAlgHom k H A).comp (SymmetricAlgebra.lift (SMulMemClass.subtype V)) := by
      apply SymmetricAlgebra.algHom_ext
      ext v
      simp only [← AlgHom.toLinearMap_eq_coe, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        AlgHom.comp_apply, Comodule.symmetricAlgebraCoact_ι, SymmetricAlgebra.lift_ι_apply,
        coactAlgHom_apply]
      rw [SMulMemClass.coe_subtype, ← Subcomodule.subtype_rTensor_coact V v]
      induction Comodule.coact (R := k) (C := H) v using TensorProduct.inductionOn with
      | tmul w h => simp
      | add x y hx hy => simp only [map_add, hx, hy]
    simpa [TensorProduct.AlgebraTensorModule.map_eq] using congrArg AlgHom.toLinearMap h

/-- The underlying map of the equivariant lift is the symmetric-algebra lift. -/
@[simp]
theorem liftSubcomoduleHom_apply [Module.Flat k H] (V : Subcomodule k H A)
    (x : SymmetricAlgebra k V) :
    liftSubcomoduleHom V x = SymmetricAlgebra.lift (SMulMemClass.subtype V) x :=
  (rfl)

end Lift

end ComoduleAlgebra

end TauCeti
