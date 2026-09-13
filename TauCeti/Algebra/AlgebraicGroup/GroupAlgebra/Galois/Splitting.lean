/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GroupAlgebra.Galois.Hopf
public import Mathlib.RingTheory.HopfAlgebra.TensorProduct

/-!
# Splitting the descended group algebra

For a finite Galois extension `L/k` and an integral representation on an abelian group `M`,
scalar extension of the invariant coordinate Hopf algebra recovers `L[M]` as a bialgebra.
The equivalence sends `a ⊗ x` to `a • x`. Thus it identifies the descended affine group
after extension to its splitting field with the diagonalizable group of `M`.

The underlying algebra equivalence is `groupAlgebraInvariantsBaseChangeEquiv`. We prove
that it respects the descended counit and comultiplication, using
`groupAlgebraInvariantsTensorEquiv` to compare the tensor squares. Neither finite generation
of `M` nor a restriction on the characteristic is needed.

## References

* J. S. Milne, *Algebraic Groups* (2017), Theorem 12.23 and Appendix A.64.
-/

public section

open scoped TensorProduct

namespace TauCeti.GaloisDescent

variable {k L M : Type*} [Field k] [Field L] [Algebra k L] [AddCommGroup M]
variable [FiniteDimensional k L] [IsGalois k L]
variable (rho : Representation ℤ (L ≃ₐ[k] L) M)

/-- The split coordinate algebra. -/
local notation "A" => MonoidAlgebra L (Multiplicative M)
/-- The descended coordinate algebra. -/
local notation "B" => groupAlgebraInvariants rho

private theorem splitting_counit_comp :
    (Bialgebra.counitAlgHom L A).comp
        (groupAlgebraInvariantsBaseChangeEquiv rho).toAlgHom =
      Bialgebra.counitAlgHom L (L ⊗[k] B) := by
  apply Algebra.TensorProduct.ext'
  intro a x
  simp [Algebra.smul_def, mul_comm]

private theorem splitting_map_comp_comul :
    (Algebra.TensorProduct.map
        (groupAlgebraInvariantsBaseChangeEquiv rho).toAlgHom
        (groupAlgebraInvariantsBaseChangeEquiv rho).toAlgHom).comp
      (Bialgebra.comulAlgHom L (L ⊗[k] B)) =
    (Bialgebra.comulAlgHom L A).comp
      (groupAlgebraInvariantsBaseChangeEquiv rho).toAlgHom := by
  apply Algebra.TensorProduct.ext'
  intro a x
  have h (t : B ⊗[k] B) :
      Algebra.TensorProduct.map
          (groupAlgebraInvariantsBaseChangeEquiv rho).toAlgHom
          (groupAlgebraInvariantsBaseChangeEquiv rho).toAlgHom
        (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm
          k L k L L L B B ((1 ⊗ₜ[L] a) ⊗ₜ[k] t)) =
        a • (groupAlgebraInvariantsTensorEquiv rho t : A ⊗[L] A) := by
    induction t using TensorProduct.induction_on with
    | zero =>
        simp only [TensorProduct.tmul_zero, LinearEquiv.map_zero]
        simp
    | tmul y z => simp [TensorProduct.tmul_smul]
    | add y z hy hz =>
        simp only [TensorProduct.tmul_add, LinearEquiv.map_add]
        simp only [map_add, AddMemClass.coe_add, hy, hz, smul_add]
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply,
    TensorProduct.comul_tmul, CommSemiring.comul_apply, h,
    groupAlgebraInvariantsTensorEquiv_comul, groupAlgebraInvariantsComul_apply,
    AlgEquiv.coe_toAlgHom, groupAlgebraInvariantsBaseChangeEquiv_tmul,
    map_smul]

/-- Extending the descended group algebra to its splitting field recovers the split group
algebra as a bialgebra, with the standard scalar-extension Hopf structure on the source. -/
noncomputable def groupAlgebraInvariantsBaseChangeBialgEquiv :
    L ⊗[k] B ≃ₐc[L] A :=
  BialgEquiv.ofAlgEquiv (groupAlgebraInvariantsBaseChangeEquiv rho)
    (splitting_counit_comp rho) (splitting_map_comp_comul rho)

/-- Forgetting the coalgebra structure recovers the scalar-extension algebra equivalence. -/
@[simp]
theorem groupAlgebraInvariantsBaseChangeBialgEquiv_toAlgEquiv :
    (groupAlgebraInvariantsBaseChangeBialgEquiv rho).toAlgEquiv =
      groupAlgebraInvariantsBaseChangeEquiv rho := by
  rfl

/-- On pure tensors the splitting isomorphism is scalar multiplication. -/
@[simp]
theorem groupAlgebraInvariantsBaseChangeBialgEquiv_tmul (a : L) (x : B) :
    groupAlgebraInvariantsBaseChangeBialgEquiv rho (a ⊗ₜ[k] x) = a • (x : A) := by
  rw [← BialgEquiv.coe_toAlgEquiv, groupAlgebraInvariantsBaseChangeBialgEquiv_toAlgEquiv,
    groupAlgebraInvariantsBaseChangeEquiv_tmul]

/-- An invariant split element corresponds to its tensor with one under the inverse splitting. -/
@[simp]
theorem groupAlgebraInvariantsBaseChangeBialgEquiv_symm_apply (x : B) :
    (groupAlgebraInvariantsBaseChangeBialgEquiv rho).symm (x : A) = 1 ⊗ₜ[k] x := by
  apply EquivLike.injective (groupAlgebraInvariantsBaseChangeBialgEquiv rho)
  rw [BialgEquiv.apply_symm_apply, groupAlgebraInvariantsBaseChangeBialgEquiv_tmul, one_smul]

end TauCeti.GaloisDescent
