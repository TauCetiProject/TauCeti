/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.BaseChange.Hom
public import TauCeti.Algebra.Lie.NormTwoShell.FixedBasis
public import TauCeti.Algebra.Lie.Subalgebra.Fixed

/-!
# Scalar extension of the pinned shell fixed lattice

For a pinned diagram action on the signed shell Lie algebra, the canonical map from the
scalar extension of its integral fixed lattice into the scalar-extended fixed module is always
injective. It is surjective exactly when there are no negative root cycles or the coefficient
ring has no `2`-torsion. Thus it is an equivalence over every ring without `2`-torsion, without
requiring flatness over `ℤ`. When negative cycles occur, the criterion also detects the extra
fixed vectors in characteristic two.

The comparison is the existing `LinearMap.fixedSubmoduleBaseChange`, not an independently
chosen map. The signed-permutation description of the Cartan/root basis identifies the obstruction
via `Module.Basis.fixedSubmoduleBaseChange_signedPerm_surjective_iff`: the Cartan cycles all have
positive signs, so only root cycles contribute. When `B` is positive definite with even diagonal,
`IsBaseChange.lieEquiv` upgrades this linear equivalence to the `A`-Lie algebra isomorphism
`Matrix.ShellLieAlgebra.fixedSubalgebraBaseChangeLieEquiv` induced by the canonical `ℤ`-Lie map
`Matrix.ShellLieAlgebra.toFixedSubalgebraBaseChange`. This compares the actual integral fixed
lattice, not a normalized folded Chevalley lattice.

## References

* V. G. Kac, *Infinite dimensional Lie algebras*, third edition, §§7.8–7.9.
-/

public section

open TensorProduct

namespace Matrix.ShellLieAlgebra

variable {I : Type*} [Fintype I] [LinearOrder I] {B : Matrix I I ℤ}
  (σ : Equiv.Perm I) (hσ : B.reindex σ σ = B) [Finite B.normTwoShell]
  (A : Type*) [CommRing A]

/-- Scalar extension embeds the integral fixed lattice of the pinned shell action. No
flatness or torsion hypothesis on the coefficient ring is needed. -/
theorem fixedSubmoduleBaseChange_injective :
    Function.Injective ((reindex σ hσ).toLinearMap.fixedSubmoduleBaseChange A) :=
  (basis B).fixedSubmoduleBaseChange_signedPerm_injective
    (Equiv.Perm.sumCongr σ (normTwoShellCongr hσ))
    (Sum.elim (1 : I → ℤˣ) (fun a ↦ inversionSign B σ a))
    (reindex σ hσ).toLinearMap (reindex_basis σ hσ) A

/-- Negative root cycles are the only obstruction to surjectivity of scalar extension of
the integral fixed lattice: each such cycle contributes the coefficient ring's `2`-torsion. -/
theorem fixedSubmoduleBaseChange_surjective_iff :
    Function.Surjective ((reindex σ hσ).toLinearMap.fixedSubmoduleBaseChange A) ↔
      IsEmpty {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
        monodromy σ hσ C = -1} ∨ Submodule.torsionBy A A 2 = ⊥ := by
  rw [(basis B).fixedSubmoduleBaseChange_signedPerm_surjective_iff
    (Equiv.Perm.sumCongr σ (normTwoShellCongr hσ))
    (Sum.elim (1 : I → ℤˣ) (fun a ↦ inversionSign B σ a))
    (reindex σ hσ).toLinearMap (reindex_basis σ hσ)
    (Sum.map Quotient.out Quotient.out) (existsUnique_sameCycle_basis σ hσ) A]
  exact or_congr_left (negativeCycleEquiv σ hσ).isEmpty_congr

/-- If there are no negative root cycles or the coefficient ring has no `2`-torsion, the
actual scalar-extension comparison for the integral fixed lattice is an equivalence. -/
noncomputable def fixedSubmoduleBaseChangeEquiv
    (hA : IsEmpty {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
      monodromy σ hσ C = -1} ∨ Submodule.torsionBy A A 2 = ⊥) :
    A ⊗[ℤ] (reindex σ hσ).toLinearMap.fixedSubmodule ≃ₗ[A]
      ((reindex σ hσ).toLinearMap.baseChange A).fixedSubmodule :=
  LinearEquiv.ofBijective ((reindex σ hσ).toLinearMap.fixedSubmoduleBaseChange A)
    ⟨fixedSubmoduleBaseChange_injective σ hσ A,
      (fixedSubmoduleBaseChange_surjective_iff σ hσ A).mpr hA⟩

/-- The equivalence is the canonical scalar extension of the fixed-lattice inclusion. -/
@[simp]
theorem fixedSubmoduleBaseChangeEquiv_apply
    (hA : IsEmpty {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
      monodromy σ hσ C = -1} ∨ Submodule.torsionBy A A 2 = ⊥)
    (x : A ⊗[ℤ] (reindex σ hσ).toLinearMap.fixedSubmodule) :
    fixedSubmoduleBaseChangeEquiv σ hσ A hA x =
      (reindex σ hσ).toLinearMap.fixedSubmoduleBaseChange A x := by
  rfl

section FixedSubalgebra

variable [Fact B.PosDef] [Fact (∀ i, Even (B i i))]

omit [Finite B.normTwoShell] in
/-- The underlying submodule of the integral fixed Lie subalgebra of
`reindexLieEquiv σ hσ Fact.out Fact.out` is the fixed submodule of `reindex σ hσ`. -/
theorem toSubmodule_fixedSubalgebra_reindexLieEquiv :
    (reindexLieEquiv σ hσ Fact.out Fact.out).toLieHom.fixedSubalgebra.toSubmodule =
      (reindex σ hσ).toLinearMap.fixedSubmodule := by
  rw [LieHom.fixedSubalgebra_toSubmodule]
  exact congrArg LinearMap.fixedSubmodule (LinearMap.ext (reindexLieEquiv_apply σ hσ _ _))

omit [Finite B.normTwoShell] in
/-- After extension of scalars to `A`, the underlying submodule of the fixed Lie subalgebra of
`LieEquiv.baseChange A (reindexLieEquiv σ hσ Fact.out Fact.out)` is the fixed submodule of
`(reindex σ hσ).toLinearMap.baseChange A`. -/
theorem toSubmodule_fixedSubalgebra_baseChange_reindexLieEquiv :
    (LieEquiv.baseChange A
        (reindexLieEquiv σ hσ Fact.out Fact.out)).toLieHom.fixedSubalgebra.toSubmodule =
      ((reindex σ hσ).toLinearMap.baseChange A).fixedSubmodule := by
  rw [LieHom.fixedSubalgebra_toSubmodule, LieEquiv.toLieHom_baseChange, LieHom.coe_baseChange]
  refine congrArg (fun f : ShellLieAlgebra B →ₗ[ℤ] ShellLieAlgebra B ↦
    (f.baseChange A).fixedSubmodule) ?_
  exact LinearMap.ext (reindexLieEquiv_apply σ hσ _ _)

omit [Finite B.normTwoShell] in
/-- Canonical `ℤ`-Lie homomorphism embedding the integral fixed Lie subring of
`reindexLieEquiv σ hσ Fact.out Fact.out` into the fixed Lie subalgebra after scalar extension to
`A`, sending `v` to `1 ⊗ₜ[ℤ] v`. -/
noncomputable def toFixedSubalgebraBaseChange :
    (reindexLieEquiv σ hσ Fact.out Fact.out).toLieHom.fixedSubalgebra →ₗ⁅ℤ⁆
      (LieEquiv.baseChange A
        (reindexLieEquiv σ hσ Fact.out Fact.out)).toLieHom.fixedSubalgebra where
  toFun v := ⟨1 ⊗ₜ[ℤ] (v : ShellLieAlgebra B), by
    rw [LieHom.mem_fixedSubalgebra, LieEquiv.toLieHom_baseChange, LieHom.baseChange_tmul,
      LieHom.mem_fixedSubalgebra.mp v.property]⟩
  map_add' x y := Subtype.ext (TensorProduct.tmul_add 1 (x : ShellLieAlgebra B)
    (y : ShellLieAlgebra B))
  map_smul' n x := Subtype.ext <| by
    simp [TensorProduct.tmul_smul]
  map_lie' {x y} := Subtype.ext <| by
    simp

omit [Finite B.normTwoShell] in
@[simp]
theorem coe_toFixedSubalgebraBaseChange
    (v : (reindexLieEquiv σ hσ Fact.out Fact.out).toLieHom.fixedSubalgebra) :
    (toFixedSubalgebraBaseChange σ hσ A v : A ⊗[ℤ] ShellLieAlgebra B) =
      1 ⊗ₜ[ℤ] (v : ShellLieAlgebra B) :=
  (rfl)

omit [Finite B.normTwoShell] in
private noncomputable def fixedSubalgebraBaseChangeLinearEquiv
    (hA : IsEmpty {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
      monodromy σ hσ C = -1} ∨ Submodule.torsionBy A A 2 = ⊥) :
    A ⊗[ℤ] (reindexLieEquiv σ hσ Fact.out Fact.out).toLieHom.fixedSubalgebra ≃ₗ[A]
      (LieEquiv.baseChange A (reindexLieEquiv σ hσ Fact.out Fact.out)).toLieHom.fixedSubalgebra :=
  haveI : Finite B.normTwoShell := (Fact.out : B.PosDef).finite_normTwoShell.to_subtype
  ((LinearEquiv.ofEq _ _
    (toSubmodule_fixedSubalgebra_reindexLieEquiv σ hσ)).baseChange ℤ A _ _).trans
    ((fixedSubmoduleBaseChangeEquiv σ hσ A hA).trans
      (LinearEquiv.ofEq _ _
        (toSubmodule_fixedSubalgebra_baseChange_reindexLieEquiv σ hσ A).symm))

omit [Finite B.normTwoShell] in
/-- Whenever there are no negative root cycles or `A` has no `2`-torsion,
`toFixedSubalgebraBaseChange` exhibits the fixed Lie subalgebra after scalar extension as the base
change of the integral fixed Lie subring. -/
theorem isBaseChange_toFixedSubalgebraBaseChange
    (hA : IsEmpty {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
      monodromy σ hσ C = -1} ∨ Submodule.torsionBy A A 2 = ⊥) :
    IsBaseChange A (toFixedSubalgebraBaseChange σ hσ A).toLinearMap := by
  have : Finite B.normTwoShell := (Fact.out : B.PosDef).finite_normTwoShell.to_subtype
  refine IsBaseChange.of_equiv (fixedSubalgebraBaseChangeLinearEquiv σ hσ A hA)
    fun v ↦ Subtype.ext ?_
  rw [fixedSubalgebraBaseChangeLinearEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.baseChange_tmul, fixedSubmoduleBaseChangeEquiv_apply,
    LinearEquiv.coe_ofEq_apply, LinearMap.fixedSubmoduleBaseChange_tmul,
    LinearEquiv.coe_ofEq_apply, LieHom.coe_toLinearMap, coe_toFixedSubalgebraBaseChange]

omit [Finite B.normTwoShell] in
/-- If there are no negative root cycles or the coefficient ring `A` has no `2`-torsion, the
scalar extension of the integral fixed Lie subring is canonically isomorphic as an `A`-Lie algebra
to the fixed Lie subalgebra of the scalar-extended pinned diagram action. -/
noncomputable def fixedSubalgebraBaseChangeLieEquiv
    (hA : IsEmpty {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
      monodromy σ hσ C = -1} ∨ Submodule.torsionBy A A 2 = ⊥) :
    A ⊗[ℤ] (reindexLieEquiv σ hσ Fact.out Fact.out).toLieHom.fixedSubalgebra ≃ₗ⁅A⁆
      (LieEquiv.baseChange A (reindexLieEquiv σ hσ Fact.out Fact.out)).toLieHom.fixedSubalgebra :=
  (isBaseChange_toFixedSubalgebraBaseChange σ hσ A hA).lieEquiv

omit [Finite B.normTwoShell] in
theorem fixedSubalgebraBaseChangeLieEquiv_tmul
    (hA : IsEmpty {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
      monodromy σ hσ C = -1} ∨ Submodule.torsionBy A A 2 = ⊥) (a : A)
    (v : (reindexLieEquiv σ hσ Fact.out Fact.out).toLieHom.fixedSubalgebra) :
    fixedSubalgebraBaseChangeLieEquiv σ hσ A hA (a ⊗ₜ[ℤ] v) =
      a • toFixedSubalgebraBaseChange σ hσ A v :=
  (isBaseChange_toFixedSubalgebraBaseChange σ hσ A hA).lieEquiv_tmul a v

omit [Finite B.normTwoShell] in
@[simp]
theorem coe_fixedSubalgebraBaseChangeLieEquiv_tmul
    (hA : IsEmpty {C : Quotient (Equiv.Perm.SameCycle.setoid (normTwoShellCongr hσ)) //
      monodromy σ hσ C = -1} ∨ Submodule.torsionBy A A 2 = ⊥) (a : A)
    (v : (reindexLieEquiv σ hσ Fact.out Fact.out).toLieHom.fixedSubalgebra) :
    (fixedSubalgebraBaseChangeLieEquiv σ hσ A hA (a ⊗ₜ[ℤ] v) :
        A ⊗[ℤ] ShellLieAlgebra B) =
      a ⊗ₜ[ℤ] (v : ShellLieAlgebra B) := by
  rw [fixedSubalgebraBaseChangeLieEquiv_tmul, SetLike.val_smul, coe_toFixedSubalgebraBaseChange,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end FixedSubalgebra

end Matrix.ShellLieAlgebra
