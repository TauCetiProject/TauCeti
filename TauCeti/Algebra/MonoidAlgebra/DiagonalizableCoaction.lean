/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import TauCeti.Algebra.Group.Submonoid.NSMulSaturation
public import TauCeti.Algebra.MonoidAlgebra.Coaction

/-!
# Diagonalizable-group coaction and point action on semigroup algebras

For an additive submonoid `S` of an abelian group `G`, `AddSubmonoid.diagonalizableCoaction R`
defines the native `R[AddSubgroup.closure (S : Set G)]`-comodule algebra structure on `R[S]`,
obtained by specializing `AddMonoidAlgebra.gradedCoaction` to `S.toGroupClosure`. This file also
records saturation equivariance and the induced multiplicative action of `A`-valued characters
`Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ` on `AddMonoidAlgebra R S →ₐ[R] A`.

## Main declarations

* `AddSubmonoid.diagonalizableCoaction`: native diagonalizable-group coaction on `R[S]`.
* `AddSubmonoid.map_inclusion_nsmulSaturation_comp_diagonalizableCoaction`: saturation equivariance.
* `AddSubmonoid.instSMulCharAlgHom`, `AddSubmonoid.instMulActionCharAlgHom`: point action.
-/

public section

open scoped TensorProduct
open AddMonoidAlgebra

namespace AddSubmonoid

section DiagonalizableCoaction

variable {G : Type*} [AddCommGroup G] (S : AddSubmonoid G) (R : Type*) [CommSemiring R]

/-- The native coaction of the diagonalizable-group algebra `R[AddSubgroup.closure S]` on `R[S]`
(which is a split-torus coaction when `AddSubgroup.closure S` is finite-rank free abelian, e.g.
when `S.FG` and `G` is torsion-free). -/
noncomputable def diagonalizableCoaction :
    AddMonoidAlgebra R S →ₐ[R]
      AddMonoidAlgebra R (AddSubgroup.closure (S : Set G)) ⊗[R] AddMonoidAlgebra R S :=
  gradedCoaction R S.toGroupClosure

/-- Explicit definition of `AddSubmonoid.diagonalizableCoaction`. -/
theorem diagonalizableCoaction_def :
    S.diagonalizableCoaction R = gradedCoaction R S.toGroupClosure := (rfl)

/-- `S.diagonalizableCoaction R` sends `single s r` to
`single (S.toGroupClosure s) 1 ⊗ₜ single s r`. -/
@[simp]
theorem diagonalizableCoaction_single (s : S) (r : R) :
    S.diagonalizableCoaction R (single s r) = single (S.toGroupClosure s) 1 ⊗ₜ[R] single s r :=
  gradedCoaction_single R S.toGroupClosure s r

/-- The positive-multiple saturation inclusion from `R[S]` to
`R[S.nsmulSaturation ⊓ AddSubgroup.closure S]` is equivariant for the diagonalizable-group
algebra `R[AddSubgroup.closure S]`. -/
theorem map_inclusion_nsmulSaturation_comp_diagonalizableCoaction :
    (Algebra.TensorProduct.map (AlgHom.id R _)
      (mapDomainAlgHom R R
        (inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure)))).comp
      (S.diagonalizableCoaction R) =
      (gradedCoaction R S.nsmulSaturationInfClosureToGroupClosure).comp
        (mapDomainAlgHom R R
          (inclusion (le_inf S.le_nsmulSaturation AddSubgroup.subset_closure))) := by
  simpa [diagonalizableCoaction] using map_mapDomain_comp_gradedCoaction R (g := .id _)
    (AddMonoidHom.ext fun s ↦ S.nsmulSaturationInfClosureToGroupClosure_inclusion_apply s)

end DiagonalizableCoaction

section DiagonalizableAction

variable {G : Type*} [AddCommGroup G] (S : AddSubmonoid G)
  {R A : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- Scalar action of `A`-points `Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ` on
`AddMonoidAlgebra R S →ₐ[R] A` induced by `S.diagonalizableCoaction R`. -/
noncomputable instance instSMulCharAlgHom :
    SMul (Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
      (AddMonoidAlgebra R S →ₐ[R] A) where
  smul χ x :=
    (Algebra.TensorProduct.lift
      (AddMonoidAlgebra.lift R A _ ((Units.coeHom A).comp χ)) x
      fun _ _ ↦ Commute.all _ _).comp (S.diagonalizableCoaction R)

/-- Explicit definition of the diagonalizable-group action on `A`-points. -/
theorem smul_algHom_def {S : AddSubmonoid G}
    (χ : Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
    (x : AddMonoidAlgebra R S →ₐ[R] A) :
    χ • x =
      (Algebra.TensorProduct.lift
        (AddMonoidAlgebra.lift R A _ ((Units.coeHom A).comp χ)) x
        fun _ _ ↦ Commute.all _ _).comp (S.diagonalizableCoaction R) := (rfl)

/-- Acting by `χ` scales `x (single s r)` by `χ (S.toGroupClosure s)`. -/
@[simp]
theorem smul_algHom_single_apply {S : AddSubmonoid G}
    (χ : Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
    (x : AddMonoidAlgebra R S →ₐ[R] A) (s : S) (r : R) :
    (χ • x) (single s r) = (χ (.ofAdd (S.toGroupClosure s)) : A) * x (single s r) := by
  rw [smul_algHom_def, AlgHom.comp_apply]; simp

/-- Multiplicative action of `A`-points `Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ`
on `AddMonoidAlgebra R S →ₐ[R] A` via `S.diagonalizableCoaction R`. -/
noncomputable instance instMulActionCharAlgHom :
    MulAction (Multiplicative (AddSubgroup.closure (S : Set G)) →* Aˣ)
      (AddMonoidAlgebra R S →ₐ[R] A) where
  one_smul x := by ext; simp
  mul_smul χ₁ χ₂ x := by ext; simp [mul_assoc]

end DiagonalizableAction

end AddSubmonoid
