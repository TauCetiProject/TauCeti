/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.Algebra.MonoidAlgebra.Basic
public import TauCeti.LinearAlgebra.Dual.RightAction
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Duality over a finite group algebra

For a finite group `G` and a commutative semiring `R`, the group algebra `R[G]` is a symmetric
Frobenius algebra. Taking the coefficient at the identity identifies the `R[G]`-linear dual
`Hom_{R[G]}(M, R[G])` with the `R`-linear dual `Hom_R(M, R)`. The action on the latter is the
contragredient action: `op a` sends `ψ` to the functional `m ↦ ψ(a • m)`.

This file constructs that equivalence explicitly and proves its naturality under precomposition.
The range statement is the bridge used to express an Auslander--Reiten transpose through an
ordinary base-ring dual.

## Main definitions

* `TauCeti.MonoidAlgebra.dualLinearEquiv`: the coefficient-at-one equivalence between the two
  duals.
* `TauCeti.MonoidAlgebra.contragredientDualMap`: precomposition on base-ring duals, equipped with
  the contragredient group-algebra action.
* `TauCeti.MonoidAlgebra.quotientRangeContragredientDualMapEquiv`: the cokernel of contragredient
  precomposition is, additively, the cokernel of the base-ring dual map.

## Main results

* `TauCeti.MonoidAlgebra.contragredientDualMap_eq_dualMap`: contragredient precomposition is the
  base-ring dual map.
* `TauCeti.MonoidAlgebra.map_range_lcomp_dualLinearEquiv`: the duality carries the range of
  group-algebra precomposition to the range of contragredient base-ring precomposition.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren 323,
  Springer (2008), (5.6.9).
-/

public section

noncomputable section

namespace TauCeti.MonoidAlgebra

section ContragredientAction

variable {R G M : Type*} [CommSemiring R] [Group G]
  [AddCommMonoid M] [Module (MonoidAlgebra R G) M] [Module R M]
  [SMulCommClass R (MonoidAlgebra R G) M]

/-- The contragredient action of a group algebra on a base-ring dual. -/
noncomputable instance instModuleDualContragredient :
    Module (MonoidAlgebra R G)ᵐᵒᵖ (Module.Dual R M) :=
  inferInstanceAs (Module (DomMulAct (MonoidAlgebra R G)) (Module.Dual R M))

/-- The contragredient group-algebra action on the base-ring dual is precomposition. -/
@[simp]
theorem _root_.MonoidAlgebra.op_smul_dual_apply (a : MonoidAlgebra R G) (ψ : Module.Dual R M)
    (m : M) :
    (MulOpposite.op a • ψ) m = ψ (a • m) := rfl

end ContragredientAction

section CoefficientMap

variable {R G M : Type*} [CommSemiring R] [Group G]
  [AddCommMonoid M] [Module (MonoidAlgebra R G) M] [Module R M]
  [IsScalarTower R (MonoidAlgebra R G) M]

private noncomputable def dualLinearMap :
    Module.Dual (MonoidAlgebra R G) M →ₗ[(MonoidAlgebra R G)ᵐᵒᵖ] Module.Dual R M where
  toFun φ :=
    { toFun := fun m => (φ m).coeff 1
      map_add' := fun x y => by simp
      map_smul' := fun r m => by
        calc
          (φ (r • m)).coeff 1 =
              (φ ((r • (1 : MonoidAlgebra R G)) • m)).coeff 1 := by
                rw [smul_assoc, one_smul]
          _ = ((r • (1 : MonoidAlgebra R G)) • φ m).coeff 1 := by rw [map_smul]
          _ = r • (φ m).coeff 1 := by simp }
  map_add' φ ψ := by ext m; rfl
  map_smul' a φ := by
    ext m
    -- Unfold only the two opposite actions; the remaining equality is symmetry of the
    -- coefficient-at-one pairing.
    change ((a • φ) m).coeff 1 = (φ (MulOpposite.unop a • m)).coeff 1
    simp only [LinearMap.smul_apply]
    rw [map_smul]
    exact _root_.MonoidAlgebra.coeff_one_mul_comm _ _

@[simp]
private theorem dualLinearMap_apply (φ : Module.Dual (MonoidAlgebra R G) M) (m : M) :
    dualLinearMap φ m = (φ m).coeff 1 := rfl

end CoefficientMap

section ContragredientMap

variable {R G M N : Type*} [CommSemiring R] [Group G]
  [AddCommMonoid M] [Module (MonoidAlgebra R G) M] [Module R M]
  [IsScalarTower R (MonoidAlgebra R G) M]
  [AddCommMonoid N] [Module (MonoidAlgebra R G) N] [Module R N]
  [IsScalarTower R (MonoidAlgebra R G) N]

/-- Precomposition with a group-algebra linear map, on base-ring duals equipped with the
contragredient action. -/
def contragredientDualMap (f : M →ₗ[MonoidAlgebra R G] N) :
    Module.Dual R N →ₗ[(MonoidAlgebra R G)ᵐᵒᵖ] Module.Dual R M where
  toFun ψ := ψ.comp (f.restrictScalars R)
  map_add' ψ χ := by ext m; simp
  map_smul' a ψ := by
    rcases a with ⟨a⟩
    ext m
    -- Both sides are precomposition by the action of `a`; expose this before using linearity.
    change ψ.toFun (a • f m) = ψ.toFun (f (a • m))
    rw [map_smul]

/-- Contragredient dual precomposition evaluates by applying the original map first. -/
@[simp]
theorem contragredientDualMap_apply (f : M →ₗ[MonoidAlgebra R G] N)
    (ψ : Module.Dual R N) (m : M) :
    contragredientDualMap f ψ m = ψ (f m) := by
  simp [contragredientDualMap]

/-- Contragredient dual precomposition is the base-ring dual map of `f`. -/
theorem contragredientDualMap_eq_dualMap (f : M →ₗ[MonoidAlgebra R G] N)
    (ψ : Module.Dual R N) :
    contragredientDualMap f ψ = (f.restrictScalars R).dualMap ψ :=
  LinearMap.ext fun m ↦ by
    rw [contragredientDualMap_apply, LinearMap.dualMap_apply, LinearMap.restrictScalars_apply]

end ContragredientMap

section ContragredientQuotient

variable {R G M N : Type*} [CommRing R] [Group G]
  [AddCommMonoid M] [Module (MonoidAlgebra R G) M] [Module R M]
  [IsScalarTower R (MonoidAlgebra R G) M]
  [AddCommMonoid N] [Module (MonoidAlgebra R G) N] [Module R N]
  [IsScalarTower R (MonoidAlgebra R G) N]

/-- The functionals on `M` that extend along `f`, described as the range of contragredient dual
precomposition and as the range of the base-ring dual map, agree as additive subgroups. -/
theorem restrictScalars_range_contragredientDualMap (f : M →ₗ[MonoidAlgebra R G] N) :
    (LinearMap.range (contragredientDualMap f)).restrictScalars ℤ =
      (LinearMap.range (f.restrictScalars R).dualMap).restrictScalars ℤ := by
  ext ψ
  simp only [Submodule.restrictScalars_mem, LinearMap.mem_range]
  exact exists_congr fun φ ↦ by rw [contragredientDualMap_eq_dualMap]

/-- The quotients of `Hom_R(M, R)` by the range of contragredient dual precomposition and by the
range of the base-ring dual map agree, as additive groups. -/
def quotientRangeContragredientDualMapEquiv (f : M →ₗ[MonoidAlgebra R G] N) :
    (Module.Dual R M ⧸ LinearMap.range (contragredientDualMap f)) ≃ₗ[ℤ]
      (Module.Dual R M ⧸ LinearMap.range (f.restrictScalars R).dualMap) :=
  (Submodule.Quotient.restrictScalarsEquiv ℤ _).symm.trans <|
    (Submodule.quotEquivOfEq _ _ (restrictScalars_range_contragredientDualMap f)).trans
      (Submodule.Quotient.restrictScalarsEquiv ℤ _)

/-- `TauCeti.MonoidAlgebra.quotientRangeContragredientDualMapEquiv` sends the class of a
functional to its class. -/
@[simp]
theorem quotientRangeContragredientDualMapEquiv_mk (f : M →ₗ[MonoidAlgebra R G] N)
    (ψ : Module.Dual R M) :
    quotientRangeContragredientDualMapEquiv f (Submodule.Quotient.mk ψ) =
      Submodule.Quotient.mk ψ := by
  rw [quotientRangeContragredientDualMapEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.quotEquivOfEq_mk,
    Submodule.Quotient.restrictScalarsEquiv_mk]

end ContragredientQuotient

section FiniteGroup

variable {R G M : Type*} [CommSemiring R] [Group G] [Finite G]
  [AddCommMonoid M] [Module (MonoidAlgebra R G) M] [Module R M]

private noncomputable def dualLift (ψ : Module.Dual R M) (m : M) : MonoidAlgebra R G :=
  MonoidAlgebra.ofCoeff <|
    (Finsupp.linearEquivFunOnFinite R R G).symm fun g =>
      ψ (MonoidAlgebra.single g⁻¹ (1 : R) • m)

@[simp]
private theorem dualLift_coeff (ψ : Module.Dual R M) (m : M) (g : G) :
    (dualLift ψ m).coeff g = ψ (MonoidAlgebra.single g⁻¹ (1 : R) • m) := rfl

private theorem dualLift_add (ψ : Module.Dual R M) (x y : M) :
    dualLift (G := G) ψ (x + y) = dualLift ψ x + dualLift ψ y := by
  ext g
  simp

variable [IsScalarTower R (MonoidAlgebra R G) M]

private theorem dualLift_smul_base (ψ : Module.Dual R M) (r : R) (m : M) :
    dualLift (G := G) ψ (r • m) = r • dualLift ψ m := by
  ext g
  rw [dualLift_coeff (G := G), MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    dualLift_coeff (G := G), ← smul_comm r (MonoidAlgebra.single g⁻¹ (1 : R)) m, map_smul]

private noncomputable def dualLinearEquivInv (ψ : Module.Dual R M) :
    Module.Dual (MonoidAlgebra R G) M where
  toFun := dualLift (G := G) ψ
  map_add' := dualLift_add (G := G) ψ
  map_smul' a m := by
    rw [RingHom.id_apply]
    induction a using MonoidAlgebra.induction_on with
    | of h =>
        ext g
        simp only [dualLift_coeff (G := G), MonoidAlgebra.of_apply]
        rw [← mul_smul]
        simp
    | add a b ha hb =>
        rw [add_smul, dualLift_add (G := G), ha, hb, add_smul]
    | smul r a ha =>
        rw [IsScalarTower.smul_assoc, dualLift_smul_base (G := G), ha,
          IsScalarTower.smul_assoc]

/-- For a finite group, taking the coefficient at the identity identifies the group-algebra
linear dual with the base-ring dual carrying the contragredient action. -/
noncomputable def dualLinearEquiv :
    Module.Dual (MonoidAlgebra R G) M ≃ₗ[(MonoidAlgebra R G)ᵐᵒᵖ] Module.Dual R M where
  toFun := dualLinearMap
  invFun := dualLinearEquivInv
  left_inv φ := by
    ext m g
    -- Expose the coefficient formula for the explicit inverse.
    change (dualLift (dualLinearMap φ) m).coeff g = (φ m).coeff g
    rw [dualLift_coeff (G := G), dualLinearMap_apply, map_smul]
    simp
  right_inv ψ := by
    ext m
    -- At the identity, the explicit inverse recovers the original functional.
    change (dualLift ψ m).coeff 1 = ψ m
    exact (dualLift_coeff (G := G) ψ m 1).trans (by
      rw [inv_one, ← MonoidAlgebra.one_def, one_smul])
  map_add' := map_add dualLinearMap
  map_smul' := map_smul dualLinearMap

/-- The forward group-algebra duality map takes the coefficient at the identity. -/
@[simp]
theorem dualLinearEquiv_apply (φ : Module.Dual (MonoidAlgebra R G) M) (m : M) :
    dualLinearEquiv φ m = (φ m).coeff 1 :=
  dualLinearMap_apply φ m

/-- The inverse group-algebra duality map records the translates of a functional as its
coefficients. -/
@[simp]
theorem dualLinearEquiv_symm_apply_coeff (ψ : Module.Dual R M) (m : M) (g : G) :
    (dualLinearEquiv.symm ψ m).coeff g =
      ψ (MonoidAlgebra.single g⁻¹ (1 : R) • m) :=
  dualLift_coeff (G := G) ψ m g

section Naturality

variable {N : Type*} [AddCommMonoid N] [Module (MonoidAlgebra R G) N] [Module R N]
  [IsScalarTower R (MonoidAlgebra R G) N]

/-- Group-algebra precomposition becomes contragredient base-ring precomposition under
`dualLinearEquiv`. -/
theorem dualLinearEquiv_comp_lcomp (f : M →ₗ[MonoidAlgebra R G] N) :
    (dualLinearEquiv (G := G) (M := M)).toLinearMap.comp
        (f.lcomp (MonoidAlgebra R G)ᵐᵒᵖ (MonoidAlgebra R G)) =
      (contragredientDualMap f).comp (dualLinearEquiv (G := G) (M := N)).toLinearMap := by
  ext ψ m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lcomp_apply,
    dualLinearEquiv_apply, contragredientDualMap_apply]

/-- The coefficient-at-one duality carries the range of group-algebra precomposition to the
range of contragredient base-ring precomposition. -/
theorem map_range_lcomp_dualLinearEquiv (f : M →ₗ[MonoidAlgebra R G] N) :
    (LinearMap.range (f.lcomp (MonoidAlgebra R G)ᵐᵒᵖ (MonoidAlgebra R G))).map
        (dualLinearEquiv (G := G) (M := M)).toLinearMap =
      LinearMap.range (contragredientDualMap f) := by
  rw [← LinearMap.range_comp, dualLinearEquiv_comp_lcomp, LinearMap.range_comp,
    LinearEquiv.range]
  exact Submodule.map_top _

end Naturality

end FiniteGroup

end TauCeti.MonoidAlgebra
