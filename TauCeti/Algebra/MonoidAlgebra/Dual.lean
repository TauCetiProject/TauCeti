/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import TauCeti.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Finsupp.Pi

/-!
# Duality over a finite group algebra

For a finite group `G` and a commutative semiring `R`, the group algebra `R[G]` is a symmetric
Frobenius algebra. Taking the coefficient at the identity identifies the `R[G]`-linear dual
`Hom_{R[G]}(M, R[G])` with the `R`-linear dual `Hom_R(M, R)`. The action on the latter is the
contragredient action: `op a` sends `ψ` to the functional `m ↦ ψ(a • m)`.

This file constructs that equivalence explicitly and proves its naturality under precomposition.
The range statement is the bridge used to express an Auslander--Reiten transpose through an
ordinary base-ring dual. The contragredient action and precomposition need only semiring
coefficients and also apply to arbitrary monoids. The range comparison uses commutative semiring
coefficients; over a commutative ring, the corresponding quotient comparison is base-ring linear.

## Main definitions

* `TauCeti.MonoidAlgebra.dualLinearEquiv`: the coefficient-at-one equivalence between the two
  duals.
* `LinearMap.contragredientDualMap`: precomposition on base-ring duals, equipped with
  the contragredient monoid-algebra action.
* `LinearMap.quotientRangeContragredientDualMapEquiv`: the cokernel of contragredient
  precomposition is base-ring linearly equivalent to the cokernel of the base-ring dual map.

## Main results

* `LinearMap.contragredientDualMap_eq_dualMap`: contragredient precomposition is the
  base-ring dual map.
* `LinearMap.map_range_lcomp_dualLinearEquiv`: the duality carries the range of
  group-algebra precomposition to the range of contragredient base-ring precomposition.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Grundlehren 323,
  Springer (2008), (5.6.9).
-/

public section

noncomputable section

open LinearMap TauCeti.MonoidAlgebra

section ContragredientAction

variable {R G M : Type*} [Semiring R] [Monoid G]
  [AddCommMonoid M] [Module (MonoidAlgebra R G) M] [Module R M]
  [SMulCommClass R (MonoidAlgebra R G) M]

/-- The contragredient action of a monoid algebra on a base-ring dual. -/
noncomputable instance TauCeti.MonoidAlgebra.instModuleDualContragredient :
    Module (MonoidAlgebra R G)ᵐᵒᵖ (Module.Dual R M) :=
  inferInstanceAs (Module (DomMulAct (MonoidAlgebra R G)) (Module.Dual R M))

end ContragredientAction

section ContragredientScalarTower

variable {R G M : Type*} [CommSemiring R] [Monoid G]
  [AddCommMonoid M] [Module (MonoidAlgebra R G) M] [Module R M]
  [IsScalarTower R (MonoidAlgebra R G) M]

/-- The contragredient action restricts to the usual base-ring action on the dual. -/
instance TauCeti.MonoidAlgebra.instIsScalarTowerDualContragredient :
    IsScalarTower R (MonoidAlgebra R G)ᵐᵒᵖ (Module.Dual R M) where
  smul_assoc r a ψ := by
    ext m
    -- Expose domain precomposition and codomain scaling on the two sides.
    change ψ ((r • MulOpposite.unop a) • m) = r • ψ (MulOpposite.unop a • m)
    simp [smul_assoc]

end ContragredientScalarTower

section CoefficientMap

variable {R G M : Type*} [CommSemiring R] [Group G]
  [AddCommMonoid M] [Module (MonoidAlgebra R G) M] [Module R M]
  [IsScalarTower R (MonoidAlgebra R G) M]

private noncomputable def dualLinearMap :
    Module.Dual (MonoidAlgebra R G) M →ₗ[(MonoidAlgebra R G)ᵐᵒᵖ] Module.Dual R M where
  toFun φ :=
    Finsupp.lapply 1 ∘ₗ (MonoidAlgebra.coeffLinearEquiv R).toLinearMap ∘ₗ φ.restrictScalars R
  map_add' φ ψ := by ext m; rfl
  map_smul' a φ := by
    ext m
    -- Unfold only the two opposite actions; the remaining equality is symmetry of the
    -- coefficient-at-one pairing.
    change ((a • φ) m).coeff 1 = (φ (MulOpposite.unop a • m)).coeff 1
    simp only [LinearMap.smul_apply]
    rw [map_smul]
    exact MonoidAlgebra.coeff_one_mul_comm _ _

@[simp]
private theorem dualLinearMap_apply (φ : Module.Dual (MonoidAlgebra R G) M) (m : M) :
    dualLinearMap φ m = (φ m).coeff 1 := rfl

end CoefficientMap

section ContragredientMap

variable {R G M N : Type*} [Semiring R] [Monoid G]
  [AddCommMonoid M] [Module (MonoidAlgebra R G) M] [Module R M]
  [SMulCommClass R (MonoidAlgebra R G) M]
  [AddCommMonoid N] [Module (MonoidAlgebra R G) N] [Module R N]
  [SMulCommClass R (MonoidAlgebra R G) N]
  [LinearMap.CompatibleSMul M N R (MonoidAlgebra R G)]

/-- Precomposition with a monoid-algebra linear map, on base-ring duals equipped with the
contragredient action. Scalar compatibility ensures that the map is also base-ring linear. -/
def LinearMap.contragredientDualMap (f : M →ₗ[MonoidAlgebra R G] N) :
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
theorem LinearMap.contragredientDualMap_apply (f : M →ₗ[MonoidAlgebra R G] N)
    (ψ : Module.Dual R N) (m : M) :
    contragredientDualMap f ψ m = ψ (f m) := by
  simp [contragredientDualMap]

end ContragredientMap

section ContragredientMapComparison

variable {R G M N : Type*} [CommSemiring R] [Monoid G]
  [AddCommMonoid M] [Module (MonoidAlgebra R G) M] [Module R M]
  [IsScalarTower R (MonoidAlgebra R G) M]
  [AddCommMonoid N] [Module (MonoidAlgebra R G) N] [Module R N]
  [IsScalarTower R (MonoidAlgebra R G) N]

/-- Restricting contragredient dual precomposition to the base ring gives the usual dual map. -/
theorem LinearMap.contragredientDualMap_eq_dualMap (f : M →ₗ[MonoidAlgebra R G] N) :
    (contragredientDualMap f).restrictScalars R = (f.restrictScalars R).dualMap := by
  ext ψ m
  simp

/-- The functionals on `M` that extend along `f`, described as the range of contragredient dual
precomposition and as the range of the base-ring dual map, agree as base-ring submodules. -/
theorem LinearMap.restrictScalars_range_contragredientDualMap
    (f : M →ₗ[MonoidAlgebra R G] N) :
    (LinearMap.range (contragredientDualMap f)).restrictScalars R =
      LinearMap.range (f.restrictScalars R).dualMap := by
  rw [← LinearMap.range_restrictScalars, contragredientDualMap_eq_dualMap]

end ContragredientMapComparison

section ContragredientQuotient

variable {R G M N : Type*} [CommRing R] [Monoid G]
  [AddCommMonoid M] [Module (MonoidAlgebra R G) M] [Module R M]
  [IsScalarTower R (MonoidAlgebra R G) M]
  [AddCommMonoid N] [Module (MonoidAlgebra R G) N] [Module R N]
  [IsScalarTower R (MonoidAlgebra R G) N]

/-- The quotients of `Hom_R(M, R)` by the range of contragredient dual precomposition and by the
range of the base-ring dual map agree as base-ring modules. -/
def LinearMap.quotientRangeContragredientDualMapEquiv (f : M →ₗ[MonoidAlgebra R G] N) :
    (Module.Dual R M ⧸ LinearMap.range (contragredientDualMap f)) ≃ₗ[R]
      (Module.Dual R M ⧸ LinearMap.range (f.restrictScalars R).dualMap) :=
  (Submodule.Quotient.restrictScalarsEquiv R _).symm.trans <|
    Submodule.quotEquivOfEq _ _ (restrictScalars_range_contragredientDualMap f)

/-- `LinearMap.quotientRangeContragredientDualMapEquiv` sends the class of a
functional to its class. -/
@[simp]
theorem LinearMap.quotientRangeContragredientDualMapEquiv_mk (f : M →ₗ[MonoidAlgebra R G] N)
    (ψ : Module.Dual R M) :
    quotientRangeContragredientDualMapEquiv f (Submodule.Quotient.mk ψ) =
      Submodule.Quotient.mk ψ := by
  simp [quotientRangeContragredientDualMapEquiv]

/-- The inverse quotient comparison sends the class of a functional to its class. -/
@[simp]
theorem LinearMap.quotientRangeContragredientDualMapEquiv_symm_mk
    (f : M →ₗ[MonoidAlgebra R G] N) (ψ : Module.Dual R M) :
    (quotientRangeContragredientDualMapEquiv f).symm (Submodule.Quotient.mk ψ) =
      Submodule.Quotient.mk ψ := by
  rw [LinearEquiv.symm_apply_eq]
  simp

end ContragredientQuotient

section FiniteGroup

section

variable {R G M : Type*} [Semiring R] [Group G] [Finite G]
  [AddCommMonoid M] [Module (MonoidAlgebra R G) M] [Module R M]
  [SMulCommClass (MonoidAlgebra R G) R M]

private noncomputable def dualLift (ψ : Module.Dual R M) : M →ₗ[R] MonoidAlgebra R G :=
  (MonoidAlgebra.coeffLinearEquiv R).symm.toLinearMap ∘ₗ
    (Finsupp.linearEquivFunOnFinite R R G).symm.toLinearMap ∘ₗ
      LinearMap.pi fun g ↦ ψ.comp
        (DistribSMul.toLinearMap R M (MonoidAlgebra.single g⁻¹ (1 : R)))

@[simp]
private theorem dualLift_coeff (ψ : Module.Dual R M) (m : M) (g : G) :
    (dualLift ψ m).coeff g = ψ (MonoidAlgebra.single g⁻¹ (1 : R) • m) := rfl

end

variable {R G M : Type*} [CommSemiring R] [Group G] [Finite G]
  [AddCommMonoid M] [Module (MonoidAlgebra R G) M] [Module R M]
  [IsScalarTower R (MonoidAlgebra R G) M]

private noncomputable def dualLinearEquivInv (ψ : Module.Dual R M) :
    Module.Dual (MonoidAlgebra R G) M where
  toFun := dualLift (G := G) ψ
  map_add' := map_add (dualLift (G := G) ψ)
  map_smul' a m := by
    rw [RingHom.id_apply]
    induction a using MonoidAlgebra.induction_on with
    | of h =>
        ext g
        simp only [dualLift_coeff (G := G), MonoidAlgebra.of_apply]
        rw [← mul_smul]
        simp
    | add a b ha hb =>
        rw [add_smul, map_add, ha, hb, add_smul]
    | smul r a ha =>
        rw [IsScalarTower.smul_assoc, map_smul, ha,
          IsScalarTower.smul_assoc]

/-- For a finite group, taking the coefficient at the identity identifies the group-algebra
linear dual with the base-ring dual carrying the contragredient action. -/
noncomputable def TauCeti.MonoidAlgebra.dualLinearEquiv :
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
theorem TauCeti.MonoidAlgebra.dualLinearEquiv_apply
    (φ : Module.Dual (MonoidAlgebra R G) M) (m : M) :
    dualLinearEquiv φ m = (φ m).coeff 1 :=
  dualLinearMap_apply φ m

/-- The inverse group-algebra duality map records the translates of a functional as its
coefficients. -/
@[simp]
theorem TauCeti.MonoidAlgebra.dualLinearEquiv_symm_apply_coeff
    (ψ : Module.Dual R M) (m : M) (g : G) :
    (dualLinearEquiv.symm ψ m).coeff g =
      ψ (MonoidAlgebra.single g⁻¹ (1 : R) • m) :=
  dualLift_coeff (G := G) ψ m g

section Naturality

variable {N : Type*} [AddCommMonoid N] [Module (MonoidAlgebra R G) N] [Module R N]
  [IsScalarTower R (MonoidAlgebra R G) N]

/-- Group-algebra precomposition becomes contragredient base-ring precomposition under
`dualLinearEquiv`. -/
theorem LinearMap.dualLinearEquiv_comp_lcomp (f : M →ₗ[MonoidAlgebra R G] N) :
    (dualLinearEquiv (G := G) (M := M)).toLinearMap.comp
        (f.lcomp (MonoidAlgebra R G)ᵐᵒᵖ (MonoidAlgebra R G)) =
      (contragredientDualMap f).comp (dualLinearEquiv (G := G) (M := N)).toLinearMap := by
  ext ψ m
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.lcomp_apply,
    dualLinearEquiv_apply, contragredientDualMap_apply]

/-- The coefficient-at-one duality carries the range of group-algebra precomposition to the
range of contragredient base-ring precomposition. -/
theorem LinearMap.map_range_lcomp_dualLinearEquiv (f : M →ₗ[MonoidAlgebra R G] N) :
    (LinearMap.range (f.lcomp (MonoidAlgebra R G)ᵐᵒᵖ (MonoidAlgebra R G))).map
        (dualLinearEquiv (G := G) (M := M)).toLinearMap =
      LinearMap.range (contragredientDualMap f) := by
  rw [← LinearMap.range_comp, dualLinearEquiv_comp_lcomp, LinearMap.range_comp,
    LinearEquiv.range]
  exact Submodule.map_top _

end Naturality

end FiniteGroup
