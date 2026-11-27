/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Connections on modules

Given a derivation `d : A → Ω`, a connection sends a section of an `A`-module `M` to an
`M`-valued one-form and satisfies the Leibniz rule with symbol `d`. Taking the universal
Kähler derivation gives ordinary algebraic connections. Taking its composite with a quotient
of the differentials allows the same construction to be used for divided power differentials.

## References

* The Stacks Project, [Remark 60.6.8](https://stacks.math.columbia.edu/tag/07I0).
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {R A Ω : Type*} [CommSemiring R] [CommSemiring A] [Algebra R A]
  [AddCommMonoid Ω] [Module A Ω] [Module R Ω]

/-- A connection relative to `d` takes values in module-valued one-forms. -/
structure ModuleConnection (d : Derivation R A Ω) (M : Type*) [AddCommMonoid M] [Module A M]
    extends M →+ M ⊗[A] Ω where
  /-- The product rule for multiplication of a section by a scalar. -/
  leibniz' (a : A) (m : M) : toAddMonoidHom (a • m) = a • toAddMonoidHom m + m ⊗ₜ[A] d a

namespace ModuleConnection

variable {d : Derivation R A Ω} {M N P : Type*}
  [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N] [AddCommMonoid P] [Module A P]

instance : FunLike (ModuleConnection d M) M (M ⊗[A] Ω) where
  coe c := c.toAddMonoidHom
  coe_injective c c' h := by
    cases c
    cases c'
    congr 1
    exact DFunLike.coe_injective h

instance : AddMonoidHomClass (ModuleConnection d M) M (M ⊗[A] Ω) where
  map_zero c := c.toAddMonoidHom.map_zero
  map_add c := c.toAddMonoidHom.map_add

@[simp]
theorem toAddMonoidHom_apply (c : ModuleConnection d M) (m : M) : c.toAddMonoidHom m = c m :=
  (rfl)

@[simp]
theorem mk_apply (f : M →+ M ⊗[A] Ω) (h) (m : M) :
    (ModuleConnection.mk (d := d) f h) m = f m := (rfl)

/-- Connections are determined by their values on sections. -/
@[ext]
theorem ext {c c' : ModuleConnection d M} (h : ∀ m, c m = c' m) : c = c' :=
  DFunLike.ext _ _ h

/-- The Leibniz rule for a module connection. -/
@[simp]
theorem leibniz (c : ModuleConnection d M) (a : A) (m : M) :
    c (a • m) = a • c m + m ⊗ₜ[A] d a :=
  c.leibniz' a m

/-- A connection as a linear map over the base semiring. -/
def toLinearMap [Module R M] [IsScalarTower R A M] (c : ModuleConnection d M) :
    M →ₗ[R] M ⊗[A] Ω where
  toFun := c
  map_add' := map_add c
  map_smul' r m := by
    rw [RingHom.id_apply, ← algebraMap_smul A r m, c.leibniz]
    simp

@[simp]
theorem toLinearMap_apply [Module R M] [IsScalarTower R A M] (c : ModuleConnection d M) (m : M) :
    c.toLinearMap m = c m := (rfl)

/-- The connection on the scalar module induced by the derivation itself. -/
def _root_.Derivation.moduleConnection (d : Derivation R A Ω) : ModuleConnection d A where
  toAddMonoidHom := (TensorProduct.lid A Ω).symm.toLinearMap.toAddMonoidHom.comp
    d.toLinearMap.toAddMonoidHom
  leibniz' a b := by
    simp [TensorProduct.tmul_add, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul]

@[simp]
theorem _root_.Derivation.moduleConnection_apply (d : Derivation R A Ω) (a : A) :
    d.moduleConnection a = (1 : A) ⊗ₜ[A] d a := (rfl)

/-- A linear map is horizontal if applying it to the coefficients commutes with the connections. -/
def IsHorizontal (c : ModuleConnection d M) (c' : ModuleConnection d N) (f : M →ₗ[A] N) : Prop :=
  ∀ m, c' (f m) = f.rTensor Ω (c m)

/-- A pointwise test for horizontality. -/
theorem isHorizontal_iff (c : ModuleConnection d M) (c' : ModuleConnection d N) (f : M →ₗ[A] N) :
    c.IsHorizontal c' f ↔ ∀ m, c' (f m) = f.rTensor Ω (c m) := Iff.rfl

@[simp]
theorem isHorizontal_id (c : ModuleConnection d M) : c.IsHorizontal c LinearMap.id := by
  intro m
  simp

/-- Horizontal maps compose. -/
theorem IsHorizontal.comp {c : ModuleConnection d M} {c' : ModuleConnection d N}
    {c'' : ModuleConnection d P} {f : M →ₗ[A] N} {g : N →ₗ[A] P}
    (hg : c'.IsHorizontal c'' g) (hf : c.IsHorizontal c' f) :
    c.IsHorizontal c'' (g.comp f) := by
  intro m
  rw [LinearMap.comp_apply, hg, hf, LinearMap.rTensor_comp, LinearMap.comp_apply]

/-- The inverse of a horizontal linear equivalence is horizontal. -/
theorem IsHorizontal.symm {c : ModuleConnection d M} {c' : ModuleConnection d N} {e : M ≃ₗ[A] N}
    (he : c.IsHorizontal c' e.toLinearMap) : c'.IsHorizontal c e.symm.toLinearMap := by
  intro n
  apply (e.rTensor Ω).eq_symm_apply.mpr
  simpa only [← LinearEquiv.coe_rTensor, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    using (he (e.symm n)).symm

end ModuleConnection

end TauCeti
