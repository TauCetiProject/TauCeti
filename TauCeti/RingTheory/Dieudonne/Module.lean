/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.RingTheory.WittVector.Frobenius

/-!
# Semilinear Dieudonné modules

A Dieudonné module over a perfect ring `k` of characteristic `p` is a `W(k)`-module
with Frobenius-semilinear `F` and inverse-Frobenius-semilinear `V`, satisfying
`FV = VF = p`. No finiteness or torsion condition is imposed. Over perfect fields,
finite-length and finite-free modules are used for finite commutative `p`-groups
and `p`-divisible groups respectively.

This file constructs their category and faithful forgetful functor to Witt-vector
modules. The images of `F` and `V` are actual submodules, not just their spans, and
both cokernels are killed by `p`. On modules with injective multiplication by `p`,
both operators are injective. The standard étale and multiplicative modules have
operators `(σ, pσ⁻¹)` and `(pσ, σ⁻¹)` in the contravariant convention.

The semilinear formulation parallels Mathlib's `WittVector.Isocrystal` and
`WittVector.IsocrystalHom`; here the coefficients are integral and both operators
are retained.

## References

* R. Pink, *Finite group schemes*, lecture notes (2005), §23.
* M. Demazure, *Lectures on p-divisible groups*, Chapter III.
-/

public noncomputable section

namespace TauCeti

open CategoryTheory

universe u v

variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p]
  [PerfectRing k p]

/-- A Witt-vector module with semilinear Frobenius and Verschiebung satisfying
`FV = VF = p`. This is the contravariant Dieudonné convention. -/
structure DieudonneModule where
  /-- The underlying Witt-vector module. -/
  toModuleCat : ModuleCat.{v} (WittVector p k)
  /-- Frobenius, semilinear for Witt Frobenius. -/
  F : toModuleCat →ₛₗ[(WittVector.frobeniusEquiv p k : WittVector p k →+* WittVector p k)]
    toModuleCat
  /-- Verschiebung, semilinear for inverse Witt Frobenius. -/
  V : toModuleCat →ₛₗ[((WittVector.frobeniusEquiv p k).symm :
    WittVector p k →+* WittVector p k)] toModuleCat
  /-- Frobenius after Verschiebung is multiplication by `p`. -/
  F_V (x : toModuleCat) : F (V x) = (p : WittVector p k) • x
  /-- Verschiebung after Frobenius is multiplication by `p`. -/
  V_F (x : toModuleCat) : V (F x) = (p : WittVector p k) • x

namespace DieudonneModule

variable {p k}

instance : CoeSort (DieudonneModule.{u, v} p k) (Type v) := ⟨fun M => M.toModuleCat⟩

instance (M : DieudonneModule.{u, v} p k) : AddCommGroup M :=
  inferInstanceAs (AddCommGroup M.toModuleCat)

instance (M : DieudonneModule.{u, v} p k) : Module (WittVector p k) M :=
  inferInstanceAs (Module (WittVector p k) M.toModuleCat)

attribute [simp] F_V V_F

/-- A morphism of Dieudonné modules is a Witt-linear map commuting with both operators. -/
@[ext]
structure Hom (M N : DieudonneModule.{u, v} p k) where
  /-- The underlying Witt-linear map. -/
  toLinearMap : M →ₗ[WittVector p k] N
  /-- Compatibility with Frobenius. -/
  map_F (x : M) : toLinearMap (M.F x) = N.F (toLinearMap x)
  /-- Compatibility with Verschiebung. -/
  map_V (x : M) : toLinearMap (M.V x) = N.V (toLinearMap x)

instance : Category (DieudonneModule.{u, v} p k) where
  Hom := Hom
  id M := ⟨LinearMap.id, fun _ => rfl, fun _ => rfl⟩
  comp f g := ⟨g.toLinearMap.comp f.toLinearMap,
    fun x => by simp only [LinearMap.comp_apply, Hom.map_F],
    fun x => by simp only [LinearMap.comp_apply, Hom.map_V]⟩

instance {M N : DieudonneModule.{u, v} p k} : FunLike (Hom M N) M N where
  coe f := f.toLinearMap
  coe_injective _ _ h := Hom.ext (LinearMap.ext (congrFun h))

attribute [simp] Hom.map_F Hom.map_V

instance : ConcreteCategory (DieudonneModule.{u, v} p k) Hom where
  hom f := f
  ofHom f := f

@[simp]
theorem coe_hom {M N : DieudonneModule.{u, v} p k} (f : M ⟶ N) :
    (f : M → N) = f.toLinearMap := (rfl)

@[simp]
theorem id_toLinearMap (M : DieudonneModule.{u, v} p k) :
    (𝟙 M : M ⟶ M).toLinearMap = LinearMap.id := (rfl)

@[simp]
theorem comp_toLinearMap {M N P : DieudonneModule.{u, v} p k} (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).toLinearMap = g.toLinearMap.comp f.toLinearMap := (rfl)

/-- Forget Frobenius and Verschiebung. -/
-- Its object part must compute so that forgotten morphisms have the native ModuleCat type.
@[expose]
def forget : DieudonneModule.{u, v} p k ⥤ ModuleCat.{v} (WittVector p k) where
  obj M := M.toModuleCat
  map f := ModuleCat.ofHom f.toLinearMap

@[simp]
theorem forget_obj (M : DieudonneModule.{u, v} p k) :
    (forget (p := p) (k := k)).obj M = M.toModuleCat := (rfl)

@[simp]
theorem forget_map {M N : DieudonneModule.{u, v} p k} (f : M ⟶ N) :
    (forget (p := p) (k := k)).map f = ModuleCat.ofHom f.toLinearMap := (rfl)

instance : (forget (p := p) (k := k)).Faithful where
  map_injective h := by
    apply ConcreteCategory.hom_ext
    intro x
    exact LinearMap.congr_fun (congrArg ModuleCat.Hom.hom h) x

/-- A Witt-linear equivalence commuting with the operators gives an isomorphism of
Dieudonné modules. -/
def isoOfLinearEquiv (M N : DieudonneModule.{u, v} p k)
    (e : M ≃ₗ[WittVector p k] N)
    (hF : ∀ x, e (M.F x) = N.F (e x))
    (hV : ∀ x, e (M.V x) = N.V (e x)) : M ≅ N where
  hom := ⟨e.toLinearMap, hF, hV⟩
  inv := ⟨e.symm.toLinearMap,
    fun x => by
      apply e.injective
      simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply, hF],
    fun x => by
      apply e.injective
      simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply, hV]⟩
  hom_inv_id := by
    apply ConcreteCategory.hom_ext
    intro x
    exact e.symm_apply_apply x
  inv_hom_id := by
    apply ConcreteCategory.hom_ext
    intro x
    exact e.apply_symm_apply x

@[simp]
theorem isoOfLinearEquiv_hom_toLinearMap (M N : DieudonneModule.{u, v} p k)
    (e : M ≃ₗ[WittVector p k] N) (hF : ∀ x, e (M.F x) = N.F (e x))
    (hV : ∀ x, e (M.V x) = N.V (e x)) :
    (isoOfLinearEquiv M N e hF hV).hom.toLinearMap = e.toLinearMap := (rfl)

@[simp]
theorem isoOfLinearEquiv_inv_toLinearMap (M N : DieudonneModule.{u, v} p k)
    (e : M ≃ₗ[WittVector p k] N) (hF : ∀ x, e (M.F x) = N.F (e x))
    (hV : ∀ x, e (M.V x) = N.V (e x)) :
    (isoOfLinearEquiv M N e hF hV).inv.toLinearMap = e.symm.toLinearMap := (rfl)

/-- Every `p`-multiple is in the image of Frobenius. -/
theorem p_smul_mem_range_F (M : DieudonneModule.{u, v} p k) (x : M) :
    (p : WittVector p k) • x ∈ LinearMap.range M.F :=
  ⟨M.V x, M.F_V x⟩

/-- Every `p`-multiple is in the image of Verschiebung. -/
theorem p_smul_mem_range_V (M : DieudonneModule.{u, v} p k) (x : M) :
    (p : WittVector p k) • x ∈ LinearMap.range M.V :=
  ⟨M.F x, M.V_F x⟩

/-- The Frobenius cokernel is killed by `p`. -/
theorem p_smul_quotient_range_F (M : DieudonneModule.{u, v} p k)
    (x : M ⧸ LinearMap.range M.F) : (p : WittVector p k) • x = 0 := by
  refine Submodule.Quotient.induction_on _ x fun x => ?_
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact M.p_smul_mem_range_F x

/-- The Verschiebung cokernel is killed by `p`. -/
theorem p_smul_quotient_range_V (M : DieudonneModule.{u, v} p k)
    (x : M ⧸ LinearMap.range M.V) : (p : WittVector p k) • x = 0 := by
  refine Submodule.Quotient.induction_on _ x fun x => ?_
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact M.p_smul_mem_range_V x

/-- Frobenius is injective when multiplication by `p` is injective. -/
theorem F_injective (M : DieudonneModule.{u, v} p k)
    (hp : Function.Injective fun x : M => (p : WittVector p k) • x) :
    Function.Injective M.F := by
  intro x y h
  apply hp
  simpa only [M.V_F] using congrArg M.V h

/-- Verschiebung is injective when multiplication by `p` is injective. -/
theorem V_injective (M : DieudonneModule.{u, v} p k)
    (hp : Function.Injective fun x : M => (p : WittVector p k) • x) :
    Function.Injective M.V := by
  intro x y h
  apply hp
  simpa only [M.F_V] using congrArg M.F h

variable (p k)

/-- The standard étale module `W(k)`, with `F = σ` and `V = pσ⁻¹`. -/
-- The carrier must reduce during implicit typechecking of Witt-vector expressions.
@[expose, implicit_reducible]
def etale : DieudonneModule.{u, u} p k where
  toModuleCat := ModuleCat.of (WittVector p k) (WittVector p k)
  F := (WittVector.frobeniusEquiv p k : WittVector p k →+* WittVector p k).toSemilinearMap
  V := (p : WittVector p k) •
    ((WittVector.frobeniusEquiv p k).symm :
      WittVector p k →+* WittVector p k).toSemilinearMap
  F_V x := by
    simp only [LinearMap.smul_apply, RingHom.coe_toSemilinearMap, smul_eq_mul,
      RingEquiv.coe_toRingHom, map_mul, map_natCast, RingEquiv.apply_symm_apply]
  V_F x := by
    simp only [LinearMap.smul_apply, RingHom.coe_toSemilinearMap, smul_eq_mul,
      RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]

/-- The standard multiplicative module `W(k)`, with `F = pσ` and `V = σ⁻¹`. -/
-- The carrier must reduce during implicit typechecking of Witt-vector expressions.
@[expose, implicit_reducible]
def multiplicative : DieudonneModule.{u, u} p k where
  toModuleCat := ModuleCat.of (WittVector p k) (WittVector p k)
  F := (p : WittVector p k) •
    (WittVector.frobeniusEquiv p k : WittVector p k →+* WittVector p k).toSemilinearMap
  V := ((WittVector.frobeniusEquiv p k).symm :
    WittVector p k →+* WittVector p k).toSemilinearMap
  F_V x := by
    simp only [LinearMap.smul_apply, RingHom.coe_toSemilinearMap, smul_eq_mul,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  V_F x := by
    simp only [LinearMap.smul_apply, RingHom.coe_toSemilinearMap, smul_eq_mul,
      RingEquiv.coe_toRingHom, map_mul, map_natCast, RingEquiv.symm_apply_apply]

@[simp]
theorem etale_F (x : WittVector p k) :
    (etale p k).F x = WittVector.frobenius x := (rfl)

@[simp]
theorem etale_V (x : WittVector p k) :
    (etale p k).V x = (p : WittVector p k) * (WittVector.frobeniusEquiv p k).symm x := (rfl)

@[simp]
theorem multiplicative_F (x : WittVector p k) :
    (multiplicative p k).F x = (p : WittVector p k) * WittVector.frobenius x := (rfl)

@[simp]
theorem multiplicative_V (x : WittVector p k) :
    (multiplicative p k).V x = (WittVector.frobeniusEquiv p k).symm x := (rfl)

end DieudonneModule

end TauCeti
