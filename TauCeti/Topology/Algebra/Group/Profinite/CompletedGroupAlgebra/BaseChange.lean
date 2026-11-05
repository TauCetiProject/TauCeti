/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.MapDomain
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Basic
import TauCeti.LinearAlgebra.Basis.Algebra
import TauCeti.RingTheory.TensorProduct.Free

/-!
# Coefficient change of the completed group algebra

A ring homomorphism `f : R →+* S` induces a ring homomorphism
`completedGroupAlgebra.mapRingHom Γ f : R[[Γ]] →+* S[[Γ]]` by applying `f` to every coefficient of
every finite-quotient projection `R[Γ ⧸ U]`. It preserves the group elements `of` and is continuous
for the inverse-limit topologies when `f` is continuous.

When `O` is a commutative `R`-algebra, scalar multiplication in `O[[Γ]]` combines with
`mapRingHom Γ (algebraMap R O)` into a canonical `O`-algebra homomorphism
`completedGroupAlgebra.baseChange R O Γ : O ⊗[R] R[[Γ]] →ₐ[O] O[[Γ]]`. For an infinite extension
such as `ℚ` over `ℤ` or `ℚ_p` over `ℤ_p` this map need not be surjective, because a finite sum of
pure tensors has bounded denominators across all levels `U` whereas inverse limits of group
algebras do not. When `O` is finite and free as an `R`-module, choosing a finite `R`-basis
identifies both sides with finite products of copies of `R[[Γ]]`, so `baseChange R O Γ` is
bijective and upgrades to the `O`-algebra equivalence `completedGroupAlgebra.baseChangeEquiv R O Γ`.

## Main definitions

* `TauCeti.completedGroupAlgebra.mapRingHom Γ f`: the ring homomorphism `R[[Γ]] →+* S[[Γ]]`
  applying `f : R →+* S` levelwise to the coefficients.
* `TauCeti.completedGroupAlgebra.baseChange R O Γ`: the canonical `O`-algebra homomorphism
  `O ⊗[R] R[[Γ]] →ₐ[O] O[[Γ]]`.
* `TauCeti.completedGroupAlgebra.baseChangeEquiv R O Γ`: the `O`-algebra isomorphism
  `O ⊗[R] R[[Γ]] ≃ₐ[O] O[[Γ]]` when `O` is finite and free over `R`.

## Main results

* `TauCeti.completedGroupAlgebra.proj_mapRingHom`,
  `TauCeti.completedGroupAlgebra.mapRingHom_of`,
  `TauCeti.completedGroupAlgebra.mapRingHom_smul`,
  `TauCeti.completedGroupAlgebra.continuous_mapRingHom`: levelwise formula, behaviour on group
  elements, semilinearity, and continuity for the inverse-limit topologies.
* `TauCeti.completedGroupAlgebra.baseChange_bijective`: bijectivity of `baseChange R O Γ` for a
  finite free `R`-algebra `O`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 5.3.
* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*, Section 3.3,
  Proposition 3.16.
-/

public noncomputable section

open scoped TensorProduct

namespace TauCeti.completedGroupAlgebra

universe u v w z

section MapRingHom

variable (Γ : Type v) [Group Γ] [TopologicalSpace Γ]
  {R : Type u} {S : Type w} {T : Type z} [CommRing R] [CommRing S] [CommRing T]

private theorem mapDomain_mapOfLE_mapRingHom (f : R →+* S) {U V : OpenNormalSubgroup Γ}
    (hUV : U ≤ V) (x : completedGroupAlgebra R Γ) :
    MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV)
        (MonoidAlgebra.mapRingHom (Γ ⧸ U.toSubgroup) f (proj R Γ U x)) =
      MonoidAlgebra.mapRingHom (Γ ⧸ V.toSubgroup) f (proj R Γ V x) := by
  have hcomm := RingHom.congr_fun
    (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom f (QuotientGroup.mapOfLE hUV)).symm
    (proj R Γ U x)
  simpa only [RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
    mapDomain_mapOfLE_proj] using hcomm

/-- Change of coefficients `R[[Γ]] →+* S[[Γ]]` along a ring homomorphism `f : R →+* S`, applying
`f` to the coefficients of every projection `R[Γ ⧸ U]`. -/
def mapRingHom (f : R →+* S) : completedGroupAlgebra R Γ →+* completedGroupAlgebra S Γ where
  toFun x := mk S Γ
    (fun U ↦ MonoidAlgebra.mapRingHom (Γ ⧸ U.toSubgroup) f (proj R Γ U x))
    (fun _ _ hUV ↦ mapDomain_mapOfLE_mapRingHom Γ f hUV x)
  map_one' := ext fun U ↦ by simp
  map_mul' x y := ext fun U ↦ by simp
  map_zero' := ext fun U ↦ by simp
  map_add' x y := ext fun U ↦ by simp

/-- The projection of `mapRingHom Γ f x` at level `U` is obtained by applying `f` to the
coefficients of the projection of `x` at `U`. -/
@[simp]
theorem proj_mapRingHom (f : R →+* S) (U : OpenNormalSubgroup Γ)
    (x : completedGroupAlgebra R Γ) :
    proj S Γ U (mapRingHom Γ f x) =
      MonoidAlgebra.mapRingHom (Γ ⧸ U.toSubgroup) f (proj R Γ U x) := by
  simp [mapRingHom]

/-- Each coefficient of a projection of `mapRingHom Γ f x` is the image under `f` of the
corresponding coefficient of `x`. -/
theorem coeff_proj_mapRingHom (f : R →+* S) (U : OpenNormalSubgroup Γ)
    (x : completedGroupAlgebra R Γ) (g : Γ ⧸ U.toSubgroup) :
    (proj S Γ U (mapRingHom Γ f x)).coeff g = f ((proj R Γ U x).coeff g) := by
  simp [proj_mapRingHom]

/-- Coefficient change preserves the canonical group elements. -/
@[simp]
theorem mapRingHom_of (f : R →+* S) (γ : Γ) :
    mapRingHom Γ f (of R Γ γ) = of S Γ γ :=
  ext fun U ↦ by simp

/-- Coefficient change along `f : R →+* S` is `f`-semilinear for scalar multiplication. -/
@[simp]
theorem mapRingHom_smul (f : R →+* S) (r : R) (x : completedGroupAlgebra R Γ) :
    mapRingHom Γ f (r • x) = f r • mapRingHom Γ f x :=
  ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun g ↦ by
    simp [smul_eq_mul]

/-- Coefficient change along the identity ring homomorphism is the identity. -/
@[simp]
theorem mapRingHom_id :
    mapRingHom Γ (RingHom.id R) = RingHom.id (completedGroupAlgebra R Γ) :=
  RingHom.ext fun x ↦ ext fun U ↦ by simp

/-- Coefficient change is functorial under composition of ring homomorphisms. -/
theorem mapRingHom_comp (g : S →+* T) (f : R →+* S) :
    mapRingHom Γ (g.comp f) = (mapRingHom Γ g).comp (mapRingHom Γ f) :=
  RingHom.ext fun x ↦ ext fun U ↦ by
    simp [MonoidAlgebra.mapRingHom_comp]

variable {Γ}

/-- Coefficient change along an injective ring homomorphism is injective. -/
theorem mapRingHom_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (mapRingHom Γ f) := fun x y h ↦
  ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun g ↦ hf <| by
    simpa only [coeff_proj_mapRingHom] using
      congrArg (fun z ↦ (proj S Γ U z).coeff g) h

/-- Coefficient change along a continuous ring homomorphism is continuous for the inverse-limit
topologies. -/
theorem continuous_mapRingHom [TopologicalSpace R] [TopologicalSpace S] {f : R →+* S}
    (hf : Continuous f) : Continuous (mapRingHom Γ f) := by
  refine continuous_iff.mpr fun U g ↦ ?_
  simp_rw [coeff_proj_mapRingHom]
  exact hf.comp (continuous_coeff_proj R Γ U g)

end MapRingHom

section BaseChange

variable (R : Type u) (O : Type w) (Γ : Type v) [CommRing R] [CommRing O] [Algebra R O]
  [Group Γ] [TopologicalSpace Γ]

/-- The canonical `O`-algebra homomorphism `O ⊗[R] R[[Γ]] →ₐ[O] O[[Γ]]` sending `a ⊗ x` to `a`
times `mapRingHom Γ (algebraMap R O) x`. -/
def baseChange : O ⊗[R] completedGroupAlgebra R Γ →ₐ[O] completedGroupAlgebra O Γ :=
  letI : Algebra R (completedGroupAlgebra O Γ) := Algebra.restrictScalars R O _
  letI : IsScalarTower R O (completedGroupAlgebra O Γ) := IsScalarTower.restrictScalars R O _
  let j : completedGroupAlgebra R Γ →ₐ[R] completedGroupAlgebra O Γ :=
    AlgHom.mk' (mapRingHom Γ (algebraMap R O)) fun r x ↦ by
      rw [mapRingHom_smul, IsScalarTower.algebraMap_smul]
  Algebra.TensorProduct.lift (Algebra.ofId O (completedGroupAlgebra O Γ)) j
    fun a _ ↦ Algebra.commutes a _

/-- On a pure tensor `a ⊗ x`, `baseChange` scales `mapRingHom Γ (algebraMap R O) x` by `a`. -/
@[simp]
theorem baseChange_tmul (a : O) (x : completedGroupAlgebra R Γ) :
    baseChange R O Γ (a ⊗ₜ[R] x) = a • mapRingHom Γ (algebraMap R O) x :=
  (Algebra.smul_def a (mapRingHom Γ (algebraMap R O) x)).symm

/-- On `a ⊗ of γ`, `baseChange` produces `a • of γ`. -/
theorem baseChange_tmul_of (a : O) (γ : Γ) :
    baseChange R O Γ (a ⊗ₜ[R] of R Γ γ) = a • of O Γ γ := by
  simp

/-- Projecting `baseChange R O Γ (a ⊗ x)` to level `U` scales the coefficient-extended projection
of `x` by `a`. -/
theorem proj_baseChange_tmul (U : OpenNormalSubgroup Γ) (a : O)
    (x : completedGroupAlgebra R Γ) :
    proj O Γ U (baseChange R O Γ (a ⊗ₜ[R] x)) =
      a • MonoidAlgebra.mapRingHom (Γ ⧸ U.toSubgroup) (algebraMap R O) (proj R Γ U x) := by
  simp

section FiniteFree

/-- Apply an `R`-linear functional `φ : O →ₗ[R] R` coefficientwise at every level of `O[[Γ]]`. -/
private def mapCoord (φ : O →ₗ[R] R) :
    completedGroupAlgebra O Γ →+ completedGroupAlgebra R Γ where
  toFun y := mk R Γ
    (fun U ↦ MonoidAlgebra.ofCoeff ((proj O Γ U y).coeff.mapRange φ (map_zero φ)))
    fun U V hUV ↦ by
      apply MonoidAlgebra.coeff_injective
      rw [MonoidAlgebra.coeff_mapDomain, MonoidAlgebra.coeff_ofCoeff, MonoidAlgebra.coeff_ofCoeff,
        ← mapDomain_mapOfLE_proj hUV y, MonoidAlgebra.coeff_mapDomain]
      exact Finsupp.mapDomain_mapRange (QuotientGroup.mapOfLE hUV) _ φ (map_zero φ) (map_add φ)
  map_zero' := ext fun U ↦ MonoidAlgebra.coeff_injective <| by
    ext g
    simp
  map_add' x y := ext fun U ↦ MonoidAlgebra.coeff_injective <| by
    ext g
    simp

@[simp]
private theorem coeff_proj_mapCoord (φ : O →ₗ[R] R)
    (U : OpenNormalSubgroup Γ) (y : completedGroupAlgebra O Γ) (g : Γ ⧸ U.toSubgroup) :
    (proj R Γ U (mapCoord R O Γ φ y)).coeff g = φ ((proj O Γ U y).coeff g) := by
  simp [mapCoord]

@[simp]
private theorem mapCoord_smul_mapRingHom (φ : O →ₗ[R] R) (a : O)
    (x : completedGroupAlgebra R Γ) :
    mapCoord R O Γ φ (a • mapRingHom Γ (algebraMap R O) x) = φ a • x :=
  ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun g ↦ by
    simp [LinearMap.map_mul_algebraMap, smul_eq_mul]

variable [Module.Free R O] [Module.Finite R O]

/-- **Finite free base change of the completed group algebra is bijective.** When `O` is finite
and free as an `R`-module, `baseChange R O Γ : O ⊗[R] R[[Γ]] →ₐ[O] O[[Γ]]` is bijective. -/
theorem baseChange_bijective : Function.Bijective (baseChange R O Γ) := by
  let _ : Algebra R (completedGroupAlgebra O Γ) := Algebra.restrictScalars R O _
  let _ : IsScalarTower R O (completedGroupAlgebra O Γ) := IsScalarTower.restrictScalars R O _
  let b := Module.Free.chooseBasis R O
  let j : completedGroupAlgebra R Γ →ₗ[R] completedGroupAlgebra O Γ :=
    { toFun := mapRingHom Γ (algebraMap R O)
      map_add' := map_add _
      map_smul' r x := by rw [RingHom.id_apply, mapRingHom_smul, IsScalarTower.algebraMap_smul] }
  have hbase : (baseChange R O Γ).toLinearMap = j.liftBaseChange O :=
    (LinearMap.liftBaseChangeEquiv O).symm.injective <| LinearMap.ext fun x ↦ by simp [j]
  rw [← AlgHom.coe_toLinearMap, hbase]
  refine j.liftBaseChange_bijective_of_basis_coord b (fun i ↦ mapCoord R O Γ (b.coord i))
    (fun i ↦ mapCoord_smul_mapRingHom R O Γ (b.coord i)) fun y ↦ ?_
  exact ext fun U ↦ MonoidAlgebra.coeff_injective <| Finsupp.ext fun g ↦ by
    simpa [j, smul_eq_mul] using b.sum_mul_algebraMap_coord ((proj O Γ U y).coeff g)

/-- **Finite free base change of the completed group algebra.** When `O` is finite and free as an
`R`-module, `O ⊗[R] R[[Γ]]` is canonically isomorphic as an `O`-algebra to `O[[Γ]]`. -/
def baseChangeEquiv : O ⊗[R] completedGroupAlgebra R Γ ≃ₐ[O] completedGroupAlgebra O Γ :=
  AlgEquiv.ofBijective (baseChange R O Γ) (baseChange_bijective R O Γ)

/-- The forward map of `baseChangeEquiv` is `baseChange`. -/
@[simp]
theorem coe_baseChangeEquiv :
    ⇑(baseChangeEquiv R O Γ) = baseChange R O Γ :=
  (rfl)

/-- Applying `baseChangeEquiv` evaluates `baseChange`. -/
theorem baseChangeEquiv_apply (z : O ⊗[R] completedGroupAlgebra R Γ) :
    baseChangeEquiv R O Γ z = baseChange R O Γ z :=
  AlgEquiv.ofBijective_apply _ _ _

/-- `baseChangeEquiv` sends `a ⊗ x` to `a • mapRingHom Γ (algebraMap R O) x`. -/
theorem baseChangeEquiv_tmul (a : O) (x : completedGroupAlgebra R Γ) :
    baseChangeEquiv R O Γ (a ⊗ₜ[R] x) = a • mapRingHom Γ (algebraMap R O) x :=
  baseChange_tmul R O Γ a x

/-- `baseChangeEquiv` sends `a ⊗ of γ` to `a • of γ`. -/
theorem baseChangeEquiv_tmul_of (a : O) (γ : Γ) :
    baseChangeEquiv R O Γ (a ⊗ₜ[R] of R Γ γ) = a • of O Γ γ :=
  baseChange_tmul_of R O Γ a γ

/-- The inverse of `baseChangeEquiv` sends `mapRingHom Γ (algebraMap R O) x` to `1 ⊗ x`. -/
@[simp]
theorem baseChangeEquiv_symm_mapRingHom (x : completedGroupAlgebra R Γ) :
    (baseChangeEquiv R O Γ).symm (mapRingHom Γ (algebraMap R O) x) = 1 ⊗ₜ[R] x := by
  apply (baseChangeEquiv R O Γ).injective
  simp

/-- The inverse of `baseChangeEquiv` sends `of γ` to `1 ⊗ of γ`. -/
@[simp]
theorem baseChangeEquiv_symm_of (γ : Γ) :
    (baseChangeEquiv R O Γ).symm (of O Γ γ) = 1 ⊗ₜ[R] of R Γ γ := by
  rw [← mapRingHom_of Γ (algebraMap R O) γ, baseChangeEquiv_symm_mapRingHom]

/-- Over `O = R`, `baseChangeEquiv` is the canonical left unit isomorphism
`R ⊗[R] R[[Γ]] ≃ₐ R[[Γ]]`. -/
@[simp]
theorem baseChangeEquiv_self :
    baseChangeEquiv R R Γ = Algebra.TensorProduct.lid R (completedGroupAlgebra R Γ) := by
  refine AlgEquiv.ext fun z ↦ ?_
  induction z using TensorProduct.inductionOn with
  | tmul a x => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end FiniteFree

end BaseChange

end TauCeti.completedGroupAlgebra
