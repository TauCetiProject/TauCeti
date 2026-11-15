/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.CompletedGroupAlgebra.Basic
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finsupp.Basic

/-!
# Coefficient change and finite free base change for the completed group algebra

For a topological group `Γ`, a homomorphism of commutative coefficient rings `f : R →+* S` applies
coefficientwise at every open normal quotient `Γ ⧸ U` and commutes with the transition maps
`Γ ⧸ U → Γ ⧸ V` (`U ≤ V`), inducing a ring homomorphism
`completedGroupAlgebra.mapRingHom Γ f : R[[Γ]] →+* S[[Γ]]` that fixes the group elements `of · Γ γ`
and is continuous when `f` is continuous. Likewise, any additive group homomorphism `φ : O →+ S`
induces a levelwise additive homomorphism
`completedGroupAlgebra.mapAddMonoidHom Γ φ : O[[Γ]] →+ S[[Γ]]`, continuous when `φ` is continuous.

For any `R`-algebra `O`, combining the `O`-algebra structure of `O[[Γ]]` with
`mapRingHom Γ (algebraMap R O) : R[[Γ]] →+* O[[Γ]]` yields the canonical `O`-algebra homomorphism
`completedGroupAlgebra.baseChangeHom R O Γ : O ⊗[R] R[[Γ]] →ₐ[O] O[[Γ]]`. In general tensor products
do not commute with inverse limits, so `baseChangeHom` need not be surjective when `O` is not
finitely presented (for instance `ℚ ⊗[ℤ] ℤ_p[[ℤ_p]]` is strictly smaller than `ℚ_p[[ℤ_p]]`). When
`O` is finite and free as an `R`-module, however, inverse limits commute with tensoring by `O`:
applying `mapAddMonoidHom Γ (b.coord i).toAddMonoidHom` along any finite `R`-basis `b` of `O`
supplies the inverse `y ↦ ∑ i, b i ⊗ₜ mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y`, upgrading
`baseChangeHom` to an `O`-algebra isomorphism
`completedGroupAlgebra.baseChange R O Γ : O ⊗[R] R[[Γ]] ≃ₐ[O] O[[Γ]]` without any commutativity or
compactness hypothesis on `Γ` or topological assumption on `R` and `O`.

## Main definitions

* `TauCeti.completedGroupAlgebra.mapRingHom Γ f`: the ring homomorphism `R[[Γ]] →+* S[[Γ]]` induced
  by `f : R →+* S`.
* `TauCeti.completedGroupAlgebra.mapAddMonoidHom Γ φ`: the additive map `O[[Γ]] →+ S[[Γ]]`
  applying `φ : O →+ S` to every coefficient at every level.
* `TauCeti.completedGroupAlgebra.baseChangeHom R O Γ`: the canonical `O`-algebra homomorphism
  `O ⊗[R] R[[Γ]] →ₐ[O] O[[Γ]]`.
* `TauCeti.completedGroupAlgebra.baseChange R O Γ`: for `O` finite and free over `R`, the
  `O`-algebra isomorphism `O ⊗[R] R[[Γ]] ≃ₐ[O] O[[Γ]]`.

## Main results

* `TauCeti.completedGroupAlgebra.proj_mapRingHom`, `TauCeti.completedGroupAlgebra.mapRingHom_of`,
  `TauCeti.completedGroupAlgebra.continuous_mapRingHom`: levelwise formula, behaviour on group
  elements, and continuity of `mapRingHom`.
* `TauCeti.completedGroupAlgebra.coeff_proj_mapAddMonoidHom`,
  `TauCeti.completedGroupAlgebra.continuous_mapAddMonoidHom`: coefficient formula and continuity of
  `mapAddMonoidHom`.
* `TauCeti.completedGroupAlgebra.baseChangeHom_bijective`: `baseChangeHom R O Γ` is bijective when
  `O` is finite and free over `R`.
* `TauCeti.completedGroupAlgebra.baseChange_tmul`,
  `TauCeti.completedGroupAlgebra.baseChange_tmul_of`,
  `TauCeti.completedGroupAlgebra.baseChange_symm_eq_sum_basis`: forward and inverse formulas for
  `baseChange`.

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

variable {R : Type u} {S : Type v} {T : Type z} [CommRing R] [CommRing S] [CommRing T]
  (Γ : Type w) [Group Γ] [TopologicalSpace Γ]

private theorem mapDomain_mapRingHom_proj {U V : OpenNormalSubgroup Γ} (hUV : U ≤ V)
    (f : R →+* S) (x : completedGroupAlgebra R Γ) :
    MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV)
        (MonoidAlgebra.mapRingHom (Γ ⧸ U.toSubgroup) f (proj R Γ U x)) =
      MonoidAlgebra.mapRingHom (Γ ⧸ V.toSubgroup) f (proj R Γ V x) := by
  have h := RingHom.congr_fun
    (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom f (QuotientGroup.mapOfLE hUV)) (proj R Γ U x)
  simpa only [RingHom.comp_apply, MonoidAlgebra.mapDomainRingHom_apply,
    mapDomain_mapOfLE_proj hUV] using h.symm

/-- Coefficient change `R[[Γ]] →+* S[[Γ]]` induced levelwise by a ring homomorphism
`f : R →+* S`. -/
def mapRingHom (f : R →+* S) : completedGroupAlgebra R Γ →+* completedGroupAlgebra S Γ where
  toFun x := mk S Γ
    (fun U ↦ MonoidAlgebra.mapRingHom (Γ ⧸ U.toSubgroup) f (proj R Γ U x))
    fun _ _ hUV ↦ mapDomain_mapRingHom_proj Γ hUV f x
  map_one' := ext fun U ↦ by simp [proj_mk]
  map_mul' x y := ext fun U ↦ by simp [proj_mk]
  map_zero' := ext fun U ↦ by simp [proj_mk]
  map_add' x y := ext fun U ↦ by simp [proj_mk]

variable {Γ}

/-- At level `U`, `mapRingHom Γ f` applies `MonoidAlgebra.mapRingHom` with `f`. -/
@[simp]
theorem proj_mapRingHom (f : R →+* S) (U : OpenNormalSubgroup Γ) (x : completedGroupAlgebra R Γ) :
    proj S Γ U (mapRingHom Γ f x) =
      MonoidAlgebra.mapRingHom (Γ ⧸ U.toSubgroup) f (proj R Γ U x) :=
  proj_mk S Γ _ _ U

/-- Each levelwise coefficient of `mapRingHom Γ f x` is `f` applied to the corresponding
coefficient of `x`. -/
theorem coeff_proj_mapRingHom (f : R →+* S) (U : OpenNormalSubgroup Γ)
    (x : completedGroupAlgebra R Γ) (g : Γ ⧸ U.toSubgroup) :
    (proj S Γ U (mapRingHom Γ f x)).coeff g = f ((proj R Γ U x).coeff g) := by
  simp [proj_mapRingHom]

/-- Coefficient change sends the group element `γ` in `R[[Γ]]` to `γ` in `S[[Γ]]`. -/
@[simp]
theorem mapRingHom_of (f : R →+* S) (γ : Γ) :
    mapRingHom Γ f (of R Γ γ) = of S Γ γ :=
  ext fun U ↦ by simp

/-- Coefficient change intertwines the scalar embeddings `R → R[[Γ]]` and `S → S[[Γ]]`. -/
@[simp]
theorem mapRingHom_algebraMap (f : R →+* S) (r : R) :
    mapRingHom Γ f (algebraMap R (completedGroupAlgebra R Γ) r) =
      algebraMap S (completedGroupAlgebra S Γ) (f r) :=
  ext fun U ↦ by simp [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def]

variable (Γ) in
/-- Coefficient change along the identity ring homomorphism is the identity. -/
@[simp]
theorem mapRingHom_id :
    mapRingHom Γ (RingHom.id R) = RingHom.id (completedGroupAlgebra R Γ) :=
  RingHom.ext fun _ ↦ ext fun _ ↦ by simp

variable (Γ) in
/-- Coefficient change is functorial under composition of ring homomorphisms. -/
theorem mapRingHom_comp (g : S →+* T) (f : R →+* S) :
    mapRingHom Γ (g.comp f) = (mapRingHom Γ g).comp (mapRingHom Γ f) :=
  RingHom.ext fun _ ↦ ext fun _ ↦ by simp [MonoidAlgebra.mapRingHom_comp]

/-- Coefficient change along an injective ring homomorphism is injective. -/
theorem mapRingHom_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (mapRingHom Γ f) := by
  intro x y hxy
  ext U : 1
  apply MonoidAlgebra.coeff_injective
  ext g
  have h1 := congrArg (fun z ↦ (proj S Γ U z).coeff g) hxy
  simp only [coeff_proj_mapRingHom] at h1
  exact hf h1

/-- Coefficient change along a continuous ring homomorphism is continuous for the inverse-limit
topologies. -/
theorem continuous_mapRingHom [TopologicalSpace R] [TopologicalSpace S] {f : R →+* S}
    (hf : Continuous f) : Continuous (mapRingHom Γ f) := by
  rw [continuous_iff]
  intro U g
  simp_rw [coeff_proj_mapRingHom]
  exact hf.comp (continuous_coeff_proj R Γ U g)

end MapRingHom

section MapAddMonoidHom

variable {O : Type u} {S : Type v} [CommRing O] [CommRing S]
  (Γ : Type w) [Group Γ] [TopologicalSpace Γ]

private def monoidAlgebraMapAdd (M : Type*) (φ : O →+ S) :
    MonoidAlgebra O M →+ MonoidAlgebra S M :=
  (MonoidAlgebra.coeffAddEquiv).symm.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom φ).comp MonoidAlgebra.coeffAddEquiv.toAddMonoidHom)

private theorem coeff_monoidAlgebraMapAdd {M : Type*} (φ : O →+ S)
    (x : MonoidAlgebra O M) (m : M) :
    (monoidAlgebraMapAdd M φ x).coeff m = φ (x.coeff m) := by
  simp [monoidAlgebraMapAdd]

private theorem mapDomain_monoidAlgebraMapAdd {M N : Type*} (e : M → N) (φ : O →+ S)
    (x : MonoidAlgebra O M) :
    MonoidAlgebra.mapDomain e (monoidAlgebraMapAdd M φ x) =
      monoidAlgebraMapAdd N φ (MonoidAlgebra.mapDomain e x) := by
  apply MonoidAlgebra.coeff_injective
  simpa [monoidAlgebraMapAdd] using
    Finsupp.mapDomain_mapRange e x.coeff φ (map_zero φ) (map_add φ)

/-- Levelwise additive coefficient map `O[[Γ]] →+ S[[Γ]]` induced by `φ : O →+ S`. -/
def mapAddMonoidHom (φ : O →+ S) : completedGroupAlgebra O Γ →+ completedGroupAlgebra S Γ where
  toFun y := mk S Γ
    (fun U ↦ monoidAlgebraMapAdd (Γ ⧸ U.toSubgroup) φ (proj O Γ U y))
    fun _ _ hUV ↦ by
      rw [mapDomain_monoidAlgebraMapAdd, mapDomain_mapOfLE_proj hUV]
  map_zero' := ext fun U ↦ by simp [proj_mk]
  map_add' x y := ext fun U ↦ by simp [proj_mk, map_add]

variable {Γ}

/-- At level `U`, each coefficient of `mapAddMonoidHom Γ φ y` is `φ` applied to the corresponding
coefficient of `y`. -/
@[simp]
theorem coeff_proj_mapAddMonoidHom (φ : O →+ S) (U : OpenNormalSubgroup Γ)
    (y : completedGroupAlgebra O Γ) (g : Γ ⧸ U.toSubgroup) :
    (proj S Γ U (mapAddMonoidHom Γ φ y)).coeff g = φ ((proj O Γ U y).coeff g) := by
  rw [mapAddMonoidHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk, proj_mk, coeff_monoidAlgebraMapAdd]

/-- `mapAddMonoidHom` intertwines scalar multiplication along `R` when `φ : O →ₗ[R] S` is
`R`-linear. -/
theorem mapAddMonoidHom_algebraMap_smul {R : Type z} [CommRing R] [Algebra R O] [Algebra R S]
    (φ : O →ₗ[R] S) (r : R) (y : completedGroupAlgebra O Γ) :
    mapAddMonoidHom Γ φ.toAddMonoidHom (algebraMap R O r • y) =
      algebraMap R S r • mapAddMonoidHom Γ φ.toAddMonoidHom y := by
  ext U : 1
  apply MonoidAlgebra.coeff_injective
  ext g
  simp [Finsupp.smul_apply]

/-- `mapAddMonoidHom Γ φ` is continuous whenever `φ` is continuous. -/
theorem continuous_mapAddMonoidHom [TopologicalSpace O] [TopologicalSpace S] {φ : O →+ S}
    (hφ : Continuous φ) : Continuous (mapAddMonoidHom Γ φ) := by
  rw [continuous_iff]
  intro U g
  simp_rw [coeff_proj_mapAddMonoidHom]
  exact hφ.comp (continuous_coeff_proj O Γ U g)

end MapAddMonoidHom

section BaseChange

variable (R : Type u) (O : Type v) (Γ : Type w) [CommRing R] [CommRing O] [Algebra R O]
  [Group Γ] [TopologicalSpace Γ]

private def baseChangeLevelAlgHom (U : OpenNormalSubgroup Γ) :
    O ⊗[R] completedGroupAlgebra R Γ →ₐ[O] MonoidAlgebra O (Γ ⧸ U.toSubgroup) :=
  let fU : completedGroupAlgebra R Γ →ₐ[R] MonoidAlgebra O (Γ ⧸ U.toSubgroup) :=
    { (MonoidAlgebra.mapRingHom (Γ ⧸ U.toSubgroup) (algebraMap R O)).comp
        (proj R Γ U).toRingHom with
      commutes' r := by simp [Algebra.algebraMap_eq_smul_one, MonoidAlgebra.one_def] }
  Algebra.TensorProduct.lift (Algebra.ofId O _) fU fun a x ↦ Algebra.commutes a (fU x)

private theorem baseChangeLevelAlgHom_tmul (U : OpenNormalSubgroup Γ) (a : O)
    (x : completedGroupAlgebra R Γ) :
    baseChangeLevelAlgHom R O Γ U (a ⊗ₜ[R] x) =
      a • MonoidAlgebra.mapRingHom (Γ ⧸ U.toSubgroup) (algebraMap R O) (proj R Γ U x) := by
  simp [baseChangeLevelAlgHom, Algebra.smul_def]

private theorem mapDomain_baseChangeLevelAlgHom {U V : OpenNormalSubgroup Γ} (hUV : U ≤ V)
    (z : O ⊗[R] completedGroupAlgebra R Γ) :
    MonoidAlgebra.mapDomain (QuotientGroup.mapOfLE hUV) (baseChangeLevelAlgHom R O Γ U z) =
      baseChangeLevelAlgHom R O Γ V z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    rw [baseChangeLevelAlgHom_tmul, baseChangeLevelAlgHom_tmul, MonoidAlgebra.mapDomain_smul,
      mapDomain_mapRingHom_proj Γ hUV (algebraMap R O) x]
  | add u v hu hv =>
    rw [map_add, map_add, MonoidAlgebra.mapDomain_add, hu, hv]

/-- **Base-change comparison homomorphism.** The canonical `O`-algebra homomorphism
`O ⊗[R] R[[Γ]] →ₐ[O] O[[Γ]]` sending `a ⊗ₜ x` to `a • mapRingHom Γ (algebraMap R O) x`. -/
def baseChangeHom : O ⊗[R] completedGroupAlgebra R Γ →ₐ[O] completedGroupAlgebra O Γ :=
  lift O Γ (baseChangeLevelAlgHom R O Γ) fun _ _ hUV z ↦
    mapDomain_baseChangeLevelAlgHom R O Γ hUV z

variable {R O Γ}

/-- On a pure tensor `a ⊗ₜ x`, `baseChangeHom` multiplies `mapRingHom Γ (algebraMap R O) x` by
`a`. -/
@[simp]
theorem baseChangeHom_tmul (a : O) (x : completedGroupAlgebra R Γ) :
    baseChangeHom R O Γ (a ⊗ₜ[R] x) = a • mapRingHom Γ (algebraMap R O) x :=
  ext fun U ↦ by simp [baseChangeHom, baseChangeLevelAlgHom_tmul]

/-- On `a ⊗ₜ of R Γ γ`, `baseChangeHom` produces `a • of O Γ γ`. -/
theorem baseChangeHom_tmul_of (a : O) (γ : Γ) :
    baseChangeHom R O Γ (a ⊗ₜ[R] of R Γ γ) = a • of O Γ γ := by
  simp

/-- Levelwise coefficient of `baseChangeHom R O Γ (a ⊗ₜ x)`. -/
theorem coeff_proj_baseChangeHom_tmul (a : O) (x : completedGroupAlgebra R Γ)
    (U : OpenNormalSubgroup Γ) (g : Γ ⧸ U.toSubgroup) :
    (proj O Γ U (baseChangeHom R O Γ (a ⊗ₜ[R] x))).coeff g =
      (proj R Γ U x).coeff g • a := by
  simp [Algebra.smul_def, mul_comm]

/-- Applying `mapAddMonoidHom Γ φ.toAddMonoidHom` for `φ : O →ₗ[R] R` to
`baseChangeHom R O Γ (a ⊗ₜ x)` extracts `φ a • x`. -/
theorem mapAddMonoidHom_baseChangeHom_tmul (φ : O →ₗ[R] R) (a : O)
    (x : completedGroupAlgebra R Γ) :
    mapAddMonoidHom Γ φ.toAddMonoidHom (baseChangeHom R O Γ (a ⊗ₜ[R] x)) = φ a • x := by
  ext U : 1
  apply MonoidAlgebra.coeff_injective
  ext g
  simp only [coeff_proj_mapAddMonoidHom, LinearMap.toAddMonoidHom_coe,
    coeff_proj_baseChangeHom_tmul, map_smul, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
    smul_eq_mul, mul_comm]

section FiniteFree

variable [Module.Free R O] [Module.Finite R O]

/-- **Bijectivity of finite free base change for the completed group algebra.** When `O` is finite
and free over `R`, `baseChangeHom R O Γ : O ⊗[R] R[[Γ]] →ₐ[O] O[[Γ]]` is bijective. -/
theorem baseChangeHom_bijective : Function.Bijective (baseChangeHom R O Γ) := by
  let b := Module.Free.chooseBasis R O
  let inv (y : completedGroupAlgebra O Γ) : O ⊗[R] completedGroupAlgebra R Γ :=
    ∑ i, b i ⊗ₜ[R] mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y
  have hleft : ∀ u, inv (baseChangeHom R O Γ u) = u := by
    intro u
    induction u using TensorProduct.inductionOn with
    | tmul a x =>
      simp only [inv, mapAddMonoidHom_baseChangeHom_tmul, ← TensorProduct.smul_tmul,
        ← TensorProduct.sum_tmul, b.coord_apply]
      rw [b.sum_repr]
    | add u v hu hv =>
      dsimp only [inv]
      rw [map_add]
      simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
      exact congrArg₂ (· + ·) hu hv
  refine ⟨Function.HasLeftInverse.injective ⟨inv, hleft⟩, fun y ↦ ⟨inv y, ?_⟩⟩
  ext U : 1
  apply MonoidAlgebra.coeff_injective
  ext g
  simp only [inv, map_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    coeff_proj_baseChangeHom_tmul, coeff_proj_mapAddMonoidHom, LinearMap.toAddMonoidHom_coe,
    b.coord_apply]
  exact b.sum_repr ((proj O Γ U y).coeff g)

variable (R O Γ) in
/-- **Finite free base change of the completed group algebra.** For `O` finite and free as an
`R`-module, `O ⊗[R] R[[Γ]]` is canonically isomorphic to `O[[Γ]]` as an `O`-algebra. -/
def baseChange : O ⊗[R] completedGroupAlgebra R Γ ≃ₐ[O] completedGroupAlgebra O Γ :=
  AlgEquiv.ofBijective (baseChangeHom R O Γ) baseChangeHom_bijective

/-- `baseChange R O Γ` has `baseChangeHom R O Γ` as its underlying function. -/
@[simp]
theorem coe_baseChange : ⇑(baseChange R O Γ) = baseChangeHom R O Γ :=
  (rfl)

/-- On a pure tensor `a ⊗ₜ x`, `baseChange R O Γ` evaluates to
`a • mapRingHom Γ (algebraMap R O) x`. -/
@[simp]
theorem baseChange_tmul (a : O) (x : completedGroupAlgebra R Γ) :
    baseChange R O Γ (a ⊗ₜ[R] x) = a • mapRingHom Γ (algebraMap R O) x :=
  baseChangeHom_tmul a x

/-- On `a ⊗ₜ of R Γ γ`, `baseChange R O Γ` evaluates to `a • of O Γ γ`. -/
theorem baseChange_tmul_of (a : O) (γ : Γ) :
    baseChange R O Γ (a ⊗ₜ[R] of R Γ γ) = a • of O Γ γ :=
  baseChangeHom_tmul_of a γ

/-- At level `U`, `baseChange R O Γ (a ⊗ₜ x)` has coefficients `(proj R Γ U x).coeff g • a`. -/
theorem coeff_proj_baseChange_tmul (a : O) (x : completedGroupAlgebra R Γ)
    (U : OpenNormalSubgroup Γ) (g : Γ ⧸ U.toSubgroup) :
    (proj O Γ U (baseChange R O Γ (a ⊗ₜ[R] x))).coeff g = (proj R Γ U x).coeff g • a :=
  coeff_proj_baseChangeHom_tmul a x U g

/-- Along any finite `R`-basis `b` of `O`, the inverse of `baseChange R O Γ` expands `y` into its
levelwise `b`-coordinate components `mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y`. -/
theorem baseChange_symm_eq_sum_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι R O)
    (y : completedGroupAlgebra O Γ) :
    (baseChange R O Γ).symm y =
      ∑ i, b i ⊗ₜ[R] mapAddMonoidHom Γ (b.coord i).toAddMonoidHom y := by
  apply (baseChange R O Γ).injective
  rw [AlgEquiv.apply_symm_apply]
  ext U : 1
  apply MonoidAlgebra.coeff_injective
  ext g
  simp only [map_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    coeff_proj_baseChange_tmul, coeff_proj_mapAddMonoidHom, LinearMap.toAddMonoidHom_coe,
    b.coord_apply]
  exact (b.sum_repr ((proj O Γ U y).coeff g)).symm

end FiniteFree

end BaseChange

/-! ### Checks -/

-- Over `O = R`, `baseChange R R Γ` is the canonical left unit `R ⊗[R] R[[Γ]] ≃ₐ[R] R[[Γ]]`.
example (R Γ : Type*) [CommRing R] [Group Γ] [TopologicalSpace Γ] :
    baseChange R R Γ = Algebra.TensorProduct.lid R (completedGroupAlgebra R Γ) := by
  apply AlgEquiv.coe_toAlgHom_injective
  ext x
  simp [Algebra.algebraMap_self]

-- Distinct scalars give distinct images of `a ⊗ₜ of R Γ γ` in `O[[Γ]]`.
example {R O Γ : Type*} [CommRing R] [CommRing O] [Algebra R O] [Module.Free R O]
    [Module.Finite R O] [Group Γ] [TopologicalSpace Γ] {a b : O} (hab : a ≠ b) (γ : Γ) :
    baseChange R O Γ (a ⊗ₜ[R] of R Γ γ) ≠ baseChange R O Γ (b ⊗ₜ[R] of R Γ γ) := by
  intro h
  have h1 :=
    congrArg (fun z ↦ (proj O Γ ⊤ z).coeff (γ : Γ ⧸ (⊤ : OpenNormalSubgroup Γ).toSubgroup)) h
  simp only [coeff_proj_baseChange_tmul, proj_of, MonoidAlgebra.coeff_single,
    Finsupp.single_eq_same, one_smul] at h1
  exact hab h1

end TauCeti.completedGroupAlgebra
