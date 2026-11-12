/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Localization.Away.Basic
import TauCeti.Algebra.Group.OneParameterGauss
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.RankOne

/-!
# Opposite-root Gauss factorization for a Kostant root pair

Let `U_ℤ = kostantForm e h` act on a rational vector space `V` through `ρ` and preserve an additive
subgroup `M ≤ V` equipped with a Cartan weight basis `(b, wt)`. Suppose `(eᵢ, eⱼ)` is a root pair
of weights `α` and `-α` whose images form an `sl₂` triple with the designated Cartan vector `h c`.
Over any commutative `ℤ`-algebra `A`, write `xᵢ` and `xⱼ` for the two divided-power root subgroups
on `A ⊗[ℤ] M` and `h_c` for the coordinate cocharacter at `c`. Whenever `r, s ∈ A` satisfy
`u = 1 + r s ∈ Aˣ`, the opposite-root products factor in both multiplication orders as

```text
xᵢ(r) xⱼ(s) = xⱼ(s u⁻¹) h_c(u) xᵢ(r u⁻¹),
xⱼ(s) xᵢ(r) = xᵢ(r u⁻¹) h_c(u⁻¹) xⱼ(s u⁻¹).
```

Neither `r` nor `s` is assumed invertible, no factorial is inverted in `A`, and no bound is placed
on the nilpotency class of `ρ(eᵢ)` or `ρ(eⱼ)`. In particular, the identities hold over arbitrary
commutative rings—including characteristic `2` and `3`, rings with nilpotent or torsion elements,
and the zero ring—and apply directly to representations such as the adjoint module where root
strings have length three or four.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupParam_mul_kostantRootSubgroupParam_e_f`:
  the raising-times-lowering Gauss factorization `xᵢ(r) xⱼ(s) = xⱼ(s u⁻¹) h_c(u) xᵢ(r u⁻¹)`.
* `TauCeti.UniversalEnvelopingAlgebra.kostantRootSubgroupParam_mul_kostantRootSubgroupParam_f_e`:
  the lowering-times-raising Gauss factorization `xⱼ(s) xᵢ(r) = xᵢ(r u⁻¹) h_c(u⁻¹) xⱼ(s u⁻¹)`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 3, Lemmas 19--20.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 12.1.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§26--27.
-/

public section

open TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]
variable {ι : Type*} {κ : Type*}
variable {V : Type v} [AddCommGroup V] [Module ℚ V]

variable (e : ι → L) (h : κ → L)
variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)
variable (M : AddSubgroup V)
variable (hM : ∀ u ∈ kostantForm e h, ∀ v ∈ M, ρ u v ∈ M)

attribute [local instance 100] LieRing.ofAssociativeRing

-- Match tensor products to the `ℤ`-algebra instance stored by `CommAlgCat` objects.
attribute [local instance high] Algebra.toModule

private abbrev GaussPoly := MvPolynomial (ULift.{w} (Fin 2)) ℤ

private noncomputable def gaussPolyP₀ : GaussPoly.{w} :=
  1 + MvPolynomial.X (.up 0) * MvPolynomial.X (.up 1)

private theorem gaussPolyP₀_ne_zero : gaussPolyP₀.{w} ≠ 0 := by
  intro hzero
  have hcoeff := congrArg MvPolynomial.constantCoeff hzero
  simp [gaussPolyP₀] at hcoeff

private noncomputable abbrev gaussUnivObj : CommAlgCat.{w} ℤ :=
  CommAlgCat.of ℤ (Localization.Away gaussPolyP₀.{w})

private noncomputable def gaussUnivR : gaussUnivObj.{w} :=
  algebraMap GaussPoly.{w} (Localization.Away gaussPolyP₀.{w}) (MvPolynomial.X (.up 0))

private noncomputable def gaussUnivS : gaussUnivObj.{w} :=
  algebraMap GaussPoly.{w} (Localization.Away gaussPolyP₀.{w}) (MvPolynomial.X (.up 1))

private noncomputable def gaussUnivU : (gaussUnivObj.{w})ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away gaussPolyP₀.{w}) gaussPolyP₀.{w}).unit

private theorem gaussUnivU_val :
    (gaussUnivU.{w} : gaussUnivObj.{w}) =
      algebraMap GaussPoly.{w} (Localization.Away gaussPolyP₀.{w}) gaussPolyP₀.{w} :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := Localization.Away gaussPolyP₀.{w}) gaussPolyP₀.{w}).unit_spec

/-- Embed `gaussUnivObj = ℤ[x₀, x₁][(1 + x₀ x₁)⁻¹]` injectively into the principal localization
`ℤ[x₀, x₁][(x₀ x₁ (1 + x₀ x₁))⁻¹]` where `x₀`, `x₁`, and `1 + x₀ x₁` are all units. -/
private theorem exists_gaussUniv_embedding :
    ∃ (B₁ : CommAlgCat.{w} ℤ) (ι : gaussUnivObj.{w} ⟶ B₁) (sK tK uK : B₁ˣ),
      Function.Injective ι.hom ∧
      (uK : B₁) = 1 + (sK : B₁) * (tK : B₁) ∧
      ι.hom gaussUnivR.{w} = (sK : B₁) ∧
      ι.hom gaussUnivS.{w} = (tK : B₁) ∧
      Units.map ι.hom.toRingHom.toMonoidHom gaussUnivU.{w} = uK := by
  let x₀ : GaussPoly.{w} := MvPolynomial.X (.up 0)
  let x₁ : GaussPoly.{w} := MvPolynomial.X (.up 1)
  let q₀ : GaussPoly.{w} := x₀ * x₁ * gaussPolyP₀.{w}
  have hq₀ : q₀ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _))
      gaussPolyP₀_ne_zero
  let K := Localization.Away q₀
  have hsK : IsUnit (algebraMap GaussPoly.{w} K x₀) :=
    IsLocalization.Away.isUnit_of_dvd q₀ ⟨x₁ * gaussPolyP₀.{w}, by ring⟩
  have htK : IsUnit (algebraMap GaussPoly.{w} K x₁) :=
    IsLocalization.Away.isUnit_of_dvd q₀ ⟨x₀ * gaussPolyP₀.{w}, by ring⟩
  have hp₀K : IsUnit (algebraMap GaussPoly.{w} K gaussPolyP₀.{w}) :=
    IsLocalization.Away.isUnit_of_dvd q₀ ⟨x₀ * x₁, by ring⟩
  let B₁ : CommAlgCat.{w} ℤ := CommAlgCat.of ℤ K
  let fK : GaussPoly.{w} →ₐ[ℤ] K := IsScalarTower.toAlgHom ℤ GaussPoly.{w} K
  have hp₀K' : IsUnit (fK gaussPolyP₀.{w}) := hp₀K
  let ι₀ : Localization.Away gaussPolyP₀.{w} →ₐ[ℤ] K :=
    IsLocalization.Away.liftAlgHom (A := ℤ) (S := Localization.Away gaussPolyP₀.{w})
      gaussPolyP₀.{w} (f := fK) hp₀K'
  have hPp₀ : Function.Injective (algebraMap GaussPoly.{w} (Localization.Away gaussPolyP₀.{w})) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors gaussPolyP₀_ne_zero)
  have hPK : Function.Injective (algebraMap GaussPoly.{w} K) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hq₀)
  have hι₀_inj : Function.Injective ι₀ := by
    dsimp only [ι₀]
    rw [IsLocalization.Away.coe_liftAlgHom]
    exact (IsLocalization.lift_injective_iff _).mpr fun _ _ => hPp₀.eq_iff.trans hPK.eq_iff.symm
  refine ⟨B₁, CommAlgCat.ofHom ι₀, hsK.unit, htK.unit, hp₀K.unit,
    hι₀_inj, ?_, ?_, ?_, ?_⟩
  · rw [IsUnit.unit_spec, IsUnit.unit_spec, IsUnit.unit_spec]
    -- Expose the carrier `K` so `simp` expands `algebraMap` on `gaussPolyP₀`.
    change algebraMap GaussPoly.{w} K gaussPolyP₀.{w} =
      1 + algebraMap GaussPoly.{w} K x₀ * algebraMap GaussPoly.{w} K x₁
    simp [gaussPolyP₀, x₀, x₁]
  · simp [ι₀, fK, gaussUnivR, x₀]
  · simp [ι₀, fK, gaussUnivS, x₁]
  · apply Units.ext
    simp [ι₀, fK, gaussUnivU_val]

/-- Specialize `gaussUnivObj = ℤ[x₀, x₁][(1 + x₀ x₁)⁻¹]` to any `A : CommAlgCat ℤ` along
`(x₀, x₁) ↦ (r, s)` whenever `u = 1 + r * s` is a unit of `A`. -/
private theorem exists_gaussUniv_specialization (A : CommAlgCat.{w} ℤ) (r s : A) (u : Aˣ)
    (hu : (u : A) = 1 + r * s) :
    ∃ ψ : gaussUnivObj.{w} ⟶ A,
      ψ.hom gaussUnivR.{w} = r ∧
      ψ.hom gaussUnivS.{w} = s ∧
      Units.map ψ.hom.toRingHom.toMonoidHom gaussUnivU.{w} = u := by
  let evP : GaussPoly.{w} →ₐ[ℤ] A :=
    MvPolynomial.aeval (fun k => if k.down = 0 then r else s)
  have hevP_x₀ : evP (MvPolynomial.X (.up 0)) = r :=
    MvPolynomial.aeval_X (fun k : ULift.{w} (Fin 2) => if k.down = 0 then r else s) ⟨0⟩
  have hevP_x₁ : evP (MvPolynomial.X (.up 1)) = s :=
    MvPolynomial.aeval_X (fun k : ULift.{w} (Fin 2) => if k.down = 0 then r else s) ⟨1⟩
  have hevP_p₀ : evP gaussPolyP₀.{w} = (u : A) := by
    rw [hu]
    simp [gaussPolyP₀, hevP_x₀, hevP_x₁]
  have hp₀_unit : IsUnit (evP gaussPolyP₀.{w}) := hevP_p₀ ▸ u.isUnit
  let ψ₀ : Localization.Away gaussPolyP₀.{w} →ₐ[ℤ] A :=
    IsLocalization.Away.liftAlgHom (A := ℤ) (S := Localization.Away gaussPolyP₀.{w})
      gaussPolyP₀.{w} (f := evP) hp₀_unit
  refine ⟨CommAlgCat.ofHom ψ₀, ?_, ?_, ?_⟩
  · simp [ψ₀, gaussUnivR, hevP_x₀]
  · simp [ψ₀, gaussUnivS, hevP_x₁]
  · apply Units.ext
    simp [ψ₀, gaussUnivU_val, hevP_p₀]

section Gauss

variable {i j : ι}
variable (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))

/-- Solve Steinberg's Weyl definition `n_α(v) = xᵢ(v) xⱼ(-v⁻¹) xᵢ(v)` for the left factor
`xᵢ(v)`. -/
private theorem kostantRootSubgroupParam_e_eq_kostantWeylParam_mul
    (K : CommAlgCat.{w} ℤ) (v : Kˣ) :
    kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd (v : K)) =
      kostantWeylParam e h ρ M hM hi hj K v *
        kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd (-(v : K))) *
        kostantRootSubgroupParam e h ρ M hM j hj K (Multiplicative.ofAdd ((v⁻¹ : Kˣ) : K)) := by
  have hn := kostantWeylParam_def e h ρ M hM hi hj K v
  rw [ofAdd_neg, map_inv] at hn
  rw [ofAdd_neg, map_inv, hn]
  group

private theorem gauss_group_rearrange {G : Type*} [Group G] {xj b' a w₁ xv w₂ d' f g h' : G}
    (hxj : xj = a * w₁ * a) (hadd : a * b' = xv) (hxi : xv = w₂ * d' * f)
    (hnn : w₁ * w₂ = g) (hconj : g * d' * g⁻¹ = h') :
    xj * b' = (a * h') * g * f := by
  have hab : b' = a⁻¹ * (w₂ * d' * f) := eq_inv_mul_of_mul_eq (hadd.trans hxi)
  have hd : d' = g⁻¹ * h' * g := by rw [← hconj]; group
  have hw₂ : w₂ = w₁⁻¹ * g := eq_inv_mul_of_mul_eq hnn
  rw [hxj, hab, hd, hw₂]
  group

variable {η : Type*} (b : Module.Basis η ℤ M) (wt : η → κ → ℤ)
variable [Fintype κ] [DecidableEq κ]

private theorem mapScalarExtensionAutomorphisms_gauss_rhs
    {c : κ} {B₀ B₁ : CommAlgCat.{w} ℤ} (φ : B₀ ⟶ B₁)
    {r₀ s₀ : B₀} {u₀ : B₀ˣ} {r₁ s₁ : B₁} {u₁ : B₁ˣ}
    (hr : φ.hom r₀ = r₁) (hs : φ.hom s₀ = s₁)
    (hu : Units.map φ.hom.toRingHom.toMonoidHom u₀ = u₁) :
    GeneralLinear.mapScalarExtensionAutomorphisms (V := M) φ
        (kostantRootSubgroupParam e h ρ M hM i hi B₀ (Multiplicative.ofAdd (r₀ * ↑u₀⁻¹)) *
          kostantCoordinateCocharacter M b wt B₀ c u₀⁻¹ *
          kostantRootSubgroupParam e h ρ M hM j hj B₀ (Multiplicative.ofAdd (s₀ * ↑u₀⁻¹))) =
      kostantRootSubgroupParam e h ρ M hM i hi B₁ (Multiplicative.ofAdd (r₁ * ↑u₁⁻¹)) *
        kostantCoordinateCocharacter M b wt B₁ c u₁⁻¹ *
        kostantRootSubgroupParam e h ρ M hM j hj B₁ (Multiplicative.ofAdd (s₁ * ↑u₁⁻¹)) := by
  have : Module.Free ℤ M := Module.Free.of_basis b
  have hu_inv : φ.hom ((u₀⁻¹ : B₀ˣ) : B₀) = ((u₁⁻¹ : B₁ˣ) : B₁) := by
    rw [← hu, Units.coe_map_inv]
    simp
  rw [map_mul, map_mul,
    mapScalarExtensionAutomorphisms_kostantRootSubgroupParam,
    mapScalarExtensionAutomorphisms_kostantRootSubgroupParam,
    mapScalarExtensionAutomorphisms_kostantCoordinateCocharacter,
    toAdd_ofAdd, toAdd_ofAdd, map_mul φ.hom, map_mul φ.hom,
    map_inv (Units.map φ.hom.toRingHom.toMonoidHom), hr, hs, hu, hu_inv]

variable (hwt : ∀ x, IsCartanWeightVector h ρ (wt x) ((b x : M) : V))
variable {c : κ} {α : κ → ℤ}
variable (hT : IsSl2Triple (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (h c)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i)))
  (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
variable (hα : ∀ j', ⁅h j', e i⁆ = (α j' : ℚ) • e i)
variable (hαneg : ∀ j', ⁅h j', e j⁆ = -((α j' : ℚ) • e j))

include hwt hT hα hαneg

/-- When both root parameters `s` and `t` as well as `u = 1 + s t` are units, the opposite-root
product `xⱼ(t) xᵢ(s)` factors through Steinberg's Weyl elements `n_α(-t⁻¹)` and `n_α(t⁻¹ u)`,
whose product is the coroot value `h_c(u⁻¹)`. -/
private theorem kostantRootSubgroupParam_mul_kostantRootSubgroupParam_f_e_of_units
    (K : CommAlgCat.{w} ℤ) (s t u : Kˣ) (hu : (u : K) = 1 + (s : K) * (t : K)) :
    kostantRootSubgroupParam e h ρ M hM j hj K (Multiplicative.ofAdd (t : K)) *
        kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd (s : K)) =
      kostantRootSubgroupParam e h ρ M hM i hi K
          (Multiplicative.ofAdd ((s : K) * ((u⁻¹ : Kˣ) : K))) *
        kostantCoordinateCocharacter M b wt K c u⁻¹ *
        kostantRootSubgroupParam e h ρ M hM j hj K
          (Multiplicative.ofAdd ((t : K) * ((u⁻¹ : Kˣ) : K))) := by
  let v : Kˣ := t⁻¹ * u
  have hv_val : (v : K) = ((t⁻¹ : Kˣ) : K) + (s : K) := by
    rw [Units.val_mul]
    linear_combination ((t⁻¹ : Kˣ) : K) * hu + (s : K) * Units.inv_mul t
  have hv_inv_val : ((v⁻¹ : Kˣ) : K) = (t : K) * ((u⁻¹ : Kˣ) : K) := by
    simp [v, mul_inv_rev, mul_comm]
  have hxj := kostantRootSubgroupParam_f_eq_mul_kostantWeylParam e h ρ M hM hi hj K t
  have hxi := kostantRootSubgroupParam_e_eq_kostantWeylParam_mul e h ρ M hM hi hj K v
  -- Multiply the two Weyl elements into `h_c(u⁻¹)`.
  have hnn :
      kostantWeylParam e h ρ M hM hi hj K (-t⁻¹) * kostantWeylParam e h ρ M hM hi hj K v =
        kostantCoordinateCocharacter M b wt K c u⁻¹ := by
    rw [kostantWeylParam_mul_kostantWeylParam e h ρ M hM hi hj b wt hwt hT hα hαneg]
    congr 1
    simp [v, mul_inv_rev, mul_left_comm, mul_comm]
  -- Conjugate `xᵢ(-v)` past `h_c(u⁻¹)`.
  have hc : α c = 2 := rootWeight_apply_coroot_eq_two e h ρ hT (hα c)
  have hconj := kostantTorusPoints_conj_kostantRootSubgroupParam e h ρ M hM b wt hwt hα hi K
    (Pi.mulSingle c u⁻¹) (Multiplicative.ofAdd (-(v : K)))
  rw [← kostantCoordinateCocharacter_apply, torusCharacter_mulSingle, hc, toAdd_ofAdd,
    zpow_ofNat] at hconj
  -- Assemble the product and simplify the left `xᵢ` parameter.
  have hparam :
      ((t⁻¹ : Kˣ) : K) + ((u⁻¹ ^ 2 : Kˣ) : K) * -(v : K) =
        (s : K) * ((u⁻¹ : Kˣ) : K) := by
    simp only [v, Units.val_pow_eq_pow_val, Units.val_mul]
    linear_combination
      -(((t⁻¹ : Kˣ) : K) * (1 + ((u⁻¹ : Kˣ) : K))) * Units.mul_inv u +
        ((t⁻¹ : Kˣ) : K) * ((u⁻¹ : Kˣ) : K) * hu +
        (s : K) * ((u⁻¹ : Kˣ) : K) * Units.inv_mul t
  have hadd_left :
      kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd ((t⁻¹ : Kˣ) : K)) *
          kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd (s : K)) =
        kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd (v : K)) := by
    rw [← map_mul, ← ofAdd_add, ← hv_val]
  rw [gauss_group_rearrange hxj hadd_left hxi hnn hconj, ← map_mul, ← ofAdd_add, hparam,
    hv_inv_val]

/-- Transport the unit-parameter Gauss factorization from `B₁` back along an injective scalar
extension `ι : B₀ ⟶ B₁` and forward along a specialization `ψ : B₀ ⟶ A`. Keeping `B₀` and `B₁`
as `CommAlgCat ℤ` parameters ensures uniform `ℤ`-algebra instances throughout the rewrite. -/
private theorem kostantRootSubgroupParam_mul_kostantRootSubgroupParam_f_e_of_universal
    {B₀ B₁ A : CommAlgCat.{w} ℤ} (ι : B₀ ⟶ B₁) (hι_inj : Function.Injective ι.hom)
    (ψ : B₀ ⟶ A) (r₀ s₀ : B₀) (u₀ : B₀ˣ)
    (sK tK uK : B₁ˣ) (huK : (uK : B₁) = 1 + (sK : B₁) * (tK : B₁))
    (hι_r₀ : ι.hom r₀ = (sK : B₁)) (hι_s₀ : ι.hom s₀ = (tK : B₁))
    (hι_u₀ : Units.map ι.hom.toRingHom.toMonoidHom u₀ = uK)
    (r s : A) (u : Aˣ)
    (hψ_r₀ : ψ.hom r₀ = r) (hψ_s₀ : ψ.hom s₀ = s)
    (hψ_u₀ : Units.map ψ.hom.toRingHom.toMonoidHom u₀ = u) :
    kostantRootSubgroupParam e h ρ M hM j hj A (Multiplicative.ofAdd s) *
        kostantRootSubgroupParam e h ρ M hM i hi A (Multiplicative.ofAdd r) =
      kostantRootSubgroupParam e h ρ M hM i hi A (Multiplicative.ofAdd (r * ↑u⁻¹)) *
        kostantCoordinateCocharacter M b wt A c u⁻¹ *
        kostantRootSubgroupParam e h ρ M hM j hj A (Multiplicative.ofAdd (s * ↑u⁻¹)) := by
  have : Module.Free ℤ M := Module.Free.of_basis b
  have huniv :
      kostantRootSubgroupParam e h ρ M hM j hj B₀ (Multiplicative.ofAdd s₀) *
          kostantRootSubgroupParam e h ρ M hM i hi B₀ (Multiplicative.ofAdd r₀) =
        kostantRootSubgroupParam e h ρ M hM i hi B₀
            (Multiplicative.ofAdd (r₀ * ((u₀⁻¹ : B₀ˣ) : B₀))) *
          kostantCoordinateCocharacter M b wt B₀ c u₀⁻¹ *
          kostantRootSubgroupParam e h ρ M hM j hj B₀
            (Multiplicative.ofAdd (s₀ * ((u₀⁻¹ : B₀ˣ) : B₀))) := by
    apply GeneralLinear.mapScalarExtensionAutomorphisms_injective ι
      (GeneralLinear.scalarExtensionMap_injective ι hι_inj)
    rw [map_mul, mapScalarExtensionAutomorphisms_kostantRootSubgroupParam,
      mapScalarExtensionAutomorphisms_kostantRootSubgroupParam, toAdd_ofAdd, toAdd_ofAdd,
      hι_s₀, hι_r₀,
      mapScalarExtensionAutomorphisms_gauss_rhs e h ρ M hM hi hj b wt ι hι_r₀ hι_s₀ hι_u₀]
    exact kostantRootSubgroupParam_mul_kostantRootSubgroupParam_f_e_of_units
      e h ρ M hM hi hj b wt hwt hT hα hαneg B₁ sK tK uK huK
  have hspec := congrArg (GeneralLinear.mapScalarExtensionAutomorphisms (V := M) ψ) huniv
  rwa [map_mul, mapScalarExtensionAutomorphisms_kostantRootSubgroupParam,
    mapScalarExtensionAutomorphisms_kostantRootSubgroupParam, toAdd_ofAdd, toAdd_ofAdd,
    hψ_s₀, hψ_r₀,
    mapScalarExtensionAutomorphisms_gauss_rhs e h ρ M hM hi hj b wt ψ hψ_r₀ hψ_s₀ hψ_u₀] at hspec

/-- **Opposite-root Gauss factorization (lowering times raising).** Whenever `u = 1 + r s` is a
unit of the value ring `A`, the product `xⱼ(s) xᵢ(r)` factors as
`xᵢ(r u⁻¹) h_c(u⁻¹) xⱼ(s u⁻¹)`. -/
theorem kostantRootSubgroupParam_mul_kostantRootSubgroupParam_f_e
    (A : CommAlgCat.{w} ℤ) (r s : A) (u : Aˣ) (hu : (u : A) = 1 + r * s) :
    kostantRootSubgroupParam e h ρ M hM j hj A (Multiplicative.ofAdd s) *
        kostantRootSubgroupParam e h ρ M hM i hi A (Multiplicative.ofAdd r) =
      kostantRootSubgroupParam e h ρ M hM i hi A (Multiplicative.ofAdd (r * ↑u⁻¹)) *
        kostantCoordinateCocharacter M b wt A c u⁻¹ *
        kostantRootSubgroupParam e h ρ M hM j hj A (Multiplicative.ofAdd (s * ↑u⁻¹)) := by
  obtain ⟨B₁, ι, sK, tK, uK, hι_inj, huK, hι_r₀, hι_s₀, hι_u₀⟩ := exists_gaussUniv_embedding.{w}
  obtain ⟨ψ, hψ_r₀, hψ_s₀, hψ_u₀⟩ := exists_gaussUniv_specialization A r s u hu
  exact kostantRootSubgroupParam_mul_kostantRootSubgroupParam_f_e_of_universal
    e h ρ M hM hi hj b wt hwt hT hα hαneg ι hι_inj ψ
    gaussUnivR gaussUnivS gaussUnivU sK tK uK huK hι_r₀ hι_s₀ hι_u₀
    r s u hψ_r₀ hψ_s₀ hψ_u₀

/-- **Opposite-root Gauss factorization (raising times lowering).** Whenever `u = 1 + r s` is a
unit of the value ring `A`, the product `xᵢ(r) xⱼ(s)` factors as
`xⱼ(s u⁻¹) h_c(u) xᵢ(r u⁻¹)`. -/
theorem kostantRootSubgroupParam_mul_kostantRootSubgroupParam_e_f
    (A : CommAlgCat.{w} ℤ) (r s : A) (u : Aˣ) (hu : (u : A) = 1 + r * s) :
    kostantRootSubgroupParam e h ρ M hM i hi A (Multiplicative.ofAdd r) *
        kostantRootSubgroupParam e h ρ M hM j hj A (Multiplicative.ofAdd s) =
      kostantRootSubgroupParam e h ρ M hM j hj A (Multiplicative.ofAdd (s * ↑u⁻¹)) *
        kostantCoordinateCocharacter M b wt A c u *
        kostantRootSubgroupParam e h ρ M hM i hi A (Multiplicative.ofAdd (r * ↑u⁻¹)) := by
  simpa only [inv_inv] using
    map_ofAdd_mul_map_ofAdd_eq_of_map_ofAdd_neg_mul_map_ofAdd_neg_eq
      (kostantRootSubgroupParam_mul_kostantRootSubgroupParam_f_e (c := c) (α := α)
        e h ρ M hM hi hj b wt hwt hT hα hαneg A (-r) (-s) u (by rwa [neg_mul_neg]))

end Gauss

end TauCeti.UniversalEnvelopingAlgebra
