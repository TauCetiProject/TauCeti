/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Torus.Basic
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Weyl.RankOne
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

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

section Gauss

variable {i j : ι}
variable (hi : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))
variable (hj : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e j))))
variable {η : Type*} (b : Module.Basis η ℤ M) (wt : η → κ → ℤ)
variable [Fintype κ] [DecidableEq κ]
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
    rw [Units.val_mul, hu, mul_add, mul_one, ← mul_assoc, mul_comm ((t⁻¹ : Kˣ) : K) (s : K),
      mul_assoc, Units.inv_mul, mul_one]
  have hv_inv_val : ((v⁻¹ : Kˣ) : K) = (t : K) * ((u⁻¹ : Kˣ) : K) := by
    simp [v, mul_inv_rev, mul_comm]
  -- Solve `n_α(-t⁻¹) = xᵢ(-t⁻¹) xⱼ(t) xᵢ(-t⁻¹)` for `xⱼ(t)`.
  have hxj :
      kostantRootSubgroupParam e h ρ M hM j hj K (Multiplicative.ofAdd (t : K)) =
        kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd ((t⁻¹ : Kˣ) : K)) *
          kostantWeylParam e h ρ M hM hi hj K (-t⁻¹) *
          kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd ((t⁻¹ : Kˣ) : K)) := by
    have hcancel : ∀ {G : Type (max v w)} [Group G] {x w a : G},
        w = a⁻¹ * x * a⁻¹ → x = a * w * a := by
      intro G _ x w a hw
      symm
      rw [hw, ← mul_assoc a (a⁻¹ * x) a⁻¹, mul_inv_cancel_left, inv_mul_cancel_right]
    have hn := kostantWeylParam_def e h ρ M hM hi hj K (-t⁻¹)
    have hpar : -(((-t⁻¹)⁻¹ : Kˣ) : K) = (t : K) := by simp
    rw [Units.val_neg, hpar, ofAdd_neg, map_inv] at hn
    exact hcancel hn
  -- Solve `n_α(v) = xᵢ(v) xⱼ(-v⁻¹) xᵢ(v)` for the left factor `xᵢ(v)`.
  have hxi :
      kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd (v : K)) =
        kostantWeylParam e h ρ M hM hi hj K v *
          kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd (-(v : K))) *
          kostantRootSubgroupParam e h ρ M hM j hj K (Multiplicative.ofAdd ((v⁻¹ : Kˣ) : K)) := by
    have hcancel : ∀ {G : Type (max v w)} [Group G] {a b' w : G},
        w = a * b'⁻¹ * a → a = w * a⁻¹ * b' := by
      intro G _ a b' w hw
      symm
      rw [hw, mul_inv_cancel_right, inv_mul_cancel_right]
    have hn := kostantWeylParam_def e h ρ M hM hi hj K v
    rw [ofAdd_neg, map_inv] at hn
    rw [ofAdd_neg, map_inv]
    exact hcancel hn
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
    calc
      ((t⁻¹ : Kˣ) : K) + ((u⁻¹ ^ 2 : Kˣ) : K) * -(v : K)
        = ((t⁻¹ : Kˣ) : K) * ((u : K) * ((u⁻¹ : Kˣ) : K)) -
            ((u⁻¹ : Kˣ) : K) * (((u⁻¹ : Kˣ) : K) * (u : K)) * ((t⁻¹ : Kˣ) : K) := by
          rw [Units.val_pow_eq_pow_val, sq, Units.val_mul t⁻¹ u, Units.mul_inv u, mul_one,
            mul_neg, sub_eq_add_neg]
          congr 2
          rw [mul_assoc ((u⁻¹ : Kˣ) : K), mul_comm ((t⁻¹ : Kˣ) : K) (u : K),
            ← mul_assoc ((u⁻¹ : Kˣ) : K) (u : K), ← mul_assoc]
      _ = ((t⁻¹ : Kˣ) : K) * (1 + (s : K) * (t : K)) * ((u⁻¹ : Kˣ) : K) -
            ((t⁻¹ : Kˣ) : K) * ((u⁻¹ : Kˣ) : K) := by
          rw [Units.inv_mul u, mul_one, hu, ← mul_assoc,
            mul_comm ((u⁻¹ : Kˣ) : K) ((t⁻¹ : Kˣ) : K)]
      _ = (s : K) * ((u⁻¹ : Kˣ) : K) := by
          rw [mul_add, mul_one, add_mul, add_sub_cancel_left, ← mul_assoc,
            mul_comm ((t⁻¹ : Kˣ) : K) (s : K), mul_assoc (s : K), Units.inv_mul t, mul_one]
  have hadd_left :
      kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd ((t⁻¹ : Kˣ) : K)) *
          kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd (s : K)) =
        kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd (v : K)) := by
    rw [← map_mul, ← ofAdd_add, ← hv_val]
  let a := kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd ((t⁻¹ : Kˣ) : K))
  let w₁ := kostantWeylParam e h ρ M hM hi hj K (-t⁻¹)
  let b' := kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd (s : K))
  let w₂ := kostantWeylParam e h ρ M hM hi hj K v
  let d' := kostantRootSubgroupParam e h ρ M hM i hi K (Multiplicative.ofAdd (-(v : K)))
  let f := kostantRootSubgroupParam e h ρ M hM j hj K (Multiplicative.ofAdd ((v⁻¹ : Kˣ) : K))
  let g := kostantCoordinateCocharacter M b wt K c u⁻¹
  let h' := kostantRootSubgroupParam e h ρ M hM i hi K
    (Multiplicative.ofAdd (((u⁻¹ ^ 2 : Kˣ) : K) * -(v : K)))
  rw [hxj, mul_assoc (a * w₁) a b', hadd_left, hxi, ← mul_assoc (a * w₁) (w₂ * d') f,
    mul_assoc a w₁ (w₂ * d'), ← mul_assoc w₁ w₂ d', hnn,
    ← inv_mul_cancel_right (g * d') g, hconj, ← mul_assoc a h' g]
  dsimp only [a, h', f]
  rw [← map_mul, ← ofAdd_add, hparam, hv_inv_val]

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
  have hι_u₀_inv : ι.hom ((u₀⁻¹ : B₀ˣ) : B₀) = ((uK⁻¹ : B₁ˣ) : B₁) := by
    rw [← hι_u₀, ← map_inv]
    rfl
  have hψ_u₀_inv : ψ.hom ((u₀⁻¹ : B₀ˣ) : B₀) = ((u⁻¹ : Aˣ) : A) := by
    rw [← hψ_u₀, ← map_inv]
    rfl
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
    rw [map_mul, map_mul, map_mul,
      mapScalarExtensionAutomorphisms_kostantRootSubgroupParam,
      mapScalarExtensionAutomorphisms_kostantRootSubgroupParam,
      mapScalarExtensionAutomorphisms_kostantRootSubgroupParam,
      mapScalarExtensionAutomorphisms_kostantRootSubgroupParam,
      mapScalarExtensionAutomorphisms_kostantCoordinateCocharacter,
      toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd,
      map_mul ι.hom, map_mul ι.hom, map_inv (Units.map ι.hom.toRingHom.toMonoidHom),
      hι_r₀, hι_s₀, hι_u₀, hι_u₀_inv]
    exact kostantRootSubgroupParam_mul_kostantRootSubgroupParam_f_e_of_units
      e h ρ M hM hi hj b wt hwt hT hα hαneg B₁ sK tK uK huK
  have hspec := congrArg (GeneralLinear.mapScalarExtensionAutomorphisms (V := M) ψ) huniv
  rw [map_mul, map_mul, map_mul,
    mapScalarExtensionAutomorphisms_kostantRootSubgroupParam,
    mapScalarExtensionAutomorphisms_kostantRootSubgroupParam,
    mapScalarExtensionAutomorphisms_kostantRootSubgroupParam,
    mapScalarExtensionAutomorphisms_kostantRootSubgroupParam,
    mapScalarExtensionAutomorphisms_kostantCoordinateCocharacter,
    toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd,
    map_mul ψ.hom, map_mul ψ.hom, map_inv (Units.map ψ.hom.toRingHom.toMonoidHom),
    hψ_r₀, hψ_s₀, hψ_u₀, hψ_u₀_inv] at hspec
  exact hspec

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
  -- Construct the universal localization `R₀ = ℤ[x₀, x₁][(1 + x₀ x₁)⁻¹]`, embed it into the
  -- principal localization `K = ℤ[x₀, x₁][(x₀ x₁ (1 + x₀ x₁))⁻¹]` where `x₀`, `x₁`, and
  -- `1 + x₀ x₁` are all units, and specialize `R₀ → A` along `(x₀, x₁) ↦ (r, s)`.
  let P := MvPolynomial (ULift.{w} (Fin 2)) ℤ
  let x₀ : P := MvPolynomial.X (.up 0)
  let x₁ : P := MvPolynomial.X (.up 1)
  let p₀ : P := 1 + x₀ * x₁
  have hp₀ : p₀ ≠ 0 := by
    intro hzero
    have hcoeff := congrArg MvPolynomial.constantCoeff hzero
    simp [p₀, x₀, x₁] at hcoeff
  let q₀ : P := x₀ * x₁ * p₀
  have hq₀ : q₀ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _)) hp₀
  let R₀ := Localization.Away p₀
  let K := Localization.Away q₀
  have hPK_inj : Function.Injective (algebraMap P K) :=
    IsLocalization.injective K (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hq₀))
  have hsK_unit : IsUnit (algebraMap P K x₀) :=
    IsLocalization.Away.isUnit_of_dvd q₀ ⟨x₁ * p₀, by ring⟩
  have htK_unit : IsUnit (algebraMap P K x₁) :=
    IsLocalization.Away.isUnit_of_dvd q₀ ⟨x₀ * p₀, by ring⟩
  have hp₀K_unit : IsUnit (algebraMap P K p₀) :=
    IsLocalization.Away.isUnit_of_dvd q₀ ⟨x₀ * x₁, by ring⟩
  let B₀ : CommAlgCat.{w} ℤ := CommAlgCat.of ℤ R₀
  let B₁ : CommAlgCat.{w} ℤ := CommAlgCat.of ℤ K
  let sK : B₁ˣ := hsK_unit.unit
  let tK : B₁ˣ := htK_unit.unit
  let uK : B₁ˣ := hp₀K_unit.unit
  have hsK_val : (sK : B₁) = algebraMap P K x₀ := hsK_unit.unit_spec
  have htK_val : (tK : B₁) = algebraMap P K x₁ := htK_unit.unit_spec
  have huK_val : (uK : B₁) = algebraMap P K p₀ := hp₀K_unit.unit_spec
  have huK : (uK : B₁) = 1 + (sK : B₁) * (tK : B₁) := by
    rw [huK_val, hsK_val, htK_val]
    -- Expose the carrier `K` so `simp` expands `algebraMap P K p₀` through `map_add` and `map_mul`.
    change algebraMap P K p₀ = 1 + algebraMap P K x₀ * algebraMap P K x₁
    simp [p₀]
  let ι₀ : R₀ →+* K := IsLocalization.Away.lift p₀ hp₀K_unit
  have hι₀_inj : Function.Injective ι₀ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨n, q, hq⟩ := IsLocalization.Away.surj p₀ z
    have hqK : algebraMap P K q = 0 := by
      rw [← IsLocalization.Away.lift_eq (S := R₀) p₀ hp₀K_unit q, ← hq, map_mul, hz, zero_mul]
    rw [hPK_inj (hqK.trans (map_zero _).symm), map_zero] at hq
    have hinv : algebraMap P R₀ p₀ ^ n * IsLocalization.Away.invSelf (S := R₀) p₀ ^ n = 1 := by
      rw [← mul_pow, IsLocalization.Away.mul_invSelf (S := R₀) p₀, one_pow]
    calc
      z = z * (algebraMap P R₀ p₀ ^ n * IsLocalization.Away.invSelf (S := R₀) p₀ ^ n) := by
        rw [hinv, mul_one]
      _ = 0 := by rw [← mul_assoc, hq, zero_mul]
  let ι : B₀ ⟶ B₁ := CommAlgCat.ofHom
    { toRingHom := ι₀
      commutes' := fun z => by
        rw [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_ofClass, eq_intCast (algebraMap ℤ R₀), eq_intCast (algebraMap ℤ K),
          map_intCast] }
  let r₀ : B₀ := algebraMap P R₀ x₀
  let s₀ : B₀ := algebraMap P R₀ x₁
  let u₀ : B₀ˣ := (IsLocalization.Away.algebraMap_isUnit (S := R₀) p₀).unit
  have hu₀_val : (u₀ : B₀) = algebraMap P R₀ p₀ :=
    (IsLocalization.Away.algebraMap_isUnit (S := R₀) p₀).unit_spec
  have hι_r₀ : ι.hom r₀ = (sK : B₁) :=
    (IsLocalization.Away.lift_eq (S := R₀) p₀ hp₀K_unit x₀).trans hsK_val.symm
  have hι_s₀ : ι.hom s₀ = (tK : B₁) :=
    (IsLocalization.Away.lift_eq (S := R₀) p₀ hp₀K_unit x₁).trans htK_val.symm
  have hι_u₀ : Units.map ι.hom.toRingHom.toMonoidHom u₀ = uK := by
    apply Units.ext
    -- Compare the underlying elements in `K` so `IsLocalization.Away.lift_eq` rewrites directly.
    change ι₀ u₀ = uK
    rw [hu₀_val, IsLocalization.Away.lift_eq (S := R₀) p₀ hp₀K_unit p₀, ← huK_val]
  let evP : P →+* A :=
    MvPolynomial.eval₂Hom (algebraMap ℤ A) (fun k => if k.down = 0 then r else s)
  have hevP_x₀ : evP x₀ = r :=
    MvPolynomial.eval₂Hom_X' (algebraMap ℤ A)
      (fun k : ULift.{w} (Fin 2) => if k.down = 0 then r else s) ⟨0⟩
  have hevP_x₁ : evP x₁ = s :=
    MvPolynomial.eval₂Hom_X' (algebraMap ℤ A)
      (fun k : ULift.{w} (Fin 2) => if k.down = 0 then r else s) ⟨1⟩
  have hevP_p₀ : evP p₀ = (u : A) := by
    rw [hu]
    simp [p₀, hevP_x₀, hevP_x₁]
  have hp₀_unit : IsUnit (evP p₀) := hevP_p₀ ▸ u.isUnit
  let ψ₀ : R₀ →+* A := IsLocalization.Away.lift p₀ hp₀_unit
  let ψ : B₀ ⟶ A := CommAlgCat.ofHom
    { toRingHom := ψ₀
      commutes' := fun z => by
        rw [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
          MonoidHom.coe_ofClass, eq_intCast (algebraMap ℤ R₀), eq_intCast (algebraMap ℤ A),
          map_intCast] }
  have hψ_r₀ : ψ.hom r₀ = r := by
    -- Expose the underlying localization lift `ψ₀` on `r₀`.
    change ψ₀ (algebraMap P R₀ x₀) = r
    rw [IsLocalization.Away.lift_eq p₀ hp₀_unit x₀, hevP_x₀]
  have hψ_s₀ : ψ.hom s₀ = s := by
    -- Expose the underlying localization lift `ψ₀` on `s₀`.
    change ψ₀ (algebraMap P R₀ x₁) = s
    rw [IsLocalization.Away.lift_eq p₀ hp₀_unit x₁, hevP_x₁]
  have hψ_u₀ : Units.map ψ.hom.toRingHom.toMonoidHom u₀ = u := by
    apply Units.ext
    -- Compare the underlying elements in `A` via `ψ₀`.
    change ψ₀ u₀ = u
    rw [hu₀_val, IsLocalization.Away.lift_eq p₀ hp₀_unit p₀, hevP_p₀]
  exact kostantRootSubgroupParam_mul_kostantRootSubgroupParam_f_e_of_universal
    e h ρ M hM hi hj b wt hwt hT hα hαneg ι (fun _ _ hxy => hι₀_inj hxy) ψ r₀ s₀ u₀
    sK tK uK huK hι_r₀ hι_s₀ hι_u₀ r s u hψ_r₀ hψ_s₀ hψ_u₀

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
  have hneg : (u : A) = 1 + (-r) * (-s) := by simpa only [neg_mul_neg] using hu
  have hinv := congrArg Inv.inv
    (kostantRootSubgroupParam_mul_kostantRootSubgroupParam_f_e (c := c) (α := α)
      e h ρ M hM hi hj b wt hwt hT hα hαneg A (-r) (-s) u hneg)
  simpa only [mul_inv_rev, ← map_inv, ofAdd_neg, inv_inv, neg_mul, mul_assoc] using hinv

end Gauss

end TauCeti.UniversalEnvelopingAlgebra
