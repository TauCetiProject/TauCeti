/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Divisible
public import Mathlib.Topology.Algebra.Algebra.Equiv
public import TauCeti.RingTheory.LaurentSeries.Puiseux.Continuity
public import TauCeti.RingTheory.LaurentSeries.Substitution.Basic

import TauCeti.GroupTheory.Divisible.Basic
import TauCeti.RingTheory.LaurentSeries.Colimit
import TauCeti.RingTheory.LaurentSeries.LaurentPolynomial
import TauCeti.RingTheory.LaurentSeries.Puiseux.Root

/-!
# Substitution and formal-coordinate lifts on the Puiseux field

Let `K` be a field and `puiseuxField K` the field of Puiseux series over `K`, endowed with its
valuation topology (`Puiseux/Valuation.lean`) and homomorphism continuity criteria
(`Puiseux/Continuity.lean`).

This file studies lifts of Laurent-series substitutions `LaurentSeries.substAlgHom hφ hφ₀` and
formal-coordinate automorphisms `LaurentSeries.substAlgEquiv φ` from `K⸨X⸩` to `puiseuxField K`:

* **Automatic continuity and valuation scaling**: every ring endomorphism intertwining any pair of
  ramified levels `n` and `m` via a Laurent-series substitution `LaurentSeries.substAlgHom hφ hφ₀`
  is automatically continuous (`continuous_of_apply_levelEmbedding_substAlgHom`). For level-one
  lifts, every ring endomorphism extending `LaurentSeries.substAlgHom hφ hφ₀` on `K⸨X⸩` is
  automatically continuous (`continuous_of_apply_algebraMap_substAlgHom`), multiplies rational
  orders (`order_of_apply_algebraMap_substAlgHom`) and `addVal K`
  (`addVal_of_apply_algebraMap_substAlgHom`) by `φ.order.toNat`, and raises `valuation K` to the
  `φ.order.toNat`-th power (`valuation_of_apply_algebraMap_substAlgHom`). Every ring endomorphism
  extending `LaurentSeries.substAlgEquiv φ` on `K⸨X⸩` preserves rational orders, `addVal K`, and
  valuations (`order_of_apply_algebraMap_substAlgEquiv`, `addVal_of_apply_algebraMap_substAlgEquiv`,
  `valuation_of_apply_algebraMap_substAlgEquiv`), and every ring automorphism extending it is
  automatically a homeomorphism (`isHomeomorph_of_apply_algebraMap_substAlgEquiv`).
* **Automatic level compatibility**: every `K`-algebra lift `ρ` of `LaurentSeries.substAlgHom`
  preserves each ramified level `n` via a Laurent substitution `ψ` satisfying `ψ ^ n = φ.expand n`
  (`exists_substAlgHom_apply_levelEmbedding`).
* **Existence of lifts**: whenever `Kˣ` is `ℕ`-rootable (for instance when `K` is algebraically
  closed, in any characteristic), `(puiseuxField K)ˣ` is `ℕ`-rootable (`Puiseux/Root.lean`);
  choosing a compatible family of `n`-th roots of `φ` and descending along the colimit presentation
  `levelCoconeIsColimit` constructs continuous `K`-algebra endomorphisms lifting arbitrary nonzero
  substitutions `X ↦ φ` with `constantCoeff φ = 0`, and bicontinuous `K`-algebra automorphisms
  lifting arbitrary formal coordinates `φ : FormalCoordinate K`.

## Main definitions

* `TauCeti.puiseuxField.continuousAlgHomOfSubstAlgHom`: bundles any `K`-algebra lift of
  `LaurentSeries.substAlgHom` as a continuous `K`-algebra endomorphism of `puiseuxField K`.
* `TauCeti.puiseuxField.continuousAlgEquivOfSubstAlgEquiv`: bundles any `K`-algebra automorphism
  lifting `LaurentSeries.substAlgEquiv` as a bicontinuous `K`-algebra automorphism.

## Main results

* `TauCeti.puiseuxField.continuous_of_apply_levelEmbedding_substAlgHom`,
  `TauCeti.puiseuxField.continuous_of_apply_algebraMap_substAlgHom`,
  `TauCeti.puiseuxField.isHomeomorph_of_apply_algebraMap_substAlgEquiv`: automatic continuity and
  bicontinuity of substitution and formal-coordinate lifts.
* `TauCeti.puiseuxField.exists_substAlgHom_apply_levelEmbedding`: every `K`-algebra lift of
  `LaurentSeries.substAlgHom` preserves each ramified level via a Laurent substitution.
* `TauCeti.puiseuxField.order_of_apply_algebraMap_substAlgHom`,
  `TauCeti.puiseuxField.valuation_of_apply_algebraMap_substAlgHom`,
  `TauCeti.puiseuxField.addVal_of_apply_algebraMap_substAlgHom`,
  `TauCeti.puiseuxField.order_of_apply_algebraMap_substAlgEquiv`,
  `TauCeti.puiseuxField.valuation_of_apply_algebraMap_substAlgEquiv`,
  `TauCeti.puiseuxField.addVal_of_apply_algebraMap_substAlgEquiv`: order and valuation formulas for
  substitution and formal-coordinate lifts.
* `TauCeti.puiseuxField.exists_continuousAlgHom_apply_algebraMap_substAlgHom`,
  `TauCeti.puiseuxField.exists_continuousAlgEquiv_apply_algebraMap_substAlgEquiv`: existence of
  continuous substitution endomorphisms and bicontinuous coordinate automorphisms when
  `[RootableBy Kˣ ℕ]`, in arbitrary characteristic.
-/

public section

open Filter HahnSeries LaurentSeries Topology WithZero
open scoped LaurentSeries PowerSeries

namespace TauCeti.puiseuxField

variable {K : Type*} [Field K]

private theorem coe_ne_zero {x : puiseuxField K} (hx : x ≠ 0) :
    (x : HahnSeries ℚ K) ≠ 0 :=
  ZeroMemClass.coe_eq_zero.not.mpr hx

/-! ### Automatic continuity and level compatibility of substitution and coordinate lifts -/

section SubstLift

/-- If `y ^ n` is the level-one image of a nonzero power series `φ` with `constantCoeff φ = 0`,
then `y` is the level-`n` image of a nonzero power series `ψ` with `constantCoeff ψ = 0` and
`ψ ^ n = φ.expand n`. -/
private theorem exists_powerSeries_levelEmbedding_eq_of_pow_eq {φ : K⟦X⟧}
    (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0) (n : ℕ+) {y : puiseuxField K}
    (hy : y ^ (n : ℕ) = algebraMap K⸨X⸩ (puiseuxField K) (φ : K⸨X⸩)) :
    ∃ (ψ : K⟦X⟧) (_ : PowerSeries.constantCoeff ψ = 0) (_ : ψ ≠ 0),
      ψ ^ (n : ℕ) = φ.expand n n.ne_zero ∧ levelEmbedding K n (ψ : K⸨X⸩) = y := by
  obtain ⟨g, hg⟩ := (AlgHom.mem_range _).mp (mem_range_levelEmbedding_of_pow_eq_algebraMap hy)
  have hinj : Function.Injective (levelEmbedding K n) := (levelEmbedding K n).toRingHom.injective
  have hg_pow : g ^ (n : ℕ) = ((φ.expand n n.ne_zero : K⟦X⟧) : K⸨X⸩) :=
    hinj (by rw [map_pow, hg, hy, ← levelEmbedding_expand_self n, expand_coe])
  have hexp₀ : φ.expand n n.ne_zero ≠ 0 := fun h ↦
    hφ₀ (PowerSeries.ext fun k ↦ by
      simpa [PowerSeries.coeff_expand_mul] using congrArg (PowerSeries.coeff (n * k)) h)
  have hg0 : g ≠ 0 := fun h ↦ hexp₀ (ofPowerSeries_injective (Γ := ℤ) (R := K) (by
    rw [← hg_pow, h, zero_pow n.ne_zero, map_zero]))
  have hg_ordTop : (1 : WithTop ℤ) ≤ g.orderTop := by
    have hmul_ord : (g ^ (n : ℕ)).order = (n : ℤ) * g.order :=
      (HahnSeries.order_pow g n).trans (nsmul_eq_mul _ _)
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (PowerSeries.order_eq_top.not.mpr hφ₀)
    have hm_pos : 1 ≤ m := by
      have hm_ne : m ≠ 0 := by
        have := PowerSeries.toNat_order_ne_zero hφ hφ₀
        rwa [← hm, ENat.toNat_natCast] at this
      omega
    have hexp_ord : (φ.expand n n.ne_zero).order.toNat = (n : ℕ) * m := by
      rw [PowerSeries.order_expand, ← hm, nsmul_eq_mul, ← Nat.cast_mul, ENat.toNat_natCast]
    have hgn : (n : ℤ) ≤ (g ^ (n : ℕ)).order := by
      rw [hg_pow, PowerSeries.order_coe, hexp_ord, Nat.cast_mul]
      have : 1 ≤ (m : ℤ) := by exact_mod_cast hm_pos
      nlinarith
    rw [← order_eq_orderTop_of_ne_zero hg0, ← WithTop.coe_one, WithTop.coe_le_coe]
    rw [hmul_ord] at hgn
    have : (0 : ℤ) < n := by exact_mod_cast n.pos
    nlinarith
  obtain ⟨ψ, rfl⟩ : g ∈ Set.range (ofPowerSeries ℤ K) :=
    TauCeti.LaurentSeries.mem_range_ofPowerSeries_iff.mpr fun k hk ↦
      coeff_eq_zero_of_lt_orderTop ((WithTop.coe_lt_coe.mpr (by omega)).trans_le hg_ordTop)
  have hψ_pow : ψ ^ (n : ℕ) = φ.expand n n.ne_zero :=
    ofPowerSeries_injective (by rwa [PowerSeries.coe_pow])
  have hψ₀ : ψ ≠ 0 := fun h ↦ hg0 (by simp [h])
  have hψ : PowerSeries.constantCoeff ψ = 0 := by
    have h0 : ((ψ : K⸨X⸩)).coeff 0 = 0 :=
      coeff_eq_zero_of_lt_orderTop ((WithTop.coe_lt_coe.mpr zero_lt_one).trans_le hg_ordTop)
    simpa [PowerSeries.coeff_coe] using h0
  exact ⟨ψ, hψ, hψ₀, hψ_pow, hg⟩

/-- Any ring endomorphism of `puiseuxField K` that intertwines a ramified level `n` with a
Laurent-series substitution into level `m` is automatically continuous on the entire Puiseux
field. -/
theorem continuous_of_apply_levelEmbedding_substAlgHom {ρ : puiseuxField K →+* puiseuxField K}
    (n m : ℕ+) {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (levelEmbedding K n f) =
      levelEmbedding K m (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    Continuous ρ := by
  rw [continuous_ringHom_iff_continuous_comp_algebraMap]
  have hcomp : (fun f : K⸨X⸩ ↦ ρ (algebraMap K⸨X⸩ (puiseuxField K) f)) =
      fun f ↦ levelEmbedding K m
        (LaurentSeries.substAlgHom hφ hφ₀ (_root_.LaurentSeries.expand K n f)) := by
    funext f
    rw [← levelEmbedding_expand_self n f, hρ]
  rw [hcomp]
  exact (continuous_levelEmbedding m).comp
    ((LaurentSeries.continuous_substAlgHom hφ hφ₀).comp (_root_.LaurentSeries.continuous_expand n))

/-- Any ring endomorphism of `puiseuxField K` extending `LaurentSeries.substAlgHom hφ hφ₀` on
`K⸨X⸩` is automatically continuous on `puiseuxField K`. -/
theorem continuous_of_apply_algebraMap_substAlgHom {ρ : puiseuxField K →+* puiseuxField K}
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    Continuous ρ :=
  continuous_of_apply_levelEmbedding_substAlgHom 1 1 hφ hφ₀
    (by simpa only [← algebraMap_laurentSeries_apply] using hρ)

/-- Any ring automorphism of `puiseuxField K` extending `LaurentSeries.substAlgEquiv φ` on `K⸨X⸩`
is automatically a homeomorphism of `puiseuxField K`. -/
theorem isHomeomorph_of_apply_algebraMap_substAlgEquiv {ρ : puiseuxField K ≃+* puiseuxField K}
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    IsHomeomorph ρ :=
  (isHomeomorph_ringEquiv_iff ρ).mpr
    (continuous_of_apply_algebraMap_substAlgHom (ρ := ρ.toRingHom)
      φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero
      (by simpa only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        LaurentSeries.coe_substAlgEquiv] using hρ))

/-- **Automatic level compatibility**: every `K`-algebra endomorphism `ρ` of `puiseuxField K`
extending `LaurentSeries.substAlgHom hφ hφ₀` preserves each ramified level `n` via a Laurent
substitution `ψ` satisfying `ψ ^ n = φ.expand n`. -/
theorem exists_substAlgHom_apply_levelEmbedding {ρ : puiseuxField K →ₐ[K] puiseuxField K}
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (n : ℕ+) :
    ∃ (ψ : K⟦X⟧) (hψ : PowerSeries.constantCoeff ψ = 0) (hψ₀ : ψ ≠ 0),
      ψ ^ (n : ℕ) = φ.expand n n.ne_zero ∧
        ∀ f, ρ (levelEmbedding K n f) =
          levelEmbedding K n (LaurentSeries.substAlgHom hψ hψ₀ f) := by
  set y : puiseuxField K := ρ (levelEmbedding K n (HahnSeries.single 1 1))
  have hy_pow : y ^ (n : ℕ) = algebraMap K⸨X⸩ (puiseuxField K) (φ : K⸨X⸩) := by
    rw [← map_pow, ← map_pow (levelEmbedding K n), HahnSeries.single_pow, one_pow, nsmul_eq_mul,
      mul_one, levelEmbedding_single_self, ← algebraMap_laurentSeries_single_one, hρ,
      LaurentSeries.substAlgHom_single_one]
  obtain ⟨ψ, hψ, hψ₀, hψ_pow, hg⟩ :=
    exists_powerSeries_levelEmbedding_eq_of_pow_eq hφ hφ₀ n hy_pow
  refine ⟨ψ, hψ, hψ₀, hψ_pow, fun f ↦ ?_⟩
  have h_eq := TauCeti.LaurentSeries.algHom_eq_of_continuous_of_single_one_eq
    (φ₁ := ρ.comp (levelEmbedding K n))
    (φ₂ := (levelEmbedding K n).comp (LaurentSeries.substAlgHom hψ hψ₀))
    ((continuous_of_apply_algebraMap_substAlgHom (ρ := ρ.toRingHom) hφ hφ₀ hρ).comp
      (continuous_levelEmbedding n))
    ((continuous_levelEmbedding n).comp (LaurentSeries.continuous_substAlgHom hψ hψ₀))
    (by simp [y, hg])
  exact AlgHom.congr_fun h_eq f

/-- Bundles any `K`-algebra endomorphism `ρ` of `puiseuxField K` extending
`LaurentSeries.substAlgHom hφ hφ₀` as a continuous `K`-algebra endomorphism. -/
noncomputable def continuousAlgHomOfSubstAlgHom (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    puiseuxField K →A[K] puiseuxField K where
  toAlgHom := ρ
  cont := continuous_of_apply_algebraMap_substAlgHom hφ hφ₀ hρ

/-- Evaluation of `continuousAlgHomOfSubstAlgHom` is the underlying algebra endomorphism. -/
@[simp]
theorem continuousAlgHomOfSubstAlgHom_apply (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    continuousAlgHomOfSubstAlgHom ρ hφ hφ₀ hρ x = ρ x :=
  (rfl)

/-- Forgetting continuity of `continuousAlgHomOfSubstAlgHom` recovers `ρ`. -/
@[simp]
theorem toAlgHom_continuousAlgHomOfSubstAlgHom (ρ : puiseuxField K →ₐ[K] puiseuxField K)
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    (continuousAlgHomOfSubstAlgHom ρ hφ hφ₀ hρ).toAlgHom = ρ :=
  (rfl)

/-- Re-bundling an already continuous substitution endomorphism recovers it. -/
@[simp]
theorem continuousAlgHomOfSubstAlgHom_toAlgHom (ρ : puiseuxField K →A[K] puiseuxField K)
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    continuousAlgHomOfSubstAlgHom ρ.toAlgHom hφ hφ₀ hρ = ρ :=
  DFunLike.ext _ _ fun _ ↦ rfl

/-- Under any lift `ρ` of `LaurentSeries.substAlgHom hφ hφ₀`, the image of `t` has rational order
`φ.order.toNat`. -/
theorem order_single_one_of_apply_algebraMap_substAlgHom {ρ : puiseuxField K →+* puiseuxField K}
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f)) :
    (ρ (single K 1 1) : HahnSeries ℚ K).order = φ.order.toNat := by
  rw [← algebraMap_laurentSeries_single_one, hρ, LaurentSeries.substAlgHom_single_one,
    coe_algebraMap_laurentSeries, order_ramifiedEmbedding, PowerSeries.order_coe, PNat.one_coe,
    Nat.cast_one, div_one, Int.cast_natCast]

/-- Any lift `ρ` of `LaurentSeries.substAlgHom hφ hφ₀` multiplies the rational order of every
Puiseux series by `φ.order.toNat`. -/
theorem order_of_apply_algebraMap_substAlgHom {ρ : puiseuxField K →+* puiseuxField K}
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    (ρ x : HahnSeries ℚ K).order = φ.order.toNat * (x : HahnSeries ℚ K).order := by
  have hpow := ((continuous_ringHom_iff ρ).mp
    (continuous_of_apply_algebraMap_substAlgHom hφ hφ₀ hρ)).1
  rw [order_map_eq_mul_of_forall_addVal_nonneg ρ hpow x,
    order_single_one_of_apply_algebraMap_substAlgHom hφ hφ₀ hρ, mul_comm]

/-- Any lift `ρ` of `LaurentSeries.substAlgHom hφ hφ₀` raises the Puiseux valuation to the power
`φ.order.toNat`. -/
theorem valuation_of_apply_algebraMap_substAlgHom {ρ : puiseuxField K →+* puiseuxField K}
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    valuation K (ρ x) = valuation K x ^ φ.order.toNat := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [map_zero, map_zero, zero_pow (PowerSeries.toNat_order_ne_zero hφ hφ₀)]
  have hρx := coe_ne_zero ((map_ne_zero_iff ρ ρ.injective).mpr hx0)
  rw [valuation_apply, valuation_apply, valuation_eq_exp_neg_order hρx,
    valuation_eq_exp_neg_order (coe_ne_zero hx0), ← exp_nsmul,
    order_of_apply_algebraMap_substAlgHom hφ hφ₀ hρ x, nsmul_eq_mul, mul_neg]

/-- Any lift `ρ` of `LaurentSeries.substAlgHom hφ hφ₀` multiplies the `WithTop ℚ`-valued order
`addVal K` by `φ.order.toNat`. -/
theorem addVal_of_apply_algebraMap_substAlgHom {ρ : puiseuxField K →+* puiseuxField K}
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f))
    (x : puiseuxField K) :
    addVal K (ρ x) = φ.order.toNat • addVal K x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (PowerSeries.toNat_order_ne_zero hφ hφ₀)
    simp [hk, succ_nsmul]
  have hρx := coe_ne_zero ((map_ne_zero_iff ρ ρ.injective).mpr hx0)
  rw [addVal_apply, addVal_apply, ← order_eq_orderTop_of_ne_zero hρx,
    ← order_eq_orderTop_of_ne_zero (coe_ne_zero hx0),
    order_of_apply_algebraMap_substAlgHom hφ hφ₀ hρ x, ← WithTop.coe_nsmul, nsmul_eq_mul]

/-- Bundles any `K`-algebra automorphism `ρ` of `puiseuxField K` extending
`LaurentSeries.substAlgEquiv φ` as a bicontinuous `K`-algebra automorphism. -/
noncomputable def continuousAlgEquivOfSubstAlgEquiv (ρ : puiseuxField K ≃ₐ[K] puiseuxField K)
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    puiseuxField K ≃A[K] puiseuxField K where
  toAlgEquiv := ρ
  continuous_toFun :=
    ((ρ.toRingEquiv.toEquiv.isHomeomorph_iff).mp
      (isHomeomorph_of_apply_algebraMap_substAlgEquiv (ρ := ρ.toRingEquiv) φ hρ)).1
  continuous_invFun :=
    ((ρ.toRingEquiv.toEquiv.isHomeomorph_iff).mp
      (isHomeomorph_of_apply_algebraMap_substAlgEquiv (ρ := ρ.toRingEquiv) φ hρ)).2

/-- Evaluation of `continuousAlgEquivOfSubstAlgEquiv` is the underlying algebra automorphism. -/
@[simp]
theorem continuousAlgEquivOfSubstAlgEquiv_apply (ρ : puiseuxField K ≃ₐ[K] puiseuxField K)
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    continuousAlgEquivOfSubstAlgEquiv ρ φ hρ x = ρ x :=
  (rfl)

/-- Inverse evaluation of `continuousAlgEquivOfSubstAlgEquiv` is `ρ.symm`. -/
@[simp]
theorem continuousAlgEquivOfSubstAlgEquiv_symm_apply (ρ : puiseuxField K ≃ₐ[K] puiseuxField K)
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    (continuousAlgEquivOfSubstAlgEquiv ρ φ hρ).symm x = ρ.symm x :=
  (rfl)

/-- Forgetting bicontinuity of `continuousAlgEquivOfSubstAlgEquiv` recovers `ρ`. -/
@[simp]
theorem toAlgEquiv_continuousAlgEquivOfSubstAlgEquiv (ρ : puiseuxField K ≃ₐ[K] puiseuxField K)
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    (continuousAlgEquivOfSubstAlgEquiv ρ φ hρ).toAlgEquiv = ρ :=
  (rfl)

/-- Re-bundling an already bicontinuous formal-coordinate automorphism recovers it. -/
@[simp]
theorem continuousAlgEquivOfSubstAlgEquiv_toAlgEquiv (ρ : puiseuxField K ≃A[K] puiseuxField K)
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    continuousAlgEquivOfSubstAlgEquiv ρ.toAlgEquiv φ hρ = ρ :=
  DFunLike.ext _ _ fun _ ↦ rfl

/-- Viewing `continuousAlgEquivOfSubstAlgEquiv` as a continuous algebra endomorphism agrees with
`continuousAlgHomOfSubstAlgHom`. -/
@[simp]
theorem toContinuousAlgHom_continuousAlgEquivOfSubstAlgEquiv
    (ρ : puiseuxField K ≃ₐ[K] puiseuxField K) (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f)) :
    (continuousAlgEquivOfSubstAlgEquiv ρ φ hρ).toContinuousAlgHom =
      continuousAlgHomOfSubstAlgHom ρ.toAlgHom φ.constantCoeff_toPowerSeries
        φ.toPowerSeries_ne_zero
        (by simpa only [AlgEquiv.coe_toAlgHom, LaurentSeries.coe_substAlgEquiv] using hρ) :=
  DFunLike.ext _ _ fun _ ↦ rfl

/-- Any lift of a formal-coordinate substitution preserves rational orders on `puiseuxField K`. -/
theorem order_of_apply_algebraMap_substAlgEquiv {ρ : puiseuxField K →+* puiseuxField K}
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    (ρ x : HahnSeries ℚ K).order = (x : HahnSeries ℚ K).order := by
  simpa [φ.order_toPowerSeries] using
    order_of_apply_algebraMap_substAlgHom φ.constantCoeff_toPowerSeries
      φ.toPowerSeries_ne_zero (by simpa only [LaurentSeries.coe_substAlgEquiv] using hρ) x

/-- Any lift of a formal-coordinate substitution preserves the valuation of `puiseuxField K`. -/
theorem valuation_of_apply_algebraMap_substAlgEquiv {ρ : puiseuxField K →+* puiseuxField K}
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    valuation K (ρ x) = valuation K x := by
  simpa [φ.order_toPowerSeries] using
    valuation_of_apply_algebraMap_substAlgHom φ.constantCoeff_toPowerSeries
      φ.toPowerSeries_ne_zero (by simpa only [LaurentSeries.coe_substAlgEquiv] using hρ) x

/-- Any lift of a formal-coordinate substitution preserves the `WithTop ℚ`-valued order
`addVal K`. -/
theorem addVal_of_apply_algebraMap_substAlgEquiv {ρ : puiseuxField K →+* puiseuxField K}
    (φ : FormalCoordinate K)
    (hρ : ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f))
    (x : puiseuxField K) :
    addVal K (ρ x) = addVal K x := by
  simpa [φ.order_toPowerSeries] using
    addVal_of_apply_algebraMap_substAlgHom φ.constantCoeff_toPowerSeries
      φ.toPowerSeries_ne_zero (by simpa only [LaurentSeries.coe_substAlgEquiv] using hρ) x

end SubstLift

/-! ### Existence of continuous substitution and coordinate lifts -/

section Existence

/-- Assembles a compatible family of level-`n` substitution maps into a cocone over
`levelDiagram K`. -/
private noncomputable def substCocone (leg : ℕ+ → (K⸨X⸩ →ₐ[K] puiseuxField K))
    (hleg_compat : ∀ {n m : ℕ+}, n ∣ m →
      (leg m).comp (_root_.LaurentSeries.expand K (m.divExact n)) = leg n) :
    CategoryTheory.Limits.Cocone (levelDiagram K) where
  pt := CommAlgCat.of K (puiseuxField K)
  ι :=
    { app := fun n ↦ CommAlgCat.ofHom (leg n.toPNat)
      naturality := fun {_ _} f ↦ by
        apply CommAlgCat.hom_ext
        dsimp only [levelDiagram, CategoryTheory.Functor.const_obj_obj]
        simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom,
          CategoryTheory.Functor.const_obj_map, CommAlgCat.hom_id, AlgHom.id_comp]
        rw [RamificationIndex.transitionDegree_def]
        exact hleg_compat f.le }

/-- **Existence of continuous substitution endomorphisms**: over a field `K` with
`[RootableBy Kˣ ℕ]` (in arbitrary characteristic), every nonzero power series `φ` with
`constantCoeff φ = 0` lifts to a continuous `K`-algebra endomorphism of `puiseuxField K` extending
`LaurentSeries.substAlgHom`. -/
theorem exists_continuousAlgHom_apply_algebraMap_substAlgHom [RootableBy Kˣ ℕ]
    {φ : K⟦X⟧} (hφ : PowerSeries.constantCoeff φ = 0) (hφ₀ : φ ≠ 0) :
    ∃ ρ : puiseuxField K →A[K] puiseuxField K,
      ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
        algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f) := by
  obtain ⟨y, hy1, hy_pow⟩ :=
    TauCeti.exists_apply_one_eq_and_forall_pow_eq_of_rootableBy_units
      (algebraMap K⸨X⸩ (puiseuxField K) (φ : K⸨X⸩))
  have hy_self : ∀ n : ℕ+, y n ^ (n : ℕ) = algebraMap K⸨X⸩ (puiseuxField K) (φ : K⸨X⸩) := fun n ↦ by
    simpa [hy1] using hy_pow 1 n
  choose ψ hψ hψ₀ _ hψ_eq using fun n ↦
    exists_powerSeries_levelEmbedding_eq_of_pow_eq hφ hφ₀ n (hy_self n)
  let leg : ℕ+ → (K⸨X⸩ →ₐ[K] puiseuxField K) := fun n ↦
    (levelEmbedding K n).comp (LaurentSeries.substAlgHom (hψ n) (hψ₀ n))
  have hleg_compat : ∀ {n m : ℕ+}, n ∣ m →
      (leg m).comp (_root_.LaurentSeries.expand K (m.divExact n)) = leg n := by
    intro n m h
    refine TauCeti.LaurentSeries.algHom_eq_of_continuous_of_single_one_eq
      ((continuous_levelEmbedding m).comp
        ((LaurentSeries.continuous_substAlgHom (hψ m) (hψ₀ m)).comp
          (_root_.LaurentSeries.continuous_expand (m.divExact n))))
      ((continuous_levelEmbedding n).comp (LaurentSeries.continuous_substAlgHom (hψ n) (hψ₀ n))) ?_
    simp only [leg, AlgHom.comp_apply, expand_single, mul_one,
      LaurentSeries.substAlgHom_single_one]
    rw [RatFunc.single_zpow, zpow_natCast, map_pow, map_pow,
      LaurentSeries.substAlgHom_single_one, hψ_eq m, hψ_eq n]
    have hpow := hy_pow n (m.divExact n)
    rwa [PNat.mul_div_exact h] at hpow
  let s := substCocone leg hleg_compat
  let ρ₀ : puiseuxField K →ₐ[K] puiseuxField K := (levelCoconeIsColimit.desc s).hom
  have hψ1 : ψ 1 = φ :=
    ofPowerSeries_injective ((levelEmbedding K 1).toRingHom.injective
      ((hψ_eq 1).trans (hy1.trans (algebraMap_laurentSeries_apply (φ : K⸨X⸩)))))
  have hρ₀ : ∀ f, ρ₀ (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgHom hφ hφ₀ f) := by
    intro f
    have hfac : ρ₀ (levelEmbedding K 1 f) = leg 1 f :=
      CategoryTheory.ConcreteCategory.congr_hom (levelCoconeIsColimit.fac s ⟨1⟩) f
    rw [algebraMap_laurentSeries_apply, hfac]
    simp only [leg, AlgHom.comp_apply, algebraMap_laurentSeries_apply]
    have hsubst : LaurentSeries.substAlgHom (hψ 1) (hψ₀ 1) = LaurentSeries.substAlgHom hφ hφ₀ := by
      subst hψ1
      rfl
    rw [hsubst]
  exact ⟨continuousAlgHomOfSubstAlgHom ρ₀ hφ hφ₀ hρ₀, hρ₀⟩

/-- **Existence of bicontinuous coordinate automorphisms**: over a field `K` with
`[RootableBy Kˣ ℕ]` (in arbitrary characteristic), every formal coordinate `φ` lifts to a
bicontinuous `K`-algebra automorphism of `puiseuxField K` extending
`LaurentSeries.substAlgEquiv φ`. -/
theorem exists_continuousAlgEquiv_apply_algebraMap_substAlgEquiv [RootableBy Kˣ ℕ]
    (φ : FormalCoordinate K) :
    ∃ ρ : puiseuxField K ≃A[K] puiseuxField K,
      ∀ f, ρ (algebraMap K⸨X⸩ (puiseuxField K) f) =
        algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f) := by
  obtain ⟨ρ₀, hρ₀⟩ := exists_continuousAlgHom_apply_algebraMap_substAlgHom
    φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero
  have hsurj : Function.Surjective ρ₀ := by
    intro z
    obtain ⟨n, hn⟩ := exists_mem_range_levelEmbedding z
    obtain ⟨h, rfl⟩ := (AlgHom.mem_range _).mp hn
    obtain ⟨ψ, hψ, hψ₀, hψ_pow, hψ_level⟩ := exists_substAlgHom_apply_levelEmbedding
      (ρ := ρ₀.toAlgHom) φ.constantCoeff_toPowerSeries φ.toPowerSeries_ne_zero hρ₀ n
    simp only [ContinuousAlgHom.coe_coe] at hψ_level
    have hψ_ord : ψ.order = 1 := by
      have hmul : (n : ℕ) • ψ.order = (n : ℕ) • (1 : ℕ∞) := by
        rw [← PowerSeries.order_pow, hψ_pow, PowerSeries.order_expand, φ.order_toPowerSeries]
      obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp (PowerSeries.order_eq_top.not.mpr hψ₀)
      rw [← hk, nsmul_eq_mul, nsmul_eq_mul, mul_one, ← Nat.cast_mul, Nat.cast_inj] at hmul
      have hk1 : k = 1 := by
        have := n.pos
        nlinarith
      rw [← hk, hk1, Nat.cast_one]
    let ψc : FormalCoordinate K :=
      ⟨ψ, hψ, ((PowerSeries.order_eq_nat.mp hψ_ord).1).isUnit⟩
    refine ⟨levelEmbedding K n ((LaurentSeries.substAlgEquiv ψc).symm h), ?_⟩
    have hcoe : LaurentSeries.substAlgHom hψ hψ₀ ((LaurentSeries.substAlgEquiv ψc).symm h) =
        LaurentSeries.substAlgEquiv ψc ((LaurentSeries.substAlgEquiv ψc).symm h) :=
      (congrFun (LaurentSeries.coe_substAlgEquiv ψc) _).symm
    rw [hψ_level, hcoe, AlgEquiv.apply_symm_apply]
  let e : puiseuxField K ≃ₐ[K] puiseuxField K :=
    AlgEquiv.ofBijective ρ₀.toAlgHom ⟨ρ₀.toAlgHom.injective, hsurj⟩
  have he : ∀ f, e (algebraMap K⸨X⸩ (puiseuxField K) f) =
      algebraMap K⸨X⸩ (puiseuxField K) (LaurentSeries.substAlgEquiv φ f) := fun f ↦ by
    rw [LaurentSeries.coe_substAlgEquiv]
    exact hρ₀ f
  exact ⟨continuousAlgEquivOfSubstAlgEquiv e φ he, he⟩

end Existence

end TauCeti.puiseuxField
