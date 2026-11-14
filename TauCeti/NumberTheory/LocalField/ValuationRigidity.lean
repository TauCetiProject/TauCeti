/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Henselian
public import TauCeti.NumberTheory.LocalField.Uniformizer
public import TauCeti.RingTheory.Henselian.Valuation
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# Rigidity of discrete valuations and automatic continuity on nonarchimedean local fields

The valuation ring `𝒪[K]` of a nonarchimedean local field `K` is a Henselian discrete valuation ring
(`TauCeti.henselianLocalRing_integer`) with finite residue field `𝓀[K]`. Importing this file makes
the algebraic rigidity results of `TauCeti.RingTheory.Henselian.Valuation` — including
`Valuation.isEquiv_of_henselianLocalRing`, `Valuation.compatible_of_henselianLocalRing`,
`RingHom.isEquiv_comap_valuation_of_finite_residueField`,
`RingHom.map_vle_map_iff_of_finite_residueField`, and `ValuativeExtension.of_finite_residueField` —
apply directly to nonarchimedean local fields with all Henselian and residue-finiteness instances
supplied automatically.

This file adds the consequences specific to the normalized valuation and topology of a
nonarchimedean local field:

* Every `ℤᵐ⁰`-valued valuation `v` on `K` (trivial or nontrivial) is determined on `Kˣ` by its
  single value at a uniformizer `ϖ`: `v(x) = v(ϖ) ^ v_K(x)`
  (`Valuation.apply_eq_zpow_toAdd_normalizedValuation`). Consequently, `(normalizedValuationWithZero
  K ·)⁻¹` is the unique surjective `ℤᵐ⁰`-valued valuation on `K`, with no compatibility assumption
  (`Valuation.eq_inv_normalizedValuationWithZero_of_surjective`).
* Every ring homomorphism `f : K →+* L` between nonarchimedean local fields is automatically a
  closed topological embedding (`RingHom.isClosedEmbedding_of_isNonarchimedeanLocalField`), hence
  continuous (`RingHom.continuous_of_isNonarchimedeanLocalField`). Every ring isomorphism
  `K ≃+* L` is therefore a homeomorphism (`RingEquiv.homeomorphOfIsNonarchimedeanLocalField`).

## Main definitions

* `RingEquiv.homeomorphOfIsNonarchimedeanLocalField`: a ring isomorphism between nonarchimedean
  local fields upgraded to a homeomorphism.

## Main results

* `Valuation.apply_eq_zpow_toAdd_normalizedValuation`: `v(x) = v(ϖ) ^ v_K(x)` for every
  `v : Valuation K ℤᵐ⁰`, uniformizer `ϖ`, and `x ∈ Kˣ`.
* `Valuation.eq_inv_normalizedValuationWithZero_of_surjective`: every surjective `ℤᵐ⁰`-valued
  valuation on `K` equals `(normalizedValuationWithZero K ·)⁻¹`.
* `RingHom.isClosedEmbedding_of_isNonarchimedeanLocalField` and
  `RingHom.continuous_of_isNonarchimedeanLocalField`: every ring homomorphism between
  nonarchimedean local fields is a closed embedding, hence continuous.

## References

* F. K. Schmidt, *Mehrfach perfekte Körper*, Mathematische Annalen **108** (1933), 1–25.
* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter II, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §§3–4.
-/

public section

open scoped WithZero

open ValuativeRel

section SingleLocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

namespace Valuation

/-- **Uniformizer power formula for `ℤᵐ⁰`-valued valuations on a nonarchimedean local field**:
every `v : Valuation K ℤᵐ⁰` (trivial or nontrivial) satisfies `v(x) = v(ϖ) ^ v_K(x)` for every
uniformizer `ϖ` and every `x ∈ Kˣ`. -/
theorem apply_eq_zpow_toAdd_normalizedValuation (v : _root_.Valuation K ℤᵐ⁰) {ϖ : Kˣ}
    (hϖ : TauCeti.IsUniformizer K ϖ) (x : Kˣ) :
    v (x : K) = v (ϖ : K) ^ (TauCeti.normalizedValuation K x).toAdd := by
  set n := (TauCeti.normalizedValuation K x).toAdd
  set u : Kˣ := x * ϖ ^ (-n)
  have hu1 : valuation K (u : K) = 1 := by
    rw [← TauCeti.normalizedValuation_eq_one_iff, ← toAdd_eq_zero]
    simp [u, n, (TauCeti.isUniformizer_def ϖ).mp hϖ]
  have hvu : v (u : K) = 1 := v.eq_one_of_eq_one_of_henselianLocalRing (valuation K) hu1
  have hx : x = u * ϖ ^ n := by simp [u]
  have hx_coe : (x : K) = (u : K) * (ϖ : K) ^ n := by
    rw [hx, Units.val_mul, Units.val_zpow_eq_zpow_val]
  rw [hx_coe, map_mul, hvu, one_mul, map_zpow₀]

/-- **Characterization of the normalized valuation without compatibility**: every surjective
`ℤᵐ⁰`-valued valuation on a nonarchimedean local field `K` is the point-wise inverse of
`normalizedValuationWithZero K`. This strengthens
`Valuation.normalizedValuationWithZero_eq_inv_of_surjective` by removing `[v.Compatible]`. -/
theorem eq_inv_normalizedValuationWithZero_of_surjective (v : _root_.Valuation K ℤᵐ⁰)
    (hv : Function.Surjective v) (x : K) :
    v x = (TauCeti.normalizedValuationWithZero K x)⁻¹ := by
  have : v.IsNontrivial := isNontrivial_of_surjective hv
  have : v.Compatible := v.compatible_of_henselianLocalRing
  rw [normalizedValuationWithZero_eq_inv_of_surjective v hv x, inv_inv]

end Valuation

end SingleLocalField

section TwoLocalFields

variable {K L : Type*}
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]

namespace RingHom

/-- **Every ring homomorphism between nonarchimedean local fields is a closed topological
embedding.** -/
theorem isClosedEmbedding_of_isNonarchimedeanLocalField (f : K →+* L) :
    Topology.IsClosedEmbedding f := by
  let _ : Algebra K L := f.toAlgebra
  have : ValuativeExtension K L := .of_finite_residueField K L
  let _ := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  let _ := IsTopologicalAddGroup.rightUniformSpace L
  have := isUniformAddGroup_of_addCommGroup (G := L)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have hϖ0 : (ϖ : K) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have hfϖ : valuation L (f ϖ) < 1 :=
    (ValuativeExtension.valuation_algebraMap_lt_one_iff (A := K) (B := L) ϖ).mpr
      (Valuation.integer.v_irreducible_lt_one hϖ)
  refine TauCeti.isClosedEmbedding_algebraMap_of_coinitial K L fun y hy ↦ ?_
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hfϖ (Units.mk0 (valuation L y) (by simpa using hy))
  refine ⟨(ϖ : K) ^ n, pow_ne_zero n hϖ0, (valuation L).vle_iff_le.mpr ?_⟩
  simpa only [RingHom.algebraMap_toAlgebra, map_pow, Units.val_mk0] using hn.le

/-- **Automatic continuity of homomorphisms between nonarchimedean local fields**: every ring
homomorphism `f : K →+* L` is continuous. -/
theorem continuous_of_isNonarchimedeanLocalField (f : K →+* L) : Continuous f :=
  f.isClosedEmbedding_of_isNonarchimedeanLocalField.continuous

end RingHom

namespace RingEquiv

/-- **Every ring isomorphism between nonarchimedean local fields is a homeomorphism.** -/
noncomputable def homeomorphOfIsNonarchimedeanLocalField (e : K ≃+* L) : K ≃ₜ L where
  toEquiv := e.toEquiv
  continuous_toFun := e.toRingHom.continuous_of_isNonarchimedeanLocalField
  continuous_invFun := e.symm.toRingHom.continuous_of_isNonarchimedeanLocalField

/-- Coercing `e.homeomorphOfIsNonarchimedeanLocalField` to a function gives `e`. -/
@[simp]
theorem coe_homeomorphOfIsNonarchimedeanLocalField (e : K ≃+* L) :
    (e.homeomorphOfIsNonarchimedeanLocalField : K → L) = e :=
  (rfl)

/-- Applying `e.homeomorphOfIsNonarchimedeanLocalField` agrees with applying `e`. -/
theorem homeomorphOfIsNonarchimedeanLocalField_apply (e : K ≃+* L) (x : K) :
    e.homeomorphOfIsNonarchimedeanLocalField x = e x :=
  (rfl)

/-- Taking `.symm` commutes with `RingEquiv.homeomorphOfIsNonarchimedeanLocalField`. -/
@[simp]
theorem homeomorphOfIsNonarchimedeanLocalField_symm (e : K ≃+* L) :
    e.homeomorphOfIsNonarchimedeanLocalField.symm =
      e.symm.homeomorphOfIsNonarchimedeanLocalField :=
  (rfl)

end RingEquiv

end TwoLocalFields
