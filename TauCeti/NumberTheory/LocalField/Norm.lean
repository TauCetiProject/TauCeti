/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.NormTrace
public import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
public import TauCeti.NumberTheory.LocalField.InertiaDegree
public import TauCeti.NumberTheory.LocalField.Uniformizer
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.RingTheory.Norm.Units
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Valuation.Integral

/-!
# Norm valuations in finite local-field extensions

This file computes the normalized valuation of a field norm in finite extensions of
nonarchimedean local fields. Mapping the norm back to the extension field raises the original
valuation to the extension degree. The intrinsic formula is
`v_K(N_{L/K}(x)) = f(L/K) v_L(x)`.

The formula is the valuation input to the norm-group criterion for unramified extensions.  The
subsequent surjectivity-on-units argument identifies the entire norm group; this file deliberately
records only the valuation computation that that argument uses.

## Main results

* `TauCeti.normalizedValuation_algebraMap_norm`: the valuation calculation after applying the
  algebra map to a norm.
* `TauCeti.normalizedValuation_norm`: the normalized valuation of a norm is multiplied by the
  inertia degree.
* `TauCeti.toAdd_normalizedValuation_norm`: the preceding result in additive notation.
* `TauCeti.normalizedValuationWithZero_norm`: the same formula for arbitrary field elements,
  including zero.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7.
-/

public section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [FiniteDimensional K L]

/-- The norm of a valuation-zero unit has valuation zero in every finite local-field extension. -/
theorem normalizedValuation_norm_eq_one_of_eq_one (x : Lˣ)
    (hx : normalizedValuation L x = 1) :
    normalizedValuation K (Algebra.normUnits K x) = 1 := by
  have hint (y : Lˣ) (hy : normalizedValuation L y = 1) : IsIntegral 𝒪[K] (y : L) := by
    apply (Valuation.Integers.isIntegral_iff_valuation_le_one
      (Valuation.integer.integers (valuation K)) (y : L)).2
    rw [(normalizedValuation_eq_one_iff y).1 hy]
  have hnorm (y : Lˣ) (hy : normalizedValuation L y = 1) :
      0 ≤ (normalizedValuation K (Algebra.normUnits K y)).toAdd := by
    apply (mem_integer_iff_toAdd_normalizedValuation_nonneg _).1
    rw [Valuation.mem_integer_iff, Algebra.coe_normUnits]
    exact (Valuation.Integers.isIntegral_iff_v_le_one
      (Valuation.integer.integers (valuation K))).1
        (Algebra.isIntegral_norm K (hint y hy))
  have hxinv : normalizedValuation L x⁻¹ = 1 := by simp [hx]
  have h₁ := hnorm x hx
  have h₂ := hnorm x⁻¹ hxinv
  simp only [map_inv, toAdd_inv] at h₂
  apply Multiplicative.toAdd.injective
  simp only [toAdd_one]
  omega

/-- **Valuation of a norm in a finite local-field extension.** The normalized valuation of
`N_{L/K}(x)` is `f(L/K)` times the normalized valuation of `x`. -/
@[simp]
theorem normalizedValuation_norm (x : Lˣ) :
    normalizedValuation K (Algebra.normUnits K x) =
      normalizedValuation L x ^ inertiaDegree K L := by
  obtain ⟨t, ht⟩ := normalizedValuation_surjective (K := K) (normalizedValuation L x)
  let u : Lˣ := Units.map (algebraMap K L : K →* L) t
  have hu : normalizedValuation L u =
      normalizedValuation L x ^ ramificationIndex K L := by
    rw [normalizedValuation_algebraMap, ht]
  let y := x ^ ramificationIndex K L * u⁻¹
  have hy : normalizedValuation L y = 1 := by
    simp only [y, map_mul, map_pow, map_inv]
    rw [hu]
    simp
  have hnorm : Algebra.normUnits K u = t ^ Module.finrank K L := by
    apply Units.ext
    simp [u, Algebra.norm_algebraMap]
  have hmap : (normalizedValuation K (Algebra.normUnits K u)).toAdd =
      Module.finrank K L * (normalizedValuation L x).toAdd := by
    rw [hnorm, map_pow, ht, toAdd_pow, nsmul_eq_mul]
  have heq : (normalizedValuation K (Algebra.normUnits K y)).toAdd =
      ramificationIndex K L * (normalizedValuation K (Algebra.normUnits K x)).toAdd -
        (normalizedValuation K (Algebra.normUnits K u)).toAdd := by
    simp [y, toAdd_mul, toAdd_pow, toAdd_inv, sub_eq_add_neg]
  have h := congrArg Multiplicative.toAdd
    (normalizedValuation_norm_eq_one_of_eq_one (K := K) y hy)
  rw [heq, hmap, toAdd_one, ← ramificationIndex_mul_inertiaDegree (K := K) (L := L)] at h
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, nsmul_eq_mul]
  have he : (ramificationIndex K L : ℤ) ≠ 0 := by
    exact_mod_cast (ramificationIndex_pos (K := K) (L := L)).ne'
  simp only [Nat.cast_mul] at h
  exact mul_left_cancel₀ he (by simpa only [mul_assoc] using (sub_eq_zero.mp h))

/-- **Valuation of a norm after scalar extension.** This is the intrinsic norm formula
multiplied by the ramification index, using `e(L/K) f(L/K) = [L : K]`. -/
theorem normalizedValuation_algebraMap_norm (x : Lˣ) :
    normalizedValuation L (Units.map (algebraMap K L : K →* L) (Algebra.normUnits K x)) =
      normalizedValuation L x ^ Module.finrank K L := by
  rw [normalizedValuation_algebraMap, normalizedValuation_norm, ← pow_mul,
    mul_comm (inertiaDegree K L) (ramificationIndex K L),
    ramificationIndex_mul_inertiaDegree]

/-- **Additive valuation of a norm in a finite local-field extension.** This is
`v_K(N_{L/K}(x)) = f(L/K) v_L(x)`. -/
theorem toAdd_normalizedValuation_norm (x : Lˣ) :
    (normalizedValuation K (Algebra.normUnits K x)).toAdd =
      inertiaDegree K L * (normalizedValuation L x).toAdd := by
  rw [normalizedValuation_norm, toAdd_pow, nsmul_eq_mul]

/-- **Valuation of the field norm in a finite local-field extension**, including zero. -/
@[simp]
theorem normalizedValuationWithZero_norm (x : L) :
    normalizedValuationWithZero K (Algebra.norm K x) =
      normalizedValuationWithZero L x ^ inertiaDegree K L := by
  by_cases hx : x = 0
  · subst x
    have hzero : (0 : WithZero (Multiplicative ℤ)) ^ inertiaDegree K L = 0 :=
      zero_pow ((inertiaDegree_pos (K := K) (L := L)).ne')
    rw [Algebra.norm_zero]
    simpa only [map_zero] using hzero.symm
  · let x' : Lˣ := Units.mk0 x hx
    have hnorm : normalizedValuationWithZero K (Algebra.norm K (x' : L)) =
        normalizedValuationWithZero L (x' : L) ^ inertiaDegree K L := by
      rw [← Algebra.coe_normUnits K x', normalizedValuationWithZero_coe,
        normalizedValuationWithZero_coe, normalizedValuation_norm]
      exact WithZero.coe_pow _ _
    simpa only [x', Units.val_mk0] using hnorm


section NormGroup

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The norm group `N_{L/K}(Lˣ)` of a finite field extension `L/K`: the image in `Kˣ` of the field
norm on units, `Algebra.normUnits K : Lˣ →* Kˣ`. Finiteness is required because `Algebra.norm K`
is identically `1` on an infinite extension. -/
noncomputable def normGroup [_hfin : Module.Finite K L] : Subgroup Kˣ :=
  (Algebra.normUnits K : Lˣ →* Kˣ).range

variable {K L} in
/-- An element of `Kˣ` lies in the norm group exactly when it is the norm of a unit of `L`. -/
theorem mem_normGroup_iff [Module.Finite K L] {x : Kˣ} :
    x ∈ normGroup K L ↔ ∃ y : Lˣ, Algebra.norm K (y : L) = x := by
  simp [normGroup, Units.ext_iff]

/-- The norm of a unit of `L` lies in the norm group. -/
theorem normUnits_mem_normGroup [Module.Finite K L] (y : Lˣ) :
    Algebra.normUnits K y ∈ normGroup K L :=
  ⟨y, rfl⟩

end NormGroup

omit [FiniteDimensional K L] in
/-- The norm of `𝒪[L]` over `𝒪[K]`, a free module of finite rank, is the restriction of the field
norm of `L/K`. -/
@[simp]
theorem coe_norm_integerRing (y : 𝒪[L]) :
    ((Algebra.norm 𝒪[K] y : 𝒪[K]) : K) = Algebra.norm K (y : L) := by
  have := isLocalization_integerRing K L
  exact (Algebra.norm_localization 𝒪[K] (nonZeroDivisors 𝒪[K]) y).symm

omit [FiniteDimensional K L] in
/-- The norm of an element of `𝒪[L]` lies in `𝒪[K]`. -/
theorem norm_mem_integer {y : L} (hy : y ∈ 𝒪[L]) : Algebra.norm K y ∈ 𝒪[K] := by
  simpa using (Algebra.norm 𝒪[K] (⟨y, hy⟩ : 𝒪[L])).2

/-- A unit of `L` is a unit of `𝒪[L]` exactly when its norm is a unit of `𝒪[K]`. -/
theorem normUnits_mem_unitFiltration_zero_iff {y : Lˣ} :
    Algebra.normUnits K y ∈ unitFiltration K 0 ↔ y ∈ unitFiltration L 0 := by
  rw [mem_unitFiltration_zero, mem_unitFiltration_zero, ← normalizedValuation_eq_one_iff,
    ← normalizedValuation_eq_one_iff, normalizedValuation_norm,
    pow_eq_one_iff_left (inertiaDegree_pos (K := K) (L := L)).ne']

variable (K L) in
/-- The norm carries the units of `𝒪[L]` into the units of `𝒪[K]`: `N_{L/K}(U(L,0)) ⊆ U(K,0)`. -/
theorem map_normUnits_unitFiltration_zero_le :
    (unitFiltration L 0).map (Algebra.normUnits K) ≤ unitFiltration K 0 := by
  rintro _ ⟨y, hy, rfl⟩
  exact normUnits_mem_unitFiltration_zero_iff.2 hy

/-- The norm of a uniformizer of `L` is a uniformizer of `K` exactly when the residue degree is
`1`, that is when `L/K` is totally ramified. -/
theorem isUniformizer_normUnits_iff {ϖ : Lˣ} (hϖ : IsUniformizer L ϖ) :
    IsUniformizer K (Algebra.normUnits K ϖ) ↔ inertiaDegree K L = 1 := by
  rw [isUniformizer_def] at hϖ ⊢
  rw [normalizedValuation_norm, hϖ, ← ofAdd_nsmul, Multiplicative.ofAdd.injective.eq_iff,
    nsmul_one]
  exact Nat.cast_eq_one

variable (L) in
omit [FiniteDimensional K L] in
/-- The normalized valuation of an element of the norm group `N_{L/K}(Lˣ)` is divisible by the
residue degree `f(L/K)`. -/
theorem inertiaDegree_dvd_of_mem_normGroup [Module.Finite K L] {x : Kˣ}
    (hx : x ∈ normGroup K L) :
    (inertiaDegree K L : ℤ) ∣ (normalizedValuation K x).toAdd := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨_, toAdd_normalizedValuation_norm y⟩

end TauCeti
