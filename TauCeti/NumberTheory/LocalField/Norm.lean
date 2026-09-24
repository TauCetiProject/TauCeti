/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.NormTrace
public import TauCeti.RingTheory.Norm.Units
public import TauCeti.NumberTheory.LocalField.InertiaDegree
public import TauCeti.NumberTheory.LocalField.Uniformizer
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic

/-!
# The field norm of an extension of local fields

Let `L/K` be an extension of nonarchimedean local fields whose valuations are compatible, in the
sense of `ValuativeExtension K L`. This file records how the field norm `N_{L/K}` interacts with
the normalized valuations:

`v_K(N_{L/K}(y)) = f(L/K) · v_L(y)` for every `y : Lˣ`,

where `f(L/K) = inertiaDegree K L` is the residue degree. It is the multiplicative counterpart of
the characteristic property `v_L(x) = e(L/K) · v_K(x)` of the ramification index, and the two are
tied together by `e · f = [L : K]` and `N_{L/K}(x) = x ^ [L : K]` for `x : K`.

Consequently the norm carries units of `𝒪[L]` to units of `𝒪[K]`, and only those: a unit of `L`
lies in the depth-zero step `U(L,0)` of the unit filtration exactly when its norm lies in
`U(K,0)`. The norm of a uniformizer of `L` has valuation `f(L/K)`, so it is a uniformizer of `K`
exactly when `f(L/K) = 1`, that is when `L/K` is totally ramified. Every element of the norm group
`N_{L/K}(Lˣ)` therefore has valuation divisible by `f(L/K)`; for an unramified extension this is
the necessary half of the norm-equation criterion.

The norm of `𝒪[L]` over `𝒪[K]`, which is a free module of finite rank, is the restriction of the
field norm, so the norm of an integral element is integral.

The norm on unit groups is `TauCeti.Algebra.normUnits K : Lˣ →* Kˣ`, the field norm
`Algebra.norm K` read on units.

## Main definitions

* `TauCeti.normGroup K L`: the norm group `N_{L/K}(Lˣ)` of a finite extension, the image of the
  field norm in `Kˣ`.

## Main results

* `TauCeti.coe_norm_integerRing`: the norm of `𝒪[L]` over `𝒪[K]` is the field norm on integers.
* `TauCeti.normalizedValuation_normUnits`: `v_K(N_{L/K}(y)) = f(L/K) · v_L(y)`,
  multiplicatively; `TauCeti.toAdd_normalizedValuation_normUnits` and
  `TauCeti.normalizedValuationWithZero_norm` are the additive form and the form on all of `L`.
* `TauCeti.normUnits_mem_unitFiltration_zero_iff` and
  `TauCeti.map_normUnits_unitFiltration_zero_le`: the norm maps `U(L,0)` into `U(K,0)`, and a
  unit of `L` whose norm is in `U(K,0)` is in `U(L,0)`.
* `TauCeti.isUniformizer_normUnits_iff`: the norm of a uniformizer of `L` is a uniformizer of `K`
  exactly when `f(L/K) = 1`.
* `TauCeti.inertiaDegree_dvd_of_mem_normGroup`: the valuation of an element of the norm group is
  divisible by `f(L/K)`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter I, §4 and Chapter V, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti

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

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- The norm of `𝒪[L]` over `𝒪[K]`, a free module of finite rank, is the restriction of the field
norm of `L/K`. -/
@[simp]
theorem coe_norm_integerRing (y : 𝒪[L]) :
    ((Algebra.norm 𝒪[K] y : 𝒪[K]) : K) = Algebra.norm K (y : L) := by
  have := isLocalization_integerRing K L
  exact (Algebra.norm_localization 𝒪[K] (nonZeroDivisors 𝒪[K]) y).symm

/-- The norm of an element of `𝒪[L]` lies in `𝒪[K]`. -/
theorem norm_mem_integer {y : L} (hy : y ∈ 𝒪[L]) : Algebra.norm K y ∈ 𝒪[K] := by
  simpa using (Algebra.norm 𝒪[K] (⟨y, hy⟩ : 𝒪[L])).2

/-- The norm of a unit of `𝒪[L]` is a unit of `𝒪[K]`, stated on normalized valuations. -/
private theorem normalizedValuation_normUnits_eq_one {u : Lˣ} (hu : valuation L (u : L) = 1) :
    normalizedValuation K (Algebra.normUnits K u) = 1 := by
  have hmem : (u : L) ∈ 𝒪[L] := (Valuation.mem_integer_iff _ _).2 hu.le
  have hunit : IsUnit (⟨u, hmem⟩ : 𝒪[L]) :=
    (Valuation.integer.integers (valuation L)).isUnit_of_one' hu
  have h := coe_norm_integerRing (K := K) ⟨(u : L), hmem⟩
  rw [Subtype.coe_mk] at h
  rw [normalizedValuation_eq_one_iff, Algebra.coe_normUnits, ← h]
  exact (Valuation.integer.integers (valuation K)).valuation_unit
    (hunit.map (Algebra.norm 𝒪[K] : 𝒪[L] →* 𝒪[K])).unit

/-- The norm of a uniformizer of `L`, written as an irreducible element of `𝒪[L]`, has normalized
valuation `f(L/K)`. -/
private theorem normalizedValuation_normUnits_irreducible {ϖ : 𝒪[L]} (hϖ : Irreducible ϖ) :
    normalizedValuation K (Algebra.normUnits K
      (Units.mk0 (ϖ : L) fun h ↦ hϖ.ne_zero (Subtype.ext h))) =
        Multiplicative.ofAdd (inertiaDegree K L : ℤ) := by
  -- Compare the valuations of `N_{L/K}(π_K) = π_K ^ [L : K]` and of `π_K = u · ϖ ^ e(L/K)`:
  -- this gives `e · v_K(N_{L/K}(ϖ)) = [L : K] = e · f`.
  have := finite_of_valuativeExtension K L
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  set πu : Kˣ := Units.mk0 (π : K) fun h ↦ hπ.ne_zero (Subtype.ext h)
  obtain ⟨u, n, hu, hπu⟩ :=
    exists_eq_mul_zpow_of_irreducible hϖ (Units.map (algebraMap K L : K →* L) πu)
  -- The exponent of `ϖ` in `π_K` is the ramification index.
  have hn : n = ramificationIndex K L := by
    have h := congrArg (fun z ↦ (normalizedValuation L z).toAdd) hπu
    simpa [πu, normalizedValuation_irreducible hπ, normalizedValuation_irreducible hϖ,
      (normalizedValuation_eq_one_iff u).2 hu] using h.symm
  -- The norm of `π_K` is `π_K ^ [L : K]`.
  have hNπ : Algebra.normUnits K (Units.map (algebraMap K L : K →* L) πu) =
      πu ^ Module.finrank K L :=
    Units.ext (by simp [Algebra.norm_algebraMap])
  have h := congrArg (fun z ↦ (normalizedValuation K (Algebra.normUnits K z)).toAdd) hπu
  simp only [hNπ, map_mul, map_zpow, map_pow, normalizedValuation_normUnits_eq_one hu, one_mul,
    πu, normalizedValuation_irreducible hπ, toAdd_pow, toAdd_zpow, toAdd_ofAdd, hn] at h
  rw [← ramificationIndex_mul_inertiaDegree K L] at h
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd]
  have he : (ramificationIndex K L : ℤ) ≠ 0 := by exact_mod_cast ramificationIndex_pos.ne'
  apply mul_left_cancel₀ he
  simpa [mul_comm] using h.symm

/-- **The valuation of a norm**: `v_K(N_{L/K}(y)) = f(L/K) · v_L(y)` for every `y : Lˣ`, written
multiplicatively, where `f(L/K)` is the residue degree. -/
@[simp]
theorem normalizedValuation_normUnits (y : Lˣ) :
    normalizedValuation K (Algebra.normUnits K y) =
      normalizedValuation L y ^ inertiaDegree K L := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[L]
  obtain ⟨u, n, hu, rfl⟩ := exists_eq_mul_zpow_of_irreducible hϖ y
  simp only [map_mul, map_zpow, normalizedValuation_normUnits_irreducible hϖ,
    normalizedValuation_normUnits_eq_one hu, (normalizedValuation_eq_one_iff u).2 hu,
    normalizedValuation_irreducible hϖ, one_mul]
  apply Multiplicative.toAdd.injective
  simp [mul_comm]

/-- The valuation of a norm in additive form: `v_K(N_{L/K}(y)) = f(L/K) · v_L(y)`. -/
theorem toAdd_normalizedValuation_normUnits (y : Lˣ) :
    (normalizedValuation K (Algebra.normUnits K y)).toAdd =
      inertiaDegree K L * (normalizedValuation L y).toAdd := by
  rw [normalizedValuation_normUnits, toAdd_pow, nsmul_eq_mul]

/-- The valuation of a norm for the zero-preserving normalized valuations, on all of `L`. -/
@[simp]
theorem normalizedValuationWithZero_norm (y : L) :
    normalizedValuationWithZero K (Algebra.norm K y) =
      normalizedValuationWithZero L y ^ inertiaDegree K L := by
  have := finite_of_valuativeExtension K L
  rcases eq_or_ne y 0 with rfl | hy
  · simp [zero_pow inertiaDegree_pos.ne']
  · have hK := normalizedValuationWithZero_coe (Algebra.normUnits K (Units.mk0 y hy))
    have hL := normalizedValuationWithZero_coe (Units.mk0 y hy)
    rw [Algebra.coe_normUnits, Units.val_mk0] at hK
    rw [Units.val_mk0] at hL
    rw [hK, hL, normalizedValuation_normUnits, WithZero.coe_pow]

/-- A unit of `L` is a unit of `𝒪[L]` exactly when its norm is a unit of `𝒪[K]`. -/
theorem normUnits_mem_unitFiltration_zero_iff {y : Lˣ} :
    Algebra.normUnits K y ∈ unitFiltration K 0 ↔ y ∈ unitFiltration L 0 := by
  rw [mem_unitFiltration_zero, mem_unitFiltration_zero, ← normalizedValuation_eq_one_iff,
    ← normalizedValuation_eq_one_iff, normalizedValuation_normUnits,
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
  rw [normalizedValuation_normUnits, hϖ, ← ofAdd_nsmul, Multiplicative.ofAdd.injective.eq_iff,
    nsmul_one]
  exact Nat.cast_eq_one

variable (L) in
/-- The normalized valuation of an element of the norm group `N_{L/K}(Lˣ)` is divisible by the
residue degree `f(L/K)`. -/
theorem inertiaDegree_dvd_of_mem_normGroup [Module.Finite K L] {x : Kˣ}
    (hx : x ∈ normGroup K L) :
    (inertiaDegree K L : ℤ) ∣ (normalizedValuation K x).toAdd := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨_, toAdd_normalizedValuation_normUnits y⟩

end TauCeti
