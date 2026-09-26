/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Norm.Basic
public import TauCeti.NumberTheory.LocalField.Unramified
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Trace.Quotient
import TauCeti.NumberTheory.LocalField.Henselian
import TauCeti.RingTheory.Norm.Henselian
import TauCeti.RingTheory.Norm.Quotient

/-!
# Norms in unramified extensions of local fields

Let `L/K` be a finite unramified extension of nonarchimedean local fields. This file proves that
the norm maps the units of `𝒪[L]` onto the units of `𝒪[K]`,

`N_{L/K}(U(L,0)) = U(K,0)`,

and deduces the norm-equation criterion: an element `x` of `Kˣ` is a norm from `L` exactly when
the residue degree `f(L/K)` divides `v_K(x)`. So `N_{L/K}(Lˣ) = π^{fℤ} × 𝒪[K]ˣ` for any
uniformizer `π` of `K`, in the form that decides the norm equation one element at a time.

Surjectivity on units is Hensel's lemma for the norm
(`TauCeti.Algebra.exists_norm_eq_of_norm_sub_mem_maximalIdeal`), applied to the finite free
`𝒪[K]`-algebra `𝒪[L]`. Its two residual inputs hold because `𝓂[K] 𝒪[L] = 𝓂[L]`, so that
`𝒪[L] ⧸ 𝓂[K] 𝒪[L]` is the residue field of `L`, a finite extension of the finite residue field of
`K`: the norm of a finite extension of finite fields is surjective, and its trace is surjective
because the extension is separable. Norm and trace commute with reduction modulo `𝓂[K]`.

⚠ Both statements fail for ramified extensions: at `L = ℚ_2(√2)` the norms of the units of
`𝒪[L]` form a subgroup of index `2` in `ℤ_2ˣ`.

## Main results

* `TauCeti.map_normUnits_unitFiltration_zero`: in an unramified extension the norm maps
  `U(L,0)` onto `U(K,0)`.
* `TauCeti.mem_normGroup_iff_dvd_normalizedValuation`: in an unramified extension `x ∈ Kˣ` is a
  norm exactly when `f(L/K)` divides `v_K(x)`.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §7 and Chapter V, §1.
-/

public section

open ValuativeRel IsLocalRing

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [FiniteDimensional K L] [IsUnramified K L]

attribute [local instance] Ideal.Quotient.field

omit [FiniteDimensional K L] in
/-- In an unramified extension the ideal `𝓂[K] 𝒪[L]` is maximal. -/
private theorem isMaximal_map_maximalIdeal :
    (𝓂[K].map (algebraMap 𝒪[K] 𝒪[L])).IsMaximal := by
  rw [IsUnramified.map_maximalIdeal (K := K)]
  exact maximalIdeal.isMaximal _

attribute [local instance] isMaximal_map_maximalIdeal

omit [IsNonarchimedeanLocalField L] [ValuativeExtension K L] [FiniteDimensional K L]
  [IsUnramified K L] in
/-- The residue ring `𝒪[K] ⧸ 𝓂[K]` is finite. -/
private theorem finite_quotient_maximalIdeal : Finite (𝒪[K] ⧸ 𝓂[K]) :=
  inferInstanceAs (Finite 𝓀[K])

omit [FiniteDimensional K L] [IsUnramified K L] in
/-- `𝒪[L] ⧸ 𝓂[K] 𝒪[L]` is finite over `𝒪[K] ⧸ 𝓂[K]`. -/
private theorem moduleFinite_quotient :
    Module.Finite (𝒪[K] ⧸ 𝓂[K]) (𝒪[L] ⧸ 𝓂[K].map (algebraMap 𝒪[K] 𝒪[L])) :=
  Module.Finite.of_restrictScalars_finite 𝒪[K] _ _

attribute [local instance] finite_quotient_maximalIdeal moduleFinite_quotient

omit [FiniteDimensional K L] in
/-- Every element of `𝒪[K]` is a norm from `𝒪[L]` modulo `𝓂[K]`. -/
private theorem exists_norm_sub_mem_maximalIdeal (v : 𝒪[K]) :
    ∃ a : 𝒪[L], Algebra.norm 𝒪[K] a - v ∈ 𝓂[K] := by
  have := Module.finite_of_finite (𝒪[K] ⧸ 𝓂[K])
    (M := 𝒪[L] ⧸ 𝓂[K].map (algebraMap 𝒪[K] 𝒪[L]))
  obtain ⟨a, ha⟩ := FiniteField.norm_surjective (𝒪[K] ⧸ 𝓂[K])
    (𝒪[L] ⧸ 𝓂[K].map (algebraMap 𝒪[K] 𝒪[L])) (Ideal.Quotient.mk _ v)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨a, Ideal.Quotient.eq.1 ?_⟩
  rw [← Algebra.norm_quotient_mk, ha]

omit [FiniteDimensional K L] in
/-- Some unit of `𝒪[L]` has a unit trace over `𝒪[K]`. -/
private theorem exists_isUnit_trace :
    ∃ w : 𝒪[L], IsUnit w ∧ IsUnit (Algebra.trace 𝒪[K] 𝒪[L] w) := by
  obtain ⟨w, hw⟩ := Algebra.trace_surjective (𝒪[K] ⧸ 𝓂[K])
    (𝒪[L] ⧸ 𝓂[K].map (algebraMap 𝒪[K] 𝒪[L])) 1
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine ⟨w, notMem_maximalIdeal.1 fun h ↦ ?_, notMem_maximalIdeal.1 fun h ↦ ?_⟩
  · rw [← IsUnramified.map_maximalIdeal (K := K), ← Ideal.Quotient.eq_zero_iff_mem] at h
    rw [h, map_zero] at hw
    exact zero_ne_one hw
  · rw [← Ideal.Quotient.eq_zero_iff_mem] at h
    rw [Algebra.trace_quotient_mk, h] at hw
    exact zero_ne_one hw

variable (K L) in
/-- **The norm is surjective on units in an unramified extension.** If `L/K` is unramified, the
norm maps the units of `𝒪[L]` onto the units of `𝒪[K]`: `N_{L/K}(U(L,0)) = U(K,0)`. -/
theorem map_normUnits_unitFiltration_zero :
    (unitFiltration L 0).map (Algebra.normUnits K) = unitFiltration K 0 := by
  refine le_antisymm (map_normUnits_unitFiltration_zero_le K L) fun x hx ↦ ?_
  let u := unitFiltrationZeroEquivIntegerUnits ⟨x, hx⟩
  obtain ⟨w, hw, htr⟩ := exists_isUnit_trace (K := K) (L := L)
  obtain ⟨a, ha⟩ := exists_norm_sub_mem_maximalIdeal (L := L) (u : 𝒪[K])
  obtain ⟨y, hy, -⟩ := Algebra.exists_norm_eq_of_norm_sub_mem_maximalIdeal hw htr u.isUnit ha
  have hyK : Algebra.norm K (y : L) = x := by
    rw [← coe_norm_integerRing, hy, coe_unitFiltrationZeroEquivIntegerUnits]
  have hy0 : (y : L) ≠ 0 := fun h ↦ x.ne_zero (by rw [← hyK, h, Algebra.norm_zero])
  have hyx : Algebra.normUnits K (Units.mk0 (y : L) hy0) = x := Units.ext (by simpa using hyK)
  exact ⟨Units.mk0 (y : L) hy0, normUnits_mem_unitFiltration_zero_iff.1 (hyx ▸ hx), hyx⟩

/-- **The norm-equation criterion in an unramified extension.** If `L/K` is unramified, an
element `x` of `Kˣ` is a norm from `L` exactly when the residue degree `f(L/K)` divides
`v_K(x)`. -/
theorem mem_normGroup_iff_dvd_normalizedValuation {x : Kˣ} :
    x ∈ normGroup K L ↔ (inertiaDegree K L : ℤ) ∣ (normalizedValuation K x).toAdd := by
  refine ⟨inertiaDegree_dvd_of_mem_normGroup L, fun ⟨m, hm⟩ ↦ ?_⟩
  obtain ⟨π, hπ⟩ := exists_isUniformizer (K := K)
  rw [isUniformizer_def] at hπ
  have hπN : π ^ inertiaDegree K L ∈ normGroup K L :=
    mem_normGroup_iff.2 ⟨Units.map (algebraMap K L : K →* L) π, by
      simp [Algebra.norm_algebraMap, IsUnramified.inertiaDegree_eq_finrank]⟩
  have hU : unitFiltration K 0 ≤ normGroup K L := by
    rw [← map_normUnits_unitFiltration_zero K L]
    rintro _ ⟨y, -, rfl⟩
    exact mem_normGroup_iff.2 ⟨y, by simp⟩
  have hu : x * (π ^ inertiaDegree K L) ^ (-m) ∈ unitFiltration K 0 := by
    refine (mem_unitFiltration_zero _).2 ((normalizedValuation_eq_one_iff _).1 ?_)
    apply Multiplicative.toAdd.injective
    simp only [map_mul, map_zpow, map_pow, toAdd_mul, toAdd_zpow, toAdd_pow, hm, hπ,
      toAdd_ofAdd, toAdd_one, nsmul_eq_mul, smul_eq_mul]
    ring
  simpa using mul_mem (hU hu) (zpow_mem hπN m)

end TauCeti
