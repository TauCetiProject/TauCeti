/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.WithVal
public import TauCeti.RingTheory.Huber.CompleteRankOneBase.Basic
public import TauCeti.RingTheory.Huber.LocalizationTopology.Away

import TauCeti.RingTheory.KrullDimension.LocalRing
import TauCeti.RingTheory.Valuation.AdicSeparated
import TauCeti.RingTheory.Valuation.Integers
import TauCeti.Topology.Algebra.Nonarchimedean.AdicTopology.Basic

/-!
# The valued fraction field of a complete rank-one valuation base

Let `O` be a valuation domain carrying the standing data `TauCeti.Huber.IsCompleteRankOneBase O ϖ`
with pseudouniformiser `ϖ`, and let `K` be a fraction field of `O` with canonical valuation
`v = ValuationRing.valuation O K`.

* Because `O` has Krull dimension one and `ϖ` is a nonzero nonunit, the radical of `(ϖ)` is the
  maximal ideal of `O`, so every nonunit of `O` has a power divisible by `ϖ`
  (`IsCompleteRankOneBase.exists_dvd_pow_of_not_isUnit`).
* Because `O` is `ϖ`-adically separated, every nonzero element of `O` divides a power of `ϖ`, so
  `K` is already the localisation `O[1/ϖ]` (`IsCompleteRankOneBase.isLocalization_away`).
* Together these two divisibility properties make the value group of any valuation on `K` with
  integer ring `O` archimedean and nontrivial, so `v` has rank one
  (`IsCompleteRankOneBase.nonempty_rankOne_valuation`).
* On the valued field `WithVal v`, the subgroups `ϖⁿ O` form a neighbourhood basis of zero, so
  `WithVal v` is complete (`IsCompleteRankOneBase.completeSpace_withVal`) and `O` is isomorphic
  as a topological ring to its valuation subring `(Valued.v).integer`
  (`IsCompleteRankOneBase.equivIntegerWithVal`).

Equipping `WithVal (ValuationRing.valuation O (FractionRing O))` with a `Valuation.RankOne`
instance therefore realises `O` as the closed unit ball of a complete nontrivially normed
ultrametric field, without placing non-canonical topological instances on `FractionRing O`.

## References

* S. Bosch and W. Lütkebohmert, *Formal and rigid geometry. I. Rigid spaces*, Math. Ann. 295
  (1993), §1.
* B. Conrad, *Several approaches to non-archimedean geometry*, in *p-adic Geometry* (Arizona
  Winter School 2007), §3.3.
-/

public section

open Filter IsLocalRing MonoidWithZeroHom Topology
open scoped nonZeroDivisors

namespace TauCeti.Huber.IsCompleteRankOneBase

section Radical

variable {O : Type*} [CommRing O] [TopologicalSpace O] (ϖ : O) [IsCompleteRankOneBase O ϖ]

include ϖ

/-- Every nonunit in a complete rank-one valuation base domain has a power divisible by the
pseudouniformiser `ϖ`. -/
theorem exists_dvd_pow_of_not_isUnit [IsDomain O] [IsLocalRing O] {d : O} (hd : ¬ IsUnit d) :
    ∃ n : ℕ, ϖ ∣ d ^ n := by
  have hd_mem : d ∈ (Ideal.span {ϖ}).radical := by
    rw [TauCeti.radical_span_singleton_eq_maximalIdeal_of_ringKrullDim_eq_one
      (ringKrullDim_eq_one (O := O) (ϖ := ϖ))
      ((mem_maximalIdeal _).mpr (not_isUnit (O := O) (ϖ := ϖ))) (ne_zero (O := O) (ϖ := ϖ))]
    exact (mem_maximalIdeal _).mpr hd
  obtain ⟨n, hn⟩ := hd_mem
  exact ⟨n, Ideal.mem_span_singleton.mp hn⟩

end Radical

section FractionField

variable {O : Type*} [CommRing O] [IsDomain O] [ValuationRing O] [TopologicalSpace O]
  (ϖ : O) [IsCompleteRankOneBase O ϖ] (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K]

include ϖ in
/-- Any fraction field of a complete rank-one valuation base `O` is the localisation `O[1/ϖ]`. -/
theorem isLocalization_away : IsLocalization.Away ϖ K :=
  TauCeti.PreValuationRing.isLocalization_away_of_isFractionRing (ne_zero (O := O) (ϖ := ϖ)) K

omit [IsDomain O] [ValuationRing O] in
include ϖ in
/-- Any valuation on a fraction field of a complete rank-one valuation base `O` with integer ring
`O` is nontrivial: `ϖ` has nonzero valuation strictly less than `1`. -/
theorem isNontrivial_of_integers {K : Type*} [Field K] [Algebra O K]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} (hv : v.Integers O) :
    v.IsNontrivial :=
  hv.isNontrivial_of_ne_zero_of_not_isUnit (ne_zero (O := O) (ϖ := ϖ))
    (not_isUnit (O := O) (ϖ := ϖ))

include ϖ in
/-- The canonical valuation on a fraction field of a complete rank-one valuation base is
nontrivial. -/
theorem isNontrivial_valuation : (ValuationRing.valuation O K).IsNontrivial :=
  isNontrivial_of_integers ϖ (ValuationRing.integers O K)

include ϖ in
/-- For any valuation `v` on a fraction field `K` of a complete rank-one valuation base `O` with
integer ring `O`, the restricted value group `v.ValueGroup₀` is archimedean. -/
theorem mulArchimedean_valueGroup₀_of_integers {K : Type*} [Field K] [Algebra O K]
    [IsFractionRing O K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀}
    (hv : v.Integers O) :
    MulArchimedean v.ValueGroup₀ := by
  have : IsLocalization.Away ϖ K := isLocalization_away ϖ K
  let w : Valuation K v.ValueGroup₀ := v.restrict
  have hw_int (a : O) : w (algebraMap O K a) ≤ 1 := v.restrict_le_one_iff.mpr (hv.map_le_one a)
  have hw_dvd {a b : O} (h : a ∣ b) : w (algebraMap O K b) ≤ w (algebraMap O K a) :=
    v.restrict_le_iff.mpr (hv.le_of_dvd h)
  refine ⟨fun x {y} hy ↦ ?_⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, by simp⟩
  obtain ⟨α, rfl⟩ : ∃ α : K, w α = x := ValueGroup₀.restrict₀_surjective (v : K →*₀ Γ₀) x
  obtain ⟨β, rfl⟩ : ∃ β : K, w β = y := ValueGroup₀.restrict₀_surjective (v : K →*₀ Γ₀) y
  have hβ0 : w β ≠ 0 := ne_of_gt (zero_lt_one.trans hy)
  have hβinv_lt : w β⁻¹ < 1 := by
    rw [map_inv₀, inv_lt_one₀ (pos_iff_ne_zero.mpr hβ0)]
    exact hy
  obtain ⟨d, hd⟩ := hv.exists_of_le_one (v.restrict_le_one_iff.mp hβinv_lt.le)
  have hd_not_unit : ¬ IsUnit d := fun hu ↦
    hβinv_lt.ne (hd ▸ v.restrict_eq_one_iff.mpr (hv.one_of_isUnit hu))
  obtain ⟨N, hN⟩ := exists_dvd_pow_of_not_isUnit ϖ hd_not_unit
  -- `ϖ ∣ d ^ N` gives `w(ϖ)⁻¹ ≤ w(β) ^ N`.
  have hϖK : algebraMap O K ϖ ≠ 0 :=
    (map_ne_zero_iff _ hv.hom_inj).mpr (ne_zero (O := O) (ϖ := ϖ))
  have hϖ0 : w (algebraMap O K ϖ) ≠ 0 := (Valuation.ne_zero_iff w).mpr hϖK
  have hϖ_le : (w (algebraMap O K ϖ))⁻¹ ≤ w β ^ N := by
    have hdN : w (algebraMap O K d) ^ N ≤ w (algebraMap O K ϖ) := by
      simpa only [map_pow] using hw_dvd hN
    rw [hd, map_inv₀, inv_pow, inv_le_comm₀ (pos_iff_ne_zero.mpr (pow_ne_zero N hβ0))
      (pos_iff_ne_zero.mpr hϖ0)] at hdN
    exact hdN
  -- `α = a / ϖ ^ m` gives `w(α) ≤ w(ϖ)⁻¹ ^ m ≤ w(β) ^ (N * m)`.
  obtain ⟨m, a, hma⟩ := IsLocalization.Away.surj ϖ α
  have hα_eq : α = algebraMap O K a * (algebraMap O K ϖ)⁻¹ ^ m := by
    rw [inv_pow, eq_mul_inv_iff_mul_eq₀ (pow_ne_zero m hϖK)]
    exact hma
  have hα_le : w α ≤ (w (algebraMap O K ϖ))⁻¹ ^ m := by
    rw [hα_eq, map_mul, map_pow, map_inv₀]
    exact mul_le_of_le_one_left' (hw_int a)
  exact ⟨N * m, by simpa only [pow_mul] using hα_le.trans (pow_le_pow_left' hϖ_le m)⟩

include ϖ in
/-- The value group of `ValuationRing.valuation O K` over a complete rank-one valuation base is
archimedean. -/
theorem mulArchimedean_valueGroup₀_valuation :
    MulArchimedean (ValuationRing.valuation O K).ValueGroup₀ :=
  mulArchimedean_valueGroup₀_of_integers ϖ (ValuationRing.integers O K)

include ϖ in
/-- The canonical valuation on a fraction field of a complete rank-one valuation base has rank
one. -/
theorem nonempty_rankOne_valuation : Nonempty (ValuationRing.valuation O K).RankOne := by
  have := isNontrivial_valuation ϖ K
  exact Valuation.nonempty_rankOne_iff_mulArchimedean.mpr
    (mulArchimedean_valueGroup₀_valuation ϖ K)

include ϖ in
/-- On `WithVal (ValuationRing.valuation O K)`, the valuation `Valued.v` has rank one. -/
theorem nonempty_rankOne_withVal :
    Nonempty (Valued.v (R := WithVal (ValuationRing.valuation O K))).RankOne := by
  set v := ValuationRing.valuation O K
  have : (Valued.v (R := WithVal v)).IsNontrivial := by
    obtain ⟨x, hx0, hx1⟩ := (isNontrivial_valuation ϖ K).exists_val_nontrivial
    exact ⟨WithVal.toVal v x, by simpa using hx0, by simpa using hx1⟩
  have := mulArchimedean_valueGroup₀_valuation ϖ K
  have hma : MulArchimedean (Valued.v (R := WithVal v)).ValueGroup₀ :=
    MulArchimedean.comap (WithVal.valueGroupOrderIso₀ v).toMonoidHom
      (WithVal.strictMono_valueGroupOrderIso₀ v)
  exact Valuation.nonempty_rankOne_iff_mulArchimedean.mpr hma

include ϖ in
/-- The subgroups `ϖⁿ O` form a neighbourhood basis of zero in the valued fraction field
`WithVal (ValuationRing.valuation O K)`. -/
theorem hasBasis_nhds_zero_withVal :
    (𝓝 (0 : WithVal (ValuationRing.valuation O K))).HasBasis (fun _ : ℕ ↦ True)
      fun n ↦ (awayNhd ϖ (WithVal (ValuationRing.valuation O K)) n : Set _) := by
  set v := ValuationRing.valuation O K
  let _ : (Valued.v (R := WithVal v)).RankOne := Classical.choice (nonempty_rankOne_withVal ϖ K)
  open scoped Valued in
  have hv : (Valued.v (R := WithVal v)).Integers O :=
    { hom_inj := WithVal.algebraMap_right_injective v (IsFractionRing.injective O K)
      map_le_one := fun a ↦ (ValuationRing.integers O K).map_le_one a
      exists_of_le_one := fun {x} hx ↦ by
        obtain ⟨a, ha⟩ := (ValuationRing.integers O K).exists_of_le_one (r := x.ofVal) hx
        exact ⟨a, WithVal.ofVal_injective v ha⟩ }
  have hϖ0 : 0 < ‖algebraMap O (WithVal v) ϖ‖ :=
    norm_pos_iff.mpr ((map_ne_zero_iff _ hv.hom_inj).mpr (ne_zero (O := O) (ϖ := ϖ)))
  have hϖ1 : ‖algebraMap O (WithVal v) ϖ‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff]
    refine lt_of_le_of_ne (hv.map_le_one ϖ) fun h1 ↦ not_isUnit (O := O) (ϖ := ϖ) ?_
    exact hv.isUnit_of_one (isUnit_iff_ne_zero.mpr (norm_pos_iff.mp hϖ0)) h1
  -- Under the rank-one norm inducing the valuation topology, `awayNhd ϖ _ n` is precisely the
  -- closed ball of radius `‖ϖ‖ ^ n`.
  have hball (n : ℕ) : (awayNhd ϖ (WithVal v) n : Set (WithVal v)) =
      {x : WithVal v | ‖x‖ ≤ ‖algebraMap O (WithVal v) ϖ‖ ^ n} := by
    ext x
    simp only [SetLike.mem_coe, mem_awayNhd, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, rfl⟩
      rw [map_mul, map_pow, norm_mul, norm_pow]
      exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) n)
        (Valued.toNormedField.norm_le_one_iff.mpr (hv.map_le_one a))
    · intro hx
      have hdiv : Valued.v (x / algebraMap O (WithVal v) ϖ ^ n) ≤ 1 := by
        rw [← Valued.toNormedField.norm_le_one_iff, norm_div, norm_pow]
        exact (div_le_one (pow_pos hϖ0 n)).mpr hx
      obtain ⟨a, ha⟩ := hv.exists_of_le_one hdiv
      refine ⟨a, ?_⟩
      rw [map_mul, map_pow, ha, mul_div_cancel₀ _ (pow_ne_zero n (norm_pos_iff.mp hϖ0))]
  refine NormedAddGroup.nhds_zero_basis_norm_lt.to_hasBasis
    (fun ε hε ↦ ?_) (fun n _ ↦ ?_)
  · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hϖ1
    exact ⟨n, trivial, fun x hx ↦ lt_of_le_of_lt ((hball n).subset hx) hn⟩
  · exact ⟨‖algebraMap O (WithVal v) ϖ‖ ^ (n + 1), pow_pos hϖ0 (n + 1), fun x hx ↦
      (hball n).symm.subset (le_trans (le_of_lt hx)
        (pow_le_pow_of_le_one hϖ0.le hϖ1.le n.le_succ))⟩

include ϖ in
/-- The valued fraction field `WithVal (ValuationRing.valuation O K)` of a complete rank-one
valuation base is complete. -/
theorem completeSpace_withVal : CompleteSpace (WithVal (ValuationRing.valuation O K)) := by
  have : IsLocalization.Away ϖ K := isLocalization_away ϖ K
  exact completeSpace_of_hasBasis (hasBasis_nhds_zero_withVal ϖ K)
    (mem_nonZeroDivisors_of_ne_zero (ne_zero (O := O) (ϖ := ϖ)))

omit [TopologicalSpace O] in
variable (O) in
/-- The canonical ring isomorphism from `O` to the valuation subring `(Valued.v).integer` of
`WithVal (ValuationRing.valuation O K)`. -/
noncomputable def equivIntegerWithVal :
    O ≃+* (Valued.v : Valuation (WithVal (ValuationRing.valuation O K)) _).integer :=
  RingEquiv.ofBijective
    ({ toFun a := ⟨algebraMap O _ a,
         (Valuation.mem_integer_iff _ _).mpr ((ValuationRing.integers O K).map_le_one a)⟩
       map_one' := Subtype.ext (map_one _)
       map_mul' _ _ := Subtype.ext (map_mul _ _ _)
       map_zero' := Subtype.ext (map_zero _)
       map_add' _ _ := Subtype.ext (map_add _ _ _) } :
      O →+* (Valued.v : Valuation (WithVal (ValuationRing.valuation O K)) _).integer)
    ⟨fun _ _ h ↦
      WithVal.algebraMap_right_injective _ (IsFractionRing.injective O K) (congrArg Subtype.val h),
     fun ⟨x, hx⟩ ↦ by
      obtain ⟨a, ha⟩ := (ValuationRing.integers O K).exists_of_le_one (r := x.ofVal) hx
      exact ⟨a, Subtype.ext (WithVal.ofVal_injective _ ha)⟩⟩

omit [TopologicalSpace O] in
@[simp]
theorem coe_equivIntegerWithVal (a : O) :
    ((equivIntegerWithVal O K a :
      (Valued.v : Valuation (WithVal (ValuationRing.valuation O K)) _).integer) :
        WithVal (ValuationRing.valuation O K)) =
      algebraMap O (WithVal (ValuationRing.valuation O K)) a := by
  rw [equivIntegerWithVal]
  rfl

include ϖ in
/-- `equivIntegerWithVal` is continuous from the `ϖ`-adic topology on `O` to the valuation
topology on `(Valued.v).integer`. -/
theorem continuous_equivIntegerWithVal : Continuous (equivIntegerWithVal O K) := by
  have : NonarchimedeanRing O := nonarchimedeanRing ϖ
  refine continuous_of_continuousAt_zero (equivIntegerWithVal O K).toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, nhds_subtype_eq_comap, tendsto_comap_iff]
  refine ((isAdic (O := O) (ϖ := ϖ)).hasBasis_nhds_zero.tendsto_iff
    (hasBasis_nhds_zero_withVal ϖ K)).mpr fun n _ ↦ ⟨n, trivial, fun a ha ↦ ?_⟩
  rw [Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton] at ha
  obtain ⟨b, rfl⟩ := ha
  exact mem_awayNhd.mpr ⟨b, rfl⟩

include ϖ in
/-- The inverse of `equivIntegerWithVal` is continuous from the valuation topology on
`(Valued.v).integer` to the `ϖ`-adic topology on `O`. -/
theorem continuous_equivIntegerWithVal_symm : Continuous (equivIntegerWithVal O K).symm := by
  have : NonarchimedeanRing O := nonarchimedeanRing ϖ
  refine continuous_of_continuousAt_zero (equivIntegerWithVal O K).symm.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero, nhds_subtype_eq_comap]
  refine (((hasBasis_nhds_zero_withVal ϖ K).comap Subtype.val).tendsto_iff
    (isAdic (O := O) (ϖ := ϖ)).hasBasis_nhds_zero).mpr fun n _ ↦ ⟨n, trivial, fun x hx ↦ ?_⟩
  obtain ⟨b, hb⟩ := mem_awayNhd.mp hx
  have hval : algebraMap O (WithVal (ValuationRing.valuation O K))
      ((equivIntegerWithVal O K).symm x) = (x : WithVal (ValuationRing.valuation O K)) := by
    rw [← coe_equivIntegerWithVal, RingEquiv.apply_symm_apply]
  have heq : (equivIntegerWithVal O K).symm x = ϖ ^ n * b :=
    WithVal.algebraMap_right_injective _ (IsFractionRing.injective O K) (hval.trans hb.symm)
  rw [SetLike.mem_coe, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ⟨b, heq⟩

end FractionField

end TauCeti.Huber.IsCompleteRankOneBase
