/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
public import TauCeti.NumberTheory.LocalField.Uniformizer
import TauCeti.NumberTheory.LocalField.UnitFiltration.Pow.Basic
import TauCeti.NumberTheory.LocalField.UnitsDecomposition
import TauCeti.RingTheory.Valuation.NontrivialComap
import TauCeti.RingTheory.Valuation.ValuativeRel.Discrete
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# Automatic valuation compatibility on extensions of a nonarchimedean local field

Let `K` be a nonarchimedean local field and let `R` be a ring carrying a discrete rank-at-most-one
valuative relation (`[ValuativeRel.IsDiscrete R] [ValuativeRel.IsRankLeOne R]`). Every ring
homomorphism `f : K →+* R` sends the units of `𝒪[K]` to elements of valuation `1` in `R`: if `q` is
the cardinality of the residue field `𝓀[K]` and `ℓ` is a prime exceeding `ringChar 𝓀[K]`, then
`(q - 1)`-st powers of units lie in `U(K, 1)`, where `ℓ ^ k`-th roots exist for every `k : ℕ`
(`TauCeti.map_powMonoidHom_unitFiltration_succ_of_isUnit`), and a discrete archimedean value group
contains no nontrivial `ℓ ^ ∞`-divisible values
(`ValuativeRel.valuation_eq_one_of_pow_forall_exists_pow_pow_eq`).

Writing every `x ∈ Kˣ` as a unit times a power of a uniformizer `ϖ` expresses `valuation R (f x)` as
`valuation R (f ϖ) ^ v_K(x)`. Since `1 + ϖ` is a unit of `𝒪[K]`, ultrametricity rules out
`1 < valuation R (f ϖ)`, so `f` maps `𝒪[K]` into the valuation subring of `R` unconditionally, and
the pullback `(valuation R).comap f` is either trivial (when `valuation R (f ϖ) = 1`) or equivalent
to `valuation K` (when `valuation R (f ϖ) < 1`).

Three rigidity statements follow without any continuity assumption:

* **Uniqueness on `K`** (`TauCeti.valuativeRel_eq_of_isDiscrete_of_isRankLeOne`): `K` admits a
  unique nontrivial discrete rank-at-most-one valuative relation.
* **Automatic compatibility of integral and algebraic extensions**
  (`ValuativeExtension.of_isIntegral`): when `R` is an integral `K`-algebra and the valuative
  relation of `R` is nontrivial, its restriction to `K` is nontrivial
  (`Valuation.isNontrivial_comap_algebraMap`), so `ValuativeExtension K R` holds automatically.
  Over a field `K`, algebraic extensions (`Algebra.IsAlgebraic K R`) and finite extensions
  (`Module.Finite K R`) are integral by typeclass inference, and every nonarchimedean local field
  satisfies `IsDiscrete`, `IsRankLeOne`, and `IsNontrivial`, so any algebraic algebra structure
  between nonarchimedean local fields is automatically compatible and continuous.
* **Identification with the spectral valuation and topology**
  (`TauCeti.algebraicExtensionValuativeRel_eq_of_isDiscrete`,
  `TauCeti.algebraicExtensionNormedFieldTopology_eq_of_isDiscrete`): on an algebraic extension
  `M/K`, any nontrivial discrete rank-at-most-one valuative relation coincides with
  `algebraicExtensionValuativeRel K M`, and its valuative topology coincides with
  `algebraicExtensionNormedFieldTopology K M`.

## Main results

* `RingHom.valuation_map_eq_one_of_valuation_eq_one`: `f : K →+* R` sends elements of valuation `1`
  in `K` to elements of valuation `1` in `R`.
* `RingHom.valuation_map_eq_zpow_toAdd_normalizedValuation`: for a uniformizer `ϖ` of `K` and
  `x : Kˣ`, `valuation R (f x) = valuation R (f ϖ) ^ (normalizedValuation K x).toAdd`.
* `RingHom.valuation_map_le_one_of_valuation_le_one`: `f : K →+* R` sends elements of valuation at
  most `1` in `K` to elements of valuation at most `1` in `R`.
* `RingHom.isEquiv_comap_valuation_iff_isNontrivial`: `(valuation R).comap f` is equivalent to
  `valuation K` if and only if it is nontrivial.
* `RingHom.isEquiv_comap_valuation_of_surjective` and `RingHom.map_vle_map_iff_of_surjective`: a
  surjective homomorphism into a nontrivial discrete rank-at-most-one valued ring preserves and
  reflects the valuative relation.
* `TauCeti.valuativeRel_eq_of_isDiscrete_of_isRankLeOne`: a nonarchimedean local field carries a
  unique nontrivial discrete rank-at-most-one valuative relation.
* `ValuativeExtension.of_isIntegral`: every integral algebra over `K` carrying a nontrivial discrete
  rank-at-most-one valuative relation is a `ValuativeExtension` of `K`.
* `TauCeti.algebraicExtensionValuativeRel_eq_of_isDiscrete`,
  `TauCeti.algebraicExtensionNormedFieldTopology_eq_of_isDiscrete`, and
  `TauCeti.continuous_algebraMap_of_isAlgebraic`: automatic agreement with the spectral valuation
  and topology and continuity of `algebraMap K M` on algebraic extensions.

## Implementation notes

`ValuativeExtension.of_isIntegral` is a `theorem` rather than a global `instance`, matching
`ValuativeExtension.trans` and `ValuativeExtension.of_continuous_algebraMap`, because
`TopologicalSpace K` does not appear in the target `ValuativeExtension K R` and would leave an
undetermined metavariable during backward typeclass search.

## References

* F. K. Schmidt, *Mehrfach perfekte Körper*, Math. Ann. 108 (1933), 1–25.
* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005], Corollary 4.1.4.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4.
-/

public section
noncomputable section

open ValuativeRel TauCeti

section RingHom

variable {K R : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Ring R] [ValuativeRel R] [IsDiscrete R] [IsRankLeOne R]

namespace RingHom

/-- **Units of `𝒪[K]` have valuation `1` under any homomorphism into a discrete rank-at-most-one
valued ring.** Raising `u ∈ U(K, 0)` to `#𝓀[K] - 1` lands in `U(K, 1)`, where `ℓ ^ k`-th roots exist
for any prime `ℓ > ringChar 𝓀[K]`. -/
theorem valuation_map_eq_one_of_valuation_eq_one (f : K →+* R) {x : K} (hx : valuation K x = 1) :
    valuation R (f x) = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  let u : Kˣ := Units.mk0 x hx0
  have hu0 : u ∈ unitFiltration K 0 := (mem_unitFiltration_zero u).2 hx
  have hq : Nat.card 𝓀[K] - 1 ≠ 0 := Nat.sub_ne_zero_of_lt (Finite.one_lt_card (α := 𝓀[K]))
  have hu1 : u ^ (Nat.card 𝓀[K] - 1) ∈ unitFiltration K 1 :=
    relIndex_unitFiltration_one_zero (K := K) ▸ (unitFiltration K 1).pow_relIndex_mem hu0
  -- Choose a prime `ℓ` strictly above the residue characteristic so `ℓ` is invertible in `𝒪[K]`.
  obtain ⟨ℓ, hℓgt, hℓ⟩ := Nat.exists_infinite_primes (ringChar 𝓀[K] + 1)
  have hℓunit : IsUnit (ℓ : 𝒪[K]) :=
    IsLocalRing.isUnit_natCast_iff_not_dvd.2 fun hdvd ↦ by
      have := (hℓ.dvd_iff_eq (CharP.prime_ringChar 𝓀[K]).ne_one).1 hdvd
      omega
  have hfv0 : valuation R (f x) ≠ 0 := (((Units.isUnit u).map f).map (valuation R)).ne_zero
  refine valuation_eq_one_of_pow_forall_exists_pow_pow_eq hfv0 hq hℓ.two_le fun k ↦ ?_
  have hpow_unit : IsUnit ((ℓ ^ k : ℕ) : 𝒪[K]) := by
    rw [Nat.cast_pow]
    exact hℓunit.pow k
  have hmem : u ^ (Nat.card 𝓀[K] - 1) ∈ (unitFiltration K 1).map (powMonoidHom (ℓ ^ k)) := by
    rwa [map_powMonoidHom_unitFiltration_succ_of_isUnit hpow_unit 0]
  obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 hmem
  refine ⟨f y, ?_⟩
  simpa only [u, powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, map_pow]
    using congrArg f (congrArg Units.val hy)

/-- For a uniformizer `ϖ` of `K` and any `x : Kˣ`, the valuation of `f x` in `R` is the normalized
valuation power of `valuation R (f ϖ)`. -/
theorem valuation_map_eq_zpow_toAdd_normalizedValuation (f : K →+* R) {ϖ : Kˣ}
    (hϖ : IsUniformizer K ϖ) (x : Kˣ) :
    valuation R (f x) = valuation R (f ϖ) ^ (normalizedValuation K x).toAdd := by
  set n := (normalizedValuation K x).toAdd
  set u : Kˣ := x * ϖ ^ (-n)
  have hu : u ∈ unitFiltration K 0 :=
    mul_zpow_neg_mem_unitFiltration_zero ((isUniformizer_def ϖ).1 hϖ) x
  have hx : x = u * ϖ ^ n := by
    rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  let φ : Kˣ →* (ValueGroupWithZero R)ˣ :=
    (Units.map (valuation R).toMonoidHom).comp (Units.map f.toMonoidHom)
  have hφ : φ x = φ u * φ ϖ ^ n := by rw [hx, map_mul, map_zpow]
  have hval : valuation R (f x) = valuation R (f u) * valuation R (f ϖ) ^ n := by
    simpa [φ] using congrArg Units.val hφ
  rw [hval, f.valuation_map_eq_one_of_valuation_eq_one ((mem_unitFiltration_zero u).1 hu), one_mul]

/-- **Integers of `K` map into the valuation subring of `R`** under any homomorphism into a discrete
rank-at-most-one valued ring: for a uniformizer `ϖ`, `1 + ϖ` is a unit of `𝒪[K]`, which prevents
`1 < valuation R (f ϖ)`. -/
theorem valuation_map_le_one_of_valuation_le_one (f : K →+* R) {x : K} (hx : valuation K x ≤ 1) :
    valuation R (f x) ≤ 1 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer K
  obtain ⟨π, hπ, hπϖ⟩ := (isUniformizer_iff_exists_irreducible K ϖ).1 hϖ
  have hϖK1 : valuation K (ϖ : K) < 1 := hπϖ ▸ Valuation.integer.v_irreducible_lt_one hπ
  -- If `1 < valuation R (f ϖ)`, ultrametricity gives `valuation R (1 + f ϖ) = valuation R (f ϖ)`,
  -- contradicting `1 + ϖ ∈ 𝒪[K]ˣ`.
  have hϖR_le : valuation R (f ϖ) ≤ 1 := by
    by_contra! hgt
    have h1add : valuation K (1 + (ϖ : K)) = 1 := (valuation K).map_one_add_of_lt hϖK1
    have hf1add : valuation R (1 + f ϖ) = 1 := by
      simpa only [map_add, map_one] using f.valuation_map_eq_one_of_valuation_eq_one h1add
    have hlt : valuation R (1 : R) < valuation R (f ϖ) := by rwa [map_one]
    exact hgt.ne' ((valuation R).map_add_eq_of_lt_right hlt ▸ hf1add)
  let ux : Kˣ := Units.mk0 x hx0
  have hn : 0 ≤ (normalizedValuation K ux).toAdd := by
    have h1 : (normalizedValuation K (1 : Kˣ)).toAdd ≤ (normalizedValuation K ux).toAdd :=
      (toAdd_normalizedValuation_le_iff_valuation_le 1 ux).2 (by simpa [ux] using hx)
    simpa using h1
  have hϖR0 : 0 < valuation R (f ϖ) :=
    zero_lt_iff.2 (((ϖ.isUnit.map f).map (valuation R)).ne_zero)
  have hval := f.valuation_map_eq_zpow_toAdd_normalizedValuation hϖ ux
  rw [Units.val_mk0] at hval
  rw [hval]
  exact zpow_le_one₀ hϖR0 hϖR_le hn

/-- **Dichotomy for discrete rank-at-most-one valuations on a nonarchimedean local field.** The
pullback of `valuation R` along `f : K →+* R` is equivalent to `valuation K` if and only if it is
nontrivial. -/
theorem isEquiv_comap_valuation_iff_isNontrivial (f : K →+* R) :
    ((valuation R).comap f).IsEquiv (valuation K) ↔ ((valuation R).comap f).IsNontrivial := by
  constructor
  · intro heq
    obtain ⟨x, hx0, hx1⟩ := (inferInstance : (valuation K).IsNontrivial).exists_val_nontrivial
    exact ⟨x, heq.eq_zero.not.2 hx0, heq.eq_one_iff_eq_one.not.2 hx1⟩
  · intro hnt
    obtain ⟨ϖ, hϖ⟩ := exists_isUniformizer K
    obtain ⟨π, hπ, hπϖ⟩ := (isUniformizer_iff_exists_irreducible K ϖ).1 hϖ
    have hϖK1 : valuation K (ϖ : K) < 1 := hπϖ ▸ Valuation.integer.v_irreducible_lt_one hπ
    have hϖR0 : 0 < valuation R (f ϖ) :=
      zero_lt_iff.2 (((ϖ.isUnit.map f).map (valuation R)).ne_zero)
    have hϖR1 : valuation R (f ϖ) < 1 := by
      refine lt_of_le_of_ne (f.valuation_map_le_one_of_valuation_le_one hϖK1.le) fun h1 ↦ ?_
      obtain ⟨x, hx0, hx1⟩ := hnt.exists_val_nontrivial
      have hx0' : x ≠ 0 := by rintro rfl; simp at hx0
      have := f.valuation_map_eq_zpow_toAdd_normalizedValuation hϖ (Units.mk0 x hx0')
      rw [Units.val_mk0, h1, one_zpow] at this
      exact hx1 this
    refine Valuation.isEquiv_iff_val_le_one.2 fun {x} ↦
      ⟨fun hx ↦ ?_, f.valuation_map_le_one_of_valuation_le_one⟩
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    let ux : Kˣ := Units.mk0 x hx0
    rw [Valuation.comap_apply] at hx
    have hn : 0 ≤ (normalizedValuation K ux).toAdd := by
      rw [← zpow_le_one_iff_right_of_lt_one₀ hϖR0 hϖR1,
        ← f.valuation_map_eq_zpow_toAdd_normalizedValuation hϖ ux]
      exact hx
    have hle := (toAdd_normalizedValuation_le_iff_valuation_le 1 ux).1 (by simpa using hn)
    simpa [ux] using hle

/-- A surjective homomorphism from `K` to a ring carrying a nontrivial discrete rank-at-most-one
valuative relation pulls back the valuation of `R` to the valuation class of `K`. -/
theorem isEquiv_comap_valuation_of_surjective [IsNontrivial R] (f : K →+* R)
    (hf : Function.Surjective f) :
    ((valuation R).comap f).IsEquiv (valuation K) := by
  refine f.isEquiv_comap_valuation_iff_isNontrivial.2 ?_
  obtain ⟨y, hy0, hy1⟩ := (inferInstance : (valuation R).IsNontrivial).exists_val_nontrivial
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨x, hy0, hy1⟩

/-- A surjective homomorphism from `K` to a ring carrying a nontrivial discrete rank-at-most-one
valuative relation preserves and reflects the valuative relation, with no continuity assumption. -/
theorem map_vle_map_iff_of_surjective [IsNontrivial R] (f : K →+* R) (hf : Function.Surjective f)
    (x y : K) : f x ≤ᵥ f y ↔ x ≤ᵥ y := by
  rw [(valuation R).vle_iff_le, (valuation K).vle_iff_le]
  exact f.isEquiv_comap_valuation_of_surjective hf x y

end RingHom

end RingHom

/-- **Uniqueness of the discrete rank-one valuative relation on a nonarchimedean local field.** Any
nontrivial discrete rank-at-most-one valuative relation on `K` coincides with its local-field
valuative relation. -/
theorem TauCeti.valuativeRel_eq_of_isDiscrete_of_isRankLeOne (K : Type*) [Field K]
    [v₁ : ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (v₂ : ValuativeRel K) [letI := v₂; IsDiscrete K] [letI := v₂; IsRankLeOne K]
    [letI := v₂; IsNontrivial K] :
    v₂ = v₁ :=
  ValuativeRel.ext <| funext₂ fun x y ↦ propext <|
    @RingHom.map_vle_map_iff_of_surjective K K _ v₁ _ _ _ v₂ _ _ _ (.id K)
      Function.surjective_id x y

/-- **Automatic valuation compatibility along integral extensions of a nonarchimedean local field.**
Every integral `K`-algebra carrying a nontrivial discrete rank-at-most-one valuative relation is a
`ValuativeExtension` of `K`. Since `K` is a field, this applies by typeclass inference to every
algebraic extension (`Algebra.IsAlgebraic K R`) and every finite extension (`Module.Finite K R`), in
particular whenever `R` is itself a nonarchimedean local field. -/
theorem ValuativeExtension.of_isIntegral (K R : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Ring R] [ValuativeRel R]
    [IsDiscrete R] [IsRankLeOne R] [IsNontrivial R] [Algebra K R] [Algebra.IsIntegral K R] :
    ValuativeExtension K R := by
  have hnt : ((valuation R).comap (algebraMap K R)).IsNontrivial :=
    (valuation R).isNontrivial_comap_algebraMap
  have heq := (algebraMap K R).isEquiv_comap_valuation_iff_isNontrivial.2 hnt
  exact ⟨fun {a b} ↦ (valuation R).vle_iff_le.trans ((heq a b).trans (valuation K).vle_iff_le.symm)⟩

namespace TauCeti

variable (K M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field M] [Algebra K M] [Algebra.IsAlgebraic K M]
  [ValuativeRel M] [IsDiscrete M] [IsRankLeOne M] [IsNontrivial M]

/-- On an algebraic extension `M` of a nonarchimedean local field `K`, any nontrivial discrete
rank-at-most-one valuative relation coincides with the spectral valuative relation
`algebraicExtensionValuativeRel K M`, without assuming compatibility over `K` in advance. -/
theorem algebraicExtensionValuativeRel_eq_of_isDiscrete :
    algebraicExtensionValuativeRel K M = ‹ValuativeRel M› := by
  have := ValuativeExtension.of_isIntegral K M
  exact algebraicExtensionValuativeRel_eq K M

/-- On an algebraic extension `M` of a nonarchimedean local field `K`, the valuative topology of any
nontrivial discrete rank-at-most-one valuative relation coincides with
`algebraicExtensionNormedFieldTopology K M`, without assuming compatibility over `K` in advance. -/
theorem algebraicExtensionNormedFieldTopology_eq_of_isDiscrete [TopologicalSpace M]
    [IsValuativeTopology M] :
    algebraicExtensionNormedFieldTopology K M = ‹TopologicalSpace M› := by
  have := ValuativeExtension.of_isIntegral K M
  exact algebraicExtensionNormedFieldTopology_eq K M

/-- The structure map `algebraMap K M` into an algebraic extension carrying the valuative topology
of a nontrivial discrete rank-at-most-one valuative relation is automatically continuous. -/
theorem continuous_algebraMap_of_isAlgebraic [TopologicalSpace M] [IsValuativeTopology M] :
    Continuous (algebraMap K M) := by
  have := ValuativeExtension.of_isIntegral K M
  exact continuous_algebraMap_of_valuativeExtension K M

end TauCeti
