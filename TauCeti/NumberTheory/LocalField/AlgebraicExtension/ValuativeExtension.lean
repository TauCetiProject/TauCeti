/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.AlgebraicExtension.Basic
public import TauCeti.NumberTheory.LocalField.Henselian
public import TauCeti.NumberTheory.LocalField.Uniformizer
import TauCeti.Algebra.CharP.LocalRing
import TauCeti.NumberTheory.LocalField.UnitsDecomposition
import TauCeti.RingTheory.Valuation.NontrivialComap
import TauCeti.RingTheory.Valuation.ValuativeRel.Discrete
import TauCeti.Topology.Algebra.ValuativeRel.ContinuousRingHom

/-!
# Automatic valuation compatibility on extensions of a Henselian valued field

Let `K` be a nontrivial Henselian valued field (`[HenselianRing 𝒪[K] 𝓂[K]] [IsNontrivial K]`) and
let `R` be a ring carrying a discrete archimedean valuative relation
(`[ValuativeRel.IsDiscrete R] [MulArchimedean (ValueGroupWithZero R)]`, in particular whenever
`ValuativeRel.IsRankLeOne R` holds). Every ring homomorphism `f : K →+* R` sends `𝒪[K]` into the
valuation subring of `R`: for any `m ∈ 𝓂[K]`, Hensel's lemma
(`TauCeti.HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem`) extracts `k`-th roots of
`1 + m` in `𝒪[K]` for every prime `k` exceeding `ringChar 𝓀[K]`, so divisibility rigidity in `R`
(`ValuativeRel.valuation_eq_one_of_forall_exists_le_pow_eq`) forces `valuation R (f (1 + m)) = 1`
and hence `valuation R (f m) ≤ 1` by ultrametricity. Multiplying any `x ∈ 𝒪[K]` by a nonzero
element `m ∈ 𝓂[K]` gives `x ^ n * m ∈ 𝓂[K]` for every `n : ℕ`, so the archimedean property of
`ValueGroupWithZero R` forces `valuation R (f x) ≤ 1`, and therefore `valuation R (f x) = 1` when
`valuation K x = 1`.

When `ValueGroupWithZero K` is also archimedean (`[MulArchimedean (ValueGroupWithZero K)]`), the
pullback `(valuation R).comap f` is either trivial or equivalent to `valuation K`. Four rigidity
statements follow without any continuity assumption, covering nonarchimedean local fields as well as
non-local Henselian fields such as `Breve E` and completions of rank-one valued fields:

* **Uniqueness on `K`** (`TauCeti.valuativeRel_eq_of_isDiscrete_of_mulArchimedean`): `K` admits a
  unique nontrivial discrete archimedean valuative relation.
* **Automatic compatibility of integral and algebraic extensions**
  (`ValuativeExtension.of_isIntegral`): when `R` is an integral `K`-algebra and the valuative
  relation of `R` is nontrivial, its restriction to `K` is nontrivial
  (`Valuation.isNontrivial_comap_algebraMap`), so `ValuativeExtension K R` holds automatically.
  Over a field `K`, algebraic extensions (`Algebra.IsAlgebraic K R`) and finite extensions
  (`Module.Finite K R`) are integral by typeclass inference, and every nonarchimedean local field
  satisfies `IsDiscrete`, `MulArchimedean (ValueGroupWithZero _)`, `IsNontrivial`, and
  `HenselianRing 𝒪[_] 𝓂[_]` (via `TauCeti.henselianLocalRing_integer`), so any algebraic algebra
  structure between nonarchimedean local fields is automatically compatible and continuous.
* **Automatic continuity on algebraic extensions** (`TauCeti.continuous_algebraMap_of_isDiscrete`):
  when `K` and an algebraic extension `M/K` carry valuative topologies and `M` has a nontrivial
  discrete archimedean valuative relation, `algebraMap K M` is continuous.
* **Identification with the spectral valuation and topology over a local field**
  (`TauCeti.algebraicExtensionValuativeRel_eq_of_isDiscrete`,
  `TauCeti.algebraicExtensionNormedFieldTopology_eq_of_isDiscrete`): on an algebraic extension
  `M/K` of a nonarchimedean local field `K`, any nontrivial discrete archimedean valuative relation
  coincides with `algebraicExtensionValuativeRel K M`, and its valuative topology coincides with
  `algebraicExtensionNormedFieldTopology K M`.

## Main results

* `RingHom.valuation_map_le_one_of_valuation_le_one`: for a nontrivial Henselian valued field `K`
  and a discrete archimedean valued ring `R`, `f : K →+* R` sends elements of valuation at most `1`
  in `K` to elements of valuation at most `1` in `R`.
* `RingHom.valuation_map_eq_one_of_valuation_eq_one`: under the same hypotheses, `f : K →+* R`
  sends elements of valuation `1` in `K` to elements of valuation `1` in `R`.
* `RingHom.isEquiv_comap_valuation_iff_isNontrivial`: when `ValueGroupWithZero K` is also
  archimedean, `(valuation R).comap f` is equivalent to `valuation K` if and only if it is
  nontrivial.
* `RingHom.isEquiv_comap_valuation_of_surjective` and `RingHom.map_vle_map_iff_of_surjective`: a
  surjective homomorphism from a nontrivial archimedean Henselian valued field into a nontrivial
  discrete archimedean valued ring preserves and reflects the valuative relation.
* `RingHom.valuation_map_eq_zpow_toAdd_normalizedValuation`: for a uniformizer `ϖ` of a
  nonarchimedean local field `K` and `x : Kˣ`,
  `valuation R (f x) = valuation R (f ϖ) ^ (normalizedValuation K x).toAdd`.
* `TauCeti.valuativeRel_eq_of_isDiscrete_of_mulArchimedean`: a nontrivial archimedean Henselian
  valued field carries a unique nontrivial discrete archimedean valuative relation.
* `ValuativeExtension.of_isIntegral`: every integral algebra over a nontrivial archimedean
  Henselian valued field `K` carrying a nontrivial discrete archimedean valuative relation is a
  `ValuativeExtension` of `K`.
* `TauCeti.continuous_algebraMap_of_isDiscrete`: automatic continuity of `algebraMap K M` for an
  algebraic extension of a nontrivial archimedean Henselian valued field `K` when `M` carries the
  valuative topology of a nontrivial discrete archimedean valuative relation.
* `TauCeti.algebraicExtensionValuativeRel_eq_of_isDiscrete` and
  `TauCeti.algebraicExtensionNormedFieldTopology_eq_of_isDiscrete`: automatic agreement with the
  spectral valuation and topology on algebraic extensions of a nonarchimedean local field.

## Implementation notes

`ValuativeExtension.of_isIntegral` is a `theorem` rather than a global `instance`, matching
`ValuativeExtension.trans` and `ValuativeExtension.of_continuous_algebraMap`, to avoid firing global
backward typeclass search for `Field K`, `HenselianRing 𝒪[K] 𝓂[K]`, `IsDiscrete R`,
`MulArchimedean`, and `Algebra.IsIntegral K R` on every `ValuativeExtension` query.

## References

* F. K. Schmidt, *Mehrfach perfekte Körper*, Math. Ann. 108 (1933), 1–25.
* [A. J. Engler and A. Prestel, *Valued Fields*][engler2005], Corollary 4.1.4.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4.
-/

public section
noncomputable section

open ValuativeRel TauCeti

section RingHom

variable {K R : Type*} [Field K] [ValuativeRel K] [HenselianRing 𝒪[K] 𝓂[K]]
  [Ring R] [ValuativeRel R] [IsDiscrete R] [MulArchimedean (ValueGroupWithZero R)]

namespace RingHom

/-- Every homomorphism from a Henselian valued field `K` into a discrete archimedean valued ring
`R` sends elements of valuation strictly less than `1` to elements of valuation at most `1`. -/
private theorem valuation_map_le_one_of_valuation_lt_one (f : K →+* R) {m : K}
    (hm : valuation K m < 1) :
    valuation R (f m) ≤ 1 := by
  have h1m : valuation K (1 + m) = 1 := (valuation K).map_one_add_of_lt hm
  have h1m0 : 1 + m ≠ 0 := by rintro h; simp [h] at h1m
  have hf1m0 : valuation R (f (1 + m)) ≠ 0 :=
    (((IsUnit.mk0 (1 + m) h1m0).map f).map (valuation R)).ne_zero
  have hm' : (⟨m, hm.le⟩ : 𝒪[K]) ∈ 𝓂[K] :=
    (IsLocalRing.mem_maximalIdeal _).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 hm)
  have hf1m : valuation R (f (1 + m)) = 1 := by
    refine valuation_eq_one_of_forall_exists_le_pow_eq hf1m0 fun n ↦ ?_
    obtain ⟨k, hk, hkprime⟩ := Nat.exists_infinite_primes (max n (ringChar 𝓀[K] + 1))
    have hkunit : IsUnit (k : 𝒪[K]) :=
      IsLocalRing.isUnit_natCast_iff_not_dvd.2 fun hdvd ↦ by
        have := (hkprime.dvd_iff_eq CharP.ringChar_ne_one).1 hdvd
        omega
    obtain ⟨a, ha, -⟩ := TauCeti.HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem
      (I := 𝓂[K]) (J := 𝓂[K]) le_rfl hkunit (w := 1 + ⟨m, hm.le⟩) (by simpa using hm')
    refine ⟨k, (le_max_left _ _).trans hk, f (a : K), ?_⟩
    simpa [map_pow] using congrArg f (congrArg Subtype.val ha)
  by_contra! hgt
  have hlt : valuation R (1 : R) < valuation R (f m) := by rwa [map_one]
  have hadd : valuation R (1 + f m) = 1 := by simpa only [map_add, map_one] using hf1m
  exact hgt.ne' ((valuation R).map_add_eq_of_lt_right hlt ▸ hadd)

/-- **Integers of a nontrivial Henselian valued field map into the valuation subring of `R`** under
any homomorphism into a discrete archimedean valued ring:
`valuation K x ≤ 1 → valuation R (f x) ≤ 1`. -/
theorem valuation_map_le_one_of_valuation_le_one [IsNontrivial K] (f : K →+* R) {x : K}
    (hx : valuation K x ≤ 1) :
    valuation R (f x) ≤ 1 := by
  by_contra! hgt
  obtain ⟨γ, hγ0, hγ1⟩ := IsNontrivial.exists_lt_one (R := K)
  obtain ⟨m, rfl⟩ := valuation_surjective γ
  have hm0 : m ≠ 0 := by rintro rfl; simp at hγ0
  have hfm0 : valuation R (f m) ≠ 0 := (((IsUnit.mk0 m hm0).map f).map (valuation R)).ne_zero
  obtain ⟨n, hn⟩ := MulArchimedean.arch (valuation R (f m))⁻¹ hgt
  have hlt : valuation K (x ^ (n + 1) * m) < 1 := by
    rw [map_mul, map_pow]
    exact (mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hx)).trans_lt hγ1
  have hle := f.valuation_map_le_one_of_valuation_lt_one hlt
  rw [map_mul, map_pow, map_mul, map_pow] at hle
  have hgt' : 1 < valuation R (f x) ^ (n + 1) * valuation R (f m) :=
    calc (1 : ValueGroupWithZero R)
        = (valuation R (f m))⁻¹ * valuation R (f m) := (inv_mul_cancel₀ hfm0).symm
      _ < valuation R (f x) ^ (n + 1) * valuation R (f m) :=
          mul_lt_mul_of_pos_right (hn.trans_lt (pow_lt_pow_right₀ hgt n.lt_succ_self))
            (zero_lt_iff.2 hfm0)
  exact hgt'.not_ge hle

/-- **Units of `𝒪[K]` have valuation `1` under any homomorphism from a nontrivial Henselian valued
field `K` into a discrete archimedean valued ring `R`.** Every `f : K →+* R` sends elements of
valuation `1` in `K` to elements of valuation `1` in `R`. -/
theorem valuation_map_eq_one_of_valuation_eq_one [IsNontrivial K] (f : K →+* R) {x : K}
    (hx : valuation K x = 1) :
    valuation R (f x) = 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hle : valuation R (f x) ≤ 1 := f.valuation_map_le_one_of_valuation_le_one hx.le
  have hinv : valuation R (f x⁻¹) ≤ 1 :=
    f.valuation_map_le_one_of_valuation_le_one (by rw [map_inv₀, hx, inv_one])
  refine le_antisymm hle ?_
  have hmul : valuation R (f x) * valuation R (f x⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, map_one]
  simpa [hmul] using mul_le_mul_right hinv (valuation R (f x))

/-- **Dichotomy for discrete archimedean valuations pulled back to a nontrivial archimedean
Henselian valued field.** The pullback of `valuation R` along `f : K →+* R` is equivalent to
`valuation K` if and only if it is nontrivial. -/
theorem isEquiv_comap_valuation_iff_isNontrivial [IsNontrivial K]
    [MulArchimedean (ValueGroupWithZero K)] (f : K →+* R) :
    ((valuation R).comap f).IsEquiv (valuation K) ↔ ((valuation R).comap f).IsNontrivial := by
  refine ⟨fun heq ↦ heq.isNontrivial_iff.2 inferInstance, fun hnt ↦ ?_⟩
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} ↦
    ⟨fun hx ↦ ?_, f.valuation_map_le_one_of_valuation_le_one⟩
  rw [Valuation.comap_apply] at hx
  by_contra! hvx
  have hx0 : x ≠ 0 := by rintro rfl; simp at hvx
  obtain ⟨y, hy⟩ := hnt.exists_one_lt
  obtain ⟨n, hn⟩ := MulArchimedean.arch (valuation K y) hvx
  have hdiv : valuation K (y / x ^ n) ≤ 1 := by
    rw [map_div₀, map_pow, div_le_one₀ (pow_pos (zero_lt_one.trans hvx) n)]
    exact hn
  have hle := f.valuation_map_le_one_of_valuation_le_one hdiv
  have hy_eq : y = y / x ^ n * x ^ n := (div_mul_cancel₀ y (pow_ne_zero n hx0)).symm
  rw [Valuation.comap_apply, hy_eq, map_mul, map_pow, map_mul, map_pow] at hy
  exact hy.not_ge (mul_le_one' hle (pow_le_one' hx n))

/-- A surjective homomorphism from a nontrivial archimedean Henselian valued field `K` to a ring
carrying a nontrivial discrete archimedean valuative relation pulls back the valuation of `R` to the
valuation class of `K`. -/
theorem isEquiv_comap_valuation_of_surjective [IsNontrivial K]
    [MulArchimedean (ValueGroupWithZero K)] [IsNontrivial R] (f : K →+* R)
    (hf : Function.Surjective f) :
    ((valuation R).comap f).IsEquiv (valuation K) := by
  refine f.isEquiv_comap_valuation_iff_isNontrivial.2 ?_
  obtain ⟨y, hy0, hy1⟩ := (inferInstance : (valuation R).IsNontrivial).exists_val_nontrivial
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨x, hy0, hy1⟩

/-- A surjective homomorphism from a nontrivial archimedean Henselian valued field `K` to a ring
carrying a nontrivial discrete archimedean valuative relation preserves and reflects the valuative
relation, with no continuity assumption. -/
theorem map_vle_map_iff_of_surjective [IsNontrivial K] [MulArchimedean (ValueGroupWithZero K)]
    [IsNontrivial R] (f : K →+* R) (hf : Function.Surjective f) (x y : K) :
    f x ≤ᵥ f y ↔ x ≤ᵥ y := by
  rw [(valuation R).vle_iff_le, (valuation K).vle_iff_le]
  exact f.isEquiv_comap_valuation_of_surjective hf x y

end RingHom

end RingHom

section LocalFieldRingHom

variable {K R : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Ring R] [ValuativeRel R] [IsDiscrete R]
  [MulArchimedean (ValueGroupWithZero R)]

/-- For a uniformizer `ϖ` of a nonarchimedean local field `K`, a ring `R` carrying a discrete
archimedean valuative relation, and any `x : Kˣ`, the valuation of `f x` in `R` is the normalized
valuation power of `valuation R (f ϖ)`. -/
theorem RingHom.valuation_map_eq_zpow_toAdd_normalizedValuation (f : K →+* R) {ϖ : Kˣ}
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

end LocalFieldRingHom

/-- **Uniqueness of the discrete archimedean valuative relation on a Henselian rank-one field.** Any
nontrivial discrete archimedean valuative relation on a nontrivial archimedean Henselian valued
field `K` coincides with its Henselian valuative relation. -/
theorem TauCeti.valuativeRel_eq_of_isDiscrete_of_mulArchimedean (K : Type*) [Field K]
    [v₁ : ValuativeRel K] [HenselianRing 𝒪[K] 𝓂[K]] [IsNontrivial K]
    [MulArchimedean (ValueGroupWithZero K)]
    (v₂ : ValuativeRel K) [letI := v₂; IsDiscrete K]
    [letI := v₂; MulArchimedean (ValueGroupWithZero K)] [letI := v₂; IsNontrivial K] :
    v₂ = v₁ :=
  ValuativeRel.ext <| funext₂ fun x y ↦ propext <|
    @RingHom.map_vle_map_iff_of_surjective K K _ v₁ _ _ v₂ _ _ _ _ _ (.id K)
      Function.surjective_id x y

/-- **Automatic valuation compatibility along integral extensions of a Henselian rank-one field.**
Every integral algebra `R` over a nontrivial archimedean Henselian valued field `K` carrying a
nontrivial discrete archimedean valuative relation is a `ValuativeExtension` of `K`. Over a field
`K`, `Algebra.IsAlgebraic K R` and `Module.Finite K R` synthesize `Algebra.IsIntegral K R`; when
`K` or `R` is a nonarchimedean local field, `IsNonarchimedeanLocalField` together with
`TauCeti.henselianLocalRing_integer` discharges the remaining valuation hypotheses. -/
theorem ValuativeExtension.of_isIntegral (K R : Type*) [Field K] [ValuativeRel K]
    [HenselianRing 𝒪[K] 𝓂[K]] [IsNontrivial K] [MulArchimedean (ValueGroupWithZero K)]
    [Ring R] [ValuativeRel R] [IsDiscrete R] [MulArchimedean (ValueGroupWithZero R)]
    [IsNontrivial R] [Algebra K R] [Algebra.IsIntegral K R] :
    ValuativeExtension K R := by
  have hnt : ((valuation R).comap (algebraMap K R)).IsNontrivial :=
    (valuation R).isNontrivial_comap_algebraMap
  have heq := (algebraMap K R).isEquiv_comap_valuation_iff_isNontrivial.2 hnt
  exact ⟨fun {a b} ↦ (valuation R).vle_iff_le.trans ((heq a b).trans (valuation K).vle_iff_le.symm)⟩

namespace TauCeti

/-- For a nontrivial archimedean Henselian valued field `K` with its valuative topology and an
algebraic extension `M` carrying the valuative topology of a nontrivial discrete archimedean
valuative relation, the structure map `algebraMap K M` is automatically continuous. -/
theorem continuous_algebraMap_of_isDiscrete (K M : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsValuativeTopology K] [HenselianRing 𝒪[K] 𝓂[K]] [IsNontrivial K]
    [MulArchimedean (ValueGroupWithZero K)] [Field M] [ValuativeRel M] [IsDiscrete M]
    [MulArchimedean (ValueGroupWithZero M)] [IsNontrivial M] [TopologicalSpace M]
    [IsValuativeTopology M] [Algebra K M] [Algebra.IsAlgebraic K M] :
    Continuous (algebraMap K M) := by
  have := ValuativeExtension.of_isIntegral K M
  exact continuous_algebraMap_of_valuativeExtension K M

section LocalField

variable (K M : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field M] [Algebra K M] [Algebra.IsAlgebraic K M]
  [ValuativeRel M] [IsDiscrete M] [MulArchimedean (ValueGroupWithZero M)] [IsNontrivial M]

/-- On an algebraic extension `M` of a nonarchimedean local field `K`, any nontrivial discrete
archimedean valuative relation coincides with the spectral valuative relation
`algebraicExtensionValuativeRel K M`, without assuming compatibility over `K` in advance. -/
theorem algebraicExtensionValuativeRel_eq_of_isDiscrete :
    algebraicExtensionValuativeRel K M = ‹ValuativeRel M› := by
  have := ValuativeExtension.of_isIntegral K M
  exact algebraicExtensionValuativeRel_eq K M

/-- On an algebraic extension `M` of a nonarchimedean local field `K`, the valuative topology of any
nontrivial discrete archimedean valuative relation coincides with
`algebraicExtensionNormedFieldTopology K M`, without assuming compatibility over `K` in advance. -/
theorem algebraicExtensionNormedFieldTopology_eq_of_isDiscrete [TopologicalSpace M]
    [IsValuativeTopology M] :
    algebraicExtensionNormedFieldTopology K M = ‹TopologicalSpace M› := by
  have := ValuativeExtension.of_isIntegral K M
  exact algebraicExtensionNormedFieldTopology_eq K M

end LocalField

end TauCeti
