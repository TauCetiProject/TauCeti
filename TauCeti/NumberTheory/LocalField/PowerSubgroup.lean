/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NatCastValuation
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Pow
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import TauCeti.GroupTheory.Index.NSmul
import TauCeti.NumberTheory.LocalField.MultiplicativeGroup
import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded

/-!
# The `n`-th power subgroup of a local field

Let `K` be a nonarchimedean local field. This file counts the power classes `Kˣ ⧸ (Kˣ)ⁿ`, where
`(Kˣ)ⁿ` is the range of `powMonoidHom n : Kˣ →* Kˣ`, and studies `(Kˣ)ⁿ` further when `n` is
invertible in `𝒪[K]`, that is, prime to the residue characteristic.

For every `n` with `(n : K) ≠ 0`,

`#(Kˣ ⧸ (Kˣ)ⁿ) = n · #μ_n(K) · q ^ v_K(n)`,

where `μ_n(K)` is the group of `n`-th roots of unity in `K`, `q` is the cardinality of the residue
field and `v_K(n)` is the normalized valuation `natCastValuation K n hn`. In characteristic zero,
for instance for a finite extension of `ℚ_[p]`, this covers every `n ≠ 0`, including multiples of
the residue characteristic. The proof compares the index of the `n`-th powers with the number of
`n`-torsion elements, which is unchanged on passing to a subgroup of finite index
(`Subgroup.index_range_pow_mul_card_ker`). Through the splitting `Kˣ ≅ ℤ × U(K,0)`, the factor `ℤ`
contributes `n`. In `U(K,0)` the `n`-torsion is all of `μ_n(K)`, and the deep subgroup
`U(K, v_K(n) + 1)` has no `n`-torsion and is carried by the `n`-th power map onto
`U(K, 2 v_K(n) + 1)`, of index `q ^ v_K(n)` (`TauCeti.map_powMonoidHom_unitFiltration`).
In particular there are `4` square classes when `2` is a unit of `𝒪[K]`.

When `n` is invertible in `𝒪[K]`, so that `v_K(n) = 0`, the `n`-th power map is an automorphism of
each positive-depth step `U(K,i+1)`, so every principal unit is an `n`-th power. Hence `(Kˣ)ⁿ`
contains an open subgroup and is open, and hence closed, in `Kˣ`. Openness does not follow from
any finiteness of the quotient `Kˣ ⧸ (Kˣ)ⁿ`: a subgroup of finite index in a topological group need
not be open. Since the principal units are exactly the units of `𝒪[K]` that reduce to `1`, a unit
of `𝒪[K]` is then an `n`-th power in `K` precisely when its residue is an `n`-th power in `𝓀[K]`.
At `n = 2` that is the criterion for a unit of `𝒪[K]` to be a square. As a consequence, a subgroup
of `Kˣ` is open as soon as the exponent (for instance, the index) of the quotient by it is
invertible in `𝒪[K]`, since it then contains the power subgroup attached to that exponent.

## Main results

* `TauCeti.card_powerClasses`: `#(Kˣ ⧸ (Kˣ)ⁿ) = n · #μ_n(K) · q ^ v_K(n)` for `(n : K) ≠ 0`.
* `TauCeti.finiteIndex_range_powMonoidHom`: `(Kˣ)ⁿ` has finite index in `Kˣ` for `(n : K) ≠ 0`.
* `TauCeti.map_powMonoidHom_unitFiltration_succ_of_isUnit`: the `n`-th power map carries
  `U(K,i+1)` onto itself.
* `TauCeti.unitFiltration_one_le_range_powMonoidHom_of_isUnit`: every principal unit is an
  `n`-th power, `U(K,1) ≤ (Kˣ)ⁿ`.
* `TauCeti.unitsMap_subtype_mem_range_powMonoidHom_iff` and
  `TauCeti.isSquare_unitsMap_subtype_iff`: a unit of `𝒪[K]` is an `n`-th power, respectively a
  square, in `K` exactly when its residue is one in `𝓀[K]`.
* `TauCeti.isOpen_range_powMonoidHom_of_isUnit` and
  `TauCeti.isClosed_range_powMonoidHom_of_isUnit`: the power subgroup is open and closed.
* `TauCeti.isOpen_of_isUnit_exponent` and `TauCeti.isOpen_of_isUnit_index`: a subgroup of `Kˣ`
  is open when the exponent, or the index, of the quotient by it is invertible in `𝒪[K]`.
* `TauCeti.disjoint_rootsOfUnity_unitFiltration_one_of_isUnit`: no nontrivial `n`-th root of
  unity is a principal unit.
* `TauCeti.powMonoidHom_unitFiltration_succ_bijective_of_isUnit`: the `n`-th power map is a
  bijection of `U(K,i+1)`.
* `TauCeti.card_powerClasses_of_isUnit`: `#(Kˣ ⧸ (Kˣ)ⁿ) = n · #μ_n(K)`.
* `TauCeti.finiteIndex_range_powMonoidHom_of_isUnit`: `(Kˣ)ⁿ` has finite index in `Kˣ`.
* `TauCeti.card_squareClasses_of_isUnit`: `#(Kˣ ⧸ (Kˣ)²) = 4` when `2` is a unit of `𝒪[K]`.

## Implementation notes

The hypothesis `IsUnit (n : 𝒪[K])` already forces `n ≠ 0`, so no separate nonvanishing
assumption is taken. The hypothesis `(n : K) ≠ 0` of the count is needed: in equal
characteristic `p` the quotient `Kˣ ⧸ (Kˣ)ᵖ` is infinite. For the same reason the range of
`powMonoidHom p` is not open in equal characteristic `p`. In characteristic zero `(Kˣ)ⁿ` contains
the open subgroup `U(K, 2 v_K(n) + 1)` for every `n ≠ 0`, by
`TauCeti.map_powMonoidHom_unitFiltration`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §3.
* J. Neukirch, J. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Chapter VII, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- For `n` invertible in `𝒪[K]`, the `n`-th power map carries each positive-depth step
`U(K,i+1)` of the unit filtration onto itself. This is the case `v_K(n) = 0` of
`map_powMonoidHom_unitFiltration`. -/
theorem map_powMonoidHom_unitFiltration_succ_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K]))
    (i : ℕ) :
    (unitFiltration K (i + 1)).map (powMonoidHom n) = unitFiltration K (i + 1) := by
  have hnK := natCast_ne_zero_of_isUnit hn
  have hv := natCastValuation_eq_zero_of_isUnit K hnK hn
  simpa [hv] using map_powMonoidHom_unitFiltration hnK (i := i + 1) fun p hp hpK hpn ↦
    natCastValuation_lt_sub_one_mul_of_dvd_of_lt hnK (hv ▸ i.succ_pos) hp hpK hpn

/-- For `n` invertible in `𝒪[K]`, every principal unit of `K` is an `n`-th power. -/
theorem unitFiltration_one_le_range_powMonoidHom_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    unitFiltration K 1 ≤ (powMonoidHom n : Kˣ →* Kˣ).range :=
  map_powMonoidHom_unitFiltration_succ_of_isUnit hn 0 ▸ Subgroup.map_le_range _ _

/-- **`n`-th powers away from the residue characteristic are detected in the residue field.**
For `n` invertible in `𝒪[K]`, a unit of `𝒪[K]` is an `n`-th power in `K` exactly when its residue
is an `n`-th power in `𝓀[K]`. -/
theorem unitsMap_subtype_mem_range_powMonoidHom_iff {n : ℕ} (hn : IsUnit (n : 𝒪[K]))
    (u : 𝒪[K]ˣ) :
    Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u ∈ (powMonoidHom n : Kˣ →* Kˣ).range ↔
      Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u ∈
        (powMonoidHom n : 𝓀[K]ˣ →* 𝓀[K]ˣ).range := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have hinj : Function.Injective (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K)) :=
    Units.map_injective Subtype.val_injective
  have hmem : Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u ∈ unitFiltration K 0 :=
    (mem_unitFiltration_zero _).mpr
      ((Valuation.integer.integers (valuation K)).valuation_unit u)
  constructor
  · rintro ⟨z, hz⟩
    rw [powMonoidHom_apply] at hz
    -- The value group `Multiplicative ℤ` is torsion-free, so `z` itself has valuation zero.
    have hz0 : z ∈ unitFiltration K 0 := by
      rw [← ker_normalizedValuation, MonoidHom.mem_ker]
      have hpow : normalizedValuation K z ^ n = 1 := by
        rw [← map_pow]
        exact MonoidHom.mem_ker.mp ((ker_normalizedValuation K).ge (hz ▸ hmem))
      have htoAdd := congrArg Multiplicative.toAdd hpow
      rw [toAdd_pow, toAdd_one] at htoAdd
      simpa [hn0] using htoAdd
    refine ⟨Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) (unitFiltrationToIntegerUnits 0 ⟨z, hz0⟩),
      ?_⟩
    rw [powMonoidHom_apply, ← map_pow]
    refine congrArg _ (hinj ?_)
    rw [map_pow, unitsMap_subtype_unitFiltrationToIntegerUnits]
    exact hz
  · rintro ⟨α, hα⟩
    rw [powMonoidHom_apply] at hα
    have hp : (α ^ n, (integerUnitsEquivProd u).2) = integerUnitsEquivProd u :=
      Prod.ext (hα.trans (fst_integerUnitsEquivProd u).symm) rfl
    have hu : integerUnitsProdHom (α ^ n, (integerUnitsEquivProd u).2) = u := by
      rw [← integerUnitsEquivProd_symm_apply]
      exact (congrArg (integerUnitsEquivProd (K := K)).symm hp).trans
        ((integerUnitsEquivProd (K := K)).symm_apply_apply u)
    obtain ⟨z, hz⟩ := unitFiltration_one_le_range_powMonoidHom_of_isUnit hn
      (integerUnitsEquivProd u).2.2
    rw [powMonoidHom_apply] at hz
    have hpow : TauCeti.teichmuller 𝒪[K] α ^ n =
        TauCeti.teichmuller 𝒪[K] (α ^ n) :=
      (map_pow (TauCeti.teichmuller 𝒪[K]) α n).symm
    have hu' : TauCeti.teichmuller 𝒪[K] (α ^ n) *
        unitFiltrationToIntegerUnits 1 (integerUnitsEquivProd u).2 = u := by
      calc
        _ = integerUnitsProdHom (K := K) (α ^ n, (integerUnitsEquivProd u).2) :=
          (integerUnitsProdHom_apply (K := K) _).symm
        _ = u := hu
    refine ⟨Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K)
      (TauCeti.teichmuller 𝒪[K] α) * z, ?_⟩
    rw [powMonoidHom_apply, mul_pow, hz, ← map_pow,
      ← unitsMap_subtype_unitFiltrationToIntegerUnits, ← map_mul,
      hpow, hu']

/-- Away from residue characteristic two, a unit of `𝒪[K]` is a square in `K` exactly when its
residue is a square in `𝓀[K]`. -/
@[simp]
theorem isSquare_unitsMap_subtype_iff (h2 : IsUnit (2 : 𝒪[K])) (u : 𝒪[K]ˣ) :
    IsSquare (Units.map (Subring.subtype 𝒪[K] : 𝒪[K] →* K) u) ↔
      IsSquare (Units.map (residue 𝒪[K] : 𝒪[K] →* 𝓀[K]) u) := by
  have h2' : IsUnit ((2 : ℕ) : 𝒪[K]) := by simpa using h2
  have h := unitsMap_subtype_mem_range_powMonoidHom_iff h2' u
  simpa only [MonoidHom.mem_range, powMonoidHom_apply, isSquare_iff_exists_sq, eq_comm] using h

/-- **The power subgroup is open away from the residue characteristic.** For `n` invertible in
`𝒪[K]`, the subgroup `(Kˣ)ⁿ` of `n`-th powers is open in `Kˣ`. -/
theorem isOpen_range_powMonoidHom_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) :=
  Subgroup.isOpen_mono (unitFiltration_one_le_range_powMonoidHom_of_isUnit hn)
    (isOpen_unitFiltration 1)

/-- For `n` invertible in `𝒪[K]`, the subgroup `(Kˣ)ⁿ` of `n`-th powers is closed in `Kˣ`. -/
theorem isClosed_range_powMonoidHom_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    IsClosed ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_range_powMonoidHom_of_isUnit hn)

/-- A subgroup `H` of `Kˣ` is open as soon as the exponent of `Kˣ ⧸ H` is invertible in `𝒪[K]`:
`H` then contains the power subgroup attached to that exponent. -/
theorem isOpen_of_isUnit_exponent {H : Subgroup Kˣ}
    (hH : IsUnit (Monoid.exponent (Kˣ ⧸ H) : 𝒪[K])) : IsOpen (H : Set Kˣ) := by
  refine Subgroup.isOpen_mono ?_ (isOpen_range_powMonoidHom_of_isUnit hH)
  rintro _ ⟨y, rfl⟩
  simpa [← QuotientGroup.eq_one_iff] using Monoid.pow_exponent_eq_one (y : Kˣ ⧸ H)

/-- A subgroup of `Kˣ` whose index is invertible in `𝒪[K]` is open. Such a subgroup has finite
index, since the index `0` of an infinite-index subgroup is not a unit. -/
theorem isOpen_of_isUnit_index {H : Subgroup Kˣ} (hH : IsUnit (H.index : 𝒪[K])) :
    IsOpen (H : Set Kˣ) :=
  isOpen_of_isUnit_exponent <|
    isUnit_of_dvd_unit (Nat.cast_dvd_cast Group.exponent_dvd_nat_card) hH

/-- For `n` invertible in `𝒪[K]`, the only `n`-th root of unity in `K` that is a principal unit
is `1`: the groups `μ_n(K)` and `U(K,1)` intersect trivially. This is the case `v_K(n) = 0` of
`disjoint_rootsOfUnity_unitFiltration`. -/
theorem disjoint_rootsOfUnity_unitFiltration_one_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    Disjoint (rootsOfUnity n K) (unitFiltration K 1) := by
  have hnK := natCast_ne_zero_of_isUnit hn
  exact disjoint_rootsOfUnity_unitFiltration hnK fun p hp hpK hpn ↦
    natCastValuation_lt_sub_one_mul_of_dvd_of_lt hnK
      (natCastValuation_eq_zero_of_isUnit K hnK hn ▸ Nat.one_pos) hp hpK hpn

/-- For `n` invertible in `𝒪[K]`, the `n`-th power map is a bijection of each positive-depth step
`U(K,i+1)` of the unit filtration. -/
theorem powMonoidHom_unitFiltration_succ_bijective_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K]))
    (i : ℕ) :
    Function.Bijective (powMonoidHom n : unitFiltration K (i + 1) →* unitFiltration K (i + 1)) := by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp <| eq_bot_iff.mpr fun x hx ↦ Subtype.ext ?_,
    MonoidHom.range_eq_top.mp ?_⟩
  · refine Subgroup.disjoint_def.mp (disjoint_rootsOfUnity_unitFiltration_one_of_isUnit hn)
      ((mem_rootsOfUnity n (x : Kˣ)).mpr ?_) (unitFiltration_antitone (Nat.le_add_left 1 i) x.2)
    simpa using congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  · rw [← Subgroup.subgroupOf_map_powMonoidHom_eq_range,
      map_powMonoidHom_unitFiltration_succ_of_isUnit hn i, Subgroup.subgroupOf_self]

/-- Through the splitting `Kˣ ≅ ℤ × U(K,0)` attached to a uniformizer, the index of `(Kˣ)ⁿ` is `n`
times the index of the `n`-th powers in `U(K,0)`. -/
private theorem index_range_powMonoidHom_eq_mul_unitFiltration_zero (n : ℕ) :
    (powMonoidHom n : Kˣ →* Kˣ).range.index =
      n * (powMonoidHom n : unitFiltration K 0 →* unitFiltration K 0).range.index := by
  obtain ⟨ϖ, hϖ⟩ := normalizedValuation_surjective (K := K) (.ofAdd 1)
  let e := (unitsEquivIntProd K ϖ hϖ).toMulEquiv
  have hprod : (powMonoidHom n : Multiplicative ℤ × unitFiltration K 0 →* _) =
      (powMonoidHom n).prodMap (powMonoidHom n) := by
    ext x <;> simp
  -- The factor `ℤ` contributes index `n`.
  have hZ : (powMonoidHom n : Multiplicative ℤ →* _).range.index = n := by
    have : (powMonoidHom n : Multiplicative ℤ →* _) =
        AddMonoidHom.toMultiplicative (nsmulAddMonoidHom (α := ℤ) n) := by
      ext
      simp
    rw [this, MonoidHom.coe_toMultiplicative_range, AddSubgroup.index_toSubgroup,
      AddSubgroup.index_range_nsmul]
    simp
  rw [← Subgroup.index_map_equiv _ e, e.map_range_powMonoidHom n, hprod,
    MonoidHom.range_prodMap, Subgroup.index_prod, hZ]

/-- **The number of `n`-th power classes.** For `n` with `(n : K) ≠ 0`, the quotient
`Kˣ ⧸ (Kˣ)ⁿ` has `n · #μ_n(K) · q ^ v_K(n)` elements, where `μ_n(K)` is the group of `n`-th roots
of unity in `K`, `q` is the cardinality of the residue field and `v_K(n)` is the normalized
valuation of `n`. This holds in either characteristic; in characteristic zero, for instance for
`K` a finite extension of `ℚ_[p]`, it applies to every `n ≠ 0`, including multiples of the residue
characteristic. -/
theorem card_powerClasses {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * Nat.card (rootsOfUnity n K) * Nat.card 𝓀[K] ^ natCastValuation K n hn := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  set v := natCastValuation K n hn
  set G := unitFiltration K 0
  -- The deep subgroup `U(K,v+1)`, viewed inside `U(K,0)`.
  set U := (unitFiltration K (v + 1)).subgroupOf G
  -- The `n`-torsion of `U(K,0)` is all of `μ_n(K)`.
  have hker : Nat.card (powMonoidHom n : G →* G).ker = Nat.card (rootsOfUnity n K) := by
    have h : (powMonoidHom n : G →* G).ker = (rootsOfUnity n K).subgroupOf G := by
      ext x
      simp [Subgroup.mem_subgroupOf, mem_rootsOfUnity, Subtype.ext_iff]
    rw [h]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (rootsOfUnity_le_unitFiltration_zero K hn0)).toEquiv
  -- `U(K,v+1)` has finite index in `U(K,0)`.
  have : (unitFiltration K (v + 1)).IsFiniteRelIndex G :=
    (unitFiltration_isFiniteRelIndex_succ (v + 1) 0).trans unitFiltration_one_isFiniteRelIndex_zero
  -- Every prime `p ∣ n` has `v_K(p) < (p - 1) (v + 1)`.
  have hdepth : ∀ p : ℕ, p.Prime → ∀ hpK : (p : K) ≠ 0, p ∣ n →
      natCastValuation K p hpK < (p - 1) * (v + 1) := fun p hp hpK hpn ↦
    natCastValuation_lt_sub_one_mul_of_dvd_of_lt hn (Nat.lt_succ_self v) hp hpK hpn
  -- On `U(K,v+1)` the `n`-th power map is injective with image `U(K,2v+1)`.
  have hkerU : Nat.card (powMonoidHom n : U →* U).ker = 1 := by
    rw [Subgroup.card_eq_one, eq_bot_iff]
    intro x hx
    have h1 : ((x : G) : Kˣ) = 1 := Subgroup.disjoint_def.mp
      (disjoint_rootsOfUnity_unitFiltration hn hdepth)
      ((mem_rootsOfUnity n _).mpr
        (by simpa using congrArg (fun y : U ↦ ((y : G) : Kˣ)) (MonoidHom.mem_ker.mp hx)))
      x.2
    exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext h1))
  have hidxU : (powMonoidHom n : U →* U).range.index = Nat.card 𝓀[K] ^ v := by
    let f : U ≃* unitFiltration K (v + 1) :=
      Subgroup.subgroupOfEquivOfLe (unitFiltration_antitone (Nat.zero_le _))
    have hrel := relIndex_unitFiltration_add_succ_succ (K := K) v v
    rw [Subgroup.relIndex] at hrel
    rw [← Subgroup.index_map_equiv _ f, f.map_range_powMonoidHom n,
      ← Subgroup.subgroupOf_map_powMonoidHom_eq_range,
      map_powMonoidHom_unitFiltration hn hdepth,
      show v + 1 + v = v + v + 1 by omega, hrel]
  -- Comparing `U(K,0)` with its finite-index subgroup `U(K,v+1)`.
  have h := Subgroup.index_range_pow_mul_card_ker U n
  rw [hkerU, mul_one, hker, hidxU] at h
  rw [← Subgroup.index_eq_card, index_range_powMonoidHom_eq_mul_unitFiltration_zero, h, mul_assoc]

/-- For `(n : K) ≠ 0`, the subgroup `(Kˣ)ⁿ` of `n`-th powers has finite index in `Kˣ`. -/
theorem finiteIndex_range_powMonoidHom {n : ℕ} (hn : (n : K) ≠ 0) :
    (powMonoidHom n : Kˣ →* Kˣ).range.FiniteIndex := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have : NeZero n := ⟨hn0⟩
  refine ⟨?_⟩
  rw [Subgroup.index_eq_card, card_powerClasses hn]
  exact mul_ne_zero (mul_ne_zero hn0 Nat.card_pos.ne') (pow_ne_zero _ Nat.card_pos.ne')

/-- **The number of `n`-th power classes away from the residue characteristic.** For `n`
invertible in `𝒪[K]`, the quotient `Kˣ ⧸ (Kˣ)ⁿ` has `n · #μ_n(K)` elements, where `μ_n(K)` is the
group of `n`-th roots of unity in `K`. This holds in either characteristic. -/
theorem card_powerClasses_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) = n * Nat.card (rootsOfUnity n K) := by
  have hnK := natCast_ne_zero_of_isUnit hn
  rw [card_powerClasses hnK, natCastValuation_eq_zero_of_isUnit K hnK hn, pow_zero, mul_one]

/-- For `n` invertible in `𝒪[K]`, the subgroup `(Kˣ)ⁿ` of `n`-th powers has finite index in
`Kˣ`. -/
theorem finiteIndex_range_powMonoidHom_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    (powMonoidHom n : Kˣ →* Kˣ).range.FiniteIndex :=
  finiteIndex_range_powMonoidHom (natCast_ne_zero_of_isUnit hn)

/-- **The square classes away from residue characteristic `2`.** If `2` is invertible in `𝒪[K]`,
then `Kˣ ⧸ (Kˣ)²` has `4` elements: `μ_2(K) = {±1}` has order `2`. -/
theorem card_squareClasses_of_isUnit (h2 : IsUnit (2 : 𝒪[K])) :
    Nat.card (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) = 4 := by
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_isUnit_two h2
  have hchar : ringChar K ≠ 2 := fun h ↦ h2K (by exact_mod_cast h ▸ ringChar.Nat.cast_ringChar)
  rw [card_powerClasses_of_isUnit (by exact_mod_cast h2),
    (IsPrimitiveRoot.neg_one (ringChar K) hchar).card_rootsOfUnity]

end TauCeti
