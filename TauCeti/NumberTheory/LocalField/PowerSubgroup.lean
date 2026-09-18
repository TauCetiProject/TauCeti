/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IndexNSmul
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import TauCeti.NumberTheory.LocalField.UnitsDecomposition
public import TauCeti.RingTheory.Henselian
public import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# The `n`-th power subgroup of a local field away from the residue characteristic

Let `K` be a nonarchimedean local field and let `n` be a natural number that is invertible in
`𝒪[K]`, that is, prime to the residue characteristic. This file shows that the subgroup
`(Kˣ)ⁿ`, the range of `powMonoidHom n : Kˣ →* Kˣ`, is open, and hence closed, in `Kˣ`.

The proof exhibits an explicit open subgroup inside the range: every principal unit is an
`n`-th power. More precisely, the `n`-th power map carries each positive-depth step `U(K,i+1)` of
the unit filtration onto itself, by Hensel's lemma applied to `X ^ n - u` at the approximate root
`1`, whose derivative `n` is a unit there. Openness does not follow from any finiteness of the
quotient `Kˣ ⧸ (Kˣ)ⁿ`: a subgroup of finite index in a topological group need not be open.

As a consequence, a subgroup of `Kˣ` is open as soon as the exponent (for instance, the index) of
the quotient by it is invertible in `𝒪[K]`, since it then contains the power subgroup attached to
that exponent.

The file also counts the power classes: `#(Kˣ ⧸ (Kˣ)ⁿ) = n · #μ_n(K)`, where `μ_n(K)` is the group
of `n`-th roots of unity in `K`. The `n`-th power map is an automorphism of the group `U(K,1)` of
principal units: it is onto by the Hensel argument above, and one-to-one because a root of unity
of order prime to the residue characteristic that is congruent to `1` is equal to `1`. Through
the splitting `Kˣ ≅ ℤ × μ_{q-1}(K) × U(K,1)`, the count therefore comes from the factor `ℤ`, which
contributes `n`, and the finite factor `μ_{q-1}(K)`, whose power classes are as many as its
`n`-torsion elements, which make up `μ_n(K)`. In particular there are `4` square classes
when `2` is a unit of `𝒪[K]`.

## Main results

* `TauCeti.map_powMonoidHom_unitFiltration_succ_of_isUnit`: the `n`-th power map carries
  `U(K,i+1)` onto itself.
* `TauCeti.unitFiltration_one_le_range_powMonoidHom_of_isUnit`: every principal unit is an
  `n`-th power, `U(K,1) ≤ (Kˣ)ⁿ`.
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
assumption is taken. In mixed characteristic the same openness holds for every `n ≠ 0`, but
there the `p`-primary part needs the logarithm on deep units instead of Hensel's lemma at `1`,
and in equal characteristic `p` the range of `powMonoidHom p` is not open. Likewise the count
acquires the factor `q ^ v_K(n)` when `n` is not a unit, and in equal characteristic `p` the
quotient `Kˣ ⧸ (Kˣ)ᵖ` is infinite.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- For `n` invertible in `𝒪[K]`, the `n`-th power map carries each positive-depth step
`U(K,i+1)` of the unit filtration onto itself. -/
theorem map_powMonoidHom_unitFiltration_succ_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K]))
    (i : ℕ) :
    (unitFiltration K (i + 1)).map (powMonoidHom n) = unitFiltration K (i + 1) := by
  refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr fun x hx ↦ pow_mem hx n) fun x hx ↦ ?_
  -- `𝒪[K]` is Henselian at `𝓂[K]`: it is complete for the adic topology of its maximal ideal,
  -- which Mathlib records for the uniformity attached to the topological additive group `K`.
  have : HenselianRing 𝒪[K] 𝓂[K] := by
    let := IsTopologicalAddGroup.rightUniformSpace K
    have := isUniformAddGroup_of_addCommGroup (G := K)
    exact IsAdicComplete.henselianRing 𝒪[K] 𝓂[K]
  obtain ⟨u, hu, hux⟩ := mem_unitFiltration_iff_exists.mp hx
  obtain ⟨a, ha, ha1⟩ := HenselianRing.exists_pow_eq_and_sub_one_mem_of_sub_one_mem
    (Ideal.pow_le_self i.succ_ne_zero) hn hu
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have haU : IsUnit a := (isUnit_pow_iff hn0).mp (ha ▸ u.isUnit)
  refine ⟨Units.map (Subring.subtype 𝒪[K]).toMonoidHom haU.unit,
    (mem_unitFiltration_succ_congr i _).mpr (by simpa using ha1), ?_⟩
  ext
  simp [← hux, ← ha]

/-- For `n` invertible in `𝒪[K]`, every principal unit of `K` is an `n`-th power. -/
theorem unitFiltration_one_le_range_powMonoidHom_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    unitFiltration K 1 ≤ (powMonoidHom n : Kˣ →* Kˣ).range :=
  map_powMonoidHom_unitFiltration_succ_of_isUnit hn 0 ▸ Subgroup.map_le_range _ _

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
is `1`: the groups `μ_n(K)` and `U(K,1)` intersect trivially. -/
theorem disjoint_rootsOfUnity_unitFiltration_one_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    Disjoint (rootsOfUnity n K) (unitFiltration K 1) := by
  refine Subgroup.disjoint_def.mpr fun {x} hxn hx1 ↦ ?_
  obtain ⟨u, hu1, hux⟩ := mem_unitFiltration_iff_exists.mp hx1
  have hpow : (u : 𝒪[K]) ^ n = 1 :=
    Subtype.coe_injective <| by simpa [hux] using congrArg Units.val ((mem_rootsOfUnity n x).mp hxn)
  have hu : (u : 𝒪[K]) = 1 := eq_one_of_pow_eq_one_of_sub_one_mem
    (notMem_maximalIdeal.mpr hn) hpow (by simpa using hu1)
  ext
  simp [← hux, hu]

/-- For `n` invertible in `𝒪[K]`, the `n`-th power map is a bijection of each positive-depth step
`U(K,i+1)` of the unit filtration: it is onto by Hensel's lemma, and one-to-one because `U(K,1)`
contains no nontrivial `n`-th root of unity. -/
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

/-- **The number of `n`-th power classes away from the residue characteristic.** For `n`
invertible in `𝒪[K]`, the quotient `Kˣ ⧸ (Kˣ)ⁿ` has `n · #μ_n(K)` elements, where `μ_n(K)` is the
group of `n`-th roots of unity in `K`. This holds in either characteristic. -/
theorem card_powerClasses_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) = n * Nat.card (rootsOfUnity n K) := by
  obtain ⟨ϖ, hϖ⟩ := normalizedValuation_surjective (K := K) (.ofAdd 1)
  set μ := rootsOfUnity (Nat.card 𝓀[K] - 1) K
  set V := unitFiltration K 1
  have : Finite μ := .of_equiv _ (rootsOfUnityFieldEquivResidueFieldUnits K).symm.toEquiv
  -- The splitting `Kˣ ≃* ℤ × μ_{q-1}(K) × U(K,1)` attached to the uniformizer `ϖ`.
  let e : Kˣ ≃* Multiplicative ℤ × μ × V :=
    (unitsEquivIntProd K ϖ hϖ).toMulEquiv.trans
      (MulEquiv.prodCongr (.refl _) (unitFiltrationZeroEquivProd K).toMulEquiv)
  -- Both the index of `(Kˣ)ⁿ` and the number of `n`-th roots of unity transfer along `e`.
  have hidx : (powMonoidHom n : Kˣ →* Kˣ).range.index =
      (powMonoidHom n : Multiplicative ℤ × μ × V →* _).range.index := by
    rw [← e.map_range_powMonoidHom n, Subgroup.index_map_equiv]
  have hker : Nat.card (rootsOfUnity n K) =
      Nat.card (powMonoidHom n : Multiplicative ℤ × μ × V →* _).ker := by
    have hmap : (powMonoidHom n : Kˣ →* Kˣ).ker.map e.toMonoidHom =
        (powMonoidHom n : Multiplicative ℤ × μ × V →* _).ker := by
      ext x
      rw [Subgroup.mem_map_equiv, MonoidHom.mem_ker, MonoidHom.mem_ker, powMonoidHom_apply,
        powMonoidHom_apply, ← map_pow, MulEquiv.map_eq_one_iff]
    rw [rootsOfUnity_eq_ker, ← hmap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv
  -- On the product, the power map is componentwise.
  have hprod : (powMonoidHom n : Multiplicative ℤ × μ × V →* _) =
      (powMonoidHom n).prodMap ((powMonoidHom n).prodMap (powMonoidHom n)) := by
    ext x <;> simp
  -- The factor `ℤ` contributes index `n` and no torsion.
  have hZ : (powMonoidHom n : Multiplicative ℤ →* _).range.index = n := by
    have : (powMonoidHom n : Multiplicative ℤ →* _) =
        AddMonoidHom.toMultiplicative (nsmulAddMonoidHom (α := ℤ) n) := by
      ext
      simp
    rw [this, MonoidHom.coe_toMultiplicative_range, AddSubgroup.index_toSubgroup,
      AddSubgroup.index_range_nsmul]
    simp
  have hZker : (powMonoidHom n : Multiplicative ℤ →* _).ker = ⊥ := by
    ext
    simp [(show n ≠ 0 by rintro rfl; simp at hn)]
  -- The factor `U(K,1)` contributes neither, and the finite factor `μ_{q-1}(K)` has as many power
  -- classes as `n`-torsion elements.
  obtain ⟨hVinj, hVsurj⟩ := powMonoidHom_unitFiltration_succ_bijective_of_isUnit hn 0
  rw [← Subgroup.index_eq_card, hidx, hker, hprod, MonoidHom.range_prodMap,
    MonoidHom.range_prodMap, Subgroup.index_prod, Subgroup.index_prod, MonoidHom.ker_prodMap,
    MonoidHom.ker_prodMap, hZ, hZker, MonoidHom.range_eq_top.mpr hVsurj,
    (MonoidHom.ker_eq_bot_iff _).mpr hVinj, Subgroup.index_top, Subgroup.index_range,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
  simp

/-- For `n` invertible in `𝒪[K]`, the subgroup `(Kˣ)ⁿ` of `n`-th powers has finite index in
`Kˣ`, as a consequence of `card_powerClasses_of_isUnit`. -/
theorem finiteIndex_range_powMonoidHom_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    (powMonoidHom n : Kˣ →* Kˣ).range.FiniteIndex := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  have : NeZero n := ⟨hn0⟩
  refine ⟨?_⟩
  rw [Subgroup.index_eq_card, card_powerClasses_of_isUnit hn]
  exact mul_ne_zero hn0 Nat.card_pos.ne'

/-- **The square classes away from residue characteristic `2`.** If `2` is invertible in `𝒪[K]`,
then `Kˣ ⧸ (Kˣ)²` has `4` elements: `μ_2(K) = {±1}` has order `2`. -/
theorem card_squareClasses_of_isUnit (h2 : IsUnit (2 : 𝒪[K])) :
    Nat.card (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) = 4 := by
  have h2K : (2 : K) ≠ 0 := by
    simpa only [map_ofNat] using (h2.map (Subring.subtype 𝒪[K])).ne_zero
  have hchar : ringChar K ≠ 2 := fun h ↦ h2K (by exact_mod_cast h ▸ ringChar.Nat.cast_ringChar)
  rw [card_powerClasses_of_isUnit (by exact_mod_cast h2),
    (IsPrimitiveRoot.neg_one (ringChar K) hchar).card_rootsOfUnity]

end TauCeti
