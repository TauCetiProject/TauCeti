/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NatCastValuation
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Basic
public import TauCeti.NumberTheory.LocalField.UnitFiltration.Pow
import TauCeti.GroupTheory.Index.NSmul
import TauCeti.NumberTheory.LocalField.MultiplicativeGroup
import TauCeti.NumberTheory.LocalField.UnitFiltration.Graded
import TauCeti.RingTheory.RootsOfUnity.Basic

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
(`Subgroup.index_range_pow_mul_card_ker`). The general reduction to principal units splits
`Kˣ ≅ ℤ × μ_{q-1}(K) × U(K,1)`, where the factor `ℤ` contributes `n`. Inside `U(K,1)`, the
deep subgroup `U(K, v_K(n) + 1)` has no `n`-torsion and is carried by the `n`-th power map onto
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
The openness results are stated in `PowerSubgroup.Open`, including the general case
`(n : K) ≠ 0` obtained from powers of deep units.

## Main results

* `TauCeti.card_powerClasses`: `#(Kˣ ⧸ (Kˣ)ⁿ) = n · #μ_n(K) · q ^ v_K(n)` for `(n : K) ≠ 0`.
* `TauCeti.card_powerClasses_eq_mul_inv_normalizedAbsoluteValue`: the same count as an equality
  `#(Kˣ ⧸ (Kˣ)ⁿ) = n · #μ_n(K) · ‖n‖_K⁻¹` in `ℚ≥0`, with `‖·‖_K` the normalized absolute value.
* `TauCeti.finiteIndex_range_powMonoidHom`: `(Kˣ)ⁿ` has finite index in `Kˣ` for `(n : K) ≠ 0`.
* `TauCeti.map_powMonoidHom_unitFiltration_succ_of_isUnit`: the `n`-th power map carries
  `U(K,i+1)` onto itself.
* `TauCeti.unitFiltration_one_le_range_powMonoidHom_of_isUnit`: every principal unit is an
  `n`-th power, `U(K,1) ≤ (Kˣ)ⁿ`.
* `TauCeti.unitsMap_subtype_mem_range_powMonoidHom_iff` and
  `TauCeti.isSquare_unitsMap_subtype_iff`: a unit of `𝒪[K]` is an `n`-th power, respectively a
  square, in `K` exactly when its residue is one in `𝓀[K]`.
* `TauCeti.disjoint_rootsOfUnity_unitFiltration_one_of_isUnit`: no nontrivial `n`-th root of
  unity is a principal unit.
* `TauCeti.powMonoidHom_unitFiltration_succ_bijective_of_isUnit`: the `n`-th power map is a
  bijection of `U(K,i+1)`.
* `TauCeti.card_powerClasses_eq_of_index_unitFiltration_one`: the power-class count reduces to
  the index/kernel ratio of the power map on the principal units.
* `TauCeti.card_powerClasses_of_isUnit`: `#(Kˣ ⧸ (Kˣ)ⁿ) = n · #μ_n(K)`.
* `TauCeti.finiteIndex_range_powMonoidHom_of_isUnit`: `(Kˣ)ⁿ` has finite index in `Kˣ`.
* `TauCeti.card_squareClasses_of_isUnit`: `#(Kˣ ⧸ (Kˣ)²) = 4` when `2` is a unit of `𝒪[K]`.
* `TauCeti.card_squareClasses`: `#(Kˣ ⧸ (Kˣ)²) = 4 · q ^ v_K(2)` when `2 ≠ 0` in `K`.

## Implementation notes

In the theorems assuming `IsUnit (n : 𝒪[K])`, this hypothesis already forces `n ≠ 0`, so
no separate nonvanishing assumption is taken. The general reduction theorem
`card_powerClasses_eq_of_index_unitFiltration_one` instead requires `n ≠ 0` explicitly. In mixed
characteristic the same openness holds for every `n ≠ 0`, using the binomial power identity on
deep units instead of Hensel's lemma at `1`, and in equal characteristic `p` the range
of `powMonoidHom p` is not open. Likewise the count acquires the factor `q ^ v_K(n)` when `n` is not
a unit, and in equal characteristic `p` the quotient `Kˣ ⧸ (Kˣ)ᵖ` is infinite.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter V, §3.
* J. Neukirch, J. Schmidt, K. Wingberg, *Cohomology of Number Fields*, Chapter VII, §3.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §5.
-/

public section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

open scoped NNRat

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
    natCastValuation_lt_sub_one_mul_of_lt_of_dvd hnK (hv ▸ i.succ_pos) hp hpK hpn

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

/-- For `n` invertible in `𝒪[K]`, the only `n`-th root of unity in `K` that is a principal unit
is `1`: the groups `μ_n(K)` and `U(K,1)` intersect trivially. This is the case `v_K(n) = 0` of
`disjoint_rootsOfUnity_unitFiltration`. -/
theorem disjoint_rootsOfUnity_unitFiltration_one_of_isUnit {n : ℕ} (hn : IsUnit (n : 𝒪[K])) :
    Disjoint (rootsOfUnity n K) (unitFiltration K 1) := by
  have hnK := natCast_ne_zero_of_isUnit hn
  exact disjoint_rootsOfUnity_unitFiltration hnK fun p hp hpK hpn ↦
    natCastValuation_lt_sub_one_mul_of_lt_of_dvd hnK
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

/-- **Reduction of the power-class count to the principal units.** Suppose the `n`-th power map
on `U(K,1)` has index `#U(K,1)[n] · c`. Then
`#(Kˣ/(Kˣ)ⁿ) = n · #μ_n(K) · c`.

The factor `n` comes from the normalized valuation `Kˣ → ℤ`; the prime-to-residue-
characteristic roots of unity and the principal units together account for all of `μ_n(K)`.
Thus the remaining local-field input to a power-class formula is exactly the index/kernel ratio
of the power map on the principal units. -/
theorem card_powerClasses_eq_of_index_unitFiltration_one {n c : ℕ} (hn : n ≠ 0)
    (hV : (powMonoidHom n : unitFiltration K 1 →* unitFiltration K 1).range.index =
      Nat.card (powMonoidHom n : unitFiltration K 1 →* unitFiltration K 1).ker * c) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * Nat.card (rootsOfUnity n K) * c := by
  obtain ⟨ϖ, hϖ⟩ := normalizedValuation_surjective (K := K) (.ofAdd 1)
  set μ := rootsOfUnity (Nat.card 𝓀[K] - 1) K
  set V := unitFiltration K 1
  have : Finite μ := .of_equiv _
    (TauCeti.rootsOfUnityAlgebraMulEquivUnitsResidueField
      𝒪[K] K).symm.toEquiv
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
      have hcomm :
          (powMonoidHom n : Kˣ →* Kˣ).comp e.symm.toMonoidHom =
            e.symm.toMonoidHom.comp
              (powMonoidHom n : Multiplicative ℤ × μ × V →* _) := by
        ext
        simp
      calc
        _ = ((powMonoidHom n : Kˣ →* Kˣ).comp e.symm.toMonoidHom).ker :=
          (MonoidHom.ker_comp_mulEquiv (powMonoidHom n : Kˣ →* Kˣ) e.symm).symm
        _ = (e.symm.toMonoidHom.comp
              (powMonoidHom n : Multiplicative ℤ × μ × V →* _)).ker :=
          congrArg MonoidHom.ker hcomm
        _ = _ := MonoidHom.ker_mulEquiv_comp _ e.symm
    rw [rootsOfUnity_eq_ker, ← hmap]
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv
  -- On the product, the power map is componentwise.
  have hprod : (powMonoidHom n : Multiplicative ℤ × μ × V →* _) =
      (powMonoidHom n).prodMap ((powMonoidHom n).prodMap (powMonoidHom n)) := by
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
  have hZker : (powMonoidHom n : Multiplicative ℤ →* _).ker = ⊥ := by
    ext
    simp [hn]
  -- The finite factor `μ_{q-1}(K)` has as many power classes as `n`-torsion elements. The
  -- hypothesis `hV` records the corresponding index/kernel ratio on the principal units.
  have hμ : (powMonoidHom n : μ →* μ).range.index =
      Nat.card (powMonoidHom n : μ →* μ).ker := Subgroup.index_range
  have hZkerCard : Nat.card (powMonoidHom n : Multiplicative ℤ →* _).ker = 1 := by
    rw [hZker]
    simp
  have hproductIndex :
      (powMonoidHom n : Multiplicative ℤ × μ × V →* _).range.index =
        n * (Nat.card (powMonoidHom n : μ →* μ).ker *
          Nat.card (powMonoidHom n : V →* V).ker) * c := by
    calc
      _ = (powMonoidHom n : Multiplicative ℤ →* _).range.index *
          ((powMonoidHom n : μ →* μ).range.index *
            (powMonoidHom n : V →* V).range.index) := by
        rw [hprod, MonoidHom.range_prodMap, MonoidHom.range_prodMap,
          Subgroup.index_prod, Subgroup.index_prod]
      _ = n * (Nat.card (powMonoidHom n : μ →* μ).ker *
          (Nat.card (powMonoidHom n : V →* V).ker * c)) := by
        rw [hZ, hμ, hV]
      _ = _ := by ring
  have hproductKernel :
      Nat.card (powMonoidHom n : Multiplicative ℤ × μ × V →* _).ker =
        Nat.card (powMonoidHom n : μ →* μ).ker *
          Nat.card (powMonoidHom n : V →* V).ker := by
    calc
      _ = Nat.card (powMonoidHom n : Multiplicative ℤ →* _).ker *
          (Nat.card (powMonoidHom n : μ →* μ).ker *
            Nat.card (powMonoidHom n : V →* V).ker) := by
        rw [hprod, MonoidHom.ker_prodMap, MonoidHom.ker_prodMap,
          Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
          Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod]
      _ = 1 * (Nat.card (powMonoidHom n : μ →* μ).ker *
          Nat.card (powMonoidHom n : V →* V).ker) := by rw [hZkerCard]
      _ = _ := by simp
  calc
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
        (powMonoidHom n : Kˣ →* Kˣ).range.index := (Subgroup.index_eq_card _).symm
    _ = (powMonoidHom n : Multiplicative ℤ × μ × V →* _).range.index := hidx
    _ = n * (Nat.card (powMonoidHom n : μ →* μ).ker *
        Nat.card (powMonoidHom n : V →* V).ker) * c := hproductIndex
    _ = n * Nat.card (powMonoidHom n : Multiplicative ℤ × μ × V →* _).ker * c :=
      congrArg (· * c) (congrArg (n * ·) hproductKernel.symm)
    _ = n * Nat.card (rootsOfUnity n K) * c :=
      congrArg (· * c) (congrArg (n * ·) hker.symm)

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
  set G := unitFiltration K 1
  -- The deep subgroup `U(K,v+1)`, viewed inside `U(K,1)`.
  set U := (unitFiltration K (v + 1)).subgroupOf G
  -- `U(K,v+1)` has finite index in `U(K,1)`.
  have : (unitFiltration K (v + 1)).IsFiniteRelIndex G :=
    unitFiltration_isFiniteRelIndex_succ (v + 1) 0
  -- Every prime `p ∣ n` has `v_K(p) < (p - 1) (v + 1)`.
  have hdepth : ∀ p : ℕ, p.Prime → ∀ hpK : (p : K) ≠ 0, p ∣ n →
      natCastValuation K p hpK < (p - 1) * (v + 1) := fun p hp hpK hpn ↦
    natCastValuation_lt_sub_one_mul_of_lt_of_dvd hn (Nat.lt_succ_self v) hp hpK hpn
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
      Subgroup.subgroupOfEquivOfLe (unitFiltration_antitone (Nat.le_add_left 1 v))
    have hrel := relIndex_unitFiltration_add_succ_succ (K := K) v v
    rw [Subgroup.relIndex] at hrel
    -- Reassociate the filtration depth to match the form in the relative-index theorem.
    have hdepth_eq : v + 1 + v = v + v + 1 := by omega
    rw [← Subgroup.index_map_equiv _ f, f.map_range_powMonoidHom n,
      ← Subgroup.subgroupOf_map_powMonoidHom_eq_range,
      map_powMonoidHom_unitFiltration hn hdepth, hdepth_eq, hrel]
  -- Comparing `U(K,1)` with its finite-index subgroup `U(K,v+1)` gives the input required by
  -- the general reduction of the power-class count to principal units.
  apply card_powerClasses_eq_of_index_unitFiltration_one hn0
  have h := Subgroup.index_range_pow_mul_card_ker U n
  rw [hkerU, mul_one, hidxU] at h
  exact h

/-- **The number of `n`-th power classes, absolute-value form.** For `n` with `(n : K) ≠ 0`, the
quotient `Kˣ ⧸ (Kˣ)ⁿ` has `n · #μ_n(K) · ‖n‖_K⁻¹` elements, where `μ_n(K)` is the group of `n`-th
roots of unity in `K` and `‖·‖_K` is the normalized absolute value of `K`. Since
`‖n‖_K = q ^ (-v_K(n))`, the factor `‖n‖_K⁻¹` is the factor `q ^ v_K(n)` of `card_powerClasses`,
and the equation holds in `ℚ≥0` after casting the natural-number cardinalities. -/
theorem card_powerClasses_eq_mul_inv_normalizedAbsoluteValue {n : ℕ} (hn : (n : K) ≠ 0) :
    (Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) : ℚ≥0) =
      (n : ℚ≥0) * (Nat.card (rootsOfUnity n K) : ℚ≥0) * (normalizedAbsoluteValue K (n : K))⁻¹ := by
  simp [card_powerClasses hn, normalizedAbsoluteValue_natCast K n hn]

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

/-- In characteristic zero, the subgroup `(Kˣ)ⁿ` of `n`-th powers has finite index in `Kˣ` for
every nonzero `n`. -/
instance instFiniteIndexRangePowMonoidHom [CharZero K] {n : ℕ} [NeZero n] :
    (powMonoidHom n : Kˣ →* Kˣ).range.FiniteIndex :=
  finiteIndex_range_powMonoidHom (Nat.cast_ne_zero.2 (NeZero.ne n))

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
  rw [card_powerClasses_of_isUnit (by exact_mod_cast h2),
    card_rootsOfUnity_two (two_ne_zero_of_isUnit_two h2)]

/-- **The number of square classes of a nonarchimedean local field.** If `2` is nonzero in `K`,
then `Kˣ ⧸ (Kˣ)²` has `4 · #𝓀[K] ^ v_K(2)` elements. -/
@[simp]
theorem card_squareClasses (h2 : (2 : K) ≠ 0) :
    Nat.card (Kˣ ⧸ (powMonoidHom 2 : Kˣ →* Kˣ).range) =
      4 * Nat.card 𝓀[K] ^ natCastValuation K 2 h2 := by
  rw [card_powerClasses h2, card_rootsOfUnity_two h2]

end TauCeti
