/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Units
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Unit power classes at finite places

At a finite place `v` of a number field `K` not dividing `n`, the units of the completed
integer ring have as many `n`-th power classes as there are `n`-th roots of unity in `K_v`.
If `K` contains these roots, the count is `n`, and consequently the product of these unit
quotients over a finite set `T` has `n ^ #T` elements.
This is the local cardinality input to the S-unit surjectivity argument in the Kummer proof
of the second fundamental inequality.

The local calculation is `TauCeti.card_integerUnitPowerClasses_of_isUnit`, transported along
the existing identification `HeightOneSpectrum.integerEquivAdicCompletionIntegers` of the
two integer-ring presentations of the completion.

## References

* J. S. Milne, *Class Field Theory*, VII, proof of Lemma 6.9.
-/

public section

open IsDedekindDomain NumberField ValuativeRel

namespace IsDedekindDomain.HeightOneSpectrum

variable {K : Type*} [Field K] [NumberField K]

/-- For nonzero `n`, the `n`-th powers of the completed integer-ring units have finite index. -/
theorem finiteIndex_range_powMonoidHom_adicCompletionIntegers
    (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} (hn : n ≠ 0) :
    (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →* _).range.FiniteIndex := by
  let e := Units.mapEquiv (v.integerEquivAdicCompletionIntegers (K := K)).toMulEquiv
  have h := TauCeti.finiteIndex_range_powMonoidHom_integerUnits
    (K := v.adicCompletion K) (Nat.cast_ne_zero.mpr hn)
  refine ⟨?_⟩
  rw [← e.map_range_powMonoidHom n, Subgroup.index_map_equiv]
  exact h.index_ne_zero

/-- For nonzero `n`, the power-map range on completed integer-ring units has finite index. -/
instance instFiniteIndexRangePowMonoidHomAdicCompletionIntegers
    (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} [NeZero n] :
    (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →* _).range.FiniteIndex :=
  v.finiteIndex_range_powMonoidHom_adicCompletionIntegers (NeZero.ne n)

/-- For nonzero `n`, the power-class quotient of the completed integer-ring units is finite. -/
instance finite_powerClassQuotient_adicCompletionIntegers
    (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} [NeZero n] :
    Finite (TauCeti.powerClassQuotient (v.adicCompletionIntegers K)ˣ n) :=
  have : (TauCeti.powerSubgroup (v.adicCompletionIntegers K)ˣ n).FiniteIndex :=
    TauCeti.powerSubgroup_eq_range_powMonoidHom (v.adicCompletionIntegers K)ˣ n ▸
      v.finiteIndex_range_powMonoidHom_adicCompletionIntegers (NeZero.ne n)
  Subgroup.finite_quotient_of_finiteIndex

/-- At a finite place away from `n`, the completed integer-ring units have as many `n`-th
power classes as there are `n`-th roots of unity in the completion. -/
theorem card_unitPowerClasses_adicCompletion (v : HeightOneSpectrum (𝓞 K)) {n : ℕ}
    (hnv : (n : 𝓞 K) ∉ v.asIdeal) :
    Nat.card ((v.adicCompletionIntegers K)ˣ ⧸
      (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →* _).range) =
      Nat.card (rootsOfUnity n (v.adicCompletion K)) := by
  let e := Units.mapEquiv (v.integerEquivAdicCompletionIntegers (K := K)).toMulEquiv
  have hu' := (v.isUnit_natCast_integer_adicCompletion_iff (K := K) n).mpr hnv
  rw [← Subgroup.index_eq_card, ← e.map_range_powMonoidHom n,
    Subgroup.index_map_equiv, Subgroup.index_eq_card,
    TauCeti.card_integerUnitPowerClasses_of_isUnit hu']

/-- At a finite place away from `n`, the completed integer-ring units have `n` power classes
if the number field contains the `n`-th roots of unity. -/
theorem card_unitPowerClasses_adicCompletion_of_hasEnoughRootsOfUnity
    (v : HeightOneSpectrum (𝓞 K)) {n : ℕ} [HasEnoughRootsOfUnity K n]
    (hnv : (n : 𝓞 K) ∉ v.asIdeal) :
    Nat.card ((v.adicCompletionIntegers K)ˣ ⧸
      (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →* _).range) = n := by
  have : NeZero n := ⟨by
    rintro rfl
    simp at hnv⟩
  rw [v.card_unitPowerClasses_adicCompletion hnv]
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot K n
  exact (hζ.map_of_injective (algebraMap K (v.adicCompletion K)).injective).card_rootsOfUnity

end IsDedekindDomain.HeightOneSpectrum

namespace TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- **The product of local unit power-class counts.** If `K` contains `μ_n` and `T` is a finite
set of finite places avoiding `n`, then the product of the orders of their unit power-class
quotients is `n ^ #T`. -/
theorem prod_card_unitPowerClasses (n : ℕ) [HasEnoughRootsOfUnity K n]
    (T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, (n : 𝓞 K) ∉ v.asIdeal) :
    (∏ v ∈ T, Nat.card ((v.adicCompletionIntegers K)ˣ ⧸
      (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →* _).range)) = n ^ T.card := by
  calc
    _ = ∏ v ∈ T, n := Finset.prod_congr rfl fun v hv ↦
      v.card_unitPowerClasses_adicCompletion_of_hasEnoughRootsOfUnity (hT v hv)
    _ = n ^ T.card := by simp

end TauCeti.GlobalNumberFields
