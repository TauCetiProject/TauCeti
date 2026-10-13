/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.NumberTheory.LocalField.PowerSubgroup.Units
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Unit power classes at finite places

Let a number field `K` contain the `n`-th roots of unity. At a finite place `v` not dividing
`n`, the units of the completed integer ring have exactly `n` classes modulo `n`-th powers.
Consequently the product of these unit quotients over a finite set `T` has `n ^ #T` elements.
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

/-- At a finite place away from `n`, the completed integer-ring units have `n` power classes
if the number field contains the `n`-th roots of unity. -/
theorem card_unitPowerClasses_adicCompletion (v : HeightOneSpectrum (𝓞 K)) {n : ℕ}
    [HasEnoughRootsOfUnity K n] (hnv : (n : 𝓞 K) ∉ v.asIdeal) :
    Nat.card ((v.adicCompletionIntegers K)ˣ ⧸
      (powMonoidHom n : (v.adicCompletionIntegers K)ˣ →* _).range) = n := by
  have : NeZero n := ⟨by
    rintro rfl
    simp at hnv⟩
  let e := Units.mapEquiv (v.integerEquivAdicCompletionIntegers (K := K)).toMulEquiv
  have hu : IsUnit (n : v.adicCompletionIntegers K) := by
    rw [adicCompletionIntegers.isUnit_iff_valued_eq_one]
    simpa using
      (v.valuedAdicCompletion_eq_valuation (n : 𝓞 K)).trans
        (v.valuation_eq_one_iff_notMem.mpr hnv)
  have hu' : IsUnit (n : 𝒪[v.adicCompletion K]) := by
    simpa using hu.map (v.integerEquivAdicCompletionIntegers (K := K)).symm
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  rw [← Subgroup.index_eq_card, ← e.map_range_powMonoidHom n,
    Subgroup.index_map_equiv, Subgroup.index_eq_card,
    TauCeti.card_integerUnitPowerClasses_of_isUnit hu']
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
      v.card_unitPowerClasses_adicCompletion (hT v hv)
    _ = n ^ T.card := by simp

end TauCeti.GlobalNumberFields
